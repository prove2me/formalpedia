-- Prove2me | solution 1 for SepCostShare.exchange_count
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T20:51:25.660472+00:00
-- url     : https://prove2.me/submissions/5cfc57e8-5b92-4714-9be5-e7c2367d6e13

import Mathlib
import Definitions.Def_SepCostShare_MatroidGame
import Definitions.Def_SepCostShare_Deviation

namespace Aux_SepCostShare_exchange_count

open SepCostShare

variable {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]

/-- Position of `x` in player `i`'s virtual-cost order. -/
noncomputable def rk (G : MatroidGame N E) (i : N) (x : E) : ℕ :=
  (Finset.univ.filter (fun g => G.pi i g < G.pi i x)).card

theorem rk_le (G : MatroidGame N E) (i : N) (x : E) : rk G i x ≤ Fintype.card E - 1 := by
  unfold rk
  have hsub : Finset.univ.filter (fun g => G.pi i g < G.pi i x) ⊆ Finset.univ.erase x := by
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ g⟩
    intro h
    rw [h] at hg
    exact lt_irrefl _ hg
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ] at this
  exact this

theorem rk_lt (G : MatroidGame N E) (i : N) (e f : E) (hlt : G.pi i f < G.pi i e) :
    rk G i f < rk G i e := by
  unfold rk
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨f, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hlt
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_irrefl _
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    exact lt_trans hg hlt

end Aux_SepCostShare_exchange_count

open SepCostShare Aux_SepCostShare_exchange_count in
theorem solution {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]
    (G : MatroidGame N E) (hG : G.Subadditive) (s : ℕ → (N → Finset E)) (k : ℕ)
    (hs0 : G.IsProfile (s 0))
    (hstep : ∀ t < k, G.IsProfile (s (t + 1)) ∧
      ∃ (i : N) (e f : E), e ∈ s t i ∧ f ∉ s t i ∧ G.pi i f < G.pi i e ∧
        s (t + 1) = G.swap (s t) i e f) :
    k ≤ ∑ i : N, G.rank i * (Fintype.card E - 1) ∧
      ∑ i : N, G.rank i * (Fintype.card E - 1) ≤
        Fintype.card N * Fintype.card E * G.rkMax := by
  have hdec : ∀ t < k, (∑ j : N, ∑ x ∈ s (t + 1) j, rk G j x) + 1
      ≤ ∑ j : N, ∑ x ∈ s t j, rk G j x := by
    intro t ht
    obtain ⟨_, i, e, f, he, hf, hlt, hsw⟩ := hstep t ht
    have hY' : ∀ j, j ≠ i → s (t + 1) j = s t j := by
      intro j hj
      rw [hsw]
      simp [MatroidGame.swap, hj]
    have hYi : s (t + 1) i = insert f ((s t i).erase e) := by
      rw [hsw]
      simp [MatroidGame.swap]
    have h1 : (∑ j : N, ∑ x ∈ s (t + 1) j, rk G j x)
        = (∑ x ∈ s (t + 1) i, rk G i x) + ∑ j ∈ Finset.univ.erase i, ∑ x ∈ s t j, rk G j x := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [hY' j (Finset.ne_of_mem_erase hj)]
    have h2 : (∑ j : N, ∑ x ∈ s t j, rk G j x)
        = (∑ x ∈ s t i, rk G i x) + ∑ j ∈ Finset.univ.erase i, ∑ x ∈ s t j, rk G j x :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
    have h3 : (∑ x ∈ s (t + 1) i, rk G i x) = rk G i f + ∑ x ∈ (s t i).erase e, rk G i x := by
      rw [hYi, Finset.sum_insert (fun h => hf (Finset.mem_of_mem_erase h))]
    have h4 : (∑ x ∈ s t i, rk G i x) = rk G i e + ∑ x ∈ (s t i).erase e, rk G i x :=
      (Finset.add_sum_erase _ _ he).symm
    have h5 := rk_lt G i e f hlt
    rw [h1, h2, h3, h4]
    omega
  have hall : ∀ t ≤ k, (∑ j : N, ∑ x ∈ s t j, rk G j x) + t
      ≤ ∑ j : N, ∑ x ∈ s 0 j, rk G j x := by
    intro t
    induction t with
    | zero => intro _; omega
    | succ t ih =>
      intro ht
      have a := hdec t (by omega)
      have b := ih (by omega)
      omega
  have hcard : ∀ j, (s 0 j).card = G.rank j := by
    intro j
    unfold MatroidGame.rank
    rw [← (hs0 j).encard_eq_eRank, Set.encard_coe_eq_coe_finsetCard, ENat.toNat_coe]
  have hΦ0 : (∑ j : N, ∑ x ∈ s 0 j, rk G j x) ≤ ∑ j : N, G.rank j * (Fintype.card E - 1) := by
    apply Finset.sum_le_sum
    intro j _
    calc (∑ x ∈ s 0 j, rk G j x) ≤ ∑ x ∈ s 0 j, (Fintype.card E - 1) :=
          Finset.sum_le_sum (fun x _ => rk_le G j x)
      _ = G.rank j * (Fintype.card E - 1) := by
          rw [Finset.sum_const, smul_eq_mul, hcard j]
  have hle : ∀ j, G.rank j ≤ G.rkMax := by
    intro j
    unfold MatroidGame.rkMax
    exact Finset.le_sup (f := fun i => G.rank i) (Finset.mem_univ j)
  refine ⟨?_, ?_⟩
  · have := hall k le_rfl
    omega
  · calc ∑ i : N, G.rank i * (Fintype.card E - 1)
        ≤ ∑ _i : N, G.rkMax * Fintype.card E :=
          Finset.sum_le_sum (fun i _ => Nat.mul_le_mul (hle i) (Nat.sub_le _ _))
      _ = Fintype.card N * Fintype.card E * G.rkMax := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          ring
