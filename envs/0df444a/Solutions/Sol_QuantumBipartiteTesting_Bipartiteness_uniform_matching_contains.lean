-- Prove2me | solution 1 for QuantumBipartiteTesting.Bipartiteness.uniform_matching_contains
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T14:48:36.302944+00:00
-- url     : https://prove2.me/submissions/70dd380c-8f24-483e-b469-31fc91ba2e61

-- Matching-count argument adapted from the accepted Prove2Me proof of
-- BordenaveCollins.tendsto_expFix, submission 27ec2b7d-adb9-48ae-aa0c-5fe28fdd5865,
-- BordenaveCollins.PartC (Apache 2.0 public contribution).
import Definitions.Def_DerandSq_PM
import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction

namespace QuantumBipartiteTesting.Bipartiteness.MatchingCountProof
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable Classical.decEq
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

private def PMat {N : ℕ} (E : Finset (Sym2 (Fin N))) : Prop :=
  (∀ p ∈ E, ¬ p.IsDiag) ∧ ∀ p ∈ E, ∀ q ∈ E, (∃ x, x ∈ p ∧ x ∈ q) → p = q


variable {N : ℕ}

/-- The matching `σ` contains the pairs of `E`. -/
private def Cont (E : Finset (Sym2 (Fin N))) (σ : DerandSq.PM N) : Prop :=
  ∀ a b, s(a, b) ∈ E → σ.1 a = b

/-- The number of perfect matchings containing `E`. -/
private def cnt (E : Finset (Sym2 (Fin N))) : ℕ :=
  (univ.filter fun σ : DerandSq.PM N => Cont E σ).card

/-- The points covered by `E`. -/
private def supp (E : Finset (Sym2 (Fin N))) : Finset (Fin N) :=
  univ.filter fun x => ∃ y, s(x, y) ∈ E

private lemma mem_supp (E : Finset (Sym2 (Fin N))) (x : Fin N) : x ∈ supp E ↔ ∃ y, s(x, y) ∈ E := by
  simp [supp]

private lemma cont_insert (E : Finset (Sym2 (Fin N))) (a b : Fin N) (σ : DerandSq.PM N) :
    Cont (insert s(a, b) E) σ ↔ σ.1 a = b ∧ Cont E σ := by
  constructor
  · intro h
    exact ⟨h a b (mem_insert_self _ _), fun x y hxy => h x y (mem_insert_of_mem hxy)⟩
  · rintro ⟨hab, h⟩ x y hxy
    rcases mem_insert.1 hxy with e | e
    · rcases Sym2.eq_iff.1 e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hab
      · rw [← hab]; exact (σ.2 y).1
    · exact h x y e

private lemma cnt_eq_sum (E : Finset (Sym2 (Fin N))) (a : Fin N) :
    cnt E = ∑ b, cnt (insert s(a, b) E) := by
  unfold cnt
  rw [card_eq_sum_card_fiberwise (f := fun σ : DerandSq.PM N => σ.1 a) (t := univ)
    (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun b _ => ?_
  congr 1
  ext σ
  simp only [mem_filter, mem_univ, true_and, cont_insert]
  tauto

/-- Conjugation of a perfect matching by a permutation. -/
private def conjPM (π : Equiv.Perm (Fin N)) (σ : DerandSq.PM N) : DerandSq.PM N :=
  ⟨π * σ.1 * π⁻¹, fun x => by
    refine ⟨?_, ?_⟩
    · have h1 := fun y => (σ.2 y).1
      simp [h1]
    · simp only [Equiv.Perm.mul_apply]
      intro h
      apply (σ.2 (π⁻¹ x)).2
      have := congrArg (fun y => π⁻¹ y) h
      simpa using this⟩

private lemma conjPM_apply (π : Equiv.Perm (Fin N)) (σ : DerandSq.PM N) (x : Fin N) :
    (conjPM π σ).1 x = π (σ.1 (π⁻¹ x)) := rfl

private lemma conjPM_conjPM (π : Equiv.Perm (Fin N)) (hπ : π⁻¹ = π) (σ : DerandSq.PM N) :
    conjPM π (conjPM π σ) = σ := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  rw [conjPM_apply, conjPM_apply]
  have h1 : ∀ y, π (π y) = y := fun y =>
    calc π (π y) = π⁻¹ (π y) := by rw [hπ]
      _ = y := by simp
  rw [hπ, h1, h1]

private lemma cont_conj (E : Finset (Sym2 (Fin N))) (a b b' : Fin N) (hb : b ≠ a) (hb' : b' ≠ a)
    (hbE : b ∉ supp E) (hbE' : b' ∉ supp E) (σ : DerandSq.PM N)
    (h : Cont (insert s(a, b) E) σ) :
    Cont (insert s(a, b') E) (conjPM (Equiv.swap b b') σ) := by
  rw [cont_insert] at h ⊢
  rw [mem_supp] at hbE hbE'
  push Not at hbE hbE'
  refine ⟨?_, ?_⟩
  · rw [conjPM_apply, Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne hb.symm hb'.symm, h.1]
    simp
  · intro x y hxy
    have hx1 : x ≠ b := by rintro rfl; exact hbE y hxy
    have hx2 : x ≠ b' := by rintro rfl; exact hbE' y hxy
    have hxy' : s(y, x) ∈ E := by rw [Sym2.eq_swap]; exact hxy
    have hy1 : y ≠ b := by rintro rfl; exact hbE x hxy'
    have hy2 : y ≠ b' := by rintro rfl; exact hbE' x hxy'
    rw [conjPM_apply, Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne hx1 hx2, h.2 x y hxy,
      Equiv.swap_apply_of_ne_of_ne hy1 hy2]

private lemma cnt_swap (E : Finset (Sym2 (Fin N))) (a b b' : Fin N) (hb : b ≠ a) (hb' : b' ≠ a)
    (hbE : b ∉ supp E) (hbE' : b' ∉ supp E) :
    cnt (insert s(a, b) E) = cnt (insert s(a, b') E) := by
  unfold cnt
  refine card_nbij' (conjPM (Equiv.swap b b')) (conjPM (Equiv.swap b b')) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
    exact cont_conj E a b b' hb hb' hbE hbE' σ hσ
  · intro σ hσ
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
    have := cont_conj E a b' b hb' hb hbE' hbE σ hσ
    rwa [Equiv.swap_comm] at this
  · intro σ _; exact conjPM_conjPM _ (Equiv.swap_inv _ _) σ
  · intro σ _; exact conjPM_conjPM _ (Equiv.swap_inv _ _) σ

private lemma cnt_bad (E : Finset (Sym2 (Fin N))) (a b : Fin N) (ha : a ∉ supp E)
    (hb : b = a ∨ b ∈ supp E) : cnt (insert s(a, b) E) = 0 := by
  unfold cnt
  rw [card_eq_zero, filter_eq_empty_iff]
  intro σ _ h
  rw [cont_insert] at h
  rcases hb with rfl | hb
  · exact (σ.2 b).2 h.1
  · obtain ⟨y, hy⟩ := (mem_supp E b).1 hb
    have h1 : σ.1 b = y := h.2 b y hy
    have h2 : σ.1 b = a := by rw [← h.1]; exact (σ.2 a).1
    apply ha
    rw [mem_supp]
    refine ⟨b, ?_⟩
    rw [Sym2.eq_swap, ← h2, h1]; exact hy

private lemma supp_insert (E : Finset (Sym2 (Fin N))) (a b : Fin N) :
    supp (insert s(a, b) E) = insert a (insert b (supp E)) := by
  ext x
  simp only [mem_supp, mem_insert]
  constructor
  · rintro ⟨y, e | e⟩
    · rcases Sym2.eq_iff.1 e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨y, e⟩)
  · rintro (rfl | rfl | ⟨y, hy⟩)
    · exact ⟨b, Or.inl rfl⟩
    · exact ⟨a, Or.inl Sym2.eq_swap⟩
    · exact ⟨y, Or.inr hy⟩

private lemma pmat_insert (E : Finset (Sym2 (Fin N))) (a b : Fin N) (h : PMat (insert s(a, b) E))
    (hn : s(a, b) ∉ E) : PMat E ∧ a ≠ b ∧ a ∉ supp E ∧ b ∉ supp E := by
  refine ⟨⟨fun p hp => h.1 p (mem_insert_of_mem hp), fun p hp q hq =>
    h.2 p (mem_insert_of_mem hp) q (mem_insert_of_mem hq)⟩, ?_, ?_, ?_⟩
  · intro e
    exact h.1 _ (mem_insert_self _ _) (Sym2.mk_isDiag_iff.2 e)
  · intro ha
    obtain ⟨y, hy⟩ := (mem_supp E a).1 ha
    have := h.2 _ (mem_insert_self _ _) _ (mem_insert_of_mem hy)
      ⟨a, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
    exact hn (this ▸ hy)
  · intro hb
    obtain ⟨y, hy⟩ := (mem_supp E b).1 hb
    have := h.2 _ (mem_insert_self _ _) _ (mem_insert_of_mem hy)
      ⟨b, Sym2.mem_mk_right _ _, Sym2.mem_mk_left _ _⟩
    exact hn (this ▸ hy)

private lemma card_supp (E : Finset (Sym2 (Fin N))) : PMat E → (supp E).card = 2 * E.card := by
  induction E using Finset.induction_on with
  | empty => intro _; simp [supp]
  | insert p E hp ih =>
    induction p using Sym2.inductionOn with
    | hf a b =>
      intro h
      obtain ⟨hE, hab, ha, hb⟩ := pmat_insert E a b h hp
      rw [supp_insert, card_insert_of_notMem, card_insert_of_notMem hb, ih hE,
        card_insert_of_notMem hp]
      · ring
      · simp [hab, ha]

private lemma two_mul_card_le (E : Finset (Sym2 (Fin N))) (h : PMat E) : 2 * E.card ≤ N := by
  rw [← card_supp E h]
  exact (card_le_univ _).trans (Fintype.card_fin N).le

private lemma cnt_mul (E : Finset (Sym2 (Fin N))) :
    PMat E → cnt E * ∏ l ∈ range E.card, (N - 2 * l - 1) = Fintype.card (DerandSq.PM N) := by
  induction E using Finset.induction_on with
  | empty =>
    intro _
    simp [cnt, Cont]
  | insert p E hp ih =>
    induction p using Sym2.inductionOn with
    | hf a b =>
      intro h
      obtain ⟨hE, hab, ha, hb⟩ := pmat_insert E a b h hp
      have hV : cnt E = (N - 2 * E.card - 1) * cnt (insert s(a, b) E) := by
        rw [cnt_eq_sum E a, ← sum_subset (subset_univ (univ \ insert a (supp E)))]
        · rw [sum_congr rfl (g := fun _ => cnt (insert s(a, b) E)), sum_const, smul_eq_mul]
          · congr 1
            rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin,
              card_insert_of_notMem ha, card_supp E hE]
            omega
          · intro b' hb'
            simp only [mem_sdiff, mem_univ, true_and, mem_insert, not_or] at hb'
            exact cnt_swap E a b' b hb'.1 (Ne.symm hab) hb'.2 hb
        · intro b' _ hb'
          simp only [mem_sdiff, mem_univ, true_and, mem_insert, not_not] at hb'
          exact cnt_bad E a b' ha hb'
      rw [card_insert_of_notMem hp, prod_range_succ, ← ih hE, hV]
      ring

private lemma cnt_not_pmat (E : Finset (Sym2 (Fin N))) (h : ¬ PMat E) : cnt E = 0 := by
  unfold cnt
  rw [card_eq_zero, filter_eq_empty_iff]
  intro σ _ hσ
  apply h
  refine ⟨fun p hp => ?_, fun p hp q hq => ?_⟩
  · induction p using Sym2.inductionOn with
    | hf a b =>
      rw [Sym2.mk_isDiag_iff]
      intro e
      have := hσ a b hp
      rw [← e] at this
      exact (σ.2 a).2 this
  · induction p using Sym2.inductionOn with
    | hf a b =>
      induction q using Sym2.inductionOn with
      | hf a' b' =>
        rintro ⟨x, hx, hx'⟩
        have h1 := hσ a b hp
        have h2 := hσ a' b' hq
        have h3 : σ.1 b = a := by rw [← h1]; exact (σ.2 a).1
        have h4 : σ.1 b' = a' := by rw [← h2]; exact (σ.2 a').1
        rw [Sym2.eq_iff]
        rcases Sym2.mem_iff.1 hx with rfl | rfl <;> rcases Sym2.mem_iff.1 hx' with rfl | rfl
        · exact Or.inl ⟨rfl, h1.symm.trans h2⟩
        · exact Or.inr ⟨rfl, h1.symm.trans h4⟩
        · exact Or.inr ⟨h3.symm.trans h2, rfl⟩
        · exact Or.inl ⟨h3.symm.trans h4, rfl⟩

private lemma prod_cast (k : ℕ) (hk : 2 * k ≤ N) :
    ((∏ l ∈ range k, (N - 2 * l - 1) : ℕ) : ℝ) = ∏ l ∈ range k, ((N : ℝ) - 2 * l - 1) := by
  rw [Nat.cast_prod]
  refine prod_congr rfl fun l hl => ?_
  have := mem_range.1 hl
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast; ring

private lemma prod_ne_zero' (k : ℕ) (hk : 2 * k ≤ N) :
    ∏ l ∈ range k, ((N : ℝ) - 2 * l - 1) ≠ 0 := by
  rw [← prod_cast k hk, Nat.cast_ne_zero, prod_ne_zero_iff]
  intro l hl
  have := mem_range.1 hl
  omega

private lemma cnt_real (E : Finset (Sym2 (Fin N))) (h : PMat E) :
    (cnt E : ℝ) = (Fintype.card (DerandSq.PM N) : ℝ) /
      ∏ l ∈ range E.card, ((N : ℝ) - 2 * l - 1) := by
  have h2 := two_mul_card_le E h
  rw [eq_div_iff (prod_ne_zero' _ h2), ← prod_cast _ h2, ← Nat.cast_mul, cnt_mul E h]

private lemma card_PM_ne_zero (hN : Even N) : Fintype.card (DerandSq.PM N) ≠ 0 := by
  obtain ⟨n, rfl⟩ := hN
  rw [← Nat.pos_iff_ne_zero, Fintype.card_pos_iff]
  refine ⟨⟨finSumFinEquiv.symm.trans ((Equiv.sumComm _ _).trans finSumFinEquiv), fun x => ?_⟩⟩
  refine ⟨?_, ?_⟩
  · simp
  · intro h
    have h' : (Equiv.sumComm (Fin n) (Fin n)) (finSumFinEquiv.symm x) = finSumFinEquiv.symm x := by
      apply finSumFinEquiv.injective
      simpa using h
    rcases hx : finSumFinEquiv.symm x with y | y <;> rw [hx] at h' <;> simp at h'

end
end QuantumBipartiteTesting.Bipartiteness.MatchingCountProof

open QuantumBipartiteTesting.Bipartiteness
open QuantumBipartiteTesting.Bipartiteness.MatchingCountProof
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution (N : ℕ) (hN : Even N) (E : Finset (Sym2 (Fin N)))
    (hloop : ∀ p ∈ E, ¬ p.IsDiag)
    (hdisj : ∀ p ∈ E, ∀ q ∈ E, (∃ x, x ∈ p ∧ x ∈ q) → p = q) :
    Average univ (fun σ : DerandSq.PM N => if ∀ a b, s(a,b) ∈ E → σ.val a = b then (1:ℝ) else 0) =
      ∏ a ∈ range E.card, ((N:ℝ)-2*a-1)⁻¹ := by
  have hE : PMat E := ⟨hloop,hdisj⟩
  have hcard : (Fintype.card (DerandSq.PM N):ℝ) ≠ 0 := by
    exact_mod_cast card_PM_ne_zero hN
  have heq : Average univ (fun σ : DerandSq.PM N => if ∀ a b, s(a,b) ∈ E → σ.val a = b then (1:ℝ) else 0) =
      (cnt E:ℝ)/(Fintype.card (DerandSq.PM N):ℝ) := by
    unfold Average cnt QuantumBipartiteTesting.Bipartiteness.MatchingCountProof.Cont
    simp only [card_univ]
    congr 1
    rw [← Finset.sum_filter]
    simp
  rw [heq,cnt_real E hE]
  rw [div_right_comm,div_self hcard,one_div,Finset.prod_inv_distrib]
end
