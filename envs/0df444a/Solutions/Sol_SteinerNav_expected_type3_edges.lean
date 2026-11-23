-- Prove2me | solution 1 for SteinerNav.expected_type3_edges
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:03:09.785603+00:00
-- url     : https://prove2.me/submissions/8591ea0c-c6e7-45c1-99b1-701a8b0d5a4b

import Mathlib
import Definitions.Def_SteinerNav_constructionEdges
import Theorems.Thm_SteinerNav_expected_gap

open SteinerNav

namespace AuxType3

open scoped Classical in
lemma card_type3_eq_sum {d : ℕ} (P Q : Finset (Pt d)) :
    ((type3Edges P Q).card : ℝ) =
      ∑ t ∈ P, ((P.filter fun s => s ≠ t ∧ ∀ q ∈ Q, dist s t < dist q t).card : ℝ) := by
  have h1 : (type3Edges P Q).card =
      ∑ t ∈ P, (P.filter fun s => s ≠ t ∧ ∀ q ∈ Q, dist s t < dist q t).card := by
    unfold type3Edges
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product_right]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
  exact_mod_cast h1

open scoped Classical in
lemma sum_target_le {d : ℕ} (P : Finset (Pt d)) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.card)
    (t : Pt d) :
    (∑ Q ∈ P.powersetCard m,
        ((P.filter fun s => s ≠ t ∧ ∀ q ∈ Q, dist s t < dist q t).card : ℝ)) ≤
      ((P.powersetCard m).card : ℝ) * (((P.card : ℝ) - m) / ((m : ℝ) + 1)) := by
  let n : ℕ := P.card
  let e₀ : Fin n ≃ {x // x ∈ P} := P.equivFin.symm
  let σ : Equiv.Perm (Fin n) := Tuple.sort (fun i : Fin n => dist (e₀ i).1 t)
  let f : Fin n ≃ {x // x ∈ P} := σ.trans e₀
  have hmono : Monotone (fun i : Fin n => dist (f i).1 t) :=
    Tuple.monotone_sort (fun i : Fin n => dist (e₀ i).1 t)
  let g : ℕ → Pt d := fun i => if hi : i < n then (f ⟨i, hi⟩).1 else t
  have hg_inj : Set.InjOn g (Finset.range n) := by
    intro i hi j hj hij
    have hi' : i < n := Finset.mem_range.mp (Finset.mem_coe.mp hi)
    have hj' : j < n := Finset.mem_range.mp (Finset.mem_coe.mp hj)
    dsimp [g] at hij
    rw [dif_pos hi', dif_pos hj'] at hij
    have hfeq : f ⟨i, hi'⟩ = f ⟨j, hj'⟩ := Subtype.ext hij
    have hfin : (⟨i, hi'⟩ : Fin n) = ⟨j, hj'⟩ := f.injective hfeq
    exact congrArg Fin.val hfin
  have hg_img : (Finset.range n).image g = P := by
    ext x
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      dsimp [g]
      rw [dif_pos hi]
      exact (f ⟨i, hi⟩).2
    · intro hx
      let k : Fin n := f.symm ⟨x, hx⟩
      refine ⟨k.1, k.2, ?_⟩
      dsimp [g]
      simp [k.2, k]
  have hbij : ∑ Q ∈ P.powersetCard m,
        ((P.filter fun s => s ≠ t ∧ ∀ q ∈ Q, dist s t < dist q t).card : ℝ) =
      ∑ I ∈ (Finset.range n).powersetCard m,
        ((P.filter fun s => s ≠ t ∧ ∀ q ∈ I.image g, dist s t < dist q t).card : ℝ) := by
    symm
    refine Finset.sum_bij (fun I _ => I.image g) ?_ ?_ ?_ ?_
    · intro I hI
      obtain ⟨hIsub, hIcard⟩ := Finset.mem_powersetCard.mp hI
      refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
      · rw [← hg_img]
        exact Finset.image_subset_image hIsub
      · rw [Finset.card_image_of_injOn (hg_inj.mono (Finset.coe_subset.mpr hIsub)), hIcard]
    · intro I₁ hI₁ I₂ hI₂ heq
      have hsub₁ := (Finset.mem_powersetCard.mp hI₁).1
      have hsub₂ := (Finset.mem_powersetCard.mp hI₂).1
      ext a
      constructor
      · intro ha
        have hga : g a ∈ I₂.image g := heq ▸ Finset.mem_image_of_mem g ha
        obtain ⟨b, hb, hgb⟩ := Finset.mem_image.mp hga
        have hba : b = a := hg_inj (hsub₂ hb) (hsub₁ ha) hgb
        exact hba ▸ hb
      · intro ha
        have hga : g a ∈ I₁.image g := heq.symm ▸ Finset.mem_image_of_mem g ha
        obtain ⟨b, hb, hgb⟩ := Finset.mem_image.mp hga
        have hba : b = a := hg_inj (hsub₁ hb) (hsub₂ ha) hgb
        exact hba ▸ hb
    · intro Q hQ
      obtain ⟨hQsub, hQcard⟩ := Finset.mem_powersetCard.mp hQ
      let I : Finset ℕ := (Finset.range n).filter fun i => g i ∈ Q
      have hIsub : I ⊆ Finset.range n := Finset.filter_subset _ _
      have hIimg : I.image g = Q := by
        ext x
        simp only [I, Finset.mem_image, Finset.mem_filter]
        constructor
        · rintro ⟨i, ⟨_, hgi⟩, rfl⟩
          exact hgi
        · intro hxQ
          have hxP : x ∈ (Finset.range n).image g := hg_img.symm ▸ hQsub hxQ
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxP
          exact ⟨i, ⟨hi, hxQ⟩, rfl⟩
      have hIcard : I.card = m := by
        have hc := Finset.card_image_of_injOn (hg_inj.mono (Finset.coe_subset.mpr hIsub))
        rw [hIimg, hQcard] at hc
        exact hc.symm
      exact ⟨I, Finset.mem_powersetCard.mpr ⟨hIsub, hIcard⟩, hIimg⟩
    · intro _ _
      rfl
  rw [hbij]
  have hterm : ∀ I ∈ (Finset.range n).powersetCard m,
      ((P.filter fun s => s ≠ t ∧ ∀ q ∈ I.image g, dist s t < dist q t).card : ℝ) ≤
        (((Finset.range n).filter fun i => ∀ q ∈ I, i < q).card : ℝ) := by
    intro I hI
    have hIsub := (Finset.mem_powersetCard.mp hI).1
    have hsub : (P.filter fun s => s ≠ t ∧ ∀ q ∈ I.image g, dist s t < dist q t) ⊆
        ((Finset.range n).filter fun i => ∀ q ∈ I, i < q).image g := by
      intro s hs
      obtain ⟨hsP, _, hlt_all⟩ := Finset.mem_filter.mp hs
      rw [← hg_img] at hsP
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hsP
      have hi_lt : i < n := Finset.mem_range.mp hi
      refine Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, ?_⟩, rfl⟩
      intro j hj
      have hj_lt : j < n := Finset.mem_range.mp (hIsub hj)
      have hdist_lt : dist (g i) t < dist (g j) t :=
        hlt_all (g j) (Finset.mem_image_of_mem g hj)
      dsimp [g] at hdist_lt
      rw [dif_pos hi_lt, dif_pos hj_lt] at hdist_lt
      by_contra hnot_lt
      have hji : (⟨j, hj_lt⟩ : Fin n) ≤ ⟨i, hi_lt⟩ := Fin.mk_le_mk.mpr (Nat.le_of_not_lt hnot_lt)
      exact not_lt_of_ge (hmono hji) hdist_lt
    have hcard_nat : (P.filter fun s => s ≠ t ∧ ∀ q ∈ I.image g, dist s t < dist q t).card ≤
        ((Finset.range n).filter fun i => ∀ q ∈ I, i < q).card :=
      le_trans (Finset.card_le_card hsub) Finset.card_image_le
    exact_mod_cast hcard_nat
  have hsum_le : ∑ I ∈ (Finset.range n).powersetCard m,
        ((P.filter fun s => s ≠ t ∧ ∀ q ∈ I.image g, dist s t < dist q t).card : ℝ) ≤
      ∑ I ∈ (Finset.range n).powersetCard m,
        (((Finset.range n).filter fun i => ∀ q ∈ I, i < q).card : ℝ) :=
    Finset.sum_le_sum hterm
  have hgap := SteinerNav.expected_gap n m hm hmn
  have hchoose_pos : (0 : ℝ) < (n.choose m : ℝ) := by exact_mod_cast Nat.choose_pos hmn
  have hgap_mul : ∑ I ∈ (Finset.range n).powersetCard m,
        (((Finset.range n).filter fun i => ∀ q ∈ I, i < q).card : ℝ) =
      (n.choose m : ℝ) * (((n : ℝ) - m) / ((m : ℝ) + 1)) := by
    rw [div_eq_iff (ne_of_gt hchoose_pos)] at hgap
    linarith
  have hpcard : ((P.powersetCard m).card : ℝ) = (n.choose m : ℝ) := by
    rw [Finset.card_powersetCard]
  rw [hpcard, ← hgap_mul]
  exact hsum_le

end AuxType3

open scoped Classical in
theorem solution {d : ℕ} (P : Finset (Pt d)) (hn : 2 ≤ P.card) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.card) :
    (∑ Q ∈ P.powersetCard m, ((type3Edges P Q).card : ℝ)) / ((P.powersetCard m).card : ℝ) ≤
        (P.card : ℝ) * ((P.card : ℝ) - m) / ((m : ℝ) + 1) ∧
      (P.card : ℝ) * ((P.card : ℝ) - m) / ((m : ℝ) + 1) ≤ (P.card : ℝ) ^ 2 / (m : ℝ) ∧
      (3 / 4 : ℝ) * ((P.powersetCard m).card : ℝ) ≤
        (((P.powersetCard m).filter fun Q =>
          ((type3Edges P Q).card : ℝ) ≤ 4 * (P.card : ℝ) ^ 2 / (m : ℝ)).card : ℝ) := by
  let U : Finset (Finset (Pt d)) := P.powersetCard m
  have hU_pos : (0 : ℝ) < (U.card : ℝ) := by
    dsimp [U]
    rw [Finset.card_powersetCard]
    exact_mod_cast Nat.choose_pos hmn
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm1_pos : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hn_pos : (0 : ℝ) < (P.card : ℝ) := by exact_mod_cast (show 0 < P.card by omega)
  have h1 : (∑ Q ∈ U, ((type3Edges P Q).card : ℝ)) / (U.card : ℝ) ≤
      (P.card : ℝ) * ((P.card : ℝ) - m) / ((m : ℝ) + 1) := by
    have hswap : ∑ Q ∈ U, ((type3Edges P Q).card : ℝ) =
        ∑ t ∈ P, ∑ Q ∈ U, ((P.filter fun s => s ≠ t ∧ ∀ q ∈ Q, dist s t < dist q t).card : ℝ) := by
      calc ∑ Q ∈ U, ((type3Edges P Q).card : ℝ)
          = ∑ Q ∈ U, ∑ t ∈ P, ((P.filter fun s => s ≠ t ∧ ∀ q ∈ Q, dist s t < dist q t).card : ℝ) :=
            Finset.sum_congr rfl fun Q _ => AuxType3.card_type3_eq_sum P Q
        _ = ∑ t ∈ P, ∑ Q ∈ U, ((P.filter fun s => s ≠ t ∧ ∀ q ∈ Q, dist s t < dist q t).card : ℝ) :=
            Finset.sum_comm
    have hsum_P : ∑ t ∈ P, ∑ Q ∈ U,
          ((P.filter fun s => s ≠ t ∧ ∀ q ∈ Q, dist s t < dist q t).card : ℝ) ≤
        ∑ _t ∈ P, (U.card : ℝ) * (((P.card : ℝ) - m) / ((m : ℝ) + 1)) :=
      Finset.sum_le_sum fun t _ => AuxType3.sum_target_le P m hm hmn t
    rw [Finset.sum_const, nsmul_eq_mul] at hsum_P
    rw [div_le_iff₀ hU_pos, hswap]
    calc ∑ t ∈ P, ∑ Q ∈ U, ((P.filter fun s => s ≠ t ∧ ∀ q ∈ Q, dist s t < dist q t).card : ℝ)
        ≤ (P.card : ℝ) * ((U.card : ℝ) * (((P.card : ℝ) - m) / ((m : ℝ) + 1))) := hsum_P
      _ = (P.card : ℝ) * ((P.card : ℝ) - m) / ((m : ℝ) + 1) * (U.card : ℝ) := by ring
  have h2 : (P.card : ℝ) * ((P.card : ℝ) - m) / ((m : ℝ) + 1) ≤ (P.card : ℝ) ^ 2 / (m : ℝ) := by
    rw [div_le_div_iff₀ hm1_pos hm_pos]
    have hnn : 0 ≤ (P.card : ℝ) * (m : ℝ) ^ 2 := by positivity
    nlinarith
  refine ⟨h1, h2, ?_⟩
  let G : Finset (Finset (Pt d)) :=
    U.filter fun Q => ((type3Edges P Q).card : ℝ) ≤ 4 * (P.card : ℝ) ^ 2 / (m : ℝ)
  let B : Finset (Finset (Pt d)) := U \ G
  have hGB_card : B.card + G.card = U.card :=
    Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  have hGB_real : (G.card : ℝ) + (B.card : ℝ) = (U.card : ℝ) := by
    have hc : (B.card : ℝ) + (G.card : ℝ) = (U.card : ℝ) := by exact_mod_cast hGB_card
    linarith
  have hB_sum : (B.card : ℝ) * (4 * (P.card : ℝ) ^ 2 / (m : ℝ)) ≤
      ∑ Q ∈ B, ((type3Edges P Q).card : ℝ) := by
    calc (B.card : ℝ) * (4 * (P.card : ℝ) ^ 2 / (m : ℝ))
        = ∑ _Q ∈ B, (4 * (P.card : ℝ) ^ 2 / (m : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ Q ∈ B, ((type3Edges P Q).card : ℝ) := by
          refine Finset.sum_le_sum fun Q hQ => ?_
          obtain ⟨hQU, hQG⟩ := Finset.mem_sdiff.mp hQ
          have hnot : ¬ (((type3Edges P Q).card : ℝ) ≤ 4 * (P.card : ℝ) ^ 2 / (m : ℝ)) :=
            fun hle => hQG (Finset.mem_filter.mpr ⟨hQU, hle⟩)
          linarith
  have hBU_sum : ∑ Q ∈ B, ((type3Edges P Q).card : ℝ) ≤ ∑ Q ∈ U, ((type3Edges P Q).card : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ => by positivity
  have hU_sum : ∑ Q ∈ U, ((type3Edges P Q).card : ℝ) ≤ ((P.card : ℝ) ^ 2 / (m : ℝ)) * (U.card : ℝ) :=
    (div_le_iff₀ hU_pos).mp (le_trans h1 h2)
  have h4pos : 0 < 4 * (P.card : ℝ) ^ 2 / (m : ℝ) := by positivity
  have hB_chain : (B.card : ℝ) * (4 * (P.card : ℝ) ^ 2 / (m : ℝ)) ≤
      (1 / 4 : ℝ) * (U.card : ℝ) * (4 * (P.card : ℝ) ^ 2 / (m : ℝ)) := by
    have hrhs : ((P.card : ℝ) ^ 2 / (m : ℝ)) * (U.card : ℝ) =
        (1 / 4 : ℝ) * (U.card : ℝ) * (4 * (P.card : ℝ) ^ 2 / (m : ℝ)) := by ring
    linarith
  have hB_le : (B.card : ℝ) ≤ (1 / 4 : ℝ) * (U.card : ℝ) :=
    le_of_mul_le_mul_right hB_chain h4pos
  linarith
