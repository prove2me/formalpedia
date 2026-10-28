-- Prove2me | solution 1 for PrivateRelease.VCLowerBound.lemma_3_13
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T21:51:54.96021+00:00
-- url     : https://prove2.me/submissions/64209418-f39f-4a06-86e2-5960d4e28b83

import Mathlib
import Definitions.Def_PrivateRelease_VCLowerBound_Queries
import Definitions.Def_PrivateRelease_VCLowerBound_Construction

open MeasureTheory

namespace Aux_PrivateRelease_VCLowerBound_lemma_3_13

lemma card_symm {X : Type} [DecidableEq X] (A B : Finset X) :
    ((symmDiff A B).card : ℝ) + 2 * ((A ∩ B).card : ℝ) = A.card + B.card := by
  have h1 : (symmDiff A B).card = (A \ B).card + (B \ A).card := by
    rw [symmDiff_def, Finset.sup_eq_union]
    exact Finset.card_union_eq_card_add_card.2 disjoint_sdiff_sdiff
  have h2 := Finset.card_sdiff_add_card_inter A B
  have h3 := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at h3
  have : ((symmDiff A B).card : ℝ) = ((A \ B).card : ℝ) + ((B \ A).card : ℝ) := by
    exact_mod_cast h1
  have h2' : ((A \ B).card : ℝ) + ((A ∩ B).card : ℝ) = A.card := by exact_mod_cast h2
  have h3' : ((B \ A).card : ℝ) + ((A ∩ B).card : ℝ) = B.card := by exact_mod_cast h3
  linarith

end Aux_PrivateRelease_VCLowerBound_lemma_3_13

open Aux_PrivateRelease_VCLowerBound_lemma_3_13 in
open PrivateRelease.VCLowerBound in
theorem solution {X O : Type} [DecidableEq X] [MeasurableSpace O] (C : Set (X → Bool))
    (S : Finset X) (m : ℕ) (hS : S.card = 2 * m) (φ : Finset X → X → Bool)
    (hφC : ∀ T ∈ DS S m, φ T ∈ C) (hφ : ∀ T ∈ DS S m, IsIndicatorOn S T (φ T))
    (M : (Fin m → X) → Measure O) (ans : O → (X → Bool) → ℝ) (α δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hM : IsUseful C α δ M ans) (T : Finset X) (hT : T ∈ DS S m) (z : Fin m → X)
    (hz : IsEnum T z) :
    ENNReal.ofReal (1 - δ) ≤
      M z {o | ((symmDiff (reconstruct S m φ ans o) T).card : ℝ) ≤ 2 * (S.card : ℝ) * α} := by
  refine (hM z).trans (measure_mono ?_)
  intro o ho
  simp only [Set.mem_setOf_eq] at ho ⊢
  have hne : (DS S m).Nonempty := ⟨T, hT⟩
  unfold reconstruct
  rw [dif_pos hne]
  obtain ⟨hT'mem, hT'min⟩ := Classical.choose_spec
    (Finset.exists_min_image (DS S m) (fun T' => countQF (φ T') T' - ans o (φ T')) hne)
  set T' := Classical.choose
    (Finset.exists_min_image (DS S m) (fun T' => countQF (φ T') T' - ans o (φ T')) hne)
  have hmemDS : ∀ U, U ∈ DS S m → U ⊆ S ∧ U.card = m := fun U hU => Finset.mem_powersetCard.1 hU
  obtain ⟨hTS, hTc⟩ := hmemDS T hT
  obtain ⟨hT'S, hT'c⟩ := hmemDS T' hT'mem
  have hsymm := card_symm T' T
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have h1 : T = ∅ := Finset.card_eq_zero.1 hTc
    have h2 : T' = ∅ := Finset.card_eq_zero.1 hT'c
    rw [h1, h2]
    simp [hS]
  · have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hQF : ∀ U ∈ DS S m, countQF (φ U) U = 1 := by
      intro U hU
      obtain ⟨hUS, hUc⟩ := hmemDS U hU
      unfold countQF
      rw [Finset.filter_true_of_mem (fun x hx => ((hφ U hU) x (hUS hx)).2 hx), hUc]
      exact div_self hmR.ne'
    have hQ : ∀ U ∈ DS S m, countQ (φ U) z = ((U ∩ T).card : ℝ) / m := by
      intro U hU
      unfold countQ
      congr 2
      have himg : (Finset.univ.filter fun i => φ U (z i) = true).image z = U ∩ T := by
        ext x
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_inter]
        constructor
        · rintro ⟨i, hi, rfl⟩
          have hzT : z i ∈ T := (hz.2 (z i)).2 ⟨i, rfl⟩
          exact ⟨((hφ U hU) (z i) (hTS hzT)).1 hi, hzT⟩
        · rintro ⟨hxU, hxT⟩
          obtain ⟨i, rfl⟩ := (hz.2 x).1 hxT
          exact ⟨i, ((hφ U hU) (z i) (hTS hxT)).2 hxU, rfl⟩
      rw [← himg, Finset.card_image_of_injective _ hz.1]
    have hmin := hT'min T hT
    rw [hQF T hT, hQF T' hT'mem] at hmin
    have hgT := ho (φ T) (hφC T hT)
    have hgT' := ho (φ T') (hφC T' hT'mem)
    rw [hQ T hT, Finset.inter_self, hTc, div_self hmR.ne'] at hgT
    rw [hQ T' hT'mem] at hgT'
    rw [abs_le] at hgT hgT'
    have hint : (1 - 2 * α) * m ≤ ((T' ∩ T).card : ℝ) := by
      have : 1 - 2 * α ≤ ((T' ∩ T).card : ℝ) / m := by linarith [hgT.1, hgT'.2]
      rwa [le_div_iff₀ hmR] at this
    rw [hT'c, hTc] at hsymm
    rw [hS]
    push_cast
    nlinarith
