-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_finrank_gradedPiece_map_d80caa80bd95
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:13:23.965036+00:00
-- url     : https://prove2.me/submissions/6ec08fa8-a061-4199-95d5-2eb394fe4f6d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_monomial_6aa346b05c3c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_mem_0f251d0f8cfe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_gradedPiece_eq_span_bcb2fa78a226
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_sum_smul_mk_monomial_4718e7a55a19
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_monomials_of_multidegree_04d4ee134769

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Heights₂.Heights.FieldNumbers.coeff_coeffForm

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (I : Ideal (MRing ι F)) (m : K → ℕ) :
    Module.finrank F' (gradedPiece (I.map (map (algebraMap F F'))) m) =
      Module.finrank F (gradedPiece I m) := by
  classical
  have hsfin : {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m}.Finite :=
    finite_monomials_of_multidegree m
  obtain ⟨B, hBT, hBspan, hBind⟩ := exists_linearIndependent F
    ((fun d => Ideal.Quotient.mk I (monomial d (1 : F))) ''
      {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m})
  have hBfin : B.Finite := (hsfin.image _).subset hBT
  let : Fintype B := hBfin.fintype
  have hlift : ∀ x : B, ∃ d, d ∈ {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m} ∧
      Ideal.Quotient.mk I (monomial d (1 : F)) = x := fun x => hBT x.2
  choose lift hlift_s hlift_v using hlift
  have hF : Module.finrank F (gradedPiece I m) = Fintype.card B := by
    have h := finrank_span_eq_card hBind
    rw [Subtype.range_coe] at h
    rw [gradedPiece_eq_span, ← hBspan, h]
  have hind' : LinearIndependent F'
      (fun x : B => Ideal.Quotient.mk (I.map (map (algebraMap F F'))) (monomial (lift x) (1 : F'))) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg x
    have hg' : Ideal.Quotient.mk (I.map (map (algebraMap F F')))
        (∑ y, monomial (lift y) (g y)) = 0 := by
      rw [← sum_smul_mk_monomial]
      exact hg
    rw [Ideal.Quotient.eq_zero_iff_mem] at hg'
    rw [← Module.forall_dual_apply_eq_zero_iff F (g x)]
    intro φ
    have hmem := coeffForm_mem φ hg'
    rw [map_sum] at hmem
    simp only [coeffForm_monomial] at hmem
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← sum_smul_mk_monomial] at hmem
    simp only [hlift_v] at hmem
    exact Fintype.linearIndependent_iff.mp hBind (fun y => φ (g y)) hmem x
  have hspan' : Submodule.span F' (Set.range
      (fun x : B => Ideal.Quotient.mk (I.map (map (algebraMap F F'))) (monomial (lift x) (1 : F')))) =
      gradedPiece (I.map (map (algebraMap F F'))) m := by
    rw [gradedPiece_eq_span]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact Submodule.subset_span ⟨lift x, hlift_s x, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨d, hd, rfl⟩
      have hmem : Ideal.Quotient.mk I (monomial d (1 : F)) ∈
          Submodule.span F (Set.range ((↑) : B → MRing ι F ⧸ I)) := by
        rw [Subtype.range_coe, hBspan]
        exact Submodule.subset_span ⟨d, hd, rfl⟩
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hmem
      have hc' : ∑ x, c x • Ideal.Quotient.mk I (monomial (lift x) (1 : F)) =
          Ideal.Quotient.mk I (monomial d (1 : F)) := by
        simpa only [hlift_v] using hc
      rw [sum_smul_mk_monomial, Ideal.Quotient.eq] at hc'
      have h' := Ideal.mem_map_of_mem (map (algebraMap F F')) hc'
      rw [map_sub, map_sum] at h'
      simp only [map_monomial, map_one] at h'
      rw [← Ideal.Quotient.eq, ← sum_smul_mk_monomial] at h'
      rw [SetLike.mem_coe]
      beta_reduce
      rw [← h']
      exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  rw [← hspan', finrank_span_eq_card hind', hF]
end GroundTheory.Heights₂.Heights.FieldNumbers
