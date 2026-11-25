-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_isPrime_map_ratFunc_3552ddc99f6c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:07:30.334022+00:00
-- url     : https://prove2.me/submissions/cfd2edbb-e8eb-4349-b9a5-5181f39bebb5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_map_ne_top_202927de85d4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isPrime_map_polynomial_6eef1ef7fe50
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
variable {σ : Type*} {F : Type*} [Field F]
attribute [local instance] MvPolynomial.algebraMvPolynomial
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (P : Ideal (MvPolynomial σ F)) [hP : P.IsPrime] :
    (P.map (map (algebraMap F (RatFunc F)) : MvPolynomial σ F →+* _)).IsPrime := by
  have hcomp : Ideal.map (algebraMap (MvPolynomial σ (Polynomial F)) (MvPolynomial σ (RatFunc F)))
      (P.map (map (algebraMap F (Polynomial F)) : MvPolynomial σ F →+* _)) =
      P.map (map (algebraMap F (RatFunc F)) : MvPolynomial σ F →+* _) := by
    rw [Ideal.map_map, MvPolynomial.algebraMap_def]
    congr 1
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, map_C, ← IsScalarTower.algebraMap_apply]
    · intro i
      simp only [RingHom.comp_apply, map_X]
  rw [← hcomp]
  refine IsLocalization.isPrime_of_isPrime_disjoint
    ((nonZeroDivisors (Polynomial F)).map (C (σ := σ))) (MvPolynomial σ (RatFunc F)) _
    (isPrime_map_polynomial P) ?_
  rw [Set.disjoint_left]
  rintro _ ⟨p, hp, rfl⟩ hmem
  apply map_ne_top (F' := RatFunc F) hP.ne_top
  rw [← hcomp]
  apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hmem)
  rw [MvPolynomial.algebraMap_def, map_C]
  exact (isUnit_iff_ne_zero.mpr
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hp)).map C
end GroundTheory.Heights₂.Heights.FieldNumbers
