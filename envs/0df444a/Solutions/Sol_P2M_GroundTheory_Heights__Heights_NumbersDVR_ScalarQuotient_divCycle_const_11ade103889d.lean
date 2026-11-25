-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_divCycle_const_11ade103889d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:14:33.20484+00:00
-- url     : https://prove2.me/submissions/11df9829-8c09-4709-a1c0-b8ff2624ee7e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PScalarQuotient
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_divCycle_unit_aedc5c616d81
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DivCycleMul_proof_5282581d8898


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient
theorem _root_.solution (P : Ideal (MRing ι O)) [P.IsPrime]
    (hP : ∀ a : O, a ≠ 0 → (C a : MRing ι O) ∉ P) {ϖ : O} (hϖ : ϖ ≠ 0) (u : Oˣ) (n : ℕ) :
    divCycle P (C ((u : O) * ϖ ^ n)) = fun W => (n : ℤ) * divCycle P (C ϖ) W := by
  induction n with
  | zero =>
    funext W
    simp [divCycle_unit]
  | succ n ih =>
    have hmul : (C ((u : O) * ϖ ^ (n + 1)) : MRing ι O) = C ((u : O) * ϖ ^ n) * C ϖ := by
      rw [← map_mul, pow_succ, mul_assoc]
    rw [hmul, DivCycleMul.proof O K ι P _ _ inferInstance
      (hP _ (mul_ne_zero u.ne_zero (pow_ne_zero _ hϖ))) (hP _ hϖ), ih]
    funext W
    simp only [Pi.add_apply]
    push_cast
    ring
end GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient
