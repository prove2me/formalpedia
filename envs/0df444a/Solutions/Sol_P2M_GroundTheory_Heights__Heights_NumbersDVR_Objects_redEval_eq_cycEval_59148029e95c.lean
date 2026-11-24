-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_redEval_eq_cycEval_59148029e95c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:43.606816+00:00
-- url     : https://prove2.me/submissions/9a9b73f2-3684-4a0a-9325-2f56925ef88f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.Objects
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.Objects
theorem _root_.solution (J : Ideal (MRing ι (IsLocalRing.ResidueField O)) → ℤ)
    (Z : Ideal (MRing ι O) →₀ ℤ) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.redEval J Z =
      cycEval (fun W => J (specialIdeal W)) Z := by
  classical
  rw [GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.redEval, cycEval,
    finsum_eq_sum_of_support_subset _ (s := Z.support) fun W hW =>
      Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul (Function.mem_support.mp hW))]
  rfl
end GroundTheory.Heights₂.Heights.NumbersDVR.Objects
