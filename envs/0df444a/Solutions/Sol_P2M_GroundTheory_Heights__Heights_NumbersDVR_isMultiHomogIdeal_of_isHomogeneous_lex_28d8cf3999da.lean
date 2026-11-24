-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_of_isHomogeneous_lex_28d8cf3999da
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:44.475722+00:00
-- url     : https://prove2.me/submissions/9f64656b-7e25-423e-8f1d-295dd1f57708

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_comp_addMonoidHom_c2a78c747026
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_lexRelabel_injective_9aa4aa668bcb

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
variable {K : Type} [Fintype K] {ι : K → Type} {R : Type*} [CommRing R]
variable [DecidableEq K] [DecidableEq (Lex (Fin (Fintype.card K) → ℕ))]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (e : K ≃ Fin (Fintype.card K))
    {I : Ideal (MRing ι R)}
    (hI : letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v))
      I.IsHomogeneous (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))) :
    IsMultiHomogIdeal I := by
  letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v))
  intro f hf b
  rw [← weightedHomogeneousComponent_comp_addMonoidHom _ (lexRelabel_injective e)]
  exact weightedHomogeneousComponent_mem_of_mem R _ hI hf _
end GroundTheory.Heights₂.Heights.NumbersDVR
