-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MinimalPrimeHomog_proof_bf27ffa11a53
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:24.107121+00:00
-- url     : https://prove2.me/submissions/deb3a623-6191-4576-99c0-976b56993567

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PMinimalPrimeHomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isHomogIdeal_iff_isHomogeneous_degree_aea066f22143

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GroundTheory.Heights₂.Heights
namespace MinimalPrimeHomog
theorem _root_.solution : MinimalPrimeHomog.Statement := by
  intro F _ n J W hJ hW
  rw [isHomogIdeal_iff_isHomogeneous_degree] at hJ ⊢
  have hWp : W.IsPrime := hW.1.1
  have hcore : (W.homogeneousCore (homogeneousSubmodule (Fin n) F)).toIdeal = W := by
    apply le_antisymm (Ideal.toIdeal_homogeneousCore_le _ _)
    refine hW.2 ⟨hWp.homogeneousCore, ?_⟩ (Ideal.toIdeal_homogeneousCore_le _ _)
    exact hJ.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hW.1.2)
  rw [← hcore]
  exact (W.homogeneousCore _).isHomogeneous
end MinimalPrimeHomog
end GroundTheory.Heights₂.Heights
