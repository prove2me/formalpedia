-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_isMultigraded_iff_isMultigrading_ac258fa1b81e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:32.831955+00:00
-- url     : https://prove2.me/submissions/e57926dd-2dcb-4e57-807f-6b43b20fe051

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ProjectiveSpaceIncrementHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_WeightedHomogeneousSubmoduleBlockWeightIntEqRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
  {M : Type*} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
theorem _root_.solution (ℳ : (K → ℤ) → Submodule F M) :
    IsMultigraded ι ℳ ↔ GroundTheory.Heights₂.Heights.HilbertSamuel.IsMultigrading ι M ℳ :=
  ⟨fun h => ⟨by convert h.internal, fun v m x hx => h.var_mul v m x hx⟩,
    fun h => ⟨by convert h.internal, fun v m x hx => h.smul_mem v m x hx⟩⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
