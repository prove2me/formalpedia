-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_isMultigrading_ring_97b61877372f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:55:46.800272+00:00
-- url     : https://prove2.me/submissions/4487224a-8e77-4596-8f6d-e393377ef572

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u v
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {F : Type u} [Field F]
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution : IsMultigrading ι (MRing ι F) (ringPiece (F := F) (ι := ι)) where
  internal := (weightedDecomposition F (intWeight (ι := ι))).isInternal
  smul_mem := by
    intro v m x hx
    rw [smul_eq_mul]
    have hX : IsWeightedHomogeneous (intWeight (ι := ι)) (X v : MRing ι F) (unitDeg v.1) :=
      isWeightedHomogeneous_X F _ v
    have := hX.mul hx
    change X v * x ∈ weightedHomogeneousSubmodule F intWeight (m + unitDeg v.1)
    rw [mem_weightedHomogeneousSubmodule, add_comm]
    exact this
end GroundTheory.Heights₂.Heights.HilbertSamuel
