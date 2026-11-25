-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitConjSum_isWeightedHomogeneous_chartHomog_c0b2ddf82b13
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:45:51.095278+00:00
-- url     : https://prove2.me/submissions/cd3e49e5-5d88-4eb6-b20c-923372dec0db

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitConjSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitConjSumLemmas
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitConjSum_blockDeg_le_9e02025f8eb2

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitConjSum
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.OrbitConjSum
theorem _root_.solution (c : (k : ι) → Fin (n k + 1))
    (P : MvPolynomial (Coord n) ℤ) :
    IsWeightedHomogeneous (coordDeg n) (chartHomog c P) (fun _ ↦ P.totalDegree) := by
  apply (mem_weightedHomogeneousSubmodule _ _ _ _).mp
  refine Submodule.sum_mem _ fun m hm ↦ (mem_weightedHomogeneousSubmodule _ _ _ _).mpr ?_
  have h := (isWeightedHomogeneous_monomial (coordDeg n) m (P.coeff m) rfl).mul
    (isWeightedHomogeneous_chartMonomial c (fun k ↦ P.totalDegree - ∑ i, m ⟨k, i⟩))
  convert h using 1
  funext k
  rw [Pi.add_apply, weight_coordDeg_apply, Nat.add_sub_cancel' (blockDeg_le P hm k)]
end GroundTheory.Heights₂.Heights.OrbitConjSum
