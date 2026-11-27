-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitCenterZero_proof_f29a9d7c5910
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:07:21.717416+00:00
-- url     : https://prove2.me/submissions/a5787ea8-2304-4cfe-91ca-0d553d99e936

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterMemIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PHeightRecR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCenterZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_coordVec_ne_zero_c6e0cd13558e


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
open ReciprocityTheory.ChartRestriction.G NumberField
namespace GroundTheory.Heights₂.Heights
namespace OrbitCenterZero
theorem _root_.solution (hLe : OrbitCenterLe.Statement)
    (hIff : OrbitCenterMemIff.Statement) (hDiv : OrbitCenterDivSupp.Statement) :
    OrbitCenterZero.Statement := by
  intro ι _ _ _ n A x s hx ⟨a, ha, hs, hsW⟩ v hv
  have hsc : s ∉ orbitCenter x v := fun h ↦ hv (hDiv ι n x s a hx hs hsW v h)
  have heq : v (evalCone (coordVec x) s) = ∏ k, (⨆ i, v (coordVec x k i)) ^ a k :=
    le_antisymm (hLe ι n x v s a hs) (not_lt.mp (mt (hIff ι n x hx v s a hs).mpr hsc))
  have hne : v (evalCone (coordVec x) s) ≠ 0 :=
    (FinitePlace.pos_iff.mpr (evalCone_coordVec_ne_zero x s a hs hsW)).ne'
  rw [heq] at hne ⊢
  rw [Real.log_prod (fun k _ ↦ Finset.prod_ne_zero_iff.mp hne k (Finset.mem_univ k)),
    finiteTerm, sub_eq_zero]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Real.log_pow, show (A.deg k : ℝ) = (a k : ℝ) by exact_mod_cast ha k]
end OrbitCenterZero
end GroundTheory.Heights₂.Heights
