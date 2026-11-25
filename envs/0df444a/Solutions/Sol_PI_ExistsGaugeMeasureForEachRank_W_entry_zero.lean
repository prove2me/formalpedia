-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.entry_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:56:13.208906+00:00
-- url     : https://prove2.me/submissions/7c077761-2e6f-4873-a2c1-bdcffb048aff

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_OfRealCoordsSmulCenterCoord
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_dgl_apply_off
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_eq_dgl


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open PI PI.ExistsGaugeMeasureForEachRank PI.ExistsGaugeMeasureForEachRank.W
variable {r : ℕ}
set_option backward.isDefEq.respectTransparency false
open scoped Norms.Operator
namespace PI.ExistsGaugeMeasureForEachRank.W
theorem _root_.solution {X : Mat 0 r} (hX : X ∈ lieOf (UWb 0 r)) (i j : Fin (2 * r + 0 + 1))
    (hij : ¬ (i = cI r ∧ j = cI r)) : X i j = 0 := by
  letI : NormedRing (Mat 0 r) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat 0 r) := Matrix.linftyOpNormedAlgebra
  have hconst : ∀ t : ℝ, (NormedSpace.exp (t • X)) i j = (1 : Mat 0 r) i j := by
    intro t
    have hm := hX t
    rw [Complex.coe_smul] at hm
    rw [eq_dgl hm, dgl_apply_off _ _ _ hij]
  let L : Mat 0 r →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  have hd := (L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp_smul_const X (0 : ℝ)))
  have hfun : (L ∘ fun t : ℝ => NormedSpace.exp (t • X)) = fun _ => (1 : Mat 0 r) i j :=
    funext hconst
  rw [hfun] at hd
  have h0 := hd.unique (hasDerivAt_const (0 : ℝ) ((1 : Mat 0 r) i j))
  simpa [L] using h0
end PI.ExistsGaugeMeasureForEachRank.W
