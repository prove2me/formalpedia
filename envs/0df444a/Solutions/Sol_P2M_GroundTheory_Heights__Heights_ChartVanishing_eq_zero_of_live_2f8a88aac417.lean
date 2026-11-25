-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartVanishing_eq_zero_of_live_2f8a88aac417
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:27:18.057195+00:00
-- url     : https://prove2.me/submissions/d622363e-2886-47c8-a831-a5dfc9c4bd52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroTer
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartVanishing_evalHom_apply_58ec575df9f4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartVanishing_cross_mem_of_live_a5ef6372da62
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartVanishing_evalCone_chartMonomial_ne_zero_0f3c784853ae

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
noncomputable section
open GroundTheory.Heights₂.Heights.ChartVanishing
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.ChartVanishing
theorem _root_.solution {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (hg : D.IsFormSystem d g) {z : Cone n ℂ} (hz : z ∈ P.points ℂ) {c : (k : ι) → Fin (n k + 1)}
    (hc : P.IsLive c) (hm : evalCone z (chartMonomial c d) = 0) (j : Fin (D.size + 1)) :
    evalCone z (g c j) = 0 := by
  have hex : ∀ k, ∃ i, z k i ≠ 0 := fun k ↦ Function.ne_iff.mp (hz.1 k)
  choose c' hc'z using hex
  have hlive : P.IsLive c' := fun k hk ↦ hc'z k (by
    have := hz.2 _ hk
    simpa [evalCone] using this)
  have hv := hz.2 _ (cross_mem_of_live hg hc hlive j)
  rw [← evalHom_apply, map_sub, map_mul, map_mul, evalHom_apply, evalHom_apply, evalHom_apply,
    evalHom_apply, hm, zero_mul, sub_zero] at hv
  exact (mul_eq_zero.mp hv).resolve_left (evalCone_chartMonomial_ne_zero hc'z d)
end GroundTheory.Heights₂.Heights.ChartVanishing
