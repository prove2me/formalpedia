-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_sigma_mem_points_5c3b047266ee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:39:45.816525+00:00
-- url     : https://prove2.me/submissions/e8131544-63b0-44c7-9eaa-fec379ed36cf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_map_d62ae25f8d4a

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
open MvPolynomial NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} (P : ArithVariety n)
    {x : Cone n (AlgebraicClosure ℚ)} (hx : x ∈ P.points (AlgebraicClosure ℚ))
    (σ : coordField x →+* ℂ) : (fun k i ↦ σ (coordVec x k i)) ∈ P.points ℂ := by
  refine ⟨fun k h ↦ hx.1 k ?_, fun f hf ↦ ?_⟩
  · funext i
    have h1 : σ (coordVec x k i) = 0 := congrFun h i
    have h2 : coordVec x k i = 0 := (map_eq_zero σ).mp h1
    exact congrArg Subtype.val h2
  · rw [evalCone_map σ (coordVec x) f]
    have h0 : evalCone x f = 0 := hx.2 f hf
    have h1 := evalCone_map (coordField x).val.toRingHom (coordVec x) f
    have h2 : evalCone (coordVec x) f = 0 := by
      apply (coordField x).val.toRingHom.injective
      rw [map_zero, ← h1]
      exact h0
    rw [h2, map_zero]
end GroundTheory.Heights₂.Heights
