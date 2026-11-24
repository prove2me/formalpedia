-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_eval_conj_eq_zero_be975f9d4692
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:57.093798+00:00
-- url     : https://prove2.me/submissions/60afd6ea-d792-480f-a114-81da194d1db4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegree

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
variable {ι : Type} {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution [Fintype ι] [DecidableEq ι] (x : Cone n (AlgebraicClosure ℚ)) (σ : AlgebraicClosure ℚ →+* ℂ)
    {f : MvPolynomial (Coord n) ℤ} (hf : f ∈ orbitIdeal x) :
    eval (fun p ↦ σ (flatCone x p)) (map (Int.castRingHom ℂ) f) = 0 := by
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker] at hf
  have h : ∀ f : MvPolynomial (Coord n) ℤ,
      eval (fun p ↦ σ (flatCone x p)) (map (Int.castRingHom ℂ) f) =
        σ (eval (fun _ : ι ↦ (1 : AlgebraicClosure ℚ))
          (Geo.mConeMap (ι := blockIdx n) (flatCone x) f)) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [Geo.mConeMap]
    | add f g hf hg => simp only [map_add, hf, hg]
    | mul_X f p hf => simp only [map_mul, hf, eval_X, map_X, Geo.mConeMap, aeval_X, eval_C, mul_one]
  rw [h, hf, map_zero, map_zero]
end GroundTheory.Heights₂.Heights
