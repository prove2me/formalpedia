-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_evalCone_ne_zero_of_notMem_orbitIdeal_a02cd0c741c7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:39:35.445802+00:00
-- url     : https://prove2.me/submissions/deeaf9fa-4ae7-433f-a677-77e3e390afb0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartTerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartTerm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval__mul_block_of_isMultiHomog_db091611cf8f

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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
variable {ι : Type} [Fintype ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (x : Cone n (AlgebraicClosure ℚ))
    (s : MvPolynomial (Coord n) ℤ) (a : ι → ℕ) (hs : Geo.IsMultiHomog (ι := blockIdx n) s a)
    (hW : s ∉ orbitIdeal x) : evalCone x s ≠ 0 := by
  intro h0
  apply hW
  have hC : ∀ g : ℤ →+* MvPolynomial ι (AlgebraicClosure ℚ),
      eval₂ g (fun p ↦ C (flatCone x p)) s = C (evalCone x s) := fun g ↦ by
    rw [evalCone, eval₂_comp_left]
    congr 1
    exact RingHom.ext_int _ _
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_def,
    eval₂_mul_block_of_isMultiHomog s a hs _ (fun p ↦ C (flatCone x p)) X, hC, h0, map_zero,
    zero_mul]
end GroundTheory.Heights₂.Heights
