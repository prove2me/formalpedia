-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ArithVariety_evalCone_chartPoint_cf5b16f39004
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:35:47.724216+00:00
-- url     : https://prove2.me/submissions/7b27e417-974f-4bf1-9e0a-fd2a9ad6dc1f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_DenseChart

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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.ArithVariety
variable (P : ArithVariety n)
variable (c : (k : ι) → Fin (n k + 1))
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.ArithVariety
theorem _root_.solution (ψ : P.ChartAlg c →ₐ[ℚ] AlgebraicClosure ℚ)
    (f : MvPolynomial (Coord n) ℤ) :
    evalCone (P.chartPoint c ψ) f =
      ψ ((P.chartMap c).rangeRestrict (map (Int.castRingHom ℚ) f)) := by
  set χ : MvPolynomial (Coord n) ℚ →ₐ[ℚ] AlgebraicClosure ℚ := ψ.comp (P.chartMap c).rangeRestrict
  change _ = χ (map (Int.castRingHom ℚ) f)
  rw [aeval_unique χ, aeval_def, eval₂_map, evalCone]
  congr 1
end GroundTheory.Heights₂.Heights.ArithVariety
