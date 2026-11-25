-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___cinv_mul_adb95d831303
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:23:27.565385+00:00
-- url     : https://prove2.me/submissions/45e14a87-dc9a-4150-8f5f-914832e34d0d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartIso
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_cinv_mul_cx_d1cdfb4307c6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___cx_89ebc424d343

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Vertical.SpecChart
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
  (j : Fin n)
variable (W : Ideal (MvPolynomial (Fin n) (𝓞 K)))
variable {I W}
variable {v : HeightOneSpectrum (𝓞 K)}
variable (𝔫 : Ideal (SecB e I v)) [𝔫.IsPrime]
variable {e j 𝔫}
namespace GroundTheory.Heights₂.Heights.Vertical.SpecChart
theorem _root_.solution (hj : toSecB e I v (X j) ∉ 𝔫) :
    Φ hj (cinv e I j) * algebraMap _ _ (toSecB e I v (X j)) = 1 := by
  rw [← Φ_cx hj, ← map_mul, cinv_mul_cx, map_one]
end GroundTheory.Heights₂.Heights.Vertical.SpecChart
