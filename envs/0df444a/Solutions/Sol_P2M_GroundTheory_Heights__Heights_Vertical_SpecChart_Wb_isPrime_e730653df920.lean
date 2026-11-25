-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_Wb_isPrime_e730653df920
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:23:26.962796+00:00
-- url     : https://prove2.me/submissions/387a9943-06f1-4de0-a59b-d8f6606a636f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartIso
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_map_mk_isPrime_117a21e5f9cd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_disjoint_powers_8cdf492256f5

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
namespace GroundTheory.Heights₂.Heights.Vertical.SpecChart
theorem _root_.solution [W.IsPrime] (hPW : integralModel I ≤ W) (hXj : X j ∉ W) : (Wb I j W).IsPrime :=
  have := map_mk_isPrime hPW
  IsLocalization.isPrime_of_isPrime_disjoint _ _ _ this (disjoint_powers j hPW hXj)
end GroundTheory.Heights₂.Heights.Vertical.SpecChart
