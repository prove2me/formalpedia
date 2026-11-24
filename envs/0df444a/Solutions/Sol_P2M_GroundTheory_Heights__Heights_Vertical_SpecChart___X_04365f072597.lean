-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___X_04365f072597
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:57.29504+00:00
-- url     : https://prove2.me/submissions/03c61eae-b870-4359-8dbb-be814b145c99

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartIso

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
theorem _root_.solution (hj : toSecB e I v (X j) ∉ 𝔫) (y : FreePar e j) : Φ hj (X y) = parB e 𝔫 (FreePar.val e j y) :=
  eval₂Hom_X' _ _ _
end GroundTheory.Heights₂.Heights.Vertical.SpecChart
