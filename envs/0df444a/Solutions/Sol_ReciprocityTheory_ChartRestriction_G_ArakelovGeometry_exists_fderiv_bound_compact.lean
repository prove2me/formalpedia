-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_fderiv_bound_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:41:55.209538+00:00
-- url     : https://prove2.me/submissions/d888ec12-87bc-4ee1-b111-31d9cf733bb1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsBoundIteratedFDerivCompact
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SectionBasisLocalUniformBound
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory
open scoped ContDiff
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {U K : Set (Fin D → ℂ)} (hU : IsOpen U) {ν : (Fin D → ℂ) → ℝ}
    (hν : ContDiffOn ℝ 1 ν U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ L : ℝ, ∀ y ∈ K, ‖fderiv ℝ ν y‖ ≤ L :=
  hK.exists_bound_of_continuousOn ((hν.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
