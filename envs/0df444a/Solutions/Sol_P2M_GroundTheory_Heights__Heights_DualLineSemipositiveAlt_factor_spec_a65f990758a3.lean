-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualLineSemipositiveAlt_factor_spec_a65f990758a3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:01:16.683455+00:00
-- url     : https://prove2.me/submissions/c8a8fa17-0f9c-4fd4-9078-fb67346669ab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualLineSemipositive

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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix NumberField
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.DualLineSemipositiveAlt
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]
namespace GroundTheory.Heights₂.Heights.DualLineSemipositiveAlt
theorem _root_.solution (F : HermLattice K i) (σ : K →+* ℂ) :
    F.metric σ = (factor F σ)ᴴ * factor F σ :=
  Classical.choose_spec (exists_conjTranspose_mul_self (F.posDef σ).posSemidef)
end GroundTheory.Heights₂.Heights.DualLineSemipositiveAlt
