-- Prove2me | solution 1 for PositivityTheory.RgUd.T2.HaarDistr.intLC_transl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:54:40.391736+00:00
-- url     : https://prove2.me/submissions/5474b444-8528-4b8b-aeab-84d8a2c1928a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_PowNear
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_HaarDistr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob GroundTheory.Automorphic
open scoped Pointwise
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T2 PositivityTheory.RgUd.T2.HaarDistr
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable [MeasurableSpace G] [BorelSpace G]
namespace PositivityTheory.RgUd.T2.HaarDistr
theorem _root_.solution (μ : Measure G) [μ.IsHaarMeasure] (g : G) (α : SB G) :
    intLC μ (transl g α) = intLC μ α :=
  integral_mul_left_eq_self (fun x => (α : G → ℂ) x) g⁻¹
end PositivityTheory.RgUd.T2.HaarDistr
