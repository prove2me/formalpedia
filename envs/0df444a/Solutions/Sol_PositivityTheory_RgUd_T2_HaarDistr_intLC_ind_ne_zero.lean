-- Prove2me | solution 1 for PositivityTheory.RgUd.T2.HaarDistr.intLC_ind_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:54:36.132864+00:00
-- url     : https://prove2.me/submissions/3b147308-5bc2-4878-b790-1bb6122ec996

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_PowNear
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_HaarDistr
import Theorems.Thm_PositivityTheory_RgUd_T2_HaarDistr_mulLC_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.RgUd.T2.HaarDistr.mulLC_apply

set_option autoImplicit false
noncomputable section
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob GroundTheory.Automorphic
open scoped Pointwise
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T2 PositivityTheory.RgUd.T2.HaarDistr
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable [MeasurableSpace G] [BorelSpace G]
namespace PositivityTheory.RgUd.T2.HaarDistr
theorem _root_.solution (μ : Measure G) [μ.IsHaarMeasure] (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) : intLC μ (ind K hK) ≠ 0 := by
  have hm : MeasurableSet (K : Set G) := K.isOpen.measurableSet
  have hpos : 0 < μ (K : Set G) := K.isOpen.measure_pos μ ⟨1, K.one_mem⟩
  have hfin : μ (K : Set G) ≠ ⊤ := hK.measure_lt_top.ne
  show ∫ x, (K : Set G).indicator (fun _ => (1 : ℂ)) x ∂μ ≠ 0
  rw [integral_indicator_const _ hm]
  simp only [measureReal_def, Complex.real_smul, mul_one, ne_eq, Complex.ofReal_eq_zero]
  exact (ENNReal.toReal_pos hpos.ne' hfin).ne'
end PositivityTheory.RgUd.T2.HaarDistr
