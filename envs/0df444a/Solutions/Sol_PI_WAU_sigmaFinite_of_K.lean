-- Prove2me | solution 1 for PI.WAU.sigmaFinite_of_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:15:16.899081+00:00
-- url     : https://prove2.me/submissions/6313922f-5a72-4b0f-ab23-016934b365fe

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_KCountable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularIndex_PairwiseDisjointCosets
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open Formalism.MainNotions.S MeasureTheory Matrix Pointwise
namespace PI.WAU
theorem _root_.solution (I : AutInst) (μ : Measure I.Gf) (hμ : μ.IsHaarMeasure)
    (hKc : IsCompact I.Kset) (hQ : ∃ s : Set I.Gf, s.Countable ∧ ∀ x : I.Gf, ∃ y ∈ s, y⁻¹ * x ∈ I.Kset) :
    SigmaFinite μ := by
  haveI := hμ
  obtain ⟨s, hs, hcov⟩ := hQ
  refine Measure.sigmaFinite_of_countable (S := (fun y => (fun x => y * x) '' I.Kset) '' s)
    (hs.image _) ?_ ?_
  · rintro _ ⟨y, -, rfl⟩
    show μ ((fun x => y * x) '' I.Kset) < ⊤
    rw [Set.image_mul_left, measure_preimage_mul]
    exact hKc.measure_lt_top
  · rw [Set.sUnion_image, Set.eq_univ_iff_forall]
    intro x
    obtain ⟨y, hy, hyx⟩ := hcov x
    exact Set.mem_biUnion hy ⟨y⁻¹ * x, hyx, mul_inv_cancel_left y x⟩
end PI.WAU
