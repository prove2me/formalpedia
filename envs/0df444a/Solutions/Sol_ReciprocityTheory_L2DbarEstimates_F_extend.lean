-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:43:41.730553+00:00
-- url     : https://prove2.me/submissions/3d863fb7-2017-4a3d-aa1f-71ebe584594c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Extend
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_extend_support_subset
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_extend_eventuallyEq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : ExtendStatement n M := by
  intro z _hz e G he hG hGc hGt
  have hK : IsCompact (e.symm '' tsupport G) :=
    hGc.image_of_continuousOn (e.continuousOn_symm.mono hGt)
  have hKs : e.symm '' tsupport G ⊆ e.source := by
    rintro _ ⟨y, hy, rfl⟩; exact e.map_target (hGt hy)
  have hts : tsupport (e.source.indicator (G ∘ e)) ⊆ e.symm '' tsupport G :=
    closure_minimal (fun q hq => extend_support_subset e G q hq) hK.isClosed
  have hw : ∀ e'' : OpenPartialHomeomorph M (V n), IsChart n z e'' → ∀ x ∈ e''.source, x ∈ e.source →
      (e.source.indicator (G ∘ e) ∘ e''.symm) =ᶠ[𝓝 (z x)] G ∧ z x = e x := by
    intro e'' h1 x h2 hx
    have hzx : z x = e'' x := h1 h2
    refine ⟨?_, he hx⟩
    rw [hzx]
    refine extend_eventuallyEq z e e'' G he h1 (e'' x) (e''.map_source h2) ?_
    rw [e''.left_inv h2]; exact hx
  refine ⟨?_, hK.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hKs, ?_⟩
  · intro e' he' y hy
    by_cases hs : e'.symm y ∈ e.source
    · exact (hG.contDiffAt.congr_of_eventuallyEq
        (extend_eventuallyEq z e e' G he he' y hy hs)).contDiffWithinAt
    · have hq : e'.symm y ∉ tsupport (e.source.indicator (G ∘ e)) := fun h => hs (hKs (hts h))
      have h0 := notMem_tsupport_iff_eventuallyEq.1 hq
      have h0' := h0.comp_tendsto (e'.continuousAt_symm hy).tendsto
      exact (contDiffAt_const.congr_of_eventuallyEq h0').contDiffWithinAt
  · intro j x hx
    have key : ∀ e'' : OpenPartialHomeomorph M (V n), IsChart n z e'' → x ∈ e''.source →
        wd n j (e.source.indicator (G ∘ e) ∘ e''.symm) (z x) = wd n j G (e x) ∧
        wdb n j (e.source.indicator (G ∘ e) ∘ e''.symm) (z x) = wdb n j G (e x) := by
      intro e'' h1 h2
      obtain ⟨hev, hzx⟩ := hw e'' h1 x h2 hx
      constructor
      · unfold wd; rw [hev.fderiv_eq, hzx]
      · unfold wdb; rw [hev.fderiv_eq, hzx]
    have hex : ∃ e'' : OpenPartialHomeomorph M (V n), IsChart n z e'' ∧ x ∈ e''.source := ⟨e, he, hx⟩
    constructor
    · simp only [d, dif_pos hex]
      exact (key _ (Classical.choose_spec hex).1 (Classical.choose_spec hex).2).1
    · simp only [db, dif_pos hex]
      exact (key _ (Classical.choose_spec hex).1 (Classical.choose_spec hex).2).2
end ReciprocityTheory.L2DbarEstimates.F
