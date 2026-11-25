-- Prove2me | solution 1 for PI.ProdFormulaE.HaarBox.exists_ball_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:05:29.796189+00:00
-- url     : https://prove2.me/submissions/9f2267a1-ec79-4ec3-bbe0-3fff32ea8016

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarBox
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarScale
import Theorems.Thm_PI_ProdFormulaE_HaarBox_isOpen_box


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.style.haveILetI false
open MeasureTheory Measure ValuativeRel Topology Filter Module
open scoped NNReal ENNReal Pointwise
open PI PI.ProdFormulaE PI.ProdFormulaE.HaarBox
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.ProdFormulaE.HaarBox
theorem _root_.solution {C : Set K} (hC : IsCompact C) :
    ∃ y : K, y ≠ 0 ∧ C ⊆ {x | valuation K x ≤ valuation K y} := by
  classical
  have hopen : ∀ y : K, y ≠ 0 → IsOpen {x : K | valuation K x ≤ valuation K y} := by
    intro y hy
    have h := isOpen_box (Basis.singleton Unit K) (fun _ => valuation K y)
      (fun _ => (Valuation.ne_zero_iff _).mpr hy)
    convert h using 1
    ext x
    simp [box, Basis.singleton_repr]
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover
    (fun y : {y : K // y ≠ 0} => {x : K | valuation K x ≤ valuation K y.1})
    (fun y => hopen y.1 y.2) (by
      intro x _
      by_cases hx : x = 0
      · refine Set.mem_iUnion.mpr ⟨⟨1, one_ne_zero⟩, ?_⟩
        simp [hx]
      · exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, show valuation K x ≤ valuation K x from le_rfl⟩)
  rcases t.eq_empty_or_nonempty with h0 | hne
  · refine ⟨1, one_ne_zero, fun x hx => ?_⟩
    have h1 := ht hx
    simp [h0] at h1
  · obtain ⟨y, hy, hmax⟩ := t.exists_max_image (fun y => valuation K y.1) hne
    refine ⟨y.1, y.2, fun x hx => ?_⟩
    have hx' := ht hx
    simp only [Set.mem_iUnion] at hx'
    obtain ⟨y', hy', hxy'⟩ := hx'
    have hxy'' : valuation K x ≤ valuation K y'.1 := hxy'
    exact le_trans hxy'' (hmax y' hy')
end PI.ProdFormulaE.HaarBox
