-- Prove2me | solution 1 for PI.ProdFormulaE.HaarBox.box_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:06:11.41065+00:00
-- url     : https://prove2.me/submissions/92250556-5cac-407b-bf03-95dafddfb5ab

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarBox

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
theorem _root_.solution (b : Basis ι K E) (γ : ι → ValueGroupWithZero K) :
    box b γ = b.equivFun.symm '' Set.univ.pi (fun i => {a : K | valuation K a ≤ γ i}) := by
  have hr : ∀ y : ι → K, b.repr (b.equivFun.symm y) = y := fun y => by
    have h1 := b.equivFun.apply_symm_apply y
    rw [Basis.equivFun_apply] at h1
    exact h1
  ext x
  simp only [box, Set.mem_setOf_eq, Set.mem_image, Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · intro h
    exact ⟨b.equivFun x, fun i => by simpa [Basis.equivFun_apply] using h i, by simp⟩
  · rintro ⟨y, hy, rfl⟩ i
    rw [hr]
    exact hy i
end PI.ProdFormulaE.HaarBox
