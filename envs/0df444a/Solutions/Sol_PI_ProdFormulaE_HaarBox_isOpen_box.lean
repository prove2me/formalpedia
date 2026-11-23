-- Prove2me | solution 1 for PI.ProdFormulaE.HaarBox.isOpen_box
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:26.113672+00:00
-- url     : https://prove2.me/submissions/6e4c4593-a843-4536-aa0d-3467fdce8747

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarBox
import Theorems.Thm_PI_ProdFormulaE_HaarBox_isOpen_ball
import Theorems.Thm_PI_ProdFormulaE_HaarBox_continuous_coord

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
theorem _root_.solution (b : Basis ι K E) (γ : ι → ValueGroupWithZero K) (hγ : ∀ i, γ i ≠ 0) :
    IsOpen (box b γ) := by
  have e : box b γ = ⋂ i, (fun x : E => b.repr x i) ⁻¹' {a : K | valuation K a ≤ γ i} := by
    ext x
    simp [box]
  rw [e]
  exact isOpen_iInter_of_finite fun i => (isOpen_ball (γ i) (hγ i)).preimage (continuous_coord b i)
end PI.ProdFormulaE.HaarBox
