-- Prove2me | solution 1 for PI.ProdFormulaE.HaarBox.image_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:05:36.147178+00:00
-- url     : https://prove2.me/submissions/fa6ed70e-f237-482f-b2e3-833b26b34a43

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarBox
import Theorems.Thm_PI_ProdFormulaE_HaarBox_locallyCompact
import Theorems.Thm_PI_ProdFormulaE_HaarBox_secondCountableE

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
variable [MeasurableSpace E] [BorelSpace E]
namespace PI.ProdFormulaE.HaarBox
theorem _root_.solution (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure] (T : E ≃ₗ[K] E) :
    ∃ c : ℝ≥0, ∀ S : Set E, μ (T '' S) = c * μ S := by
  haveI : IsTopologicalAddGroup E := IsModuleTopology.topologicalAddGroup K E
  haveI := locallyCompact b
  haveI := secondCountableE b
  let L := toCLE T
  haveI : (μ.map L.symm).IsAddHaarMeasure := L.symm.isAddHaarMeasure_map μ
  refine ⟨addHaarScalarFactor (μ.map L.symm) μ, fun S => ?_⟩
  have h := isAddLeftInvariant_eq_smul (μ.map L.symm) μ
  have h2 : (μ.map L.symm) S = μ (T '' S) := by
    have hm : (μ.map L.symm) = μ.map (L.symm.toHomeomorph.toMeasurableEquiv) := rfl
    rw [hm, MeasurableEquiv.map_apply]
    have hL : ∀ x, L.symm x = T.symm x := fun x => rfl
    congr 1
    ext x
    simp only [Set.mem_preimage, Homeomorph.toMeasurableEquiv_coe,
      ContinuousLinearEquiv.coe_toHomeomorph, hL, Set.mem_image]
    constructor
    · intro hx; exact ⟨T.symm x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩; simpa using hy
  have h' : (μ.map L.symm) S = _ := DFunLike.congr_fun h S
  rw [← h2, h']
  first | rfl | exact (nnreal_smul_coe_apply _ _ _) | simp
end PI.ProdFormulaE.HaarBox
