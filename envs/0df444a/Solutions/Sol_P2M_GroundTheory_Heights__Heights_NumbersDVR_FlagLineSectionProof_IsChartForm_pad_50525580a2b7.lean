-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_IsChartForm_pad_50525580a2b7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:43.073186+00:00
-- url     : https://prove2.me/submissions/af7812ce-e3cd-4547-83e4-f175618212be

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagLineSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagLineSectionForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_tMon_add_4ee6ed9d9839
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_liftN_add_7d29f9120d3f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_projMap_chartMon_ef7312781bb0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_isMultiHomog_chartMon_ffa9ade91345

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineSectionProof
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type*} [Field Ω]
  {F : Type*} [Field F] [Algebra F Ω] {N M : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
  {Φ : Type*} [Field Φ] [Algebra Ω Φ]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineSectionProof
namespace IsChartForm
theorem _root_.solution {y : (Σ k, ι k) → Ω} {w : Module.Basis (Fin N) Ω E}
    {φ : Fin M → Module.Dual Ω E} {t : Fin N → Φ} {c : ∀ k, ι k} {a : Ω} {n : ℕ}
    {A : MRing (bundleIdx ι M) F} (h : IsChartForm F M y w φ t c a n A) (m : ℕ) :
    IsChartForm F M y w φ t c a (n + m) (A * chartMon F M c (fun _ => m)) := by
  refine ⟨?_, ?_⟩
  · have := h.1.mul (isMultiHomog_chartMon (F := F) (M := M) c (fun _ => m))
    rwa [← liftN_add] at this
  · rw [map_mul, h.2, projMap_chartMon]
    have e : (fun _ : K => n + m) = (fun _ => n) + (fun _ => m) := rfl
    rw [e, tMon_add]
    simp only [segreVec, pow_add, Finset.prod_pow, map_mul]
    ring
end IsChartForm
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineSectionProof
