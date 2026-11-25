-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_exists_chartForm_24bb01e3d3b4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:23:19.528603+00:00
-- url     : https://prove2.me/submissions/2282b8bc-78d3-4c18-a316-cc7028c85512

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagLineSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagLineSectionForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_tMon_add_4ee6ed9d9839
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_liftN_add_7d29f9120d3f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_projMap_C_9682b00465f1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_projMap_chartMon_ef7312781bb0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_isMultiHomog_chartMon_ffa9ade91345
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_IsChartForm_pad_50525580a2b7

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
theorem _root_.solution (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k) (hc : segreVec y c ≠ 0)
    {a : Ω} (ha : a ∈ chartRing F (segreVec y) c) :
    ∃ (n : ℕ) (A : MRing (bundleIdx ι M) F), IsChartForm F M y w φ t c a n A := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    refine ⟨1, chartMon F M j (fun _ => 1), ?_, ?_⟩
    · exact isMultiHomog_chartMon j _
    · rw [projMap_chartMon, div_mul_eq_mul_div, pow_one, mul_div_assoc, div_self hc, mul_one]
      simp [segreVec]
  | algebraMap r =>
    refine ⟨0, C r, ?_, ?_⟩
    · have e : liftN (fun _ : K => 0) = 0 := by funext o; cases o <;> rfl
      unfold IsMultiHomog
      rw [e]
      exact isWeightedHomogeneous_C _ _
    · rw [projMap_C]
      simp [tMon]
  | add x z _ _ hx hz =>
    obtain ⟨n₁, A₁, h₁⟩ := hx
    obtain ⟨n₂, A₂, h₂⟩ := hz
    have h₁' := h₁.pad n₂
    have h₂' := h₂.pad n₁
    rw [Nat.add_comm n₂ n₁] at h₂'
    refine ⟨n₁ + n₂, _, h₁'.1.add h₂'.1, ?_⟩
    rw [map_add, h₁'.2, h₂'.2, add_mul, map_add, C_add, add_mul]
  | mul x z _ _ hx hz =>
    obtain ⟨n₁, A₁, h₁⟩ := hx
    obtain ⟨n₂, A₂, h₂⟩ := hz
    refine ⟨n₁ + n₂, A₁ * A₂, ?_, ?_⟩
    · have := h₁.1.mul h₂.1
      rwa [← liftN_add] at this
    · rw [map_mul, h₁.2, h₂.2]
      have e : (fun _ : K => n₁ + n₂) = (fun _ => n₁) + (fun _ => n₂) := rfl
      rw [e, tMon_add, pow_add]
      simp only [map_mul]
      ring
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineSectionProof
