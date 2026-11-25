-- Prove2me | solution 1 for PositivityTheory.ThK.LinAct.coeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:08:52.033731+00:00
-- url     : https://prove2.me/submissions/5fcfb3f7-9de0-42d8-97b0-96a12acdcaa4

import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_EvlLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_LinearActInt
import Theorems.Thm_PositivityTheory_ThK_LinAct_eventually_fix
import Theorems.Thm_PositivityTheory_ThK_LinAct_exists_compact_ann
import Theorems.Thm_PositivityTheory_ThK_LinAct_schr_add
import Theorems.Thm_PositivityTheory_ThK_LinAct_schr_comm
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Implements_comp
import Theorems.Thm_PositivityTheory_ThKH_Evl_schr_mem
import Theorems.Thm_PositivityTheory_ThKH_Evl_t2Space_local_field_bis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.WeilM MeasureTheory ValuativeRel Topology Filter PositivityTheory.ThKH.Evl
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.LinAct
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
  {κ ι : Type} [Fintype κ] [Fintype ι] {ψ : AddChar k ℂ}
namespace PositivityTheory.ThK.LinAct
theorem _root_.solution (hc : Continuous ψ) (h1 : ψ ≠ 1) (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ)
    (X S : (ι → k) →ₗ[k] (κ → k) × (κ → k)) (hX : ∀ x x', (X x).1 ⬝ᵥ (X x').2 = (X x').1 ⬝ᵥ (X x).2)
    (hS : ∀ y, ∀ φ ∈ SB (κ → k), l (schr ψ (S y) φ) = l φ)
    (hXS : ∀ x y, (X x).1 ⬝ᵥ (S y).2 - (S y).1 ⬝ᵥ (X x).2 = x ⬝ᵥ y) {φ : (κ → k) → ℂ} (hφ : φ ∈ SB (κ → k)) :
    (fun x => l (schr ψ (X x) φ)) ∈ SB (ι → k) := by
  have := t2Space_local_field_bis (k := k)
  have cX : Continuous X := X.continuous_on_pi
  have cS : Continuous S := S.continuous_on_pi
  have hf := eventually_fix (ψ := ψ) hc hφ
  constructor
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have ht : Tendsto (fun y => X (y - x)) (𝓝 x) (𝓝 0) :=
      (cX.comp (continuous_id.sub continuous_const)).tendsto' _ _ (by simp)
    filter_upwards [ht.eventually hf] with y hy
    conv_rhs => rw [← hy, schr_add (hX _ _), ← map_add, add_sub_cancel]
  · obtain ⟨C, hC, h⟩ := exists_compact_ann (ι := ι) hc h1 ((cS.tendsto' 0 0 (map_zero S)).eventually hf)
    refine HasCompactSupport.intro hC fun x hx => ?_
    by_contra hne
    refine hx (h x fun y hy => ?_)
    have e := congrArg l (schr_comm (ψ := ψ) (X x) (S y) φ)
    have hy' : schr ψ (S y) φ = φ := hy
    rw [hy', map_smul, hS y _ (schr_mem hc _ hφ), hXS, smul_eq_mul] at e
    exact (mul_eq_right₀ hne).1 e.symm
end PositivityTheory.ThK.LinAct
