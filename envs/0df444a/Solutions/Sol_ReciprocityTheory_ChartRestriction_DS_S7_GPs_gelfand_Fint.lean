-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.gelfand_Fint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:48:06.55936+00:00
-- url     : https://prove2.me/submissions/3188093b-7195-417b-8ae1-c2e25a7a5f3b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_smooth_g0_on_Wset
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_psM_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_emb_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_Fint_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_sm_opPowH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_opPowH_slice
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_opPow_Fint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.GPs
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
local notation "𝕄f" => Fin n → Fin n → ℂ
variable {g : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ}
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ} [CompactSpace (KG ε)]
namespace ReciprocityTheory.ChartRestriction.DS.S7.GPs
theorem _root_.solution (T : KType ε Λ) (μ : Fin n → ℤ) (M : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ)
    (m : ℕ) (C : ℂ)
    (hM : ∀ (k : KG ε) (z : Matrix (Fin n) (Fin n) ℂ), toMK k⁻¹ * z * toMK k ∈ OmegaSet n →
      opGelfand (fun a b => Lhol (M a b)) m (fun y => PhiM μ (toMK k⁻¹ * y * toMK k)) z =
        C * PhiM μ (toMK k⁻¹ * z * toMK k))
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ Ps1.Uset ε) :
    opGelfand (fun a b => Lhol (M a b)) m (psM T μ) z = C • psM T μ z := by
  have key : ∀ k : KG ε, (∑ a, opPow (fun a b => DH (M a b)) m a a (g0 μ)) (emb z k) =
      C * g0 μ (emb z k) := by
    intro k
    have hp := emb_mem hz k
    rw [Finset.sum_apply, Finset.sum_congr rfl fun a _ => opPowH_slice M (smooth_g0_on_Wset μ) m a a _ hp]
    have h := hM k z (hz k)
    unfold opGelfand at h
    rw [Finset.sum_apply] at h
    exact h
  rw [psM_eq]
  unfold opGelfand
  rw [Finset.sum_apply, Finset.sum_congr rfl fun a _ => opPow_Fint T M (smooth_g0_on_Wset μ) m a a z hz,
    ← Fint_sum T Finset.univ _ (fun a _ => sm_opPowH M (smooth_g0_on_Wset μ) m a a) hz]
  unfold Fint
  simp_rw [key, mul_smul]
  rw [integral_smul, smul_comm]
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
