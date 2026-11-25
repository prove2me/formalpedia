-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_G__apply_f1b4125cf86b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:50:39.817157+00:00
-- url     : https://prove2.me/submissions/00f450eb-29b2-4ce1-a12c-56eb3533bfb6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_PsWord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_diffAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_isOpen_Om
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_hasFDerivAt_slice
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_contDiffOn_Fw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_toMK_mul_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW
variable {n : ℕ}
local notation "𝕄" => Fin n → Fin n → ℂ
local notation "MM" => Matrix (Fin n) (Fin n) ℂ
local notation "WW" => ((Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ)) × (Fin n → Fin n → ℂ)
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW
theorem _root_.solution (T : KType ε Λ) (μ : Fin n → ℤ) (D : List MM) {z : MM} (hz : z ∈ Ps1.Uset ε)
    (k : KG ε) (Z : MM) : G' T μ D z k (Z * z) = G T μ (Z :: D) z k := by
  have hq : psi k z ∈ (Om : Set WW) := hz k
  have hs := hasFDerivAt_slice (diffAt (contDiffOn_Fw μ D) isOpen_Om hq)
  have hrep : Fw μ (Z :: D) (psi k z) = fderiv ℂ (Fw μ D) (psi k z)
      (ContinuousLinearMap.inr ℂ (𝕄 × 𝕄) 𝕄
        (mmul (mmul (mmul (psi k z).1.1 Z) (psi k z).1.2) (psi k z).2)) := by
    show fderiv ℂ (fun y : 𝕄 => Fw μ D ((psi k z).1, y)) (psi k z).2
      (mmul (mmul (mmul (psi k z).1.1 Z) (psi k z).1.2) (psi k z).2) = _
    rw [hs.fderiv]
    rfl
  have hv : dpsi k (Z * z) = ContinuousLinearMap.inr ℂ (𝕄 × 𝕄) 𝕄
      (mmul (mmul (mmul (psi k z).1.1 Z) (psi k z).1.2) (psi k z).2) := by
    have h1 := toMK_mul_inv k
    refine Prod.ext rfl ?_
    show toMK k⁻¹ * (Z * z) * toMK k = toMK k⁻¹ * Z * toMK k * (toMK k⁻¹ * z * toMK k)
    calc toMK k⁻¹ * (Z * z) * toMK k = toMK k⁻¹ * Z * (toMK k * toMK k⁻¹) * z * toMK k := by
          rw [h1]
          simp only [mul_one, mul_assoc]
      _ = toMK k⁻¹ * Z * toMK k * (toMK k⁻¹ * z * toMK k) := by
          simp only [mul_assoc]
  show ((fderiv ℂ (Fw μ D) (psi k z)).comp (dpsi k)).smulRight (T.op k * projW T * T.op k⁻¹) (Z * z) =
    Fw μ (Z :: D) (psi k z) • (T.op k * projW T * T.op k⁻¹)
  rw [hrep, ← hv]
  rfl
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW
