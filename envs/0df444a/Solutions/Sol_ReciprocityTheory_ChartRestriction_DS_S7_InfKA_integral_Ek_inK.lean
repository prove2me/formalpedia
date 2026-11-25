-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.InfKA.integral_Ek_inK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:07:01.668386+00:00
-- url     : https://prove2.me/submissions/bae293cb-8ca6-4be6-a7d7-50ea7bef0122

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ByParts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_DkL_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_continuous_B
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_continuous_Gint
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_continuous_Ek
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dga_path
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_exists_oneParam
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_gamma_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hasDerivAt_Gint
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_kByParts


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
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}
open ReciprocityTheory.ChartRestriction.DS.S7.InfKA
namespace ReciprocityTheory.ChartRestriction.DS.S7.InfKA
theorem _root_.solution [CompactSpace (KG ε)] (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : x.PosDef) (φ : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) : ∫ k, Ek T μ x φ A Z k ∂(muK ε) = 0 := by
  obtain ⟨γ, -, hγ, hmul⟩ := exists_oneParam ε hZ
  have hγ0 : γ 0 = 1 := gamma_zero hmul
  have hmk : ∀ a b : KG ε, toMK (a * b) = toMK a * toMK b := fun _ _ => rfl
  have hinv_t : ∀ t : ℝ, toMK (γ t)⁻¹ = NormedSpace.exp (-((t : ℂ) • Z)) := by
    intro t
    have h1 : toMK (γ t)⁻¹ * toMK (γ t) = 1 := by rw [← hmk, inv_mul_cancel]; rfl
    calc toMK (γ t)⁻¹ = toMK (γ t)⁻¹ * (toMK (γ t) * NormedSpace.exp (-((t : ℂ) • Z))) := by
          rw [hγ, kfa_exp_mul_neg, Matrix.mul_one]
      _ = NormedSpace.exp (-((t : ℂ) • Z)) := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  refine kByParts ε (fun k => φ (toMK k⁻¹ * A * toMK k) • Gint T μ x k) (Ek T μ x φ A Z) hZ γ hγ
    ((φ.continuous.comp (continuous_B A)).smul (continuous_Gint T μ hx)) (continuous_Ek T μ hx φ A Z) ?_
  intro k
  set Bk := toMK k⁻¹ * A * toMK k with hBk
  have hφ : HasDerivAt
      (fun t : ℝ => φ (NormedSpace.exp (-((t : ℂ) • Z)) * Bk * NormedSpace.exp ((t : ℂ) • Z)))
      (φ (Bk * Z - Z * Bk)) 0 :=
    (φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (dga_path Z Bk)
  have h := hφ.smul (hasDerivAt_Gint T μ hx k hZ γ hγ)
  convert h using 1
  · funext t
    congr 2
    rw [_root_.mul_inv_rev, hmk, hmk, hinv_t, hγ, hBk]
    simp only [Matrix.mul_assoc]
  · simp only [Ek, DkL_apply, hγ0, mul_one, Complex.ofReal_zero, zero_smul, neg_zero, NormedSpace.exp_zero,
      Matrix.one_mul, Matrix.mul_one, hBk]
end ReciprocityTheory.ChartRestriction.DS.S7.InfKA
