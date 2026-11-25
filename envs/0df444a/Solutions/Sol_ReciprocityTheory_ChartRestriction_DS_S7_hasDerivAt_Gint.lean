-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.hasDerivAt_Gint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:22:39.364031+00:00
-- url     : https://prove2.me/submissions/797d5041-7d49-4ec4-8c32-5a151f7f9b36

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dga_path
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hasDerivAt_op
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_inK_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_isOpen_omega
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_phiM_differentiableOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_posSet_subset_omega


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
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) (k : KG ε) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y)
    (γ : ℝ → KG ε) (hγ : ∀ t, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Y)) :
    HasDerivAt (fun t => Gint T μ x (k * γ t))
      (fderiv ℂ (PhiM μ) (toMK k⁻¹ * x * toMK k)
          (toMK k⁻¹ * x * toMK k * Y - Y * (toMK k⁻¹ * x * toMK k)) •
          (T.op k * projW T * T.op k⁻¹) +
        PhiM μ (toMK k⁻¹ * x * toMK k) •
          (T.op k * (T.dτ Y * projW T - projW T * T.dτ Y) * T.op k⁻¹)) 0 := by
  have hm : ∀ a b : KG ε, toMK (a * b) = toMK a * toMK b := by
    intro a b
    simp [toMK, toM]
  have hi : ∀ a : KG ε, toMK a⁻¹ * toMK a = 1 := by
    intro a
    simp [toMK, toM]
  have hop : ∀ a b : KG ε, T.op (a * b) = T.op a * T.op b := by
    intro a b
    simp [KType.op]
  have hop1 : ∀ a : KG ε, T.op a⁻¹ * T.op a = 1 := by
    intro a
    simp only [KType.op, map_inv]
    rw [← Submonoid.coe_mul, inv_mul_cancel, Submonoid.coe_one]
  have hγ0 : γ 0 = 1 := by
    ext i j
    have h00 := congrFun (congrFun (hγ 0) i) j
    simpa [toMK, toM] using h00
  have hk2 : toMK k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ toMK k * Jm ε = Jm ε * toMK k := by
    simpa [KG, Kset, toM, toMK] using k.2
  have hst : star (toMK k) * toMK k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk2.1
  have hst' : toMK k * star (toMK k) = 1 := Matrix.mem_unitaryGroup_iff.1 hk2.1
  have hkinv : toMK k⁻¹ = (toMK k)ᴴ := by
    rw [← Matrix.star_eq_conjTranspose]
    calc toMK k⁻¹ = toMK k⁻¹ * (toMK k * star (toMK k)) := by rw [hst', mul_one]
      _ = (toMK k⁻¹ * toMK k) * star (toMK k) := by rw [mul_assoc]
      _ = star (toMK k) := by rw [hi, one_mul]
  have hinjk : Function.Injective (toMK k).mulVec := by
    intro v w hvw
    have h2 := congrArg (star (toMK k)).mulVec hvw
    simpa [Matrix.mulVec_mulVec, hst] using h2
  have hzP : toMK k⁻¹ * x * toMK k ∈ OmegaSet n := by
    apply posSet_subset_omega
    show (toMK k⁻¹ * x * toMK k).PosDef
    rw [hkinv]
    exact hx.conjTranspose_mul_mul_same hinjk
  have hexp : ∀ A : Matrix (Fin n) (Fin n) ℂ, NormedSpace.exp A * NormedSpace.exp (-A) = 1 := by
    intro A
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl A)), add_neg_cancel,
      NormedSpace.exp_zero]
  have hinvγ : ∀ t : ℝ, toMK (γ t)⁻¹ = NormedSpace.exp (-((t : ℂ) • Y)) := by
    intro t
    calc toMK (γ t)⁻¹
        = toMK (γ t)⁻¹ * (NormedSpace.exp ((t : ℂ) • Y) * NormedSpace.exp (-((t : ℂ) • Y))) := by
          rw [hexp, mul_one]
      _ = (toMK (γ t)⁻¹ * toMK (γ t)) * NormedSpace.exp (-((t : ℂ) • Y)) := by
          rw [hγ t, mul_assoc]
      _ = _ := by rw [hi, one_mul]
  have hf : ∀ t : ℝ, toMK (k * γ t)⁻¹ * x * toMK (k * γ t) =
      NormedSpace.exp (-((t : ℂ) • Y)) * (toMK k⁻¹ * x * toMK k) * NormedSpace.exp ((t : ℂ) • Y) := by
    intro t
    rw [_root_.mul_inv_rev, hm, hm, hinvγ, hγ]
    simp only [mul_assoc]
  have hQe : ∀ t : ℝ, T.op (1 * (γ t)⁻¹) * T.op k⁻¹ = T.op (k * γ t)⁻¹ := by
    intro t
    rw [one_mul, _root_.mul_inv_rev, hop]
  have hfun : (fun t : ℝ => Gint T μ x (k * γ t)) = fun t : ℝ =>
      PhiM μ (NormedSpace.exp (-((t : ℂ) • Y)) * (toMK k⁻¹ * x * toMK k) *
        NormedSpace.exp ((t : ℂ) • Y)) •
        (T.op (k * γ t) * projW T * (T.op (1 * (γ t)⁻¹) * T.op k⁻¹)) := by
    funext t
    simp only [Gint]
    rw [hf t, hQe t]
  have hP := hasDerivAt_op T k hY γ hγ
  have hδ : ∀ t : ℝ, toMK ((fun s : ℝ => (γ s)⁻¹) t) = NormedSpace.exp ((t : ℂ) • (-Y)) := by
    intro t
    rw [smul_neg]
    exact hinvγ t
  have hQ := (hasDerivAt_op T 1 (inK_neg hY) (fun s : ℝ => (γ s)⁻¹) hδ).mul_const (T.op k⁻¹)
  have hM := (hP.mul_const (projW T)).mul hQ
  have hφ : HasDerivAt (fun t : ℝ => PhiM μ (NormedSpace.exp (-((t : ℂ) • Y)) *
      (toMK k⁻¹ * x * toMK k) * NormedSpace.exp ((t : ℂ) • Y)))
      (fderiv ℂ (PhiM μ) (toMK k⁻¹ * x * toMK k)
        (toMK k⁻¹ * x * toMK k * Y - Y * (toMK k⁻¹ * x * toMK k))) 0 := by
    have hd := ((phiM_differentiableOn μ).differentiableAt (isOpen_omega.mem_nhds hzP)).hasFDerivAt
    have h0 : toMK k⁻¹ * x * toMK k = NormedSpace.exp (-(((0 : ℝ) : ℂ) • Y)) *
        (toMK k⁻¹ * x * toMK k) * NormedSpace.exp (((0 : ℝ) : ℂ) • Y) := by
      simp
    exact (hd.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) (dga_path Y _) h0
  have hop1' : T.op 1 = 1 := by simp [KType.op]
  rw [hfun]
  convert hφ.smul hM using 1
  all_goals try rfl
  simp only [hγ0, mul_one, one_mul, inv_one, hop1', map_neg, Complex.ofReal_zero, zero_smul,
    neg_zero, NormedSpace.exp_zero]
  rw [add_comm]
  simp only [Pi.mul_apply, hγ0, mul_one, inv_one, hop1', one_mul]
  refine congrArg₂ (· + ·) (congrArg _ ?_) rfl
  noncomm_ring
end ReciprocityTheory.ChartRestriction.DS.S7
