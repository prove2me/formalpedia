-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_HW_pre_conj_d__863c89af0a82
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:45:07.403496+00:00
-- url     : https://prove2.me/submissions/086f2e89-3d4d-496a-9818-57f7eecc9e01

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HasDerivAtRealOfComplex
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_SingleMulJmComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelGenA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_preOp_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_preOp_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_pre_op_curve
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_hasDerivAt_real_of_complex__aa8f135a3a47
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_inK_conj__14f76c740320
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_toMK_inv__f48a87546ad5
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_exists_curve


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V] {ε : Fin n → Bool} (τ : KG ε →* unitary (V →L[ℂ] V))
  (dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V))
variable (hder : ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
    HasDerivAt (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) (dτ X) 0)
include hder
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (k : KG ε) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) :
    preOp τ k * dτ Y * star (preOp τ k) = dτ (toMK k * Y * star (toMK k)) := by
  obtain ⟨γ, hγ⟩ := exists_curve ε hY
  have hY' := inK_conj' k hY
  set U : (Matrix (Fin n) (Fin n) ℂ)ˣ := ((k : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)
  have hU : ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = star (toMK k) :=
    toMK_inv' k
  have hγ' : ∀ t : ℝ, toMK (k * γ t * k⁻¹) =
      NormedSpace.exp ((t : ℂ) • (toMK k * Y * star (toMK k))) := by
    intro t
    have e1 : toMK (k * γ t * k⁻¹) = toMK k * toMK (γ t) * toMK k⁻¹ := rfl
    rw [e1, toMK_inv', hγ t, ← hU]
    have e2 : (t : ℂ) • ((U : Matrix (Fin n) (Fin n) ℂ) * Y * ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ)) = (U : Matrix (Fin n) (Fin n) ℂ) * ((t : ℂ) • Y) *
        ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [e2, Matrix.exp_units_conj]
  set B := dτ Y
  set C := dτ (toMK k * Y * star (toMK k))
  have key : ∀ t : ℝ, preOp τ k * NormedSpace.exp ((t : ℂ) • B) * star (preOp τ k) =
      NormedSpace.exp ((t : ℂ) • C) := by
    intro t
    rw [← pre_op_curve τ dτ hder hY γ hγ t, ← pre_op_curve τ dτ hder hY' _ hγ' t, ← preOp_inv,
      preOp_mul, preOp_mul]
  have h1 := hasDerivAt_real_of_complex' (z := 0)
    (((hasDerivAt_exp_smul_const B ((0 : ℝ) : ℂ)).const_mul (preOp τ k)).mul_const (star (preOp τ k)))
  have h2 := hasDerivAt_real_of_complex' (z := 0) (hasDerivAt_exp_smul_const C ((0 : ℝ) : ℂ))
  have hf : (fun y : ℝ => preOp τ k * NormedSpace.exp ((y : ℂ) • B) * star (preOp τ k)) =
      fun y : ℝ => NormedSpace.exp ((y : ℂ) • C) := funext key
  simp only [hf] at h1
  have := h1.unique h2
  simpa using this
end ReciprocityTheory.ChartRestriction.DS.HW
