-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_HW_KType_conj_d__50b083afe397
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:46:06.024739+00:00
-- url     : https://prove2.me/submissions/497481c3-7199-4612-ba8c-e5e12723251d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OpEqExp
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HasDerivAtRealOfComplex
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_KType_op_inv
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_toMK_inv__f48a87546ad5
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_hasDerivAt_real_of_complex__aa8f135a3a47
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_inK_conj__14f76c740320
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_KType_op_curve
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
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
namespace KType
theorem _root_.solution {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) :
    T.op k * T.dτ Y * star (T.op k) = T.dτ (toMK k * Y * star (toMK k)) := by
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
  set B := T.dτ Y
  set C := T.dτ (toMK k * Y * star (toMK k))
  have key : ∀ t : ℝ, T.op k * NormedSpace.exp ((t : ℂ) • B) * star (T.op k) =
      NormedSpace.exp ((t : ℂ) • C) := by
    intro t
    rw [← KType.op_curve T hY γ hγ t, ← KType.op_curve T hY' _ hγ' t, ← KType.op_inv]
    show _ = ((T.τ (k * γ t * k⁻¹) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V)
    rw [map_mul, map_mul]
    rfl
  have h1 := hasDerivAt_real_of_complex' (z := 0)
    (((hasDerivAt_exp_smul_const B ((0 : ℝ) : ℂ)).const_mul (T.op k)).mul_const (star (T.op k)))
  have h2 := hasDerivAt_real_of_complex' (z := 0) (hasDerivAt_exp_smul_const C ((0 : ℝ) : ℂ))
  have hf : (fun y : ℝ => T.op k * NormedSpace.exp ((y : ℂ) • B) * star (T.op k)) =
      fun y : ℝ => NormedSpace.exp ((y : ℂ) • C) := funext key
  simp only [hf] at h1
  have := h1.unique h2
  simpa using this
end KType
end ReciprocityTheory.ChartRestriction.DS.HW
