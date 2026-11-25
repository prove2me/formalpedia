-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_HW_pre_d__bracket_ee11bdc2726a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:56:34.245331+00:00
-- url     : https://prove2.me/submissions/0f938b81-946c-4f4a-b122-f4d93ef16f94

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HasDerivAtRealOfComplex
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_SingleMulJmComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelGenA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_pre_op_curve
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_pre_star_d__9265fbbd55c9
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_pre_conj_d__863c89af0a82
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_pre_d__conj_hasDerivAt_8d9d6be50006
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_hasDerivAt_real_of_complex__aa8f135a3a47
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_inK_iff__24a5ac304dfc
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
theorem _root_.solution {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (hY : inK ε Y) :
    dτ X * dτ Y - dτ Y * dτ X = dτ (X * Y - Y * X) := by
  obtain ⟨γ, hγ⟩ := exists_curve ε hX
  set A := dτ X
  set B := dτ Y
  have hA := pre_star_dτ τ dτ hder hX
  have hXs := ((inK_iff' ε X).1 hX).1
  have key : ∀ s : ℝ, NormedSpace.exp ((s : ℂ) • A) * B * NormedSpace.exp ((s : ℂ) • (-A)) =
      dτ (NormedSpace.exp ((s : ℂ) • X) * Y * NormedSpace.exp ((s : ℂ) • (-X))) := by
    intro s
    have h := pre_conj_dτ τ dτ hder (γ s) hY
    rw [pre_op_curve τ dτ hder hX γ hγ s, hγ s, NormedSpace.star_exp, star_smul, hA,
      Complex.star_def, Complex.conj_ofReal] at h
    rw [h]
    congr 2
    rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hXs,
      Complex.star_def, Complex.conj_ofReal]
  have h1 := hasDerivAt_real_of_complex' (z := 0)
    (((hasDerivAt_exp_smul_const A ((0 : ℝ) : ℂ)).mul_const B).mul
      (hasDerivAt_exp_smul_const (-A) ((0 : ℝ) : ℂ)))
  have h2 := pre_dτ_conj_hasDerivAt dτ X Y
  have h1' := h1.congr_of_eventuallyEq
    (f₁ := fun s : ℝ => dτ (NormedSpace.exp ((s : ℂ) • X) * Y * NormedSpace.exp ((s : ℂ) • (-X))))
    (Filter.Eventually.of_forall fun s => (key s).symm)
  have := h1'.unique h2
  rw [← this]
  simp [sub_eq_add_neg]
end ReciprocityTheory.ChartRestriction.DS.HW
