-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_HW_pre_star_d__9265fbbd55c9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:44:21.605983+00:00
-- url     : https://prove2.me/submissions/be727d50-76f5-4bcc-8395-5d8054b8a446

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HasDerivAtRealOfComplex
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_SingleMulJmComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelGenA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_pre_op_curve
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_hasDerivAt_real_of_complex__aa8f135a3a47
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
theorem _root_.solution {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) : star (dτ X) = -dτ X := by
  obtain ⟨γ, hγ⟩ := exists_curve ε hX
  set A := dτ X
  have key : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • star A) * NormedSpace.exp ((t : ℂ) • A) = 1 := by
    intro t
    have h1 := pre_op_curve τ dτ hder hX γ hγ t
    have h2 : star (preOp τ (γ t)) * preOp τ (γ t) = 1 := Unitary.coe_star_mul_self _
    rw [h1, NormedSpace.star_exp, star_smul, Complex.star_def, Complex.conj_ofReal] at h2
    exact h2
  have hd0 := (hasDerivAt_exp_smul_const (star A) ((0 : ℝ) : ℂ)).mul
    (hasDerivAt_exp_smul_const A ((0 : ℝ) : ℂ))
  have hd2 := hasDerivAt_real_of_complex' hd0
  have hf : (fun y : ℝ => ((fun u : ℂ => NormedSpace.exp (u • star A)) *
      fun u : ℂ => NormedSpace.exp (u • A)) (y : ℂ)) = fun _ => 1 := funext fun t => by
    simpa using key t
  rw [hf] at hd2
  have := hd2.unique (hasDerivAt_const _ _)
  simp at this
  exact eq_neg_of_add_eq_zero_left this
end ReciprocityTheory.ChartRestriction.DS.HW
