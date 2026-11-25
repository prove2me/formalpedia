-- Prove2me | solution 1 for P2M_GlobalTheory_exists_E__cube_div_discriminant_eq_bed7c5b84d7f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:44:11.711052+00:00
-- url     : https://prove2.me/submissions/e8706ea4-478e-4558-a3bb-29512909715a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Theorems.Thm_P2M_GlobalTheory_tendsto_E__atImInfty_ea4a24c64cca

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm MatrixGroups Filter EisensteinSeries
open scoped Real Topology
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (c : ℂ) :
    ∃ τ : ℍ, E₄ τ ^ 3 / discriminant τ = c := by
  by_contra! hc
  let g : ModularForm 𝒮ℒ 12 := ModularForm.mcast (by decide) (E₄.pow 3) -
    c • (CuspForm.discriminant : ModularForm 𝒮ℒ 12)
  have hg : ∀ τ, g τ = E₄ τ ^ 3 - c * discriminant τ := fun τ ↦ by
    simp [g]
    rfl
  have hg0 : ∀ τ, g τ ≠ 0 := fun τ h ↦ hc τ (by
    rw [hg] at h
    rw [div_eq_iff (discriminant_ne_zero τ)]
    linear_combination h)
  have hlim : Tendsto (g : ℍ → ℂ) atImInfty (𝓝 1) := by
    have := (tendsto_E₄_atImInfty.pow 3).sub
      ((show Tendsto discriminant atImInfty (𝓝 0) from discriminant_isZeroAtImInfty).const_mul c)
    simpa [funext hg] using this
  have hsl : ∀ γ : SL(2, ℤ),
      ((1 : ℍ → ℂ) / g) ∣[(0 : ℤ) - 12] γ = (1 : ℍ → ℂ) / g := fun γ ↦ by
    have hγ : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
    rw [div_slash_SL2, is_invariant_one, SL_slash, SlashInvariantForm.slash_action_eqn _ _ hγ]
  let f : ModularForm 𝒮ℒ ((0 : ℤ) - 12) :=
    { toFun := (1 : ℍ → ℂ) / g
      slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ hsl γ
      holo' := mdifferentiable_const.div g.holo' hg0
      bdd_at_cusps' := fun {c} hc ↦ by
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
        rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
        intro γ _
        rw [hsl γ]
        exact ((tendsto_const_nhds (x := (1 : ℂ))).div hlim one_ne_zero).isBigO_one ℝ }
  have := congrFun (ModularFormClass.levelOne_neg_weight_eq_zero (by norm_num) f) UpperHalfPlane.I
  have h3 : (1 : ℂ) / g UpperHalfPlane.I = 0 := this
  simp [hg0] at h3
end GlobalTheory
