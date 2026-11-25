-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.kType_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:10:37.078872+00:00
-- url     : https://prove2.me/submissions/8cecf6c6-0593-43a3-b7eb-d28ed5ee24ad

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelTwist
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_twist_det_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_twist_toMK_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_twist_hasDerivAt_det_exp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_twist_smul_mem_unitary
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_twist_zpow_star

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
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (c : ℤ) :
    Nonempty (KType ε (fun a => Λ a + (c : ℝ))) := by
  letI := T.instNACG
  letI := T.instIPS
  letI := T.instFD
  letI := T.instCS
  let d : KG ε → ℂ := fun k => (toMK k).det ^ c
  have hd : ∀ k, star (d k) * d k = 1 := fun k => twist_zpow_star k c
  have hdne : ∀ k, d k ≠ 0 := fun k => zpow_ne_zero c (twist_det_ne k)
  have hdmul : ∀ k k', d (k * k') = d k * d k' := by
    intro k k'
    show (toMK (k * k')).det ^ c = (toMK k).det ^ c * (toMK k').det ^ c
    rw [show toMK (k * k') = toMK k * toMK k' from rfl, Matrix.det_mul, _root_.mul_zpow]
  have hd1 : d 1 = 1 := by
    show (toMK (1 : KG ε)).det ^ c = 1
    rw [show toMK (1 : KG ε) = 1 from rfl, Matrix.det_one, _root_.one_zpow]
  let τ' : KG ε →* unitary (T.V →L[ℂ] T.V) :=
    { toFun := fun k => ⟨d k • ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V),
        twist_smul_mem_unitary (hd k) (T.τ k).2⟩
      map_one' := by
        apply Subtype.ext
        show d 1 • ((T.τ 1 : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = 1
        rw [hd1, one_smul, map_one, OneMemClass.coe_one]
      map_mul' := fun k k' => by
        apply Subtype.ext
        show d (k * k') • ((T.τ (k * k') : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) =
          (d k • ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V)) *
            (d k' • ((T.τ k' : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V))
        rw [hdmul, map_mul, Submonoid.coe_mul, smul_mul_smul_comm] }
  have hcontd : Continuous d := by
    have h1 : Continuous fun k : KG ε => (toMK k).det :=
      Continuous.matrix_det (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val))
    exact h1.zpow₀ c (fun k => Or.inl (twist_det_ne k))
  let dτ' : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (T.V →L[ℂ] T.V) :=
    T.dτ + (c : ℂ) • (Matrix.traceLinearMap (Fin n) ℂ ℂ).smulRight (1 : T.V →L[ℂ] T.V)
  have hdτ : ∀ X, dτ' X = T.dτ X + ((c : ℂ) * X.trace) • (1 : T.V →L[ℂ] T.V) := by
    intro X
    simp only [dτ', LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
      Matrix.traceLinearMap_apply, smul_smul]
  refine ⟨⟨T.V, τ', ?_, ?_, dτ', ?_, T.w, T.w_norm, ?_, ?_⟩⟩
  · show Continuous (fun k => (⟨d k • ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V),
        twist_smul_mem_unitary (hd k) (T.τ k).2⟩ : unitary (T.V →L[ℂ] T.V)))
    exact Continuous.subtype_mk (hcontd.smul (continuous_subtype_val.comp T.cont)) _
  · intro W hW
    refine T.irred W (fun k v hv => ?_)
    have h : (d k • ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V)) v ∈ W := hW k v hv
    have e : ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) v =
        (d k)⁻¹ • ((d k • ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V)) v) := by
      rw [ContinuousLinearMap.smul_apply, smul_smul, inv_mul_cancel₀ (hdne k), one_smul]
    rw [e]
    exact W.smul_mem _ h
  · intro X hX γ hγ
    have hg := T.hasDeriv X hX γ hγ
    have hγ0 : γ 0 = 1 := by
      apply twist_toMK_inj
      rw [hγ 0, show (((0 : ℝ) : ℂ) • X) = 0 by simp, NormedSpace.exp_zero]
      rfl
    have hf0 : HasDerivAt (fun t : ℝ => (toMK (γ t)).det) X.trace 0 := by
      refine (twist_hasDerivAt_det_exp X).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t => ?_))
      simp only [hγ t]
    have hdet0 : (toMK (γ 0)).det = 1 := by
      rw [hγ0]
      exact Matrix.det_one
    have hf : HasDerivAt (fun t : ℝ => d (γ t)) ((c : ℂ) * X.trace) 0 := by
      have hz := hasDerivAt_zpow c ((toMK (γ 0)).det) (Or.inl (twist_det_ne _))
      have hc := hz.comp (0 : ℝ) hf0
      rw [hdet0, _root_.one_zpow, mul_one] at hc
      exact hc
    have hτ0 : ((T.τ (γ 0) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = 1 := by
      rw [hγ0, map_one, OneMemClass.coe_one]
    have hd0 : d (γ 0) = 1 := by
      show (toMK (γ 0)).det ^ c = 1
      rw [hdet0, _root_.one_zpow]
    have hsm := hf.smul hg
    simp only [hτ0, hd0, one_smul] at hsm
    rw [← hdτ] at hsm
    exact hsm
  · intro a
    rw [hdτ, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
      T.w_wt a, Matrix.trace_single_eq_same, mul_one]
    push_cast
    rw [add_smul]
  · intro a b hab he
    rw [hdτ, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
      T.w_hw a b hab he, Matrix.trace_single_eq_of_ne _ _ _ hab.ne, mul_zero, zero_smul, add_zero]
end ReciprocityTheory.ChartRestriction.DS.HW
