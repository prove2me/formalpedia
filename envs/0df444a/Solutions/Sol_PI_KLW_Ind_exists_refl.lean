-- Prove2me | solution 1 for PI.KLW.Ind.exists_refl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:55:19.4358+00:00
-- url     : https://prove2.me/submissions/2750938c-8379-49d4-bc83-30e849eabf33

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOneInduction
import Theorems.Thm_PI_KLW_Ind_hf_add_left
import Theorems.Thm_PI_KLW_Ind_hf_conj
import Theorems.Thm_PI_KLW_Ind_hf_smul_left
import Theorems.Thm_PI_KLW_Ind_hf_smul_right
import Theorems.Thm_PI_KLW_Ind_hf_sub_left
import Theorems.Thm_PI_KLW_Ind_hf_sub_right
import Theorems.Thm_PI_KLW_Ind_mkU_apply
import Theorems.Thm_PI_KLW_Ind_mkU_unitary


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW PI.KLW.Ind
open PI.KLW
namespace PI.KLW.Ind
theorem _root_.solution {K : Type} [Field K] (c : K →+* K) (hc : ∀ x, c (c x) = x) {ι : Type}
    [Fintype ι] (e0 e : ι → K) (h0 : hf c e0 e0 = 1) (h1 : hf c e e = 1) (hne : hf c e0 e ≠ 1) :
    ∃ σ : (ι → K) ≃ₗ[K] (ι → K), IsUnitary c σ ∧ σ e0 = e := by
  obtain ⟨w, hw⟩ : ∃ w, w = e0 - e := ⟨_, rfl⟩
  obtain ⟨t, htdef⟩ : ∃ t, t = hf c e0 w := ⟨_, rfl⟩
  have ht : t = 1 - hf c e0 e := by rw [htdef, hw, hf_sub_right, h0]
  have ht0 : t ≠ 0 := by rw [ht]; exact sub_ne_zero.mpr (Ne.symm hne)
  have hct : c t = 1 - hf c e e0 := by rw [htdef, hf_conj c hc, hw, hf_sub_left, h0]
  have hww : hf c w w = t + c t := by
    rw [hct, ht, hw, hf_sub_left, hf_sub_right, hf_sub_right, h0, h1]
    ring
  have hct0 : c t ≠ 0 := (map_ne_zero c).mpr ht0
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = t⁻¹ := ⟨_, rfl⟩
  have key : γ + c γ = γ * c γ * hf c w w := by
    rw [hww, hγ, map_inv₀]
    field_simp
    ring
  let φ : (ι → K) →ₗ[K] K :=
    { toFun := fun v => γ * hf c v w
      map_add' := fun a b => by rw [hf_add_left, mul_add]
      map_smul' := fun k a => by rw [hf_smul_left, RingHom.id_apply, smul_eq_mul]; ring }
  let σL : (ι → K) →ₗ[K] (ι → K) := LinearMap.id - φ.smulRight w
  have hσ : ∀ v, σL v = v - (γ * hf c v w) • w := fun v => rfl
  have iso : ∀ v v', hf c (σL v) (σL v') = hf c v v' := by
    intro v v'
    rw [hσ, hσ]
    simp only [hf_sub_left, hf_sub_right, hf_smul_left, hf_smul_right, map_mul]
    rw [← hf_conj c hc v' w]
    linear_combination (-(hf c v w * c (hf c v' w))) * key
  refine ⟨mkU c σL iso, mkU_unitary c σL iso, ?_⟩
  rw [mkU_apply, hσ, ← htdef, hγ, inv_mul_cancel₀ ht0, one_smul, hw, sub_sub_cancel]
end PI.KLW.Ind
