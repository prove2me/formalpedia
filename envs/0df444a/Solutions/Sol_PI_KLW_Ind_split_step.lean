-- Prove2me | solution 1 for PI.KLW.Ind.split_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:02:53.552936+00:00
-- url     : https://prove2.me/submissions/0eeb6fae-02fd-49ff-a555-f12a0e655d17

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOneInduction
import Theorems.Thm_PI_KLW_Ind_extL_self
import Theorems.Thm_PI_KLW_Ind_extL_ne
import Theorems.Thm_PI_KLW_Ind_decomp
import Theorems.Thm_PI_KLW_Ind_hf_ext_ext
import Theorems.Thm_PI_KLW_Ind_hf_decomp
import Theorems.Thm_PI_KLW_Ind_add_smul_mem
import Theorems.Thm_PI_KLW_Ind_hf_add_right
import Theorems.Thm_PI_KLW_Ind_hf_smul_right
import Theorems.Thm_PI_KLW_Ind_mkU_apply
import Theorems.Thm_PI_KLW_Ind_mkU_unitary
import Theorems.Thm_PI_KLW_Ind_rp_neg


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
theorem _root_.solution {K : Type} [Field K] [NumberField K] (c : K →+* K) (p : ℕ) {ι : Type}
    [Fintype ι] [DecidableEq ι] (i0 : ι) (L : Set (ι → K)) (hL : Unimod K c p L)
    (hS : Spans K L) (he : Pi.single i0 (1 : K) ∈ L)
    (hrec : ∀ L' : Set ({i // i ≠ i0} → K), Unimod K c p L' → Spans K L' →
      ∃ u : ({i // i ≠ i0} → K) ≃ₗ[K] ({i // i ≠ i0} → K),
        IsUnitary c u ∧ ∀ v, v ∈ L' ↔ ∀ j, Rp K p (u v j)) :
    ∃ u : (ι → K) ≃ₗ[K] (ι → K), IsUnitary c u ∧ ∀ v, v ∈ L ↔ ∀ i, Rp K p (u v i) := by
  have hv0 : ∀ v ∈ L, Rp K p (v i0) := fun v hv => by
    have := (hL v).1 hv _ he
    rwa [hf_single_right] at this
  have hres : ∀ v ∈ L, extL i0 (resL i0 v) ∈ L := fun v hv => by
    have e1 : extL i0 (resL i0 v) = v + (-(v i0)) • Pi.single i0 1 := by
      rw [neg_smul, ← sub_eq_add_neg]
      exact eq_sub_iff_add_eq.mpr (decomp i0 v).symm
    rw [e1]
    exact add_smul_mem hL hv he (rp_neg (hv0 v hv))
  let L' : Set ({i // i ≠ i0} → K) := {a | extL i0 a ∈ L}
  have hL' : Unimod K c p L' := by
    intro a
    constructor
    · intro ha b hb
      rw [← hf_ext_ext c i0]
      exact (hL _).1 ha _ hb
    · intro h
      show extL i0 a ∈ L
      rw [hL]
      intro x hx
      rw [decomp i0 x, hf_add_right, hf_smul_right, hf_single_right, extL_self, mul_zero,
        add_zero, hf_ext_ext]
      exact h _ (hres x hx)
  have hS' : Spans K L' := fun a => by
    obtain ⟨N, hN, h⟩ := hS (extL i0 a)
    exact ⟨N, hN, by show extL i0 _ ∈ L; rw [map_smul]; exact h⟩
  obtain ⟨u', hu', hmem'⟩ := hrec L' hL' hS'
  let U : (ι → K) →ₗ[K] (ι → K) :=
    extL i0 ∘ₗ (u'.toLinearMap ∘ₗ resL i0) + (LinearMap.proj i0).smulRight (Pi.single i0 1)
  have hU : ∀ v, U v = extL i0 (u' (resL i0 v)) + v i0 • Pi.single i0 1 := fun v => rfl
  have iso : ∀ v w, hf c (U v) (U w) = hf c v w := by
    intro v w
    rw [hU, hU, hf_decomp, hu']
    conv_rhs => rw [decomp i0 v, decomp i0 w]
    rw [hf_decomp]
  refine ⟨mkU c U iso, mkU_unitary c U iso, fun v => ?_⟩
  simp only [mkU_apply]
  have hUi0 : U v i0 = v i0 := by
    rw [hU]
    simp [extL_self]
  have hUj : ∀ j : {i // i ≠ i0}, U v j.1 = u' (resL i0 v) j := fun j => by
    rw [hU, Pi.add_apply, extL_ne, Pi.smul_apply, Pi.single_eq_of_ne j.2, smul_zero, add_zero]
  constructor
  · intro hv i
    by_cases h : i = i0
    · subst h
      rw [hUi0]
      exact hv0 v hv
    · have := hUj ⟨i, h⟩
      simp only at this
      rw [this]
      exact (hmem' _).1 (hres v hv) _
  · intro h
    have h0 : Rp K p (v i0) := hUi0 ▸ h i0
    have h1 : resL i0 v ∈ L' := (hmem' _).2 fun j => hUj j ▸ h j.1
    rw [decomp i0 v]
    exact add_smul_mem hL h1 he h0
end PI.KLW.Ind
