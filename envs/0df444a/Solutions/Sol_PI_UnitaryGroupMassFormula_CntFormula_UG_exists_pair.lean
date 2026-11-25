-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.UG.exists_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:44:01.9443+00:00
-- url     : https://prove2.me/submissions/a8c96991-cb0a-46ba-a96e-a489ea5fbdd6

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_GmapLocEqOfFrame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_ExistsIsomMove
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula PI.UnitaryGroupMassFormula.CntFormula.UG
open Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V}
namespace PI.UnitaryGroupMassFormula.CntFormula.UG
theorem _root_.solution (hS : IsHermSemilocal S) (hM : IsSelfDualMod S h M) {ι : Type} [Fintype ι]
    (x : ι → V) (hxo : ∀ i j, i ≠ j → h (x i) (x j) = 0) (hxu : ∀ i, IsUnitIn S (h (x i) (x i)))
    (hxM : ∀ i, x i ∈ M) {r : V} (hr : ∃ v, h v r ≠ 0) (hrx : ∀ i, h (x i) r = 0) :
    ∃ α : K, α ≠ 0 ∧ α⁻¹ • r ∈ M ∧ ∃ w ∈ M, h w (α⁻¹ • r) = 1 ∧ ∀ i, h (x i) w = 0 := by
  classical
  obtain ⟨v, hv⟩ := hr
  let A : AddSubgroup K :=
    { carrier := {a | ∃ m ∈ M, h m r = a}
      add_mem' := by
        rintro _ _ ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩
        exact ⟨m + m', M.add_mem hm hm', by simp⟩
      zero_mem' := ⟨0, M.zero_mem, by simp⟩
      neg_mem' := by
        rintro _ ⟨m, hm, rfl⟩
        exact ⟨-m, M.neg_mem hm, by simp⟩ }
  have h1 : ∀ s ∈ S, ∀ a ∈ A, s * a ∈ A := by
    rintro s hs _ ⟨m, hm, rfl⟩
    refine ⟨star s • m, hM.smul_mem _ (hS.star_mem s hs) m hm, ?_⟩
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
  have h2 : ∃ a ∈ A, a ≠ 0 := by
    obtain ⟨t, ht, htv⟩ := hM.span v
    refine ⟨h (t • v) r, ⟨_, htv, rfl⟩, ?_⟩
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
    exact mul_ne_zero (star_ne_zero.mpr ht) hv
  have h3 : ∃ t : K, t ≠ 0 ∧ ∀ a ∈ A, t * a ∈ S := by
    obtain ⟨t, ht, htr⟩ := hM.span r
    refine ⟨t, ht, ?_⟩
    rintro _ ⟨m, hm, rfl⟩
    have := hM.int m hm _ htr
    rwa [map_smul, smul_eq_mul] at this
  obtain ⟨α, ⟨m₀, hm₀, hα⟩, hα0, hαS⟩ := hS.principal A h1 h2 h3
  have hrM : α⁻¹ • r ∈ M := hM.dual _ fun m hm => by
    rw [map_smul, smul_eq_mul, mul_comm]
    exact hαS _ ⟨m, hm, rfl⟩
  refine ⟨α, hα0, hrM, m₀ - ∑ i, (h (x i) m₀ * (h (x i) (x i))⁻¹) • x i, ?_, ?_, ?_⟩
  · refine M.sub_mem hm₀ (M.sum_mem fun i _ => hM.smul_mem _ ?_ _ (hxM i))
    exact S.mul_mem (hM.int _ (hxM i) _ hm₀) (hxu i).2.2
  · simp only [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply,
      map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply, hrx, mul_zero,
      Finset.sum_const_zero, sub_zero]
    rw [hα, inv_mul_cancel₀ hα0]
  · intro j
    rw [map_sub, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [Finset.sum_eq_single j (fun i _ hij => by rw [hxo j i (Ne.symm hij), mul_zero])
      (by simp), mul_assoc, inv_mul_cancel₀ (hxu j).1, mul_one, sub_self]
end PI.UnitaryGroupMassFormula.CntFormula.UG
