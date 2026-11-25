-- Prove2me | solution 1 for PI.Dv.ProjAW.dual_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:01:10.222662+00:00
-- url     : https://prove2.me/submissions/0c4e4355-df82-4c0e-8a96-a17299e88d19

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_LenAtEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_MemDualLat
import Theorems.Thm_PI_Dv_ProjAW_ext_lat
import Theorems.Thm_PI_Dv_ProjAW_mem_dualLat
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_Dv_ProjAW_fg_img
import Theorems.Thm_PI_Dv_ProjAW_idem_of
import Theorems.Thm_PI_Dv_ProjAW_mem_cutE
import Theorems.Thm_PI_Dv_ProjAW_mem_imgE
import Theorems.Thm_PI_Dv_ProjAW_part1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjAW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K]
variable [StarRing K] (A : HLat K)
namespace PI.Dv.ProjAW
theorem _root_.solution (hG : A.Good) {e : Module.End K A.V} (he : e * e = e) {n : ℕ} (hn0 : 0 < n)
    (hn : ∀ x ∈ A.L, ((n : ℕ) : 𝓞 K) • e x ∈ A.L) (ψ : Module.Dual K A.V) (hψ : ψ ∘ₗ e = ψ) :
    ψ ∈ Formalism.HN.dualLat (cutE A e A.L) ↔ ∃ φ ∈ A.dualL, ψ = φ ∘ₗ e := by
  constructor
  · intro h
    rw [mem_dualLat] at h
    let Q := imgE A (1 - e) A.L
    haveI : Module.IsTorsionFree (𝓞 K) A.V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K A.V
    haveI : Module.IsTorsionFree (𝓞 K) Q :=
      Function.Injective.moduleIsTorsionFree (Q.subtype) Subtype.val_injective (fun _ _ => rfl)
    haveI : Module.Finite (𝓞 K) Q := Module.Finite.iff_fg.mpr (fg_img A hG (1 - e))
    haveI : Module.FinitePresentation (𝓞 K) Q := Module.finitePresentation_of_finite _ _
    haveI : Module.Projective (𝓞 K) Q := Module.Flat.projective_of_finitePresentation
    let g : A.L →ₗ[𝓞 K] Q := ((1 - e).restrictScalars (𝓞 K)).submoduleMap A.L
    obtain ⟨s, hs⟩ := Module.projective_lifting_property g LinearMap.id
      (LinearMap.submoduleMap_surjective _ _)
    have hgs : ∀ q : Q, (1 - e) (s q : A.V) = q := fun q => by
      have h1 := LinearMap.congr_fun hs q
      have h2 := congrArg Subtype.val h1
      exact h2
    let r : A.L →ₗ[𝓞 K] A.V := A.L.subtype - A.L.subtype ∘ₗ s ∘ₗ g
    have hr_apply : ∀ a : A.L, r a = (a : A.V) - (s (g a) : A.V) := fun a => rfl
    have hr : ∀ a : A.L, r a ∈ cutE A e A.L := by
      intro a
      refine (mem_cutE A e A.L _).2 ⟨?_, ?_⟩
      · rw [hr_apply]; exact A.L.sub_mem a.2 (s (g a)).2
      · refine ⟨r a, ?_⟩
        have h0 : (1 - e) (r a) = 0 := by
          rw [hr_apply, map_sub, hgs]
          change (1 - e) (a : A.V) - (1 - e) (a : A.V) = 0
          exact sub_self _
        have h3 : e (r a) = r a - (1 - e) (r a) := by simp
        rw [h3, h0, sub_zero]
    obtain ⟨φ, hφ⟩ := ext_lat A.L hG.2.2 ((ψ.restrictScalars (𝓞 K)) ∘ₗ r)
    have hagree : ∀ y ∈ cutE A e A.L, φ y = ψ y := by
      intro y hy
      have hy' := (mem_cutE A e A.L y).1 hy
      have hg0 : g ⟨y, hy'.1⟩ = 0 := by
        apply Subtype.ext
        change (1 - e) y = 0
        rw [LinearMap.sub_apply, Module.End.one_apply, idem_of A he hy'.2, sub_self]
      have hry : r ⟨y, hy'.1⟩ = y := by
        rw [hr_apply, hg0, map_zero]; simp
      rw [hφ ⟨y, hy'.1⟩, LinearMap.comp_apply, hry]
      rfl
    refine ⟨φ, ?_, ?_⟩
    · intro a ha
      rw [hφ ⟨a, ha⟩]
      exact h _ (hr _)
    · have hnK : ((n : ℕ) : K) ≠ 0 := by exact_mod_cast hn0.ne'
      have hcomp : φ ∘ₗ e = ψ ∘ₗ e := by
        refine LinearMap.ext_on hG.2.2 ?_
        intro a ha
        have hmem : ((n : ℕ) : 𝓞 K) • e a ∈ cutE A e A.L :=
          part1 A hn (e a) ((mem_imgE A e A.L _).2 ⟨a, ha, rfl⟩)
        have h1 := hagree _ hmem
        rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower,
          Nat.cast_smul_eq_nsmul (𝓞 K), Nat.cast_smul_eq_nsmul (𝓞 K),
          ← Nat.cast_smul_eq_nsmul K, ← Nat.cast_smul_eq_nsmul K, smul_eq_mul, smul_eq_mul] at h1
        simp only [LinearMap.comp_apply]
        exact mul_left_cancel₀ hnK h1
      refine LinearMap.ext fun x => ?_
      have h1 : ψ (e x) = ψ x := LinearMap.congr_fun hψ x
      have h2 : φ (e x) = ψ (e x) := LinearMap.congr_fun hcomp x
      simp only [LinearMap.comp_apply]
      rw [h2, h1]
  · rintro ⟨φ, hφ, rfl⟩
    rw [mem_dualLat]
    intro m hm
    obtain ⟨hmL, hmr⟩ := (mem_cutE A e A.L m).1 hm
    simp only [LinearMap.comp_apply]
    rw [idem_of A he hmr]
    exact hφ m hmL
end PI.Dv.ProjAW
