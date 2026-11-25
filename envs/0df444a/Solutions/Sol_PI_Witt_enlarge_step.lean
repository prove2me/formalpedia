-- Prove2me | solution 1 for PI.Witt.enlarge_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:21:16.318967+00:00
-- url     : https://prove2.me/submissions/c288da87-7e78-4f8b-93b4-2784403b12e4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_EnlargeStep
import Theorems.Thm_PI_Witt_expand
import Theorems.Thm_PI_Witt_partner
import Theorems.Thm_PI_Witt_riesz


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Witt
variable {K V : Type} [Field K] [StarRing K] [CharZero K] [AddCommGroup V] [Module K V]
namespace PI.Witt
theorem _root_.solution [FiniteDimensional K V] (B : V →ₗ⋆[K] V →ₗ[K] K)
    (hB : ∀ x y, star (B x y) = B y x) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (U : Submodule K V) (f : U →ₗ[K] V) (hinj : Function.Injective f)
    (hf : ∀ x y : U, B (f x) (f y) = B x y)
    (r : V) (hrU : r ∈ U) (hr0 : r ≠ 0) (hr : ∀ u ∈ U, B r u = 0) :
    ∃ (U' : Submodule K V) (hlt : U < U') (f' : U' →ₗ[K] V), Function.Injective f' ∧
      (∀ x y : U', B (f' x) (f' y) = B x y) ∧ ∀ u : U, f' ⟨u, hlt.le u.2⟩ = f u := by
  classical

  obtain ⟨φ0, hφ0⟩ : ∃ φ : Module.Dual K V, φ r ≠ 0 := by
    by_contra h
    push_neg at h
    exact hr0 ((Module.forall_dual_apply_eq_zero_iff K r).1 h)
  set φ : V →ₗ[K] K := (φ0 r)⁻¹ • φ0 with hφdef
  have hφr : φ r = 1 := by simp [hφdef, hφ0]
  obtain ⟨p0, hp0⟩ := riesz B hB hnd φ
  obtain ⟨p, hpp, hpU'⟩ := partner B hB r p0 (hr r hrU) (by rw [hp0, hφr])
  have hpU : ∀ u ∈ U, B p u = φ u := fun u hu => by rw [hpU' u (hr u hu), hp0]

  set e := LinearEquiv.ofInjective f hinj with he
  obtain ⟨χ, hχ⟩ := LinearMap.exists_extend ((φ.comp U.subtype).comp e.symm.toLinearMap)
  have hχf : ∀ u : U, χ (f u) = φ u := fun u => by
    have := LinearMap.congr_fun hχ (e u)
    simpa [he] using this
  obtain ⟨q0, hq0⟩ := riesz B hB hnd χ
  set r' : U := ⟨r, hrU⟩ with hr'
  have hφr' : φ (r' : V) = 1 := hφr
  have hfr : ∀ u : U, B (f r') (f u) = 0 := fun u => by rw [hf]; exact hr u u.2
  obtain ⟨q, hqq, hqU'⟩ := partner B hB (f r') q0 (hfr r') (by rw [hq0, hχf]; exact hφr')
  have hqU : ∀ u : U, B q (f u) = φ u := fun u => by rw [hqU' _ (hfr u), hq0, hχf]

  set Φ : (U × K) →ₗ[K] V := U.subtype.coprod (LinearMap.toSpanSingleton K V p) with hΦdef
  set Ψ : (U × K) →ₗ[K] V := f.coprod (LinearMap.toSpanSingleton K V q) with hΨdef
  have hΦ : ∀ a : U × K, Φ a = (a.1 : V) + a.2 • p := fun a => by simp [hΦdef]
  have hΨ : ∀ a : U × K, Ψ a = f a.1 + a.2 • q := fun a => by simp [hΨdef]
  have hpnot : p ∉ U := by
    intro hp
    have h1 : B r p = 0 := hr p hp
    have h2 : B p r = 1 := by rw [hpU r hrU, hφr]
    have h3 := hB p r
    rw [h2, h1, star_one] at h3
    exact one_ne_zero h3
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, c⟩ h
    rw [hΦ] at h
    have hc : c = 0 := by
      by_contra hc
      apply hpnot
      have h' : c • p = -(u : V) := by
        rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact h
      have : p = c⁻¹ • -(u : V) := by rw [← h', smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [this]
      exact U.smul_mem _ (U.neg_mem u.2)
    subst hc
    refine Prod.ext ?_ rfl
    ext
    simpa using h
  have hΨinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, c⟩ h
    rw [hΨ] at h
    have hc : c = 0 := by
      have h4 := congrArg (B (f r')) h
      rw [map_add, map_smul, hfr u, ← hB q (f r'), hqU r', hφr', map_zero] at h4
      simpa using h4
    subst hc
    have hu : f u = 0 := by simpa using h
    have hu0 : u = 0 := hinj (by rw [hu, map_zero])
    subst hu0
    rfl
  have hlt : U < LinearMap.range Φ := by
    rw [SetLike.lt_iff_le_and_exists]
    refine ⟨fun u hu => ⟨(⟨u, hu⟩, 0), by simp [hΦ]⟩, p, ⟨(0, 1), by simp [hΦ]⟩, hpnot⟩
  set eΦ := LinearEquiv.ofInjective Φ hΦinj with heΦ
  have hval : ∀ x : LinearMap.range Φ, (x : V) = Φ (eΦ.symm x) := fun x =>
    (congrArg Subtype.val (eΦ.apply_symm_apply x)).symm.trans (LinearEquiv.ofInjective_apply _ _)
  refine ⟨LinearMap.range Φ, hlt, Ψ.comp eΦ.symm.toLinearMap, hΨinj.comp eΦ.symm.injective, ?_, ?_⟩
  · intro x y
    rw [hval x, hval y]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    generalize eΦ.symm x = a
    generalize eΦ.symm y = b
    obtain ⟨u, c⟩ := a
    obtain ⟨u', c'⟩ := b
    rw [hΨ, hΨ, hΦ, hΦ]
    dsimp only
    rw [expand B q (f u) (f u') c c', expand B p (u : V) (u' : V) c c', hf, hqq, hpp,
      ← hB q (f u), ← hB p (u : V), hqU u, hqU u', hpU _ u.2, hpU _ u'.2]
  · intro u
    have h5 : eΦ.symm ⟨u, hlt.le u.2⟩ = (u, 0) := by
      rw [LinearEquiv.symm_apply_eq]
      ext
      rw [LinearEquiv.ofInjective_apply, hΦ]
      simp
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h5, hΨ, zero_smul, add_zero]
end PI.Witt
