-- Prove2me | solution 1 for TateModule.isPerfPair_of_forall_apply_one_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/50d561bc-94fa-5b22-a1e0-767e26da26de

import Mathlib
import Definitions.Def_EllipticCurve_TateModule
import Theorems.Thm_TateModule_nonempty_basis_of_card_torsionBy
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateModule_isPerfPair_of_forall_apply_one_ne_zero

set_option autoImplicit false

open Module

namespace TatePerf

variable {p : ℕ} [Fact p.Prime]

theorem dvd_iff_toZMod_eq_zero (x : ℤ_[p]) : (p : ℤ_[p]) ∣ x ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]

theorem isUnit_of_toZMod_ne_zero {x : ℤ_[p]} (h : PadicInt.toZMod x ≠ 0) : IsUnit x := by
  by_contra hu
  apply h
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod]
  exact (IsLocalRing.mem_maximalIdeal _).2 hu

theorem bijective_of_nondeg {T : Type} [AddCommGroup T] [Module ℤ_[p] T] {r : ℕ}
    (v : Basis (Fin r) ℤ_[p] T) (e : T →ₗ[ℤ_[p]] T →ₗ[ℤ_[p]] ℤ_[p])
    (hleft : ∀ a : T, (∃ i, ¬ (p : ℤ_[p]) ∣ v.repr a i) → ∃ b : T, ¬ (p : ℤ_[p]) ∣ e a b) :
    Function.Bijective e := by
  classical

  set G : Matrix (Fin r) (Fin r) ℤ_[p] := LinearMap.toMatrix v v.dualBasis e with hG
  have hGij : ∀ i j, G i j = e (v j) (v i) := by
    intro i j; rw [hG, LinearMap.toMatrix_apply, Basis.dualBasis_repr]

  set Gb : Matrix (Fin r) (Fin r) (ZMod p) := G.map PadicInt.toZMod with hGb
  have hker : ∀ w : Fin r → ZMod p, Gb.mulVec w = 0 → w = 0 := by
    intro w hw
    by_contra hw0

    let c : Fin r → ℤ_[p] := fun i => ((w i).val : ℕ)
    have hc : ∀ i, PadicInt.toZMod (c i) = w i := by intro i; simp [c]
    let a : T := v.equivFun.symm c
    have ha_def : a = ∑ i, c i • v i := v.equivFun_symm_apply c
    have hrepr : ∀ i, v.repr a i = c i := by
      intro i; rw [← v.equivFun_apply, LinearEquiv.apply_symm_apply]
    have ha : ∃ i, ¬ (p : ℤ_[p]) ∣ v.repr a i := by
      by_contra hall
      push Not at hall
      apply hw0; funext i
      have := hall i
      rw [hrepr, dvd_iff_toZMod_eq_zero, hc] at this
      exact this
    obtain ⟨b, hb⟩ := hleft a ha
    apply hb

    have hcol : ∀ j, (p : ℤ_[p]) ∣ e a (v j) := by
      intro j
      rw [dvd_iff_toZMod_eq_zero]
      have hwj := congrFun hw j
      rw [Matrix.mulVec, Pi.zero_apply] at hwj
      change (∑ i, Gb j i * w i) = 0 at hwj
      have : e a (v j) = ∑ i, c i * G j i := by
        simp only [ha_def, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hGij, smul_eq_mul]
      rw [this, map_sum]
      rw [← hwj]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hc, hGb, Matrix.map_apply, mul_comm]

    rw [← v.sum_repr b, map_sum]
    refine Finset.dvd_sum fun j _ => ?_
    rw [map_smul, smul_eq_mul]
    exact Dvd.dvd.mul_left (hcol j) _
  have hdet : Gb.det ≠ 0 := by
    intro h0
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    exact hw0 (hker w hw)
  have hunit : IsUnit G.det := by
    apply isUnit_of_toZMod_ne_zero
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← hGb]; exact hdet
  have hunit' : IsUnit (LinearMap.toMatrix v v.dualBasis e).det := by rw [← hG]; exact hunit
  have hb : Function.Bijective
      ((LinearEquiv.ofIsUnitDet (f := e) (v := v) (v' := v.dualBasis) hunit' : T →ₗ[ℤ_[p]] Dual ℤ_[p] T)) :=
    (LinearEquiv.ofIsUnitDet hunit').bijective
  rwa [LinearEquiv.coe_ofIsUnitDet] at hb

theorem exists_not_dvd_repr {M : Type} [AddCommGroup M] {r : ℕ}
    (v : Basis (Fin r) ℤ_[p] (TateModule p M)) (a : TateModule p M) (ha : (a : ℕ → M) 1 ≠ 0) :
    ∃ i, ¬ (p : ℤ_[p]) ∣ v.repr a i := by
  by_contra hall
  push Not at hall
  apply ha

  choose d hd using hall
  have hay : a = (p : ℤ_[p]) • ∑ i, d i • v i := by
    rw [Finset.smul_sum, ← v.sum_repr a]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hd i, smul_smul]
  have : TateModule.proj p M 1 a = 0 := by
    rw [TateModule.proj_eq_zero_iff, hay, pow_one, PadicInt.maximalIdeal_eq_span_p]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  simpa using this

end TatePerf

open TatePerf in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] (r : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r)
    (e : TateModule p M →ₗ[ℤ_[p]] TateModule p M →ₗ[ℤ_[p]] ℤ_[p])
    (hleft : ∀ a : TateModule p M, (a : ℕ → M) 1 ≠ 0 → ∃ b : TateModule p M, ¬ (p : ℤ_[p]) ∣ e a b)
    (hright : ∀ b : TateModule p M, (b : ℕ → M) 1 ≠ 0 → ∃ a : TateModule p M, ¬ (p : ℤ_[p]) ∣ e a b) :
    e.IsPerfPair := by
  obtain ⟨v⟩ := TateModule.nonempty_basis_of_card_torsionBy p r hcard
  have hrev : ∀ a : TateModule p M, (∃ i, ¬ (p : ℤ_[p]) ∣ v.repr a i) → (a : ℕ → M) 1 ≠ 0 := by
    intro a ⟨i, hi⟩ h0
    apply hi
    have : TateModule.proj p M 1 a = 0 := by simpa using h0
    rw [TateModule.proj_eq_zero_iff, pow_one, PadicInt.maximalIdeal_eq_span_p] at this

    refine Submodule.smul_induction_on this (fun c hc y _ => ?_) (fun y z hy hz => ?_)
    · obtain ⟨c', rfl⟩ := Ideal.mem_span_singleton.1 hc
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_assoc]
      exact Dvd.intro _ rfl
    · rw [map_add, Finsupp.add_apply]; exact dvd_add hy hz
  refine ⟨bijective_of_nondeg v e (fun a ha => hleft a (hrev a ha)), ?_⟩
  exact bijective_of_nondeg v e.flip (fun b hb => by
    obtain ⟨a, ha⟩ := hright b (hrev b hb)
    exact ⟨a, by rw [LinearMap.flip_apply]; exact ha⟩)

end S_TateModule_isPerfPair_of_forall_apply_one_ne_zero
end P2MW
export P2MW.S_TateModule_isPerfPair_of_forall_apply_one_ne_zero (solution)
