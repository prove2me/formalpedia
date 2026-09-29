-- Prove2me | solution 1 for WeierstrassCurve.IsCyclicGenKernel.variableChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/df3aa633-dde5-5745-9c1b-6b0b44edb54d

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Theorems.Thm_WeierstrassCurve_eval_prePsi_variableChange
import Theorems.Thm_WeierstrassCurve_eval_PsiSq_variableChange
import Theorems.Thm_WeierstrassCurve_eval_Phi_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_IsCyclicGenKernel_variableChange

set_option autoImplicit false

universe u

open Polynomial

namespace GenKerVCAux

variable {T : Type u} [CommRing T]

noncomputable def hom (d : ℕ) (p A B : T[X]) : T[X] :=
  ∑ i ∈ Finset.range (d + 1), C (p.coeff i) * A ^ i * B ^ (d - i)

lemma smulNumerator_eq_hom (W : WeierstrassCurve T) (a d : ℕ) (h : T[X]) :
    W.smulNumerator a d h = hom d h (W.Φ a) (W.ΨSq a) := rfl

lemma hom_add (d : ℕ) (p q A B : T[X]) : hom d (p + q) A B = hom d p A B + hom d q A B := by
  simp only [hom, coeff_add, C_add, add_mul, Finset.sum_add_distrib]

lemma hom_zero (d : ℕ) (A B : T[X]) : hom d 0 A B = 0 := by simp [hom]

lemma hom_sum {ι : Type*} (s : Finset ι) (f : ι → T[X]) (d : ℕ) (A B : T[X]) :
    hom d (∑ j ∈ s, f j) A B = ∑ j ∈ s, hom d (f j) A B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hom_zero]
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, hom_add, ih]

lemma hom_C_mul (d : ℕ) (c : T) (p A B : T[X]) : hom d (C c * p) A B = C c * hom d p A B := by
  simp only [hom, coeff_C_mul, C_mul, mul_assoc, Finset.mul_sum]

lemma hom_comp (d : ℕ) (p A B q : T[X]) : (hom d p A B).comp q = hom d p (A.comp q) (B.comp q) := by
  simp only [hom, sum_comp, mul_comp, pow_comp, C_comp]

lemma hom_smul (d : ℕ) (p A B : T[X]) (γ : T) :
    hom d p (C γ * A) (C γ * B) = C γ ^ d * hom d p A B := by
  simp only [hom, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [mul_pow, mul_pow, show C γ ^ d = C γ ^ i * C γ ^ (d - i) by rw [← pow_add, Nat.add_sub_cancel' hi']]
  ring

lemma hom_succ (d : ℕ) (p A B : T[X]) (hp : p.natDegree ≤ d) : hom (d + 1) p A B = B * hom d p A B := by
  simp only [hom]
  rw [Finset.sum_range_succ, coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le hp), C_0, zero_mul, zero_mul, add_zero,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [show d + 1 - i = (d - i) + 1 by omega, pow_succ]
  ring

lemma hom_mul_X (d : ℕ) (p A B : T[X]) : hom (d + 1) (p * X) A B = A * hom d p A B := by
  simp only [hom]
  rw [Finset.sum_range_succ', coeff_mul_X_zero, C_0, zero_mul, zero_mul, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [coeff_mul_X, show d + 1 - (i + 1) = d - i by omega, pow_succ]
  ring

lemma hom_lin_pow (α β : T) (A B : T[X]) (j : ℕ) : ∀ (d : ℕ), j ≤ d →
    hom d ((C α * X + C β) ^ j) A B = (C α * A + C β * B) ^ j * B ^ (d - j) := by
  induction j with
  | zero =>
      intro d _
      simp only [pow_zero, one_mul, Nat.sub_zero, hom]
      rw [Finset.sum_eq_single 0]
      · simp
      · intro i _ hi; rw [coeff_one, if_neg hi]; simp
      · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos d)) h
  | succ j ih =>
      intro d hjd
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
      have hjd' : j ≤ d' := by omega
      have e : (C α * X + C β) ^ (j + 1) = C α * ((C α * X + C β) ^ j * X) + C β * (C α * X + C β) ^ j := by ring
      have hdeg : ((C α * X + C β) ^ j).natDegree ≤ d' := by
        refine (natDegree_pow_le).trans ?_
        calc j * (C α * X + C β).natDegree ≤ j * 1 := Nat.mul_le_mul_left _ (by
              refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
              · exact (natDegree_C_mul_le _ _).trans natDegree_X_le
              · exact (natDegree_C _).le.trans (Nat.zero_le _))
          _ = j := mul_one j
          _ ≤ d' := hjd'
      rw [e, hom_add, hom_C_mul, hom_C_mul, hom_mul_X, hom_succ _ _ _ _ hdeg, ih d' hjd',
        show d' + 1 - (j + 1) = d' - j by omega]
      ring

lemma hom_comp_lin (d : ℕ) (p : T[X]) (hp : p.natDegree ≤ d) (α β : T) (A B : T[X]) :
    hom d (p.comp (C α * X + C β)) A B = hom d p (C α * A + C β * B) B := by
  conv_lhs => rw [as_sum_range' p (d + 1) (Nat.lt_succ_of_le hp)]
  rw [sum_comp, hom_sum]
  simp only [monomial_comp, hom_C_mul]
  show _ = ∑ i ∈ Finset.range (d + 1), C (p.coeff i) * (C α * A + C β * B) ^ i * B ^ (d - i)
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [hom_lin_pow α β A B i d hi', mul_assoc]

section VC
variable (W : WeierstrassCurve T) (vc : WeierstrassCurve.VariableChange T)

noncomputable def linIn : T[X] := Polynomial.C (((vc.u⁻¹ : Tˣ) : T) ^ 2) * (X - Polynomial.C vc.r)

noncomputable def linOut : T[X] := Polynomial.C (((vc.u : Tˣ) : T) ^ 2) * X + Polynomial.C vc.r

lemma linIn_comp_linOut : (linIn vc).comp (linOut vc) = X := by
  simp only [linIn, linOut, mul_comp, C_comp, sub_comp, X_comp]
  have : Polynomial.C (((vc.u⁻¹ : Tˣ) : T) ^ 2) * Polynomial.C (((vc.u : Tˣ) : T) ^ 2) = (1 : T[X]) := by
    rw [← C_mul, ← C_1, ← mul_pow, Units.inv_mul, one_pow]
  linear_combination (X : T[X]) * this

lemma linOut_comp_linIn : (linOut vc).comp (linIn vc) = X := by
  simp only [linIn, linOut, add_comp, mul_comp, C_comp, X_comp]
  have : Polynomial.C (((vc.u : Tˣ) : T) ^ 2) * Polynomial.C (((vc.u⁻¹ : Tˣ) : T) ^ 2) = (1 : T[X]) := by
    rw [← C_mul, ← C_1, ← mul_pow, Units.mul_inv, one_pow]
  linear_combination (X - Polynomial.C vc.r : T[X]) * this

lemma eval_map_C (p q : T[X]) : (p.map Polynomial.C).eval q = p.comp q := by
  rw [eval_map]; rfl

lemma coe_map_u_inv : (((vc.map (Polynomial.C : T →+* T[X])).u⁻¹ : T[X]ˣ) : T[X]) = Polynomial.C ((vc.u⁻¹ : Tˣ) : T) := by
  simp [WeierstrassCurve.VariableChange.map]

lemma map_r : (vc.map (Polynomial.C : T →+* T[X])).r = Polynomial.C vc.r := rfl

lemma preΨ_comp_linIn (n : ℤ) :
    ((vc • W).preΨ n).comp (linIn vc) =
      Polynomial.C (((vc.u⁻¹ : Tˣ) : T) ^ (n.natAbs ^ 2 - if Even n then 4 else 1)) * W.preΨ n := by
  have h := WeierstrassCurve.eval_prePsi_variableChange (W.map (Polynomial.C : T →+* T[X]))
    (vc.map (Polynomial.C : T →+* T[X])) n X
  rw [WeierstrassCurve.map_variableChange, WeierstrassCurve.map_preΨ, WeierstrassCurve.map_preΨ, eval_map_C, eval_map_C,
    comp_X, coe_map_u_inv, map_r, ← C_pow, ← C_pow] at h
  exact h

lemma ΨSq_comp_linIn (n : ℤ) :
    ((vc • W).ΨSq n).comp (linIn vc) = Polynomial.C (((vc.u⁻¹ : Tˣ) : T) ^ (2 * (n.natAbs ^ 2 - 1))) * W.ΨSq n := by
  have h := WeierstrassCurve.eval_PsiSq_variableChange (W.map (Polynomial.C : T →+* T[X]))
    (vc.map (Polynomial.C : T →+* T[X])) n X
  rw [WeierstrassCurve.map_variableChange, WeierstrassCurve.map_ΨSq, WeierstrassCurve.map_ΨSq, eval_map_C, eval_map_C,
    comp_X, coe_map_u_inv, map_r, ← C_pow, ← C_pow] at h
  exact h

lemma Φ_comp_linIn (n : ℤ) :
    ((vc • W).Φ n).comp (linIn vc) =
      Polynomial.C (((vc.u⁻¹ : Tˣ) : T) ^ (2 * n.natAbs ^ 2)) * (W.Φ n - Polynomial.C vc.r * W.ΨSq n) := by
  have h := WeierstrassCurve.eval_Phi_variableChange (W.map (Polynomial.C : T →+* T[X]))
    (vc.map (Polynomial.C : T →+* T[X])) n X
  rw [WeierstrassCurve.map_variableChange, WeierstrassCurve.map_Φ, WeierstrassCurve.map_Φ, WeierstrassCurve.map_ΨSq,
    eval_map_C, eval_map_C, eval_map_C, comp_X, comp_X, coe_map_u_inv, map_r, ← C_pow, ← C_pow] at h
  exact h

end VC

end GenKerVCAux

open ModularCurve

open GenKerVCAux in

theorem solution
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T) (p k : ℕ)
    (h : Polynomial T) (hh : W.IsCyclicGenKernel p k h) :
    (C • W).IsCyclicGenKernel p k (ModularCurve.kernelVariableChangeDeg C (Nat.totient (p ^ k) / 2) h) := by
  classical
  obtain ⟨h1, h2, h3, h4⟩ := hh
  set d : ℕ := Nat.totient (p ^ k) / 2 with hd
  have hkv : ModularCurve.kernelVariableChangeDeg C d h =
      Polynomial.C (((C.u⁻¹ : Tˣ) : T) ^ (2 * d)) * h.comp (linOut C) := by
    show Polynomial.C (((C.u⁻¹ : Tˣ) : T) ^ (2 * d)) * h.comp (Polynomial.C ((C.u : Tˣ) : T) ^ 2 * X + Polynomial.C C.r) = _
    rw [← C_pow]; rfl
  have hc : IsUnit (Polynomial.C (((C.u⁻¹ : Tˣ) : T) ^ (2 * d)) : T[X]) :=
    Polynomial.isUnit_C.mpr ((C.u⁻¹).isUnit.pow _)
  have hM1 : (linOut C).natDegree ≤ 1 := natDegree_linear_le

  have hcompdvd : ∀ {p q : T[X]}, p ∣ q → p.comp (linOut C) ∣ q.comp (linOut C) := by
    rintro p q ⟨k, rfl⟩; exact ⟨k.comp (linOut C), by rw [mul_comp]⟩

  have hresub : ∀ p : T[X], p = (p.comp (linIn C)).comp (linOut C) := by
    intro p; rw [comp_assoc, linIn_comp_linOut, comp_X]

  have hPre : ∀ n : ℤ, (C • W).preΨ n =
      Polynomial.C (((C.u⁻¹ : Tˣ) : T) ^ (n.natAbs ^ 2 - if Even n then 4 else 1)) * (W.preΨ n).comp (linOut C) := by
    intro n
    have e := hresub ((C • W).preΨ n)
    rw [preΨ_comp_linIn, C_mul_comp] at e
    exact e
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    rw [hkv]
    refine (natDegree_C_mul_le _ _).trans (natDegree_comp_le.trans ?_)
    calc h.natDegree * (linOut C).natDegree ≤ d * 1 := Nat.mul_le_mul h1 hM1
      _ = d := mul_one d
  ·
    rw [hkv, coeff_C_mul]
    rcases subsingleton_or_nontrivial T with hT | hT
    · exact Subsingleton.elim _ _
    have hu2 : (((C.u : Tˣ) : T) ^ 2) ≠ 0 := (C.u.isUnit.pow 2).ne_zero
    have hdegM : (linOut C).natDegree = 1 := natDegree_linear hu2
    have hlcM : (linOut C).leadingCoeff = ((C.u : Tˣ) : T) ^ 2 := leadingCoeff_linear hu2
    have hdegh : h.natDegree = d := natDegree_eq_of_le_of_coeff_ne_zero h1 (by rw [h2]; exact one_ne_zero)
    have hlch : h.leadingCoeff = 1 := by rw [leadingCoeff, hdegh, h2]
    have key := coeff_comp_degree_mul_degree (p := h) (q := linOut C) (by rw [hdegM]; exact one_ne_zero)
    rw [hdegh, hdegM, mul_one, hlch, hlcM, one_mul] at key
    rw [key, pow_mul, ← mul_pow, ← mul_pow, Units.inv_mul, one_pow, one_pow]
  ·
    rw [hkv, hPre ((p : ℤ) ^ (k - 1)), hPre ((p : ℤ) ^ k)]
    have hc' : IsUnit (Polynomial.C (((C.u⁻¹ : Tˣ) : T) ^
        (((p : ℤ) ^ (k - 1)).natAbs ^ 2 - if Even ((p : ℤ) ^ (k - 1)) then 4 else 1)) : T[X]) :=
      Polynomial.isUnit_C.mpr ((C.u⁻¹).isUnit.pow _)
    have e : Polynomial.C (((C.u⁻¹ : Tˣ) : T) ^ (2 * d)) * h.comp (linOut C) *
        (Polynomial.C (((C.u⁻¹ : Tˣ) : T) ^
          (((p : ℤ) ^ (k - 1)).natAbs ^ 2 - if Even ((p : ℤ) ^ (k - 1)) then 4 else 1)) *
          (W.preΨ ((p : ℤ) ^ (k - 1))).comp (linOut C)) =
        (Polynomial.C (((C.u⁻¹ : Tˣ) : T) ^ (2 * d)) * Polynomial.C (((C.u⁻¹ : Tˣ) : T) ^
          (((p : ℤ) ^ (k - 1)).natAbs ^ 2 - if Even ((p : ℤ) ^ (k - 1)) then 4 else 1))) *
          (h * W.preΨ ((p : ℤ) ^ (k - 1))).comp (linOut C) := by
      rw [mul_comp]; ring
    rw [e]
    exact ((hc.mul hc').mul_left_dvd).mpr ((hcompdvd h3).mul_left _)
  ·
    intro a ha2 had hpa
    have hS := h4 a ha2 had hpa
    rw [hkv]
    set ui : T := ((C.u⁻¹ : Tˣ) : T) with hui
    set γ : T := ui ^ (2 * (a ^ 2 - 1)) with hγ
    have hunit : Polynomial.C (((C.u : Tˣ) : T) ^ 2) * Polynomial.C (ui ^ 2) = (1 : T[X]) := by
      rw [← C_mul, ← C_1, ← mul_pow, hui, Units.mul_inv, one_pow]
    have hpow : ui ^ (2 * a ^ 2) = γ * ui ^ 2 := by
      have ha1 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ (by omega)
      rw [hγ, ← pow_add]
      congr 1
      generalize a ^ 2 = e at ha1 ⊢
      omega

    have hA : (Polynomial.C (((C.u : Tˣ) : T) ^ 2) * (C • W).Φ a + Polynomial.C C.r * (C • W).ΨSq a).comp (linIn C) =
        Polynomial.C γ * W.Φ a := by
      rw [add_comp, C_mul_comp, C_mul_comp, Φ_comp_linIn, ΨSq_comp_linIn, Int.natAbs_natCast, ← hui, hpow, ← hγ, C_mul]
      linear_combination (Polynomial.C γ * (W.Φ ↑a - Polynomial.C C.r * W.ΨSq ↑a)) * hunit
    have hB : ((C • W).ΨSq a).comp (linIn C) = Polynomial.C γ * W.ΨSq a := by
      rw [ΨSq_comp_linIn, Int.natAbs_natCast, ← hui, ← hγ]
    have key : (C • W).smulNumerator a d (Polynomial.C (ui ^ (2 * d)) * h.comp (linOut C)) =
        Polynomial.C (ui ^ (2 * d)) * (Polynomial.C γ ^ d * (W.smulNumerator a d h).comp (linOut C)) := by
      rw [smulNumerator_eq_hom, hom_C_mul, show linOut C = Polynomial.C (((C.u : Tˣ) : T) ^ 2) * X + Polynomial.C C.r from rfl,
        hom_comp_lin d h h1]
      conv_lhs => rw [hresub (hom d h _ _)]
      rw [hom_comp, hA, hB, hom_smul, ← smulNumerator_eq_hom]
      simp only [mul_comp, C_comp, pow_comp]
      rfl
    rw [key]
    exact mul_dvd_mul_left _ ((hcompdvd hS).mul_left _)

end S_WeierstrassCurve_IsCyclicGenKernel_variableChange
end P2MW
export P2MW.S_WeierstrassCurve_IsCyclicGenKernel_variableChange (solution)
