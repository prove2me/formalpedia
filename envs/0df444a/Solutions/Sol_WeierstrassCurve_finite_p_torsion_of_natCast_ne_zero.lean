-- Prove2me | solution 1 for WeierstrassCurve.finite_p_torsion_of_natCast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/61b89cbd-0c12-5bce-a385-a329ff83b94b

import Mathlib
import Definitions.Def_WeierstrassCurve_DivPolyMulFormula
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_finite_p_torsion_of_natCast_ne_zero

set_option autoImplicit false

open Polynomial

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine ΨSq_ofNat mk.injEq map natDegree_preΨ' mk Affine.Point.some reduction preΨ' ΨSq toAffine Affine.Point Affine.equation_iff_nonsingular Affine.Point.some_ne_zero Affine.Y_eq_of_X_eq Affine.MFred Affine.LowTorsionFree Affine.mfred_all Affine.ΨSq_eval_eq_zero_of_succ_nsmul_eq_zero"
p2m_open "WeierstrassCurve"

universe u

variable {F : Type u} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {p : ℕ}

private abbrev _root_.WeierstrassCurve.n_torsionGen (W : WeierstrassCurve F) (n : ℕ) : Type u := Submodule.torsionBy ℤ W.toAffine.Point n

p2m_export "WeierstrassCurve" "n_torsionGen"
section UpperBound

omit [DecidableEq F] in

private lemma eval_ΨSq_eq_zero_iff_preΨ'_specialFibre (hp : p.Prime) (hp5 : 5 ≤ p) {x : F} :
    (W.ΨSq (p : ℤ)).eval x = 0 ↔ (W.preΨ' p).eval x = 0 := by
  have hodd : ¬ Even p := Nat.not_even_iff_odd.mpr (hp.odd_of_ne_two (by omega))
  rw [ΨSq_ofNat, if_neg hodd, mul_one, eval_pow, pow_eq_zero_iff two_ne_zero]

omit [DecidableEq F] in

lemma preΨ'_p_ne_zero_of_natCast_ne_zero (hp : p.Prime) (hp5 : 5 ≤ p) (hpF : (p : F) ≠ 0) :
    W.preΨ' p ≠ 0 := by
  have hodd : ¬ Even p := Nat.not_even_iff_odd.mpr (hp.odd_of_ne_two (by omega))
  have hdeg : (W.preΨ' p).natDegree = (p ^ 2 - 1) / 2 := by
    rw [W.natDegree_preΨ' hpF, if_neg hodd]
  intro h
  rw [h, natDegree_zero] at hdeg
  have h25 : 5 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp5 2
  omega

lemma finite_equation_fiber (x : F) : Finite {y : F // W.toAffine.Equation x y} := by
  rcases isEmpty_or_nonempty {y : F // W.toAffine.Equation x y} with h | ⟨⟨y₀, hy₀⟩⟩
  · infer_instance
  · refine Finite.of_injective
      (fun y => (⟨y.1, ?_⟩ : ({y₀, W.toAffine.negY x y₀} : Finset F)))
      (fun y y' h => Subtype.ext (by simpa only [Subtype.mk.injEq] using h))
    rcases Affine.Y_eq_of_X_eq y.2 hy₀ rfl with h | h <;>
      simp [Finset.mem_insert, Finset.mem_singleton, h]

lemma card_equation_fiber_le_two (x : F) :
    Nat.card {y : F // W.toAffine.Equation x y} ≤ 2 := by
  rcases isEmpty_or_nonempty {y : F // W.toAffine.Equation x y} with h | ⟨⟨y₀, hy₀⟩⟩
  · simp [Nat.card_of_isEmpty]
  · have hinj : Function.Injective
        (fun y : {y : F // W.toAffine.Equation x y} =>
          (⟨y.1, by
            rcases Affine.Y_eq_of_X_eq y.2 hy₀ rfl with h | h <;>
              simp [Finset.mem_insert, Finset.mem_singleton, h]⟩ :
            ({y₀, W.toAffine.negY x y₀} : Finset F))) :=
      fun y y' h => Subtype.ext (by simpa only [Subtype.mk.injEq] using h)
    calc Nat.card {y : F // W.toAffine.Equation x y}
        ≤ Nat.card ({y₀, W.toAffine.negY x y₀} : Finset F) :=
          Nat.card_le_card_of_injective _ hinj
      _ = ({y₀, W.toAffine.negY x y₀} : Finset F).card := Nat.card_eq_finsetCard _
      _ ≤ 2 := by
          calc ({y₀, W.toAffine.negY x y₀} : Finset F).card
              ≤ ({W.toAffine.negY x y₀} : Finset F).card + 1 := Finset.card_insert_le _ _
            _ ≤ 2 := by simp

private lemma lowTorsionFree_of_prime_nsmul_eq_zero_specialFibre (hp : p.Prime) {x y : F}
    (h : W.toAffine.Nonsingular x y)
    (hkill : p • (Affine.Point.some x y h : W.toAffine.Point) = 0) :
    Affine.LowTorsionFree (p - 1) h := by
  intro k hk1 hkp hk0
  have hnotdvd : ¬ p ∣ k := fun hdvd =>
    absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)
  have hgcd : Nat.gcd p k = 1 := (hp.coprime_iff_not_dvd.mpr hnotdvd).gcd_eq_one
  have hdvd : addOrderOf (Affine.Point.some x y h : W.toAffine.Point) ∣ Nat.gcd p k :=
    Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hkill) (addOrderOf_dvd_of_nsmul_eq_zero hk0)
  rw [hgcd, Nat.dvd_one] at hdvd
  exact Affine.Point.some_ne_zero h (AddMonoid.addOrderOf_eq_one_iff.mp hdvd)

lemma preΨ'_eval_eq_zero_of_prime_nsmul_eq_zero (hp : p.Prime) (hp5 : 5 ≤ p) {x y : F}
    (h : W.toAffine.Nonsingular x y)
    (hkill : p • (Affine.Point.some x y h : W.toAffine.Point) = 0) :
    (W.preΨ' p).eval x = 0 := by
  have hfree : Affine.LowTorsionFree (p - 1) h :=
    lowTorsionFree_of_prime_nsmul_eq_zero_specialFibre hp h hkill
  have hmf : Affine.MFred (p - 1) h :=
    Affine.mfred_all h (p - 1) (by omega) hfree
  have hmf' : Affine.MFred (p - 1 - 2) h :=
    Affine.mfred_all h (p - 1 - 2) (by omega) (hfree.mono (by omega))
  have hkill' : (p - 1 + 1) • (Affine.Point.some x y h : W.toAffine.Point) = 0 := by
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have hroot := Affine.ΨSq_eval_eq_zero_of_succ_nsmul_eq_zero
    (m := p - 1) (by omega) h hfree hmf hmf' hkill'
  have hcast : (((p - 1 : ℕ) : ℤ) + 1) = (p : ℤ) := by omega
  rw [hcast] at hroot
  exact (eval_ΨSq_eq_zero_iff_preΨ'_specialFibre hp hp5).mp hroot

variable (W) in

theorem finite_n_torsionGen_of_natCast_ne_zero [W.IsElliptic] (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpF : (p : F) ≠ 0) : Finite (W.n_torsionGen p) := by
  classical
  have hne : W.preΨ' p ≠ 0 := preΨ'_p_ne_zero_of_natCast_ne_zero hp hp5 hpF
  have hequiv : {x : F // (W.preΨ' p).eval x = 0} ≃ (W.preΨ' p).roots.toFinset :=
    (Equiv.refl F).subtypeEquiv fun x => by
      rw [Multiset.mem_toFinset, mem_roots hne, IsRoot]
      exact Iff.rfl
  haveI : Finite {x : F // (W.preΨ' p).eval x = 0} := Finite.of_equiv _ hequiv.symm
  haveI hfibFin : ∀ x : {x : F // (W.preΨ' p).eval x = 0},
      Finite {y : F // W.toAffine.Equation x.1 y} := fun x => finite_equation_fiber x.1
  let toPoint : Option ((x : {x : F // (W.preΨ' p).eval x = 0}) ×
      {y : F // W.toAffine.Equation x.1 y}) → W.toAffine.Point :=
    fun z => match z with
      | none => 0
      | some ⟨x, y⟩ =>
          Affine.Point.some x.1 y.1 ((Affine.equation_iff_nonsingular (W := W)).mp y.2)
  have hcover : ∀ Q : W.n_torsionGen p, ∃ z, toPoint z = (Q : W.toAffine.Point) := by
    rintro ⟨Q, hQ⟩
    have hkillz : ((p : ℤ)) • Q = 0 := (Submodule.mem_torsionBy_iff _ _).mp hQ
    have hkill : p • Q = 0 := by rwa [natCast_zsmul] at hkillz
    rcases Q with _ | ⟨x, y, h⟩
    · exact ⟨none, rfl⟩
    · exact ⟨some ⟨⟨x, preΨ'_eval_eq_zero_of_prime_nsmul_eq_zero hp hp5 h hkill⟩, ⟨y, h.1⟩⟩, rfl⟩
  let pick : W.n_torsionGen p →
      Option ((x : {x : F // (W.preΨ' p).eval x = 0}) × {y : F // W.toAffine.Equation x.1 y}) :=
    fun Q => (hcover Q).choose
  have hpick : ∀ Q, toPoint (pick Q) = (Q : W.toAffine.Point) := fun Q => (hcover Q).choose_spec
  have hpick_inj : Function.Injective pick := fun Q Q' hQQ' => by
    apply Subtype.ext
    rw [← hpick Q, ← hpick Q', hQQ']
  exact Finite.of_injective pick hpick_inj

variable (W) in

theorem card_p_torsion_le_of_natCast_ne_zero [W.IsElliptic] (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpF : (p : F) ≠ 0) : Nat.card (W.n_torsionGen p) ≤ p ^ 2 := by
  classical
  have hne : W.preΨ' p ≠ 0 := preΨ'_p_ne_zero_of_natCast_ne_zero hp hp5 hpF

  have hequiv : {x : F // (W.preΨ' p).eval x = 0} ≃ (W.preΨ' p).roots.toFinset :=
    (Equiv.refl F).subtypeEquiv fun x => by
      rw [Multiset.mem_toFinset, mem_roots hne, IsRoot]
      exact Iff.rfl
  haveI : Finite {x : F // (W.preΨ' p).eval x = 0} := Finite.of_equiv _ hequiv.symm
  haveI : Fintype {x : F // (W.preΨ' p).eval x = 0} := Fintype.ofFinite _
  haveI hfibFin : ∀ x : {x : F // (W.preΨ' p).eval x = 0},
      Finite {y : F // W.toAffine.Equation x.1 y} := fun x => finite_equation_fiber x.1

  let toPoint : Option ((x : {x : F // (W.preΨ' p).eval x = 0}) ×
      {y : F // W.toAffine.Equation x.1 y}) → W.toAffine.Point :=
    fun z => match z with
      | none => 0
      | some ⟨x, y⟩ =>
          Affine.Point.some x.1 y.1 ((Affine.equation_iff_nonsingular (W := W)).mp y.2)

  have hcover : ∀ Q : W.n_torsionGen p, ∃ z, toPoint z = (Q : W.toAffine.Point) := by
    rintro ⟨Q, hQ⟩
    have hkillz : ((p : ℤ)) • Q = 0 := (Submodule.mem_torsionBy_iff _ _).mp hQ
    have hkill : p • Q = 0 := by rwa [natCast_zsmul] at hkillz
    rcases Q with _ | ⟨x, y, h⟩
    · exact ⟨none, rfl⟩
    · exact ⟨some ⟨⟨x, preΨ'_eval_eq_zero_of_prime_nsmul_eq_zero hp hp5 h hkill⟩, ⟨y, h.1⟩⟩, rfl⟩

  let pick : W.n_torsionGen p →
      Option ((x : {x : F // (W.preΨ' p).eval x = 0}) × {y : F // W.toAffine.Equation x.1 y}) :=
    fun Q => (hcover Q).choose
  have hpick : ∀ Q, toPoint (pick Q) = (Q : W.toAffine.Point) := fun Q => (hcover Q).choose_spec
  have hpick_inj : Function.Injective pick := fun Q Q' hQQ' => by
    apply Subtype.ext
    rw [← hpick Q, ← hpick Q', hQQ']
  have hcard := Nat.card_le_card_of_injective pick hpick_inj
  rw [Finite.card_option] at hcard

  have hsigma : Nat.card ((x : {x : F // (W.preΨ' p).eval x = 0}) ×
      {y : F // W.toAffine.Equation x.1 y})
      ≤ 2 * (W.preΨ' p).roots.toFinset.card := by
    rw [Nat.card_sigma]
    have hsum : ∀ x : {x : F // (W.preΨ' p).eval x = 0},
        Nat.card {y : F // W.toAffine.Equation x.1 y} ≤ 2 := fun x =>
      card_equation_fiber_le_two x.1
    calc ∑ x : {x : F // (W.preΨ' p).eval x = 0},
          Nat.card {y : F // W.toAffine.Equation x.1 y}
        ≤ ∑ _x : {x : F // (W.preΨ' p).eval x = 0}, 2 :=
          Finset.sum_le_sum fun x _ => hsum x
      _ = 2 * Fintype.card {x : F // (W.preΨ' p).eval x = 0} := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, mul_comm]
      _ = 2 * (W.preΨ' p).roots.toFinset.card := by
          rw [← Nat.card_eq_fintype_card, Nat.card_congr hequiv, Nat.card_eq_finsetCard]

  have hodd : ¬ Even p := Nat.not_even_iff_odd.mpr (hp.odd_of_ne_two (by omega))
  have hdeg : (W.preΨ' p).natDegree = (p ^ 2 - 1) / 2 := by
    rw [W.natDegree_preΨ' hpF, if_neg hodd]
  have hroots : (W.preΨ' p).roots.toFinset.card ≤ (p ^ 2 - 1) / 2 := by
    calc (W.preΨ' p).roots.toFinset.card
        ≤ Multiset.card (W.preΨ' p).roots := Multiset.toFinset_card_le _
      _ ≤ (W.preΨ' p).natDegree := Polynomial.card_roots' _
      _ = (p ^ 2 - 1) / 2 := hdeg

  have hsq : p ^ 2 % 2 = 1 := Nat.odd_iff.mp ((hp.odd_of_ne_two (by omega)).pow)
  have h25 : 5 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp5 2
  omega

end UpperBound

end WeierstrassCurve

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_finite_p_torsion_of_natCast_ne_zero.WeierstrassCurve WeierstrassCurve.Affine"

theorem solution {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {p : ℕ}
    [W.IsElliptic] (hp : p.Prime) (hp5 : 5 ≤ p) (hpF : (p : F) ≠ 0) :
    Finite (Submodule.torsionBy ℤ W.toAffine.Point p) :=
  WeierstrassCurve.finite_n_torsionGen_of_natCast_ne_zero W hp hp5 hpF

end S_WeierstrassCurve_finite_p_torsion_of_natCast_ne_zero
end P2MW
export P2MW.S_WeierstrassCurve_finite_p_torsion_of_natCast_ne_zero (solution)
