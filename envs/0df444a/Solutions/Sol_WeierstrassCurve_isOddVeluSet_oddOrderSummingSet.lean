-- Prove2me | solution 1 for WeierstrassCurve.isOddVeluSet_oddOrderSummingSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/49a7c389-4299-542f-bda9-bf3af036072e

import Mathlib
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_isOddVeluSet_oddOrderSummingSet

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_isOddVeluSet_oddOrderSummingSet.WeierstrassCurve WeierstrassCurve.Affine"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY map toAffine Affine.Point Affine.Y_eq_of_X_eq IsOddVeluSet veluGy oddOrderSummingSet mem_oddOrderSummingSet"
p2m_open "WeierstrassCurve"

namespace OSSPort

section OrderArithmetic

variable {G : Type*} [AddCommGroup G]

lemma nsmul_ne_zero_of_addOrderOf_eq_of_not_dvd {Q : G} {p : ℕ}
    (hord : addOrderOf Q = p) {k : ℕ} (hk : ¬ p ∣ k) : k • Q ≠ 0 := fun h =>
  hk (hord ▸ (addOrderOf_dvd_iff_nsmul_eq_zero).mpr h)

lemma not_dvd_of_le_half {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk1 : 1 ≤ k)
    (hkn : k ≤ (p - 1) / 2) : ¬ p ∣ k ∧ ¬ p ∣ 2 * k := by
  have hodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
  have hp1 : 2 ≤ p := hp.two_le
  have hhalf : 2 * ((p - 1) / 2) = p - 1 := by omega
  constructor
  · intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  · intro hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h) hp2
    · have := Nat.le_of_dvd (by omega) h
      omega

lemma not_dvd_add_of_le_half {p k k' : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk1 : 1 ≤ k)
    (hkn : k ≤ (p - 1) / 2) (hk'1 : 1 ≤ k') (hk'n : k' ≤ (p - 1) / 2) : ¬ p ∣ k + k' := by
  have hodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
  have hp1 : 2 ≤ p := hp.two_le
  have hhalf : 2 * ((p - 1) / 2) = p - 1 := by omega
  intro hdvd
  have := Nat.le_of_dvd (by omega) hdvd
  omega

lemma sub_nsmul_eq_neg_of_nsmul_eq_zero {Q : G} {p : ℕ} (hp : p • Q = 0) {k : ℕ}
    (hk : k ≤ p) : (p - k) • Q = -(k • Q) := by
  rw [eq_neg_iff_add_eq_zero, ← add_nsmul, Nat.sub_add_cancel hk, hp]

end OrderArithmetic

section Points

open WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

omit [DecidableEq F] in

lemma exists_some_of_ne_zero {P : W.toAffine.Point} (hP : P ≠ 0) :
    ∃ (x y : F) (h : W.toAffine.Nonsingular x y), P = Point.some x y h ∧
      P.coordsOrZero = (x, y) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · exact ⟨x, y, h, rfl, rfl⟩

omit [DecidableEq F] in

lemma some_eq_or_eq_neg_of_X_eq {x y x' y' : F} {h : W.toAffine.Nonsingular x y}
    {h' : W.toAffine.Nonsingular x' y'} (hx : x = x') :
    (Point.some x y h : W.toAffine.Point) = Point.some x' y' h' ∨
      (Point.some x y h : W.toAffine.Point) = -Point.some x' y' h' := by
  subst hx
  rcases Affine.Y_eq_of_X_eq h.left h'.left rfl with hy | hy
  · left; subst hy; rfl
  · right; rw [Point.neg_some]; subst hy; rfl

variable {Q : W.toAffine.Point} {p : ℕ}

lemma nsmul_eq_of_X_eq (hp : p.Prime) (hp2 : p ≠ 2) (hord : addOrderOf Q = p)
    {k k' : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ (p - 1) / 2) (hk'1 : 1 ≤ k')
    (hk'n : k' ≤ (p - 1) / 2)
    {x y : F} {h : W.toAffine.Nonsingular x y} (heq : k • Q = Point.some x y h)
    {x' y' : F} {h' : W.toAffine.Nonsingular x' y'} (heq' : k' • Q = Point.some x' y' h')
    (hx : x = x') : k • Q = k' • Q := by
  rcases some_eq_or_eq_neg_of_X_eq (h := h) (h' := h') hx with hPP | hPP
  · rw [heq, heq', hPP]
  · exfalso
    have hsum : (k + k') • Q = 0 := by
      rw [add_nsmul, heq, heq', hPP, neg_add_cancel]
    exact not_dvd_add_of_le_half hp hp2 hk1 hkn hk'1 hk'n
      (hord ▸ (addOrderOf_dvd_iff_nsmul_eq_zero).mpr hsum)

lemma nsmul_injOn (hp : p.Prime) (hord : addOrderOf Q = p) {k k' : ℕ}
    (hk1 : 1 ≤ k) (hkn : k ≤ (p - 1) / 2) (hk'1 : 1 ≤ k') (hk'n : k' ≤ (p - 1) / 2)
    (heq : k • Q = k' • Q) : k = k' := by
  have hp1 : 2 ≤ p := hp.two_le
  have hhalf : (p - 1) / 2 ≤ p - 1 := Nat.div_le_self _ _
  wlog hle : k ≤ k' generalizing k k'
  · exact (this hk'1 hk'n hk1 hkn heq.symm (by omega)).symm
  have hsub : (k' - k) • Q = 0 := by
    have : (k' - k) • Q + k • Q = k • Q := by
      rw [← add_nsmul, Nat.sub_add_cancel hle, heq]
    exact add_right_cancel (this.trans (zero_add _).symm)
  have hdvd : p ∣ k' - k := hord ▸ (addOrderOf_dvd_iff_nsmul_eq_zero).mpr hsub
  rcases Nat.eq_zero_or_pos (k' - k) with h0 | h0
  · omega
  · exact absurd hdvd (Nat.not_dvd_of_pos_of_lt h0 (by omega))

lemma exists_nsmul_of_mem_oddOrderSummingSet (hp : p.Prime) (hp2 : p ≠ 2)
    (hord : addOrderOf Q = p) {n : ℕ} (hn : n ≤ (p - 1) / 2) {P : F × F}
    (hP : P ∈ W.oddOrderSummingSet Q n) :
    ∃ (k : ℕ) (x y : F) (h : W.toAffine.Nonsingular x y), 1 ≤ k ∧ k ≤ n ∧
      k • Q = Point.some x y h ∧ P = (x, y) ∧ (2 * k) • Q ≠ 0 := by
  obtain ⟨k, hk1, hkn, hkP⟩ := W.mem_oddOrderSummingSet.mp hP
  have hkn' : k ≤ (p - 1) / 2 := hkn.trans hn
  obtain ⟨hndvd, hndvd2⟩ := not_dvd_of_le_half hp hp2 hk1 hkn'
  have hne : k • Q ≠ 0 := nsmul_ne_zero_of_addOrderOf_eq_of_not_dvd hord hndvd
  obtain ⟨x, y, h, heq, hcoords⟩ := exists_some_of_ne_zero hne
  exact ⟨k, x, y, h, hk1, hkn, heq, by rw [← hkP, hcoords],
    nsmul_ne_zero_of_addOrderOf_eq_of_not_dvd hord hndvd2⟩

lemma y_ne_negY_of_two_nsmul_ne_zero {x y : F} (h : W.toAffine.Nonsingular x y)
    (h2 : (2 : ℕ) • (Point.some x y h : W.toAffine.Point) ≠ 0) :
    y ≠ W.toAffine.negY x y := fun hy =>
  h2 (by rw [two_nsmul]; exact Point.add_self_of_Y_eq hy)

lemma veluGy_ne_zero_of_two_nsmul_ne_zero {x y : F} (h : W.toAffine.Nonsingular x y)
    (h2 : (2 : ℕ) • (Point.some x y h : W.toAffine.Point) ≠ 0) :
    W.veluGy x y ≠ 0 := by
  intro h0
  refine y_ne_negY_of_two_nsmul_ne_zero h h2 ?_
  have hkey : W.toAffine.negY x y = y + W.veluGy x y := by
    simp only [Affine.negY, veluGy]; ring
  rw [hkey, h0, add_zero]

end Points

end OSSPort

end WeierstrassCurve

open WeierstrassCurve.Affine.Point WeierstrassCurve.OSSPort in

theorem solution
    {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}
    {Q : W.toAffine.Point} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hord : addOrderOf Q = p) {n : ℕ} (hn : n ≤ (p - 1) / 2) :
    W.IsOddVeluSet (W.oddOrderSummingSet Q n) where
  equation P hP := by
    obtain ⟨k, x, y, h, _, _, _, hPxy, _⟩ :=
      exists_nsmul_of_mem_oddOrderSummingSet hp hp2 hord hn hP
    rw [hPxy]
    exact h.left
  gy_ne_zero P hP := by
    obtain ⟨k, x, y, h, _, _, heq, hPxy, h2k⟩ :=
      exists_nsmul_of_mem_oddOrderSummingSet hp hp2 hord hn hP
    rw [hPxy]
    refine veluGy_ne_zero_of_two_nsmul_ne_zero h fun h2 => h2k ?_
    rw [two_mul, add_nsmul, heq, ← two_nsmul, h2]
  x_injOn P hP P' hP' hx := by
    obtain ⟨k, x, y, h, hk1, hkn, heq, hPxy, _⟩ :=
      exists_nsmul_of_mem_oddOrderSummingSet hp hp2 hord hn hP
    obtain ⟨k', x', y', h', hk'1, hk'n, heq', hP'xy, _⟩ :=
      exists_nsmul_of_mem_oddOrderSummingSet hp hp2 hord hn hP'
    subst hPxy; subst hP'xy
    have hxx' : x = x' := hx
    have hQQ' := nsmul_eq_of_X_eq hp hp2 hord hk1 (hkn.trans hn) hk'1 (hk'n.trans hn)
      heq heq' hxx'
    have hpt : (Point.some x y h : W.toAffine.Point) = Point.some x' y' h' := by
      rw [← heq, ← heq']; exact hQQ'
    exact congrArg Point.coordsOrZero hpt

end S_WeierstrassCurve_isOddVeluSet_oddOrderSummingSet
end P2MW
export P2MW.S_WeierstrassCurve_isOddVeluSet_oddOrderSummingSet (solution)
