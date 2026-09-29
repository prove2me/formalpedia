-- Prove2me | solution 1 for WeierstrassCurve.exists_veluQuotient_descent_of_smul_mem_zmultiples
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/b8ac4624-7cb3-59fb-9ee1-381aa31bc751

import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_veluQuotient_descent_of_smul_mem_zmultiples

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_veluQuotient_descent_of_smul_mem_zmultiples.WeierstrassCurve WeierstrassCurve.Affine"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ Affine Affine.negY a₃ map_map a₁ map map_b₂ b₂ Ψ₂Sq a₄ a₂ a₆ c₆ toAffine Affine.Point map_b₆ map_a₆ b₆ map_a₁ map_a₄ c₄ Affine.Y_eq_of_X_eq map_a₂ b₄ map_a₃ IsOddVeluSet veluGy veluW veluT_eq veluU_eq_Ψ₂Sq_eval veluTSum veluWSum veluQuotient veluQuotient_a₁ veluQuotient_a₂ veluQuotient_a₃ veluQuotient_a₄ veluQuotient_a₆ oddOrderSummingSet mem_oddOrderSummingSet"
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

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ Affine Affine.negY a₃ map_map a₁ map map_b₂ b₂ Ψ₂Sq a₄ a₂ a₆ c₆ toAffine Affine.Point map_b₆ map_a₆ b₆ map_a₁ map_a₄ c₄ Affine.Y_eq_of_X_eq map_a₂ b₄ map_a₃ IsOddVeluSet veluGy veluW veluT_eq veluU_eq_Ψ₂Sq_eval veluTSum veluWSum veluQuotient veluQuotient_a₁ veluQuotient_a₂ veluQuotient_a₃ veluQuotient_a₄ veluQuotient_a₆ oddOrderSummingSet mem_oddOrderSummingSet"
namespace OSSPort
p2m_open "WeierstrassCurve"

open WeierstrassCurve.Affine WeierstrassCurve.Affine.Point in

theorem isOddVeluSet_oddOrderSummingSet
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

end WeierstrassCurve.OSSPort

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ Affine Affine.negY a₃ map_map a₁ map map_b₂ b₂ Ψ₂Sq a₄ a₂ a₆ c₆ toAffine Affine.Point map_b₆ map_a₆ b₆ map_a₁ map_a₄ c₄ Affine.Y_eq_of_X_eq map_a₂ b₄ map_a₃ IsOddVeluSet veluGy veluW veluT_eq veluU_eq_Ψ₂Sq_eval veluTSum veluWSum veluQuotient veluQuotient_a₁ veluQuotient_a₂ veluQuotient_a₃ veluQuotient_a₄ veluQuotient_a₆ oddOrderSummingSet mem_oddOrderSummingSet"
p2m_open "WeierstrassCurve"

namespace OSSPort

section Galois

open WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

lemma coordsOrZero_fst_neg {R : Type*} [CommRing R] {W : Affine R} (P : W.Point) :
    (-P).coordsOrZero.1 = P.coordsOrZero.1 := by
  cases P <;> rfl

lemma zsmul_eq_emod_zsmul_of_nsmul_eq_zero {G : Type*} [AddCommGroup G] {g : G} {p : ℕ}
    (hp : p • g = 0) (m : ℤ) : m • g = (m % (p : ℤ)) • g := by
  have hp' : (p : ℤ) • g = 0 := by rw [natCast_zsmul]; exact hp
  conv_lhs => rw [show m = (p : ℤ) * (m / (p : ℤ)) + m % (p : ℤ) from
    (Int.mul_ediv_add_emod m (p : ℤ)).symm]
  rw [add_zsmul, mul_comm ((p : ℤ)) (m / (p : ℤ)), ← smul_smul, hp', smul_zero, zero_add]

local notation "Qbar" => AlgebraicClosure ℚ

variable {W : WeierstrassCurve ℚ} {Q : (W⁄Qbar).toAffine.Point} {p : ℕ}

lemma fst_mem_image_fst_of_mem_zmultiples (hp : p.Prime) (hp2 : p ≠ 2)
    (hord : addOrderOf Q = p) {P : (W⁄Qbar).toAffine.Point}
    (hP : P ∈ AddSubgroup.zmultiples Q) (hP0 : P ≠ 0) :
    P.coordsOrZero.1 ∈ ((W⁄Qbar).oddOrderSummingSet Q ((p - 1) / 2)).image Prod.fst := by
  have hp1 : 2 ≤ p := hp.two_le
  have hodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
  have hhalf : 2 * ((p - 1) / 2) = p - 1 := by omega
  have hppos : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  have hpQ : p • Q = 0 := by rw [← hord]; exact addOrderOf_nsmul_eq_zero _
  obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hP
  rw [zsmul_eq_emod_zsmul_of_nsmul_eq_zero hpQ] at hP0 ⊢
  have hr0 : 0 ≤ m % (p : ℤ) := Int.emod_nonneg m (by omega)
  have hrp : m % (p : ℤ) < (p : ℤ) := Int.emod_lt_of_pos m hppos
  obtain ⟨r', hr'⟩ : ∃ r' : ℕ, (r' : ℤ) = m % (p : ℤ) :=
    ⟨(m % (p : ℤ)).toNat, Int.toNat_of_nonneg hr0⟩
  rw [← hr', natCast_zsmul] at hP0 ⊢
  have hr'p : r' < p := by omega
  have hr'0 : 1 ≤ r' := by
    rcases Nat.eq_zero_or_pos r' with h | h
    · exact absurd (by rw [h, zero_nsmul]) hP0
    · exact h
  rcases (by omega : r' ≤ (p - 1) / 2 ∨ (p - 1) / 2 < r') with hcase | hcase
  · exact Finset.mem_image_of_mem _
      ((W⁄Qbar).mem_oddOrderSummingSet.mpr ⟨r', hr'0, hcase, rfl⟩)
  · have hk1 : 1 ≤ p - r' := by omega
    have hkn : p - r' ≤ (p - 1) / 2 := by omega
    have hneg : r' • Q = -((p - r') • Q) := by
      rw [sub_nsmul_eq_neg_of_nsmul_eq_zero hpQ (by omega : r' ≤ p), neg_neg]
    rw [hneg, coordsOrZero_fst_neg]
    exact Finset.mem_image_of_mem _
      ((W⁄Qbar).mem_oddOrderSummingSet.mpr ⟨p - r', hk1, hkn, rfl⟩)

lemma coordsOrZero_fst_algEquiv_smul (σ : Qbar ≃ₐ[ℚ] Qbar) (P : (W⁄Qbar).toAffine.Point) :
    (σ • P).coordsOrZero.1 = σ P.coordsOrZero.1 := by
  rcases P with _ | ⟨a, b, hb⟩
  · show (0 : Qbar) = σ 0
    exact (_root_.map_zero σ).symm
  · rw [Point.algEquiv_smul_def, Point.map_some]
    rfl

end Galois

end OSSPort

end WeierstrassCurve

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ Affine Affine.negY a₃ map_map a₁ map map_b₂ b₂ Ψ₂Sq a₄ a₂ a₆ c₆ toAffine Affine.Point map_b₆ map_a₆ b₆ map_a₁ map_a₄ c₄ Affine.Y_eq_of_X_eq map_a₂ b₄ map_a₃ IsOddVeluSet veluGy veluW veluT_eq veluU_eq_Ψ₂Sq_eval veluTSum veluWSum veluQuotient veluQuotient_a₁ veluQuotient_a₂ veluQuotient_a₃ veluQuotient_a₄ veluQuotient_a₆ oddOrderSummingSet mem_oddOrderSummingSet"
namespace OSSPort
p2m_open "WeierstrassCurve"

open WeierstrassCurve.Affine WeierstrassCurve.Affine.Point in

theorem algEquiv_mem_image_fst_oddOrderSummingSet
    {W : WeierstrassCurve ℚ} {Q : (W⁄(AlgebraicClosure ℚ)).toAffine.Point} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hord : addOrderOf Q = p)
    (hstab : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q ∈ AddSubgroup.zmultiples Q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {t : AlgebraicClosure ℚ}
    (ht : t ∈ ((W⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q ((p - 1) / 2)).image Prod.fst) :
    σ t ∈ ((W⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q ((p - 1) / 2)).image Prod.fst := by
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨k, hk1, hkn, rfl⟩ := (W⁄(AlgebraicClosure ℚ)).mem_oddOrderSummingSet.mp hP
  obtain ⟨hndvd, _⟩ := not_dvd_of_le_half hp hp2 hk1 hkn
  have hkQ : k • Q ≠ 0 := nsmul_ne_zero_of_addOrderOf_eq_of_not_dvd hord hndvd
  rw [← coordsOrZero_fst_algEquiv_smul]
  have hmem : σ • (k • Q) ∈ AddSubgroup.zmultiples Q := by
    have hcomm : σ • (k • Q) = k • (σ • Q) := by
      have h1 := Point.algEquiv_smul_zsmul σ (k : ℤ) Q
      rwa [natCast_zsmul, natCast_zsmul] at h1
    rw [hcomm]
    exact nsmul_mem (hstab σ) k
  have hne : σ • (k • Q) ≠ 0 := by
    obtain ⟨a, b, hb, heqk, _⟩ := exists_some_of_ne_zero hkQ
    rw [heqk, Point.algEquiv_smul_def, Point.map_some]
    exact Point.some_ne_zero _
  exact fst_mem_image_fst_of_mem_zmultiples hp hp2 hord hmem hne

end WeierstrassCurve.OSSPort

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ Affine Affine.negY a₃ map_map a₁ map map_b₂ b₂ Ψ₂Sq a₄ a₂ a₆ c₆ toAffine Affine.Point map_b₆ map_a₆ b₆ map_a₁ map_a₄ c₄ Affine.Y_eq_of_X_eq map_a₂ b₄ map_a₃ IsOddVeluSet veluGy veluW veluT_eq veluU_eq_Ψ₂Sq_eval veluTSum veluWSum veluQuotient veluQuotient_a₁ veluQuotient_a₂ veluQuotient_a₃ veluQuotient_a₄ veluQuotient_a₆ oddOrderSummingSet mem_oddOrderSummingSet"
namespace OSSPort
p2m_open "WeierstrassCurve"

section Abscissae

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

lemma veluW_eq_of_equation {x y : F} (h : W.toAffine.Equation x y) :
    W.veluW x y
      = (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)
        + x * (6 * x ^ 2 + W.b₂ * x + W.b₄) := by
  rw [veluW, veluT_eq, veluU_eq_Ψ₂Sq_eval W h]
  congr 1
  simp only [Ψ₂Sq, b₂, b₄, b₆, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]

variable [DecidableEq F] (S : Finset (F × F))

lemma veluTSum_eq_sum_abscissae
    (hinj : ∀ P ∈ S, ∀ Q ∈ S, P.1 = Q.1 → P = Q) :
    W.veluTSum S = ∑ x ∈ S.image Prod.fst, (6 * x ^ 2 + W.b₂ * x + W.b₄) := by
  rw [veluTSum, Finset.sum_image hinj]
  exact Finset.sum_congr rfl fun P _ => W.veluT_eq P.1 P.2

lemma veluWSum_eq_sum_abscissae
    (heq : ∀ P ∈ S, W.toAffine.Equation P.1 P.2)
    (hinj : ∀ P ∈ S, ∀ Q ∈ S, P.1 = Q.1 → P = Q) :
    W.veluWSum S = ∑ x ∈ S.image Prod.fst,
      ((4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)
        + x * (6 * x ^ 2 + W.b₂ * x + W.b₄)) := by
  rw [veluWSum, Finset.sum_image hinj]
  exact Finset.sum_congr rfl fun P hP => veluW_eq_of_equation W (heq P hP)

end Abscissae

lemma image_eq_self_of_mapsTo {α : Type*} [DecidableEq α] {A : Finset α} {σ : α → α}
    (hσ : Function.Injective σ) (h : ∀ x ∈ A, σ x ∈ A) : A.image σ = A :=
  Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr h)
    (le_of_eq (Finset.card_image_of_injective A hσ).symm)

section Permutation

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

lemma map_fix_b₂ {σ : F →+* F} (hW : W.map σ = W) : σ W.b₂ = W.b₂ := by
  rw [← map_b₂, hW]

lemma map_fix_b₄ {σ : F →+* F} (hW : W.map σ = W) : σ W.b₄ = W.b₄ := by
  rw [← map_b₄, hW]

lemma map_fix_b₆ {σ : F →+* F} (hW : W.map σ = W) : σ W.b₆ = W.b₆ := by
  rw [← map_b₆, hW]

variable [DecidableEq F] (S : Finset (F × F))

theorem veluTSum_map_eq {σ : F →+* F} (hW : W.map σ = W)
    (hinj : ∀ P ∈ S, ∀ Q ∈ S, P.1 = Q.1 → P = Q)
    (hstab : ∀ x ∈ S.image Prod.fst, σ x ∈ S.image Prod.fst) :
    σ (W.veluTSum S) = W.veluTSum S := by
  have himg : (S.image Prod.fst).image σ = S.image Prod.fst :=
    image_eq_self_of_mapsTo σ.injective hstab
  rw [veluTSum_eq_sum_abscissae W S hinj, map_sum]
  calc ∑ x ∈ S.image Prod.fst, σ (6 * x ^ 2 + W.b₂ * x + W.b₄)
      = ∑ x ∈ S.image Prod.fst, (6 * (σ x) ^ 2 + W.b₂ * (σ x) + W.b₄) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [map_add, map_mul, map_pow, map_ofNat,
          map_fix_b₂ W hW, map_fix_b₄ W hW]
    _ = ∑ x ∈ (S.image Prod.fst).image σ, (6 * x ^ 2 + W.b₂ * x + W.b₄) :=
        (Finset.sum_image (f := fun t => 6 * t ^ 2 + W.b₂ * t + W.b₄)
          σ.injective.injOn).symm
    _ = ∑ x ∈ S.image Prod.fst, (6 * x ^ 2 + W.b₂ * x + W.b₄) := by rw [himg]

theorem veluWSum_map_eq {σ : F →+* F} (hW : W.map σ = W)
    (heq : ∀ P ∈ S, W.toAffine.Equation P.1 P.2)
    (hinj : ∀ P ∈ S, ∀ Q ∈ S, P.1 = Q.1 → P = Q)
    (hstab : ∀ x ∈ S.image Prod.fst, σ x ∈ S.image Prod.fst) :
    σ (W.veluWSum S) = W.veluWSum S := by
  have himg : (S.image Prod.fst).image σ = S.image Prod.fst :=
    image_eq_self_of_mapsTo σ.injective hstab
  rw [veluWSum_eq_sum_abscissae W S heq hinj, map_sum]
  calc ∑ x ∈ S.image Prod.fst,
        σ ((4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)
          + x * (6 * x ^ 2 + W.b₂ * x + W.b₄))
      = ∑ x ∈ S.image Prod.fst,
          ((4 * (σ x) ^ 3 + W.b₂ * (σ x) ^ 2 + 2 * W.b₄ * (σ x) + W.b₆)
            + (σ x) * (6 * (σ x) ^ 2 + W.b₂ * (σ x) + W.b₄)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [map_add, map_mul, map_pow, map_ofNat,
          map_fix_b₂ W hW, map_fix_b₄ W hW, map_fix_b₆ W hW]
    _ = ∑ x ∈ (S.image Prod.fst).image σ,
          ((4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)
            + x * (6 * x ^ 2 + W.b₂ * x + W.b₄)) :=
        (Finset.sum_image (f := fun t => (4 * t ^ 3 + W.b₂ * t ^ 2 + 2 * W.b₄ * t + W.b₆)
          + t * (6 * t ^ 2 + W.b₂ * t + W.b₄)) σ.injective.injOn).symm
    _ = ∑ x ∈ S.image Prod.fst,
          ((4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)
            + x * (6 * x ^ 2 + W.b₂ * x + W.b₄)) := by rw [himg]

theorem veluQuotient_map_eq {σ : F →+* F} (hW : W.map σ = W)
    (heq : ∀ P ∈ S, W.toAffine.Equation P.1 P.2)
    (hinj : ∀ P ∈ S, ∀ Q ∈ S, P.1 = Q.1 → P = Q)
    (hstab : ∀ x ∈ S.image Prod.fst, σ x ∈ S.image Prod.fst) :
    (W.veluQuotient S).map σ = W.veluQuotient S := by
  have ht := veluTSum_map_eq W S hW hinj hstab
  have hw := veluWSum_map_eq W S hW heq hinj hstab
  have ha₁ : σ W.a₁ = W.a₁ := by rw [← map_a₁, hW]
  have ha₂ : σ W.a₂ = W.a₂ := by rw [← map_a₂, hW]
  have ha₃ : σ W.a₃ = W.a₃ := by rw [← map_a₃, hW]
  have ha₄ : σ W.a₄ = W.a₄ := by rw [← map_a₄, hW]
  have ha₆ : σ W.a₆ = W.a₆ := by rw [← map_a₆, hW]
  ext
  · simpa only [map_a₁, veluQuotient_a₁] using ha₁
  · simpa only [map_a₂, veluQuotient_a₂] using ha₂
  · simpa only [map_a₃, veluQuotient_a₃] using ha₃
  · simp only [map_a₄, veluQuotient_a₄, map_sub, map_mul, map_ofNat, ha₄, ht]
  · simp only [map_a₆, veluQuotient_a₆, map_sub, map_mul, map_ofNat, ha₆, ht, hw,
      map_fix_b₂ W hW]

end Permutation

section Descent

local instance isAlgebraicQbar_oss : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar_oss : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩
local instance normalQbar_oss : Normal ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
local instance isGaloisQbar_oss : IsGalois ℚ (AlgebraicClosure ℚ) := ⟨⟩

lemma exists_algebraMap_eq_of_forall_fixed {c : AlgebraicClosure ℚ}
    (h : ∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), σ c = c) :
    ∃ c₀ : ℚ, algebraMap ℚ (AlgebraicClosure ℚ) c₀ = c :=
  (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := ℚ) c).mpr h

theorem exists_map_eq_of_forall_algEquiv_map_eq (V : WeierstrassCurve (AlgebraicClosure ℚ))
    (h : ∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ),
      V.map (σ : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ)) = V) :
    ∃ V₀ : WeierstrassCurve ℚ, V₀.map (algebraMap ℚ (AlgebraicClosure ℚ)) = V := by
  obtain ⟨c₁, hc₁⟩ := exists_algebraMap_eq_of_forall_fixed
    (c := V.a₁) (fun σ => congrArg WeierstrassCurve.a₁ (h σ))
  obtain ⟨c₂, hc₂⟩ := exists_algebraMap_eq_of_forall_fixed
    (c := V.a₂) (fun σ => congrArg WeierstrassCurve.a₂ (h σ))
  obtain ⟨c₃, hc₃⟩ := exists_algebraMap_eq_of_forall_fixed
    (c := V.a₃) (fun σ => congrArg WeierstrassCurve.a₃ (h σ))
  obtain ⟨c₄, hc₄⟩ := exists_algebraMap_eq_of_forall_fixed
    (c := V.a₄) (fun σ => congrArg WeierstrassCurve.a₄ (h σ))
  obtain ⟨c₆, hc₆⟩ := exists_algebraMap_eq_of_forall_fixed
    (c := V.a₆) (fun σ => congrArg WeierstrassCurve.a₆ (h σ))
  exact ⟨⟨c₁, c₂, c₃, c₄, c₆⟩, WeierstrassCurve.ext hc₁ hc₂ hc₃ hc₄ hc₆⟩

lemma baseChange_map_algEquiv (W : WeierstrassCurve ℚ)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) :
    (W⁄(AlgebraicClosure ℚ)).map (σ : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))
      = W⁄(AlgebraicClosure ℚ) := by
  show (W.map _).map _ = W.map _
  rw [map_map]
  congr 1
  ext q
  simp

theorem exists_veluQuotient_descent (W : WeierstrassCurve ℚ)
    (S : Finset ((AlgebraicClosure ℚ) × (AlgebraicClosure ℚ)))
    (heq : ∀ P ∈ S, (W⁄(AlgebraicClosure ℚ)).toAffine.Equation P.1 P.2)
    (hinj : ∀ P ∈ S, ∀ Q ∈ S, P.1 = Q.1 → P = Q)
    (hstab : ∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ),
      ∀ x ∈ S.image Prod.fst, σ x ∈ S.image Prod.fst) :
    ∃ V₀ : WeierstrassCurve ℚ,
      V₀.map (algebraMap ℚ (AlgebraicClosure ℚ))
        = (W⁄(AlgebraicClosure ℚ)).veluQuotient S := by
  refine exists_map_eq_of_forall_algEquiv_map_eq _ fun σ => ?_
  exact veluQuotient_map_eq (W⁄(AlgebraicClosure ℚ)) S
    (baseChange_map_algEquiv W σ) heq hinj (hstab σ)

end Descent

end WeierstrassCurve.OSSPort

open WeierstrassCurve.OSSPort in

theorem solution
    {W : WeierstrassCurve ℚ} {Q : (W⁄(AlgebraicClosure ℚ)).toAffine.Point} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hord : addOrderOf Q = p)
    (hstab : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q ∈ AddSubgroup.zmultiples Q) :
    ∃ V₀ : WeierstrassCurve ℚ,
      V₀.map (algebraMap ℚ (AlgebraicClosure ℚ))
        = (W⁄(AlgebraicClosure ℚ)).veluQuotient
            ((W⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q ((p - 1) / 2)) := by
  have hset := OSSPort.isOddVeluSet_oddOrderSummingSet (W := (W⁄(AlgebraicClosure ℚ))) hp hp2 hord
    (n := (p - 1) / 2) le_rfl
  exact OSSPort.exists_veluQuotient_descent W _ hset.equation
    (fun P hP P' hP' hx => hset.x_injOn P hP P' hP' hx)
    (fun σ t ht => OSSPort.algEquiv_mem_image_fst_oddOrderSummingSet hp hp2 hord hstab σ ht)

end S_WeierstrassCurve_exists_veluQuotient_descent_of_smul_mem_zmultiples
end P2MW
export P2MW.S_WeierstrassCurve_exists_veluQuotient_descent_of_smul_mem_zmultiples (solution)
