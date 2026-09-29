-- Prove2me | solution 1 for WeierstrassCurve.exists_iterate_frobenius_eq_smul_of_forall_nsmul_char_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/2863fbe7-54b4-5cec-84fb-28e7a8a75c15

import Mathlib
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_iterate_frobenius_eq_smul_of_forall_nsmul_char_eq_zero
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

p2m_open "WeierstrassCurve~evalEval_ψ_sq P2MW.S_WeierstrassCurve_exists_iterate_frobenius_eq_smul_of_forall_nsmul_char_eq_zero.WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point Polynomial"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.CoordinateRing.mk_Ψ_sq a₃ a₁ natDegree_Φ map Affine.CoordinateRing mk a₄ a₂ a₆ ΨSq toAffine Affine.Point Affine.CoordinateRing.mk Affine.CoordinateRing.mk_ψ Affine.Point.map Affine.equation_iff j Affine.Point.smul_some_eq_zero_iff"
namespace SupersingularFrobeniusInteger
p2m_open "WeierstrassCurve~evalEval_ψ_sq"

section InjectivePolynomial

variable {k : Type*} [Field k]

theorem coeff_X_sub_C_pow_pow_mul (p : ℕ) [Fact p.Prime] [CharP k p] (t m : ℕ) (hm : 1 ≤ m)
    (x₀ : k) :
    ((X - C x₀ : k[X]) ^ (p ^ t * m)).coeff (p ^ t * (m - 1)) = -(x₀ ^ p ^ t) * (m : k) := by
  have hp : 0 < p ^ t := pow_pos (Nat.Prime.pos Fact.out) t
  rw [pow_mul, sub_pow_char_pow, ← C_pow]
  have hexp : (X ^ p ^ t - C (x₀ ^ p ^ t) : k[X]) ^ m =
      expand k (p ^ t) ((X - C (x₀ ^ p ^ t)) ^ m) := by
    rw [map_pow (expand k (p ^ t)), map_sub (expand k (p ^ t)), expand_X, expand_C]
  rw [hexp, mul_comm (p ^ t) (m - 1), coeff_expand_mul hp, sub_eq_add_neg, ← C_neg,
    coeff_X_add_C_pow]
  have h1 : m - (m - 1) = 1 := by omega
  have h2 : m.choose (m - 1) = m := by
    rw [Nat.choose_symm hm, Nat.choose_one_right]
  rw [h1, pow_one, h2]

theorem exists_eq_C_mul_X_pow_add_C_of_injective [IsAlgClosed k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (a : k[X]) (ha : Function.Injective fun x => a.eval x) :
    ∃ (t : ℕ) (c₀ c₁ : k), c₀ ≠ 0 ∧ a = C c₀ * X ^ (p ^ t) + C c₁ := by
  set n := a.natDegree with hn
  have hn0 : n ≠ 0 := by
    intro h0
    have h01 : a.eval 0 = a.eval 1 := by
      rw [eq_C_of_natDegree_eq_zero h0]; simp
    exact zero_ne_one (ha h01)
  have ha0 : a ≠ 0 := fun h => hn0 (by rw [hn, h, natDegree_zero])
  have hlc : a.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr ha0

  have key : ∀ x₀ : k, a - C (a.eval x₀) = C a.leadingCoeff * (X - C x₀) ^ n := by
    intro x₀
    set b := a - C (a.eval x₀) with hb
    have hbn : b.natDegree = n := natDegree_sub_C
    have hb0 : b ≠ 0 := fun h => by rw [h, natDegree_zero] at hbn; exact hn0 hbn.symm
    have hblc : b.leadingCoeff = a.leadingCoeff := by
      apply leadingCoeff_sub_of_degree_lt
      calc (C (a.eval x₀)).degree ≤ 0 := degree_C_le
        _ < a.degree := by
          rw [degree_eq_natDegree ha0]
          exact_mod_cast Nat.pos_of_ne_zero hn0
    have hsplit : b.Splits := IsAlgClosed.splits b
    have hroots : ∀ r ∈ b.roots, r = x₀ := by
      intro r hr
      have hr' : b.IsRoot r := (mem_roots hb0).mp hr
      have h2 : a.eval r = a.eval x₀ := by
        have := hr'.eq_zero
        rwa [hb, eval_sub, eval_C, sub_eq_zero] at this
      exact ha h2
    have hcard : b.roots.card = n := by rw [← hbn]; exact hsplit.natDegree_eq_card_roots.symm
    have hrep : b.roots = Multiset.replicate n x₀ := Multiset.eq_replicate.mpr ⟨hcard, hroots⟩
    rw [hsplit.eq_prod_roots, hblc, hrep, Multiset.map_replicate, Multiset.prod_replicate]
  obtain ⟨t, m, hpm, hnm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hn0 p (Nat.Prime.one_lt Fact.out).ne'
  have hm0 : m ≠ 0 := by rintro rfl; exact hpm (dvd_zero p)

  have hm1 : m = 1 := by
    by_contra hm1
    have hm2 : 2 ≤ m := by omega
    have hidx : p ^ t * (m - 1) ≠ 0 :=
      Nat.mul_ne_zero (pow_ne_zero _ (Nat.Prime.pos Fact.out).ne') (by omega)
    have hcoeff : ∀ x₀ : k,
        a.coeff (p ^ t * (m - 1)) = a.leadingCoeff * (-(x₀ ^ p ^ t) * (m : k)) := by
      intro x₀
      have h1 : (a - C (a.eval x₀)).coeff (p ^ t * (m - 1)) = a.coeff (p ^ t * (m - 1)) := by
        rw [coeff_sub, coeff_C, if_neg hidx, sub_zero]
      rw [← h1, key x₀, coeff_C_mul, hnm, coeff_X_sub_C_pow_pow_mul p t m (by omega) x₀]
    have h0 := hcoeff 0
    have h1 := hcoeff 1
    rw [zero_pow (pow_ne_zero _ (Nat.Prime.pos Fact.out).ne'), _root_.neg_zero, zero_mul,
      mul_zero] at h0
    rw [h0, one_pow] at h1
    have hmk : (m : k) ≠ 0 := by
      intro h
      exact hpm ((CharP.cast_eq_zero_iff k p m).mp h)
    have : a.leadingCoeff * (-1 * (m : k)) ≠ 0 :=
      mul_ne_zero hlc (mul_ne_zero (by norm_num) hmk)
    exact this h1.symm
  subst hm1
  rw [mul_one] at hnm
  refine ⟨t, a.leadingCoeff, a.eval 0, hlc, ?_⟩
  have h := key 0
  rw [_root_.map_zero, sub_zero, hnm] at h
  rw [← h, sub_add_cancel]

end InjectivePolynomial

section GroupLemma

variable {G : Type*} [AddCommGroup G]

theorem forall_eq_or_forall_eq_neg_of_forall (f : G →+ G) (hf : ∀ x, f x = x ∨ f x = -x) :
    (∀ x, f x = x) ∨ (∀ x, f x = -x) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hcon
  have ha' : f a = -a := (hf a).resolve_left ha
  have hb' : f b = b := (hf b).resolve_right hb
  rcases hf (a + b) with h | h
  · rw [map_add, ha', hb'] at h
    apply ha
    rw [ha']

    exact add_right_cancel h
  · rw [map_add, ha', hb', neg_add] at h
    apply hb
    rw [hb']
    exact add_left_cancel h

end GroupLemma

section Curve

variable {R : Type*} [CommRing R]

theorem evalEval_ψ_sq (W : WeierstrassCurve R) (n : ℤ) {x y : R} (h : W.toAffine.Equation x y) :
    ((W.ψ n).evalEval x y) ^ 2 = (W.ΨSq n).eval x := by
  have h1 : Affine.CoordinateRing.mk W (W.ψ n ^ 2) = Affine.CoordinateRing.mk W (C (W.ΨSq n)) := by
    rw [map_pow, Affine.CoordinateRing.mk_ψ, Affine.CoordinateRing.mk_Ψ_sq]
  have h2 := congrArg (AdjoinRoot.evalEval h) h1
  rw [AdjoinRoot.evalEval_mk, AdjoinRoot.evalEval_mk, evalEval_pow, evalEval_C] at h2
  exact h2

variable {k : Type*} [Field k]

theorem some_eq_or_eq_neg_of_x_eq {E : WeierstrassCurve k} {x₁ x₂ y₁ y₂ : k}
    (h₁ : E.toAffine.Nonsingular x₁ y₁) (h₂ : E.toAffine.Nonsingular x₂ y₂) (hx : x₁ = x₂) :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ ∨ Point.some x₁ y₁ h₁ = -Point.some x₂ y₂ h₂ := by
  subst hx
  rcases Y_eq_of_X_eq h₁.1 h₂.1 rfl with hy | hy
  · left; subst hy; rfl
  · right; rw [neg_some]; subst hy; rfl

theorem exists_some_eq_of_x_eq {E : WeierstrassCurve k} {x x' y : k}
    (h : E.toAffine.Nonsingular x y) (e : x = x') :
    ∃ h' : E.toAffine.Nonsingular x' y, Point.some x y h = Point.some x' y h' := by
  subst e; exact ⟨h, rfl⟩

theorem exists_nonsingular_of_isAlgClosed [IsAlgClosed k] (E : WeierstrassCurve k) [E.IsElliptic]
    (x : k) : ∃ y, E.toAffine.Nonsingular x y := by

  set f : k[X] := X ^ 2 + C (E.a₁ * x + E.a₃) * X - C (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆)
    with hf
  have hdeg : f.degree = 2 := by
    rw [hf, sub_eq_add_neg, ← C_neg]
    compute_degree!
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root f (by rw [hdeg]; norm_num)
  refine ⟨y, (equation_iff_nonsingular (W := E.toAffine)).mp ?_⟩
  rw [WeierstrassCurve.Affine.equation_iff]
  have : f.eval y = 0 := hy
  rw [hf] at this
  simp only [eval_sub, eval_add, eval_pow, eval_X, eval_mul, eval_C] at this
  linear_combination this

end Curve

section MulAbscissa

variable {k : Type*} [Field k] [DecidableEq k] [IsAlgClosed k] (E : WeierstrassCurve k)
  [E.IsElliptic]

theorem exists_polynomial_abscissa_zsmul (q : ℕ) (hq : ∀ P : E.toAffine.Point, (q : ℤ) • P = 0 → P = 0) :
    ∃ a : k[X], a.natDegree = q ^ 2 ∧ (Function.Injective fun x => a.eval x) ∧
      ∀ (x y : k) (h : E.toAffine.Nonsingular x y), ∃ (y' : k)
        (h' : E.toAffine.Nonsingular (a.eval x) y'),
          (q : ℤ) • Point.some x y h = Point.some (a.eval x) y' h' := by

  have hinj : Function.Injective fun P : E.toAffine.Point => (q : ℤ) • P := by
    intro P Q hPQ
    have : (q : ℤ) • (P - Q) = 0 := by
      have hPQ' : (q : ℤ) • P = (q : ℤ) • Q := hPQ
      rw [zsmul_sub, hPQ', sub_self]
    exact sub_eq_zero.mp (hq _ this)

  have hψ : ∀ (x y : k) (h : E.toAffine.Nonsingular x y), (E.ψ q).evalEval x y ≠ 0 := by
    intro x y h h0
    exact some_ne_zero h (hq _ ((Point.smul_some_eq_zero_iff E h q).mpr h0))

  have hΨ : ∀ x : k, (E.ΨSq q).eval x ≠ 0 := by
    intro x
    obtain ⟨y, hxy⟩ := exists_nonsingular_of_isAlgClosed E x
    rw [← evalEval_ψ_sq E q hxy.1]
    exact pow_ne_zero 2 (hψ x y hxy)
  set c : k := (E.ΨSq q).coeff 0 with hc
  have hΨc : E.ΨSq (q : ℤ) = C c := by
    apply eq_C_of_degree_le_zero
    by_contra hdeg
    push Not at hdeg
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_root (E.ΨSq q) (ne_of_gt hdeg)
    exact hΨ r hr
  have hc0 : c ≠ 0 := by
    have := hΨ 0
    rwa [hΨc, eval_C] at this

  set a : k[X] := C c⁻¹ * E.Φ q with ha
  have hdeg : a.natDegree = q ^ 2 := by
    rw [ha, natDegree_C_mul (inv_ne_zero hc0), WeierstrassCurve.natDegree_Φ]
    simp
  have hmul : ∀ (x y : k) (h : E.toAffine.Nonsingular x y), ∃ (y' : k)
      (h' : E.toAffine.Nonsingular (a.eval x) y'),
        (q : ℤ) • Point.some x y h = Point.some (a.eval x) y' h' := by
    intro x y h
    obtain ⟨y', h', e⟩ := Point.zsmul_some_eq_some_div E h (n := q) (hψ x y h)
    have hx : (E.Φ q).eval x / (E.ΨSq q).eval x = a.eval x := by
      rw [hΨc, eval_C, ha, eval_mul, eval_C, div_eq_inv_mul]
    obtain ⟨h'', e'⟩ := exists_some_eq_of_x_eq h' hx
    exact ⟨y', h'', e.trans e'⟩
  refine ⟨a, hdeg, ?_, hmul⟩

  intro x₁ x₂ hx
  obtain ⟨y₁, h₁⟩ := exists_nonsingular_of_isAlgClosed E x₁
  obtain ⟨y₂, h₂⟩ := exists_nonsingular_of_isAlgClosed E x₂
  obtain ⟨y₁', h₁', e₁⟩ := hmul x₁ y₁ h₁
  obtain ⟨y₂', h₂', e₂⟩ := hmul x₂ y₂ h₂
  rcases some_eq_or_eq_neg_of_x_eq h₁' h₂' hx with hh | hh
  · have := hinj (e₁.trans (hh.trans e₂.symm))
    exact (Point.some.inj this).1
  · rw [← e₂, ← smul_neg, neg_some] at hh
    have := hinj (e₁.trans hh)
    exact (Point.some.inj this).1

end MulAbscissa

end WeierstrassCurve.SupersingularFrobeniusInteger

open WeierstrassCurve.SupersingularFrobeniusInteger in
theorem solution {F : Type*} [Field F] [Fintype F] (k : Type*) [Field k] [DecidableEq k] [Algebra F k] [IsAlgClosed k] [Algebra.IsAlgebraic F k] (p : ℕ) [Fact p.Prime] [CharP F p] (W : WeierstrassCurve F) [W.IsElliptic] (σ : k →ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) (h : ∀ P : (W⁄k).Point, p • P = 0 → P = 0) : ∃ n : ℕ, 0 < n ∧ ∃ a : ℤ, ∀ P : (W⁄k).Point, (WeierstrassCurve.Affine.Point.map (W' := W) σ)^[n] P = a • P := by

  set q : ℕ := Fintype.card F with hqdef
  obtain ⟨d, hpp, hqd⟩ := FiniteField.card F p
  have hp : p.Prime := Fact.out
  have hq1 : 1 < q := Fintype.one_lt_card
  have hq0 : 0 < q := by omega
  haveI : CharP k p := charP_of_injective_algebraMap (algebraMap F k).injective p
  haveI hE : (W⁄k).IsElliptic := inferInstanceAs ((W.map (algebraMap F k)).IsElliptic)
  set E : WeierstrassCurve k := W⁄k with hEdef

  have hpow : ∀ (m : ℕ) (P : (W⁄k).Point), (p ^ m) • P = 0 → P = 0 := by
    intro m
    induction m with
    | zero => intro P hP; simpa using hP
    | succ m ih =>
      intro P hP
      rw [pow_succ, mul_nsmul'] at hP
      exact h P (ih _ hP)
  have hqtors : ∀ P : E.toAffine.Point, (q : ℤ) • P = 0 → P = 0 := by
    intro P hP
    rw [natCast_zsmul, hqdef, hqd] at hP
    exact hpow _ P hP

  obtain ⟨a, hadeg, hainj, hamul⟩ := exists_polynomial_abscissa_zsmul E q hqtors

  obtain ⟨t, c₀, c₁, hc₀, haeq⟩ := exists_eq_C_mul_X_pow_add_C_of_injective p a hainj
  have hpt : p ^ t = q ^ 2 := by
    have : (C c₀ * X ^ (p ^ t) + C c₁ : k[X]).natDegree = p ^ t := by
      rw [natDegree_add_C, natDegree_C_mul_X_pow _ _ hc₀]
    rw [← this, ← haeq, hadeg]
  have haeval : ∀ x : k, a.eval x = c₀ * x ^ (q ^ 2) + c₁ := by
    intro x
    rw [haeq, ← hpt]
    simp [eval_add, eval_mul, eval_C, eval_pow, eval_X]

  have hσinj : Function.Injective σ := σ.toRingHom.injective
  have hσsurj : Function.Surjective σ := by
    intro y
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (X ^ q - C y : k[X])
      (by rw [degree_X_pow_sub_C hq0]; exact_mod_cast hq0.ne')
    refine ⟨x, ?_⟩
    have : x ^ q - y = 0 := by simpa [eval_sub, eval_pow, eval_X, eval_C] using hx
    rw [hσ, sub_eq_zero.mp this]
  set σe : k ≃ₐ[F] k := AlgEquiv.ofBijective σ ⟨hσinj, hσsurj⟩ with hσe
  have hσe_apply : ∀ x, σe x = σ x := fun x => rfl
  set π : (W⁄k).Point →+ (W⁄k).Point := WeierstrassCurve.Affine.Point.map (W' := W) σ with hπdef
  set πi : (W⁄k).Point →+ (W⁄k).Point :=
    WeierstrassCurve.Affine.Point.map (W' := W) (σe.symm : k →ₐ[F] k) with hπidef
  have hππi : ∀ P, π (πi P) = P := by
    rintro (_ | ⟨x, y, hxy⟩)
    · rfl
    · rw [hπidef, map_some, hπdef, map_some]
      simp only [Point.some.injEq]
      exact ⟨by rw [AlgEquiv.coe_algHom, ← hσe_apply, AlgEquiv.apply_symm_apply],
        by rw [AlgEquiv.coe_algHom, ← hσe_apply, AlgEquiv.apply_symm_apply]⟩
  have hπiπ : ∀ P, πi (π P) = P := by
    rintro (_ | ⟨x, y, hxy⟩)
    · rfl
    · rw [hπdef, map_some, hπidef, map_some]
      simp only [Point.some.injEq]
      exact ⟨by rw [AlgEquiv.coe_algHom, ← hσe_apply, AlgEquiv.symm_apply_apply],
        by rw [AlgEquiv.coe_algHom, ← hσe_apply, AlgEquiv.symm_apply_apply]⟩

  have hσa : ∀ x : k, σ (a.eval x) = a.eval (σ x) := by
    intro x
    obtain ⟨y, hxy⟩ := exists_nonsingular_of_isAlgClosed E x
    obtain ⟨y', h', e⟩ := hamul x y hxy
    have hxy' : E.toAffine.Nonsingular (σ x) (σ y) :=
      (W.toAffine.baseChange_nonsingular hσinj ..).mpr hxy
    obtain ⟨y'', h'', e'⟩ := hamul (σ x) (σ y) hxy'
    have h1 : π ((q : ℤ) • Point.some x y hxy) = (q : ℤ) • π (Point.some x y hxy) := map_zsmul π _ _
    rw [e, hπdef, map_some, map_some] at h1
    rw [e'] at h1
    exact (Point.some.inj h1).1
  have hσc₁ : σ c₁ = c₁ := by
    have := hσa 0
    rwa [haeval, haeval, _root_.map_zero, zero_pow (pow_ne_zero _ hq0.ne'), mul_zero,
      zero_add] at this
  have hσc₀ : σ c₀ = c₀ := by
    have := hσa 1
    rwa [haeval, haeval, map_one, one_pow, mul_one, map_add, hσc₁, add_left_inj] at this
  have hc₀q : c₀ ^ (q - 1) = 1 := by
    have h1 : c₀ ^ q = c₀ := by rw [← hσ, hσc₀]
    have h2 : c₀ ^ (q - 1) * c₀ = 1 * c₀ := by
      rw [← pow_succ, Nat.sub_add_cancel hq1.le, h1, one_mul]
    exact mul_right_cancel₀ hc₀ h2

  set ε : (W⁄k).Point →+ (W⁄k).Point :=
    AddMonoidHom.mk' (fun P => (q : ℤ) • πi (πi P)) (fun P Q => by
      simp only [map_add, smul_add]) with hεdef
  have hε_apply : ∀ P, ε P = (q : ℤ) • πi (πi P) := fun P => rfl

  have hε_some : ∀ (x y : k) (hxy : E.toAffine.Nonsingular x y), ∃ (y' : k)
      (h' : E.toAffine.Nonsingular (c₀ * x + c₁) y'),
        ε (Point.some x y hxy) = Point.some (c₀ * x + c₁) y' h' := by
    intro x y hxy
    set τ : k →ₐ[F] k := (σe.symm : k →ₐ[F] k) with hτ
    have hτσ : ∀ z, σ (τ z) = z := fun z => by
      rw [hτ, AlgEquiv.coe_algHom, ← hσe_apply, AlgEquiv.apply_symm_apply]
    have hx0 : (τ (τ x)) ^ (q ^ 2) = x := by
      rw [pow_two, pow_mul, ← hσ, ← hσ, hτσ, hτσ]
    have hns : E.toAffine.Nonsingular (τ (τ x)) (τ (τ y)) :=
      (W.toAffine.baseChange_nonsingular τ.toRingHom.injective ..).mpr
        ((W.toAffine.baseChange_nonsingular τ.toRingHom.injective ..).mpr hxy)
    have hP0 : πi (πi (Point.some x y hxy)) = Point.some (τ (τ x)) (τ (τ y)) hns := by
      rw [hπidef, map_some, map_some]
    obtain ⟨y', h', e⟩ := hamul (τ (τ x)) (τ (τ y)) hns
    rw [hε_apply, hP0, e]
    have hx1 : a.eval (τ (τ x)) = c₀ * x + c₁ := by rw [haeval, hx0]
    obtain ⟨h'', e'⟩ := exists_some_eq_of_x_eq h' hx1
    exact ⟨y', h'', e'⟩

  let εM : AddMonoid.End (W⁄k).Point := ε
  let πM : AddMonoid.End (W⁄k).Point := π
  have hεM_apply : ∀ P, εM P = (q : ℤ) • πi (πi P) := fun P => rfl
  have hπM_apply : ∀ P, πM P = π P := fun P => rfl
  have hMmul : ∀ (f g : AddMonoid.End (W⁄k).Point) (P : (W⁄k).Point), (f * g) P = f (g P) :=
    fun f g P => rfl
  have hMpow : ∀ (f : AddMonoid.End (W⁄k).Point) (j : ℕ) (P : (W⁄k).Point),
      (f ^ j) P = f^[j] P := by
    intro f j P
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ', hMmul, ih, Function.iterate_succ_apply']

  have hε_pow : ∀ (j : ℕ) (x y : k) (hxy : E.toAffine.Nonsingular x y), ∃ (y' : k)
      (h' : E.toAffine.Nonsingular (c₀ ^ j * x + c₁ * ∑ i ∈ Finset.range j, c₀ ^ i) y'),
        (εM ^ j) (Point.some x y hxy) =
          Point.some (c₀ ^ j * x + c₁ * ∑ i ∈ Finset.range j, c₀ ^ i) y' h' := by
    intro j
    induction j with
    | zero =>
      intro x y hxy
      have hx : x = c₀ ^ 0 * x + c₁ * ∑ i ∈ Finset.range 0, c₀ ^ i := by simp
      obtain ⟨h', e'⟩ := exists_some_eq_of_x_eq hxy hx
      exact ⟨y, h', e'⟩
    | succ j ih =>
      intro x y hxy
      obtain ⟨y', h', e'⟩ := ih x y hxy
      obtain ⟨y'', h'', e''⟩ := hε_some _ y' h'
      have hS : ∑ i ∈ Finset.range (j + 1), c₀ ^ i =
          c₀ * (∑ i ∈ Finset.range j, c₀ ^ i) + 1 := by
        rw [Finset.sum_range_succ', pow_zero, Finset.mul_sum]
        simp only [pow_succ']
      have hx : c₀ * (c₀ ^ j * x + c₁ * ∑ i ∈ Finset.range j, c₀ ^ i) + c₁ =
          c₀ ^ (j + 1) * x + c₁ * ∑ i ∈ Finset.range (j + 1), c₀ ^ i := by
        rw [hS, pow_succ']
        ring
      obtain ⟨h₃, e₃⟩ := exists_some_eq_of_x_eq h'' hx
      refine ⟨y'', h₃, ?_⟩
      rw [pow_succ', hMmul, e']
      exact e''.trans e₃

  set L : ℕ := p * (q - 1) with hL
  have hL0 : 0 < L := Nat.mul_pos hp.pos (by omega)
  have hc₀L : c₀ ^ L = 1 := by rw [hL, mul_comm, pow_mul, hc₀q, one_pow]
  have hsumL : ∑ i ∈ Finset.range L, c₀ ^ i = 0 := by
    by_cases h1 : c₀ = 1
    · rw [h1]
      simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      rw [CharP.cast_eq_zero_iff k p]
      exact Dvd.intro _ rfl
    · rw [geom_sum_eq h1, hc₀L, sub_self, zero_div]
  have hεL : ∀ P : (W⁄k).Point, (εM ^ L) P = P ∨ (εM ^ L) P = -P := by
    rintro (_ | ⟨x, y, hxy⟩)
    · left; exact map_zero _
    · obtain ⟨y', h', e'⟩ := hε_pow L x y hxy
      have hx : c₀ ^ L * x + c₁ * ∑ i ∈ Finset.range L, c₀ ^ i = x := by
        rw [hc₀L, hsumL, one_mul, mul_zero, add_zero]
      rcases some_eq_or_eq_neg_of_x_eq h' hxy hx with hh | hh
      · left; exact e'.trans hh
      · right; exact e'.trans hh
  have hε2L : εM ^ (2 * L) = 1 := by
    rw [two_mul, pow_add]
    apply AddMonoidHom.ext
    intro P
    show (εM ^ L) ((εM ^ L) P) = P
    rcases forall_eq_or_forall_eq_neg_of_forall (εM ^ L) hεL with hh | hh
    · have hh' : ∀ x, (εM ^ L) x = x := hh
      rw [hh', hh']
    · have hh' : ∀ x, (εM ^ L) x = -x := hh
      rw [hh', hh', neg_neg]

  have hcomm : Commute εM πM := by
    show εM * πM = πM * εM
    apply AddMonoidHom.ext
    intro P
    show εM (πM P) = πM (εM P)
    rw [hεM_apply, hπM_apply, hπM_apply, hεM_apply, hπiπ, map_zsmul, hππi]
  have hfactor : ((q : ℤ) : AddMonoid.End (W⁄k).Point) = εM * πM ^ 2 := by
    rw [pow_two]
    apply AddMonoidHom.ext
    intro P
    show ((q : ℤ) : AddMonoid.End (W⁄k).Point) P = εM (πM (πM P))
    rw [AddMonoid.End.intCast_apply, hεM_apply, hπM_apply, hπM_apply, hπiπ, hπiπ]
  have key : (((q : ℤ) ^ (2 * L) : ℤ) : AddMonoid.End (W⁄k).Point) = πM ^ (4 * L) := by
    rw [Int.cast_pow, hfactor, (hcomm.pow_right 2).mul_pow, hε2L, one_mul, ← pow_mul]
    congr 1
    ring
  refine ⟨4 * L, by omega, (q : ℤ) ^ (2 * L), fun P => ?_⟩
  have := congrArg (fun f : AddMonoid.End (W⁄k).Point => f P) key
  rw [AddMonoid.End.intCast_apply, hMpow] at this
  exact this.symm

end S_WeierstrassCurve_exists_iterate_frobenius_eq_smul_of_forall_nsmul_char_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_exists_iterate_frobenius_eq_smul_of_forall_nsmul_char_eq_zero (solution)
