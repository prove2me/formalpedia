-- Prove2me | solution 1 for Polynomial.integralClosure_adjoinRoot_X_sq_sub_X_pow_five_add_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:09:46.076847+00:00
-- url     : https://prove2.me/submissions/fad7c9c9-92bc-4a76-8541-68162cb41b63

import Mathlib

/-!
Integral closure of `k[x]` in `k(x)[Y]/(Y² - (x⁵ + 1))` (2, 5 ≠ 0 in `k`): it is `k[x] ⊕ k[x] y`, i.e.
`k[x][Y]/(Y² - x⁵ - 1)`, and its `k`-algebra maps to `L` are the pairs `(u, v)` with `v² = u⁵ + 1`.
Self-contained (Mathlib only); helpers in namespace `HypIntSol`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace HypIntSol

noncomputable section

variable (Fq : Type) [Field Fq]

/-- `x⁵ + 1 ∈ Fq[x]`. -/
abbrev f0 : Fq[X] := X ^ 5 + 1

/-- `x⁵ + 1 ∈ Fq(x)`. -/
abbrev f0K : RatFunc Fq := algebraMap Fq[X] (RatFunc Fq) (f0 Fq)

/-- The defining polynomial `Y² - (x⁵ + 1)` over `Fq(x)`. -/
abbrev hypPoly : (RatFunc Fq)[X] := X ^ 2 - C (f0K Fq)

theorem natDegree_f0 : (f0 Fq).natDegree = 5 := by
  have h : f0 Fq = X ^ 5 + C 1 := by rw [C_1]
  rw [h, natDegree_X_pow_add_C]

theorem f0_ne_zero : f0 Fq ≠ 0 := by
  intro h
  have := natDegree_f0 Fq
  rw [h, natDegree_zero] at this
  omega

theorem f0K_ne_zero : f0K Fq ≠ 0 := by
  rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective Fq[X] (RatFunc Fq))]
  exact f0_ne_zero Fq

/-- `x⁵ + 1` is not a square in `Fq(x)` (odd degree). -/
theorem not_sq (b : RatFunc Fq) : b ^ 2 ≠ f0K Fq := by
  intro h
  have hb : b ≠ 0 := by
    rintro rfl
    apply f0K_ne_zero Fq
    rw [← h]
    ring
  have h1 := congrArg RatFunc.intDegree h
  rw [pow_two, RatFunc.intDegree_mul hb hb, RatFunc.intDegree_polynomial, natDegree_f0] at h1
  omega

theorem irreducible_hypPoly : Irreducible (hypPoly Fq) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two (not_sq Fq)

instance fact_irreducible : Fact (Irreducible (hypPoly Fq)) := ⟨irreducible_hypPoly Fq⟩

theorem monic_hypPoly : (hypPoly Fq).Monic := monic_X_pow_sub_C _ two_ne_zero

theorem hypPoly_ne_zero : hypPoly Fq ≠ 0 := (monic_hypPoly Fq).ne_zero

theorem natDegree_hypPoly : (hypPoly Fq).natDegree = 2 := natDegree_X_pow_sub_C

/-- The function field of `y² = x⁵ + 1`. -/
abbrev HypF : Type := AdjoinRoot (hypPoly Fq)

theorem two_ne_zero_ratFunc (h2 : (2 : Fq) ≠ 0) : (2 : RatFunc Fq) ≠ 0 := by
  intro h
  apply h2
  apply (algebraMap Fq (RatFunc Fq)).injective
  rw [map_ofNat, h, map_zero]

/-- The generator `y`. -/
abbrev yF : HypF Fq := AdjoinRoot.root (hypPoly Fq)

theorem hy : yF Fq ^ 2 = algebraMap (RatFunc Fq) (HypF Fq) (f0K Fq) := by
  have h := AdjoinRoot.eval₂_root (hypPoly Fq)
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h
  rw [AdjoinRoot.algebraMap_eq]
  exact h

/-- Every element is `a + b y` with `a, b ∈ Fq(x)`. -/
theorem exists_coords (z : HypF Fq) :
    ∃ a b : RatFunc Fq, z = algebraMap (RatFunc Fq) (HypF Fq) a + algebraMap (RatFunc Fq) (HypF Fq) b * yF Fq := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective z
  have hz : AdjoinRoot.mk (hypPoly Fq) g = AdjoinRoot.mk (hypPoly Fq) (g %ₘ hypPoly Fq) := by
    have := AdjoinRoot.mk_leftInverse (monic_hypPoly Fq) (AdjoinRoot.mk _ g)
    rw [AdjoinRoot.modByMonicHom_mk] at this
    exact this.symm
  have hdeg : (g %ₘ hypPoly Fq).degree ≤ 1 := by
    have h1 := degree_modByMonic_lt g (monic_hypPoly Fq)
    have h2 : (hypPoly Fq).degree = ((2 : ℕ) : WithBot ℕ) := by
      rw [degree_eq_natDegree (hypPoly_ne_zero Fq), natDegree_hypPoly]
    rw [h2] at h1
    rw [degree_le_iff_coeff_zero]
    intro m hm
    have hm' : 1 < m := by exact_mod_cast hm
    exact (degree_lt_iff_coeff_zero _ 2).1 h1 m (by omega)
  set r := g %ₘ hypPoly Fq with hr
  refine ⟨r.coeff 0, r.coeff 1, ?_⟩
  rw [hz, congrArg (AdjoinRoot.mk (hypPoly Fq)) (eq_X_add_C_of_degree_le_one hdeg), map_add, map_mul,
    AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X, AdjoinRoot.algebraMap_eq]
  ring

/-- `a + b y = 0` forces `a = b = 0`. -/
theorem coords_eq_zero {a b : RatFunc Fq}
    (h : algebraMap (RatFunc Fq) (HypF Fq) a + algebraMap (RatFunc Fq) (HypF Fq) b * yF Fq = 0) :
    a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst hb
    rw [map_zero, zero_mul, add_zero, map_eq_zero_iff _ (algebraMap (RatFunc Fq) (HypF Fq)).injective] at h
    exact ⟨h, rfl⟩
  · exfalso
    have hy' : yF Fq = algebraMap (RatFunc Fq) (HypF Fq) (-a / b) := by
      rw [map_div₀, map_neg]
      have hb' : algebraMap (RatFunc Fq) (HypF Fq) b ≠ 0 :=
        (map_ne_zero_iff _ (algebraMap (RatFunc Fq) (HypF Fq)).injective).2 hb
      field_simp
      linear_combination h
    apply not_sq Fq (-a / b)
    apply (algebraMap (RatFunc Fq) (HypF Fq)).injective
    rw [map_pow, ← hy', hy]

theorem coords_unique {a b a' b' : RatFunc Fq}
    (h : algebraMap (RatFunc Fq) (HypF Fq) a + algebraMap (RatFunc Fq) (HypF Fq) b * yF Fq =
      algebraMap (RatFunc Fq) (HypF Fq) a' + algebraMap (RatFunc Fq) (HypF Fq) b' * yF Fq) :
    a = a' ∧ b = b' := by
  have h0 := coords_eq_zero Fq (a := a - a') (b := b - b') (by rw [map_sub, map_sub]; linear_combination h)
  exact ⟨sub_eq_zero.1 h0.1, sub_eq_zero.1 h0.2⟩

theorem aeval_neg_y : aeval (-yF Fq) (hypPoly Fq) = 0 := by
  rw [map_sub, map_pow, aeval_X, aeval_C, neg_sq, hy, sub_self]

/-- The `Fq(x)`-automorphism `y ↦ -y`. -/
def conjHom : HypF Fq →ₐ[RatFunc Fq] HypF Fq :=
  AdjoinRoot.liftAlgHom (hypPoly Fq) (Algebra.ofId (RatFunc Fq) (HypF Fq)) (-yF Fq) (by
    rw [← aeval_neg_y Fq, aeval_def]; rfl)

theorem conjHom_y : conjHom Fq (yF Fq) = -yF Fq := AdjoinRoot.liftAlgHom_root _ _ _ _

theorem conjHom_coords (a b : RatFunc Fq) :
    conjHom Fq (algebraMap (RatFunc Fq) (HypF Fq) a + algebraMap (RatFunc Fq) (HypF Fq) b * yF Fq) =
      algebraMap (RatFunc Fq) (HypF Fq) a - algebraMap (RatFunc Fq) (HypF Fq) b * yF Fq := by
  rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, conjHom_y]
  ring



/-- `a(x) + b(x) y` for polynomials `a, b`. -/
abbrev cP (a b : Fq[X]) : HypF Fq := algebraMap Fq[X] (HypF Fq) a + algebraMap Fq[X] (HypF Fq) b * yF Fq

theorem algebraMap_poly (a : Fq[X]) : algebraMap Fq[X] (HypF Fq) a =
    algebraMap (RatFunc Fq) (HypF Fq) (algebraMap Fq[X] (RatFunc Fq) a) :=
  IsScalarTower.algebraMap_apply Fq[X] (RatFunc Fq) (HypF Fq) a

theorem isIntegral_y : IsIntegral Fq[X] (yF Fq) := by
  refine ⟨X ^ 2 - C (f0 Fq), monic_X_pow_sub_C _ two_ne_zero, ?_⟩
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, hy, algebraMap_poly, sub_self]

theorem isIntegral_cP (a b : Fq[X]) : IsIntegral Fq[X] (cP Fq a b) :=
  isIntegral_algebraMap.add (isIntegral_algebraMap.mul (isIntegral_y Fq))

theorem cP_inj {a b a' b' : Fq[X]} (h : cP Fq a b = cP Fq a' b') : a = a' ∧ b = b' := by
  simp only [cP, algebraMap_poly] at h
  have h' := coords_unique Fq h
  exact ⟨IsFractionRing.injective Fq[X] (RatFunc Fq) h'.1, IsFractionRing.injective Fq[X] (RatFunc Fq) h'.2⟩

/-- An element of `Fq(x)` that is integral over `Fq[x]` (inside `HypF`) is a polynomial. -/
theorem mem_poly_of_isIntegral {r : RatFunc Fq} (h : IsIntegral Fq[X] (algebraMap (RatFunc Fq) (HypF Fq) r)) :
    ∃ a : Fq[X], algebraMap Fq[X] (RatFunc Fq) a = r :=
  IsIntegrallyClosed.isIntegral_iff.1
    ((isIntegral_algebraMap_iff (algebraMap (RatFunc Fq) (HypF Fq)).injective).1 h)

theorem squarefree_f0 (h5 : (5 : Fq) ≠ 0) : Squarefree (f0 Fq) := by
  have e : f0 Fq = X ^ 5 - C (-1) := by rw [C_neg, C_1, sub_neg_eq_add]
  rw [e]
  exact (separable_X_pow_sub_C (-1) (by exact_mod_cast h5) (neg_ne_zero.2 one_ne_zero)).squarefree

/-- If `B² (x⁵ + 1)` is a polynomial then so is `B` (`x⁵ + 1` is squarefree). -/
theorem exists_poly_of_sq_mul (h5 : (5 : Fq) ≠ 0) {B : RatFunc Fq} {d : Fq[X]}
    (h : B ^ 2 * f0K Fq = algebraMap Fq[X] (RatFunc Fq) d) :
    ∃ b : Fq[X], algebraMap Fq[X] (RatFunc Fq) b = B := by
  have hden : B.denom ≠ 0 := B.denom_ne_zero
  have hd' : algebraMap Fq[X] (RatFunc Fq) B.denom ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective Fq[X] (RatFunc Fq))]
    exact hden
  have e := RatFunc.num_div_denom B
  rw [div_eq_iff hd'] at e
  have key : B.num ^ 2 * f0 Fq = d * B.denom ^ 2 := by
    apply IsFractionRing.injective Fq[X] (RatFunc Fq)
    rw [map_mul, map_mul, map_pow, map_pow, e, ← h]
    ring
  have hdvd : B.denom ^ 2 ∣ B.num ^ 2 * f0 Fq := ⟨d, by rw [key, mul_comm]⟩
  have hcop : IsCoprime (B.denom ^ 2) (B.num ^ 2) := (RatFunc.isCoprime_num_denom B).symm.pow
  have hdf : B.denom * B.denom ∣ f0 Fq := by
    rw [← pow_two]
    exact hcop.dvd_of_dvd_mul_left hdvd
  have hu := squarefree_f0 Fq h5 _ hdf
  have h1 : B.denom = 1 := (RatFunc.monic_denom B).isUnit_iff.1 hu
  refine ⟨B.num, ?_⟩
  rw [e, h1, map_one, mul_one]

/-- **Integral closure**: `z` is integral over `Fq[x]` iff `z = a(x) + b(x) y` with polynomials `a, b`. -/
theorem isIntegral_iff (h2 : (2 : Fq) ≠ 0) (h5 : (5 : Fq) ≠ 0) (z : HypF Fq) :
    IsIntegral Fq[X] z ↔ ∃ a b : Fq[X], z = cP Fq a b := by
  refine ⟨fun hz => ?_, fun ⟨a, b, h⟩ => h ▸ isIntegral_cP Fq a b⟩
  obtain ⟨A, B, rfl⟩ := exists_coords Fq z
  have hσ := hz.map ((conjHom Fq).restrictScalars Fq[X])
  rw [AlgHom.coe_restrictScalars', conjHom_coords] at hσ
  have htr := hz.add hσ
  have hnm := hz.mul hσ
  rw [show algebraMap (RatFunc Fq) (HypF Fq) A + algebraMap (RatFunc Fq) (HypF Fq) B * yF Fq +
      (algebraMap (RatFunc Fq) (HypF Fq) A - algebraMap (RatFunc Fq) (HypF Fq) B * yF Fq) =
      algebraMap (RatFunc Fq) (HypF Fq) (2 * A) by rw [map_mul, map_ofNat]; ring] at htr
  rw [show (algebraMap (RatFunc Fq) (HypF Fq) A + algebraMap (RatFunc Fq) (HypF Fq) B * yF Fq) *
      (algebraMap (RatFunc Fq) (HypF Fq) A - algebraMap (RatFunc Fq) (HypF Fq) B * yF Fq) =
      algebraMap (RatFunc Fq) (HypF Fq) (A ^ 2 - B ^ 2 * f0K Fq) by
        rw [map_sub, map_mul, map_pow, map_pow, ← hy]; ring] at hnm
  obtain ⟨a2, ha2⟩ := mem_poly_of_isIntegral Fq htr
  obtain ⟨c, hc⟩ := mem_poly_of_isIntegral Fq hnm
  have h2K := two_ne_zero_ratFunc Fq h2
  have hA : algebraMap Fq[X] (RatFunc Fq) (C (2⁻¹ : Fq) * a2) = A := by
    rw [map_mul, ha2, RatFunc.algebraMap_C, map_inv₀, map_ofNat, inv_mul_cancel_left₀ h2K]
  have hB2 : B ^ 2 * f0K Fq = algebraMap Fq[X] (RatFunc Fq) ((C (2⁻¹ : Fq) * a2) ^ 2 - c) := by
    rw [map_sub, map_pow, hA, hc]
    ring
  obtain ⟨b, hb⟩ := exists_poly_of_sq_mul Fq h5 hB2
  exact ⟨C (2⁻¹ : Fq) * a2, b, by rw [cP, algebraMap_poly, algebraMap_poly, hA, hb]⟩



/-- The defining polynomial `Y² - (x⁵ + 1)` over `Fq[x]`. -/
abbrev gY : Fq[X][X] := X ^ 2 - C (f0 Fq)

theorem monic_gY : (gY Fq).Monic := monic_X_pow_sub_C _ two_ne_zero

theorem natDegree_gY : (gY Fq).natDegree = 2 := natDegree_X_pow_sub_C

/-- Every element of `Fq[x][Y]/(gY)` is `a + b Y`. -/
theorem exists_ab (z : AdjoinRoot (gY Fq)) :
    ∃ a b : Fq[X], z = AdjoinRoot.of (gY Fq) a + AdjoinRoot.of (gY Fq) b * AdjoinRoot.root (gY Fq) := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  have hm : AdjoinRoot.mk (gY Fq) (p %ₘ gY Fq) = AdjoinRoot.mk (gY Fq) p := by
    rw [← AdjoinRoot.modByMonicHom_mk (monic_gY Fq)]
    exact AdjoinRoot.mk_leftInverse (monic_gY Fq) _
  have hd : (p %ₘ gY Fq).natDegree ≤ 1 := by
    have h1 : gY Fq ≠ 1 := by
      intro h
      have := natDegree_gY Fq
      rw [h, natDegree_one] at this
      exact absurd this (by norm_num)
    have := natDegree_modByMonic_lt p (monic_gY Fq) h1
    rw [natDegree_gY] at this
    omega
  refine ⟨(p %ₘ gY Fq).coeff 0, (p %ₘ gY Fq).coeff 1, ?_⟩
  conv_lhs => rw [← hm, eq_X_add_C_of_natDegree_le_one hd]
  rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  ring

theorem eval_gY_yF : (gY Fq).eval₂ (algebraMap Fq[X] (HypF Fq)) (yF Fq) = 0 := by
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, hy, algebraMap_poly, sub_self]

/-- `Fq[x][Y]/(gY) → HypF`, `Y ↦ y`. -/
abbrev toF : AdjoinRoot (gY Fq) →ₐ[Fq[X]] HypF Fq :=
  AdjoinRoot.liftAlgHom (gY Fq) (Algebra.ofId Fq[X] (HypF Fq)) (yF Fq) (eval_gY_yF Fq)

theorem toF_of (r : Fq[X]) : toF Fq (AdjoinRoot.of (gY Fq) r) = algebraMap Fq[X] (HypF Fq) r :=
  AdjoinRoot.liftAlgHom_of _ _ _ _ r

theorem toF_root : toF Fq (AdjoinRoot.root (gY Fq)) = yF Fq :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem toF_ab (a b : Fq[X]) :
    toF Fq (AdjoinRoot.of (gY Fq) a + AdjoinRoot.of (gY Fq) b * AdjoinRoot.root (gY Fq)) = cP Fq a b := by
  rw [map_add, map_mul, toF_of, toF_of, toF_root]

theorem toF_mem (z : AdjoinRoot (gY Fq)) : toF Fq z ∈ integralClosure Fq[X] (HypF Fq) := by
  obtain ⟨a, b, rfl⟩ := exists_ab Fq z
  rw [toF_ab]
  exact (mem_integralClosure_iff _ _).mpr (isIntegral_cP Fq a b)

/-- `Fq[x][Y]/(gY) → Rfin`. -/
abbrev toRfin : AdjoinRoot (gY Fq) →ₐ[Fq[X]] integralClosure Fq[X] (HypF Fq) :=
  (toF Fq).codRestrict (integralClosure Fq[X] (HypF Fq)) (toF_mem Fq)

theorem toRfin_bijective (h2 : (2 : Fq) ≠ 0) (h5 : (5 : Fq) ≠ 0) : Function.Bijective (toRfin Fq) := by
  refine ⟨fun z₁ z₂ h => ?_, fun z => ?_⟩
  · obtain ⟨a, b, rfl⟩ := exists_ab Fq z₁
    obtain ⟨a', b', rfl⟩ := exists_ab Fq z₂
    have h' := congrArg (fun r : integralClosure Fq[X] (HypF Fq) => (r : HypF Fq)) h
    simp only [AlgHom.coe_codRestrict] at h'
    rw [toF_ab, toF_ab] at h'
    obtain ⟨rfl, rfl⟩ := cP_inj Fq h'
    rfl
  · obtain ⟨a, b, hab⟩ := (isIntegral_iff Fq h2 h5 (z : HypF Fq)).mp ((mem_integralClosure_iff _ _).mp z.2)
    refine ⟨AdjoinRoot.of (gY Fq) a + AdjoinRoot.of (gY Fq) b * AdjoinRoot.root (gY Fq), Subtype.ext ?_⟩
    simp only [AlgHom.coe_codRestrict]
    rw [toF_ab, hab]

/-- **`Rfin = Fq[x, y]/(y² - x⁵ - 1)`** (over `Fq[x]`). -/
def eRfin (h2 : (2 : Fq) ≠ 0) (h5 : (5 : Fq) ≠ 0) : AdjoinRoot (gY Fq) ≃ₐ[Fq[X]] integralClosure Fq[X] (HypF Fq) :=
  AlgEquiv.ofBijective (toRfin Fq) (toRfin_bijective Fq h2 h5)

/-- `Rfin = Fq[x, y]/(y² - x⁵ - 1)` over `Fq`. -/
def eRfinFq (h2 : (2 : Fq) ≠ 0) (h5 : (5 : Fq) ≠ 0) : AdjoinRoot (gY Fq) ≃ₐ[Fq] integralClosure Fq[X] (HypF Fq) :=
  (eRfin Fq h2 h5).restrictScalars Fq

theorem root_sq : AdjoinRoot.root (gY Fq) ^ 2 = AdjoinRoot.of (gY Fq) (f0 Fq) := by
  have h := AdjoinRoot.eval₂_root (gY Fq)
  rwa [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h

/-- **`L`-points**: `Hom_{Fq}(Fq[x][Y]/(gY), L) ≃ {(u, v) | v² = u⁵ + 1}`. -/
def homEquiv (L : Type) [CommRing L] [Algebra Fq L] :
    (AdjoinRoot (gY Fq) →ₐ[Fq] L) ≃ {q : L × L // q.2 ^ 2 = q.1 ^ 5 + 1} where
  toFun ψ := ⟨(ψ (AdjoinRoot.of (gY Fq) X), ψ (AdjoinRoot.root (gY Fq))), by
    have h := congrArg ψ (root_sq Fq)
    simpa [f0, map_pow, map_add, map_one] using h⟩
  invFun q := AdjoinRoot.liftAlgHom (gY Fq) (aeval q.1.1) q.1.2 (by
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, q.2]
    simp [f0])
  left_inv ψ := by
    dsimp only
    refine AdjoinRoot.algHom_ext' (Polynomial.algHom_ext ?_) ?_
    · simp
    · simp
  right_inv q := by
    apply Subtype.ext
    simp

end

end HypIntSol

open HypIntSol in
theorem solution
    (k : Type) [Field k] (h2 : (2 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (p : (RatFunc k)[X]) (hp : p = X ^ 2 - C (algebraMap k[X] (RatFunc k) (X ^ 5 + 1)))
    (g : k[X][X]) (hg : g = X ^ 2 - C (X ^ 5 + 1)) :
    (∀ z : AdjoinRoot p, IsIntegral k[X] z ↔
      ∃ a b : k[X], z = algebraMap k[X] (AdjoinRoot p) a + algebraMap k[X] (AdjoinRoot p) b * AdjoinRoot.root p) ∧
    (∃ e : AdjoinRoot g ≃ₐ[k[X]] integralClosure k[X] (AdjoinRoot p),
      (e (AdjoinRoot.root g) : AdjoinRoot p) = AdjoinRoot.root p) ∧
    ∀ (L : Type) [CommRing L] [Algebra k L],
      ∃ e : (integralClosure k[X] (AdjoinRoot p) →ₐ[k] L) ≃ {q : L × L // q.2 ^ 2 = q.1 ^ 5 + 1},
        ∀ (ψ : integralClosure k[X] (AdjoinRoot p) →ₐ[k] L) (u v : integralClosure k[X] (AdjoinRoot p)),
          (u : AdjoinRoot p) = algebraMap k[X] (AdjoinRoot p) X → (v : AdjoinRoot p) = AdjoinRoot.root p →
            (e ψ : L × L) = (ψ u, ψ v) := by
  subst hp hg
  refine ⟨fun z => isIntegral_iff k h2 h5 z, ⟨eRfin k h2 h5, toF_root k⟩, ?_⟩
  intro L _ _
  refine ⟨((eRfinFq k h2 h5).arrowCongr (AlgEquiv.refl : L ≃ₐ[k] L)).symm.trans (homEquiv k L), ?_⟩
  intro ψ u v hu hv
  have hu' : u = eRfinFq k h2 h5 (AdjoinRoot.of (gY k) X) :=
    Subtype.ext (by rw [hu]; exact (toF_of k X).symm)
  have hv' : v = eRfinFq k h2 h5 (AdjoinRoot.root (gY k)) :=
    Subtype.ext (by rw [hv]; exact (toF_root k).symm)
  subst hu' hv'
  rfl
