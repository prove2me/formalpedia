-- Prove2me | solution 1 for PrivPCP.lemma_4_13_zero_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:48:53.888728+00:00
-- url     : https://prove2.me/submissions/abe84497-b18d-487b-8f8e-c896b515faa6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_PrivPCP_gridQ
import Definitions.Def_PrivPCP_Supplement_gammaF
import Theorems.Thm_PrivPCP_lemma_4_13_degree_theory


namespace PrivPCP.PL

open AlgebraicCurve

variable {K L : Type} [Field K] [Field L] [Algebra K L]

lemma mem_iff_ord (v : Place K L) (f : L) (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  constructor
  · intro hfO
    by_contra hneg
    push Not at hneg
    set m : ℕ := (-v.ord f).toNat with hm
    have hm1 : 1 ≤ m := by omega
    have hmz : ((m : ℕ) : ℤ) = -v.ord f := Int.toNat_of_nonneg (by omega)
    have hπ0 : (π : L) ≠ 0 := by simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
    have hu' : ((u : v.toValuationSubring) : L) = f * (π : L) ^ m := by
      have : (π : L) ^ v.ord f * (π : L) ^ m = 1 := by
        rw [← zpow_natCast, ← zpow_add₀ hπ0, hmz, add_neg_cancel, zpow_zero]
      calc ((u : v.toValuationSubring) : L) = (u : L) * ((π : L) ^ v.ord f * (π : L) ^ m) := by
            rw [this, mul_one]
        _ = f * (π : L) ^ m := by rw [← mul_assoc, ← hu]
    have heq : (u : v.toValuationSubring) = ⟨f, hfO⟩ * π ^ m := by
      apply Subtype.ext; rw [hu']; simp
    have hmax : (u : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
      rw [heq]
      apply Ideal.mul_mem_left
      apply Ideal.pow_mem_of_mem _ _ m (by omega)
      exact (IsLocalRing.mem_maximalIdeal _).2 hπ.not_isUnit
    exact (IsLocalRing.mem_maximalIdeal _).1 hmax u.isUnit
  · intro h
    have hn : ((v.ord f).toNat : ℤ) = v.ord f := Int.toNat_of_nonneg h
    rw [hu, ← hn, zpow_natCast]
    exact mul_mem (u : v.toValuationSubring).2 (pow_mem π.2 _)

lemma ord_eq_zero_of_not_mem (v : Place K L) (a : v.toValuationSubring)
    (ha : a ∉ IsLocalRing.maximalIdeal v.toValuationSubring) : v.ord (a : L) = 0 := by
  have hu : IsUnit a := by
    by_contra h; exact ha ((IsLocalRing.mem_maximalIdeal _).2 h)
  have := v.ord_coe_unit hu.unit
  simpa using this

lemma one_le_ord_of_mem (v : Place K L) (a : v.toValuationSubring)
    (ha : a ∈ IsLocalRing.maximalIdeal v.toValuationSubring) (ha0 : (a : L) ≠ 0) :
    1 ≤ v.ord (a : L) := by
  have h0 : 0 ≤ v.ord (a : L) := (mem_iff_ord v _ ha0).1 a.2
  rcases h0.lt_or_eq with h | h
  · omega
  · exfalso
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow ha0 hπ
    rw [← h, zpow_zero, mul_one] at hu
    have : a = (u : v.toValuationSubring) := Subtype.ext hu
    rw [this] at ha
    exact (IsLocalRing.mem_maximalIdeal _).1 ha u.isUnit

lemma ord_const (v : Place K L) (c : K) (hc : c ≠ 0) : v.ord (algebraMap K L c) = 0 := by
  have hu : IsUnit (algebraMap K v.toValuationSubring c) := (isUnit_iff_ne_zero.2 hc).map _
  have := v.ord_coe_unit hu.unit
  simpa using this

lemma ord_div (v : Place K L) (a b : L) (ha : a ≠ 0) (hb : b ≠ 0) :
    v.ord (a / b) = v.ord a - v.ord b := by
  rw [div_eq_mul_inv, v.ord_mul ha (inv_ne_zero hb), v.ord_inv]; ring

end PrivPCP.PL


namespace PrivPCP.ZC

open AlgebraicCurve PrivPCP.PL

variable {K L : Type} [Field K] [Field L] [Algebra K L]

lemma ord_neg (v : Place K L) (f : L) : v.ord (-f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have : -f = algebraMap K L (-1) * f := by rw [map_neg, map_one, neg_one_mul]
  rw [this, v.ord_mul (by simp) hf, ord_const v _ (by norm_num), zero_add]

lemma ord_add_ge (v : Place K L) (f g : L) (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (v.ord f) (v.ord g) ≤ v.ord (f + g) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπ0 : (π : L) ≠ 0 := by simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  set m := min (v.ord f) (v.ord g)
  have hpm : v.ord ((π : L) ^ m) = m := by rw [v.ord_zpow, v.ord_coe_irreducible hπ, mul_one]
  have hpm0 : (π : L) ^ m ≠ 0 := zpow_ne_zero _ hπ0
  have h1 : f / (π : L) ^ m ∈ v.toValuationSubring := by
    rw [mem_iff_ord v _ (div_ne_zero hf hpm0), ord_div v _ _ hf hpm0, hpm]
    have := min_le_left (v.ord f) (v.ord g); omega
  have h2 : g / (π : L) ^ m ∈ v.toValuationSubring := by
    rw [mem_iff_ord v _ (div_ne_zero hg hpm0), ord_div v _ _ hg hpm0, hpm]
    have := min_le_right (v.ord f) (v.ord g); omega
  have h3 : (f + g) / (π : L) ^ m ∈ v.toValuationSubring := by
    rw [add_div]; exact add_mem h1 h2
  rw [mem_iff_ord v _ (div_ne_zero hfg hpm0), ord_div v _ _ hfg hpm0, hpm] at h3
  omega

/-- the ultrametric inequality, allowing zero summands -/
lemma ord_add_ge' (v : Place K L) (f g : L) (m : ℤ) (hf : f = 0 ∨ m ≤ v.ord f)
    (hg : g = 0 ∨ m ≤ v.ord g) : f + g = 0 ∨ m ≤ v.ord (f + g) := by
  by_cases hfg : f + g = 0
  · exact Or.inl hfg
  right
  by_cases hf0 : f = 0
  · rw [hf0, zero_add] at hfg ⊢
    rcases hg with h | h
    · exact absurd h hfg
    · exact h
  by_cases hg0 : g = 0
  · rw [hg0, add_zero] at hfg ⊢
    rcases hf with h | h
    · exact absurd h hf0
    · exact h
  have h1 := hf.resolve_left hf0
  have h2 := hg.resolve_left hg0
  have := ord_add_ge v f g hf0 hg0 hfg
  have := le_min h1 h2
  omega

lemma ord_sum_ge {ι : Type} (v : Place K L) (s : Finset ι) (t : ι → L) (m : ℤ)
    (h : ∀ i ∈ s, t i = 0 ∨ m ≤ v.ord (t i)) : ∑ i ∈ s, t i = 0 ∨ m ≤ v.ord (∑ i ∈ s, t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact ord_add_ge' v _ _ m (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- strict ultrametric equality -/
lemma ord_add_eq_of_lt (v : Place K L) (f g : L) (hf : f ≠ 0) (hg : g ≠ 0)
    (hlt : v.ord f < v.ord g) : v.ord (f + g) = v.ord f := by
  have hfg : f + g ≠ 0 := by
    intro h
    have : f = -g := eq_neg_of_add_eq_zero_left h
    rw [this, ord_neg] at hlt; omega
  have h1 := ord_add_ge v f g hf hg hfg
  have h2 := ord_add_ge v (f + g) (-g) hfg (neg_ne_zero.2 hg) (by simpa using hf)
  rw [add_neg_cancel_right, ord_neg] at h2
  have : min (v.ord f) (v.ord g) = v.ord f := min_eq_left hlt.le
  rw [this] at h1
  rcases le_total (v.ord (f + g)) (v.ord g) with h | h
  · rw [min_eq_left h] at h2; omega
  · rw [min_eq_right h] at h2; omega

end PrivPCP.ZC


namespace PrivPCP.BP

open MvPolynomial

variable {K L : Type} [Field K] [IsAlgClosed K] [Field L] [Algebra K L]

lemma alg_in_range (x : L) (hx : IsAlgebraic K x) : ∃ k : K, x = algebraMap K L k := by
  have hint : IsIntegral K x := hx.isIntegral
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint)
  obtain ⟨k, hk⟩ := minpoly.mem_range_of_degree_eq_one K x hdeg
  exact ⟨k, hk.symm⟩

/-- the coordinates of a mixed irreducible curve are transcendental -/
lemma coord_transcendental (x y : L) (F : MvPolynomial (Fin 2) K) (hF : Irreducible F)
    (i j : Fin 2) (hij : i ≠ j) (hFj : 0 < F.degreeOf j)
    (hker : RingHom.ker (MvPolynomial.aeval (R := K) ![x, y]).toRingHom = Ideal.span {F}) :
    Transcendental K ((![x, y] : Fin 2 → L) i) := by
  intro halg
  obtain ⟨k, hk⟩ := alg_in_range _ halg
  have hmem : (X i - C k : MvPolynomial (Fin 2) K) ∈
      RingHom.ker (MvPolynomial.aeval (R := K) ![x, y]).toRingHom := by
    rw [RingHom.mem_ker]
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_sub, aeval_X, aeval_C]
    rw [hk, sub_self]
  rw [hker, Ideal.mem_span_singleton] at hmem
  obtain ⟨G, hG⟩ := hmem
  have hG0 : G ≠ 0 := by
    rintro rfl; rw [mul_zero] at hG
    have := congrArg (MvPolynomial.coeff (Finsupp.single i 1)) hG
    have h0 : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single i 1 := by
      intro h; have := congrArg (fun f => f i) h; simp at this
    simp [coeff_X', coeff_C, h0] at this
  have := degreeOf_mul_eq (n := j) hF.ne_zero hG0
  rw [← hG] at this
  have hle : (X i - C k : MvPolynomial (Fin 2) K).degreeOf j = 0 := by
    have h1 := degreeOf_sub_le j (X i : MvPolynomial (Fin 2) K) (C k)
    rw [degreeOf_X, if_neg (Ne.symm hij), degreeOf_C] at h1
    omega
  omega

end PrivPCP.BP


namespace PrivPCP.BP

variable {K L : Type} [Field K] [IsAlgClosed K] [Field L] [Algebra K L]

lemma alg_of_pow (u : L) (g : ℕ) (hg : 0 < g) (c : K) (h : u ^ g = algebraMap K L c) :
    IsAlgebraic K u := by
  refine ⟨Polynomial.X ^ g - Polynomial.C c, Polynomial.X_pow_sub_C_ne_zero hg c, ?_⟩
  simp [h]

lemma param_of_relation (x y : L) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (A B : ℤ) (hA : A ≠ 0) (hB : B ≠ 0)
    (c : K) (hc : x ^ A * y ^ B = algebraMap K L c) :
    ∃ (z : L) (μ ν : K) (β : ℕ) (e : ℤ), 0 < β ∧ e ≠ 0 ∧ Nat.Coprime β e.natAbs ∧ μ ≠ 0 ∧ ν ≠ 0 ∧
      z ≠ 0 ∧ x = algebraMap K L μ * z ^ β ∧ y = algebraMap K L ν * z ^ e := by
  set g := Int.gcd A B with hg
  have hgpos : 0 < g := Int.gcd_pos_of_ne_zero_left B hA
  set A' := A / g with hA'
  set B' := B / g with hB'
  have hAe : A = g * A' := (Int.mul_ediv_cancel' (Int.gcd_dvd_left A B)).symm
  have hBe : B = g * B' := (Int.mul_ediv_cancel' (Int.gcd_dvd_right A B)).symm
  have hA'0 : A' ≠ 0 := by intro h; apply hA; rw [hAe, h, mul_zero]
  have hB'0 : B' ≠ 0 := by intro h; apply hB; rw [hBe, h, mul_zero]
  have hcop : Int.gcd A' B' = 1 := Int.gcd_div_gcd_div_gcd hgpos
  set u := x ^ A' * y ^ B' with hu
  have hu0 : u ≠ 0 := mul_ne_zero (zpow_ne_zero _ hx0) (zpow_ne_zero _ hy0)
  have hug : u ^ g = algebraMap K L c := by
    rw [← hc, hu, mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, hAe, hBe,
      mul_comm (A' : ℤ), mul_comm (B' : ℤ)]
  obtain ⟨ζ, hζ⟩ := alg_in_range u (alg_of_pow u g hgpos c hug)
  have hζ0 : ζ ≠ 0 := by rintro rfl; rw [map_zero] at hζ; exact hu0 hζ
  have hbez : (1 : ℤ) = A' * Int.gcdA A' B' + B' * Int.gcdB A' B' := by
    rw [← Int.gcd_eq_gcd_ab, hcop]; rfl
  set s := Int.gcdA A' B'
  set t := Int.gcdB A' B'
  set z0 := x ^ t * y ^ (-s) with hz0
  have hz00 : z0 ≠ 0 := mul_ne_zero (zpow_ne_zero _ hx0) (zpow_ne_zero _ hy0)
  have hxz : x = algebraMap K L (ζ ^ s) * z0 ^ B' := by
    rw [map_zpow₀, ← hζ, hu, hz0, mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul,
      ← zpow_mul]
    have : x ^ (A' * s) * y ^ (B' * s) * (x ^ (t * B') * y ^ (-s * B')) =
        x ^ (A' * s + t * B') * y ^ (B' * s + -s * B') := by
      rw [zpow_add₀ hx0, zpow_add₀ hy0]; ring
    rw [this, show A' * s + t * B' = 1 by linarith, show B' * s + -s * B' = 0 by ring, zpow_one,
      zpow_zero, mul_one]
  have hyz : y = algebraMap K L (ζ ^ t) * z0 ^ (-A') := by
    rw [map_zpow₀, ← hζ, hu, hz0, mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul,
      ← zpow_mul]
    have : x ^ (A' * t) * y ^ (B' * t) * (x ^ (t * -A') * y ^ (-s * -A')) =
        x ^ (A' * t + t * -A') * y ^ (B' * t + -s * -A') := by
      rw [zpow_add₀ hx0, zpow_add₀ hy0]; ring
    rw [this, show A' * t + t * -A' = 0 by ring, show B' * t + -s * -A' = 1 by linarith, zpow_one,
      zpow_zero, one_mul]
  have hcopN : Nat.Coprime B'.natAbs A'.natAbs := by
    rw [Nat.coprime_comm]; exact hcop
  rcases lt_or_gt_of_ne hB'0 with hneg | hpos
  · refine ⟨z0⁻¹, ζ ^ s, ζ ^ t, B'.natAbs, A', by omega, hA'0, hcopN, zpow_ne_zero _ hζ0,
      zpow_ne_zero _ hζ0, inv_ne_zero hz00, ?_, ?_⟩
    · rw [hxz, ← zpow_natCast, inv_zpow', Int.natCast_natAbs, abs_of_neg hneg, neg_neg]
    · rw [hyz, inv_zpow']
  · refine ⟨z0, ζ ^ s, ζ ^ t, B'.natAbs, -A', by omega, neg_ne_zero.2 hA'0, by simpa using hcopN,
      zpow_ne_zero _ hζ0, zpow_ne_zero _ hζ0, hz00, ?_, hyz⟩
    rw [hxz, ← zpow_natCast, Int.natCast_natAbs, abs_of_pos hpos]

end PrivPCP.BP


namespace PrivPCP.BP

open MvPolynomial Classical

variable {K L : Type} [Field K] [Field L] [Algebra K L]

lemma aeval_eq_sum (v : Fin 2 → L) (F : MvPolynomial (Fin 2) K) :
    aeval v F = ∑ m ∈ F.support, algebraMap K L (F.coeff m) * (v 0 ^ m 0 * v 1 ^ m 1) := by
  conv_lhs => rw [F.as_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two]

/-- lower bound on the bidegree from a monomial parametrization -/
lemma degree_lower (F : MvPolynomial (Fin 2) K) (hF : F ≠ 0) (z : L) (hzt : Transcendental K z)
    (hz0 : z ≠ 0) (μ ν : K) (hμ : μ ≠ 0) (hν : ν ≠ 0) (β : ℕ) (e : ℤ) (hβ : 0 < β) (he : e ≠ 0)
    (hcop : Nat.Coprime β e.natAbs)
    (hF0 : aeval ![algebraMap K L μ * z ^ β, algebraMap K L ν * z ^ e] F = 0) :
    e.natAbs ≤ F.degreeOf 0 ∧ β ≤ F.degreeOf 1 := by
  set α := e.natAbs with hαdef
  set N : ℤ := α * F.degreeOf 1 with hN
  have hdeg : ∀ m ∈ F.support, m 0 ≤ F.degreeOf 0 ∧ m 1 ≤ F.degreeOf 1 := fun m hm =>
    ⟨(degreeOf_le_iff.mp (le_refl (F.degreeOf 0))) m hm,
      (degreeOf_le_iff.mp (le_refl (F.degreeOf 1))) m hm⟩
  set ex : (Fin 2 →₀ ℕ) → ℤ := fun m => β * m 0 + e * m 1 + N with hex
  have hexpos : ∀ m ∈ F.support, 0 ≤ ex m := by
    intro m hm
    have h1 := (hdeg m hm).2
    have he1 : -(α : ℤ) ≤ e := by rw [hαdef]; omega
    have q1 : -(α : ℤ) * m 1 ≤ e * m 1 := mul_le_mul_of_nonneg_right he1 (by positivity)
    have q2 : (α : ℤ) * m 1 ≤ α * F.degreeOf 1 :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast h1) (by positivity)
    have q3 : (0 : ℤ) ≤ β * m 0 := by positivity
    simp only [hex, hN]; linarith
  set w : (Fin 2 →₀ ℕ) → K := fun m => F.coeff m * μ ^ m 0 * ν ^ m 1 with hw
  set Q : Polynomial K := ∑ m ∈ F.support, Polynomial.C (w m) * Polynomial.X ^ (ex m).toNat with hQ
  have hQz : Polynomial.aeval z Q =
      z ^ N * aeval ![algebraMap K L μ * z ^ β, algebraMap K L ν * z ^ e] F := by
    rw [aeval_eq_sum, Finset.mul_sum, hQ, map_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    simp only [map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, Polynomial.aeval_X, map_pow, hw,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← zpow_natCast z (ex m).toNat, Int.toNat_of_nonneg (hexpos m hm)]
    have e1 : z ^ (ex m) = z ^ ((β : ℤ) * m 0) * z ^ (e * m 1) * z ^ N := by
      rw [hex, zpow_add₀ hz0, zpow_add₀ hz0]
    have e2 : (z ^ β) ^ (m 0) = z ^ ((β : ℤ) * m 0) := by
      rw [← pow_mul, ← zpow_natCast]; push_cast; ring_nf
    have e3 : (z ^ e) ^ (m 1) = z ^ (e * m 1) := by
      rw [← zpow_natCast, ← zpow_mul]
    rw [mul_pow, mul_pow, e2, e3, e1]
    ring
  rw [hF0, mul_zero] at hQz
  have hQ0 : Q = 0 := by
    by_contra h; exact hzt ⟨Q, h, hQz⟩
  obtain ⟨ms, hms⟩ := support_nonempty.2 hF
  have hcoef := congrArg (fun p => p.coeff (ex ms).toNat) hQ0
  simp only [hQ, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hcoef
  obtain ⟨m, hm, hne, hexeq⟩ : ∃ m ∈ F.support, m ≠ ms ∧ ex m = ex ms := by
    by_contra hno
    push Not at hno
    rw [Finset.sum_eq_single ms] at hcoef
    · rw [if_pos rfl] at hcoef
      have : w ms ≠ 0 := by
        simp only [hw]
        exact mul_ne_zero (mul_ne_zero (mem_support_iff.1 hms) (pow_ne_zero _ hμ)) (pow_ne_zero _ hν)
      exact this hcoef
    · intro b hb hbne
      rw [if_neg]
      intro h
      apply hno b hb hbne
      have h1 := hexpos b hb
      have h2 := hexpos ms hms
      omega
    · intro h; exact absurd hms h
  have hrel : (β : ℤ) * ((m 0 : ℤ) - ms 0) = e * ((ms 1 : ℤ) - m 1) := by
    simp only [hex] at hexeq; linarith
  have key := congrArg Int.natAbs hrel
  rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast] at key
  set D0 := ((m 0 : ℤ) - ms 0).natAbs with hD0
  set D1 := ((ms 1 : ℤ) - m 1).natAbs with hD1
  have hD0pos : 0 < D0 := by
    rw [hD0, Int.natAbs_pos]
    intro h0
    rw [h0, mul_zero] at hrel
    have h1 : (ms 1 : ℤ) - m 1 = 0 := by
      rcases mul_eq_zero.1 hrel.symm with h | h
      · exact absurd h he
      · exact h
    apply hne
    ext i; fin_cases i
    · show m 0 = ms 0; omega
    · show m 1 = ms 1; omega
  have hα0 : 0 < α := Int.natAbs_pos.2 he
  have hD1pos : 0 < D1 := by
    by_contra h
    have : D1 = 0 := by omega
    rw [this, mul_zero] at key
    have := Nat.mul_pos hβ hD0pos
    omega
  have hαD0 : α ∣ D0 := by
    have : α ∣ D0 * β := ⟨D1, by rw [mul_comm D0, key]⟩
    exact (Nat.Coprime.symm hcop).dvd_of_dvd_mul_right this
  have hβD1 : β ∣ D1 := by
    have : β ∣ D1 * α := ⟨D0, by rw [mul_comm D1, ← key]⟩
    exact hcop.dvd_of_dvd_mul_right this
  have hD0le : D0 ≤ F.degreeOf 0 := by
    have := (hdeg m hm).1; have := (hdeg ms hms).1; omega
  have hD1le : D1 ≤ F.degreeOf 1 := by
    have := (hdeg m hm).2; have := (hdeg ms hms).2; omega
  exact ⟨(Nat.le_of_dvd hD0pos hαD0).trans hD0le, (Nat.le_of_dvd hD1pos hβD1).trans hD1le⟩

end PrivPCP.BP


namespace PrivPCP.DEP

open Polynomial Classical

variable {K L : Type} [Field K] [Field L] [Algebra K L]

lemma ord_const (v : AlgebraicCurve.Place K L) (c : K) (hc : c ≠ 0) :
    v.ord (algebraMap K L c) = 0 := by
  have hu : IsUnit (algebraMap K v.toValuationSubring c) := (isUnit_iff_ne_zero.2 hc).map _
  have := v.ord_coe_unit hu.unit
  simpa using this

lemma ord_npow (v : AlgebraicCurve.Place K L) (f : L) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  have := v.ord_zpow f (n : ℤ)
  simpa using this

lemma rootMult_le_one (M : ℕ) (β : K) (hM : (M : K) ≠ 0) (hβ : β ≠ 0) (c : K) :
    (X ^ M - C β).rootMultiplicity c ≤ 1 :=
  rootMultiplicity_le_one_of_separable (separable_X_pow_sub_C β hM hβ) c

/-- common roots of two binomials -/
lemma card_common_roots (M N : ℕ) (hM : 0 < M) (hN : 0 < N) (β₁ β₂ : K) (h1 : β₁ ≠ 0) (h2 : β₂ ≠ 0) :
    ((X ^ M - C β₁).roots.toFinset ∩ (X ^ N - C β₂).roots.toFinset).card ≤ Nat.gcd M N := by
  set g := Nat.gcd M N with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hM
  set γ : K := β₁ ^ (Nat.gcdA M N) * β₂ ^ (Nat.gcdB M N)
  have hp : (X ^ g - C γ : K[X]) ≠ 0 := X_pow_sub_C_ne_zero hg0 γ
  have hsub : ((X ^ M - C β₁).roots.toFinset ∩ (X ^ N - C β₂).roots.toFinset) ⊆
      (X ^ g - C γ).roots.toFinset := by
    intro c hc
    rw [Finset.mem_inter, Multiset.mem_toFinset, Multiset.mem_toFinset,
      mem_roots (X_pow_sub_C_ne_zero hM β₁), mem_roots (X_pow_sub_C_ne_zero hN β₂)] at hc
    rw [Multiset.mem_toFinset, mem_roots hp]
    simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hc ⊢
    have hc0 : c ≠ 0 := by
      rintro rfl; rw [zero_pow hM.ne'] at hc; exact h1 hc.1.symm
    have e : ((g : ℕ) : ℤ) = M * Nat.gcdA M N + N * Nat.gcdB M N := Nat.gcd_eq_gcd_ab M N
    have : c ^ ((g : ℕ) : ℤ) = γ := by
      rw [e, zpow_add₀ hc0, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hc.1, hc.2]
    simpa using this
  have e1 := Finset.card_le_card hsub
  have e2 := Multiset.toFinset_card_le (X ^ g - C γ).roots
  have e3 := card_roots' (X ^ g - C γ)
  have e4 : (X ^ g - C γ).natDegree = g := natDegree_X_pow_sub_C
  omega

lemma gcd_le_ab (a b n1 n2 : ℕ) (ha : 0 < a) (hb : 0 < b) (hn : Nat.Coprime n1 n2) :
    Nat.gcd (b * n1) (a * n2) ≤ a * b := by
  have h1 : Nat.gcd (b * n1) (a * n2) ∣ a * b * n1 :=
    (Nat.gcd_dvd_left _ _).trans ⟨a, by ring⟩
  have h2 : Nat.gcd (b * n1) (a * n2) ∣ a * b * n2 :=
    (Nat.gcd_dvd_right _ _).trans ⟨b, by ring⟩
  have h3 := Nat.dvd_gcd h1 h2
  rw [Nat.gcd_mul_left, hn, mul_one] at h3
  exact Nat.le_of_dvd (Nat.mul_pos ha hb) h3

end PrivPCP.DEP


namespace PrivPCP.ZC

open AlgebraicCurve PrivPCP.PL MvPolynomial

variable {K L : Type} [Field K] [Field L] [Algebra K L]

lemma ord_monomial_ge (v : Place K L) (x y : L) (hx : x ≠ 0) (hy : y ≠ 0) (c : K) (i j dX dY : ℕ)
    (hi : i ≤ dX) (hj : j ≤ dY) :
    algebraMap K L c * (x ^ i * y ^ j) = 0 ∨
      -((dX * (-v.ord x).toNat + dY * (-v.ord y).toNat : ℕ) : ℤ) ≤ v.ord (algebraMap K L c * (x ^ i * y ^ j)) := by
  by_cases hc : c = 0
  · left; simp [hc]
  right
  rw [v.ord_mul (by simpa using hc) (mul_ne_zero (pow_ne_zero _ hx) (pow_ne_zero _ hy)),
    PrivPCP.PL.ord_const v c hc, v.ord_mul (pow_ne_zero _ hx) (pow_ne_zero _ hy),
    PrivPCP.DEP.ord_npow, PrivPCP.DEP.ord_npow]
  push_cast
  have h1 : -(((-v.ord x).toNat : ℕ) : ℤ) ≤ v.ord x := by omega
  have h2 : -(((-v.ord y).toNat : ℕ) : ℤ) ≤ v.ord y := by omega
  have h3 : (0 : ℤ) ≤ ((-v.ord x).toNat : ℕ) := by positivity
  have h4 : (0 : ℤ) ≤ ((-v.ord y).toNat : ℕ) := by positivity
  have hi' : (i : ℤ) ≤ dX := by exact_mod_cast hi
  have hj' : (j : ℤ) ≤ dY := by exact_mod_cast hj
  nlinarith

/-- poles of `Q(x, y)` -/
lemma pole_bound (v : Place K L) (x y : L) (hx : x ≠ 0) (hy : y ≠ 0) (Q : MvPolynomial (Fin 2) K)
    (hQ : aeval ![x, y] Q ≠ 0) :
    (-v.ord (aeval ![x, y] Q)).toNat ≤ Q.degreeOf 0 * (-v.ord x).toNat + Q.degreeOf 1 * (-v.ord y).toNat := by
  have := ord_sum_ge v Q.support (fun m => algebraMap K L (Q.coeff m) * (x ^ m 0 * y ^ m 1))
    (-((Q.degreeOf 0 * (-v.ord x).toNat + Q.degreeOf 1 * (-v.ord y).toNat : ℕ) : ℤ))
    (fun m hm => ord_monomial_ge v x y hx hy _ _ _ _ _
      ((degreeOf_le_iff.mp (le_refl (Q.degreeOf 0))) m hm)
      ((degreeOf_le_iff.mp (le_refl (Q.degreeOf 1))) m hm))
  have he := PrivPCP.BP.aeval_eq_sum ![x, y] Q
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at he
  rw [← he] at this
  rcases this with h | h
  · exact absurd h hQ
  · omega

/-- values of polynomials at integral points are integral -/
lemma aeval_mem (v : Place K L) (x y : L) (hx : x ∈ v.toValuationSubring)
    (hy : y ∈ v.toValuationSubring) (Q : MvPolynomial (Fin 2) K) :
    aeval ![x, y] Q ∈ v.toValuationSubring := by
  rw [PrivPCP.BP.aeval_eq_sum]
  refine sum_mem fun m _ => mul_mem (v.algebraMap_mem' _) (mul_mem (pow_mem ?_ _) (pow_mem ?_ _))
  · simpa using hx
  · simpa using hy

lemma ord_one_sub_pow_neg (v : Place K L) (x : L) (hx : x ≠ 0) (n : ℕ) (hn : 0 < n)
    (h : v.ord x < 0) : v.ord (1 - x ^ n) = n * v.ord x := by
  have e : 1 - x ^ n = -(x ^ n) + 1 := by ring
  rw [e, ord_add_eq_of_lt v _ _ (neg_ne_zero.2 (pow_ne_zero _ hx)) one_ne_zero, ord_neg,
    PrivPCP.DEP.ord_npow]
  rw [ord_neg, PrivPCP.DEP.ord_npow, v.ord_one]
  have : (0 : ℤ) < n := by exact_mod_cast hn
  nlinarith

lemma ord_one_sub_pow_pos (v : Place K L) (x : L) (hx : x ≠ 0) (n : ℕ) (hn : 0 < n)
    (h : 0 < v.ord x) : v.ord (1 - x ^ n) = 0 := by
  have e : 1 - x ^ n = 1 + -(x ^ n) := by ring
  rw [e, ord_add_eq_of_lt v _ _ one_ne_zero (neg_ne_zero.2 (pow_ne_zero _ hx)), v.ord_one]
  rw [ord_neg, PrivPCP.DEP.ord_npow, v.ord_one]
  have : (0 : ℤ) < n := by exact_mod_cast hn
  positivity

lemma ord_one_sub_pow_nonneg (v : Place K L) (x : L) (n : ℕ) (h : 0 ≤ v.ord x)
    (hne : 1 - x ^ n ≠ 0) : 0 ≤ v.ord (1 - x ^ n) := by
  have hx : x ∈ v.toValuationSubring := by
    by_cases hx0 : x = 0
    · rw [hx0]; exact zero_mem _
    · exact (mem_iff_ord v x hx0).2 h
  have : 1 - x ^ n ∈ v.toValuationSubring := sub_mem (one_mem _) (pow_mem hx _)
  exact (mem_iff_ord v _ hne).1 this

end PrivPCP.ZC


namespace PrivPCP.ZC

open AlgebraicCurve PrivPCP.PL Classical

variable {K L : Type} [Field K] [Field L] [Algebra K L]

lemma zeros_eq_poles (f : L) (hfin : (Function.support fun v : Place K L => v.ord f).Finite)
    (hsum : ∑ᶠ v : Place K L, v.ord f = 0) (T : Finset (Place K L)) (hT : hfin.toFinset ⊆ T) :
    ∑ v ∈ T, (v.ord f).toNat = ∑ v ∈ T, (-(v.ord f)).toNat := by
  have h := finsum_eq_finsetSum_of_support_subset (fun v : Place K L => v.ord f) (s := T)
    (by intro v hv; exact hT (hfin.mem_toFinset.2 hv))
  rw [hsum] at h
  have : ((∑ v ∈ T, (v.ord f).toNat : ℕ) : ℤ) = ((∑ v ∈ T, (-(v.ord f)).toNat : ℕ) : ℤ) := by
    push_cast
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    simp only [Int.toNat_sub_toNat_neg]
    exact h.symm
  exact_mod_cast this

lemma poles_sum (x : L) (hfin : (Function.support fun v : Place K L => v.ord x).Finite)
    (b : ℕ) (hb : ∑ᶠ v : Place K L, (-(v.ord x)).toNat = b) (T : Finset (Place K L))
    (hT : hfin.toFinset ⊆ T) : ∑ v ∈ T, (-(v.ord x)).toNat = b := by
  rw [← hb, finsum_eq_finsetSum_of_support_subset _ (s := T)]
  intro v hv
  apply hT
  rw [hfin.mem_toFinset]
  intro h0
  apply hv
  simp only [h0, neg_zero, Int.toNat_zero]

lemma pole_sub_const (v : Place K L) (x : L) (a : K) (ha : a ≠ 0) (hxa : x - algebraMap K L a ≠ 0) :
    (-(v.ord (x - algebraMap K L a))).toNat = (-(v.ord x)).toNat := by
  rcases lt_or_ge (v.ord x) 0 with h | h
  · have hx0 : x ≠ 0 := by rintro rfl; simp at h
    have e : x - algebraMap K L a = x + -(algebraMap K L a) := by ring
    rw [e, ord_add_eq_of_lt v _ _ hx0 (neg_ne_zero.2 (by simpa using ha))]
    rw [ord_neg, ord_const v a ha]; exact h
  · have hxO : x ∈ v.toValuationSubring := by
      by_cases hx0 : x = 0
      · rw [hx0]; exact zero_mem _
      · exact (mem_iff_ord v x hx0).2 h
    have : x - algebraMap K L a ∈ v.toValuationSubring := sub_mem hxO (v.algebraMap_mem' a)
    have h2 := (mem_iff_ord v _ hxa).1 this
    rw [Int.toNat_eq_zero.2 (by omega), Int.toNat_eq_zero.2 (by omega)]

/-- a single zero multiplicity is at most the number of poles -/
lemma zero_le_poles (f : L) (hf : f ≠ 0)
    (hDT : ∀ f : L, f ≠ 0 → (Function.support fun v : Place K L => v.ord f).Finite ∧
      ∑ᶠ v : Place K L, v.ord f = 0) (v : Place K L) :
    (v.ord f).toNat ≤ ∑ᶠ w : Place K L, (-(w.ord f)).toNat := by
  obtain ⟨hfin, hsum⟩ := hDT f hf
  set T := insert v hfin.toFinset
  have h1 := zeros_eq_poles f hfin hsum T (Finset.subset_insert _ _)
  have h2 : (v.ord f).toNat ≤ ∑ w ∈ T, (w.ord f).toNat :=
    Finset.single_le_sum (f := fun w : Place K L => (w.ord f).toNat) (fun _ _ => Nat.zero_le _)
      (Finset.mem_insert_self _ _)
  rw [h1] at h2
  rw [finsum_eq_finsetSum_of_support_subset _ (s := T)]
  · exact h2
  · intro w hw
    apply Finset.mem_insert_of_mem
    rw [hfin.mem_toFinset]
    intro h0; apply hw; simp only [h0, neg_zero, Int.toNat_zero]

lemma ord_prod (v : Place K L) {ι : Type} (s : Finset ι) (t : ι → L) (ht : ∀ i ∈ s, t i ≠ 0) :
    v.ord (∏ i ∈ s, t i) = ∑ i ∈ s, v.ord (t i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      v.ord_mul (ht a (Finset.mem_insert_self a s)) (Finset.prod_ne_zero_iff.2 fun i hi =>
        ht i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => ht i (Finset.mem_insert_of_mem hi)]

end PrivPCP.ZC


namespace PrivPCP.GD

open Classical MvPolynomial

variable {F : Type} [Field F]

lemma le_degreeOf_of_mem {R : MvPolynomial (Fin 2) F} {e : Fin 2 →₀ ℕ} (he : e ∈ R.support)
    (j : Fin 2) : e j ≤ R.degreeOf j :=
  (degreeOf_le_iff.mp le_rfl) e he

noncomputable def rowP (α : F) (P : MvPolynomial (Fin 2) F) : Polynomial F :=
  aeval (![Polynomial.C α, Polynomial.X] : Fin 2 → Polynomial F) P
noncomputable def colP (β : F) (P : MvPolynomial (Fin 2) F) : Polynomial F :=
  aeval (![Polynomial.X, Polynomial.C β] : Fin 2 → Polynomial F) P

lemma fin2_eq (z : Fin 2 → F) : ![z 0, z 1] = z := by funext i; fin_cases i <;> rfl

lemma eval_aeval_gen (f : Fin 2 → Polynomial F) (t : F) (P : MvPolynomial (Fin 2) F) :
    (aeval f P).eval t = eval (fun i => (f i).eval t) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => rw [map_mul, Polynomial.eval_mul, hp, map_mul, aeval_X, eval_X]

lemma eval_rowP (α y : F) (P : MvPolynomial (Fin 2) F) : (rowP α P).eval y = eval ![α, y] P := by
  unfold rowP; rw [eval_aeval_gen]; congr 2; funext i; fin_cases i <;> simp

lemma eval_colP (β x : F) (P : MvPolynomial (Fin 2) F) : (colP β P).eval x = eval ![x, β] P := by
  unfold colP; rw [eval_aeval_gen]; congr 2; funext i; fin_cases i <;> simp

lemma natDegree_aeval_le (f : Fin 2 → Polynomial F) (j : Fin 2) (hf : f j = Polynomial.X)
    (hc : ∀ l, l ≠ j → (f l).natDegree = 0) (P : MvPolynomial (Fin 2) F) :
    (aeval f P).natDegree ≤ P.degreeOf j := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc ∑ l, ((f l) ^ m l : Polynomial F).natDegree
      ≤ ∑ l, if l = j then m l else 0 := by
        refine Finset.sum_le_sum fun l _ => ?_
        refine (Polynomial.natDegree_pow_le).trans ?_
        split_ifs with h
        · subst h; rw [hf]; have := Polynomial.natDegree_X_le (R := F); nlinarith
        · rw [hc l h]; simp
    _ = m j := by simp
    _ ≤ P.degreeOf j := le_degreeOf_of_mem hm j

lemma natDegree_rowP (α : F) (P : MvPolynomial (Fin 2) F) : (rowP α P).natDegree ≤ P.degreeOf 1 :=
  natDegree_aeval_le _ 1 (by simp) (fun l hl => by fin_cases l <;> simp_all) P

lemma natDegree_colP (β : F) (P : MvPolynomial (Fin 2) F) : (colP β P).natDegree ≤ P.degreeOf 0 :=
  natDegree_aeval_le _ 0 (by simp) (fun l hl => by fin_cases l <;> simp_all) P

lemma rowP_mul (α : F) (P Q : MvPolynomial (Fin 2) F) : rowP α (P * Q) = rowP α P * rowP α Q := by
  unfold rowP; rw [map_mul]
lemma colP_mul (β : F) (P Q : MvPolynomial (Fin 2) F) : colP β (P * Q) = colP β P * colP β Q := by
  unfold colP; rw [map_mul]

lemma card_le_roots (p : Polynomial F) (hp : p ≠ 0) (s : Finset F) (hs : ∀ x ∈ s, p.eval x = 0) :
    s.card ≤ p.natDegree := by
  have h1 : s ⊆ p.roots.toFinset := by
    intro x hx; rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]; exact hs x hx
  exact (Finset.card_le_card h1).trans ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' p))

lemma card_nonzero_ge (p : Polynomial F) (hp : p ≠ 0) (s : Finset F) :
    s.card ≤ (s.filter fun x => p.eval x ≠ 0).card + p.natDegree := by
  have := card_le_roots p hp (s.filter fun x => p.eval x = 0) (fun x hx => (Finset.mem_filter.1 hx).2)
  have h2 := Finset.card_filter_add_card_filter_not (s := s) (fun x => p.eval x ≠ 0)
  simp only [not_not] at h2
  omega

lemma aeval_pure0 (D : MvPolynomial (Fin 2) F) (hD : D.degreeOf 1 = 0) {A : Type} [CommRing A]
    [Algebra F A] (f g : Fin 2 → A) (h0 : f 0 = g 0) : aeval f D = aeval g D := by
  conv_lhs => rw [D.as_sum]
  conv_rhs => rw [D.as_sum]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial]
  congr 1
  refine Finsupp.prod_congr fun i hi => ?_
  have : i = 0 := by
    fin_cases i
    · rfl
    · exfalso; rw [Finsupp.mem_support_iff] at hi
      have := le_degreeOf_of_mem hm 1; exact hi (Nat.le_zero.1 (hD ▸ this))
  subst this; rw [h0]

lemma aeval_pure1 (D : MvPolynomial (Fin 2) F) (hD : D.degreeOf 0 = 0) {A : Type} [CommRing A]
    [Algebra F A] (f g : Fin 2 → A) (h1 : f 1 = g 1) : aeval f D = aeval g D := by
  conv_lhs => rw [D.as_sum]
  conv_rhs => rw [D.as_sum]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial]
  congr 1
  refine Finsupp.prod_congr fun i hi => ?_
  have : i = 1 := by
    fin_cases i
    · exfalso; rw [Finsupp.mem_support_iff] at hi
      have := le_degreeOf_of_mem hm 0; exact hi (Nat.le_zero.1 (hD ▸ this))
    · rfl
  subst this; rw [h1]

lemma aeval_X0_colP (D : MvPolynomial (Fin 2) F) (hD : D.degreeOf 1 = 0) (β : F) :
    Polynomial.aeval (X 0 : MvPolynomial (Fin 2) F) (colP β D) = D := by
  unfold colP
  rw [← AlgHom.comp_apply, comp_aeval]
  conv_rhs => rw [← aeval_X_left_apply D]
  exact aeval_pure0 D hD _ _ (by simp)

lemma aeval_X1_rowP (D : MvPolynomial (Fin 2) F) (hD : D.degreeOf 0 = 0) (α : F) :
    Polynomial.aeval (X 1 : MvPolynomial (Fin 2) F) (rowP α D) = D := by
  unfold rowP
  rw [← AlgHom.comp_apply, comp_aeval]
  conv_rhs => rw [← aeval_X_left_apply D]
  exact aeval_pure1 D hD _ _ (by simp)

end PrivPCP.GD


namespace PrivPCP.Fact33Aux

open MvPolynomial

variable {F : Type} [Field F] {k : ℕ}

lemma degreeOf_monomial_le' (s : Fin k →₀ ℕ) (c : F) (j : Fin k) :
    (monomial s c : MvPolynomial (Fin k) F).degreeOf j ≤ s j := by
  rw [degreeOf_le_iff]
  intro m hm
  have := support_monomial_subset hm
  rw [Finset.mem_singleton] at this
  rw [this]

lemma degreeOf_aeval_X_le (i j : Fin k) (p : Polynomial F) :
    (Polynomial.aeval (X i : MvPolynomial (Fin k) F) p).degreeOf j ≤
      if j = i then p.natDegree else 0 := by
  rw [Polynomial.aeval_eq_sum_range]
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun n hn => ?_)
  rw [MvPolynomial.smul_eq_C_mul]
  refine (degreeOf_C_mul_le _ _ _).trans ?_
  split_ifs with h
  · subst h
    rw [degreeOf_X_self_pow]
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  · rw [degreeOf_X_pow_of_ne _ h]

lemma le_degreeOf_of_mem {R : MvPolynomial (Fin k) F} {e : Fin k →₀ ℕ} (he : e ∈ R.support)
    (j : Fin k) : e j ≤ R.degreeOf j :=
  (degreeOf_le_iff.mp le_rfl) e he

/-- quotient of division by `Z(X_i)` -/
noncomputable def divQ (i : Fin k) (Z : Polynomial F) (R : MvPolynomial (Fin k) F) :
    MvPolynomial (Fin k) F :=
  ∑ e ∈ R.support, monomial (Finsupp.update e i 0) (R.coeff e) *
    Polynomial.aeval (X i) (Polynomial.X ^ (e i) /ₘ Z)

/-- remainder of division by `Z(X_i)` -/
noncomputable def divR (i : Fin k) (Z : Polynomial F) (R : MvPolynomial (Fin k) F) :
    MvPolynomial (Fin k) F :=
  ∑ e ∈ R.support, monomial (Finsupp.update e i 0) (R.coeff e) *
    Polynomial.aeval (X i) (Polynomial.X ^ (e i) %ₘ Z)

lemma div_eq (i : Fin k) (Z : Polynomial F) (R : MvPolynomial (Fin k) F) :
    R = Polynomial.aeval (X i) Z * divQ i Z R + divR i Z R := by
  conv_lhs => rw [as_sum R]
  unfold divQ divR
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  have h1 : (monomial e (R.coeff e) : MvPolynomial (Fin k) F) =
      monomial (Finsupp.update e i 0) (R.coeff e) * X i ^ (e i) := by
    have hs : Finsupp.update e i 0 + Finsupp.single i (e i) = e := by
      ext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Finsupp.update_apply, hj, Finsupp.single_apply, Ne.symm hj]
    rw [X_pow_eq_monomial, monomial_mul, mul_one, hs]
  have h2 : (X i : MvPolynomial (Fin k) F) ^ (e i) =
      Polynomial.aeval (X i) (Polynomial.X ^ (e i) %ₘ Z + Z * (Polynomial.X ^ (e i) /ₘ Z)) := by
    rw [Polynomial.modByMonic_add_div]; simp
  rw [h1, h2, map_add, map_mul]
  ring

lemma divQ_degreeOf (i : Fin k) (Z : Polynomial F) (hZ : Z.Monic) (R : MvPolynomial (Fin k) F)
    (j : Fin k) :
    (divQ i Z R).degreeOf j ≤ if j = i then R.degreeOf i - Z.natDegree else R.degreeOf j := by
  unfold divQ
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun e he => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  refine (add_le_add (degreeOf_monomial_le' _ _ _) (degreeOf_aeval_X_le _ _ _)).trans ?_
  split_ifs with h
  · subst h
    have h0 : (Finsupp.update e j 0) j = 0 := by simp
    rw [h0, zero_add]
    rw [Polynomial.natDegree_divByMonic _ hZ, Polynomial.natDegree_X_pow]
    exact Nat.sub_le_sub_right (le_degreeOf_of_mem he j) _
  · simp only [Finsupp.update_apply, h, if_false, add_zero]
    exact le_degreeOf_of_mem he j

lemma divR_degreeOf_ne (i : Fin k) (Z : Polynomial F) (R : MvPolynomial (Fin k) F)
    (j : Fin k) (hj : j ≠ i) : (divR i Z R).degreeOf j ≤ R.degreeOf j := by
  unfold divR
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun e he => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  refine (add_le_add (degreeOf_monomial_le' _ _ _) (degreeOf_aeval_X_le _ _ _)).trans ?_
  simp only [Finsupp.update_apply, hj, if_false, add_zero]
  exact le_degreeOf_of_mem he j

lemma divR_degreeOf_self (i : Fin k) (Z : Polynomial F) (hZ : Z.Monic) (hZ1 : Z ≠ 1)
    (R : MvPolynomial (Fin k) F) : (divR i Z R).degreeOf i < Z.natDegree := by
  have hpos : 0 < Z.natDegree := by
    rcases Nat.eq_zero_or_pos Z.natDegree with h | h
    · exact absurd (Polynomial.eq_one_of_monic_natDegree_zero hZ h) hZ1
    · exact h
  have : (divR i Z R).degreeOf i ≤ Z.natDegree - 1 := by
    unfold divR
    refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun e he => ?_)
    refine (degreeOf_mul_le _ _ _).trans ?_
    refine (add_le_add (degreeOf_monomial_le' _ _ _) (degreeOf_aeval_X_le _ _ _)).trans ?_
    have h0 : (Finsupp.update e i 0) i = 0 := by simp
    simp only [h0, if_true, zero_add]
    have := Polynomial.natDegree_modByMonic_lt (Polynomial.X ^ (e i)) hZ hZ1
    omega
  omega

end PrivPCP.Fact33Aux


namespace PrivPCP.GD

open Classical MvPolynomial PrivPCP.Fact33Aux

variable {F : Type} [Field F]

lemma eval_aeval_X' (p : Polynomial F) (l : Fin 2) (z : Fin 2 → F) :
    eval z (Polynomial.aeval (X l : MvPolynomial (Fin 2) F) p) = p.eval (z l) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp

noncomputable def lbas (B : Finset F) (β : F) : Polynomial F := Lagrange.basis B id β

lemma eval_lbas (B : Finset F) (β b : F) (hβ : β ∈ B) (hb : b ∈ B) :
    (lbas B β).eval b = if β = b then 1 else 0 := by
  unfold lbas
  split_ifs with h
  · subst h
    have := Lagrange.eval_basis_self (v := (id : F → F)) (Set.injOn_id _) hβ
    simpa using this
  · have := Lagrange.eval_basis_of_ne (v := (id : F → F)) (s := B) h hb
    simpa using this

lemma natDegree_lbas (B : Finset F) (β : F) (hβ : β ∈ B) : (lbas B β).natDegree < B.card := by
  unfold lbas
  rw [Lagrange.natDegree_basis (Set.injOn_id _) hβ]
  have : 0 < B.card := Finset.card_pos.mpr ⟨β, hβ⟩
  omega

noncomputable def interpY (B : Finset F) (G : MvPolynomial (Fin 2) F) : MvPolynomial (Fin 2) F :=
  ∑ β ∈ B, Polynomial.aeval (X 0 : MvPolynomial (Fin 2) F) (colP β G) *
    Polynomial.aeval (X 1 : MvPolynomial (Fin 2) F) (lbas B β)

noncomputable def interpX (A : Finset F) (G : MvPolynomial (Fin 2) F) : MvPolynomial (Fin 2) F :=
  ∑ α ∈ A, Polynomial.aeval (X 0 : MvPolynomial (Fin 2) F) (lbas A α) *
    Polynomial.aeval (X 1 : MvPolynomial (Fin 2) F) (rowP α G)

lemma interpY_deg0 (B : Finset F) (G : MvPolynomial (Fin 2) F) : (interpY B G).degreeOf 0 ≤ G.degreeOf 0 := by
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun β _ => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  have h1 := degreeOf_aeval_X_le (0 : Fin 2) (0 : Fin 2) (colP β G)
  have h2 := degreeOf_aeval_X_le (1 : Fin 2) (0 : Fin 2) (lbas B β)
  rw [if_pos rfl] at h1
  rw [if_neg (show (0 : Fin 2) ≠ 1 by decide)] at h2
  have := natDegree_colP β G
  exact (add_le_add h1 h2).trans (by omega)

lemma interpY_deg1 (B : Finset F) (G : MvPolynomial (Fin 2) F) (hB : 0 < B.card) :
    (interpY B G).degreeOf 1 ≤ B.card - 1 := by
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun β hβ => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  have h1 := degreeOf_aeval_X_le (0 : Fin 2) (1 : Fin 2) (colP β G)
  have h2 := degreeOf_aeval_X_le (1 : Fin 2) (1 : Fin 2) (lbas B β)
  rw [if_neg (show (1 : Fin 2) ≠ 0 by decide)] at h1
  rw [if_pos rfl] at h2
  have := natDegree_lbas B β hβ
  exact (add_le_add h1 h2).trans (by omega)

lemma interpX_deg1 (A : Finset F) (G : MvPolynomial (Fin 2) F) : (interpX A G).degreeOf 1 ≤ G.degreeOf 1 := by
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun α _ => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  have h1 := degreeOf_aeval_X_le (0 : Fin 2) (1 : Fin 2) (lbas A α)
  have h2 := degreeOf_aeval_X_le (1 : Fin 2) (1 : Fin 2) (rowP α G)
  rw [if_neg (show (1 : Fin 2) ≠ 0 by decide)] at h1
  rw [if_pos rfl] at h2
  have := natDegree_rowP α G
  exact (add_le_add h1 h2).trans (by omega)

lemma interpX_deg0 (A : Finset F) (G : MvPolynomial (Fin 2) F) (hA : 0 < A.card) :
    (interpX A G).degreeOf 0 ≤ A.card - 1 := by
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun α hα => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  have h1 := degreeOf_aeval_X_le (0 : Fin 2) (0 : Fin 2) (lbas A α)
  have h2 := degreeOf_aeval_X_le (1 : Fin 2) (0 : Fin 2) (rowP α G)
  rw [if_pos rfl] at h1
  rw [if_neg (show (0 : Fin 2) ≠ 1 by decide)] at h2
  have := natDegree_lbas A α hα
  exact (add_le_add h1 h2).trans (by omega)

lemma eq_on_grid (A B : Finset F) (P Q : MvPolynomial (Fin 2) F)
    (hP0 : P.degreeOf 0 < A.card) (hP1 : P.degreeOf 1 < B.card)
    (hQ0 : Q.degreeOf 0 < A.card) (hQ1 : Q.degreeOf 1 < B.card)
    (h : ∀ a ∈ A, ∀ b ∈ B, eval ![a, b] P = eval ![a, b] Q) : P = Q := by
  rw [← sub_eq_zero]
  apply eq_zero_of_eval_zero_at_prod_finset _ ![A, B]
  · intro l; fin_cases l
    · exact lt_of_le_of_lt (degreeOf_sub_le _ _ _) (max_lt hP0 hQ0)
    · exact lt_of_le_of_lt (degreeOf_sub_le _ _ _) (max_lt hP1 hQ1)
  · intro x hx
    have hx0 : x 0 ∈ A := by simpa using hx 0
    have hx1 : x 1 ∈ B := by simpa using hx 1
    rw [map_sub, ← fin2_eq x, h _ hx0 _ hx1, sub_self]

lemma interpY_eq (A B : Finset F) (G : MvPolynomial (Fin 2) F) (hGA : G.degreeOf 0 < A.card)
    (hGB : G.degreeOf 1 < B.card) : interpY B G = G := by
  have hB : 0 < B.card := by omega
  apply eq_on_grid A B _ _ (lt_of_le_of_lt (interpY_deg0 B G) hGA)
    (lt_of_le_of_lt (interpY_deg1 B G hB) (by omega)) hGA hGB
  intro a _ b hb
  unfold interpY
  rw [map_sum, Finset.sum_eq_single b]
  · rw [map_mul, eval_aeval_X', eval_aeval_X']
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [eval_lbas B _ _ hb hb, if_pos rfl, mul_one, eval_colP]
  · intro β hβ hne
    rw [map_mul, eval_aeval_X', eval_aeval_X']
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [eval_lbas B _ _ hβ hb, if_neg hne, mul_zero]
  · intro h; exact absurd hb h

lemma interpX_eq (A B : Finset F) (G : MvPolynomial (Fin 2) F) (hGA : G.degreeOf 0 < A.card)
    (hGB : G.degreeOf 1 < B.card) : interpX A G = G := by
  have hA : 0 < A.card := by omega
  apply eq_on_grid A B _ _ (lt_of_le_of_lt (interpX_deg0 A G hA) (by omega))
    (lt_of_le_of_lt (interpX_deg1 A G) hGB) hGA hGB
  intro a ha b _
  unfold interpX
  rw [map_sum, Finset.sum_eq_single a]
  · rw [map_mul, eval_aeval_X', eval_aeval_X']
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [eval_lbas A _ _ ha ha, if_pos rfl, one_mul, eval_rowP]
  · intro α hα hne
    rw [map_mul, eval_aeval_X', eval_aeval_X']
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [eval_lbas A _ _ hα ha, if_neg hne, zero_mul]
  · intro h; exact absurd ha h

lemma int_div_col (G D : MvPolynomial (Fin 2) F) (hD : D.degreeOf 1 = 0) (A B : Finset F)
    (hGA : G.degreeOf 0 < A.card) (hGB : G.degreeOf 1 < B.card)
    (h : ∀ β ∈ B, colP β D ∣ colP β G) : D ∣ G := by
  rw [← interpY_eq A B G hGA hGB]
  unfold interpY
  refine Finset.dvd_sum fun β hβ => ?_
  obtain ⟨R, hR⟩ := h β hβ
  rw [hR, map_mul, aeval_X0_colP D hD, mul_assoc]
  exact dvd_mul_right _ _

lemma int_div_row (G V : MvPolynomial (Fin 2) F) (hV : V.degreeOf 0 = 0) (A B : Finset F)
    (hGA : G.degreeOf 0 < A.card) (hGB : G.degreeOf 1 < B.card)
    (h : ∀ α ∈ A, rowP α V ∣ rowP α G) : V ∣ G := by
  rw [← interpX_eq A B G hGA hGB]
  unfold interpX
  refine Finset.dvd_sum fun α hα => ?_
  obtain ⟨R, hR⟩ := h α hα
  rw [hR, map_mul, aeval_X1_rowP V hV, ← mul_assoc, mul_comm _ V, mul_assoc]
  exact dvd_mul_right _ _

end PrivPCP.GD


namespace PrivPCP.GD

open Classical MvPolynomial

variable {F : Type} [Field F]


lemma degreeOf_unit {u : MvPolynomial (Fin 2) F} (hu : IsUnit u) (i : Fin 2) : u.degreeOf i = 0 := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hu0 : u ≠ 0 := hu.ne_zero
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  have := degreeOf_mul_eq (n := i) hu0 hv0
  rw [hv, ← C_1, degreeOf_C] at this
  omega

lemma not_isUnit_lin (α : F) (i : Fin 2) : ¬ IsUnit (X i - C α : MvPolynomial (Fin 2) F) := by
  intro h
  have h2 := h.map (eval (fun _ => α))
  simp at h2

lemma rowP_ne_zero_of_irred (G : MvPolynomial (Fin 2) F) (hG : Irreducible G) (h1 : 0 < G.degreeOf 1)
    (A B : Finset F) (hA : G.degreeOf 0 < A.card) (hB : G.degreeOf 1 < B.card) (α : F) :
    rowP α G ≠ 0 := by
  intro h0
  set D : MvPolynomial (Fin 2) F := X 0 - C α
  have hD1 : D.degreeOf 1 = 0 := by
    have : D.degreeOf 1 ≤ max ((X 0 : MvPolynomial (Fin 2) F).degreeOf 1) ((C α : MvPolynomial (Fin 2) F).degreeOf 1) :=
      degreeOf_sub_le _ _ _
    rw [degreeOf_X, degreeOf_C, if_neg (by decide)] at this
    omega
  have hDG : D ∣ G := by
    apply int_div_col G D hD1 A B hA hB
    intro β _
    have : colP β D = Polynomial.X - Polynomial.C α := by simp [D, colP]
    rw [this, Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, eval_colP, ← eval_rowP, h0,
      Polynomial.eval_zero]
  obtain ⟨u, hu⟩ := hDG
  rcases hG.isUnit_or_isUnit hu with hD | hu'
  · exact not_isUnit_lin α 0 hD
  · have hD0 : D ≠ 0 := by rintro hD; rw [hD, zero_mul] at hu; exact hG.ne_zero hu
    have := degreeOf_mul_eq (n := (1 : Fin 2)) hD0 hu'.ne_zero
    rw [← hu, hD1, degreeOf_unit hu'] at this
    omega

lemma colP_ne_zero_of_irred (G : MvPolynomial (Fin 2) F) (hG : Irreducible G) (h0 : 0 < G.degreeOf 0)
    (A B : Finset F) (hA : G.degreeOf 0 < A.card) (hB : G.degreeOf 1 < B.card) (β : F) :
    colP β G ≠ 0 := by
  intro hc
  set D : MvPolynomial (Fin 2) F := X 1 - C β
  have hD0' : D.degreeOf 0 = 0 := by
    have : D.degreeOf 0 ≤ max ((X 1 : MvPolynomial (Fin 2) F).degreeOf 0) ((C β : MvPolynomial (Fin 2) F).degreeOf 0) :=
      degreeOf_sub_le _ _ _
    rw [degreeOf_X, degreeOf_C, if_neg (by decide)] at this
    omega
  have hDG : D ∣ G := by
    apply int_div_row G D hD0' A B hA hB
    intro α _
    have : rowP α D = Polynomial.X - Polynomial.C β := by simp [D, rowP]
    rw [this, Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, eval_rowP, ← eval_colP, hc,
      Polynomial.eval_zero]
  obtain ⟨u, hu⟩ := hDG
  rcases hG.isUnit_or_isUnit hu with hD | hu'
  · exact not_isUnit_lin β 1 hD
  · have hD0 : D ≠ 0 := by rintro hD; rw [hD, zero_mul] at hu; exact hG.ne_zero hu
    have := degreeOf_mul_eq (n := (0 : Fin 2)) hD0 hu'.ne_zero
    rw [← hu, hD0', degreeOf_unit hu'] at this
    omega

/-- a polynomial without mixed irreducible factors splits as `U(X) V(Y)` -/
lemma pure_split (E : MvPolynomial (Fin 2) F) (hE : E ≠ 0)
    (h : ∀ G, Irreducible G → G ∣ E → G.degreeOf 0 = 0 ∨ G.degreeOf 1 = 0) :
    ∃ U V : MvPolynomial (Fin 2) F, E = U * V ∧ U.degreeOf 1 = 0 ∧ V.degreeOf 0 = 0 := by
  induction E using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hE
  | h₂ x hx => exact ⟨x, 1, (mul_one x).symm, degreeOf_unit hx 1, by rw [← C_1, degreeOf_C]⟩
  | h₃ a p ha hp ih =>
    obtain ⟨U, V, rfl, hU, hV⟩ := ih ha (fun G hG hGa => h G hG (dvd_mul_of_dvd_right hGa p))
    have hp0 : p ≠ 0 := hp.ne_zero
    rcases h p hp.irreducible (dvd_mul_right p _) with h0 | h1
    · refine ⟨U, p * V, by ring, hU, ?_⟩
      have := degreeOf_mul_le (0 : Fin 2) p V
      omega
    · refine ⟨p * U, V, by ring, ?_, hV⟩
      have := degreeOf_mul_le (1 : Fin 2) p U
      omega

def Rows (A : Finset F) (E P : MvPolynomial (Fin 2) F) : Prop :=
  ∀ α ∈ A, ∃ R : Polynomial F, rowP α P = rowP α E * R
def Cols (B : Finset F) (E P : MvPolynomial (Fin 2) F) : Prop :=
  ∀ β ∈ B, ∃ R : Polynomial F, colP β P = colP β E * R

theorem div_main (A B : Finset F) (k1 k2 : ℕ) (τ : ℝ)
    (hτ : ∀ e : ℕ, (e : ℝ) ≤ τ → k1 + e < A.card ∧ k2 + e < B.card)
    (Hmix : ∀ E P : MvPolynomial (Fin 2) F, E ≠ 0 → (max (E.degreeOf 0) (E.degreeOf 1) : ℝ) ≤ τ →
      P.degreeOf 0 < k1 + E.degreeOf 0 → P.degreeOf 1 < k2 + E.degreeOf 1 → Rows A E P →
      Cols B E P → ∀ G, Irreducible G → G ∣ E → 0 < G.degreeOf 0 → 0 < G.degreeOf 1 → G ∣ P) :
    ∀ n, ∀ E P : MvPolynomial (Fin 2) F, E.degreeOf 0 + E.degreeOf 1 = n → E ≠ 0 →
      (max (E.degreeOf 0) (E.degreeOf 1) : ℝ) ≤ τ →
      P.degreeOf 0 < k1 + E.degreeOf 0 → P.degreeOf 1 < k2 + E.degreeOf 1 → Rows A E P →
      Cols B E P → E ∣ P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro E P hn hE hτE hPX hPY hR hC
  have hA0 := (hτ _ (le_trans (le_max_left _ _) hτE)).1
  have hB1 := (hτ _ (le_trans (le_max_right _ _) hτE)).2
  by_cases hP : P = 0
  · rw [hP]; exact dvd_zero E
  by_cases hmix : ∃ G, Irreducible G ∧ G ∣ E ∧ 0 < G.degreeOf 0 ∧ 0 < G.degreeOf 1
  · obtain ⟨G, hG, hGE, hG0, hG1⟩ := hmix
    have hGP := Hmix E P hE hτE hPX hPY hR hC G hG hGE hG0 hG1
    obtain ⟨E', rfl⟩ := hGE
    obtain ⟨P', rfl⟩ := hGP
    have hGn : G ≠ 0 := hG.ne_zero
    have hE' : E' ≠ 0 := right_ne_zero_of_mul hE
    have hP' : P' ≠ 0 := right_ne_zero_of_mul hP
    have dE0 := degreeOf_mul_eq (n := (0 : Fin 2)) hGn hE'
    have dE1 := degreeOf_mul_eq (n := (1 : Fin 2)) hGn hE'
    have dP0 := degreeOf_mul_eq (n := (0 : Fin 2)) hGn hP'
    have dP1 := degreeOf_mul_eq (n := (1 : Fin 2)) hGn hP'
    have hrowG : ∀ α, rowP α G ≠ 0 := rowP_ne_zero_of_irred G hG hG1 A B (by omega) (by omega)
    have hcolG : ∀ β, colP β G ≠ 0 := colP_ne_zero_of_irred G hG hG0 A B (by omega) (by omega)
    have hR' : Rows A E' P' := by
      intro α hα
      obtain ⟨R, hR⟩ := hR α hα
      refine ⟨R, ?_⟩
      rw [rowP_mul, rowP_mul, mul_assoc] at hR
      exact mul_left_cancel₀ (hrowG α) hR
    have hC' : Cols B E' P' := by
      intro β hβ
      obtain ⟨R, hR⟩ := hC β hβ
      refine ⟨R, ?_⟩
      rw [colP_mul, colP_mul, mul_assoc] at hR
      exact mul_left_cancel₀ (hcolG β) hR
    have hτ' : (max (E'.degreeOf 0) (E'.degreeOf 1) : ℝ) ≤ τ := by
      refine le_trans ?_ hτE
      rw [dE0, dE1]
      push_cast
      exact max_le_max (by linarith) (by linarith)
    have := ih (E'.degreeOf 0 + E'.degreeOf 1) (by omega) E' P' rfl hE' hτ' (by omega) (by omega)
      hR' hC'
    exact mul_dvd_mul_left G this
  · push Not at hmix
    obtain ⟨U, V, rfl, hU, hV⟩ := pure_split E hE (fun G hG hGE => by
      by_cases h0 : G.degreeOf 0 = 0
      · exact Or.inl h0
      · right; have := hmix G hG hGE (by omega); omega)
    have hU0 : U ≠ 0 := left_ne_zero_of_mul hE
    have hV0 : V ≠ 0 := right_ne_zero_of_mul hE
    have d0 := degreeOf_mul_eq (n := (0 : Fin 2)) hU0 hV0
    have d1 := degreeOf_mul_eq (n := (1 : Fin 2)) hU0 hV0
    have hVP : V ∣ P := by
      apply int_div_row P V hV A B (by omega) (by omega)
      intro α hα
      obtain ⟨R, hR⟩ := hR α hα
      rw [rowP_mul] at hR
      exact ⟨rowP α U * R, by rw [hR]; ring⟩
    obtain ⟨P1, rfl⟩ := hVP
    have hP1 : P1 ≠ 0 := right_ne_zero_of_mul hP
    have e0 := degreeOf_mul_eq (n := (0 : Fin 2)) hV0 hP1
    have e1 := degreeOf_mul_eq (n := (1 : Fin 2)) hV0 hP1
    set v := rowP 0 V with hvdef
    have hv : v ≠ 0 := by
      intro h0; apply hV0; rw [← aeval_X1_rowP V hV 0, ← hvdef, h0, map_zero]
    set Bg := B.filter fun β => v.eval β ≠ 0 with hBg
    have hcard : B.card ≤ Bg.card + v.natDegree := card_nonzero_ge v hv B
    have hvd : v.natDegree ≤ V.degreeOf 1 := natDegree_rowP 0 V
    have hcolV : ∀ β ∈ Bg, colP β V ≠ 0 := by
      intro β hβ h0
      have := (Finset.mem_filter.1 hβ).2
      apply this
      rw [hvdef, eval_rowP, ← eval_colP, h0, Polynomial.eval_zero]
    have hUP : U ∣ P1 := by
      apply int_div_col P1 U hU A Bg (by omega) (by omega)
      intro β hβ
      obtain ⟨C, hC'⟩ := hC β (Finset.mem_filter.1 hβ).1
      rw [colP_mul, colP_mul] at hC'
      exact ⟨C, mul_left_cancel₀ (hcolV β hβ) (by rw [hC']; ring)⟩
    obtain ⟨Q, rfl⟩ := hUP
    exact ⟨Q, by ring⟩

end PrivPCP.GD


namespace PrivPCP.ZC

open MvPolynomial Classical PrivPCP.GD

variable {K : Type} [Field K]

lemma prod_dvd (p : Polynomial K) (A : Finset K) (h : ∀ a ∈ A, p.eval a = 0) :
    (∏ a ∈ A, (Polynomial.X - Polynomial.C a)) ∣ p := by
  by_cases hp : p = 0
  · rw [hp]; exact dvd_zero _
  rw [Finset.prod_eq_multiset_prod]
  rw [Multiset.prod_X_sub_C_dvd_iff_le_roots hp]
  rw [Multiset.le_iff_subset A.nodup]
  intro a ha
  rw [Polynomial.mem_roots hp]
  exact h a ha

lemma prod_eq_X_pow_sub (A : Finset K) (n : ℕ) (hpos : 0 < n) (hA : A.card = n)
    (hroot : ∀ a ∈ A, a ^ n = 1) :
    (∏ a ∈ A, (Polynomial.X - Polynomial.C a)) = Polynomial.X ^ n - 1 := by
  have hmon : (∏ a ∈ A, (Polynomial.X - Polynomial.C a)).Monic :=
    Polynomial.monic_prod_of_monic _ _ fun a _ => Polynomial.monic_X_sub_C a
  have hmon2 : (Polynomial.X ^ n - 1 : Polynomial K).Monic := Polynomial.monic_X_pow_sub_C 1 hpos.ne'
  have hdvd := prod_dvd (Polynomial.X ^ n - 1 : Polynomial K) A (fun a ha => by simp [hroot a ha])
  have hdeg : (∏ a ∈ A, (Polynomial.X - Polynomial.C a)).natDegree = n := by
    rw [Polynomial.natDegree_prod_of_monic _ _ fun a _ => Polynomial.monic_X_sub_C a]
    simp [hA]
  symm
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon hmon2 hdvd
  have e : (Polynomial.X ^ n - 1 : Polynomial K) = Polynomial.X ^ n - Polynomial.C 1 := by simp
  rw [hdeg, e, Polynomial.natDegree_X_pow_sub_C]

lemma colP_aeval_X0 (p : Polynomial K) (β : K) :
    colP β (Polynomial.aeval (X 0 : MvPolynomial (Fin 2) K) p) = p := by
  unfold colP
  rw [← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X]
  simp

lemma rowP_aeval_X1 (p : Polynomial K) (α : K) :
    rowP α (Polynomial.aeval (X 1 : MvPolynomial (Fin 2) K) p) = p := by
  unfold rowP
  rw [← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X]
  simp

lemma degreeOf1_aeval_X0 (p : Polynomial K) :
    (Polynomial.aeval (X 0 : MvPolynomial (Fin 2) K) p).degreeOf 1 = 0 := by
  have := PrivPCP.Fact33Aux.degreeOf_aeval_X_le (0 : Fin 2) (1 : Fin 2) p
  rw [if_neg (by decide)] at this; omega

lemma degreeOf0_aeval_X1 (p : Polynomial K) :
    (Polynomial.aeval (X 1 : MvPolynomial (Fin 2) K) p).degreeOf 0 = 0 := by
  have := PrivPCP.Fact33Aux.degreeOf_aeval_X_le (1 : Fin 2) (0 : Fin 2) p
  rw [if_neg (by decide)] at this; omega

variable [Infinite K]

lemma big_finset (n : ℕ) : ∃ s : Finset K, n < s.card := by
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq K (n + 1)
  exact ⟨s, by omega⟩

/-- rows divisible on `A` give `P = F H + (∏ (X - a)) K` -/
lemma row_decomp (P F : MvPolynomial (Fin 2) K) (A : Finset K)
    (hrow : ∀ α ∈ A, rowP α F ∣ rowP α P) :
    ∃ H Kf : MvPolynomial (Fin 2) K, P = F * H +
      Polynomial.aeval (X 0 : MvPolynomial (Fin 2) K) (∏ a ∈ A, (Polynomial.X - Polynomial.C a)) * Kf := by
  choose! R hR using hrow
  set H : MvPolynomial (Fin 2) K := ∑ α ∈ A, Polynomial.aeval (X 0 : MvPolynomial (Fin 2) K) (lbas A α) *
    Polynomial.aeval (X 1 : MvPolynomial (Fin 2) K) (R α) with hH
  set G := P - F * H with hG
  have hvan : ∀ β : K, ∀ α ∈ A, (colP β G).eval α = 0 := by
    intro β α hα
    rw [eval_colP, hG, map_sub, map_mul]
    have h1 : eval ![α, β] P = eval ![α, β] F * (R α).eval β := by
      rw [← eval_rowP, ← eval_rowP, hR α hα, Polynomial.eval_mul]
    have h2 : eval ![α, β] H = (R α).eval β := by
      rw [hH, map_sum, Finset.sum_eq_single α]
      · rw [map_mul, eval_aeval_X', eval_aeval_X']
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [eval_lbas A _ _ hα hα, if_pos rfl, one_mul]
      · intro α' hα' hne
        rw [map_mul, eval_aeval_X', eval_aeval_X']
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [eval_lbas A _ _ hα' hα, if_neg hne, zero_mul]
      · intro h; exact absurd hα h
    rw [h1, h2, sub_self]
  obtain ⟨A', hA'⟩ := big_finset (K := K) (G.degreeOf 0)
  obtain ⟨B', hB'⟩ := big_finset (K := K) (G.degreeOf 1)
  have hD := int_div_col G (Polynomial.aeval (X 0 : MvPolynomial (Fin 2) K)
    (∏ a ∈ A, (Polynomial.X - Polynomial.C a))) (degreeOf1_aeval_X0 _) A' B' hA' hB'
    (fun β _ => by rw [colP_aeval_X0]; exact prod_dvd _ A (hvan β))
  obtain ⟨Kf, hKf⟩ := hD
  exact ⟨H, Kf, by rw [← hKf, hG]; ring⟩

lemma col_decomp (P F : MvPolynomial (Fin 2) K) (B : Finset K)
    (hcol : ∀ β ∈ B, colP β F ∣ colP β P) :
    ∃ H Kf : MvPolynomial (Fin 2) K, P = F * H +
      Polynomial.aeval (X 1 : MvPolynomial (Fin 2) K) (∏ b ∈ B, (Polynomial.X - Polynomial.C b)) * Kf := by
  choose! R hR using hcol
  set H : MvPolynomial (Fin 2) K := ∑ β ∈ B, Polynomial.aeval (X 0 : MvPolynomial (Fin 2) K) (R β) *
    Polynomial.aeval (X 1 : MvPolynomial (Fin 2) K) (lbas B β) with hH
  set G := P - F * H with hG
  have hvan : ∀ α : K, ∀ β ∈ B, (rowP α G).eval β = 0 := by
    intro α β hβ
    rw [eval_rowP, hG, map_sub, map_mul]
    have h1 : eval ![α, β] P = eval ![α, β] F * (R β).eval α := by
      rw [← eval_colP, ← eval_colP, hR β hβ, Polynomial.eval_mul]
    have h2 : eval ![α, β] H = (R β).eval α := by
      rw [hH, map_sum, Finset.sum_eq_single β]
      · rw [map_mul, eval_aeval_X', eval_aeval_X']
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [eval_lbas B _ _ hβ hβ, if_pos rfl, mul_one]
      · intro β' hβ' hne
        rw [map_mul, eval_aeval_X', eval_aeval_X']
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [eval_lbas B _ _ hβ' hβ, if_neg hne, mul_zero]
      · intro h; exact absurd hβ h
    rw [h1, h2, sub_self]
  obtain ⟨A', hA'⟩ := big_finset (K := K) (G.degreeOf 0)
  obtain ⟨B', hB'⟩ := big_finset (K := K) (G.degreeOf 1)
  have hD := int_div_row G (Polynomial.aeval (X 1 : MvPolynomial (Fin 2) K)
    (∏ b ∈ B, (Polynomial.X - Polynomial.C b))) (degreeOf0_aeval_X1 _) A' B' hA' hB'
    (fun α _ => by rw [rowP_aeval_X1]; exact prod_dvd _ B (hvan α))
  obtain ⟨Kf, hKf⟩ := hD
  exact ⟨H, Kf, by rw [← hKf, hG]; ring⟩

end PrivPCP.ZC


namespace PrivPCP.ZC

open AlgebraicCurve PrivPCP.PL Classical

variable {K L : Type} [Field K] [Field L] [Algebra K L]

lemma E_le (x : L) (hxt : Transcendental K x) (A : Finset K) (n : ℕ) (hn : 0 < n) (hA : A.card = n)
    (hAr : ∀ a ∈ A, a ^ n = 1)
    (hDT : ∀ f : L, f ≠ 0 → (Function.support fun v : Place K L => v.ord f).Finite ∧
      ∑ᶠ v : Place K L, v.ord f = 0)
    (b : ℕ) (hpole : ∑ᶠ w : Place K L, (-(w.ord x)).toNat = b) (v : Place K L) (hv : 0 ≤ v.ord x) :
    (v.ord (1 - x ^ n)).toNat ≤ b := by
  have hprodK := prod_eq_X_pow_sub A n hn hA hAr
  have hprodL : x ^ n - 1 = ∏ a ∈ A, (x - algebraMap K L a) := by
    have := congrArg (Polynomial.aeval x) hprodK
    simp only [map_prod, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, map_pow, map_one] at this
    exact this.symm
  have hne : ∀ a : K, x - algebraMap K L a ≠ 0 := by
    intro a h; apply hxt
    rw [sub_eq_zero.1 h]; exact isAlgebraic_algebraMap a
  have ha0 : ∀ a ∈ A, a ≠ 0 := by
    intro a ha h; have := hAr a ha; rw [h, zero_pow hn.ne'] at this; exact zero_ne_one this
  have hxO : x ∈ v.toValuationSubring := by
    by_cases hx0 : x = 0
    · rw [hx0]; exact zero_mem _
    · exact (mem_iff_ord v x hx0).2 hv
  have hnn : ∀ a : K, 0 ≤ v.ord (x - algebraMap K L a) :=
    fun a => (mem_iff_ord v _ (hne a)).1 (sub_mem hxO (v.algebraMap_mem' a))
  have hsum : v.ord (1 - x ^ n) = ∑ a ∈ A, v.ord (x - algebraMap K L a) := by
    have e : 1 - x ^ n = -(x ^ n - 1) := by ring
    rw [e, ord_neg, hprodL, ord_prod v A _ (fun a _ => hne a)]
  by_cases hpos : ∃ a0 ∈ A, 0 < v.ord (x - algebraMap K L a0)
  · obtain ⟨a0, ha0A, ha0pos⟩ := hpos
    have hzero : ∀ a ∈ A, a ≠ a0 → v.ord (x - algebraMap K L a) = 0 := by
      intro a haA hne'
      by_contra hc
      have hp : 0 < v.ord (x - algebraMap K L a) := lt_of_le_of_ne (hnn a) (Ne.symm hc)
      have hc0 : algebraMap K L (a0 - a) ≠ 0 := by
        rw [Ne, map_eq_zero_iff _ (algebraMap K L).injective]; exact sub_ne_zero.2 (Ne.symm hne')
      have e : (x - algebraMap K L a) + -(x - algebraMap K L a0) = algebraMap K L (a0 - a) := by
        rw [map_sub]; ring
      have := ord_add_ge v _ _ (hne a) (neg_ne_zero.2 (hne a0)) (by rw [e]; exact hc0)
      rw [e, ord_neg, ord_const v _ (sub_ne_zero.2 (Ne.symm hne'))] at this
      have := min_le_iff.1 this
      omega
    rw [hsum, Finset.sum_eq_single a0 (fun a ha hne' => hzero a ha hne') (fun h => absurd ha0A h)]
    calc (v.ord (x - algebraMap K L a0)).toNat ≤ ∑ᶠ w : Place K L, (-(w.ord (x - algebraMap K L a0))).toNat :=
          zero_le_poles _ (hne a0) hDT v
      _ = ∑ᶠ w : Place K L, (-(w.ord x)).toNat := by
          congr 1; funext w; exact pole_sub_const w x a0 (ha0 a0 ha0A) (hne a0)
      _ = b := hpole
  · push Not at hpos
    have : ∑ a ∈ A, v.ord (x - algebraMap K L a) = 0 :=
      Finset.sum_eq_zero fun a ha => le_antisymm (hpos a ha) (hnn a)
    rw [hsum, this]; simp

end PrivPCP.ZC


namespace PrivPCP.ZC

open AlgebraicCurve PrivPCP.PL Classical MvPolynomial

variable {K L : Type} [Field K] [IsAlgClosed K] [Field L] [Algebra K L]

lemma toNat_min (p r : ℤ) : (min p r).toNat = min p.toNat r.toNat := by
  rcases le_total p r with h | h
  · rw [min_eq_left h, min_eq_left (Int.toNat_le_toNat h)]
  · rw [min_eq_right h, min_eq_right (Int.toNat_le_toNat h)]

lemma pole_one_sub_pow (v : Place K L) (x : L) (hx0 : x ≠ 0) (n : ℕ) (hn : 0 < n)
    (hu : 1 - x ^ n ≠ 0) :
    (-(v.ord (1 - x ^ n))).toNat = n * (-(v.ord x)).toNat := by
  rcases lt_or_ge (v.ord x) 0 with h | h
  · rw [ord_one_sub_pow_neg v x hx0 n hn h]
    have ho : 0 ≤ -(v.ord x) := by omega
    have e : -((n : ℤ) * v.ord x) = ((n * (-(v.ord x)).toNat : ℕ) : ℤ) := by
      push_cast; rw [Int.toNat_of_nonneg ho]; ring
    rw [e, Int.toNat_natCast]
  · have := ord_one_sub_pow_nonneg v x n h hu
    rw [Int.toNat_eq_zero.2 (by omega), Int.toNat_eq_zero.2 (by omega), mul_zero]

theorem zero_count_gen (F P : MvPolynomial (Fin 2) K) (hF : Irreducible F) (hF0 : 0 < F.degreeOf 0)
    (hF1 : 0 < F.degreeOf 1) (hFP : ¬ F ∣ P) (A B : Finset K) (n1 n2 : ℕ) (hn1 : 0 < n1)
    (hn2 : 0 < n2) (hA : A.card = n1) (hB : B.card = n2) (hAr : ∀ a ∈ A, a ^ n1 = 1)
    (hBr : ∀ b ∈ B, b ^ n2 = 1)
    (hrow : ∀ a ∈ A, PrivPCP.GD.rowP a F ∣ PrivPCP.GD.rowP a P)
    (hcol : ∀ b ∈ B, PrivPCP.GD.colP b F ∣ PrivPCP.GD.colP b P)
    (x y : L) (hker : RingHom.ker (aeval (R := K) ![x, y]).toRingHom = Ideal.span {F})
    (hDT : ∀ f : L, f ≠ 0 → (Function.support fun v : Place K L => v.ord f).Finite ∧
      ∑ᶠ v : Place K L, v.ord f = 0)
    (hDTx : ∑ᶠ v : Place K L, (-(v.ord x)).toNat = F.degreeOf 1)
    (hDTy : ∑ᶠ v : Place K L, (-(v.ord y)).toNat = F.degreeOf 0) :
    ((n1 * F.degreeOf 1 + n2 * F.degreeOf 0 : ℕ) : ℕ∞) ≤
      PrivPCP.Supplement.gammaF K L x y n1 n2 +
        ((2 * F.degreeOf 0 * F.degreeOf 1 + P.degreeOf 0 * F.degreeOf 1 +
          P.degreeOf 1 * F.degreeOf 0 : ℕ) : ℕ∞) := by
  set a := F.degreeOf 0 with hadef
  set b := F.degreeOf 1 with hbdef
  set dX := P.degreeOf 0 with hdX
  set dY := P.degreeOf 1 with hdY
  have hxt : Transcendental K x := by
    have := PrivPCP.BP.coord_transcendental x y F hF 0 1 (by decide) hF1 hker; simpa using this
  have hyt : Transcendental K y := by
    have := PrivPCP.BP.coord_transcendental x y F hF 1 0 (by decide) hF0 hker; simpa using this
  have hx0 : x ≠ 0 := fun h => hxt (h ▸ isAlgebraic_zero)
  have hy0 : y ≠ 0 := fun h => hyt (h ▸ isAlgebraic_zero)
  obtain ⟨H1, K1, hP1⟩ := row_decomp P F A hrow
  obtain ⟨H2, K2, hP2⟩ := col_decomp P F B hcol
  rw [prod_eq_X_pow_sub A n1 hn1 hA hAr] at hP1
  rw [prod_eq_X_pow_sub B n2 hn2 hB hBr] at hP2
  have hFxy : aeval ![x, y] F = 0 := by
    have : F ∈ RingHom.ker (aeval (R := K) ![x, y]).toRingHom := by
      rw [hker]; exact Ideal.subset_span rfl
    simpa using this
  set g := aeval ![x, y] P with hgdef
  have hg0 : g ≠ 0 := by
    intro h; apply hFP
    have : P ∈ RingHom.ker (aeval (R := K) ![x, y]).toRingHom := by
      rw [RingHom.mem_ker]; exact h
    rw [hker, Ideal.mem_span_singleton] at this; exact this
  set k1 := aeval ![x, y] K1 with hk1def
  set k2 := aeval ![x, y] K2 with hk2def
  have hg1 : g = -(1 - x ^ n1) * k1 := by
    rw [hgdef, hP1, map_add, map_mul, map_mul, hFxy, zero_mul, zero_add,
      ← Polynomial.aeval_algHom_apply, aeval_X]
    simp only [Matrix.cons_val_zero, map_sub, map_pow, Polynomial.aeval_X, map_one, hk1def]
    ring
  have hg2 : g = -(1 - y ^ n2) * k2 := by
    rw [hgdef, hP2, map_add, map_mul, map_mul, hFxy, zero_mul, zero_add,
      ← Polynomial.aeval_algHom_apply, aeval_X]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, map_sub, map_pow, Polynomial.aeval_X, map_one, hk2def]
    ring
  have hu1 : 1 - x ^ n1 ≠ 0 := by
    intro h; apply hxt
    exact PrivPCP.BP.alg_of_pow x n1 hn1 1 (by rw [map_one]; exact (sub_eq_zero.1 h).symm)
  have hu2 : 1 - y ^ n2 ≠ 0 := by
    intro h; apply hyt
    exact PrivPCP.BP.alg_of_pow y n2 hn2 1 (by rw [map_one]; exact (sub_eq_zero.1 h).symm)
  have hk10 : k1 ≠ 0 := by intro h; apply hg0; rw [hg1, h, mul_zero]
  have hk20 : k2 ≠ 0 := by intro h; apply hg0; rw [hg2, h, mul_zero]
  obtain ⟨hfg, hsg⟩ := hDT g hg0
  obtain ⟨hfu1, hsu1⟩ := hDT _ hu1
  obtain ⟨hfu2, hsu2⟩ := hDT _ hu2
  obtain ⟨hfx, -⟩ := hDT x hx0
  obtain ⟨hfy, -⟩ := hDT y hy0
  set T := hfg.toFinset ∪ hfu1.toFinset ∪ hfu2.toFinset ∪ hfx.toFinset ∪ hfy.toFinset with hT
  have sg : hfg.toFinset ⊆ T := by intro v hv; simp [hT, hv]
  have su1 : hfu1.toFinset ⊆ T := by intro v hv; simp [hT, hv]
  have su2 : hfu2.toFinset ⊆ T := by intro v hv; simp [hT, hv]
  have sx : hfx.toFinset ⊆ T := by intro v hv; simp [hT, hv]
  have sy : hfy.toFinset ⊆ T := by intro v hv; simp [hT, hv]
  have SZ := zeros_eq_poles g hfg hsg T sg
  have SPx := poles_sum x hfx b hDTx T sx
  have SPy := poles_sum y hfy a hDTy T sy
  have SE1 : ∑ v ∈ T, (v.ord (1 - x ^ n1)).toNat = n1 * b := by
    rw [zeros_eq_poles _ hfu1 hsu1 T su1]
    simp_rw [pole_one_sub_pow _ x hx0 n1 hn1 hu1]
    rw [← Finset.mul_sum, SPx]
  have SE2 : ∑ v ∈ T, (v.ord (1 - y ^ n2)).toNat = n2 * a := by
    rw [zeros_eq_poles _ hfu2 hsu2 T su2]
    simp_rw [pole_one_sub_pow _ y hy0 n2 hn2 hu2]
    rw [← Finset.mul_sum, SPy]
  have SPg : ∑ v ∈ T, (-(v.ord g)).toNat ≤ dX * b + dY * a := by
    calc ∑ v ∈ T, (-(v.ord g)).toNat
        ≤ ∑ v ∈ T, (dX * (-(v.ord x)).toNat + dY * (-(v.ord y)).toNat) :=
          Finset.sum_le_sum fun v _ => pole_bound v x y hx0 hy0 P hg0
      _ = dX * b + dY * a := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, SPx, SPy]
  have Cy : (T.filter fun v : Place K L => v.ord y < 0).card ≤ a := by
    calc (T.filter fun v : Place K L => v.ord y < 0).card
        = ∑ v ∈ T.filter (fun v : Place K L => v.ord y < 0), 1 := by simp
      _ ≤ ∑ v ∈ T.filter (fun v : Place K L => v.ord y < 0), (-(v.ord y)).toNat :=
          Finset.sum_le_sum fun v hv => by
            have := (Finset.mem_filter.1 hv).2; omega
      _ ≤ ∑ v ∈ T, (-(v.ord y)).toNat := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = a := SPy
  have Cx : (T.filter fun v : Place K L => v.ord x < 0).card ≤ b := by
    calc (T.filter fun v : Place K L => v.ord x < 0).card
        = ∑ v ∈ T.filter (fun v : Place K L => v.ord x < 0), 1 := by simp
      _ ≤ ∑ v ∈ T.filter (fun v : Place K L => v.ord x < 0), (-(v.ord x)).toNat :=
          Finset.sum_le_sum fun v hv => by
            have := (Finset.mem_filter.1 hv).2; omega
      _ ≤ ∑ v ∈ T, (-(v.ord x)).toNat := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = b := SPx
  -- the local inequality
  set M : Place K L → ℕ := fun v => if v.ord x = 0 ∧ v.ord y = 0 then
    min (v.ord (1 - x ^ n1)).toNat (v.ord (1 - y ^ n2)).toNat else 0 with hM
  have hpt : ∀ v : Place K L, (v.ord (1 - x ^ n1)).toNat + (v.ord (1 - y ^ n2)).toNat ≤
      (v.ord g).toNat + M v + (if v.ord y < 0 then b else 0) + (if v.ord x < 0 then a else 0) := by
    intro v
    have E1neg : v.ord x < 0 → (v.ord (1 - x ^ n1)).toNat = 0 := fun h => by
      rw [ord_one_sub_pow_neg v x hx0 n1 hn1 h]
      apply Int.toNat_eq_zero.2
      have : (0 : ℤ) < n1 := by exact_mod_cast hn1
      nlinarith
    have E2neg : v.ord y < 0 → (v.ord (1 - y ^ n2)).toNat = 0 := fun h => by
      rw [ord_one_sub_pow_neg v y hy0 n2 hn2 h]
      apply Int.toNat_eq_zero.2
      have : (0 : ℤ) < n2 := by exact_mod_cast hn2
      nlinarith
    have E1pos : 0 < v.ord x → (v.ord (1 - x ^ n1)).toNat = 0 := fun h => by
      rw [ord_one_sub_pow_pos v x hx0 n1 hn1 h]; rfl
    have E2pos : 0 < v.ord y → (v.ord (1 - y ^ n2)).toNat = 0 := fun h => by
      rw [ord_one_sub_pow_pos v y hy0 n2 hn2 h]; rfl
    have E1b : 0 ≤ v.ord x → (v.ord (1 - x ^ n1)).toNat ≤ b :=
      E_le x hxt A n1 hn1 hA hAr hDT b hDTx v
    have E2a : 0 ≤ v.ord y → (v.ord (1 - y ^ n2)).toNat ≤ a :=
      E_le y hyt B n2 hn2 hB hBr hDT a hDTy v
    have Zfin : 0 ≤ v.ord x → 0 ≤ v.ord y →
        (v.ord (1 - x ^ n1)).toNat ≤ (v.ord g).toNat ∧ (v.ord (1 - y ^ n2)).toNat ≤ (v.ord g).toNat := by
      intro hx hy
      have hxO : x ∈ v.toValuationSubring := (mem_iff_ord v x hx0).2 hx
      have hyO : y ∈ v.toValuationSubring := (mem_iff_ord v y hy0).2 hy
      have hk1 : 0 ≤ v.ord k1 := (mem_iff_ord v _ hk10).1 (aeval_mem v x y hxO hyO K1)
      have hk2 : 0 ≤ v.ord k2 := (mem_iff_ord v _ hk20).1 (aeval_mem v x y hxO hyO K2)
      have o1 : v.ord g = v.ord (1 - x ^ n1) + v.ord k1 := by
        rw [hg1, v.ord_mul (neg_ne_zero.2 hu1) hk10, ord_neg]
      have o2 : v.ord g = v.ord (1 - y ^ n2) + v.ord k2 := by
        rw [hg2, v.ord_mul (neg_ne_zero.2 hu2) hk20, ord_neg]
      constructor
      · exact Int.toNat_le_toNat (by omega)
      · exact Int.toNat_le_toNat (by omega)
    rcases lt_or_ge (v.ord y) 0 with hy | hy
    · rw [E2neg hy, if_pos hy]
      rcases lt_or_ge (v.ord x) 0 with hx | hx
      · rw [E1neg hx]; omega
      · have := E1b hx; omega
    · rw [if_neg (not_lt.2 hy)]
      rcases lt_or_ge (v.ord x) 0 with hx | hx
      · rw [E1neg hx, if_pos hx]; have := E2a hy; omega
      · rw [if_neg (not_lt.2 hx)]
        obtain ⟨z1, z2⟩ := Zfin hx hy
        by_cases hz : (v.ord (1 - x ^ n1)).toNat = 0 ∨ (v.ord (1 - y ^ n2)).toNat = 0
        · rcases hz with hz | hz <;> omega
        · push Not at hz
          have hx' : v.ord x = 0 := by
            rcases hx.lt_or_eq with h | h
            · exact absurd (E1pos h) hz.1
            · exact h.symm
          have hy' : v.ord y = 0 := by
            rcases hy.lt_or_eq with h | h
            · exact absurd (E2pos h) hz.2
            · exact h.symm
          have : M v = min (v.ord (1 - x ^ n1)).toNat (v.ord (1 - y ^ n2)).toNat := by
            simp only [hM, if_pos (And.intro hx' hy')]
          rw [this]
          omega
  have hsum := Finset.sum_le_sum (s := T) fun v _ => hpt v
  rw [Finset.sum_add_distrib, SE1, SE2, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, SZ] at hsum
  have hIy : ∑ v ∈ T, (if v.ord y < 0 then b else 0) ≤ b * a := by
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
    exact Nat.mul_le_mul_left _ Cy
  have hIx : ∑ v ∈ T, (if v.ord x < 0 then a else 0) ≤ a * b := by
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
    exact Nat.mul_le_mul_left _ Cx
  -- the weighted count
  have hΓ : ((∑ v ∈ T, M v : ℕ) : ℕ∞) = PrivPCP.Supplement.gammaF K L x y n1 n2 := by
    unfold PrivPCP.Supplement.gammaF
    set p : Place K L → Prop := fun v => v.ord x = 0 ∧ v.ord y = 0
    rw [tsum_eq_sum (s := T.subtype p)]
    · rw [Finset.sum_subtype_eq_sum_filter (f := fun v : Place K L =>
          ((min (v.ord (1 - x ^ n1)) (v.ord (1 - y ^ n2))).toNat : ℕ∞)), Finset.sum_filter]
      push_cast
      refine Finset.sum_congr rfl fun v _ => ?_
      simp only [hM, p]
      split_ifs <;> simp [toNat_min]
    · intro w hw
      have hwT : w.1 ∉ T := by
        intro h; apply hw; rw [Finset.mem_subtype]; exact h
      have h1 : w.1.ord (1 - x ^ n1) = 0 := by
        by_contra hc
        exact hwT (su1 (hfu1.mem_toFinset.2 hc))
      have h2 : 0 ≤ w.1.ord (1 - y ^ n2) := ord_one_sub_pow_nonneg _ y n2 (le_of_eq w.2.2.symm) hu2
      rw [h1]
      simp [min_eq_left h2]
  rw [← hΓ]
  have hfinal : n1 * b + n2 * a ≤ (∑ v ∈ T, M v) + (2 * a * b + dX * b + dY * a) := by
    have := SPg
    nlinarith
  calc ((n1 * b + n2 * a : ℕ) : ℕ∞) ≤ (((∑ v ∈ T, M v) + (2 * a * b + dX * b + dY * a) : ℕ) : ℕ∞) := by
        exact_mod_cast hfinal
    _ = _ := by push_cast; ring

end PrivPCP.ZC


open PrivPCP.ZC Classical MvPolynomial in
theorem solution : ∀ (q : ℕ) [Fact q.Prime] (S₁ S₂ : Subgroup (ZMod q)ˣ)
    (F P : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod q))),
    Irreducible F → 0 < F.degreeOf 0 → 0 < F.degreeOf 1 → ¬ F ∣ P →
    (∀ α ∈ S₁,
      MvPolynomial.aeval (![Polynomial.C (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) (α : ZMod q)),
        Polynomial.X] : Fin 2 → Polynomial (AlgebraicClosure (ZMod q))) F ∣
      MvPolynomial.aeval (![Polynomial.C (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) (α : ZMod q)),
        Polynomial.X] : Fin 2 → Polynomial (AlgebraicClosure (ZMod q))) P) →
    (∀ β ∈ S₂,
      MvPolynomial.aeval (![Polynomial.X, Polynomial.C (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))
        (β : ZMod q))] : Fin 2 → Polynomial (AlgebraicClosure (ZMod q))) F ∣
      MvPolynomial.aeval (![Polynomial.X, Polynomial.C (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))
        (β : ZMod q))] : Fin 2 → Polynomial (AlgebraicClosure (ZMod q))) P) →
    ∀ (L : Type) [Field L] [Algebra (AlgebraicClosure (ZMod q)) L] (x y : L),
    RingHom.ker (MvPolynomial.aeval (R := AlgebraicClosure (ZMod q)) ![x, y]).toRingHom =
      Ideal.span {F} →
    IntermediateField.adjoin (AlgebraicClosure (ZMod q)) {x, y} = ⊤ →
    ((Nat.card S₁ * F.degreeOf 1 + Nat.card S₂ * F.degreeOf 0 : ℕ) : ℕ∞) ≤
      PrivPCP.Supplement.gammaF (AlgebraicClosure (ZMod q)) L x y (Nat.card S₁) (Nat.card S₂) +
        ((2 * F.degreeOf 0 * F.degreeOf 1 + P.degreeOf 0 * F.degreeOf 1 + P.degreeOf 1 * F.degreeOf 0 : ℕ) : ℕ∞) := by
  intro q _ S₁ S₂ F P hF hF0 hF1 hFP hrow hcol L _ _ x y hker hadj
  obtain ⟨hDT, hDTx, hDTy⟩ := PrivPCP.lemma_4_13_degree_theory q F hF hF0 hF1 L x y hker hadj
  set ι := algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) with hι
  have hinj : ∀ S : Subgroup (ZMod q)ˣ, Function.Injective (fun u : S => ι ((u : (ZMod q)ˣ) : ZMod q)) := by
    intro S u w h
    exact Subtype.ext (Units.ext (ι.injective h))
  have hpow : ∀ (S : Subgroup (ZMod q)ˣ) (u : S), (ι ((u : (ZMod q)ˣ) : ZMod q)) ^ Nat.card S = 1 := by
    intro S u
    have h1 : u ^ Nat.card S = 1 := pow_card_eq_one'
    have h2 : ((u : (ZMod q)ˣ) : ZMod q) ^ Nat.card S = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, h1]; rfl
    rw [← map_pow, h2, map_one]
  set A : Finset (AlgebraicClosure (ZMod q)) :=
    (Finset.univ : Finset S₁).image (fun u : S₁ => ι ((u : (ZMod q)ˣ) : ZMod q)) with hAdef
  set B : Finset (AlgebraicClosure (ZMod q)) :=
    (Finset.univ : Finset S₂).image (fun u : S₂ => ι ((u : (ZMod q)ˣ) : ZMod q)) with hBdef
  have hA : A.card = Nat.card S₁ := by
    rw [hAdef, Finset.card_image_of_injective _ (hinj S₁), Finset.card_univ, Nat.card_eq_fintype_card]
  have hB : B.card = Nat.card S₂ := by
    rw [hBdef, Finset.card_image_of_injective _ (hinj S₂), Finset.card_univ, Nat.card_eq_fintype_card]
  have hAr : ∀ a ∈ A, a ^ Nat.card S₁ = 1 := by
    intro a ha
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 ha
    exact hpow S₁ u
  have hBr : ∀ b ∈ B, b ^ Nat.card S₂ = 1 := by
    intro b hb
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hb
    exact hpow S₂ u
  have hrow' : ∀ a ∈ A, PrivPCP.GD.rowP a F ∣ PrivPCP.GD.rowP a P := by
    intro a ha
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 ha
    exact hrow u.1 u.2
  have hcol' : ∀ b ∈ B, PrivPCP.GD.colP b F ∣ PrivPCP.GD.colP b P := by
    intro b hb
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hb
    exact hcol u.1 u.2
  exact zero_count_gen F P hF hF0 hF1 hFP A B (Nat.card S₁) (Nat.card S₂) Nat.card_pos Nat.card_pos
    hA hB hAr hBr hrow' hcol' x y hker hDT hDTx hDTy


