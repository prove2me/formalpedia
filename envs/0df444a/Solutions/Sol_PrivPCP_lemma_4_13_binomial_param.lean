-- Prove2me | solution 1 for PrivPCP.lemma_4_13_binomial_param
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:28:38.017873+00:00
-- url     : https://prove2.me/submissions/68563d51-df38-4361-84ac-098805ff6eef

import Mathlib
import Definitions.Def_PrivPCP_gridQ


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


namespace PrivPCP.BP

open MvPolynomial Classical

variable {K L : Type} [Field K] [Field L] [Algebra K L]

lemma degree_upper (F : MvPolynomial (Fin 2) K) (hF : F ≠ 0) (x y z : L)
    (hker : RingHom.ker (MvPolynomial.aeval (R := K) ![x, y]).toRingHom = Ideal.span {F})
    (hz0 : z ≠ 0) (μ ν : K) (hμ : μ ≠ 0) (hν : ν ≠ 0) (β : ℕ) (e : ℤ) (hβ : 0 < β) (he : e ≠ 0)
    (hx : x = algebraMap K L μ * z ^ β) (hy : y = algebraMap K L ν * z ^ e) :
    F.degreeOf 0 ≤ e.natAbs ∧ F.degreeOf 1 ≤ β := by
  set α := e.natAbs with hαdef
  have hα0 : 0 < α := Int.natAbs_pos.2 he
  obtain ⟨G, hGker, hG0, hGd0, hGd1⟩ : ∃ G : MvPolynomial (Fin 2) K,
      aeval ![x, y] G = 0 ∧ G ≠ 0 ∧ G.degreeOf 0 ≤ α ∧ G.degreeOf 1 ≤ β := by
    have hs : (Finsupp.single 0 α : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 β := by
      intro h; have := congrArg (fun f => f 0) h; simp at this; omega
    rcases lt_or_gt_of_ne he with hneg | hpos
    · have heα : e = -(α : ℤ) := by omega
      refine ⟨monomial (Finsupp.single 0 α + Finsupp.single 1 β) 1 - C (μ ^ α * ν ^ β), ?_, ?_, ?_, ?_⟩
      · have hm : (monomial (Finsupp.single 0 α + Finsupp.single 1 β) (1 : K) : MvPolynomial (Fin 2) K) =
            X 0 ^ α * X 1 ^ β := by
          rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]
        rw [hm, map_sub, map_mul, map_pow, map_pow, aeval_X, aeval_X, aeval_C]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [hx, hy, mul_pow, mul_pow, ← zpow_natCast (z ^ e), ← zpow_mul, ← pow_mul, heα, map_mul,
          map_pow, map_pow]
        have : z ^ (β * α) * z ^ (-(α : ℤ) * (β : ℤ)) = 1 := by
          rw [← zpow_natCast, ← zpow_add₀ hz0]; push_cast; ring_nf; rw [zpow_zero]
        calc _ = (algebraMap K L μ ^ α * algebraMap K L ν ^ β) * (z ^ (β * α) * z ^ (-(α : ℤ) * (β : ℤ))) -
              algebraMap K L μ ^ α * algebraMap K L ν ^ β := by ring
          _ = 0 := by rw [this, mul_one, sub_self]
      · intro h0
        have := congrArg (coeff (Finsupp.single 0 α + Finsupp.single 1 β)) h0
        rw [coeff_sub, coeff_monomial, if_pos rfl, coeff_C, if_neg, coeff_zero, sub_zero] at this
        · exact one_ne_zero this
        · intro h; have := congrArg (fun f => f 0) h; simp at this; omega
      · refine (degreeOf_sub_le _ _ _).trans (max_le ?_ (by rw [degreeOf_C]; omega))
        refine (PrivPCP.Fact33Aux.degreeOf_monomial_le' _ _ _).trans ?_
        simp
      · refine (degreeOf_sub_le _ _ _).trans (max_le ?_ (by rw [degreeOf_C]; omega))
        refine (PrivPCP.Fact33Aux.degreeOf_monomial_le' _ _ _).trans ?_
        simp
    · have heα : e = (α : ℤ) := by omega
      refine ⟨monomial (Finsupp.single 0 α) (ν ^ β) - monomial (Finsupp.single 1 β) (μ ^ α), ?_, ?_, ?_, ?_⟩
      · have h1 : (monomial (Finsupp.single 0 α) (ν ^ β) : MvPolynomial (Fin 2) K) = C (ν ^ β) * X 0 ^ α := by
          rw [X_pow_eq_monomial, C_mul_monomial, mul_one]
        have h2 : (monomial (Finsupp.single 1 β) (μ ^ α) : MvPolynomial (Fin 2) K) = C (μ ^ α) * X 1 ^ β := by
          rw [X_pow_eq_monomial, C_mul_monomial, mul_one]
        rw [h1, h2]
        simp only [map_sub, map_mul, map_pow, aeval_X, aeval_C, Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [hx, hy, heα, zpow_natCast]
        ring
      · intro h0
        have := congrArg (coeff (Finsupp.single 0 α)) h0
        rw [coeff_sub, coeff_monomial, if_pos rfl, coeff_monomial, if_neg hs.symm, coeff_zero,
          sub_zero] at this
        exact pow_ne_zero _ hν this
      · refine (degreeOf_sub_le _ _ _).trans (max_le ?_ ?_) <;>
          refine (PrivPCP.Fact33Aux.degreeOf_monomial_le' _ _ _).trans ?_ <;> simp
      · refine (degreeOf_sub_le _ _ _).trans (max_le ?_ ?_) <;>
          refine (PrivPCP.Fact33Aux.degreeOf_monomial_le' _ _ _).trans ?_ <;> simp
  have hmem : G ∈ RingHom.ker (MvPolynomial.aeval (R := K) ![x, y]).toRingHom := by
    rw [RingHom.mem_ker]; exact hGker
  rw [hker, Ideal.mem_span_singleton] at hmem
  obtain ⟨H, hH⟩ := hmem
  have hH0 : H ≠ 0 := by rintro rfl; rw [mul_zero] at hH; exact hG0 hH
  have d0 := degreeOf_mul_eq (n := (0 : Fin 2)) hF hH0
  have d1 := degreeOf_mul_eq (n := (1 : Fin 2)) hF hH0
  rw [← hH] at d0 d1
  omega

end PrivPCP.BP


namespace PrivPCP.BP

variable {K L : Type} [Field K] [IsAlgClosed K] [Field L] [Algebra K L]

lemma alg_of_zpow (u : L) (hu : u ≠ 0) (A : ℤ) (hA : A ≠ 0) (c : K) (h : u ^ A = algebraMap K L c) :
    IsAlgebraic K u := by
  rcases lt_or_gt_of_ne hA with hneg | hpos
  · apply alg_of_pow u (-A).toNat (by omega) c⁻¹
    rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), zpow_neg, h, map_inv₀]
  · apply alg_of_pow u A.toNat (by omega) c
    rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), h]

end PrivPCP.BP

open PrivPCP.BP MvPolynomial in
theorem solution : ∀ (q : ℕ) [Fact q.Prime] (S₁ S₂ : Subgroup (ZMod q)ˣ),
    Nat.Coprime (Nat.card S₁) (Nat.card S₂) →
    ∀ F : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod q)),
    Irreducible F → 0 < F.degreeOf 0 → 0 < F.degreeOf 1 → F.degreeOf 0 < q → F.degreeOf 1 < q →
    ∀ (L : Type) [Field L] [Algebra (AlgebraicClosure (ZMod q)) L] (x y : L),
    RingHom.ker (MvPolynomial.aeval (R := AlgebraicClosure (ZMod q)) ![x, y]).toRingHom =
      Ideal.span {F} →
    IntermediateField.adjoin (AlgebraicClosure (ZMod q)) {x, y} = ⊤ →
    (∃ r s : ℤ, ¬ (r = 0 ∧ s = 0) ∧ ∃ c : AlgebraicClosure (ZMod q), c ≠ 0 ∧
      (x ^ Nat.card S₁) ^ r * (y ^ Nat.card S₂) ^ s =
        algebraMap (AlgebraicClosure (ZMod q)) L c) →
    ∃ (z : L) (μ ν : AlgebraicClosure (ZMod q)) (σ : ℤ), μ ≠ 0 ∧ ν ≠ 0 ∧ (σ = 1 ∨ σ = -1) ∧
      Transcendental (AlgebraicClosure (ZMod q)) z ∧
      IntermediateField.adjoin (AlgebraicClosure (ZMod q)) {z} = ⊤ ∧
      x = algebraMap (AlgebraicClosure (ZMod q)) L μ * z ^ F.degreeOf 1 ∧
      y = algebraMap (AlgebraicClosure (ZMod q)) L ν * z ^ (σ * (F.degreeOf 0 : ℤ)) := by
  intro q _ S₁ S₂ hcop F hF hF0 hF1 haq hbq L _ _ x y hker hadj hdep
  obtain ⟨r, s, hrs, c, hc0, hrel⟩ := hdep
  have hxt : Transcendental (AlgebraicClosure (ZMod q)) x := by
    have := coord_transcendental x y F hF 0 1 (by decide) hF1 hker; simpa using this
  have hyt : Transcendental (AlgebraicClosure (ZMod q)) y := by
    have := coord_transcendental x y F hF 1 0 (by decide) hF0 hker; simpa using this
  have hx0 : x ≠ 0 := by intro h; apply hxt; rw [h]; exact isAlgebraic_zero
  have hy0 : y ≠ 0 := by intro h; apply hyt; rw [h]; exact isAlgebraic_zero
  have hn1 : 0 < Nat.card S₁ := Nat.card_pos
  have hn2 : 0 < Nat.card S₂ := Nat.card_pos
  rw [← zpow_natCast x, ← zpow_natCast y, ← zpow_mul, ← zpow_mul] at hrel
  set A : ℤ := (Nat.card S₁ : ℤ) * r with hAdef
  set B : ℤ := (Nat.card S₂ : ℤ) * s with hBdef
  have hA : A ≠ 0 := by
    intro hA0
    have hr : r = 0 := by
      rcases mul_eq_zero.1 hA0 with h | h
      · exact absurd h (by exact_mod_cast hn1.ne')
      · exact h
    have hs : s ≠ 0 := fun h => hrs ⟨hr, h⟩
    rw [hA0, zpow_zero, one_mul] at hrel
    exact hyt (alg_of_zpow y hy0 B (mul_ne_zero (by exact_mod_cast hn2.ne') hs) c hrel)
  have hB : B ≠ 0 := by
    intro hB0
    rw [hB0, zpow_zero, mul_one] at hrel
    exact hxt (alg_of_zpow x hx0 A hA c hrel)
  obtain ⟨z, μ, ν, β, e, hβ, he, hcopβ, hμ, hν, hz0, hx, hy⟩ :=
    param_of_relation x y hx0 hy0 A B hA hB c hrel
  have hzt : Transcendental (AlgebraicClosure (ZMod q)) z := by
    intro halg
    obtain ⟨k, hk⟩ := alg_in_range z halg
    apply hxt
    rw [hx, hk, ← map_pow, ← map_mul]
    exact isAlgebraic_algebraMap _
  have hFxy : aeval ![x, y] F = 0 := by
    have : F ∈ RingHom.ker (aeval (R := AlgebraicClosure (ZMod q)) ![x, y]).toRingHom := by
      rw [hker]; exact Ideal.subset_span rfl
    simpa using this
  have hlow := degree_lower F hF.ne_zero z hzt hz0 μ ν hμ hν β e hβ he hcopβ (by rw [← hx, ← hy]; exact hFxy)
  have hup := degree_upper F hF.ne_zero x y z hker hz0 μ ν hμ hν β e hβ he hx hy
  have hd0 : F.degreeOf 0 = e.natAbs := le_antisymm hup.1 hlow.1
  have hd1 : F.degreeOf 1 = β := le_antisymm hup.2 hlow.2
  refine ⟨z, μ, ν, Int.sign e, hμ, hν, ?_, hzt, ?_, ?_, ?_⟩
  · rcases lt_or_gt_of_ne he with h | h
    · right; exact Int.sign_eq_neg_one_of_neg h
    · left; exact Int.sign_eq_one_of_pos h
  · rw [eq_top_iff, ← hadj, IntermediateField.adjoin_le_iff]
    intro w hw
    have hzmem : z ∈ IntermediateField.adjoin (AlgebraicClosure (ZMod q)) ({z} : Set L) :=
      IntermediateField.subset_adjoin _ _ (Set.mem_singleton z)
    rcases hw with rfl | rfl
    · rw [hx]
      exact mul_mem (IntermediateField.algebraMap_mem _ _) (pow_mem hzmem _)
    · rw [hy]
      exact mul_mem (IntermediateField.algebraMap_mem _ _) (zpow_mem hzmem _)
  · rw [hd1]; exact hx
  · rw [hd0, Int.sign_mul_natAbs]; exact hy


