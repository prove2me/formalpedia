-- Prove2me | solution 1 for PrivPCP.lemma_4_13_dependent
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:12:59.634773+00:00
-- url     : https://prove2.me/submissions/713af431-4c2d-442e-b11c-7de578535260

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_PrivPCP_Supplement_gammaF
import Theorems.Thm_PrivPCP_places_rational
import Theorems.Thm_PrivPCP_lemma_4_13_binomial_param


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


open PrivPCP.DEP Polynomial Classical in
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
    PrivPCP.Supplement.gammaF (AlgebraicClosure (ZMod q)) L x y (Nat.card S₁) (Nat.card S₂) ≠ ⊤ ∧
    (PrivPCP.Supplement.gammaF (AlgebraicClosure (ZMod q)) L x y (Nat.card S₁) (Nat.card S₂)).toNat ≤
      F.degreeOf 0 * F.degreeOf 1 := by
  intro q _ S₁ S₂ hcop F hF hF0 hF1 haq hbq L _ _ x y hker hadj hdep
  obtain ⟨z, μ, ν, σ, hμ, hν, hσ, hzt, hzadj, hx, hy⟩ :=
    PrivPCP.lemma_4_13_binomial_param q S₁ S₂ hcop F hF hF0 hF1 haq hbq L x y hker hadj hdep
  obtain ⟨res, hinj, hord⟩ := PrivPCP.places_rational (AlgebraicClosure (ZMod q)) L z hzt hzadj
  set a := F.degreeOf 0 with hadef
  set b := F.degreeOf 1 with hbdef
  set n1 := Nat.card S₁ with hn1def
  set n2 := Nat.card S₂ with hn2def
  haveI : CharP (AlgebraicClosure (ZMod q)) q :=
    charP_of_injective_algebraMap (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).injective q
  have hqp : q.Prime := Fact.out
  have hq2 := hqp.two_le
  have hcardq : ∀ S : Subgroup (ZMod q)ˣ, Nat.card S ≤ q - 1 := by
    intro S
    have := Subgroup.card_le_card_group S
    rwa [Nat.card_eq_fintype_card (α := (ZMod q)ˣ), ZMod.card_units] at this
  have hn1 : 0 < n1 := Nat.card_pos
  have hn2 : 0 < n2 := Nat.card_pos
  have hn1q := hcardq S₁
  have hn2q := hcardq S₂
  have hcast : ∀ u w : ℕ, 0 < u → u < q → 0 < w → w < q →
      ((u * w : ℕ) : AlgebraicClosure (ZMod q)) ≠ 0 := by
    intro u w hu huq hw hwq h
    rw [CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod q)) q] at h
    rcases hqp.dvd_mul.1 h with h' | h'
    · have := Nat.le_of_dvd hu h'; omega
    · have := Nat.le_of_dvd hw h'; omega
  have hM1 := hcast b n1 hF1 hbq hn1 (by omega)
  have hM2 := hcast a n2 hF0 haq hn2 (by omega)
  have hz0 : z ≠ 0 := by
    intro h; apply hzt; rw [h]; exact isAlgebraic_zero
  have heval : ∀ P : Polynomial (AlgebraicClosure (ZMod q)), P ≠ 0 → aeval z P ≠ 0 :=
    fun P hP h => hzt ⟨P, hP, h⟩
  set P1 : Polynomial (AlgebraicClosure (ZMod q)) := X ^ (b * n1) - C ((μ ^ n1)⁻¹) with hP1
  set β2 : AlgebraicClosure (ZMod q) := if σ = 1 then (ν ^ n2)⁻¹ else ν ^ n2 with hβ2
  set P2 : Polynomial (AlgebraicClosure (ZMod q)) := X ^ (a * n2) - C β2 with hP2
  have hβ1 : (μ ^ n1)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hμ)
  have hβ2ne : β2 ≠ 0 := by
    rw [hβ2]; split_ifs
    · exact inv_ne_zero (pow_ne_zero _ hν)
    · exact pow_ne_zero _ hν
  have hP1ne : P1 ≠ 0 := X_pow_sub_C_ne_zero (Nat.mul_pos hF1 hn1) _
  have hP2ne : P2 ≠ 0 := X_pow_sub_C_ne_zero (Nat.mul_pos hF0 hn2) _
  -- orders at a place of the index set
  have hordz : ∀ v : AlgebraicCurve.Place (AlgebraicClosure (ZMod q)) L,
      v.ord x = 0 → v.ord z = 0 := by
    intro v hvx
    rw [hx, v.ord_mul (by simpa using hμ) (pow_ne_zero _ hz0), ord_const v μ hμ, ord_npow] at hvx
    have hb0 : (b : ℤ) ≠ 0 := by exact_mod_cast hF1.ne'
    rcases mul_eq_zero.1 (by linarith : (b : ℤ) * v.ord z = 0) with h | h
    · exact absurd h hb0
    · exact h
  have hord1 : ∀ v : AlgebraicCurve.Place (AlgebraicClosure (ZMod q)) L, v.ord z = 0 →
      v.ord (1 - x ^ n1) = (P1.rootMultiplicity (res v) : ℤ) := by
    intro v hvz
    have hm : (algebraMap (AlgebraicClosure (ZMod q)) L μ) ^ n1 ≠ 0 := by simpa using pow_ne_zero n1 hμ
    have e : 1 - x ^ n1 = algebraMap (AlgebraicClosure (ZMod q)) L (-(μ ^ n1)) * aeval z P1 := by
      rw [hx, hP1]
      simp only [map_sub, map_pow, map_neg, map_inv₀, aeval_X, aeval_C, mul_pow, ← pow_mul]
      rw [mul_sub, neg_mul, neg_mul, mul_inv_cancel₀ hm]
      ring
    rw [e, v.ord_mul ((_root_.map_ne_zero _).2 (neg_ne_zero.2 (pow_ne_zero _ hμ))) (heval P1 hP1ne), ord_const v _ (neg_ne_zero.2 (pow_ne_zero _ hμ)),
      hord v hvz.symm.le P1 hP1ne, zero_add]
  have hord2 : ∀ v : AlgebraicCurve.Place (AlgebraicClosure (ZMod q)) L, v.ord z = 0 →
      v.ord (1 - y ^ n2) = (P2.rootMultiplicity (res v) : ℤ) := by
    intro v hvz
    have hm : (algebraMap (AlgebraicClosure (ZMod q)) L ν) ^ n2 ≠ 0 := by simpa using pow_ne_zero n2 hν
    rcases hσ with rfl | rfl
    · have e : 1 - y ^ n2 = algebraMap (AlgebraicClosure (ZMod q)) L (-(ν ^ n2)) * aeval z P2 := by
        rw [hy, hP2, hβ2, if_pos rfl, one_mul, zpow_natCast]
        simp only [map_sub, map_pow, map_neg, map_inv₀, aeval_X, aeval_C, mul_pow, ← pow_mul]
        rw [mul_sub, neg_mul, neg_mul, mul_inv_cancel₀ hm]
        ring
      rw [e, v.ord_mul ((_root_.map_ne_zero _).2 (neg_ne_zero.2 (pow_ne_zero _ hν))) (heval P2 hP2ne), ord_const v _ (neg_ne_zero.2 (pow_ne_zero _ hν)),
        hord v hvz.symm.le P2 hP2ne, zero_add]
    · have hzN : z ^ (-((a * n2 : ℕ) : ℤ)) ≠ 0 := zpow_ne_zero _ hz0
      have e : 1 - y ^ n2 = z ^ (-((a * n2 : ℕ) : ℤ)) * aeval z P2 := by
        rw [hy, hP2, hβ2, if_neg (by norm_num), map_sub, map_pow, aeval_X, aeval_C, map_pow, mul_pow,
          ← zpow_natCast (z ^ _), ← zpow_mul, mul_sub, ← zpow_natCast z (a * n2), ← zpow_add₀ hz0]
        push_cast
        rw [show -((a : ℤ) * n2) + a * n2 = 0 by ring, zpow_zero,
          show (-1 * (a : ℤ) * n2) = -((a : ℤ) * n2) by ring]
        ring
      rw [e, v.ord_mul hzN (heval P2 hP2ne), v.ord_zpow, hvz, mul_zero, zero_add,
        hord v hvz.symm.le P2 hP2ne]
  -- counting
  set R := P1.roots.toFinset ∩ P2.roots.toFinset with hR
  have hRcard : R.card ≤ a * b :=
    (card_common_roots (b * n1) (a * n2) (Nat.mul_pos hF1 hn1) (Nat.mul_pos hF0 hn2) _ _ hβ1 hβ2ne).trans
      (gcd_le_ab a b n1 n2 hF0 hF1 hcop)
  unfold PrivPCP.Supplement.gammaF
  set f : {v : AlgebraicCurve.Place (AlgebraicClosure (ZMod q)) L // v.ord x = 0 ∧ v.ord y = 0} → ℕ∞ :=
    fun v => ((min (v.1.ord (1 - x ^ n1)) (v.1.ord (1 - y ^ n2))).toNat : ℕ∞) with hfdef
  have hfv : ∀ v, f v = ((min (P1.rootMultiplicity (res v.1)) (P2.rootMultiplicity (res v.1)) : ℕ) : ℕ∞) := by
    intro v
    have hvz := hordz v.1 v.2.1
    simp only [hfdef, hord1 v.1 hvz, hord2 v.1 hvz]
    congr 1
    omega
  have hf1 : ∀ v, f v ≤ 1 := by
    intro v; rw [hfv]
    have := rootMult_le_one (b * n1) _ hM1 hβ1 (res v.1)
    exact_mod_cast (min_le_left _ _).trans this
  have hfR : ∀ v, f v ≠ 0 → res v.1 ∈ R := by
    intro v hv
    rw [hfv] at hv
    have h0 : min (P1.rootMultiplicity (res v.1)) (P2.rootMultiplicity (res v.1)) ≠ 0 := by
      intro h; apply hv; rw [h]; rfl
    have hp1 : 0 < P1.rootMultiplicity (res v.1) := by omega
    have hp2 : 0 < P2.rootMultiplicity (res v.1) := by omega
    rw [hR, Finset.mem_inter, Multiset.mem_toFinset, Multiset.mem_toFinset, mem_roots hP1ne, mem_roots hP2ne]
    exact ⟨(rootMultiplicity_pos hP1ne).1 hp1, (rootMultiplicity_pos hP2ne).1 hp2⟩
  have hinjS : Set.InjOn (fun v : {v : AlgebraicCurve.Place (AlgebraicClosure (ZMod q)) L //
      v.ord x = 0 ∧ v.ord y = 0} => res v.1) (Function.support f) := by
    intro v _ w _ h
    exact Subtype.ext (hinj v.1 w.1 (hordz v.1 v.2.1).symm.le (hordz w.1 w.2.1).symm.le h)
  have hfin : (Function.support f).Finite := by
    apply Set.Finite.of_finite_image _ hinjS
    apply (R.finite_toSet).subset
    rintro c ⟨v, hv, rfl⟩
    exact hfR v hv
  rw [tsum_eq_sum (s := hfin.toFinset) (fun v hv => by
    rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hv; exact hv)]
  have hsum : ∑ v ∈ hfin.toFinset, f v ≤ ((a * b : ℕ) : ℕ∞) := by
    calc ∑ v ∈ hfin.toFinset, f v ≤ ∑ v ∈ hfin.toFinset, (1 : ℕ∞) := Finset.sum_le_sum fun v _ => hf1 v
      _ = (hfin.toFinset.card : ℕ∞) := by simp
      _ ≤ (R.card : ℕ∞) := by
          exact_mod_cast Finset.card_le_card_of_injOn (fun v : {v : AlgebraicCurve.Place
            (AlgebraicClosure (ZMod q)) L // v.ord x = 0 ∧ v.ord y = 0} => res v.1)
            (fun v hv => hfR v (by simpa using hv))
            (fun v hv w hw h => hinjS (by simpa using hv) (by simpa using hw) h)
      _ ≤ ((a * b : ℕ) : ℕ∞) := by exact_mod_cast hRcard
  refine ⟨ne_top_of_le_ne_top (ENat.natCast_ne_top _) hsum, ?_⟩
  have := ENat.toNat_le_toNat hsum (ENat.natCast_ne_top _)
  simpa using this


