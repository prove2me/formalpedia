-- Prove2me | solution 1 for PrivPCP.places_rational
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:19:26.255303+00:00
-- url     : https://prove2.me/submissions/1d753898-c63d-42f3-a2ce-bf0a4a5aff7b

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup


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


namespace PrivPCP.PL

open AlgebraicCurve Polynomial

variable {K L : Type} [Field K] [Field L] [Algebra K L]

/-- every element of `K(z)` is a quotient of polynomials in `z` -/
lemma exists_quot (z : L) (hgen : IntermediateField.adjoin K {z} = ⊤) (f : L) :
    ∃ p r : K[X], r ≠ 0 ∧ f = aeval z p / aeval z r := by
  have hf : f ∈ IntermediateField.adjoin K ({z} : Set L) := by rw [hgen]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := IntermediateField.mem_adjoin_iff_div.1 hf
  rw [Algebra.adjoin_singleton_eq_range_aeval] at ha hb
  obtain ⟨p, rfl⟩ := ha
  obtain ⟨r, rfl⟩ := hb
  by_cases hr : r = 0
  · refine ⟨0, 1, one_ne_zero, ?_⟩
    simp [hr]
  · exact ⟨p, r, hr, rfl⟩

variable (v : Place K L) (z : L)

lemma aeval_coe (hzO : z ∈ v.toValuationSubring) (p : K[X]) :
    ((aeval (⟨z, hzO⟩ : v.toValuationSubring) p : v.toValuationSubring) : L) = aeval z p := by
  have := Polynomial.aeval_algebraMap_apply (R := K) L (⟨z, hzO⟩ : v.toValuationSubring) p
  exact this.symm

lemma const_not_mem (c : K) (hc : c ≠ 0) :
    algebraMap K v.toValuationSubring c ∉ IsLocalRing.maximalIdeal v.toValuationSubring := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  exact (isUnit_iff_ne_zero.2 hc).map _

end PrivPCP.PL


namespace PrivPCP.PL

open AlgebraicCurve Polynomial

variable {K L : Type} [Field K] [IsAlgClosed K] [Field L] [Algebra K L]

lemma inv_mem_of_not_mem (v : Place K L) (a : v.toValuationSubring)
    (ha : a ∉ IsLocalRing.maximalIdeal v.toValuationSubring) : (a : L)⁻¹ ∈ v.toValuationSubring := by
  have hu : IsUnit a := by
    by_contra h; exact ha ((IsLocalRing.mem_maximalIdeal _).2 h)
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have hL : (a : L) * (w : L) = 1 := by
    have := congrArg (fun b : v.toValuationSubring => (b : L)) hw
    simpa using this
  have : (w : L) = (a : L)⁻¹ := eq_inv_of_mul_eq_one_right hL
  rw [← this]; exact w.2

lemma exists_center (v : Place K L) (z : L) (hzO : z ∈ v.toValuationSubring)
    (hgen : IntermediateField.adjoin K {z} = ⊤) :
    ∃ c : K, aeval (⟨z, hzO⟩ : v.toValuationSubring) (X - C c) ∈
      IsLocalRing.maximalIdeal v.toValuationSubring := by
  set M := IsLocalRing.maximalIdeal v.toValuationSubring with hM
  have hE1 : ∃ p : K[X], p ≠ 0 ∧ aeval (⟨z, hzO⟩ : v.toValuationSubring) p ∈ M := by
    by_contra h
    push Not at h
    apply v.ne_top'
    rw [eq_top_iff]
    intro f _
    obtain ⟨p, r, hr, rfl⟩ := exists_quot z hgen f
    have hinv := inv_mem_of_not_mem v _ (h r hr)
    rw [aeval_coe] at hinv
    rw [div_eq_mul_inv]
    refine mul_mem ?_ hinv
    have := (aeval (⟨z, hzO⟩ : v.toValuationSubring) p).2
    rwa [aeval_coe] at this
  have key : ∀ n, ∀ p : K[X], p.natDegree = n → p ≠ 0 →
      aeval (⟨z, hzO⟩ : v.toValuationSubring) p ∈ M →
      ∃ c : K, aeval (⟨z, hzO⟩ : v.toValuationSubring) (X - C c) ∈ M := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro p hpn hp0 hpM
    by_cases hdeg : p.degree = 0
    · exfalso
      have hpc := eq_C_of_degree_eq_zero hdeg
      have hc : p.coeff 0 ≠ 0 := by
        intro h0; apply hp0; rw [hpc, h0, C_0]
      rw [hpc, aeval_C] at hpM
      exact const_not_mem v _ hc hpM
    · obtain ⟨c, hc⟩ := IsAlgClosed.exists_root p hdeg
      have hfac : (X - C c) * (p /ₘ (X - C c)) = p := mul_divByMonic_eq_iff_isRoot.2 hc
      rw [← hfac, map_mul] at hpM
      rcases (IsLocalRing.maximalIdeal.isMaximal v.toValuationSubring).isPrime.mem_or_mem hpM with h1 | h2
      · exact ⟨c, h1⟩
      · have hq0 : p /ₘ (X - C c) ≠ 0 := by
          intro h0; apply hp0; rw [← hfac, h0, mul_zero]
        have hnd : (p /ₘ (X - C c)).natDegree < n := by
          rw [natDegree_divByMonic _ (monic_X_sub_C c), natDegree_X_sub_C]
          have : p.natDegree ≠ 0 := by
            intro h0; apply hdeg; rw [degree_eq_natDegree hp0, h0]; rfl
          omega
        exact ih _ hnd _ rfl hq0 h2
  obtain ⟨p, hp0, hpM⟩ := hE1
  exact key _ p rfl hp0 hpM

lemma ord_formula (v : Place K L) (z : L) (hzO : z ∈ v.toValuationSubring)
    (hzt : Transcendental K z) (hgen : IntermediateField.adjoin K {z} = ⊤) (c : K)
    (hc : aeval (⟨z, hzO⟩ : v.toValuationSubring) (X - C c) ∈
      IsLocalRing.maximalIdeal v.toValuationSubring) :
    ∀ p : K[X], p ≠ 0 → v.ord (aeval z p) = (p.rootMultiplicity c : ℤ) := by
  set M := IsLocalRing.maximalIdeal v.toValuationSubring with hM
  have hev : ∀ p : K[X], p ≠ 0 → aeval z p ≠ 0 := fun p hp h => hzt ⟨p, hp, h⟩
  have hE4 : ∀ p0 : K[X], p0.eval c ≠ 0 → v.ord (aeval z p0) = 0 := by
    intro p0 hp0
    rw [← aeval_coe v z hzO]
    apply ord_eq_zero_of_not_mem
    intro hmem
    obtain ⟨g, hg⟩ := X_sub_C_dvd_sub_C_eval (a := c) (p := p0)
    have h1 : aeval (⟨z, hzO⟩ : v.toValuationSubring) (p0 - C (p0.eval c)) ∈ M := by
      rw [hg, map_mul]; exact Ideal.mul_mem_right _ _ hc
    rw [map_sub, aeval_C] at h1
    have h2 : algebraMap K v.toValuationSubring (p0.eval c) ∈ M := by
      have := Ideal.sub_mem _ hmem h1
      rwa [sub_sub_cancel] at this
    exact const_not_mem v _ hp0 h2
  set e := v.ord (aeval z (X - C c)) with he
  have hform : ∀ p : K[X], p ≠ 0 → v.ord (aeval z p) = (p.rootMultiplicity c : ℤ) * e := by
    intro p hp
    obtain ⟨p0, hpeq, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp c
    have hp0c : p0.eval c ≠ 0 := by
      intro h; apply hnd; rw [dvd_iff_isRoot]; exact h
    have hp00 : p0 ≠ 0 := by rintro rfl; simp at hp0c
    have hXc : (X - C c : K[X]) ≠ 0 := X_sub_C_ne_zero c
    conv_lhs => rw [hpeq]
    rw [map_mul, map_pow, v.ord_mul (pow_ne_zero _ (hev _ hXc)) (hev _ hp00), hE4 p0 hp0c,
      add_zero]
    have := v.ord_zpow (aeval z (X - C c)) ((p.rootMultiplicity c : ℕ) : ℤ)
    rw [zpow_natCast] at this
    rw [this]
  -- `e = 1`
  have he1 : 1 ≤ e := by
    rw [he, ← aeval_coe v z hzO]
    apply one_le_ord_of_mem v _ hc
    rw [aeval_coe]; exact hev _ (X_sub_C_ne_zero c)
  have heq : e = 1 := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    have hπ1 := v.ord_coe_irreducible hπ
    have hπ0 : (π : L) ≠ 0 := by simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
    obtain ⟨p, r, hr, hpr⟩ := exists_quot z hgen (π : L)
    have hp : p ≠ 0 := by
      rintro rfl; rw [map_zero, zero_div] at hpr; exact hπ0 hpr
    rw [hpr, ord_div v _ _ (hev p hp) (hev r hr), hform p hp, hform r hr] at hπ1
    have : e * ((p.rootMultiplicity c : ℤ) - r.rootMultiplicity c) = 1 := by linarith
    rcases Int.eq_one_or_neg_one_of_mul_eq_one this with h | h <;> omega
  intro p hp
  rw [hform p hp, heq, mul_one]

end PrivPCP.PL


open PrivPCP.PL AlgebraicCurve Polynomial in
theorem solution : ∀ (K L : Type) [Field K] [IsAlgClosed K] [Field L] [Algebra K L] (z : L),
    Transcendental K z → IntermediateField.adjoin K {z} = ⊤ →
    ∃ res : AlgebraicCurve.Place K L → K,
      (∀ v w : AlgebraicCurve.Place K L, 0 ≤ v.ord z → 0 ≤ w.ord z → res v = res w → v = w) ∧
      ∀ v : AlgebraicCurve.Place K L, 0 ≤ v.ord z → ∀ p : Polynomial K, p ≠ 0 →
        v.ord (Polynomial.aeval z p) = (p.rootMultiplicity (res v) : ℤ) := by
  intro K L _ _ _ _ z hzt hgen
  have hz0 : z ≠ 0 := by
    intro h; apply hzt; rw [h]; exact isAlgebraic_zero
  have hev : ∀ p : K[X], p ≠ 0 → aeval z p ≠ 0 := fun p hp h => hzt ⟨p, hp, h⟩
  have key : ∀ v : Place K L, 0 ≤ v.ord z →
      ∃ c : K, ∀ p : K[X], p ≠ 0 → v.ord (aeval z p) = (p.rootMultiplicity c : ℤ) := by
    intro v hv
    have hzO := (mem_iff_ord v z hz0).2 hv
    obtain ⟨c, hc⟩ := exists_center v z hzO hgen
    exact ⟨c, ord_formula v z hzO hzt hgen c hc⟩
  classical
  let res : Place K L → K := fun v => if h : 0 ≤ v.ord z then Classical.choose (key v h) else 0
  have hres : ∀ v (hv : 0 ≤ v.ord z) (p : K[X]), p ≠ 0 →
      v.ord (aeval z p) = (p.rootMultiplicity (res v) : ℤ) := by
    intro v hv p hp
    simp only [res, dif_pos hv]
    exact Classical.choose_spec (key v hv) p hp
  refine ⟨res, ?_, hres⟩
  intro v w hv hw heq
  have hordeq : ∀ f : L, f ≠ 0 → v.ord f = w.ord f := by
    intro f hf
    obtain ⟨p, r, hr, rfl⟩ := exists_quot z hgen f
    have hp : p ≠ 0 := by rintro rfl; rw [map_zero, zero_div] at hf; exact hf rfl
    rw [ord_div v _ _ (hev p hp) (hev r hr), ord_div w _ _ (hev p hp) (hev r hr),
      hres v hv p hp, hres v hv r hr, hres w hw p hp, hres w hw r hr, heq]
  apply Place.ext
  ext f
  by_cases hf : f = 0
  · subst hf; simp only [zero_mem]
  · rw [mem_iff_ord v f hf, mem_iff_ord w f hf, hordeq f hf]


