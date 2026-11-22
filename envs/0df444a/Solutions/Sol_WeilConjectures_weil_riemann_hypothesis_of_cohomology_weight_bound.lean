-- Prove2me | solution 1 for WeilConjectures.weil_riemann_hypothesis_of_cohomology_weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T07:41:45.441711+00:00
-- url     : https://prove2.me/submissions/62bfaba2-1c82-4fba-9f4d-a59796118712

import Mathlib
import Definitions.Def_WeilConjectures_zetaFunction
import Theorems.Thm_WeilConjectures_zetaOfCounts_mul_prod_charpolyRev_of_trace_formula
import Theorems.Thm_Matrix_charpolyRev_of_transpose_mul_mul_eq_smul

namespace WCAux

open Matrix

section Sig

variable {R : Type*} [CommRing R]

/-- `σ_a(p) = p^rev(a X)`, where `p^rev` is the reversed polynomial. -/
noncomputable def sig (a : R) (p : Polynomial R) : Polynomial R :=
  p.reverse.comp (Polynomial.C a * Polynomial.X)

theorem sig_mul [NoZeroDivisors R] (a : R) (p q : Polynomial R) :
    sig a (p * q) = sig a p * sig a q := by
  unfold sig
  rw [Polynomial.reverse_mul_of_domain, Polynomial.mul_comp]

theorem sig_one (a : R) : sig a (1 : Polynomial R) = 1 := by
  unfold sig
  rw [← Polynomial.C_1, Polynomial.reverse_C, Polynomial.C_comp]

theorem sig_C_mul [NoZeroDivisors R] (a c : R) (p : Polynomial R) :
    sig a (Polynomial.C c * p) = Polynomial.C c * sig a p := by
  rw [sig_mul]
  congr 1
  unfold sig
  rw [Polynomial.reverse_C, Polynomial.C_comp]

theorem sig_prod [NoZeroDivisors R] (a : R) {ι : Type*} (s : Finset ι) (f : ι → Polynomial R) :
    sig a (∏ i ∈ s, f i) = ∏ i ∈ s, sig a (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sig_one]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, sig_mul, ih]

theorem coeff_zero_sig (a : R) (p : Polynomial R) : (sig a p).coeff 0 = p.leadingCoeff := by
  unfold sig
  rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_X, mul_zero, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_zero_reverse]

theorem reverse_map_of_injective {S : Type*} [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) (p : Polynomial R) :
    (p.map φ).reverse = p.reverse.map φ := by
  unfold Polynomial.reverse
  rw [Polynomial.natDegree_map_eq_of_injective hφ, Polynomial.reflect_map]

theorem sig_map {S : Type*} [CommRing S] (φ : R →+* S) (hφ : Function.Injective φ) (a : R)
    (p : Polynomial R) : (sig a p).map φ = sig (φ a) (p.map φ) := by
  unfold sig
  rw [Polynomial.map_comp, reverse_map_of_injective φ hφ, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_X]

theorem reverse_reverse_of_coeff_zero_ne_zero (f : Polynomial R) (h : f.coeff 0 ≠ 0) :
    f.reverse.reverse = f := by
  have hnt : f.natTrailingDegree = 0 :=
    Nat.le_zero.mp (Polynomial.natTrailingDegree_le_of_ne_zero h)
  have hdeg : f.reverse.natDegree = f.natDegree := by
    rw [Polynomial.reverse_natDegree, hnt, Nat.sub_zero]
  ext k
  rw [Polynomial.coeff_reverse, hdeg, Polynomial.coeff_reverse, Polynomial.revAt_invol]

end Sig

theorem coe_prod' {K : Type*} [CommSemiring K] {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial K) :
    ((∏ i ∈ s, f i : Polynomial K) : PowerSeries K) =
      ∏ i ∈ s, ((f i : Polynomial K) : PowerSeries K) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, Polynomial.coe_mul, ih]

theorem reindex_even (n : ℕ) {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ∏ i ∈ (Finset.range (2 * n + 1)).filter Even, f (2 * n - i) =
      ∏ i ∈ (Finset.range (2 * n + 1)).filter Even, f i := by
  refine Finset.prod_nbij' (fun i => 2 * n - i) (fun i => 2 * n - i) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range, Nat.even_iff] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range, Nat.even_iff] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    show 2 * n - (2 * n - a) = a
    omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    show 2 * n - (2 * n - a) = a
    omega
  · intro a _
    rfl

theorem reindex_odd (n : ℕ) {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd, f (2 * n - i) =
      ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd, f i := by
  refine Finset.prod_nbij' (fun i => 2 * n - i) (fun i => 2 * n - i) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range, Nat.odd_iff] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range, Nat.odd_iff] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    show 2 * n - (2 * n - a) = a
    omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    show 2 * n - (2 * n - a) = a
    omega
  · intro a _
    rfl

/-- Poincaré duality for the reversed characteristic polynomials: `σ(P_i) = u_i P_{2n-i}`. -/
theorem sig_charpolyRev_of_pairing {K : Type*} [Field K] (n : ℕ) (a : K) (ha0 : a ≠ 0)
    (d : ℕ → ℕ) (Φ : (i : ℕ) → Matrix (Fin (d i)) (Fin (d i)) K)
    (hPD : ∀ i ≤ 2 * n, ∃ (G : Matrix (Fin (d i)) (Fin (d (2 * n - i))) K)
        (H : Matrix (Fin (d (2 * n - i))) (Fin (d i)) K),
        G * H = 1 ∧ H * G = 1 ∧ (Φ i).transpose * G * Φ (2 * n - i) = a • G)
    (i : ℕ) (hi : i ≤ 2 * n) :
    ((Φ i).charpolyRev).reverse = (Φ i).charpoly ∧
    ∃ u : K, u ≠ 0 ∧ sig a ((Φ i).charpolyRev) = Polynomial.C u * (Φ (2 * n - i)).charpolyRev := by
  obtain ⟨G, H, hGH, hHG, hG⟩ := hPD i hi
  obtain ⟨hdet, -, hB⟩ :=
    Matrix.charpolyRev_of_transpose_mul_mul_eq_smul (Φ i) (Φ (2 * n - i)) G H hGH hHG a ha0 hG
  have hc0 : (Φ i).charpoly.coeff 0 ≠ 0 := by
    intro h0
    apply hdet
    rw [Matrix.det_eq_sign_charpoly_coeff, h0, mul_zero]
  have hrev : ((Φ i).charpolyRev).reverse = (Φ i).charpoly := by
    rw [← Matrix.reverse_charpoly]
    exact reverse_reverse_of_coeff_zero_ne_zero _ hc0
  have hs : sig a ((Φ i).charpolyRev) =
      (Φ i).charpoly.comp (Polynomial.C a * Polynomial.X) := by
    unfold sig
    rw [hrev]
  refine ⟨hrev, (-1) ^ Fintype.card (Fin (d i)) * (Φ i).det,
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hdet, ?_⟩
  rw [hs, Polynomial.C_mul, mul_assoc, hB, ← mul_assoc, Polynomial.C_pow, Polynomial.C_neg,
    Polynomial.C_1, ← mul_pow]
  simp

/-- **Functional equation from a trace formula and Poincaré duality** (root-free form). -/
theorem functional_equation_of_trace_formula_of_poincare_duality
    (N : ℕ → ℕ) (n q : ℕ) (hq : 0 < q) {K : Type*} [Field K] [CharZero K] (d : ℕ → ℕ)
    (Φ : (i : ℕ) → Matrix (Fin (d i)) (Fin (d i)) K)
    (htr : ∀ m : ℕ, 0 < m →
      (N m : K) = ∑ i ∈ Finset.range (2 * n + 1), (-1 : K) ^ i * ((Φ i) ^ m).trace)
    (hPD : ∀ i ≤ 2 * n, ∃ (G : Matrix (Fin (d i)) (Fin (d (2 * n - i))) K)
        (H : Matrix (Fin (d (2 * n - i))) (Fin (d i)) K),
        G * H = 1 ∧ H * G = 1 ∧ (Φ i).transpose * G * Φ (2 * n - i) = (q : K) ^ n • G)
    (A B : Polynomial ℤ) (hA : A.coeff 0 = 1) (hB : B.coeff 0 = 1)
    (hZ : WeilConjectures.zetaOfCounts N *
        ((B.map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) =
      ((A.map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ)) :
    ∃ c : ℚ, c ≠ 0 ∧
      ((A.reverse.comp (Polynomial.C ((q : ℤ) ^ n) * Polynomial.X)) * B).map
          (Int.castRingHom ℚ) =
        Polynomial.C c * (A * (B.reverse.comp (Polynomial.C ((q : ℤ) ^ n) * Polynomial.X))).map
          (Int.castRingHom ℚ) := by
  have ha0 : ((q : K) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hq.ne')
  have hle : ∀ i ∈ Finset.range (2 * n + 1), i ≤ 2 * n :=
    fun i hi => Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hF1 : ∀ i, i ≤ 2 * n → ∃ u : K, u ≠ 0 ∧
      sig ((q : K) ^ n) ((Φ i).charpolyRev) = Polynomial.C u * (Φ (2 * n - i)).charpolyRev :=
    fun i hi => (sig_charpolyRev_of_pairing n ((q : K) ^ n) ha0 d Φ hPD i hi).2
  choose! u hu0 hu using hF1
  -- the even and odd products
  obtain ⟨E, hE⟩ : ∃ E : Polynomial K,
      E = ∏ i ∈ (Finset.range (2 * n + 1)).filter Even, (Φ i).charpolyRev := ⟨_, rfl⟩
  obtain ⟨O, hO⟩ : ∃ O : Polynomial K,
      O = ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd, (Φ i).charpolyRev := ⟨_, rfl⟩
  obtain ⟨e, he'⟩ : ∃ e : K, e = ∏ i ∈ (Finset.range (2 * n + 1)).filter Even, u i := ⟨_, rfl⟩
  obtain ⟨o, ho'⟩ : ∃ o : K, o = ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd, u i := ⟨_, rfl⟩
  have he : e ≠ 0 := by
    rw [he']
    exact Finset.prod_ne_zero_iff.mpr (fun i hi => hu0 i (hle i (Finset.mem_filter.mp hi).1))
  have ho : o ≠ 0 := by
    rw [ho']
    exact Finset.prod_ne_zero_iff.mpr (fun i hi => hu0 i (hle i (Finset.mem_filter.mp hi).1))
  have hsE : sig ((q : K) ^ n) E = Polynomial.C e * E := by
    rw [hE, he', sig_prod,
      Finset.prod_congr rfl (fun i hi => hu i (hle i (Finset.mem_filter.mp hi).1)),
      Finset.prod_mul_distrib, reindex_even n (fun i => (Φ i).charpolyRev), map_prod]
  have hsO : sig ((q : K) ^ n) O = Polynomial.C o * O := by
    rw [hO, ho', sig_prod,
      Finset.prod_congr rfl (fun i hi => hu i (hle i (Finset.mem_filter.mp hi).1)),
      Finset.prod_mul_distrib, reindex_odd n (fun i => (Φ i).charpolyRev), map_prod]
  have hPne : ∀ i, (Φ i).charpolyRev ≠ 0 := by
    intro i h
    have h1 : Polynomial.eval 0 (Φ i).charpolyRev = 1 := by simp
    rw [h, Polynomial.eval_zero] at h1
    exact zero_ne_one h1
  have hE0 : E ≠ 0 := by
    rw [hE]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hPne i)
  -- the zeta series over `K`
  have hcomp : (algebraMap ℚ K).comp (Int.castRingHom ℚ) = Int.castRingHom K :=
    RingHom.ext_int _ _
  have h1 : PowerSeries.map (algebraMap ℚ K) (WeilConjectures.zetaOfCounts N) *
      ((B.map (Int.castRingHom K) : Polynomial K) : PowerSeries K) =
      ((A.map (Int.castRingHom K) : Polynomial K) : PowerSeries K) := by
    have h := congrArg (PowerSeries.map (algebraMap ℚ K)) hZ
    rw [map_mul, ← Polynomial.polynomial_map_coe, ← Polynomial.polynomial_map_coe,
      Polynomial.map_map, Polynomial.map_map, hcomp] at h
    exact h
  have hZK := WeilConjectures.zetaOfCounts_mul_prod_charpolyRev_of_trace_formula N (Finset.range (2 * n + 1)) d Φ htr
  have hcoeE : ((E : Polynomial K) : PowerSeries K) =
      ∏ i ∈ (Finset.range (2 * n + 1)).filter Even,
        (((Φ i).charpolyRev : Polynomial K) : PowerSeries K) := by
    rw [hE]
    exact coe_prod' _ _
  have hcoeO : ((O : Polynomial K) : PowerSeries K) =
      ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd,
        (((Φ i).charpolyRev : Polynomial K) : PowerSeries K) := by
    rw [hO]
    exact coe_prod' _ _
  have hAK : A.map (Int.castRingHom K) * E = B.map (Int.castRingHom K) * O := by
    apply Polynomial.coe_injective
    rw [Polynomial.coe_mul, Polynomial.coe_mul, ← h1, hcoeE, hcoeO, ← hZK]
    ring
  -- apply `σ` and cancel
  have h2 : sig ((q : K) ^ n) (A.map (Int.castRingHom K)) * (Polynomial.C e * E) =
      sig ((q : K) ^ n) (B.map (Int.castRingHom K)) * (Polynomial.C o * O) := by
    rw [← hsE, ← hsO, ← sig_mul, ← sig_mul, hAK]
  have h3 : (sig ((q : K) ^ n) (A.map (Int.castRingHom K)) * B.map (Int.castRingHom K) *
        Polynomial.C e) * E =
      (sig ((q : K) ^ n) (B.map (Int.castRingHom K)) * A.map (Int.castRingHom K) *
        Polynomial.C o) * E := by
    calc (sig ((q : K) ^ n) (A.map (Int.castRingHom K)) * B.map (Int.castRingHom K) *
            Polynomial.C e) * E
        = (sig ((q : K) ^ n) (A.map (Int.castRingHom K)) * (Polynomial.C e * E)) *
            B.map (Int.castRingHom K) := by ring
      _ = (sig ((q : K) ^ n) (B.map (Int.castRingHom K)) * (Polynomial.C o * O)) *
            B.map (Int.castRingHom K) := by rw [h2]
      _ = sig ((q : K) ^ n) (B.map (Int.castRingHom K)) * Polynomial.C o *
            (B.map (Int.castRingHom K) * O) := by ring
      _ = sig ((q : K) ^ n) (B.map (Int.castRingHom K)) * Polynomial.C o *
            (A.map (Int.castRingHom K) * E) := by rw [hAK]
      _ = (sig ((q : K) ^ n) (B.map (Int.castRingHom K)) * A.map (Int.castRingHom K) *
            Polynomial.C o) * E := by ring
  have h4 := mul_right_cancel₀ hE0 h3
  have h5 : sig ((q : K) ^ n) (A.map (Int.castRingHom K)) * B.map (Int.castRingHom K) =
      Polynomial.C (o / e) *
        (A.map (Int.castRingHom K) * sig ((q : K) ^ n) (B.map (Int.castRingHom K))) := by
    have h6 : sig ((q : K) ^ n) (A.map (Int.castRingHom K)) * B.map (Int.castRingHom K) *
        Polynomial.C e * Polynomial.C e⁻¹ =
        sig ((q : K) ^ n) (A.map (Int.castRingHom K)) * B.map (Int.castRingHom K) := by
      rw [mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ he, Polynomial.C_1, mul_one]
    rw [← h6, h4, div_eq_mul_inv, Polynomial.C_mul]
    ring
  -- descend to `ℚ`
  have hinj : Function.Injective (Int.castRingHom K) := RingHom.injective_int _
  have hacast : (Int.castRingHom K) ((q : ℤ) ^ n) = (q : K) ^ n := by simp
  have hsigmap : ∀ p : Polynomial ℤ,
      (p.reverse.comp (Polynomial.C ((q : ℤ) ^ n) * Polynomial.X)).map (Int.castRingHom K) =
        sig ((q : K) ^ n) (p.map (Int.castRingHom K)) := by
    intro p
    rw [← hacast]
    exact sig_map (Int.castRingHom K) hinj ((q : ℤ) ^ n) p
  set L1 : Polynomial ℚ :=
    ((A.reverse.comp (Polynomial.C ((q : ℤ) ^ n) * Polynomial.X)) * B).map
      (Int.castRingHom ℚ) with hL1
  set R1 : Polynomial ℚ :=
    (A * (B.reverse.comp (Polynomial.C ((q : ℤ) ^ n) * Polynomial.X))).map
      (Int.castRingHom ℚ) with hR1
  have hL1K : L1.map (algebraMap ℚ K) =
      sig ((q : K) ^ n) (A.map (Int.castRingHom K)) * B.map (Int.castRingHom K) := by
    rw [hL1, Polynomial.map_map, hcomp, Polynomial.map_mul, hsigmap]
  have hR1K : R1.map (algebraMap ℚ K) =
      A.map (Int.castRingHom K) * sig ((q : K) ^ n) (B.map (Int.castRingHom K)) := by
    rw [hR1, Polynomial.map_map, hcomp, Polynomial.map_mul, hsigmap]
  have hK : L1.map (algebraMap ℚ K) = Polynomial.C (o / e) * R1.map (algebraMap ℚ K) := by
    rw [hL1K, hR1K, h5]
  have hBK0 : B.map (Int.castRingHom K) ≠ 0 := by
    intro h
    have h' := congrArg (fun p => Polynomial.coeff p 0) h
    simp only [Polynomial.coeff_map, hB, Polynomial.coeff_zero] at h'
    simp at h'
  have hr0 : (algebraMap ℚ K) (R1.coeff 0) ≠ 0 := by
    rw [← Polynomial.coeff_map, hR1K, Polynomial.mul_coeff_zero, coeff_zero_sig,
      Polynomial.coeff_map, hA, map_one, one_mul]
    exact Polynomial.leadingCoeff_ne_zero.mpr hBK0
  have hc := congrArg (fun p => Polynomial.coeff p 0) hK
  simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul] at hc
  have hoe : o / e = (algebraMap ℚ K) (L1.coeff 0 / R1.coeff 0) := by
    rw [map_div₀, hc, mul_div_assoc, div_self hr0, mul_one]
  refine ⟨L1.coeff 0 / R1.coeff 0, ?_, ?_⟩
  · intro h0
    rw [h0, map_zero] at hoe
    exact (div_ne_zero ho he) hoe
  · apply Polynomial.map_injective (algebraMap ℚ K) (algebraMap ℚ K).injective
    rw [Polynomial.map_mul, Polynomial.map_C, ← hoe]
    exact hK

/-! ### Bézout -/

theorem exists_bezout2 {k : Type*} [Field k] (f g : Polynomial k) :
    ∃ D u v : Polynomial k, D ∣ f ∧ D ∣ g ∧ D = f * u + g * v := by
  classical
  exact ⟨EuclideanDomain.gcd f g, EuclideanDomain.gcdA f g, EuclideanDomain.gcdB f g,
    EuclideanDomain.gcd_dvd_left f g, EuclideanDomain.gcd_dvd_right f g,
    EuclideanDomain.gcd_eq_gcd_ab f g⟩

theorem exists_bezout3 {k : Type*} [Field k] (f g h : Polynomial k) :
    ∃ D u v w : Polynomial k, D ∣ f ∧ D ∣ g ∧ D ∣ h ∧ D = f * u + g * v + h * w := by
  obtain ⟨D', u', v', h1, h2, h3⟩ := exists_bezout2 g h
  obtain ⟨D, u, v, h4, h5, h6⟩ := exists_bezout2 f D'
  refine ⟨D, u, u' * v, v' * v, h4, h5.trans h1, h5.trans h2, ?_⟩
  rw [h6, h3]
  ring

/-- Two polynomials over a field that divide each other and have constant coefficient `1`
are equal. -/
theorem eq_of_dvd_dvd_of_coeff_zero {k : Type*} [Field k] (f g : Polynomial k) (h1 : f ∣ g)
    (h2 : g ∣ f) (hf : f.coeff 0 = 1) (hg : g.coeff 0 = 1) : f = g := by
  obtain ⟨uu, huu⟩ := associated_of_dvd_dvd h1 h2
  obtain ⟨r, -, hr⟩ := Polynomial.isUnit_iff.mp uu.isUnit
  have h3 := congrArg (fun p => Polynomial.coeff p 0) huu
  simp only [← hr, Polynomial.mul_coeff_zero, Polynomial.coeff_C_zero, hf, hg, one_mul] at h3
  rw [← huu, ← hr, h3, Polynomial.C_1, mul_one]

theorem coeff_zero_prod_eq_one {R : Type*} [CommSemiring R] {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial R) (h : ∀ i ∈ s, (f i).coeff 0 = 1) : (∏ i ∈ s, f i).coeff 0 = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Polynomial.mul_coeff_zero, h a (Finset.mem_insert_self a s),
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi)), one_mul]

/-! ### Complex roots of rational polynomials -/

theorem aeval_eq_zero_of_dvd {D W : Polynomial ℚ} (h : D ∣ W) {z : ℂ}
    (hz : Polynomial.aeval z D = 0) : Polynomial.aeval z W = 0 := by
  obtain ⟨c, rfl⟩ := h
  rw [map_mul, hz, zero_mul]

theorem ne_zero_of_aeval_reverse (W : Polynomial ℚ) (hW : W ≠ 0) {z : ℂ}
    (hz : Polynomial.aeval z W.reverse = 0) : z ≠ 0 := by
  rintro rfl
  rw [← Polynomial.coeff_zero_eq_aeval_zero', Polynomial.coeff_zero_reverse] at hz
  have h1 : W.leadingCoeff = 0 := (algebraMap ℚ ℂ).injective (hz.trans (map_zero _).symm)
  exact hW (Polynomial.leadingCoeff_eq_zero.mp h1)

theorem aeval_inv_of_aeval_reverse (W : Polynomial ℚ) {z : ℂ} (hz0 : z ≠ 0)
    (hz : Polynomial.aeval z W.reverse = 0) : Polynomial.aeval z⁻¹ W = 0 := by
  letI : Invertible z⁻¹ := invertibleOfNonzero (inv_ne_zero hz0)
  have h1 : ⅟(z⁻¹) = z := by rw [invOf_eq_inv, inv_inv]
  rw [Polynomial.aeval_def] at hz ⊢
  rw [← Polynomial.eval₂_reverse_eq_zero_iff (algebraMap ℚ ℂ) z⁻¹ W, h1]
  exact hz

theorem aeval_mul_of_aeval_comp (W : Polynomial ℚ) (r : ℚ) {z : ℂ}
    (hz : Polynomial.aeval z (W.comp (Polynomial.C r * Polynomial.X)) = 0) :
    Polynomial.aeval ((r : ℂ) * z) W = 0 := by
  rw [Polynomial.aeval_comp] at hz
  simpa using hz

/-! ### Real powers of `q` -/

theorem rpow_half_mul (q n i : ℕ) (hq : 1 < q) (hi : i ≤ 2 * n) :
    (q : ℝ) ^ (((2 * n - i : ℕ) : ℝ) / 2) * (q : ℝ) ^ ((i : ℝ) / 2) = (q : ℝ) ^ n := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  rw [← Real.rpow_add hq0, ← Real.rpow_natCast]
  congr 1
  rw [Nat.cast_sub hi]
  push_cast
  ring

theorem rpow_half_mul_lt (q n i j : ℕ) (hq : 1 < q) (hij : i < j) (hj : j ≤ 2 * n) :
    (q : ℝ) ^ (((2 * n - j : ℕ) : ℝ) / 2) * (q : ℝ) ^ ((i : ℝ) / 2) < (q : ℝ) ^ n := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  rw [← Real.rpow_add hq0, ← Real.rpow_natCast]
  apply Real.rpow_lt_rpow_of_exponent_lt hq1
  rw [Nat.cast_sub hj]
  push_cast
  have h : (i : ℝ) < j := by exact_mod_cast hij
  linarith

/-- A common complex root `z` of `W₁^rev` and of `W₂(q^n T)`, where the complex roots of `W₁`
have absolute value at most `q^{i/2}` and those of `W₂` at most `q^{(2n-i)/2}`, satisfies
`|1/z| = q^{i/2}`. -/
theorem norm_inv_eq_of_roots (q n i : ℕ) (hq : 1 < q) (hi : i ≤ 2 * n) (W1 W2 : Polynomial ℚ)
    (hW1 : W1 ≠ 0)
    (h1 : ∀ z : ℂ, Polynomial.aeval z W1 = 0 → ‖z‖ ≤ (q : ℝ) ^ ((i : ℝ) / 2))
    (h2 : ∀ z : ℂ, Polynomial.aeval z W2 = 0 → ‖z‖ ≤ (q : ℝ) ^ (((2 * n - i : ℕ) : ℝ) / 2))
    {z : ℂ} (hz1 : Polynomial.aeval z W1.reverse = 0)
    (hz2 : Polynomial.aeval z (W2.comp (Polynomial.C ((q : ℚ) ^ n) * Polynomial.X)) = 0) :
    ‖z⁻¹‖ = (q : ℝ) ^ ((i : ℝ) / 2) := by
  have hz0 := ne_zero_of_aeval_reverse W1 hW1 hz1
  have ha := h1 _ (aeval_inv_of_aeval_reverse W1 hz0 hz1)
  have hb := h2 _ (aeval_mul_of_aeval_comp W2 _ hz2)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hm := rpow_half_mul q n i hq hi
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hnq : ‖(((q : ℚ) ^ n : ℚ) : ℂ)‖ = (q : ℝ) ^ n := by simp
  rw [norm_mul, hnq] at hb
  rw [norm_inv] at ha ⊢
  have hy : 0 < (q : ℝ) ^ (((2 * n - i : ℕ) : ℝ) / 2) := Real.rpow_pos_of_pos hq0 _
  have h3 : (q : ℝ) ^ (((2 * n - i : ℕ) : ℝ) / 2) * ((q : ℝ) ^ ((i : ℝ) / 2) * ‖z‖) ≤
      (q : ℝ) ^ (((2 * n - i : ℕ) : ℝ) / 2) * 1 := by
    rw [← mul_assoc, hm, mul_one]
    exact hb
  have h4 : (q : ℝ) ^ ((i : ℝ) / 2) * ‖z‖ ≤ 1 := le_of_mul_le_mul_left h3 hy
  apply le_antisymm ha
  rw [inv_eq_one_div, le_div_iff₀ hzpos]
  exact h4

/-- For `i < j ≤ 2n` the polynomials `W₁^rev` and `W₂(q^n T)` have no common complex root,
hence are coprime over `ℚ`. -/
theorem isCoprime_reverse_comp (q n i j : ℕ) (hq : 1 < q) (hij : i < j) (hj : j ≤ 2 * n)
    (W1 W2 : Polynomial ℚ) (hW1 : W1 ≠ 0)
    (h1 : ∀ z : ℂ, Polynomial.aeval z W1 = 0 → ‖z‖ ≤ (q : ℝ) ^ ((i : ℝ) / 2))
    (h2 : ∀ z : ℂ, Polynomial.aeval z W2 = 0 → ‖z‖ ≤ (q : ℝ) ^ (((2 * n - j : ℕ) : ℝ) / 2)) :
    IsCoprime W1.reverse (W2.comp (Polynomial.C ((q : ℚ) ^ n) * Polynomial.X)) := by
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℚ ℂ]
  intro z
  by_contra hcon
  push_neg at hcon
  obtain ⟨hz1, hz2⟩ := hcon
  have hz0 := ne_zero_of_aeval_reverse W1 hW1 hz1
  have ha := h1 _ (aeval_inv_of_aeval_reverse W1 hz0 hz1)
  have hb := h2 _ (aeval_mul_of_aeval_comp W2 _ hz2)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hnq : ‖(((q : ℚ) ^ n : ℚ) : ℂ)‖ = (q : ℝ) ^ n := by simp
  rw [norm_mul, hnq] at hb
  rw [norm_inv] at ha
  have hlt := rpow_half_mul_lt q n i j hq hij hj
  have h5 : (q : ℝ) ^ n = ((q : ℝ) ^ n * ‖z‖) * ‖z‖⁻¹ := by
    rw [mul_assoc, mul_inv_cancel₀ hzpos.ne', mul_one]
  have h6 : ((q : ℝ) ^ n * ‖z‖) * ‖z‖⁻¹ ≤
      (q : ℝ) ^ (((2 * n - j : ℕ) : ℝ) / 2) * (q : ℝ) ^ ((i : ℝ) / 2) :=
    mul_le_mul hb ha (inv_nonneg.mpr (norm_nonneg z)) (Real.rpow_nonneg hq0.le _)
  linarith

/-! ### Gauss's lemma for polynomials with constant coefficient `1` -/

theorem exists_int_of_dvd (A : Polynomial ℤ) (hA : A.coeff 0 = 1) (Pq : Polynomial ℚ)
    (hP0 : Pq.coeff 0 = 1) (hdvd : Pq ∣ A.map (Int.castRingHom ℚ)) :
    ∃ Pz : Polynomial ℤ, Pz.map (Int.castRingHom ℚ) = Pq := by
  have hinj : Function.Injective (Int.castRingHom ℚ) := RingHom.injective_int _
  have hnt : A.natTrailingDegree = 0 :=
    Nat.le_zero.mp (Polynomial.natTrailingDegree_le_of_ne_zero (by rw [hA]; exact one_ne_zero))
  have hmonic : A.reverse.Monic := by
    unfold Polynomial.Monic
    rw [Polynomial.reverse_leadingCoeff]
    unfold Polynomial.trailingCoeff
    rw [hnt, hA]
  have hrevdvd : Pq.reverse ∣ A.reverse.map (algebraMap ℤ ℚ) := by
    obtain ⟨c, hc⟩ := hdvd
    refine ⟨c.reverse, ?_⟩
    rw [algebraMap_int_eq, ← reverse_map_of_injective _ hinj, hc,
      Polynomial.reverse_mul_of_domain]
  obtain ⟨g', hg'⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ hmonic hrevdvd
  have hPnt : Pq.natTrailingDegree = 0 :=
    Nat.le_zero.mp (Polynomial.natTrailingDegree_le_of_ne_zero (by rw [hP0]; exact one_ne_zero))
  have hlc : Pq.reverse.leadingCoeff = 1 := by
    rw [Polynomial.reverse_leadingCoeff]
    unfold Polynomial.trailingCoeff
    rw [hPnt, hP0]
  rw [hlc, Polynomial.C_1, mul_one, algebraMap_int_eq] at hg'
  refine ⟨g'.reverse, ?_⟩
  rw [← reverse_map_of_injective _ hinj, hg']
  exact reverse_reverse_of_coeff_zero_ne_zero _ (by rw [hP0]; exact one_ne_zero)

/-! ### Factorisation over `ℂ` of a polynomial with constant coefficient `1` -/

theorem prod_X_sub_C_eq (m : Multiset ℂ) (hm : ∀ z ∈ m, z ≠ 0) :
    (m.map fun a => (Polynomial.X - Polynomial.C a : Polynomial ℂ)).prod =
      Polynomial.C ((m.map fun z => -z).prod) *
        (m.map fun z => (1 - Polynomial.C z⁻¹ * Polynomial.X : Polynomial ℂ)).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    have ha : a ≠ 0 := hm a (Multiset.mem_cons_self a m)
    have ih' := ih (fun z hz => hm z (Multiset.mem_cons_of_mem hz))
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [ih']
    have h0 : (Polynomial.C a * Polynomial.C a⁻¹ : Polynomial ℂ) = 1 := by
      rw [← Polynomial.C_mul, mul_inv_cancel₀ ha, Polynomial.C_1]
    rw [Polynomial.C_mul, Polynomial.C_neg]
    linear_combination (-(Polynomial.X : Polynomial ℂ) *
      Polynomial.C ((m.map fun z => -z).prod) *
      (m.map fun z => (1 - Polynomial.C z⁻¹ * Polynomial.X : Polynomial ℂ)).prod) * h0

theorem coeff_zero_prod_one_sub (m : Multiset ℂ) (g : ℂ → ℂ) :
    ((m.map fun z => (1 - Polynomial.C (g z) * Polynomial.X : Polynomial ℂ)).prod).coeff 0 =
      1 := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.mul_coeff_zero, ih]
    simp

/-- A complex polynomial with constant coefficient `1` is `∏ (1 - a T)`, the product over the
inverses `a` of its roots; and its roots are nonzero. -/
theorem eq_prod_one_sub (f : Polynomial ℂ) (h0 : f.coeff 0 = 1) :
    f = ((f.roots.map fun z => z⁻¹).map fun a => 1 - Polynomial.C a * Polynomial.X).prod ∧
      ∀ z ∈ f.roots, z ≠ 0 := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at h0
  have hz : ∀ z ∈ f.roots, z ≠ 0 := by
    rintro z hz rfl
    have h1 := (Polynomial.mem_roots hf0).mp hz
    rw [Polynomial.IsRoot.def, ← Polynomial.coeff_zero_eq_eval_zero, h0] at h1
    exact one_ne_zero h1
  refine ⟨?_, hz⟩
  have h1 : f = Polynomial.C f.leadingCoeff * (f.roots.map fun a => Polynomial.X - Polynomial.C a).prod :=
    (IsAlgClosed.splits f).eq_prod_roots
  have h2 : f = Polynomial.C (f.leadingCoeff * (f.roots.map fun z => -z).prod) *
      (f.roots.map fun z => (1 - Polynomial.C z⁻¹ * Polynomial.X : Polynomial ℂ)).prod := by
    rw [Polynomial.C_mul, mul_assoc, ← prod_X_sub_C_eq f.roots hz]
    exact h1
  have h3 := congrArg (fun p => Polynomial.coeff p 0) h2
  simp only [Polynomial.coeff_C_mul] at h3
  rw [h0, coeff_zero_prod_one_sub f.roots (fun z => z⁻¹), mul_one] at h3
  rw [← h3, Polynomial.C_1, one_mul] at h2
  rw [Multiset.map_map]
  exact h2

/-! ### Rational descent of a factor cut out by coprimality -/

theorem exists_rational_factor {K : Type*} [Field K] [CharZero K] (S : Finset ℕ)
    (P : ℕ → Polynomial K) (hP0 : ∀ j ∈ S, (P j).coeff 0 = 1) (Y : Polynomial ℚ)
    (hY : Y.map (algebraMap ℚ K) = ∏ j ∈ S, P j) (T1 T2 : ℕ → Polynomial ℚ)
    (h1 : ∀ j ∈ S, P j ∣ (T1 j).map (algebraMap ℚ K))
    (h2 : ∀ j ∈ S, P j ∣ (T2 j).map (algebraMap ℚ K))
    (hcop : ∀ i ∈ S, ∀ j ∈ S, i < j → IsCoprime (T1 i) (T2 j)) (i : ℕ) (hi : i ∈ S) :
    ∃ Pq : Polynomial ℚ, Pq.map (algebraMap ℚ K) = P i ∧ Pq ∣ Y ∧ Pq ∣ T1 i ∧ Pq ∣ T2 i := by
  classical
  obtain ⟨D, u, v, w, hDY, hD1, hD2, hDeq⟩ := exists_bezout3 Y (T1 i) (T2 i)
  have hPD : P i ∣ D.map (algebraMap ℚ K) := by
    rw [hDeq, Polynomial.map_add, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
      Polynomial.map_mul, hY]
    exact dvd_add (dvd_add (Dvd.dvd.mul_right (Finset.dvd_prod_of_mem P hi) _)
      (Dvd.dvd.mul_right (h1 i hi) _)) (Dvd.dvd.mul_right (h2 i hi) _)
  have hcopj : ∀ j ∈ S.erase i, IsCoprime (D.map (algebraMap ℚ K)) (P j) := by
    intro j hj
    obtain ⟨hne, hjS⟩ := Finset.mem_erase.mp hj
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h' : IsCoprime ((T1 j).map (algebraMap ℚ K)) ((T2 i).map (algebraMap ℚ K)) :=
        (Polynomial.isCoprime_map _).mpr (hcop j hjS i hi hlt)
      exact ((h'.of_isCoprime_of_dvd_left (h1 j hjS)).of_isCoprime_of_dvd_right
        (Polynomial.map_dvd _ hD2)).symm
    · have h' : IsCoprime ((T1 i).map (algebraMap ℚ K)) ((T2 j).map (algebraMap ℚ K)) :=
        (Polynomial.isCoprime_map _).mpr (hcop i hi j hjS hgt)
      exact (h'.of_isCoprime_of_dvd_left (Polynomial.map_dvd _ hD1)).of_isCoprime_of_dvd_right
        (h2 j hjS)
  have hDP : D.map (algebraMap ℚ K) ∣ P i := by
    have h3 : D.map (algebraMap ℚ K) ∣ P i * ∏ j ∈ S.erase i, P j := by
      rw [Finset.mul_prod_erase S P hi, ← hY]
      exact Polynomial.map_dvd _ hDY
    exact (IsCoprime.prod_right hcopj).dvd_of_dvd_mul_right h3
  obtain ⟨uu, huu⟩ := associated_of_dvd_dvd hPD hDP
  obtain ⟨r, hr, hru⟩ := Polynomial.isUnit_iff.mp uu.isUnit
  have hr0 : r ≠ 0 := hr.ne_zero
  have h4 := congrArg (fun p => Polynomial.coeff p 0) huu
  simp only [← hru, Polynomial.mul_coeff_zero, Polynomial.coeff_C_zero, hP0 i hi, one_mul,
    Polynomial.coeff_map] at h4
  have hδ : D.coeff 0 ≠ 0 := by
    intro h
    rw [h, map_zero] at h4
    exact hr0 h4
  have hPqD : Polynomial.C (D.coeff 0)⁻¹ * D ∣ D :=
    Dvd.intro (Polynomial.C (D.coeff 0)) (by
      rw [mul_comm (Polynomial.C (D.coeff 0)⁻¹) D, mul_assoc, ← Polynomial.C_mul,
        inv_mul_cancel₀ hδ, Polynomial.C_1, mul_one])
  refine ⟨Polynomial.C (D.coeff 0)⁻¹ * D, ?_, hPqD.trans hDY, hPqD.trans hD1, hPqD.trans hD2⟩
  rw [Polynomial.map_mul, Polynomial.map_C, ← huu, ← hru, map_inv₀, ← h4,
    mul_comm (Polynomial.C r⁻¹), mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hr0,
    Polynomial.C_1, mul_one]

/-- **The Weil factorisation from cohomological data with weight bounds.** -/
theorem weil_factorization_of_cohomology
    (N : ℕ → ℕ) (n q : ℕ) (hq : 1 < q) {K : Type*} [Field K] [CharZero K] (d : ℕ → ℕ)
    (Φ : (i : ℕ) → Matrix (Fin (d i)) (Fin (d i)) K)
    (htr : ∀ m : ℕ, 0 < m →
      (N m : K) = ∑ i ∈ Finset.range (2 * n + 1), (-1 : K) ^ i * ((Φ i) ^ m).trace)
    (hPD : ∀ i ≤ 2 * n, ∃ (G : Matrix (Fin (d i)) (Fin (d (2 * n - i))) K)
        (H : Matrix (Fin (d (2 * n - i))) (Fin (d i)) K),
        G * H = 1 ∧ H * G = 1 ∧ (Φ i).transpose * G * Φ (2 * n - i) = (q : K) ^ n • G)
    (hd0 : d 0 = 1) (hΦ0 : Φ 0 = 1)
    (hW : ∀ i ≤ 2 * n, ∃ W : Polynomial ℚ, W ≠ 0 ∧
        (Φ i).charpoly ∣ W.map (algebraMap ℚ K) ∧
        ∀ z : ℂ, Polynomial.aeval z W = 0 → ‖z‖ ≤ (q : ℝ) ^ ((i : ℝ) / 2))
    (A B : Polynomial ℤ) (hA : A.coeff 0 = 1) (hB : B.coeff 0 = 1)
    (hcop : IsCoprime (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)))
    (hZ : WeilConjectures.zetaOfCounts N *
        ((B.map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) =
      ((A.map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ)) :
    ∃ (P : ℕ → Polynomial ℤ) (α : ℕ → Multiset ℂ),
      WeilConjectures.zetaOfCounts N *
          (∏ i ∈ (Finset.range (2 * n + 1)).filter Even,
            (((P i).map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ)) =
        ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd,
            (((P i).map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) ∧
      P 0 = 1 - Polynomial.X ∧
      P (2 * n) = 1 - Polynomial.C ((q : ℤ) ^ n) * Polynomial.X ∧
      (∀ i, 1 ≤ i → i ≤ 2 * n - 1 →
        (P i).map (Int.castRingHom ℂ) =
            ((α i).map fun a => 1 - Polynomial.C a * Polynomial.X).prod ∧
        ∀ a ∈ α i, a ≠ 0) ∧
      (∀ i, 1 ≤ i → i ≤ 2 * n - 1 → ∀ a ∈ α i, ‖a‖ = (q : ℝ) ^ ((i : ℝ) / 2)) := by
  have hq0 : 0 < q := Nat.zero_lt_of_lt hq
  have ha0 : ((q : K) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hq0.ne')
  have hle : ∀ i ∈ Finset.range (2 * n + 1), i ≤ 2 * n :=
    fun i hi => Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hcomp : (algebraMap ℚ K).comp (Int.castRingHom ℚ) = Int.castRingHom K :=
    RingHom.ext_int _ _
  -- Poincaré duality on the reversed characteristic polynomials
  have hF := sig_charpolyRev_of_pairing n ((q : K) ^ n) ha0 d Φ hPD
  have hrev : ∀ i, i ≤ 2 * n → ((Φ i).charpolyRev).reverse = (Φ i).charpoly :=
    fun i hi => (hF i hi).1
  have hF1 : ∀ i, i ≤ 2 * n → ∃ u : K, u ≠ 0 ∧
      sig ((q : K) ^ n) ((Φ i).charpolyRev) = Polynomial.C u * (Φ (2 * n - i)).charpolyRev :=
    fun i hi => (hF i hi).2
  choose! u hu0 hu using hF1
  choose! W hW0 hWdvd hWroot using hW
  have hPc : ∀ i, ((Φ i).charpolyRev).coeff 0 = 1 := by
    intro i
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp
  -- the rational polynomials `T1 i = W_i^rev` and `T2 i = W_{2n-i}(q^n T)`
  obtain ⟨T1, hT1⟩ : ∃ T1 : ℕ → Polynomial ℚ, ∀ i, T1 i = (W i).reverse := ⟨_, fun _ => rfl⟩
  obtain ⟨T2, hT2⟩ : ∃ T2 : ℕ → Polynomial ℚ, ∀ i,
      T2 i = (W (2 * n - i)).comp (Polynomial.C ((q : ℚ) ^ n) * Polynomial.X) :=
    ⟨_, fun _ => rfl⟩
  have hP1 : ∀ i, i ≤ 2 * n → (Φ i).charpolyRev ∣ (T1 i).map (algebraMap ℚ K) := by
    intro i hi
    obtain ⟨c, hc⟩ := hWdvd i hi
    rw [hT1, ← reverse_map_of_injective _ (algebraMap ℚ K).injective, hc,
      Polynomial.reverse_mul_of_domain, Matrix.reverse_charpoly]
    exact dvd_mul_right _ _
  have hP2 : ∀ i, i ≤ 2 * n → (Φ i).charpolyRev ∣ (T2 i).map (algebraMap ℚ K) := by
    intro i hi
    have hj : 2 * n - i ≤ 2 * n := Nat.sub_le _ _
    have h1 := hu (2 * n - i) hj
    rw [Nat.sub_sub_self hi] at h1
    have h2 : (Φ i).charpolyRev ∣ sig ((q : K) ^ n) ((Φ (2 * n - i)).charpolyRev) := by
      rw [h1]
      exact dvd_mul_left _ _
    refine h2.trans ?_
    obtain ⟨c, hc⟩ := hWdvd (2 * n - i) hj
    have hqc : (algebraMap ℚ K) ((q : ℚ) ^ n) = (q : K) ^ n := by simp
    unfold sig
    rw [hrev (2 * n - i) hj, hT2, Polynomial.map_comp, hc, Polynomial.mul_comp,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, hqc]
    exact dvd_mul_right _ _
  have hcopT : ∀ i j, i < j → j ≤ 2 * n → IsCoprime (T1 i) (T2 j) := by
    intro i j hij hj
    rw [hT1, hT2]
    exact isCoprime_reverse_comp q n i j hq hij hj (W i) (W (2 * n - j)) (hW0 i (by omega))
      (hWroot i (by omega)) (hWroot (2 * n - j) (Nat.sub_le _ _))
  have hcopP : ∀ i j, i ≤ 2 * n → j ≤ 2 * n → i < j →
      IsCoprime ((Φ i).charpolyRev) ((Φ j).charpolyRev) := by
    intro i j hi hj hij
    have h : IsCoprime ((T1 i).map (algebraMap ℚ K)) ((T2 j).map (algebraMap ℚ K)) :=
      (Polynomial.isCoprime_map _).mpr (hcopT i j hij hj)
    exact (h.of_isCoprime_of_dvd_left (hP1 i hi)).of_isCoprime_of_dvd_right (hP2 j hj)
  have hcopP' : ∀ i j, i ≤ 2 * n → j ≤ 2 * n → i ≠ j →
      IsCoprime ((Φ i).charpolyRev) ((Φ j).charpolyRev) := by
    intro i j hi hj hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hcopP i j hi hj h
    · exact (hcopP j i hj hi h).symm
  -- the even and odd products
  obtain ⟨E, hE⟩ : ∃ E : Polynomial K,
      E = ∏ i ∈ (Finset.range (2 * n + 1)).filter Even, (Φ i).charpolyRev := ⟨_, rfl⟩
  obtain ⟨O, hO⟩ : ∃ O : Polynomial K,
      O = ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd, (Φ i).charpolyRev := ⟨_, rfl⟩
  have hEO : IsCoprime E O := by
    rw [hE, hO]
    refine IsCoprime.prod_left fun i hi => IsCoprime.prod_right fun j hj => ?_
    have hi' := Finset.mem_filter.mp hi
    have hj' := Finset.mem_filter.mp hj
    refine hcopP' i j (hle i hi'.1) (hle j hj'.1) ?_
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hj'.2) hi'.2
  have hEc : E.coeff 0 = 1 := by
    rw [hE]
    exact coeff_zero_prod_eq_one _ _ (fun i _ => hPc i)
  have hOc : O.coeff 0 = 1 := by
    rw [hO]
    exact coeff_zero_prod_eq_one _ _ (fun i _ => hPc i)
  -- the zeta series over `K`
  have h1 : PowerSeries.map (algebraMap ℚ K) (WeilConjectures.zetaOfCounts N) *
      ((B.map (Int.castRingHom K) : Polynomial K) : PowerSeries K) =
      ((A.map (Int.castRingHom K) : Polynomial K) : PowerSeries K) := by
    have h := congrArg (PowerSeries.map (algebraMap ℚ K)) hZ
    rw [map_mul, ← Polynomial.polynomial_map_coe, ← Polynomial.polynomial_map_coe,
      Polynomial.map_map, Polynomial.map_map, hcomp] at h
    exact h
  have hZK := WeilConjectures.zetaOfCounts_mul_prod_charpolyRev_of_trace_formula N (Finset.range (2 * n + 1)) d Φ htr
  have hcoeE : ((E : Polynomial K) : PowerSeries K) =
      ∏ i ∈ (Finset.range (2 * n + 1)).filter Even,
        (((Φ i).charpolyRev : Polynomial K) : PowerSeries K) := by
    rw [hE]
    exact coe_prod' _ _
  have hcoeO : ((O : Polynomial K) : PowerSeries K) =
      ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd,
        (((Φ i).charpolyRev : Polynomial K) : PowerSeries K) := by
    rw [hO]
    exact coe_prod' _ _
  have hAK : A.map (Int.castRingHom K) * E = B.map (Int.castRingHom K) * O := by
    apply Polynomial.coe_injective
    rw [Polynomial.coe_mul, Polynomial.coe_mul, ← h1, hcoeE, hcoeO, ← hZK]
    ring
  have hAKcop : IsCoprime (A.map (Int.castRingHom K)) (B.map (Int.castRingHom K)) := by
    have h := (Polynomial.isCoprime_map (algebraMap ℚ K)).mpr hcop
    rwa [Polynomial.map_map, Polynomial.map_map, hcomp] at h
  have hAc : (A.map (Int.castRingHom K)).coeff 0 = 1 := by
    rw [Polynomial.coeff_map, hA, map_one]
  have hBc : (B.map (Int.castRingHom K)).coeff 0 = 1 := by
    rw [Polynomial.coeff_map, hB, map_one]
  have hAO : A.map (Int.castRingHom K) = O := by
    apply eq_of_dvd_dvd_of_coeff_zero _ _ _ _ hAc hOc
    · exact hAKcop.dvd_of_dvd_mul_left (Dvd.intro E hAK)
    · exact hEO.symm.dvd_of_dvd_mul_right (Dvd.intro_left (B.map (Int.castRingHom K)) hAK.symm)
  have hBE : B.map (Int.castRingHom K) = E := by
    apply eq_of_dvd_dvd_of_coeff_zero _ _ _ _ hBc hEc
    · exact hAKcop.symm.dvd_of_dvd_mul_left (Dvd.intro O hAK.symm)
    · exact hEO.dvd_of_dvd_mul_right (Dvd.intro_left (A.map (Int.castRingHom K)) hAK)
  -- rational factors
  have hPq : ∀ i, i ≤ 2 * n → ∃ Pq : Polynomial ℚ,
      Pq.map (algebraMap ℚ K) = (Φ i).charpolyRev ∧
      Pq ∣ (A * B).map (Int.castRingHom ℚ) ∧ Pq ∣ T1 i ∧ Pq ∣ T2 i := by
    intro i hi
    have hmem : i ∈ Finset.range (2 * n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
    rcases Nat.even_or_odd i with he | ho
    · obtain ⟨Pq, h1, h2, h3, h4⟩ := exists_rational_factor
        ((Finset.range (2 * n + 1)).filter Even) (fun j => (Φ j).charpolyRev)
        (fun j _ => hPc j) (B.map (Int.castRingHom ℚ))
        (by rw [Polynomial.map_map, hcomp, hBE, hE]) T1 T2
        (fun j hj => hP1 j (hle j (Finset.mem_filter.mp hj).1))
        (fun j hj => hP2 j (hle j (Finset.mem_filter.mp hj).1))
        (fun a _ b hb hab => hcopT a b hab (hle b (Finset.mem_filter.mp hb).1))
        i (Finset.mem_filter.mpr ⟨hmem, he⟩)
      refine ⟨Pq, h1, h2.trans ?_, h3, h4⟩
      rw [Polynomial.map_mul]
      exact dvd_mul_left _ _
    · obtain ⟨Pq, h1, h2, h3, h4⟩ := exists_rational_factor
        ((Finset.range (2 * n + 1)).filter Odd) (fun j => (Φ j).charpolyRev)
        (fun j _ => hPc j) (A.map (Int.castRingHom ℚ))
        (by rw [Polynomial.map_map, hcomp, hAO, hO]) T1 T2
        (fun j hj => hP1 j (hle j (Finset.mem_filter.mp hj).1))
        (fun j hj => hP2 j (hle j (Finset.mem_filter.mp hj).1))
        (fun a _ b hb hab => hcopT a b hab (hle b (Finset.mem_filter.mp hb).1))
        i (Finset.mem_filter.mpr ⟨hmem, ho⟩)
      refine ⟨Pq, h1, h2.trans ?_, h3, h4⟩
      rw [Polynomial.map_mul]
      exact dvd_mul_right _ _
  choose! Pq hPqmap hPqdvd hPq1 hPq2 using hPq
  have hPqc : ∀ i, i ≤ 2 * n → (Pq i).coeff 0 = 1 := by
    intro i hi
    have h := congrArg (fun p => Polynomial.coeff p 0) (hPqmap i hi)
    simp only [Polynomial.coeff_map, hPc] at h
    exact (algebraMap ℚ K).injective (h.trans (map_one _).symm)
  have hABc : (A * B).coeff 0 = 1 := by
    rw [Polynomial.mul_coeff_zero, hA, hB, mul_one]
  have hPz : ∀ i, i ≤ 2 * n → ∃ Pz : Polynomial ℤ, Pz.map (Int.castRingHom ℚ) = Pq i :=
    fun i hi => exists_int_of_dvd (A * B) hABc (Pq i) (hPqc i hi) (hPqdvd i hi)
  choose! Pz hPzmap using hPz
  -- `H⁰` and `H^{2n}`
  have hcharpolyRev0 : (Φ 0).charpolyRev = 1 - Polynomial.X := by
    rw [hΦ0, Matrix.charpolyRev]
    have h : (1 : Matrix (Fin (d 0)) (Fin (d 0)) (Polynomial K)) -
        (Polynomial.X : Polynomial K) •
          (1 : Matrix (Fin (d 0)) (Fin (d 0)) K).map (Polynomial.C : K →+* Polynomial K) =
        (1 - Polynomial.X : Polynomial K) •
          (1 : Matrix (Fin (d 0)) (Fin (d 0)) (Polynomial K)) := by
      rw [Matrix.map_one _ (map_zero _) (map_one _), sub_smul, one_smul]
    rw [h, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, hd0, pow_one]
  have hcharpolyRev2n : (Φ (2 * n)).charpolyRev =
      1 - Polynomial.C ((q : K) ^ n) * Polynomial.X := by
    have h := hu 0 (Nat.zero_le _)
    rw [Nat.sub_zero] at h
    have hχ : (Φ 0).charpoly = Polynomial.X - 1 := by
      rw [hΦ0, Matrix.charpoly_one, Fintype.card_fin, hd0, pow_one]
    unfold sig at h
    rw [hrev 0 (Nat.zero_le _), hχ, Polynomial.sub_comp, Polynomial.X_comp,
      Polynomial.one_comp] at h
    have h0 := congrArg (fun p => Polynomial.coeff p 0) h
    simp only [Polynomial.coeff_sub, Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero,
      mul_zero, Polynomial.coeff_one_zero, zero_sub, Polynomial.coeff_C_zero, hPc,
      mul_one] at h0
    have hu1 : Polynomial.C (u 0) = (-1 : Polynomial K) := by
      rw [← h0, Polynomial.C_neg, Polynomial.C_1]
    rw [hu1] at h
    linear_combination h
  have hinjK : Function.Injective (Int.castRingHom K) := RingHom.injective_int _
  have hPzc : ∀ i, i ≤ 2 * n → ((Pz i).map (Int.castRingHom ℂ)).coeff 0 = 1 := by
    intro i hi
    have h := congrArg (fun p => Polynomial.coeff p 0) (hPzmap i hi)
    simp only [Polynomial.coeff_map, hPqc i hi] at h
    rw [Polynomial.coeff_map,
      (RingHom.injective_int (Int.castRingHom ℚ)) (h.trans (map_one _).symm), map_one]
  have hCmap : ∀ i, (Pz i).map (Int.castRingHom ℂ) =
      ((Pz i).map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ) := by
    intro i
    rw [Polynomial.map_map]
    congr 1
  refine ⟨Pz, fun i => ((Pz i).map (Int.castRingHom ℂ)).roots.map (fun z => z⁻¹),
    ?_, ?_, ?_, ?_, ?_⟩
  · -- the zeta identity
    have hprodE : ∏ i ∈ (Finset.range (2 * n + 1)).filter Even,
        (Pz i).map (Int.castRingHom ℚ) = B.map (Int.castRingHom ℚ) := by
      apply Polynomial.map_injective (algebraMap ℚ K) (algebraMap ℚ K).injective
      rw [Polynomial.map_prod, Polynomial.map_map, hcomp, hBE, hE]
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [hPzmap i (hle i (Finset.mem_filter.mp hi).1),
        hPqmap i (hle i (Finset.mem_filter.mp hi).1)]
    have hprodO : ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd,
        (Pz i).map (Int.castRingHom ℚ) = A.map (Int.castRingHom ℚ) := by
      apply Polynomial.map_injective (algebraMap ℚ K) (algebraMap ℚ K).injective
      rw [Polynomial.map_prod, Polynomial.map_map, hcomp, hAO, hO]
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [hPzmap i (hle i (Finset.mem_filter.mp hi).1),
        hPqmap i (hle i (Finset.mem_filter.mp hi).1)]
    rw [← coe_prod', ← coe_prod', hprodE, hprodO]
    exact hZ
  · -- `P 0 = 1 - T`
    apply Polynomial.map_injective (Int.castRingHom K) hinjK
    have h : (Pz 0).map (Int.castRingHom K) = (Φ 0).charpolyRev := by
      rw [← hcomp, ← Polynomial.map_map, hPzmap 0 (Nat.zero_le _), hPqmap 0 (Nat.zero_le _)]
    rw [h, hcharpolyRev0]
    simp
  · -- `P (2n) = 1 - q^n T`
    apply Polynomial.map_injective (Int.castRingHom K) hinjK
    have h : (Pz (2 * n)).map (Int.castRingHom K) = (Φ (2 * n)).charpolyRev := by
      rw [← hcomp, ← Polynomial.map_map, hPzmap (2 * n) le_rfl, hPqmap (2 * n) le_rfl]
    rw [h, hcharpolyRev2n]
    simp
  · -- factorisation over `ℂ`
    intro i hi1 hi2
    have hi : i ≤ 2 * n := by omega
    obtain ⟨h1, h2⟩ := eq_prod_one_sub ((Pz i).map (Int.castRingHom ℂ)) (hPzc i hi)
    refine ⟨h1, ?_⟩
    intro a ha
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp ha
    exact inv_ne_zero (h2 z hz)
  · -- the weights
    intro i hi1 hi2 a ha
    have hi : i ≤ 2 * n := by omega
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp ha
    have hf0 : (Pz i).map (Int.castRingHom ℂ) ≠ 0 := by
      intro h
      have h' := hPzc i hi
      rw [h, Polynomial.coeff_zero] at h'
      exact zero_ne_one h'
    have hroot := (Polynomial.mem_roots hf0).mp hz
    rw [Polynomial.IsRoot.def, hCmap, hPzmap i hi, Polynomial.eval_map,
      ← Polynomial.aeval_def] at hroot
    have hz1 : Polynomial.aeval z (W i).reverse = 0 := by
      have h := aeval_eq_zero_of_dvd (hPq1 i hi) hroot
      rwa [hT1] at h
    have hz2 : Polynomial.aeval z
        ((W (2 * n - i)).comp (Polynomial.C ((q : ℚ) ^ n) * Polynomial.X)) = 0 := by
      have h := aeval_eq_zero_of_dvd (hPq2 i hi) hroot
      rwa [hT2] at h
    exact norm_inv_eq_of_roots q n i hq hi (W i) (W (2 * n - i)) (hW0 i hi) (hWroot i hi)
      (hWroot (2 * n - i) (Nat.sub_le _ _)) hz1 hz2

end WCAux

open Polynomial
open WeilConjectures

theorem solution
    (N : ℕ → ℕ) (n q : ℕ) (hq : 1 < q) {K : Type*} [Field K] [CharZero K] (d : ℕ → ℕ)
    (Φ : (i : ℕ) → Matrix (Fin (d i)) (Fin (d i)) K)
    (htr : ∀ m : ℕ, 0 < m →
      (N m : K) = ∑ i ∈ Finset.range (2 * n + 1), (-1 : K) ^ i * ((Φ i) ^ m).trace)
    (hPD : ∀ i ≤ 2 * n, ∃ (G : Matrix (Fin (d i)) (Fin (d (2 * n - i))) K)
        (H : Matrix (Fin (d (2 * n - i))) (Fin (d i)) K),
        G * H = 1 ∧ H * G = 1 ∧ (Φ i).transpose * G * Φ (2 * n - i) = (q : K) ^ n • G)
    (hd0 : d 0 = 1) (hΦ0 : Φ 0 = 1)
    (hW : ∀ i ≤ 2 * n, ∃ W : ℚ[X], W ≠ 0 ∧ (Φ i).charpoly ∣ W.map (algebraMap ℚ K) ∧
        ∀ z : ℂ, aeval z W = 0 → ‖z‖ ≤ (q : ℝ) ^ ((i : ℝ) / 2))
    (A B : ℤ[X]) (hA : A.coeff 0 = 1) (hB : B.coeff 0 = 1)
    (hcop : IsCoprime (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)))
    (hZ : zetaOfCounts N * ((B.map (Int.castRingHom ℚ) : ℚ[X]) : PowerSeries ℚ) =
      ((A.map (Int.castRingHom ℚ) : ℚ[X]) : PowerSeries ℚ)) :
    ∃ (P : ℕ → ℤ[X]) (α : ℕ → Multiset ℂ),
      zetaOfCounts N *
          (∏ i ∈ (Finset.range (2 * n + 1)).filter Even,
            ((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ)) =
        ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd,
            ((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ) ∧
      P 0 = 1 - Polynomial.X ∧
      P (2 * n) = 1 - C ((q : ℤ) ^ n) * Polynomial.X ∧
      (∀ i, 1 ≤ i → i ≤ 2 * n - 1 →
        (P i).map (Int.castRingHom ℂ) = ((α i).map fun a => 1 - C a * Polynomial.X).prod ∧
        ∀ a ∈ α i, a ≠ 0) ∧
      (∀ i, 1 ≤ i → i ≤ 2 * n - 1 → ∀ a ∈ α i,
        ‖a‖ = (q : ℝ) ^ ((i : ℝ) / 2)) :=
  WCAux.weil_factorization_of_cohomology N n q hq d Φ htr hPD hd0 hΦ0 hW A B hA hB hcop hZ
