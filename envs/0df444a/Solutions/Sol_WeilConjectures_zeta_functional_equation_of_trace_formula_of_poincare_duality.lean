-- Prove2me | solution 1 for WeilConjectures.zeta_functional_equation_of_trace_formula_of_poincare_duality
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T23:48:28.525999+00:00
-- url     : https://prove2.me/submissions/6b2400ab-4421-4998-8e1f-035189a95b05

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

end WCAux

open Polynomial
open WeilConjectures

theorem solution
    (N : ℕ → ℕ) (n q : ℕ) (hq : 0 < q) {K : Type*} [Field K] [CharZero K] (d : ℕ → ℕ)
    (Φ : (i : ℕ) → Matrix (Fin (d i)) (Fin (d i)) K)
    (htr : ∀ m : ℕ, 0 < m →
      (N m : K) = ∑ i ∈ Finset.range (2 * n + 1), (-1 : K) ^ i * ((Φ i) ^ m).trace)
    (hPD : ∀ i ≤ 2 * n, ∃ (G : Matrix (Fin (d i)) (Fin (d (2 * n - i))) K)
        (H : Matrix (Fin (d (2 * n - i))) (Fin (d i)) K),
        G * H = 1 ∧ H * G = 1 ∧ (Φ i).transpose * G * Φ (2 * n - i) = (q : K) ^ n • G)
    (A B : ℤ[X]) (hA : A.coeff 0 = 1) (hB : B.coeff 0 = 1)
    (hZ : zetaOfCounts N * ((B.map (Int.castRingHom ℚ) : ℚ[X]) : PowerSeries ℚ) =
      ((A.map (Int.castRingHom ℚ) : ℚ[X]) : PowerSeries ℚ)) :
    ∃ c : ℚ, c ≠ 0 ∧
      ((A.reverse.comp (C ((q : ℤ) ^ n) * Polynomial.X)) * B).map (Int.castRingHom ℚ) =
        C c * (A * (B.reverse.comp (C ((q : ℤ) ^ n) * Polynomial.X))).map
          (Int.castRingHom ℚ) :=
  WCAux.functional_equation_of_trace_formula_of_poincare_duality N n q hq d Φ htr hPD A B hA hB hZ
