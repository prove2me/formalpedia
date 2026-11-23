-- Prove2me | solution 1 for WeilConjectures.exists_pure_weil_zeta_factorization_of_ge_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T20:19:56.604481+00:00
-- url     : https://prove2.me/submissions/74078673-6d37-4075-bab4-093aa8c1d257
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction
import Theorems.Thm_FiniteFields_zetaFunction_integral_presentation
import Theorems.Thm_WeilConjectures_weil_riemann_hypothesis_of_cohomology_weight_bound
import Theorems.Thm_WeilConjectures_exists_deligne_weight_bound_cohomology_of_ge_two

open AlgebraicGeometry CategoryTheory Polynomial
open WeilConjectures

section PureWeilFactorizationFromWeightBound

private lemma dualBasis_repr_apply {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    {d : ℕ} (b : Module.Basis (Fin d) K W) (φ : Module.Dual K W) (s : Fin d) :
    b.dualBasis.repr φ s = φ (b s) := by
  simp

private lemma reverse_map_of_injective {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (hf : Function.Injective f) (P : R[X]) :
    P.reverse.map f = (P.map f).reverse := by
  have hdeg : (P.map f).natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf P
  ext m
  rw [Polynomial.coeff_map, Polynomial.coeff_reverse, Polynomial.coeff_reverse, hdeg,
    Polynomial.coeff_map]

private lemma reverse_one_sub_C_mul_X {a : ℂ} (ha : a ≠ 0) :
    (1 - Polynomial.C a * Polynomial.X : ℂ[X]).reverse = Polynomial.X - Polynomial.C a := by
  have hdeg : (1 - Polynomial.C a * Polynomial.X : ℂ[X]).natDegree = 1 := by
    have h1 : (1 - Polynomial.C a * Polynomial.X : ℂ[X]) =
        Polynomial.C (-a) * Polynomial.X + Polynomial.C 1 := by
      rw [map_neg, map_one]; ring
    rw [h1, Polynomial.natDegree_add_C, Polynomial.natDegree_C_mul_X (-a) (neg_ne_zero.mpr ha)]
  ext m
  rw [Polynomial.coeff_reverse, hdeg]
  rcases m with _ | _ | m
  · simp [Polynomial.revAt_le, Polynomial.coeff_one, Polynomial.coeff_C]
  · simp [Polynomial.revAt_le, Polynomial.coeff_one, Polynomial.coeff_C]
  · rw [Polynomial.revAt_eq_self_of_lt (by omega : 1 < m + 2)]
    simp [Polynomial.coeff_one, Polynomial.coeff_X]

private lemma coeff_zero_multiset_prod_one_sub (s : Multiset ℂ) :
    ((s.map fun a => (1 - Polynomial.C a * Polynomial.X : ℂ[X])).prod).coeff 0 = 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.mul_coeff_zero, ih, mul_one]
    simp

private lemma reverse_multiset_prod_of_domain (s : Multiset ℂ[X]) :
    s.prod.reverse = (s.map Polynomial.reverse).prod := by
  induction s using Multiset.induction_on with
  | empty =>
    rw [Multiset.prod_zero, Multiset.map_zero, Multiset.prod_zero,
      ← Polynomial.C_1, Polynomial.reverse_C]
  | cons p s ih =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons,
      Polynomial.reverse_mul_of_domain, ih]

end PureWeilFactorizationFromWeightBound

theorem solution (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] [Finite k] [CharP k p] (n : ℕ) (hn : 2 ≤ n)
    (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f) :
    ∃ P : ℕ → ℚ[X],
      P 0 = 1 - Polynomial.X ∧
      (∀ i ≤ 2 * n, (P i).coeff 0 = 1) ∧
      zetaFunction p f *
          (∏ i ∈ (Finset.range (2 * n + 1)).filter Even, (P i : PowerSeries ℚ)) =
        ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd, (P i : PowerSeries ℚ) ∧
      (∀ i ≤ 2 * n, ∀ z : ℂ, aeval z (P i).reverse = 0 →
        ‖z‖ = (Nat.card k : ℝ) ^ ((i : ℝ) / 2)) := by
  obtain ⟨K, hKField, hKChar0, V, hVAdd, hVMod, hVFin, F, htr, hPD, hfin0, hF0, hW⟩ :=
    WeilConjectures.exists_deligne_weight_bound_cohomology_of_ge_two p k n hn X f hproj
  let _ : Field K := hKField
  let _ : CharZero K := hKChar0
  let _ : ∀ i, AddCommGroup (V i) := hVAdd
  let _ : ∀ i, Module K (V i) := hVMod
  let _ : ∀ i, Module.Finite K (V i) := hVFin
  let d : ℕ → ℕ := fun i => Module.finrank K (V i)
  let b : ∀ i, Module.Basis (Fin (d i)) K (V i) := fun i => Module.finBasis K (V i)
  let Φ : (i : ℕ) → Matrix (Fin (d i)) (Fin (d i)) K :=
    fun i => LinearMap.toMatrix (b i) (b i) (F i)
  have htr_mat : ∀ m : ℕ, 0 < m →
      (pointCount p f m : K) =
        ∑ i ∈ Finset.range (2 * n + 1), (-1 : K) ^ i * ((Φ i) ^ m).trace := by
    intro m hm
    rw [htr m hm]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    have hpow : (Φ i) ^ m = LinearMap.toMatrix (b i) (b i) (F i ^ m) := by
      simpa [Φ] using LinearMap.toMatrix_pow (b i) (F i) m
    rw [hpow, LinearMap.trace_eq_matrix_trace K (b i)]
  have hPD_mat : ∀ i ≤ 2 * n, ∃ (G : Matrix (Fin (d i)) (Fin (d (2 * n - i))) K)
      (H : Matrix (Fin (d (2 * n - i))) (Fin (d i)) K),
      G * H = 1 ∧ H * G = 1 ∧
        (Φ i).transpose * G * Φ (2 * n - i) = (Nat.card k : K) ^ n • G := by
    intro i hi
    obtain ⟨e, he⟩ := hPD i hi
    let M : Matrix (Fin (d (2 * n - i))) (Fin (d i)) K :=
      LinearMap.toMatrix (b i) (b (2 * n - i)).dualBasis e.toLinearMap
    let N : Matrix (Fin (d i)) (Fin (d (2 * n - i))) K :=
      LinearMap.toMatrix (b (2 * n - i)).dualBasis (b i) e.symm.toLinearMap
    refine ⟨M.transpose, N.transpose, ?_, ?_, ?_⟩
    · have hNM : N * M = 1 := by
        calc
          N * M = LinearMap.toMatrix (b i) (b i) (e.symm.toLinearMap.comp e.toLinearMap) := by
            rw [LinearMap.toMatrix_comp (b i) (b (2 * n - i)).dualBasis (b i)]
          _ = LinearMap.toMatrix (b i) (b i) LinearMap.id := by
            congr 1; ext x; simp
          _ = 1 := LinearMap.toMatrix_id (b i)
      calc
        M.transpose * N.transpose = (N * M).transpose := (Matrix.transpose_mul N M).symm
        _ = (1 : Matrix (Fin (d i)) (Fin (d i)) K).transpose := by rw [hNM]
        _ = 1 := Matrix.transpose_one
    · have hMN : M * N = 1 := by
        calc
          M * N = LinearMap.toMatrix (b (2 * n - i)).dualBasis (b (2 * n - i)).dualBasis
              (e.toLinearMap.comp e.symm.toLinearMap) := by
            rw [LinearMap.toMatrix_comp (b (2 * n - i)).dualBasis (b i) (b (2 * n - i)).dualBasis]
          _ = LinearMap.toMatrix (b (2 * n - i)).dualBasis (b (2 * n - i)).dualBasis
              LinearMap.id := by
            congr 1; ext x; simp
          _ = 1 := LinearMap.toMatrix_id (b (2 * n - i)).dualBasis
      calc
        N.transpose * M.transpose = (M * N).transpose := (Matrix.transpose_mul M N).symm
        _ = (1 : Matrix (Fin (d (2 * n - i))) (Fin (d (2 * n - i))) K).transpose := by rw [hMN]
        _ = 1 := Matrix.transpose_one
    · ext r s
      have hG_entry : ∀ u v, M.transpose u v = e (b i u) (b (2 * n - i) v) := fun u v => by
        change LinearMap.toMatrix (b i) (b (2 * n - i)).dualBasis e.toLinearMap v u =
          e (b i u) (b (2 * n - i) v)
        rw [LinearMap.toMatrix_apply, dualBasis_repr_apply]
        rfl
      have hFi_apply : F i (b i r) = ∑ u : Fin (d i), (Φ i u r) • b i u := by
        simp [Φ, LinearMap.toMatrix_apply, (b i).sum_repr]
      have hF2n_apply : F (2 * n - i) (b (2 * n - i) s) =
          ∑ v : Fin (d (2 * n - i)), (Φ (2 * n - i) v s) • b (2 * n - i) v := by
        simp [Φ, LinearMap.toMatrix_apply, (b (2 * n - i)).sum_repr]
      calc
        ((Φ i).transpose * M.transpose * Φ (2 * n - i)) r s
            = ∑ v : Fin (d (2 * n - i)),
                (∑ u : Fin (d i), Φ i u r * M.transpose u v) * Φ (2 * n - i) v s := by
              simp [Matrix.mul_apply, Matrix.transpose_apply]
        _ = ∑ u : Fin (d i), ∑ v : Fin (d (2 * n - i)),
              Φ i u r * (Φ (2 * n - i) v s * e (b i u) (b (2 * n - i) v)) := by
              simp_rw [hG_entry, Finset.sum_mul]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
              ring
        _ = ∑ u : Fin (d i), Φ i u r *
              e (b i u) (∑ v : Fin (d (2 * n - i)), (Φ (2 * n - i) v s) • b (2 * n - i) v) := by
              refine Finset.sum_congr rfl fun u _ => ?_
              rw [← Finset.mul_sum, map_sum]
              simp_rw [map_smul, smul_eq_mul]
        _ = e (∑ u : Fin (d i), (Φ i u r) • b i u) (F (2 * n - i) (b (2 * n - i) s)) := by
              rw [← hF2n_apply, map_sum, LinearMap.sum_apply]
              simp_rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
        _ = e (F i (b i r)) (F (2 * n - i) (b (2 * n - i) s)) := by rw [← hFi_apply]
        _ = (Nat.card k : K) ^ n * e (b i r) (b (2 * n - i) s) := he (b i r) (b (2 * n - i) s)
        _ = ((Nat.card k : K) ^ n • M.transpose) r s := by
              rw [Matrix.smul_apply, smul_eq_mul, hG_entry]
  have hΦ0 : Φ 0 = 1 := by
    simp [Φ, hF0]
  have hW_mat : ∀ i ≤ 2 * n, ∃ W : ℚ[X], W ≠ 0 ∧ (Φ i).charpoly ∣ W.map (algebraMap ℚ K) ∧
      ∀ z : ℂ, aeval z W = 0 → ‖z‖ ≤ (Nat.card k : ℝ) ^ ((i : ℝ) / 2) := by
    intro i hi
    obtain ⟨W, hWne, hWdvd, hWnorm⟩ := hW i hi
    refine ⟨W, hWne, ?_, hWnorm⟩
    dsimp only [Φ]
    rw [LinearMap.charpoly_toMatrix]
    exact hWdvd
  obtain ⟨A, B, hA0, hB0, hcop, hZ⟩ :=
    FiniteFields.zetaFunction_integral_presentation p k X f hproj
  have hq_gt1 : 1 < Nat.card k := Finite.one_lt_card
  obtain ⟨Pint, α, hPzeta, hP0, hP2n, hPfac, hPnorm⟩ :=
    WeilConjectures.weil_riemann_hypothesis_of_cohomology_weight_bound
      (pointCount p f) n (Nat.card k) hq_gt1 d Φ htr_mat hPD_mat hfin0 hΦ0 hW_mat
      A B hA0 hB0 hcop hZ
  let P : ℕ → ℚ[X] := fun i => (Pint i).map (Int.castRingHom ℚ)
  have hPmapC : ∀ i, (P i).map (algebraMap ℚ ℂ) = (Pint i).map (Int.castRingHom ℂ) := by
    intro i
    rw [Polynomial.map_map]
    congr 1
  refine ⟨P, ?_, ?_, hPzeta, ?_⟩
  · simp [P, hP0]
  · intro i hi
    by_cases h0 : i = 0
    · subst h0; simp [P, hP0]
    · by_cases h2n : i = 2 * n
      · subst h2n; simp [P, hP2n]
      · have hi1 : 1 ≤ i := by omega
        have hi2 : i ≤ 2 * n - 1 := by omega
        have hfac := (hPfac i hi1 hi2).1
        have hcC : (((P i).coeff 0 : ℚ) : ℂ) = 1 := by
          have h1 : (((P i).coeff 0 : ℚ) : ℂ) = ((P i).map (algebraMap ℚ ℂ)).coeff 0 :=
            (Polynomial.coeff_map (algebraMap ℚ ℂ) 0).symm
          rw [h1, hPmapC i, hfac, coeff_zero_multiset_prod_one_sub]
        exact Rat.cast_injective (α := ℂ) (by simpa using hcC)
  · intro i hi z hz
    have heval : (((Pint i).map (Int.castRingHom ℂ)).reverse).eval z = 0 := by
      have h1 : aeval z (P i).reverse = ((P i).reverse.map (algebraMap ℚ ℂ)).eval z := by
        rw [Polynomial.aeval_def, ← Polynomial.eval_map]
      rw [h1, reverse_map_of_injective (algebraMap ℚ ℂ) Rat.cast_injective, hPmapC i] at hz
      exact hz
    by_cases h0 : i = 0
    · subst h0
      have hrev0 : ((Pint 0).map (Int.castRingHom ℂ)).reverse = Polynomial.X - Polynomial.C 1 := by
        rw [hP0]
        simpa [map_one] using reverse_one_sub_C_mul_X (a := (1 : ℂ)) one_ne_zero
      rw [hrev0, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at heval
      subst heval
      simp
    · by_cases h2n : i = 2 * n
      · subst h2n
        have hqC_ne : ((Nat.card k : ℂ) ^ n) ≠ 0 :=
          pow_ne_zero n (Nat.cast_ne_zero.mpr (by omega))
        have hrev2n : ((Pint (2 * n)).map (Int.castRingHom ℂ)).reverse =
            Polynomial.X - Polynomial.C ((Nat.card k : ℂ) ^ n) := by
          rw [hP2n]
          simpa using reverse_one_sub_C_mul_X hqC_ne
        rw [hrev2n, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
          sub_eq_zero] at heval
        subst heval
        have hdiv : ((2 * n : ℕ) : ℝ) / 2 = (n : ℝ) := by push_cast; ring
        rw [hdiv, Real.rpow_natCast, norm_pow, Complex.norm_natCast]
      · have hi1 : 1 ≤ i := by omega
        have hi2 : i ≤ 2 * n - 1 := by omega
        obtain ⟨hfac, hne0⟩ := hPfac i hi1 hi2
        rw [hfac, reverse_multiset_prod_of_domain, Multiset.map_map] at heval
        have hmap_eq :
            (α i).map (Polynomial.reverse ∘ fun a : ℂ => 1 - Polynomial.C a * Polynomial.X) =
              (α i).map (fun a : ℂ => Polynomial.X - Polynomial.C a) := by
          refine Multiset.map_congr rfl fun a ha => ?_
          exact reverse_one_sub_C_mul_X (hne0 a ha)
        rw [hmap_eq] at heval
        have hprod_eval :
            ((α i).map (fun a : ℂ => z - a)).prod = 0 := by
          have hring := map_multiset_prod (Polynomial.evalRingHom z)
            ((α i).map (fun a : ℂ => Polynomial.X - Polynomial.C a))
          rw [Multiset.map_map] at hring
          have hsimp :
              (α i).map (⇑(Polynomial.evalRingHom z) ∘ fun a : ℂ => Polynomial.X - Polynomial.C a) =
                (α i).map (fun a : ℂ => z - a) := by
            refine Multiset.map_congr rfl fun a _ => ?_
            simp
          rw [hsimp] at hring
          rw [← hring]
          exact heval
        obtain ⟨a, ha_mem, hza⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hprod_eval)
        have hz_eq : z = a := sub_eq_zero.mp hza
        rw [hz_eq]
        exact hPnorm i hi1 hi2 a ha_mem
