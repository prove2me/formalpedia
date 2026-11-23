-- Prove2me | solution 1 for WeilConjectures.exists_zeta_functional_equation_of_ge_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T19:28:32.55665+00:00
-- url     : https://prove2.me/submissions/2e57e320-627e-43cc-af77-d47e99f93401
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction
import Theorems.Thm_FiniteFields_zetaFunction_integral_presentation
import Theorems.Thm_WeilConjectures_zeta_functional_equation_of_trace_formula_of_poincare_duality
import Theorems.Thm_WeilConjectures_exists_poincare_duality_cohomology_of_ge_two

open AlgebraicGeometry CategoryTheory Polynomial
open WeilConjectures

section FunctionalEquationFromCohomology

private lemma reverse_map_intCast (P : ℤ[X]) :
    P.reverse.map (Int.castRingHom ℚ) = (P.map (Int.castRingHom ℚ)).reverse := by
  have hdeg : (P.map (Int.castRingHom ℚ)).natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective P
  ext m
  rw [Polynomial.coeff_map, Polynomial.coeff_reverse, Polynomial.coeff_reverse, hdeg,
    Polynomial.coeff_map]

private lemma comp_C_pow_X_map_intCast (P : ℤ[X]) (q n : ℕ) :
    (P.reverse.comp (Polynomial.C ((q : ℤ) ^ n) * Polynomial.X)).map (Int.castRingHom ℚ) =
      (P.map (Int.castRingHom ℚ)).reverse.comp (Polynomial.C ((q : ℚ) ^ n) * Polynomial.X) := by
  rw [Polynomial.map_comp, reverse_map_intCast, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_X]
  simp

private lemma dualBasis_repr_apply {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    {d : ℕ} (b : Module.Basis (Fin d) K W) (φ : Module.Dual K W) (s : Fin d) :
    b.dualBasis.repr φ s = φ (b s) := by
  simp

end FunctionalEquationFromCohomology

theorem solution (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] [Finite k] [CharP k p] (n : ℕ) (hn : 2 ≤ n)
    (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f) :
    ∃ (P Q : ℚ[X]) (c : ℚ), Q ≠ 0 ∧ c ≠ 0 ∧
      zetaFunction p f * (Q : PowerSeries ℚ) = (P : PowerSeries ℚ) ∧
      (P.reverse.comp (Polynomial.C ((Nat.card k : ℚ) ^ n) * Polynomial.X)) * Q =
        Polynomial.C c *
          (P * (Q.reverse.comp (Polynomial.C ((Nat.card k : ℚ) ^ n) * Polynomial.X))) := by
  obtain ⟨K, hKField, hKChar0, V, hVAdd, hVMod, hVFin, F, htr, hPD⟩ :=
    WeilConjectures.exists_poincare_duality_cohomology_of_ge_two p k n hn X f hproj
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
  obtain ⟨A, B, hA0, hB0, _, hZ⟩ :=
    FiniteFields.zetaFunction_integral_presentation p k X f hproj
  obtain ⟨c, hc_ne, hfe_int⟩ :=
    WeilConjectures.zeta_functional_equation_of_trace_formula_of_poincare_duality
      (pointCount p f) n (Nat.card k) Nat.card_pos d Φ htr_mat hPD_mat A B hA0 hB0 hZ
  let P : ℚ[X] := A.map (Int.castRingHom ℚ)
  let Q : ℚ[X] := B.map (Int.castRingHom ℚ)
  have hQ_ne : Q ≠ 0 := by
    intro h0
    have hcoeff := congrArg (fun g : ℚ[X] => g.coeff 0) h0
    simp [Q, Polynomial.coeff_map, hB0] at hcoeff
  refine ⟨P, Q, c, hQ_ne, hc_ne, hZ, ?_⟩
  rw [Polynomial.map_mul, comp_C_pow_X_map_intCast A (Nat.card k) n,
    Polynomial.map_mul, comp_C_pow_X_map_intCast B (Nat.card k) n] at hfe_int
  exact hfe_int
