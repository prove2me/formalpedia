-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P40.noQuadraticLogarithmicBound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:32:24.590852+00:00
-- url     : https://prove2.me/submissions/a032f6ab-127d-45bf-b1f4-c2b724bc26d3

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open Filter MeasureTheory Asymptotics

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

open QAlgorithms.Papers.Independent.Gap48.P40
open QAlgorithms
open scoped Matrix ComplexOrder

section G78A
open Polynomial
lemma g78a_cfc_diag {X : Type*} [Fintype X] [DecidableEq X] (d : X → ℝ) (f : ℝ → ℝ) :
    cfc f (Matrix.diagonal (fun i => (d i : ℂ))) = Matrix.diagonal (fun i => (f (d i) : ℂ)) := by
  set A := Matrix.diagonal (fun i => (d i : ℂ)) with hA
  have hsa : IsSelfAdjoint A := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, hA, Matrix.diagonal_conjTranspose]
    congr 1; funext i; simp
  set S : Finset ℝ := Finset.univ.image d
  let p : ℝ[X] := Lagrange.interpolate S id f
  have hp : ∀ i, p.eval (d i) = f (d i) := by
    intro i
    have := Lagrange.eval_interpolate_at_node (s := S) (v := id) (r := f) (i := d i)
      (Set.injOn_id _) (Finset.mem_image_of_mem d (Finset.mem_univ i))
    exact this
  have hspec : ∀ x ∈ spectrum ℝ A, ∃ i, d i = x := by
    intro x hx
    rw [← spectrum.preimage_algebraMap ℂ, Set.mem_preimage, hA, spectrum_diagonal,
      Set.mem_range] at hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, by rw [Complex.coe_algebraMap] at hi; exact_mod_cast hi⟩
  have h1 : cfc f A = cfc p.eval A := by
    apply cfc_congr
    intro x hx
    obtain ⟨i, rfl⟩ := hspec x hx
    exact (hp i).symm
  rw [h1, cfc_polynomial p A]
  rw [hA, show Matrix.diagonal (fun i => (d i : ℂ)) =
    Matrix.diagonalAlgHom ℝ (fun i => (d i : ℂ)) from rfl, Polynomial.aeval_algHom_apply]
  rw [show Matrix.diagonal (fun i => (f (d i) : ℂ)) =
    Matrix.diagonalAlgHom ℝ (fun i => (f (d i) : ℂ)) from rfl]
  congr 1
  funext i
  rw [Polynomial.aeval_pi_apply₂]
  rw [show ((d i : ℝ) : ℂ) = algebraMap ℝ ℂ (d i) from rfl, Polynomial.aeval_algebraMap_apply,
    Polynomial.aeval_def, Algebra.algebraMap_self, ← Polynomial.eval, hp]
  rfl
end G78A

lemma g78a_spec_diag {X : Type*} [Fintype X] [DecidableEq X] (d : X → ℝ) :
    spectrum ℝ (Matrix.diagonal (fun i => (d i : ℂ))) = Set.range d := by
  ext x
  rw [← spectrum.preimage_algebraMap ℂ, Set.mem_preimage, spectrum_diagonal, Set.mem_range,
    Set.mem_range]
  constructor
  · rintro ⟨i, hi⟩; exact ⟨i, by rw [Complex.coe_algebraMap] at hi; exact_mod_cast hi⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, by rw [Complex.coe_algebraMap]⟩

lemma g78a_minEig_spec {X : Type*} [Fintype X] [DecidableEq X] (A : Matrix X X ℂ)
    (hA : A.IsHermitian) (hc : 0 < Fintype.card X) :
    minEigenvalue A ∈ spectrum ℝ A ∧ ∀ x ∈ spectrum ℝ A, minEigenvalue A ≤ x := by
  have hm : minEigenvalue A = hA.eigenvalues₀ (Fin.rev ⟨0, hc⟩) := by
    unfold minEigenvalue ascEigenvalues
    rw [dif_pos hc, dif_pos hA]
  have hr : spectrum ℝ A = Set.range hA.eigenvalues₀ := by
    rw [hA.spectrum_real_eq_range_eigenvalues]
    ext x; constructor
    · rintro ⟨i, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨(Fintype.equivOfCardEq (Fintype.card_fin _)) j, by
        simp [Matrix.IsHermitian.eigenvalues]⟩
  rw [hr, hm]
  refine ⟨⟨_, rfl⟩, ?_⟩
  rintro x ⟨j, rfl⟩
  apply hA.eigenvalues₀_antitone
  rw [Fin.le_def]; simp; omega

lemma g78a_minEig_diag {X : Type*} [Fintype X] [DecidableEq X] (d : X → ℝ) (i : X)
    (hi : ∀ j, d i ≤ d j) : minEigenvalue (Matrix.diagonal (fun j => (d j : ℂ))) = d i := by
  have hH : (Matrix.diagonal (fun j => (d j : ℂ))).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; funext j; simp
  have hc : 0 < Fintype.card X := Fintype.card_pos_iff.mpr ⟨i⟩
  obtain ⟨h1, h2⟩ := g78a_minEig_spec _ hH hc
  rw [g78a_spec_diag] at h1 h2
  obtain ⟨k, hk⟩ := h1
  apply le_antisymm (h2 _ ⟨i, rfl⟩)
  rw [← hk]; exact hi k

lemma g78a_relEnt_diag {X : Type*} [Fintype X] [DecidableEq X] (p q : X → ℝ)
    (hpq : ∀ i, q i = 0 → p i = 0) :
    QAlgorithms.Papers.Independent.Dependency50.P21.relativeEntropy
      (Matrix.diagonal (fun j => (p j : ℂ))) (Matrix.diagonal (fun j => (q j : ℂ))) =
      ((∑ i, (p i * Real.log (p i) - p i * Real.log (q i)) : ℝ) : EReal) := by
  unfold QAlgorithms.Papers.Independent.Dependency50.P21.relativeEntropy
  rw [if_pos]
  · rw [g78a_cfc_diag, g78a_cfc_diag, Matrix.diagonal_mul_diagonal, Matrix.trace_sub,
      Matrix.trace_diagonal, Matrix.trace_diagonal, Complex.sub_re, Complex.re_sum, Complex.re_sum,
      ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Complex.mul_re]
  · intro v hv
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
    funext i
    have := congrFun hv i
    simp only [Matrix.mulVec_diagonal, Pi.zero_apply] at this ⊢
    rcases mul_eq_zero.mp this with h | h
    · rw [hpq i (by exact_mod_cast h)]; simp
    · rw [h, mul_zero]

lemma g78a_traceNorm_diag {X : Type*} [Fintype X] [DecidableEq X] (m : X → ℝ) :
    traceNorm (Matrix.diagonal (fun j => (m j : ℂ))) = ∑ i, |m i| := by
  unfold traceNorm
  have e : (Matrix.diagonal (fun j => (m j : ℂ)))ᴴ * Matrix.diagonal (fun j => (m j : ℂ)) =
      Matrix.diagonal (fun j => ((m j ^ 2 : ℝ) : ℂ)) := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1; funext j; simp; ring
  rw [e, g78a_cfc_diag, Matrix.trace_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Real.sqrt_sq_eq_abs]

lemma g78a_density_diag {X : Type*} [Fintype X] [DecidableEq X] (m : X → ℝ)
    (h0 : ∀ i, 0 ≤ m i) (h1 : ∑ i, m i = 1) :
    IsDensityMatrix (Matrix.diagonal (fun j => (m j : ℂ))) := by
  refine ⟨Matrix.PosSemidef.diagonal (fun i => by simpa using h0 i), ?_⟩
  rw [Matrix.trace_diagonal]; exact_mod_cast h1

/-- PDF p.5, Proposition 1: commuting qubit witnesses disprove every positive
universal quadratic-logarithmic constant. The proof's (2-p-q)^2 typo is not used. -/
theorem solution (r : ℝ) (hr : 0 < r) :
    ∃ p q : ℝ, 0 ≤ p ∧ p ≤ 1 ∧ 0 < q ∧ q < 1 / 2 ∧
      let rho : Mat 2 := Matrix.diagonal ![(p : ℂ), ((1 - p : ℝ) : ℂ)]
      let sigma : Mat 2 := Matrix.diagonal ![(q : ℂ), ((1 - q : ℝ) : ℂ)]
      relativeEntropy rho sigma >
        ((r * ((rho - sigma) ^ 2).trace.re * |Real.log (minEigenvalue sigma)| : ℝ) : EReal) := by
  set q : ℝ := 1 / (16 * (r + 1) ^ 2) with hqdef
  have hr1 : 0 < r + 1 := by linarith
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 / 2 := by
    rw [hqdef, div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  refine ⟨0, q, le_refl _, zero_le_one, hq0, hq1, ?_⟩
  intro rho sigma
  have hrho : rho = Matrix.diagonal (fun j => ((![0, 1] : Fin 2 → ℝ) j : ℂ)) := by
    show Matrix.diagonal _ = _
    congr 1; funext j; fin_cases j <;> simp
  have hsig : sigma = Matrix.diagonal (fun j => ((![q, 1 - q] : Fin 2 → ℝ) j : ℂ)) := by
    show Matrix.diagonal _ = _
    congr 1; funext j; fin_cases j <;> simp
  have hD : relativeEntropy rho sigma = ((-Real.log (1 - q) : ℝ) : EReal) := by
    rw [hrho, hsig, g78a_relEnt_diag]
    · congr 1; simp [Fin.sum_univ_two]
    · intro i hi; fin_cases i
      · simp
      · simp at hi; linarith
  have hm : minEigenvalue sigma = q := by
    rw [hsig, g78a_minEig_diag _ 0]
    · simp
    · intro j; fin_cases j <;> simp; linarith
  have htr : ((rho - sigma) ^ 2).trace.re = 2 * q ^ 2 := by
    rw [hrho, hsig, Matrix.diagonal_sub, Matrix.diagonal_pow, Matrix.trace_diagonal,
      Fin.sum_univ_two]
    simp; rw [← Complex.ofReal_pow, Complex.ofReal_re]; ring
  rw [hD, hm, htr, gt_iff_lt, EReal.coe_lt_coe_iff]
  have hlq : Real.log q < 0 := Real.log_neg hq0 (by linarith)
  rw [abs_of_neg hlq]
  have h1 : q ≤ -Real.log (1 - q) := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 - q by linarith); linarith
  have h2 : -Real.log q < 8 * (r + 1) := by
    have e : -Real.log q = 2 * Real.log (4 * (r + 1)) := by
      rw [hqdef, one_div, Real.log_inv, show 16 * (r + 1) ^ 2 = (4 * (r + 1)) ^ 2 by ring,
        Real.log_pow]; push_cast; ring
    have := Real.log_le_sub_one_of_pos (show 0 < 4 * (r + 1) by linarith)
    rw [e]; linarith
  have h3 : r * (2 * q ^ 2) * (-Real.log q) ≤ r * (2 * q ^ 2) * (8 * (r + 1)) := by
    apply mul_le_mul_of_nonneg_left h2.le; positivity
  have h4 : r * (2 * q ^ 2) * (8 * (r + 1)) < q := by
    have e : r * (2 * q ^ 2) * (8 * (r + 1)) = q * (r / (r + 1)) := by
      rw [hqdef]; field_simp; ring
    rw [e]
    have : r / (r + 1) < 1 := by rw [div_lt_one hr1]; linarith
    nlinarith
  linarith



end
