-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P40.smallDistanceEquality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:39:45.073675+00:00
-- url     : https://prove2.me/submissions/2d1e3f90-1bb0-441f-880f-8e2a373620d5

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

/-- PDF p.11: the source's explicit small-distance equality construction,
with third coordinate distinct from the first two and the actual minimum beta. -/
theorem solution {d : ℕ} (hd : 3 ≤ d) (beta T : ℝ)
    (hbeta : 0 < beta ∧ beta ≤ 1 / (d : ℝ)) (hT : 0 ≤ T ∧ T ≤ beta) :
    IsDensityMatrix (smallRho d beta T) ∧ IsDensityMatrix (smallSigma d beta) ∧
    minEigenvalue (smallSigma d beta) = beta ∧
    traceNorm (smallRho d beta T - smallSigma d beta) / 2 = T ∧
    relativeEntropy (smallRho d beta T) (smallSigma d beta) =
      ((traceSmallBound beta T : ℝ) : EReal) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 3 := ⟨d - 3, by omega⟩
  obtain ⟨hb0, hb1⟩ := hbeta
  obtain ⟨hT0, hT1⟩ := hT
  have hdb : ((n + 3 : ℕ) : ℝ) * beta ≤ 1 := by
    have h := (le_div_iff₀ (show (0:ℝ) < ((n + 3 : ℕ) : ℝ) by positivity)).mp hb1
    linarith
  have k3 : ∀ k : ℕ, k + 1 + 1 + 1 ≠ 2 ∧ k + 1 + 1 + 1 ≠ 1 ∧ k + 1 + 1 + 1 ≠ 0 := by
    intro k; omega
  set sv : Fin (n + 3) → ℝ := fun i => if i.val = 2 then beta + (1 - ((n + 3 : ℕ) : ℝ) * beta) else beta
    with hsv
  set fv : Fin (n + 3) → ℝ := fun i => if i.val = 0 then 1 else if i.val = 1 then -1 else 0 with hfv
  have hS : smallSigma (n + 3) beta = Matrix.diagonal (fun i => (sv i : ℂ)) := rfl
  have hR : smallRho (n + 3) beta T = Matrix.diagonal (fun i => ((sv i + T * fv i : ℝ) : ℂ)) := by
    unfold smallRho smallSigma matrixF
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, hsv, hfv]
    split_ifs <;> push_cast <;> ring
  have hD : smallRho (n + 3) beta T - smallSigma (n + 3) beta =
      Matrix.diagonal (fun i => ((T * fv i : ℝ) : ℂ)) := by
    rw [hR, hS, Matrix.diagonal_sub]; congr 1; funext i; push_cast; ring
  have sum3 : ∀ g : Fin (n + 3) → ℝ, ∑ i, g i = g ⟨0, by omega⟩ + g ⟨1, by omega⟩ + g ⟨2, by omega⟩ +
      ∑ i : Fin n, g ⟨i.val + 3, by omega⟩ := by
    intro g; rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]; simp only [add_assoc]; rfl
  have k3 : ∀ k : ℕ, k + 3 ≠ 2 ∧ k + 3 ≠ 1 ∧ k + 3 ≠ 0 := by intro k; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hR]
    apply g78a_density_diag
    · intro i
      simp only [hsv, hfv]
      split_ifs <;> push_cast at * <;> nlinarith
    · rw [sum3]; simp [hsv, hfv, k3]; push_cast; ring
  · rw [hS]
    apply g78a_density_diag
    · intro i
      simp only [hsv]
      split_ifs <;> push_cast at * <;> nlinarith
    · rw [sum3]; simp [hsv, k3]; push_cast; ring
  · rw [hS, g78a_minEig_diag sv ⟨0, by omega⟩]
    · simp [hsv]
    · intro j; simp only [hsv]; split_ifs <;> simp <;> push_cast at * <;> linarith
  · rw [hD, g78a_traceNorm_diag, sum3]
    simp [hfv, k3, abs_of_nonneg hT0]
  · rw [hR, hS, g78a_relEnt_diag]
    · congr 1
      rw [sum3]
      simp [hsv, hfv, k3]
      unfold traceSmallBound
      have hp : 0 < beta + T := by linarith
      rw [Real.log_div hp.ne' hb0.ne']
      rcases eq_or_lt_of_le hT1 with h | h
      · subst h; simp <;> ring
      · rw [Real.log_div (by linarith) hb0.ne']; ring
    · intro i hi
      exfalso
      simp only [hsv] at hi
      split_ifs at hi <;> push_cast at * <;> linarith



end
