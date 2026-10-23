-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P40.diagonalEquality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:43:43.881025+00:00
-- url     : https://prove2.me/submissions/450ce880-d4b0-422d-92d9-5214ed360a72

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

/-- PDF p.12, Eq.(54), DOMAIN CORRECTION: the printed J beta<=T merely
ensures PSD. Requiring (J+1) beta<=T also makes the residual eigenvalue >=beta,
as required for the designated actual minimum. eta>=0 and K=d-3-J are retained.
This corrected-domain witness does not assert the deferred full sharpness clause. -/
theorem solution {d : ℕ} (hd : 3 ≤ d) (J : ℕ) (hJ : J ≤ d - 3)
    (beta T : ℝ) (hbeta : 0 < beta)
    (hresidual : ((J : ℝ) + 1) * beta ≤ T) (heta : 0 ≤ largeEta d J beta T) :
    IsDensityMatrix (largeRho d J beta T) ∧ IsDensityMatrix (largeSigma d J beta T) ∧
    minEigenvalue (largeSigma d J beta T) = beta ∧
    traceNorm (largeRho d J beta T - largeSigma d J beta T) = 2 * T ∧
    relativeEntropy (largeRho d J beta T) (largeSigma d J beta T) =
      (((T + beta) * Real.log ((T + beta) / beta) : ℝ) : EReal) := by
  obtain ⟨m, rfl⟩ : ∃ m, d = J + m + 3 := ⟨d - 3 - J, by omega⟩
  set eta := largeEta (J + m + 3) J beta T with hetadef
  have heta' : eta = 1 - T - ((m : ℝ) + 2) * beta := by
    rw [hetadef, largeEta]; push_cast; ring
  set R : ℕ → ℝ := fun k => if k = 0 then T + beta
    else if k = 1 then 0 else if k < 2 + J then 0
    else if k + 1 = J + m + 3 then beta + eta else beta with hRdef
  set S : ℕ → ℝ := fun k => if k = 0 then beta
    else if k = 1 then T - J * beta
    else if k + 1 = J + m + 3 then beta + eta else beta with hSdef
  have hRm : largeRho (J + m + 3) J beta T = Matrix.diagonal (fun i => ((R i.val : ℝ) : ℂ)) := rfl
  have hSm : largeSigma (J + m + 3) J beta T = Matrix.diagonal (fun i => ((S i.val : ℝ) : ℂ)) := rfl
  have split : ∀ F : ℕ → ℝ, ∑ i : Fin (J + m + 3), F i.val =
      F 0 + F 1 + ∑ k ∈ Finset.range J, F (2 + k) + ∑ k ∈ Finset.range m, F (2 + J + k) +
        F (2 + J + m) := by
    intro F
    rw [Fin.sum_univ_eq_sum_range F (J + m + 3), show J + m + 3 = (2 + J + m) + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_add, Finset.sum_range_add]
    simp [Finset.sum_range_succ]
  have cst : ∀ (n : ℕ) (G : ℕ → ℝ) (c : ℝ), (∀ k < n, G k = c) →
      ∑ k ∈ Finset.range n, G k = n * c := by
    intro n G c h
    rw [Finset.sum_congr rfl (fun k hk => h k (Finset.mem_range.mp hk))]; simp
  have hR0 : R 0 = T + beta := by simp [hRdef]
  have hR1 : R 1 = 0 := by simp [hRdef]
  have hRJ : ∀ k < J, R (2 + k) = 0 := by
    intro k hk; simp only [hRdef]; split_ifs <;> first | rfl | (exfalso; omega)
  have hRM : ∀ k < m, R (2 + J + k) = beta := by
    intro k hk; simp only [hRdef]; split_ifs <;> first | rfl | (exfalso; omega)
  have hRL : R (2 + J + m) = beta + eta := by
    simp only [hRdef]; split_ifs <;> first | rfl | (exfalso; omega)
  have hS0 : S 0 = beta := by simp [hSdef]
  have hS1 : S 1 = T - J * beta := by simp [hSdef]
  have hSJ : ∀ k < J, S (2 + k) = beta := by
    intro k hk; simp only [hSdef]; split_ifs <;> first | rfl | (exfalso; omega)
  have hSM : ∀ k < m, S (2 + J + k) = beta := by
    intro k hk; simp only [hSdef]; split_ifs <;> first | rfl | (exfalso; omega)
  have hSL : S (2 + J + m) = beta + eta := by
    simp only [hSdef]; split_ifs <;> first | rfl | (exfalso; omega)
  have hT0 : 0 ≤ T := by have := (J.cast_nonneg : (0:ℝ) ≤ J); nlinarith
  have hJb : (J : ℝ) * beta + beta ≤ T := by linarith
  have hSpos : ∀ k, beta ≤ S k := by
    intro k; simp only [hSdef]; split_ifs <;> linarith
  have hRnn : ∀ k, 0 ≤ R k := by
    intro k; simp only [hRdef]; split_ifs <;> linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hRm]
    apply g78a_density_diag _ (fun i => hRnn _)
    rw [split R, hR0, hR1, hRL, cst J _ 0 (fun k hk => hRJ k hk), cst m _ beta (fun k hk => hRM k hk),
      heta']
    ring
  · rw [hSm]
    apply g78a_density_diag _ (fun i => by linarith [hSpos i.val])
    rw [split S, hS0, hS1, hSL, cst J _ beta (fun k hk => hSJ k hk),
      cst m _ beta (fun k hk => hSM k hk), heta']
    ring
  · rw [hSm, g78a_minEig_diag _ ⟨0, by omega⟩]
    · exact hS0
    · intro j; rw [show ((⟨0, by omega⟩ : Fin (J + m + 3)) : ℕ) = 0 from rfl, hS0]; exact hSpos _
  · rw [hRm, hSm, Matrix.diagonal_sub]
    have e : (fun i : Fin (J + m + 3) => ((R i.val : ℝ) : ℂ) - ((S i.val : ℝ) : ℂ)) =
        fun i => (((R i.val - S i.val) : ℝ) : ℂ) := by funext i; push_cast; ring
    rw [e, g78a_traceNorm_diag, split (fun k => |R k - S k|), hR0, hR1, hRL, hS0, hS1, hSL,
      cst J _ beta (fun k hk => by beta_reduce; rw [hRJ k hk, hSJ k hk]; simp [hbeta.le]),
      cst m _ 0 (fun k hk => by beta_reduce; rw [hRM k hk, hSM k hk]; simp)]
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    simp; ring
  · rw [hRm, hSm, g78a_relEnt_diag]
    · congr 1
      rw [split (fun k => R k * Real.log (R k) - R k * Real.log (S k)), hR0, hR1, hRL, hS0, hSL,
        cst J _ 0 (fun k hk => by beta_reduce; rw [hRJ k hk]; simp),
        cst m _ 0 (fun k hk => by beta_reduce; rw [hRM k hk, hSM k hk]; simp)]
      have hp : 0 < T + beta := by linarith
      rw [Real.log_div hp.ne' hbeta.ne']
      simp; ring
    · intro i hi; exfalso; linarith [hSpos i.val]



end
