-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P40.traceOperatorFactorTwo
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:51:15.829139+00:00
-- url     : https://prove2.me/submissions/147307ee-a27d-4b28-8647-771be08e91ef

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

open scoped MatrixOrder ComplexOrder in
theorem g78a_trace_mul_psd_nonneg {X : Type*} [Fintype X] [DecidableEq X] (M ρ : Matrix X X ℂ)
    (hM : M.PosSemidef) (hρ : ρ.PosSemidef) : 0 ≤ (M * ρ).trace.re := by
  have h0 : 0 ≤ ρ := hρ.nonneg
  have hS2 : CFC.sqrt ρ * CFC.sqrt ρ = ρ := CFC.sqrt_mul_sqrt_self ρ h0
  have hSa : IsSelfAdjoint (CFC.sqrt ρ) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg ρ)
  have hSh : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ := by
    rw [← Matrix.star_eq_conjTranspose]; exact hSa.star_eq
  have htr : (M * ρ).trace = (CFC.sqrt ρ * M * (CFC.sqrt ρ)ᴴ).trace := by
    rw [hSh]
    conv_lhs => rw [← hS2, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  rw [htr]
  exact (Complex.nonneg_iff.mp (hM.mul_mul_conjTranspose_same (CFC.sqrt ρ)).trace_nonneg).1

open scoped MatrixOrder ComplexOrder in
/-- Tr(ρ log σ) ≥ log λmin for density ρ and σ with positive minimal eigenvalue. -/
theorem g78a_trace_log_ge {X : Type*} [Fintype X] [DecidableEq X] (ρ σ : Matrix X X ℂ)
    (hρ : IsDensityMatrix ρ) (hσ : σ.IsHermitian) (hc : 0 < Fintype.card X)
    (hm : 0 < minEigenvalue σ) :
    Real.log (minEigenvalue σ) ≤ (ρ * cfc Real.log σ).trace.re := by
  set m := minEigenvalue σ
  obtain ⟨_, hspec⟩ := g78a_minEig_spec σ hσ hc
  have hcont : ContinuousOn (fun x => Real.log x - Real.log m) (spectrum ℝ σ) :=
    (Matrix.finite_real_spectrum).continuousOn _
  have e : cfc Real.log σ = cfc (fun x => Real.log x - Real.log m) σ + algebraMap ℝ _ (Real.log m) := by
    rw [← cfc_add_const (Real.log m) _ σ hcont hσ.isSelfAdjoint]
    congr 1; funext x; ring
  have hnn : 0 ≤ cfc (fun x => Real.log x - Real.log m) σ := by
    apply cfc_nonneg
    intro x hx
    have := hspec x hx
    have := Real.log_le_log hm this
    linarith
  have hpsd := Matrix.nonneg_iff_posSemidef.mp hnn
  rw [Matrix.trace_mul_comm, e, Matrix.add_mul, Matrix.trace_add, Complex.add_re]
  have h1 := g78a_trace_mul_psd_nonneg _ _ hpsd hρ.1
  have h2 : (algebraMap ℝ (Matrix X X ℂ) (Real.log m) * ρ).trace.re = Real.log m := by
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, hρ.2]
    simp
  linarith

open scoped MatrixOrder ComplexOrder in
theorem g78a_negEntropy_nonpos {X : Type*} [Fintype X] [DecidableEq X] (ρ : Matrix X X ℂ)
    (hρ : IsDensityMatrix ρ) : (cfc (fun x : ℝ => x * Real.log x) ρ).trace.re ≤ 0 := by
  have hH := hρ.1.isHermitian
  have hsp : ∀ x ∈ spectrum ℝ ρ, 0 ≤ x ∧ x ≤ 1 := by
    intro x hx
    rw [hH.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    have hnn := hρ.1.eigenvalues_nonneg
    refine ⟨hnn i, ?_⟩
    have ht := hH.trace_eq_sum_eigenvalues
    rw [hρ.2] at ht
    have hs : (∑ j, hH.eigenvalues j) = 1 := by
      have := congrArg Complex.re ht
      simpa [Complex.re_sum] using this.symm
    rw [← hs]
    exact Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
  have hle : cfc (fun x : ℝ => x * Real.log x) ρ ≤ 0 := by
    apply cfc_nonpos
    intro x hx
    obtain ⟨h0, h1⟩ := hsp x hx
    exact mul_nonpos_of_nonneg_of_nonpos h0 (Real.log_nonpos h0 h1)
  have hpsd : (0 - cfc (fun x : ℝ => x * Real.log x) ρ).PosSemidef := hle
  have := hpsd.trace_nonneg
  rw [zero_sub, Matrix.trace_neg] at this
  have := (Complex.nonneg_iff.mp this).1
  simp at this
  linarith

open scoped Matrix.Norms.L2Operator in
lemma g78a_specNorm_le {X : Type*} [Fintype X] [DecidableEq X] (A : Matrix X X ℂ)
    (hA : A.IsHermitian) (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ x ∈ spectrum ℝ A, |x| ≤ M) :
    specNorm A ≤ M := by
  unfold specNorm
  have hsa : IsSelfAdjoint A := hA.isSelfAdjoint
  have h1 := hsa.toReal_spectralRadius_complex_eq_norm
  have h2 : spectralRadius ℂ A ≤ ENNReal.ofReal M := by
    apply iSup₂_le
    intro z hz
    have hz' := hsa.mem_spectrum_eq_re hz
    have hre : z.re ∈ spectrum ℝ A := by
      rw [← spectrum.preimage_algebraMap ℂ, Set.mem_preimage]
      rw [Complex.coe_algebraMap, ← hz']; exact hz
    have := hM _ hre
    rw [hz']
    rw [show ((‖((z.re : ℂ))‖₊ : NNReal) : ENNReal) = ENNReal.ofReal |z.re| by
      rw [← Real.norm_eq_abs, ← Complex.norm_real]; rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]; rfl]
    exact ENNReal.ofReal_le_ofReal this
  rw [← h1]
  exact ENNReal.toReal_le_of_le_ofReal hM0 h2

lemma g78a_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma g78a_traceNorm_herm {X : Type*} [Fintype X] [DecidableEq X] (A : Matrix X X ℂ)
    (hA : A.IsHermitian) : traceNorm A = ∑ i, |hA.eigenvalues i| := by
  unfold traceNorm
  have hsa : IsSelfAdjoint A := hA.isSelfAdjoint
  have e1 : Aᴴ * A = cfc (fun x : ℝ => x * x) A := by
    rw [hA.eq, cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) A, cfc_id' ℝ A]
  have hc : ContinuousOn (fun x : ℝ => x * x) (spectrum ℝ A) :=
    (Matrix.finite_real_spectrum).continuousOn _
  rw [e1, ← cfc_comp Real.sqrt (fun x : ℝ => x * x) A, g78a_cfc_trace hA, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Real.sqrt_mul_self_eq_abs]

/-- PDF pp.3–4, Lemma 4: traceless Hermitian matrices have the factor two. -/
theorem solution {d : ℕ} (hd : 0 < d) (A : Mat d)
    (hA : A.IsHermitian) (htrace : A.trace = 0) :
    2 * specNorm A ≤ traceNorm A := by
  set ev := hA.eigenvalues with hev
  have hsum : ∑ i, ev i = 0 := by
    have ht := hA.trace_eq_sum_eigenvalues
    rw [htrace] at ht
    have := congrArg Complex.re ht
    simpa [Complex.re_sum] using this.symm
  have hbound : ∀ i, 2 * |ev i| ≤ ∑ j, |ev j| := by
    intro i
    have h1 := Finset.add_sum_erase Finset.univ ev (Finset.mem_univ i)
    have h2 := Finset.add_sum_erase Finset.univ (fun j => |ev j|) (Finset.mem_univ i)
    have h3 : |∑ j ∈ Finset.univ.erase i, ev j| ≤ ∑ j ∈ Finset.univ.erase i, |ev j| :=
      Finset.abs_sum_le_sum_abs _ _
    have h4 : ev i = -∑ j ∈ Finset.univ.erase i, ev j := by linarith
    have h5 : |ev i| ≤ ∑ j ∈ Finset.univ.erase i, |ev j| := by rw [h4, abs_neg]; exact h3
    linarith
  rw [g78a_traceNorm_herm A hA]
  have hM0 : 0 ≤ (∑ j, |ev j|) / 2 := by positivity
  have := g78a_specNorm_le A hA _ hM0 (by
    intro x hx
    rw [hA.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    have := hbound i
    linarith)
  linarith



end
