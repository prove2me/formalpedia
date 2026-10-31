-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P17.relativeEntropy_le_of_dominated
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-30T11:43:36.782782+00:00
-- url     : https://prove2.me/submissions/775a8728-8ffd-4d9e-afff-02879157513a

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P17

noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy)

namespace P17Dom

open Matrix MatrixOrder

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The trace of a product of two positive semidefinite matrices has nonnegative real part. -/
lemma trace_mul_re_nonneg {A B : Matrix I I ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  obtain ⟨C, rfl⟩ : ∃ C : Matrix I I ℂ, B = Cᴴ * C := by
    obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hB.nonneg
    exact ⟨C, by rw [hC, Matrix.star_eq_conjTranspose]⟩
  have h := (hA.mul_mul_conjTranspose_same C).trace_nonneg
  rw [show (A * (Cᴴ * C)).trace = (C * A * Cᴴ).trace by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]]
  exact (Complex.nonneg_iff.1 h).1

/-- `x log x` of a Hermitian matrix is `X * log X`. -/
lemma cfc_xlogx {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    cfc (fun x : ℝ => x * Real.log x) X = X * cfc Real.log X := by
  have hfin := Matrix.finite_real_spectrum (A := X)
  have hsa : IsSelfAdjoint X := hX
  rw [cfc_mul (fun x : ℝ => x) Real.log X (hfin.continuousOn _) (hfin.continuousOn _),
    cfc_id' ℝ X]

/-- Key estimate: if `0 ≤ ρ ≤ W` with `W` positive definite, then
`Re Tr[ρ log ρ] ≤ Re Tr[ρ log W]`. -/
lemma trace_mul_log_le {rho W : Matrix I I ℂ} (hrho : rho.PosSemidef) (hW : W.PosDef)
    (hle : rho ≤ W) :
    (rho * cfc Real.log rho).trace.re ≤ (rho * cfc Real.log W).trace.re := by
  rcases isEmpty_or_nonempty I with hI | hI
  · simp [Matrix.trace]
  have hfin := Matrix.finite_real_spectrum (A := rho)
  have hsa : IsSelfAdjoint rho := hrho.1
  obtain ⟨m, hm, hmW⟩ := (CFC.exists_pos_algebraMap_le_iff hW.1.isSelfAdjoint).2
    fun x hx => hW.isStrictlyPositive.spectrum_pos hx
  set t := (rho.trace).re with ht
  have ht0 : 0 ≤ t := (Complex.nonneg_iff.1 hrho.trace_nonneg).1
  apply le_of_forall_pos_le_add
  intro η hη
  set δ := η / (t + 1) with hδ
  have hδ0 : 0 < δ := div_pos hη (by linarith)
  set ε := (Real.exp δ - 1) * m with hεdef
  have hexp : 0 < Real.exp δ - 1 := by linarith [Real.add_one_lt_exp hδ0.ne']
  have hε : 0 < ε := mul_pos hexp hm
  have hεmap : algebraMap ℝ (Matrix I I ℂ) ε = (Real.exp δ - 1) • algebraMap ℝ _ m := by
    simp only [hεdef, Algebra.algebraMap_eq_smul_one, mul_smul]
  -- ρ + ε ≤ e^δ W
  have hA : rho + algebraMap ℝ _ ε ≤ Real.exp δ • W := by
    have e1 : Real.exp δ • W = W + (Real.exp δ - 1) • W := by rw [sub_smul, one_smul]; abel
    rw [e1, hεmap]
    exact add_le_add hle (smul_le_smul_of_nonneg_left hmW hexp.le)
  have hposε : IsStrictlyPositive (algebraMap ℝ (Matrix I I ℂ) ε) := by
    exact isStrictlyPositive_algebraMap hε
  have hpos : IsStrictlyPositive (rho + algebraMap ℝ _ ε) :=
    hposε.of_le (le_add_of_nonneg_left hrho.nonneg)
  -- log (ρ + ε) ≤ δ + log W
  have hlog : cfc Real.log (rho + algebraMap ℝ _ ε) ≤ algebraMap ℝ _ δ + cfc Real.log W := by
    have h := CFC.log_le_log hA hpos
    rwa [CFC.log_smul' _ (Real.exp_pos δ) hW.isStrictlyPositive, Real.log_exp] at h
  -- log (ρ + ε) as a function of ρ
  have hL : cfc Real.log (rho + algebraMap ℝ _ ε) = cfc (fun x => Real.log (x + ε)) rho := by
    have e : rho + algebraMap ℝ _ ε = cfc (fun x : ℝ => x + ε) rho := by
      rw [cfc_add_const ε (fun x : ℝ => x) rho, cfc_id' ℝ rho]
    rw [e, ← cfc_comp' Real.log (fun x : ℝ => x + ε) rho
      (Set.Finite.continuousOn (hfin.image _) _) (hfin.continuousOn _)]
  have hstep1 : (rho * cfc Real.log rho).trace.re ≤
      (rho * cfc Real.log (rho + algebraMap ℝ _ ε)).trace.re := by
    have hc : cfc (fun x : ℝ => x * (Real.log (x + ε) - Real.log x)) rho =
        rho * cfc (fun x => Real.log (x + ε)) rho - rho * cfc Real.log rho := by
      rw [cfc_mul (fun x : ℝ => x) _ rho (hfin.continuousOn _) (hfin.continuousOn _),
        cfc_sub _ _ rho (hfin.continuousOn _) (hfin.continuousOn _), cfc_id' ℝ rho, Matrix.mul_sub]
    have hnn : 0 ≤ cfc (fun x : ℝ => x * (Real.log (x + ε) - Real.log x)) rho := by
      apply cfc_nonneg
      intro x hx
      have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hrho.nonneg hx
      rcases hx0.eq_or_lt with h | h
      · simp [← h]
      · exact mul_nonneg h.le (sub_nonneg.2 (Real.log_le_log h (by linarith)))
    have := (Complex.nonneg_iff.1 (Matrix.nonneg_iff_posSemidef.1 hnn).trace_nonneg).1
    rw [hc, Matrix.trace_sub, Complex.sub_re] at this
    rw [hL]; linarith
  have hstep2 : (rho * cfc Real.log (rho + algebraMap ℝ _ ε)).trace.re ≤
      (rho * (algebraMap ℝ _ δ + cfc Real.log W)).trace.re := by
    have hpsd : (algebraMap ℝ _ δ + cfc Real.log W - cfc Real.log (rho + algebraMap ℝ _ ε)).PosSemidef := by
      rw [← Matrix.nonneg_iff_posSemidef, sub_nonneg]; exact hlog
    have := trace_mul_re_nonneg hrho hpsd
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at this
    linarith
  have hstep3 : (rho * (algebraMap ℝ _ δ + cfc Real.log W)).trace.re =
      δ * t + (rho * cfc Real.log W).trace.re := by
    rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re, Algebra.algebraMap_eq_smul_one,
      Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, Complex.real_smul, Complex.re_ofReal_mul]
  have hδt : δ * t ≤ η := by
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
  linarith

theorem dom_main (rho sigma W : Matrix I I ℂ) (hrho : rho.PosSemidef) (hsigma : sigma.PosDef)
    (hWrho : (W - rho).PosSemidef) (hWsigma : (W - sigma).PosSemidef) :
    relativeEntropy rho sigma ≤ relativeEntropy W sigma := by
  have hsupp : ∀ X : Matrix I I ℂ, IsSupported X sigma := by
    intro X v hv
    have hv' : sigma *ᵥ v = 0 := hv
    by_contra hne
    have h0 : v ≠ 0 := by
      rintro rfl; exact hne (by simp)
    have := hsigma.dotProduct_mulVec_pos h0
    rw [hv'] at this
    simp at this
  simp only [relativeEntropy, if_pos (hsupp _)]
  rw [EReal.coe_le_coe_iff]
  have hW : W.PosDef := by simpa using hsigma.add_posSemidef hWsigma
  rw [cfc_xlogx hrho.1, cfc_xlogx hW.1]
  have hσW : sigma ≤ W := Matrix.le_iff.2 hWsigma
  have hρW : rho ≤ W := Matrix.le_iff.2 hWrho
  have hlog2 : (cfc Real.log W - cfc Real.log sigma).PosSemidef := by
    rw [← Matrix.nonneg_iff_posSemidef, sub_nonneg]
    exact CFC.log_le_log hσW hsigma.isStrictlyPositive
  have h2 := trace_mul_re_nonneg hWrho hlog2
  have h1 := trace_mul_log_le hrho hW hρW
  have key : W * cfc Real.log W - W * cfc Real.log sigma =
      (rho * cfc Real.log rho - rho * cfc Real.log sigma) +
      (rho * cfc Real.log W - rho * cfc Real.log rho) +
      (W - rho) * (cfc Real.log W - cfc Real.log sigma) := by noncomm_ring
  rw [key]
  simp only [Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re] at h1 ⊢
  linarith

end P17Dom

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy) in
theorem solution {I : Type*} [Fintype I] [DecidableEq I]
    (rho sigma W : Matrix I I ℂ) (hrho : rho.PosSemidef) (hsigma : sigma.PosDef)
    (hWrho : (W - rho).PosSemidef) (hWsigma : (W - sigma).PosSemidef) :
    relativeEntropy rho sigma ≤ relativeEntropy W sigma :=
  P17Dom.dom_main rho sigma W hrho hsigma hWrho hWsigma

end
