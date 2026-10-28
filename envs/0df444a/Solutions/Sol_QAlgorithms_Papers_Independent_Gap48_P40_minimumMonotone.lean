-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P40.minimumMonotone
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T01:23:03.047849+00:00
-- url     : https://prove2.me/submissions/1f4bc855-b766-42cf-bce4-7bb11b04c628

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_distanceSpectralFloor
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_addPositiveDecreasesEntropy

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

set_option linter.unusedSectionVars false
section S196M_gen

open Matrix Polynomial

variable {X K : Type*} [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K]

def S196M_conj (W : Matrix X K ℂ) (h1 : Wᴴ * W = 1) (h2 : W * Wᴴ = 1) :
    Matrix K K ℂ →ₐ[ℝ] Matrix X X ℂ where
  toFun M := W * M * Wᴴ
  map_one' := by rw [Matrix.mul_one, h2]
  map_mul' M N := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Wᴴ W, h1, Matrix.one_mul]
  map_zero' := by simp
  map_add' M N := by simp [Matrix.mul_add, Matrix.add_mul]
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, h2]

lemma S196M_herm (W : Matrix X K ℂ) (d : K → ℝ) :
    (W * diagonal (fun k => (d k : ℂ)) * Wᴴ).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose,
    Matrix.mul_assoc]
  congr 3
  funext k
  simp

lemma S196M_cfc (W : Matrix X K ℂ) (h1 : Wᴴ * W = 1) (h2 : W * Wᴴ = 1) (d : K → ℝ)
    (f : ℝ → ℝ) :
    cfc f (W * diagonal (fun k => (d k : ℂ)) * Wᴴ) =
      W * diagonal (fun k => (f (d k) : ℂ)) * Wᴴ := by
  have hσ := S196M_herm W d
  set σ := W * diagonal (fun k => (d k : ℂ)) * Wᴴ with hσdef
  set s : Finset ℝ := Finset.univ.image d ∪ Finset.univ.image hσ.eigenvalues with hs
  set p : ℝ[X] := Lagrange.interpolate s id f with hpdef
  have hp : ∀ x ∈ s, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) _ (Set.injOn_id _) hx
  rw [cfc_congr (g := fun x => p.eval x) (fun x hx => (hp x ?_).symm),
    cfc_polynomial p σ hσ.isSelfAdjoint]
  · have : σ = S196M_conj W h1 h2 (diagonalAlgHom ℝ (fun k => (d k : ℂ))) := rfl
    rw [this, Polynomial.aeval_algHom_apply, Polynomial.aeval_algHom_apply]
    change W * (diagonalAlgHom ℝ ((aeval fun k => (d k : ℂ)) p)) * Wᴴ = _
    congr 2
    change diagonal _ = _
    congr 1
    funext k
    rw [Polynomial.aeval_pi_apply₂]
    rw [show ((d k : ℂ)) = algebraMap ℝ ℂ (d k) from rfl,
      Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, hp _ (by simp [hs])]
    rfl
  · rw [hσ.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    simp [hs]

lemma S196M_tr (ρ : Matrix X X ℂ) (W : Matrix X K ℂ) (e : K → ℂ) :
    (ρ * (W * diagonal e * Wᴴ)).trace = ∑ k, (Wᴴ * ρ * W) k k * e k := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag, mul_diagonal]

lemma S196M_ker (ρ : Matrix X X ℂ) (hρ : ρ.PosSemidef) (W : Matrix X K ℂ) (h1 : Wᴴ * W = 1)
    (h2 : W * Wᴴ = 1) (d : K → ℝ) (H0 : ∀ k, d k = 0 → (Wᴴ * ρ * W) k k = 0) :
    LinearMap.ker (W * diagonal (fun k => (d k : ℂ)) * Wᴴ).mulVecLin ≤
      LinearMap.ker ρ.mulVecLin := by
  intro v hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  set c := Wᴴ *ᵥ v with hc
  have hdc : ∀ k, (d k : ℂ) * c k = 0 := by
    intro k
    have := congrArg (fun u => Wᴴ *ᵥ u) hv
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, ← Matrix.mulVec_mulVec,
      ← hc] at this
    have := congrFun this k
    simpa [Matrix.mulVec_diagonal] using this
  have hv' : v = W *ᵥ c := by
    rw [hc, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  have hcol : ∀ k, d k = 0 → ρ *ᵥ (fun x => W x k) = 0 := by
    intro k hk
    rw [← hρ.dotProduct_mulVec_zero_iff]
    rw [← H0 k hk]
    simp only [Matrix.mul_apply, conjTranspose_apply, dotProduct, Matrix.mulVec, Pi.star_apply,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [hv', Matrix.mulVec_mulVec]
  funext x
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : d k = 0
  · have := congrFun (hcol k hk) x
    simp only [Matrix.mulVec, dotProduct] at this
    rw [Matrix.mul_apply, this]; simp
  · have : c k = 0 := by
      have := hdc k
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (by exact_mod_cast h) hk
      · exact h
    rw [this, mul_zero]

lemma S196M_klein {I : Type*} [Fintype I] (p : I → ℝ) (d : K → ℝ) (M : I → K → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hd : ∀ k, 0 ≤ d k) (hM : ∀ i k, 0 ≤ M i k)
    (hrow : ∀ i, ∑ k, M i k = 1) (hcol : ∀ k, ∑ i, M i k = 1)
    (hsum : ∑ i, p i = ∑ k, d k) (H : ∀ k, d k = 0 → ∑ i, M i k * p i = 0) :
    ∑ k, (∑ i, M i k * p i) * Real.log (d k) ≤ ∑ i, p i * Real.log (p i) := by
  have hpt : ∀ i k, M i k * (p i - d k) ≤
      M i k * (p i * Real.log (p i)) - M i k * p i * Real.log (d k) := by
    intro i k
    rcases (hp i).lt_or_eq with hpi | hpi
    · rcases (hd k).lt_or_eq with hdk | hdk
      · have hl := Real.log_le_sub_one_of_pos (div_pos hdk hpi)
        rw [Real.log_div hdk.ne' hpi.ne'] at hl
        have : p i - d k ≤ p i * Real.log (p i) - p i * Real.log (d k) := by
          have h3 : p i * (Real.log (d k) - Real.log (p i)) ≤ p i * (d k / p i - 1) :=
            mul_le_mul_of_nonneg_left hl hpi.le
          rw [mul_sub, mul_sub, mul_div_cancel₀ _ hpi.ne', mul_one] at h3
          linarith
        have := mul_le_mul_of_nonneg_left this (hM i k)
        linarith
      · have h0 := H k hdk.symm
        have hz : M i k * p i = 0 := by
          have hnn : ∀ i' ∈ Finset.univ, 0 ≤ M i' k * p i' := fun i' _ =>
            mul_nonneg (hM i' k) (hp i')
          exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 i (Finset.mem_univ _)
        have hMz : M i k = 0 := by
          rcases mul_eq_zero.1 hz with h | h
          · exact h
          · exact absurd h hpi.ne'
        simp [hMz]
    · rw [← hpi]
      simp only [zero_sub, zero_mul, Real.log_zero, mul_zero, sub_zero, mul_neg]
      exact neg_nonpos.2 (mul_nonneg (hM i k) (hd k))
  have hR : ∑ i, p i * Real.log (p i) = ∑ i, ∑ k, M i k * (p i * Real.log (p i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, hrow i, one_mul]
  have hL : ∑ k, (∑ i, M i k * p i) * Real.log (d k) =
      ∑ i, ∑ k, M i k * p i * Real.log (d k) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
  have h0 : ∑ i, ∑ k, M i k * (p i - d k) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun i k => M i k * d k)]
    simp only [← Finset.sum_mul, hrow, hcol, one_mul]
    rw [hsum]; simp
  rw [hR, hL]
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hpt i k
  simp only [Finset.sum_sub_distrib] at this
  linarith


lemma S196M_cfc_trace {Y : Matrix X X ℂ} (hY : Y.IsHermitian) (f : ℝ → ℝ) :
    (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma S196M_vn_eig {Y : Matrix X X ℂ} (hY : Y.IsHermitian) :
    QAlgorithms.vnEntropy Y = (∑ i, Real.negMulLog (hY.eigenvalues i)) / Real.log 2 := by
  unfold QAlgorithms.vnEntropy
  rw [S196M_cfc_trace hY, Complex.re_sum, Finset.sum_div]
  simp only [Complex.ofReal_re]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Real.negMulLog, Real.logb]; ring_nf

lemma S196M_relW (ρ : Matrix X X ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) (W : Matrix X K ℂ)
    (h1 : Wᴴ * W = 1) (h2 : W * Wᴴ = 1) (d : K → ℝ) (hd : ∀ k, 0 ≤ d k)
    (hdsum : ∑ k, d k = 1) (H0 : ∀ k, d k = 0 → (Wᴴ * ρ * W) k k = 0) :
    QAlgorithms.IsDensityMatrix (W * diagonal (fun k => (d k : ℂ)) * Wᴴ) ∧
    LinearMap.ker (W * diagonal (fun k => (d k : ℂ)) * Wᴴ).mulVecLin ≤
      LinearMap.ker ρ.mulVecLin ∧
    (cfc (fun x : ℝ => x * Real.log x) ρ -
        ρ * cfc Real.log (W * diagonal (fun k => (d k : ℂ)) * Wᴴ)).trace.re =
      -(QAlgorithms.vnEntropy ρ * Real.log 2) -
        ∑ k, ((Wᴴ * ρ * W) k k).re * Real.log (d k) ∧
    ∑ k, ((Wᴴ * ρ * W) k k).re * Real.log (d k) ≤ -(QAlgorithms.vnEntropy ρ * Real.log 2) := by
  obtain ⟨hpsd, htr⟩ := hρ
  have hH := hpsd.isHermitian
  set p := hH.eigenvalues with hpdef
  set U : Matrix X X ℂ := (hH.eigenvectorUnitary : Matrix X X ℂ) with hU
  have hU1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2
  have hU2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
  have hρU : ρ = U * diagonal (fun i => (p i : ℂ)) * Uᴴ := by
    conv_lhs => rw [hH.spectral_theorem]
    rfl
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hvn : QAlgorithms.vnEntropy ρ * Real.log 2 = -∑ i, p i * Real.log (p i) := by
    rw [S196M_vn_eig hH, div_mul_cancel₀ _ hl2.ne', ← Finset.sum_neg_distrib]
    simp [Real.negMulLog, hpdef]
  have hplog : (cfc (fun x : ℝ => x * Real.log x) ρ).trace.re = ∑ i, p i * Real.log (p i) := by
    rw [S196M_cfc_trace hH, Complex.re_sum]
    simp [hpdef]
  have hlog : (ρ * cfc Real.log (W * diagonal (fun k => (d k : ℂ)) * Wᴴ)).trace.re =
      ∑ k, ((Wᴴ * ρ * W) k k).re * Real.log (d k) := by
    rw [S196M_cfc W h1 h2, S196M_tr, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp
  -- Klein
  set B := Uᴴ * W with hB
  have hE : ∀ z : ℂ, star z * z = (Complex.normSq z : ℂ) := fun z => by
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  have hr : ∀ k, ((Wᴴ * ρ * W) k k).re = ∑ i, Complex.normSq (B i k) * p i := by
    intro k
    have : Wᴴ * ρ * W = Bᴴ * diagonal (fun i => (p i : ℂ)) * B := by
      rw [hρU, hB, conjTranspose_mul, conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc]
    rw [this, Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_diagonal, conjTranspose_apply,
      show star (B i k) * (p i : ℂ) * B i k = (star (B i k) * B i k) * (p i : ℂ) by ring, hE,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  have hBB1 : B * Bᴴ = 1 := by
    rw [hB, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc W, h2, Matrix.one_mul, hU1]
  have hBB2 : Bᴴ * B = 1 := by
    rw [hB, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc U, hU2, Matrix.one_mul, h1]
  have hrow : ∀ i, ∑ k, Complex.normSq (B i k) = 1 := by
    intro i
    have := congrArg Complex.re (congrFun (congrFun hBB1 i) i)
    rw [Matrix.mul_apply, Complex.re_sum] at this
    simp only [Matrix.one_apply_eq, Complex.one_re] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [conjTranspose_apply, mul_comm (B i k), hE, Complex.ofReal_re]
  have hcol : ∀ k, ∑ i, Complex.normSq (B i k) = 1 := by
    intro k
    have := congrArg Complex.re (congrFun (congrFun hBB2 k) k)
    rw [Matrix.mul_apply, Complex.re_sum] at this
    simp only [Matrix.one_apply_eq, Complex.one_re] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [conjTranspose_apply, hE, Complex.ofReal_re]
  have hpsum : ∑ i, p i = 1 := by
    have := congrArg Complex.re hH.trace_eq_sum_eigenvalues
    rw [htr] at this; simpa [hpdef] using this.symm
  have hK := S196M_klein p d (fun i k => Complex.normSq (B i k)) hpsd.eigenvalues_nonneg hd
    (fun i k => Complex.normSq_nonneg _) hrow hcol (by rw [hpsum, hdsum])
    (fun k hk => by rw [← hr, H0 k hk, Complex.zero_re])
  refine ⟨⟨?_, ?_⟩, S196M_ker ρ hpsd W h1 h2 d H0, ?_, ?_⟩
  · apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    rw [Matrix.posSemidef_diagonal_iff]
    intro k
    exact_mod_cast hd k
  · rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.trace_diagonal]
    exact_mod_cast hdsum
  · rw [Matrix.trace_sub, Complex.sub_re, hplog, hlog, hvn]; ring
  · simp only [hr]
    rw [hvn, neg_neg]
    exact hK

end S196M_gen

open Matrix in
lemma S196M_klein_gen {d : ℕ} (ρ σ : Mat d) (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) :
    0 ≤ relativeEntropy ρ σ := by
  unfold relativeEntropy
  split_ifs with hs
  swap; · exact le_top
  have hH := hσ.1.isHermitian
  set W : Mat d := (hH.eigenvectorUnitary : Mat d) with hW
  have h1 : Wᴴ * W = 1 := Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2
  have h2 : W * Wᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
  have hσW : σ = W * diagonal (fun i => (hH.eigenvalues i : ℂ)) * Wᴴ := by
    conv_lhs => rw [hH.spectral_theorem]
    rfl
  have hsum : ∑ k, hH.eigenvalues k = 1 := by
    have := congrArg Complex.re hH.trace_eq_sum_eigenvalues
    rw [hσ.2] at this; simpa using this.symm
  have H0 : ∀ k, hH.eigenvalues k = 0 → (Wᴴ * ρ * W) k k = 0 := by
    intro k hk
    have hv : σ *ᵥ (fun x => W x k) = 0 := by
      have hsw : σ * W = W * diagonal (fun i => (hH.eigenvalues i : ℂ)) := by
        conv_lhs => rw [hσW]
        rw [Matrix.mul_assoc, h1, Matrix.mul_one]
      funext x
      have := congrFun (congrFun hsw x) k
      rw [Matrix.mul_apply, Matrix.mul_diagonal, hk] at this
      simpa [Matrix.mulVec, dotProduct] using this
    have hv2 : ρ *ᵥ (fun x => W x k) = 0 := by
      have := hs (show (fun x => W x k) ∈ LinearMap.ker σ.mulVecLin by simpa using hv)
      simpa using this
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun x _ => ?_
    have := congrFun hv2 x
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
    rw [Matrix.mul_apply, this, mul_zero]
  obtain ⟨-, -, htr, hle⟩ := S196M_relW ρ hρ W h1 h2 hH.eigenvalues hσ.1.eigenvalues_nonneg hsum H0
  rw [← hσW] at htr
  rw [htr]
  exact_mod_cast (by linarith : (0:ℝ) ≤ _)

open Matrix in
lemma S196M_smul_conj {d : ℕ} (W : Mat d) (q : Fin d → ℝ) (t : ℝ) :
    (t : ℂ) • (W * diagonal (fun k => (q k : ℂ)) * Wᴴ) =
      W * diagonal (fun k => ((t * q k : ℝ) : ℂ)) * Wᴴ := by
  have : diagonal (fun k => ((t * q k : ℝ) : ℂ)) = (t : ℂ) • diagonal (fun k => (q k : ℂ)) := by
    ext i j; by_cases h : i = j <;> simp [h]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

open Matrix in
lemma S196M_trconj {d : ℕ} (W : Mat d) (h1 : Wᴴ * W = 1) (e : Fin d → ℂ) :
    (W * diagonal e * Wᴴ).trace = ∑ k, e k := by
  rw [Matrix.trace_mul_cycle, h1, Matrix.one_mul, Matrix.trace_diagonal]

open Matrix in
lemma S196M_scale_W {d : ℕ} (U W : Mat d) (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1)
    (h1 : Wᴴ * W = 1) (h2 : W * Wᴴ = 1) (p q : Fin d → ℝ)
    (H0 : ∀ k, q k = 0 → (Wᴴ * (U * diagonal (fun i => (p i : ℂ)) * Uᴴ) * W) k k = 0)
    (t : ℝ) (ht : 0 < t) :
    (cfc (fun x : ℝ => x * Real.log x) ((t : ℂ) • (U * diagonal (fun i => (p i : ℂ)) * Uᴴ)) -
        ((t : ℂ) • (U * diagonal (fun i => (p i : ℂ)) * Uᴴ)) *
          cfc Real.log ((t : ℂ) • (W * diagonal (fun k => (q k : ℂ)) * Wᴴ))).trace =
      (t : ℂ) * (cfc (fun x : ℝ => x * Real.log x) (U * diagonal (fun i => (p i : ℂ)) * Uᴴ) -
        (U * diagonal (fun i => (p i : ℂ)) * Uᴴ) *
          cfc Real.log (W * diagonal (fun k => (q k : ℂ)) * Wᴴ)).trace := by
  set ρ := U * diagonal (fun i => (p i : ℂ)) * Uᴴ with hρ
  set M := Wᴴ * ρ * W with hM
  have hMs : ∑ k, M k k = ∑ i, (p i : ℂ) := by
    have : M.trace = ρ.trace := by
      rw [hM, Matrix.trace_mul_cycle, h2, Matrix.one_mul]
    rw [hρ, S196M_trconj U hU1] at this
    simpa [Matrix.trace] using this
  have hMt : Wᴴ * ((t : ℂ) • ρ) * W = (t : ℂ) • M := by
    rw [hM, Matrix.mul_smul, Matrix.smul_mul]
  rw [S196M_smul_conj, S196M_smul_conj, S196M_cfc U hU1 hU2, S196M_cfc W h1 h2,
    S196M_cfc U hU1 hU2, S196M_cfc W h1 h2, Matrix.trace_sub, Matrix.trace_sub,
    S196M_trconj U hU1, S196M_trconj U hU1, ← S196M_smul_conj, S196M_tr, S196M_tr, hMt, ← hM]
  have e1 : ∀ i, (((t * p i) * Real.log (t * p i) : ℝ) : ℂ) =
      (t : ℂ) * ((p i * Real.log (p i) : ℝ) : ℂ) + (t : ℂ) * (Real.log t : ℂ) * (p i : ℂ) := by
    intro i
    by_cases hp : p i = 0
    · simp [hp]
    · rw [Real.log_mul ht.ne' hp]; push_cast; ring
  have e2 : ∀ k, ((t : ℂ) • M) k k * ((Real.log (t * q k) : ℝ) : ℂ) =
      (t : ℂ) * (M k k * ((Real.log (q k) : ℝ) : ℂ)) + (t : ℂ) * (Real.log t : ℂ) * M k k := by
    intro k
    by_cases hq : q k = 0
    · have := H0 k hq
      simp [hq, this]
    · rw [Real.log_mul ht.ne' hq, Matrix.smul_apply, smul_eq_mul]; push_cast; ring
  simp only [e1, e2, Finset.sum_add_distrib, ← Finset.mul_sum, hMs]
  ring

open Matrix in
lemma S196M_col {d : ℕ} (ρ σ : Mat d) (hH : σ.IsHermitian)
    (hs : QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported ρ σ) (k : Fin d)
    (hk : hH.eigenvalues k = 0) :
    ρ *ᵥ (fun x => (hH.eigenvectorUnitary : Mat d) x k) = 0 := by
  set W : Mat d := (hH.eigenvectorUnitary : Mat d) with hW
  have h1 : Wᴴ * W = 1 := Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2
  have hσW : σ = W * diagonal (fun i => (hH.eigenvalues i : ℂ)) * Wᴴ := by
    conv_lhs => rw [hH.spectral_theorem]
    rfl
  have hv : σ *ᵥ (fun x => W x k) = 0 := by
    have hsw : σ * W = W * diagonal (fun i => (hH.eigenvalues i : ℂ)) := by
      conv_lhs => rw [hσW]
      rw [Matrix.mul_assoc, h1, Matrix.mul_one]
    funext x
    have := congrFun (congrFun hsw x) k
    rw [Matrix.mul_apply, Matrix.mul_diagonal, hk] at this
    simpa [Matrix.mulVec, dotProduct] using this
  have := hs (show (fun x => W x k) ∈ LinearMap.ker σ.mulVecLin by simpa using hv)
  simpa using this

lemma S196M_ker_smul {d : ℕ} (A : Mat d) (t : ℝ) (ht : t ≠ 0) :
    LinearMap.ker ((t : ℂ) • A).mulVecLin = LinearMap.ker A.mulVecLin := by
  ext v
  simp [Matrix.smul_mulVec, smul_eq_zero, ht]

open Matrix in
lemma S196M_scale_le {d : ℕ} (ρ σ : Mat d) (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    relativeEntropy ((t : ℂ) • ρ) ((t : ℂ) • σ) ≤ relativeEntropy ρ σ := by
  have hK := S196M_klein_gen ρ σ hρ hσ
  have hsupp : QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported ((t : ℂ) • ρ)
      ((t : ℂ) • σ) ↔ QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported ρ σ := by
    unfold QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported
    rw [S196M_ker_smul _ _ ht0.ne', S196M_ker_smul _ _ ht0.ne']
  by_cases hs : QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported ρ σ
  swap
  · unfold relativeEntropy; rw [if_neg hs, if_neg (by rwa [hsupp])]
  unfold relativeEntropy at hK ⊢
  rw [if_pos hs] at hK
  rw [if_pos hs, if_pos (hsupp.2 hs)]
  have hH := hσ.1.isHermitian
  set W : Mat d := (hH.eigenvectorUnitary : Mat d) with hW
  have h1 : Wᴴ * W = 1 := Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2
  have h2 : W * Wᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
  have hσW : σ = W * diagonal (fun i => (hH.eigenvalues i : ℂ)) * Wᴴ := by
    conv_lhs => rw [hH.spectral_theorem]
    rfl
  have hHρ := hρ.1.isHermitian
  set U : Mat d := (hHρ.eigenvectorUnitary : Mat d) with hU
  have hU1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hHρ.eigenvectorUnitary.2
  have hU2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hHρ.eigenvectorUnitary.2
  have hρU : ρ = U * diagonal (fun i => (hHρ.eigenvalues i : ℂ)) * Uᴴ := by
    conv_lhs => rw [hHρ.spectral_theorem]
    rfl
  have H0 : ∀ k, hH.eigenvalues k = 0 →
      (Wᴴ * (U * diagonal (fun i => (hHρ.eigenvalues i : ℂ)) * Uᴴ) * W) k k = 0 := by
    intro k hk
    rw [← hρU, Matrix.mul_assoc, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun x _ => ?_
    have := congrFun (S196M_col ρ σ hH hs k hk) x
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
    rw [Matrix.mul_apply, this, mul_zero]
  have key := S196M_scale_W U W hU1 hU2 h1 h2 _ _ H0 t ht0
  rw [← hρU, ← hσW] at key
  rw [key, Complex.re_ofReal_mul]
  set r := (cfc (fun x : ℝ => x * Real.log x) ρ - ρ * cfc Real.log σ).trace.re
  have hr : 0 ≤ r := by exact_mod_cast hK
  exact_mod_cast (by nlinarith : t * r ≤ r)

open Matrix in
lemma S196M_self_W {d : ℕ} (U : Mat d) (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) (p : Fin d → ℝ) :
    cfc (fun x : ℝ => x * Real.log x) (U * diagonal (fun i => (p i : ℂ)) * Uᴴ) -
      (U * diagonal (fun i => (p i : ℂ)) * Uᴴ) *
        cfc Real.log (U * diagonal (fun i => (p i : ℂ)) * Uᴴ) = 0 := by
  rw [S196M_cfc U hU1 hU2, S196M_cfc U hU1 hU2, sub_eq_zero]
  have : U * diagonal (fun i => (p i : ℂ)) * Uᴴ * (U * diagonal (fun i => (Real.log (p i) : ℂ)) * Uᴴ)
      = U * (diagonal (fun i => (p i : ℂ)) * diagonal (fun i => (Real.log (p i) : ℂ))) * Uᴴ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hU1, Matrix.one_mul]
  rw [this, diagonal_mul_diagonal]
  congr 2
  funext i
  push_cast; ring

open Matrix in
lemma S196M_self {d : ℕ} (ρ : Mat d) (hρ : ρ.PosSemidef) : relativeEntropy ρ ρ = 0 := by
  unfold relativeEntropy
  rw [if_pos (show QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported ρ ρ from le_refl _)]
  have hHρ := hρ.isHermitian
  set U : Mat d := (hHρ.eigenvectorUnitary : Mat d) with hU
  have hU1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hHρ.eigenvectorUnitary.2
  have hU2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hHρ.eigenvectorUnitary.2
  have hρU : ρ = U * diagonal (fun i => (hHρ.eigenvalues i : ℂ)) * Uᴴ := by
    conv_lhs => rw [hHρ.spectral_theorem]
    rfl
  have key := S196M_self_W U hU1 hU2 hHρ.eigenvalues
  rw [← hρU] at key
  rw [key]; simp

lemma S196M_cpos (r : ℝ) (hr : 0 ≤ r) : (0 : ℂ) ≤ (r : ℂ) := Complex.zero_le_real.mpr hr

open Matrix in
lemma S196M_floor {d : ℕ} (ρ σ : Mat d) (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ)
    (hs : QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported ρ σ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ (σ - (ε : ℂ) • ρ).PosSemidef := by
  have hH := hσ.1.isHermitian
  set W : Mat d := (hH.eigenvectorUnitary : Mat d) with hW
  have h1 : Wᴴ * W = 1 := Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2
  have h2 : W * Wᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
  set q := hH.eigenvalues with hq
  have hσW : σ = W * diagonal (fun i => (q i : ℂ)) * Wᴴ := by
    conv_lhs => rw [hH.spectral_theorem]
    rfl
  have hq0 : ∀ k, 0 ≤ q k := hσ.1.eigenvalues_nonneg
  have hsum : ∑ k, q k = 1 := by
    have := congrArg Complex.re hH.trace_eq_sum_eigenvalues
    rw [hσ.2] at this; simpa [hq] using this.symm
  set S := Finset.univ.filter (fun k => q k ≠ 0) with hS
  have hne : S.Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hc
    have : ∑ k, q k = 0 := Finset.sum_eq_zero fun k hk => by simpa using hc hk
    linarith
  obtain ⟨k0, hk0, hmin⟩ := S.exists_min_image q hne
  set μ := q k0 with hμ
  have hμpos : 0 < μ := lt_of_le_of_ne (hq0 k0) (fun h => by simp [hS] at hk0; exact hk0 h.symm)
  set e : Fin d → ℝ := fun k => if q k = 0 then 0 else 1 with he
  set P := W * diagonal (fun k => (e k : ℂ)) * Wᴴ with hP
  have hPh : Pᴴ = P := S196M_herm W e
  -- ρ * W * diag e = ρ * W
  have hρWe : ρ * W * diagonal (fun k => (e k : ℂ)) = ρ * W := by
    ext x k
    rw [Matrix.mul_diagonal]
    by_cases hk : q k = 0
    · have := congrFun (S196M_col ρ σ hH hs k hk) x
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
      rw [Matrix.mul_apply, this, zero_mul]
    · simp [he, hk]
  have hA : ρ * P = ρ := by
    rw [hP, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hρWe, Matrix.mul_assoc, h2, Matrix.mul_one]
  have hB : P * ρ = ρ := by
    have := congrArg Matrix.conjTranspose hA
    rwa [Matrix.conjTranspose_mul, hPh, hρ.1.isHermitian.eq] at this
  have hC : P * P = P := by
    rw [hP]
    have : W * diagonal (fun k => (e k : ℂ)) * Wᴴ * (W * diagonal (fun k => (e k : ℂ)) * Wᴴ)
        = W * (diagonal (fun k => (e k : ℂ)) * diagonal (fun k => (e k : ℂ))) * Wᴴ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Wᴴ W, h1, Matrix.one_mul]
    rw [this, diagonal_mul_diagonal]
    congr 3
    funext k
    by_cases hk : q k = 0 <;> simp [he, hk]
  -- 1 - ρ PSD
  have hD : (1 - ρ).PosSemidef := by
    have hHρ := hρ.1.isHermitian
    set U : Mat d := (hHρ.eigenvectorUnitary : Mat d) with hU
    have hU2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hHρ.eigenvectorUnitary.2
    have hρU : ρ = U * diagonal (fun i => (hHρ.eigenvalues i : ℂ)) * Uᴴ := by
      conv_lhs => rw [hHρ.spectral_theorem]
      rfl
    have hpsum : ∑ i, hHρ.eigenvalues i = 1 := by
      have := congrArg Complex.re hHρ.trace_eq_sum_eigenvalues
      rw [hρ.2] at this; simpa using this.symm
    have hp0 : ∀ i, 0 ≤ hHρ.eigenvalues i := hρ.1.eigenvalues_nonneg
    have : 1 - ρ = U * diagonal (fun i => ((1 - hHρ.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
      have hd : diagonal (fun i => ((1 - hHρ.eigenvalues i : ℝ) : ℂ)) =
          1 - diagonal (fun i => (hHρ.eigenvalues i : ℂ)) := by
        ext i j; by_cases h : i = j <;> simp [diagonal_apply, h, Matrix.one_apply]
      conv_lhs => rw [hρU]
      rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU2]
    rw [this]
    apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    have : hHρ.eigenvalues i ≤ 1 := by
      rw [← hpsum]
      exact Finset.single_le_sum (fun j _ => hp0 j) (Finset.mem_univ i)
    exact S196M_cpos _ (by linarith)
  have hPρ : (P - ρ).PosSemidef := by
    have := hD.mul_mul_conjTranspose_same P
    rwa [hPh, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hB, hC, hA] at this
  have hE : (σ - (μ : ℂ) • P).PosSemidef := by
    have : σ - (μ : ℂ) • P = W * diagonal (fun k => ((q k - μ * e k : ℝ) : ℂ)) * Wᴴ := by
      have hd : diagonal (fun k => ((q k - μ * e k : ℝ) : ℂ)) =
          diagonal (fun k => (q k : ℂ)) - (μ : ℂ) • diagonal (fun k => (e k : ℂ)) := by
        ext i j; by_cases h : i = j <;> simp [diagonal_apply, h]
      rw [hd, Matrix.mul_sub, Matrix.sub_mul, hσW, hP, Matrix.mul_smul, Matrix.smul_mul]
    rw [this]
    apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    rw [Matrix.posSemidef_diagonal_iff]
    intro k
    apply S196M_cpos
    by_cases hk : q k = 0
    · simp [he, hk]
    · have := hmin k (by simp [hS, hk])
      simp [he, hk]; linarith
  refine ⟨min μ (1 / 2), lt_min hμpos (by norm_num), by
    have := min_le_right μ (1 / 2); linarith, ?_⟩
  have heq : σ - ((min μ (1 / 2) : ℝ) : ℂ) • ρ = (σ - (μ : ℂ) • P) + (μ : ℂ) • (P - ρ) +
      ((μ - min μ (1 / 2) : ℝ) : ℂ) • ρ := by
    push_cast
    module
  rw [heq]
  refine (hE.add (hPρ.smul (S196M_cpos _ hμpos.le))).add (hρ.1.smul (S196M_cpos _ ?_))
  have := min_le_left μ (1 / 2); linarith

lemma S196M_NF_pos {d : ℕ} (hd : 2 ≤ d) (N : Mat d → ℝ) (hN : IsUINorm N) :
    0 < N (matrixF d) := by
  refine lt_of_le_of_ne (hN.1 _) (fun h => ?_)
  have h0 := (hN.2.1 _).1 h.symm
  have := congrFun (congrFun h0 ⟨0, by omega⟩) ⟨0, by omega⟩
  simp [matrixF] at this

lemma S196M_top {d : ℕ} (hd : 2 ≤ d) (N : Mat d → ℝ) (hN : IsUINorm N) (ρ σ : Mat d)
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) (h : N (ρ - σ) = N (matrixF d)) :
    relativeEntropy ρ σ = ⊤ := by
  unfold relativeEntropy
  split_ifs with hs
  swap; · rfl
  exfalso
  obtain ⟨ε, hε0, hε1, hpsd⟩ := S196M_floor ρ σ hρ hσ hs
  have hne : ((1 - ε : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show (1 - ε : ℝ) ≠ 0 by linarith)
  set τ := ((1 - ε : ℝ)⁻¹ : ℂ) • (σ - (ε : ℂ) • ρ) with hτ
  have hτd : IsDensityMatrix τ := by
    refine ⟨hpsd.smul (by
      have : (0 : ℝ) ≤ (1 - ε)⁻¹ := inv_nonneg.2 (by linarith)
      exact_mod_cast S196M_cpos _ this), ?_⟩
    rw [hτ, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_smul, hρ.2, hσ.2, smul_eq_mul,
      smul_eq_mul]
    push_cast at hne ⊢
    field_simp
  have hdiff : ρ - σ = ((1 - ε : ℝ) : ℂ) • (ρ - τ) := by
    rw [hτ, smul_sub, smul_smul, mul_inv_cancel₀ hne, one_smul]
    push_cast
    module
  have hfl := distanceSpectralFloor hd N hN ρ τ hρ hτd 0 (by simpa using hτd.1)
  have hpos := S196M_NF_pos hd N hN
  unfold rescaled at hfl
  rw [sub_zero, div_le_one hpos] at hfl
  rw [hdiff, hN.2.2.2.1, Complex.norm_real, Real.norm_of_nonneg (by linarith)] at h
  nlinarith

lemma S196M_dens_exists {d : ℕ} (hd : 0 < d) : ∃ ρ : Mat d, IsDensityMatrix ρ := by
  refine ⟨Matrix.diagonal (fun i => if i = ⟨0, hd⟩ then 1 else 0), ?_, ?_⟩
  · rw [Matrix.posSemidef_diagonal_iff]
    intro i; split_ifs <;> simp
  · rw [Matrix.trace_diagonal]; simp

theorem S196M_main {d : ℕ} (hd : 2 ≤ d) (N : Mat d → ℝ) (hN : IsUINorm N)
    (T1 T2 : ℝ) (hT1 : 0 ≤ T1) (horder : T1 ≤ T2) (hT2 : T2 ≤ N (matrixF d)) :
    minimumAt d N T1 ≤ minimumAt d N T2 ∧
    minimumAt d N 0 = 0 ∧ minimumAt d N (N (matrixF d)) = ⊤ := by
  have hd0 : 0 < d := by omega
  refine ⟨?_, ?_, ?_⟩
  · unfold minimumAt
    refine le_sInf ?_
    rintro b ⟨ρ, σ, hρ, hσ, hN2, rfl⟩
    by_cases hT2F : T2 = N (matrixF d)
    · rw [S196M_top hd N hN ρ σ hρ hσ (hN2.trans hT2F)]; exact le_top
    by_cases hT20 : T2 = 0
    · have : T1 = 0 := by linarith
      exact sInf_le ⟨ρ, σ, hρ, hσ, by rw [hN2, hT20, this], rfl⟩
    have hT2p : 0 < T2 := lt_of_le_of_ne (by linarith) (Ne.symm hT20)
    set t := T1 / T2 with ht
    have ht0 : 0 ≤ t := div_nonneg hT1 hT2p.le
    have ht1 : t ≤ 1 := (div_le_one hT2p).2 horder
    set ρt := (t : ℂ) • ρ + ((1 - t : ℝ) : ℂ) • σ with hρt
    have hρtd : IsDensityMatrix ρt := by
      refine ⟨(hρ.1.smul (S196M_cpos _ ht0)).add (hσ.1.smul (S196M_cpos _ (by linarith))), ?_⟩
      rw [hρt, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hρ.2, hσ.2]
      simp
    have hdiff : ρt - σ = (t : ℂ) • (ρ - σ) := by
      rw [hρt]; push_cast; module
    have hNt : N (ρt - σ) = T1 := by
      rw [hdiff, hN.2.2.2.1, Complex.norm_real, Real.norm_of_nonneg ht0, hN2, ht,
        div_mul_cancel₀ _ hT2p.ne']
    refine le_trans (sInf_le ⟨ρt, σ, hρtd, hσ, hNt, rfl⟩) ?_
    rcases ht0.lt_or_eq with htp | ht00
    · have hσs : σ = (t : ℂ) • σ + ((1 - t : ℝ) : ℂ) • σ := by
        push_cast; module
      have hadd := addPositiveDecreasesEntropy hd0 ((t : ℂ) • ρ) ((t : ℂ) • σ)
        (((1 - t : ℝ) : ℂ) • σ) (hρ.1.smul (S196M_cpos _ ht0)) (hσ.1.smul (S196M_cpos _ ht0))
        (hσ.1.smul (S196M_cpos _ (by linarith)))
      rw [← hσs, ← hρt] at hadd
      exact hadd.trans (S196M_scale_le ρ σ hρ hσ t htp ht1)
    · have : ρt = σ := by rw [hρt, ← ht00]; simp
      rw [this, S196M_self σ hσ.1]
      exact S196M_klein_gen ρ σ hρ hσ
  · unfold minimumAt
    obtain ⟨ρ0, hρ0⟩ := S196M_dens_exists hd0
    apply le_antisymm
    · exact sInf_le ⟨ρ0, ρ0, hρ0, hρ0, by rw [sub_self, (hN.2.1 0).2 rfl], (S196M_self ρ0 hρ0.1).symm⟩
    · refine le_sInf ?_
      rintro b ⟨ρ, σ, hρ, hσ, h0, rfl⟩
      have : ρ = σ := sub_eq_zero.1 ((hN.2.1 _).1 h0)
      rw [this, S196M_self σ hσ.1]
  · unfold minimumAt
    refine eq_top_iff.2 (le_sInf ?_)
    rintro b ⟨ρ, σ, hρ, hσ, h, rfl⟩
    rw [S196M_top hd N hN ρ σ hρ hσ h]

theorem solution {d : ℕ} (hd : 2 ≤ d) (N : Mat d → ℝ) (hN : IsUINorm N)
    (T1 T2 : ℝ) (hT1 : 0 ≤ T1) (horder : T1 ≤ T2) (hT2 : T2 ≤ N (matrixF d)) :
    minimumAt d N T1 ≤ minimumAt d N T2 ∧
    minimumAt d N 0 = 0 ∧ minimumAt d N (N (matrixF d)) = ⊤ := by
  exact S196M_main hd N hN T1 T2 hT1 horder hT2
