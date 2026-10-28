-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P30.relative_entanglement_nonlocking
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T03:53:27.140192+00:00
-- url     : https://prove2.me/submissions/31e1a897-b402-4e7f-901b-2e1cc0777605

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P30
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P54_local_pinching_penalty
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P20_strongSubadditivity

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder

set_option linter.unusedSectionVars false

namespace S198R
open Matrix Polynomial
open QAlgorithms.Papers.Independent.Information100.P54

section gen
variable {X K : Type*} [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K]

def conjH (W : Matrix X K ℂ) (h1 : Wᴴ * W = 1) (h2 : W * Wᴴ = 1) :
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

lemma herm_W (W : Matrix X K ℂ) (d : K → ℝ) :
    (W * diagonal (fun k => (d k : ℂ)) * Wᴴ).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose,
    Matrix.mul_assoc]
  congr 3
  funext k
  simp

lemma cfc_W (W : Matrix X K ℂ) (h1 : Wᴴ * W = 1) (h2 : W * Wᴴ = 1) (d : K → ℝ)
    (f : ℝ → ℝ) :
    cfc f (W * diagonal (fun k => (d k : ℂ)) * Wᴴ) =
      W * diagonal (fun k => (f (d k) : ℂ)) * Wᴴ := by
  have hσ := herm_W W d
  set σ := W * diagonal (fun k => (d k : ℂ)) * Wᴴ with hσdef
  set s : Finset ℝ := Finset.univ.image d ∪ Finset.univ.image hσ.eigenvalues with hs
  set p : ℝ[X] := Lagrange.interpolate s id f with hpdef
  have hp : ∀ x ∈ s, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) _ (Set.injOn_id _) hx
  rw [cfc_congr (g := fun x => p.eval x) (fun x hx => (hp x ?_).symm),
    cfc_polynomial p σ hσ.isSelfAdjoint]
  · have : σ = conjH W h1 h2 (diagonalAlgHom ℝ (fun k => (d k : ℂ))) := rfl
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

lemma tr_W (ρ : Matrix X X ℂ) (W : Matrix X K ℂ) (e : K → ℂ) :
    (ρ * (W * diagonal e * Wᴴ)).trace = ∑ k, (Wᴴ * ρ * W) k k * e k := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag, mul_diagonal]
lemma ker_W (ρ : Matrix X X ℂ) (hρ : ρ.PosSemidef) (W : Matrix X K ℂ) (h1 : Wᴴ * W = 1)
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

lemma klein_W {I : Type*} [Fintype I] (p : I → ℝ) (d : K → ℝ) (M : I → K → ℝ)
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


lemma cfc_trace {Y : Matrix X X ℂ} (hY : Y.IsHermitian) (f : ℝ → ℝ) :
    (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma vn_eig {Y : Matrix X X ℂ} (hY : Y.IsHermitian) :
    QAlgorithms.vnEntropy Y = (∑ i, Real.negMulLog (hY.eigenvalues i)) / Real.log 2 := by
  unfold QAlgorithms.vnEntropy
  rw [cfc_trace hY, Complex.re_sum, Finset.sum_div]
  simp only [Complex.ofReal_re]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Real.negMulLog, Real.logb]; ring_nf

lemma relW (ρ : Matrix X X ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) (W : Matrix X K ℂ)
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
    rw [vn_eig hH, div_mul_cancel₀ _ hl2.ne', ← Finset.sum_neg_distrib]
    simp [Real.negMulLog, hpdef]
  have hplog : (cfc (fun x : ℝ => x * Real.log x) ρ).trace.re = ∑ i, p i * Real.log (p i) := by
    rw [cfc_trace hH, Complex.re_sum]
    simp [hpdef]
  have hlog : (ρ * cfc Real.log (W * diagonal (fun k => (d k : ℂ)) * Wᴴ)).trace.re =
      ∑ k, ((Wᴴ * ρ * W) k k).re * Real.log (d k) := by
    rw [cfc_W W h1 h2, tr_W, Complex.re_sum]
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
  have hK := klein_W p d (fun i k => Complex.normSq (B i k)) hpsd.eigenvalues_nonneg hd
    (fun i k => Complex.normSq_nonneg _) hrow hcol (by rw [hpsum, hdsum])
    (fun k hk => by rw [← hr, H0 k hk, Complex.zero_re])
  refine ⟨⟨?_, ?_⟩, ker_W ρ hpsd W h1 h2 d H0, ?_, ?_⟩
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


lemma spec_eq (σ : Matrix X X ℂ) (hσ : σ.IsHermitian) :
    σ = (hσ.eigenvectorUnitary : Matrix X X ℂ) * diagonal (fun i => (hσ.eigenvalues i : ℂ)) *
      (hσ.eigenvectorUnitary : Matrix X X ℂ)ᴴ := by
  conv_lhs => rw [hσ.spectral_theorem]
  rfl

lemma cfc_sub {Y : Type*} [Fintype Y] [DecidableEq Y] (σ : Matrix X X ℂ) (hσ : σ.IsHermitian)
    (e : Y ≃ X) (f : ℝ → ℝ) :
    cfc f (σ.submatrix e e) = (cfc f σ).submatrix e e := by
  set U : Matrix X X ℂ := (hσ.eigenvectorUnitary : Matrix X X ℂ)
  have hU1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hσ.eigenvectorUnitary.2
  have hU2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hσ.eigenvectorUnitary.2
  set W : Matrix Y X ℂ := U.submatrix e id
  have hW1 : Wᴴ * W = 1 := by
    rw [← hU1]; ext i j
    simp only [W, Matrix.mul_apply, conjTranspose_apply, submatrix_apply, id]
    exact e.sum_comp (fun x => star (U x i) * U x j)
  have hW2 : W * Wᴴ = 1 := by
    have : W * Wᴴ = (U * Uᴴ).submatrix e e := rfl
    rw [this, hU2, submatrix_one_equiv]
  have hsub : ∀ d : X → ℝ, (U * diagonal (fun i => (d i : ℂ)) * Uᴴ).submatrix e e =
      W * diagonal (fun i => (d i : ℂ)) * Wᴴ := fun d => rfl
  rw [spec_eq σ hσ, hsub, cfc_W W hW1 hW2, cfc_W U hU1 hU2, hsub]

lemma trace_sub {Y : Type*} [Fintype Y] (M : Matrix X X ℂ) (e : Y ≃ X) :
    (M.submatrix e e).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, submatrix_apply]
  exact e.sum_comp (fun i => M i i)

lemma dens_sub {Y : Type*} [Fintype Y] (M : Matrix X X ℂ) (hM : QAlgorithms.IsDensityMatrix M)
    (e : Y ≃ X) : QAlgorithms.IsDensityMatrix (M.submatrix e e) :=
  ⟨hM.1.submatrix _, by rw [trace_sub, hM.2]⟩

lemma ume_sub_le {Y : Type*} [Fintype Y] [DecidableEq Y] (ρ σ : Matrix X X ℂ)
    (hρ : QAlgorithms.IsDensityMatrix ρ) (hσ : QAlgorithms.IsDensityMatrix σ) (e : Y ≃ X)
    (hρ' : QAlgorithms.IsDensityMatrix (ρ.submatrix e e))
    (hσ' : QAlgorithms.IsDensityMatrix (σ.submatrix e e)) :
    QAlgorithms.QuantumLoss.umegakiEntropy (ρ.submatrix e e) (σ.submatrix e e) hρ' hσ' ≤
      QAlgorithms.QuantumLoss.umegakiEntropy ρ σ hρ hσ := by
  unfold QAlgorithms.QuantumLoss.umegakiEntropy
  by_cases hk : LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin
  · have hk' : LinearMap.ker (σ.submatrix e e).mulVecLin ≤
        LinearMap.ker (ρ.submatrix e e).mulVecLin := by
      intro v hv
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
      rw [submatrix_mulVec_equiv] at hv ⊢
      have h0 : σ *ᵥ (v ∘ e.symm) = 0 := by
        funext x
        have := congrFun hv (e.symm x)
        simpa using this
      have h1 := hk (show v ∘ e.symm ∈ LinearMap.ker σ.mulVecLin by simpa using h0)
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h1
      rw [h1]; rfl
    rw [if_pos hk, if_pos hk']
    apply le_of_eq
    congr 2
    rw [cfc_sub ρ hρ.1.1, cfc_sub σ hσ.1.1, submatrix_mul_equiv,
      show ∀ M N : Matrix X X ℂ, M.submatrix e e - N.submatrix e e = (M - N).submatrix e e from
        fun M N => rfl, trace_sub]
  · rw [if_neg hk]; exact le_top

lemma reb_sub_le {Y : Type*} [Fintype Y] [DecidableEq Y] (ρ σ : Matrix X X ℂ) (e : Y ≃ X) :
    relativeEntropyBits (ρ.submatrix e e) (σ.submatrix e e) ≤ relativeEntropyBits ρ σ := by
  unfold relativeEntropyBits
  by_cases h : QAlgorithms.IsDensityMatrix ρ ∧ QAlgorithms.IsDensityMatrix σ
  · rw [dif_pos h, dif_pos ⟨dens_sub ρ h.1 e, dens_sub σ h.2 e⟩]
    gcongr
    exact ume_sub_le _ _ _ _ _ _ _
  · rw [dif_neg h]; exact le_top

end gen

section swap
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [Nonempty I] [Nonempty J]

lemma sep_swap (σ : Matrix (I × J) (I × J) ℂ) (hσ : QAlgorithms.Entanglement.IsSeparableDensity σ) :
    QAlgorithms.Entanglement.IsSeparableDensity
      (σ.submatrix (Equiv.prodComm J I) (Equiv.prodComm J I)) := by
  obtain ⟨q, w, A, B, hw, hs, hd, rfl⟩ := hσ
  refine ⟨q, w, B, A, hw, hs, fun j => ⟨(hd j).2, (hd j).1⟩, ?_⟩
  ext x y
  simp [Matrix.sum_apply, mul_comm]

lemma RE_swap_le (ρ : Matrix (I × J) (I × J) ℂ) :
    relativeEntanglement (ρ.submatrix (Equiv.prodComm J I) (Equiv.prodComm J I)) ≤
      relativeEntanglement ρ := by
  unfold relativeEntanglement
  apply le_sInf
  rintro _ ⟨σ, hσ, rfl⟩
  exact sInf_le_of_le ⟨_, sep_swap σ hσ, rfl⟩ (reb_sub_le ρ σ _)

lemma RE_swap (ρ : Matrix (I × J) (I × J) ℂ) :
    relativeEntanglement (ρ.submatrix (Equiv.prodComm J I) (Equiv.prodComm J I)) =
      relativeEntanglement ρ := by
  apply le_antisymm (RE_swap_le ρ)
  have := RE_swap_le (ρ.submatrix (Equiv.prodComm J I) (Equiv.prodComm J I))
  rw [submatrix_submatrix] at this
  have e : ρ.submatrix (⇑(Equiv.prodComm J I) ∘ ⇑(Equiv.prodComm I J))
      (⇑(Equiv.prodComm J I) ∘ ⇑(Equiv.prodComm I J)) = ρ := by
    ext ⟨a, b⟩ ⟨c, d⟩; rfl
  rw [e] at this; exact this

end swap

lemma kr {a b c d : Type*} (A : Matrix a b ℂ) (B : Matrix c d ℂ) :
    Matrix.kronecker A B = kroneckerMap (· * ·) A B := rfl

section pinch
variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K] [DecidableEq I] [DecidableEq J]

lemma Q_facts (P : Matrix J J ℂ) (hs : Pᴴ = P) (hp : P * P = P) :
    (kronecker (1 : Matrix I I ℂ) P)ᴴ = kronecker (1 : Matrix I I ℂ) P ∧
    kronecker (1 : Matrix I I ℂ) P * kronecker (1 : Matrix I I ℂ) P =
      kronecker (1 : Matrix I I ℂ) P := by
  simp only [kr]
  constructor
  · rw [conjTranspose_kronecker, conjTranspose_one, hs]
  · rw [← mul_kronecker_mul, Matrix.mul_one, hp]

lemma trQ (P : Matrix J J ℂ) (hs : Pᴴ = P) (hp : P * P = P) (ρ : Matrix (I × J) (I × J) ℂ) :
    ((kronecker (1 : Matrix I I ℂ) P) * ρ * (kronecker (1 : Matrix I I ℂ) P)ᴴ).trace =
      ((kronecker (1 : Matrix I I ℂ) P) * ρ).trace := by
  obtain ⟨h1, h2⟩ := Q_facts (I := I) P hs hp
  rw [h1, Matrix.trace_mul_cycle, h2]

lemma sumQ (P : K → Matrix J J ℂ) (hc : ∑ k, P k = 1) :
    ∑ k, kronecker (1 : Matrix I I ℂ) (P k) = 1 := by
  have : ∑ k, kronecker (1 : Matrix I I ℂ) (P k) = kronecker (1 : Matrix I I ℂ) (∑ k, P k) := by
    ext x y; simp [Matrix.sum_apply, Matrix.kronecker_apply, Finset.mul_sum]
  rw [this, hc, kr, one_kronecker_one]

lemma pinch_dens (ρ : Matrix (I × J) (I × J) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ)
    (P : K → Matrix J J ℂ) (hs : ∀ k, (P k)ᴴ = P k) (hp : ∀ k, P k * P k = P k)
    (hc : ∑ k, P k = 1) : QAlgorithms.IsDensityMatrix (bobPinching P ρ) := by
  refine ⟨posSemidef_sum _ fun k _ => hρ.1.mul_mul_conjTranspose_same _, ?_⟩
  unfold bobPinching
  rw [trace_sum]
  simp only [trQ _ (hs _) (hp _)]
  rw [← trace_sum, ← Finset.sum_mul, sumQ P hc, Matrix.one_mul, hρ.2]

lemma prob_nonneg (ρ : Matrix (I × J) (I × J) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ)
    (P : Matrix J J ℂ) (hs : Pᴴ = P) (hp : P * P = P) :
    0 ≤ ((kronecker (1 : Matrix I I ℂ) P) * ρ).trace.re := by
  rw [← trQ P hs hp]
  have := (hρ.1.mul_mul_conjTranspose_same (kronecker (1 : Matrix I I ℂ) P)).trace_nonneg
  exact (Complex.nonneg_iff.mp this).1

lemma prob_sum (ρ : Matrix (I × J) (I × J) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ)
    (P : K → Matrix J J ℂ) (hc : ∑ k, P k = 1) :
    ∑ k, ((kronecker (1 : Matrix I I ℂ) (P k)) * ρ).trace.re = 1 := by
  rw [← Complex.re_sum, ← trace_sum, ← Finset.sum_mul, sumQ P hc, Matrix.one_mul, hρ.2,
    Complex.one_re]

end pinch

lemma shannon_le_one (t : Fin 2 → ℝ) (h0 : ∀ k, 0 ≤ t k) (h1 : t 0 + t 1 = 1) :
    shannonEntropy (fun k => ENNReal.ofReal (t k)) ≤ 1 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hle : ∀ k, t k ≤ 1 := by
    intro k; fin_cases k
    · simp; linarith [h0 1]
    · simp; linarith [h0 0]
  have hnn : ∀ k, 0 ≤ -t k * Real.log (t k) / Real.log 2 := fun k =>
    div_nonneg (Real.negMulLog_nonneg (h0 k) (hle k)) hl2.le
  unfold shannonEntropy
  rw [tsum_fintype, Fin.sum_univ_two]
  simp only [ENNReal.toReal_ofReal (h0 _)]
  rw [← ENNReal.ofReal_add (hnn 0) (hnn 1), ENNReal.ofReal_le_one, ← add_div,
    div_le_one hl2]
  have := Real.binEntropy_le_log_two (p := t 0)
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, show 1 - t 0 = t 1 by linarith] at this
  simpa [Real.negMulLog] using this

section fin
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [Nonempty I] [Nonempty J]

lemma mm_dens (L : Type*) [Fintype L] [DecidableEq L] [Nonempty L] :
    QAlgorithms.IsDensityMatrix (((Fintype.card L : ℝ)⁻¹ : ℂ) • (1 : Matrix L L ℂ)) := by
  have hc : (0 : ℝ) < Fintype.card L := by exact_mod_cast Fintype.card_pos
  refine ⟨Matrix.PosSemidef.one.smul (by exact_mod_cast (inv_pos.2 hc).le), ?_⟩
  rw [trace_smul, trace_one]
  simp only [smul_eq_mul]
  push_cast
  field_simp

lemma RE_ne_top (ρ : Matrix (I × J) (I × J) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) :
    relativeEntanglement ρ ≠ ⊤ := by
  set a : ℂ := ((Fintype.card I : ℝ)⁻¹ : ℂ)
  set b : ℂ := ((Fintype.card J : ℝ)⁻¹ : ℂ)
  set σ := kronecker (a • (1 : Matrix I I ℂ)) (b • (1 : Matrix J J ℂ))
  have hsep : QAlgorithms.Entanglement.IsSeparableDensity σ :=
    ⟨1, fun _ => 1, fun _ => a • 1, fun _ => b • 1, fun _ => zero_le_one, by simp,
      fun _ => ⟨mm_dens I, mm_dens J⟩, by simp [σ]⟩
  have hσ : QAlgorithms.IsDensityMatrix σ :=
    ⟨(mm_dens I).1.kronecker (mm_dens J).1, by simp only [σ, kr]; rw [trace_kronecker, (mm_dens I).2, (mm_dens J).2, one_mul]⟩
  have hab : a * b ≠ 0 := by
    have : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
    have : (0 : ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos
    simp only [a, b]; norm_cast; positivity
  have hσ1 : σ = (a * b) • (1 : Matrix (I × J) (I × J) ℂ) := by
    simp only [σ, kr, smul_kronecker, kronecker_smul, one_kronecker_one, smul_smul, mul_comm]
  have hker : LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin := by
    intro v hv
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
    rw [hσ1, Matrix.smul_mulVec, Matrix.one_mulVec] at hv
    rw [(smul_eq_zero.mp hv).resolve_left hab, Matrix.mulVec_zero]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply ne_top_of_le_ne_top (b := relativeEntropyBits ρ σ)
  · unfold relativeEntropyBits
    rw [dif_pos ⟨hρ, hσ⟩]
    unfold QAlgorithms.QuantumLoss.umegakiEntropy
    rw [if_pos hker]
    exact ENNReal.div_ne_top ENNReal.ofReal_ne_top (by simpa using hl2)
  · exact sInf_le ⟨σ, hsep, rfl⟩

end fin
end S198R

section S193T_ent
open Matrix Polynomial

lemma S193T_spec_finite {ι : Type*} [Fintype ι] {inst : DecidableEq ι} (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) : (spectrum ℝ A).Finite := by
  rw [hA.spectrum_real_eq_range_eigenvalues]; exact Set.finite_range _

lemma S193T_vn_poly {ι : Type*} [Fintype ι] {inst : DecidableEq ι} (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (p : ℝ[X])
    (hp : ∀ x ∈ spectrum ℝ A, p.eval x = x * Real.logb 2 x) :
    QAlgorithms.vnEntropy A = -(aeval A p).trace.re := by
  unfold QAlgorithms.vnEntropy
  rw [cfc_congr (g := fun x => p.eval x) (fun x hx => (hp x hx).symm),
    cfc_polynomial p A hA.isSelfAdjoint]

/-- interpolation polynomial of x log x on a finite set -/
def S193T_interp (s : Finset ℝ) : ℝ[X] :=
  Lagrange.interpolate s id (fun x => x * Real.logb 2 x)

lemma S193T_interp_eval (s : Finset ℝ) {x : ℝ} (hx : x ∈ s) :
    (S193T_interp s).eval x = x * Real.logb 2 x :=
  Lagrange.eval_interpolate_at_node (v := id) _ (Set.injOn_id _) hx

lemma S193T_vn_submatrix {ι κ : Type*} [Fintype ι] [Fintype κ] {inst : DecidableEq ι}
    {inst' : DecidableEq κ} (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (e : κ ≃ ι) :
    QAlgorithms.vnEntropy (A.submatrix e e) = QAlgorithms.vnEntropy A := by
  set s := (S193T_spec_finite A hA).toFinset
  have hsub : A.submatrix e e = Matrix.reindexAlgEquiv ℝ ℂ e.symm A := by
    ext a b; simp [Matrix.coe_reindexAlgEquiv]
  have hspec : spectrum ℝ (A.submatrix e e) = spectrum ℝ A := by
    rw [hsub]; exact AlgEquiv.spectrum_eq _ _
  rw [S193T_vn_poly A hA (S193T_interp s) (fun x hx => S193T_interp_eval s (by simpa [s] using hx)),
    S193T_vn_poly _ (hA.submatrix e) (S193T_interp s)
      (fun x hx => S193T_interp_eval s (by rw [hspec] at hx; simpa [s] using hx))]
  rw [hsub, Polynomial.aeval_algEquiv, AlgHom.comp_apply]
  congr 2
  simp only [AlgEquiv.coe_toAlgHom, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Equiv.symm_symm, Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact e.sum_comp (fun i => (aeval A (S193T_interp s)) i i)

lemma S193T_vn_conj {ι : Type*} [Fintype ι] {inst : DecidableEq ι} (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) :
    QAlgorithms.vnEntropy (A.map (starRingEnd ℂ)) = QAlgorithms.vnEntropy A := by
  set s := (S193T_spec_finite A hA).toFinset
  set φ : Matrix ι ι ℂ ≃ₐ[ℝ] Matrix ι ι ℂ := AlgEquiv.mapMatrix Complex.conjAe
  have hφ : A.map (starRingEnd ℂ) = φ A := rfl
  have hspec : spectrum ℝ (A.map (starRingEnd ℂ)) = spectrum ℝ A := by
    rw [hφ]; exact AlgEquiv.spectrum_eq _ _
  have hH : (A.map (starRingEnd ℂ)).IsHermitian := by
    ext i j; have := congrFun (congrFun hA i) j
    simp only [conjTranspose_apply, map_apply] at this ⊢
    rw [← this]; simp
  rw [S193T_vn_poly A hA (S193T_interp s) (fun x hx => S193T_interp_eval s (by simpa [s] using hx)),
    S193T_vn_poly _ hH (S193T_interp s)
      (fun x hx => S193T_interp_eval s (by rw [hspec] at hx; simpa [s] using hx))]
  rw [hφ, Polynomial.aeval_algEquiv, AlgHom.comp_apply]
  have htr : ∀ X : Matrix ι ι ℂ, (φ X).trace = starRingEnd ℂ X.trace := by
    intro X
    simp only [φ, AlgEquiv.mapMatrix_apply, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
    rfl
  simp only [AlgEquiv.coe_toAlgHom]
  rw [htr, Complex.conj_re]

lemma S193T_pow_mul {κ ι : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M : Matrix κ ι ℂ) (N : Matrix ι κ ℂ) (k : ℕ) :
    (M * N) ^ (k + 1) = M * (N * M) ^ k * N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]; simp only [Matrix.mul_assoc]

lemma S193T_tr_pow {κ ι : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M : Matrix κ ι ℂ) (N : Matrix ι κ ℂ) (k : ℕ) :
    ((M * N) ^ (k + 1)).trace = ((N * M) ^ (k + 1)).trace := by
  rw [S193T_pow_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, pow_succ]

lemma S193T_vn_mul_comm {κ ι : Type*} [Fintype ι] [Fintype κ] {inst : DecidableEq ι}
    {inst' : DecidableEq κ} (M : Matrix κ ι ℂ) :
    QAlgorithms.vnEntropy (M * Mᴴ) = QAlgorithms.vnEntropy (Mᴴ * M) := by
  have h1 : (M * Mᴴ).IsHermitian := isHermitian_mul_conjTranspose_self M
  have h2 : (Mᴴ * M).IsHermitian := isHermitian_conjTranspose_mul_self M
  set s : Finset ℝ := insert 0 ((S193T_spec_finite (inst := inst') _ h1).toFinset ∪
    (S193T_spec_finite (inst := inst) _ h2).toFinset)
  set p := S193T_interp s
  rw [S193T_vn_poly _ h1 p (fun x hx => S193T_interp_eval s (by simp [s, hx])),
    S193T_vn_poly _ h2 p (fun x hx => S193T_interp_eval s (by simp [s, hx]))]
  have h0 : p.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, S193T_interp_eval s (by simp [s])]; simp
  congr 2
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Matrix.trace_sum,
    Matrix.trace_sum, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [h0, zero_smul, Matrix.trace_zero, add_zero, Matrix.trace_smul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [S193T_tr_pow]

end S193T_ent

section S193T_marg
open Matrix
open scoped Classical
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal)

def S193T_pure {Y : Type*} (Ψ : Y → ℂ) : Matrix Y Y ℂ := Matrix.of fun a b => Ψ a * conj (Ψ b)

def S193T_M {Y K F : Type*} [Fintype Y] (Ψ : Y → ℂ) (k : Y → K) (f : Y → F) : Matrix K F ℂ :=
  fun a z => ∑ y, if k y = a ∧ f y = z then Ψ y else 0

lemma S193T_pure_marg {Y K F : Type*} [Fintype Y] [Fintype F] (Ψ : Y → ℂ) (k : Y → K)
    (f : Y → F) : redistributionMarginal (S193T_pure Ψ) k f =
      S193T_M Ψ k f * (S193T_M Ψ k f)ᴴ := by
  ext a b
  simp only [redistributionMarginal, Matrix.mul_apply, Matrix.conjTranspose_apply, S193T_M,
    S193T_pure, Matrix.of_apply, star_sum, Finset.sum_mul_sum]
  symm
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.sum_eq_single (f x)]
  · by_cases h1 : k x = a <;> by_cases h2 : k y = b <;> by_cases h3 : f x = f y <;>
      simp [h1, h2, h3, eq_comm (a := f y)]
  · intro z _ hz; simp [Ne.symm hz]
  · simp

lemma S193T_ite_sum {α : Type*} (s : Finset α) (c : Prop) [Decidable c] (g : α → ℂ) :
    (if c then ∑ i ∈ s, g i else 0) = ∑ i ∈ s, if c then g i else 0 := by
  split_ifs <;> simp

lemma S193T_marg_comp {Y K F K2 F2 : Type*} [Fintype Y] [Fintype K] (ρ : Matrix Y Y ℂ)
    (k : Y → K) (f : Y → F) (k2 : K → K2) (f2 : K → F2) :
    redistributionMarginal (redistributionMarginal ρ k f) k2 f2 =
      redistributionMarginal ρ (k2 ∘ k) (fun y => (f2 (k y), f y)) := by
  ext a b
  simp only [redistributionMarginal, S193T_ite_sum, Function.comp]
  rw [Finset.sum_congr rfl (fun u _ => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun x _ => Finset.sum_comm))]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  rw [Finset.sum_eq_single (k x)]
  · rw [Finset.sum_eq_single (k y)]
    · by_cases h1 : k2 (k x) = a <;> by_cases h2 : k2 (k y) = b <;>
        by_cases h3 : f2 (k x) = f2 (k y) <;> by_cases h4 : f x = f y <;> simp [h1, h2, h3, h4]
    · intro v _ hv; simp [Ne.symm hv]
    · simp
  · intro u _ hu
    apply Finset.sum_eq_zero; intro v _; simp [Ne.symm hu]
  · simp


lemma S193T_marg_forget {Y K F F' : Type*} [Fintype Y] (ρ : Matrix Y Y ℂ) (k : Y → K)
    (f : Y → F) (f' : Y → F') (hf : ∀ x y, f x = f y ↔ f' x = f' y) :
    redistributionMarginal ρ k f = redistributionMarginal ρ k f' := by
  ext a b
  simp only [redistributionMarginal]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  simp only [hf x y]

lemma S193T_vn_keep {Y K K' F : Type*} [Fintype Y] [Fintype K] [Fintype K']
    {inst : DecidableEq K} {inst' : DecidableEq K'} (ρ : Matrix Y Y ℂ) (k : Y → K)
    (k' : Y → K') (f : Y → F) (hk : ∀ x y, k x = k y ↔ k' x = k' y)
    (hs : Function.Surjective k) (hs' : Function.Surjective k')
    (hH : (redistributionMarginal ρ k' f).IsHermitian) :
    QAlgorithms.vnEntropy (redistributionMarginal ρ k f) =
      QAlgorithms.vnEntropy (redistributionMarginal ρ k' f) := by
  set g : K → K' := fun a => k' (Function.surjInv hs a) with hg
  have hgk : ∀ x a, k' x = g a ↔ k x = a := by
    intro x a
    have := hk x (Function.surjInv hs a)
    rw [Function.surjInv_eq hs a] at this
    exact this.symm
  have hb : Function.Bijective g := by
    constructor
    · intro a b hab
      have h1 := (hgk (Function.surjInv hs a) b).1 hab
      rwa [Function.surjInv_eq hs a] at h1
    · intro c
      obtain ⟨y, rfl⟩ := hs' c
      exact ⟨k y, ((hgk y (k y)).2 rfl).symm⟩
  have hsub : (redistributionMarginal ρ k' f).submatrix (Equiv.ofBijective g hb)
      (Equiv.ofBijective g hb) = redistributionMarginal ρ k f := by
    ext a b
    simp only [Matrix.submatrix_apply, Equiv.ofBijective_apply, redistributionMarginal]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    by_cases h : k x = a ∧ k y = b ∧ f x = f y
    · rw [if_pos (by rwa [hgk, hgk]), if_pos h]
    · rw [if_neg (by rwa [hgk, hgk]), if_neg h]
  rw [← hsub, S193T_vn_submatrix _ hH]

lemma S193T_pure_herm {Y K F : Type*} [Fintype Y] [Fintype F] (Ψ : Y → ℂ) (k : Y → K)
    (f : Y → F) : (redistributionMarginal (S193T_pure Ψ) k f).IsHermitian := by
  rw [S193T_pure_marg]; exact isHermitian_mul_conjTranspose_self _

lemma S193T_vn_swap {Y K F : Type*} [Fintype Y] [Fintype K] [Fintype F]
    {inst : DecidableEq K} {inst' : DecidableEq F} (Ψ : Y → ℂ) (k : Y → K) (f : Y → F) :
    QAlgorithms.vnEntropy (redistributionMarginal (S193T_pure Ψ) k f) =
      QAlgorithms.vnEntropy (redistributionMarginal (S193T_pure Ψ) f k) := by
  rw [S193T_pure_marg, S193T_pure_marg]
  set M := S193T_M Ψ k f
  have hN : S193T_M Ψ f k * (S193T_M Ψ f k)ᴴ = (Mᴴ * M).map (starRingEnd ℂ) := by
    ext z w
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, map_sum, map_mul,
      M, S193T_M]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp only [and_comm, RCLike.star_def, Complex.conj_conj, map_sum]
    congr 1
    · refine Finset.sum_congr rfl (fun y _ => ?_)
      by_cases h : k y = a ∧ f y = z
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]
    · refine Finset.sum_congr rfl (fun y _ => ?_)
      by_cases h : k y = a ∧ f y = w
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]
  rw [hN, S193T_vn_conj _ (isHermitian_conjTranspose_mul_self M), S193T_vn_mul_comm]

lemma S193T_marg_trace {Y K F : Type*} [Fintype Y] [Fintype K] (ρ : Matrix Y Y ℂ)
    (k : Y → K) (f : Y → F) (hinj : Function.Injective (fun y => (k y, f y))) :
    (redistributionMarginal ρ k f).trace = ρ.trace := by
  simp only [Matrix.trace, Matrix.diag, redistributionMarginal]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm, Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single (k x)]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · intro y _ hy
    apply Finset.sum_eq_zero; intro a _
    rw [if_neg]; rintro ⟨h1, h2, h3⟩
    exact hy (hinj (Prod.ext (h2.trans h1.symm) h3.symm))
  · simp

lemma S193T_pure_density {Y K F : Type*} [Fintype Y] [Fintype K] [Fintype F] (Ψ : Y → ℂ)
    (hΨ : (S193T_pure Ψ).trace = 1) (k : Y → K) (f : Y → F)
    (hinj : Function.Injective (fun y => (k y, f y))) :
    QAlgorithms.IsDensityMatrix (redistributionMarginal (S193T_pure Ψ) k f) := by
  refine ⟨?_, ?_⟩
  · rw [S193T_pure_marg]; exact posSemidef_self_mul_conjTranspose _
  · rw [S193T_marg_trace _ _ _ hinj, hΨ]

lemma S193T_vn_unit {inst : DecidableEq Unit} (A : Matrix Unit Unit ℂ) (h : A.trace = 1) :
    QAlgorithms.vnEntropy A = 0 := by
  have : A = 1 := by
    ext a b; cases a; cases b; simpa [Matrix.trace] using h
  rw [this]; simp [QAlgorithms.vnEntropy]
end S193T_marg

section S193T_bridge
open Matrix
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal)

lemma S193T_purify {X : Type*} [Fintype X] [DecidableEq X] (ρ : Matrix X X ℂ)
    (hρ : ρ.PosSemidef) : ∃ Ψ : X × X → ℂ,
      redistributionMarginal (S193T_pure Ψ) Prod.fst Prod.snd = ρ := by
  set U : Matrix X X ℂ := (hρ.1.eigenvectorUnitary : Matrix X X ℂ)
  set lam := hρ.1.eigenvalues
  refine ⟨fun y => U y.1 y.2 * ((Real.sqrt (lam y.2) : ℝ) : ℂ), ?_⟩
  rw [S193T_pure_marg]
  have hM : S193T_M (fun y : X × X => U y.1 y.2 * ((Real.sqrt (lam y.2) : ℝ) : ℂ))
      Prod.fst Prod.snd = U * diagonal (fun j => ((Real.sqrt (lam j) : ℝ) : ℂ)) := by
    ext a j
    simp only [S193T_M, mul_diagonal]
    rw [Finset.sum_eq_single (a, j)]
    · simp
    · intro y _ hy; rw [if_neg]; rintro ⟨h1, h2⟩; exact hy (Prod.ext h1 h2)
    · simp
  rw [hM]
  have hsp := hρ.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hsp
  conv_rhs => rw [hsp]
  rw [conjTranspose_mul, diagonal_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _),
    diagonal_mul_diagonal, ← Matrix.mul_assoc]
  congr 2
  · congr 1; funext j
    simp only [Function.comp, Pi.star_apply, RCLike.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hρ.eigenvalues_nonneg j)]
    rfl

end S193T_bridge

section S193T_AL
open Matrix
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal subsystemEntropy)

lemma S193T_vn_eq {Y K K' F F' : Type*} [Fintype Y] [Fintype K] [Fintype K'] [Fintype F']
    {inst : DecidableEq K} {inst' : DecidableEq K'} (Ψ : Y → ℂ) (k : Y → K) (f : Y → F)
    (k' : Y → K') (f' : Y → F') (hk : ∀ x y, k x = k y ↔ k' x = k' y)
    (hs : Function.Surjective k) (hs' : Function.Surjective k')
    (hf : ∀ x y, f x = f y ↔ f' x = f' y) :
    QAlgorithms.vnEntropy (redistributionMarginal (S193T_pure Ψ) k f) =
      QAlgorithms.vnEntropy (redistributionMarginal (S193T_pure Ψ) k' f') := by
  rw [S193T_marg_forget _ k f f' hf]
  exact S193T_vn_keep _ k k' f' hk hs hs' (S193T_pure_herm _ _ _)


def S193T_S {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) : ℝ :=
  @QAlgorithms.vnEntropy ι _ (Classical.decEq ι) A

lemma S193T_toS {ι : Type*} [Fintype ι] (i : DecidableEq ι) (A : Matrix ι ι ℂ) :
    @QAlgorithms.vnEntropy ι _ i A = S193T_S A := by
  unfold S193T_S; congr

lemma S193T_AL1 {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    {ia : DecidableEq α} {ib : DecidableEq β} {iab : DecidableEq (α × β)}
    (ρ : Matrix (α × β) (α × β) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) :
    QAlgorithms.vnEntropy (redistributionMarginal ρ Prod.fst Prod.snd) ≤
      QAlgorithms.vnEntropy (redistributionMarginal ρ Prod.snd Prod.fst) +
        QAlgorithms.vnEntropy ρ := by
  classical
  obtain ⟨Ψ, hΨ⟩ := S193T_purify ρ hρ.1
  have hinj0 : Function.Injective (fun y : (α × β) × (α × β) => (y.1, y.2)) := by
    intro y y' h; simpa using h
  have htr : (S193T_pure Ψ).trace = 1 := by
    rw [← S193T_marg_trace _ Prod.fst Prod.snd hinj0, hΨ, hρ.2]
  subst hΨ
  rw [S193T_marg_comp, S193T_marg_comp]
  set k : (α × β) × (α × β) → β × ((α × β) × Unit) := fun y => (y.1.2, (y.2, ())) with hk
  set f : (α × β) × (α × β) → α := fun y => y.1.1 with hf
  have hinj : Function.Injective (fun y => (k y, f y)) := by
    intro y y' h
    simp only [hk, hf, Prod.mk.injEq, and_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact Prod.ext (Prod.ext h3 h1) h2
  have hssa := QAlgorithms.Papers.Independent.Gap48.P20.strongSubadditivity
    (redistributionMarginal (S193T_pure Ψ) k f) (S193T_pure_density Ψ htr k f hinj)
  unfold subsystemEntropy at hssa
  rw [S193T_marg_comp, S193T_marg_comp, S193T_marg_comp] at hssa
  obtain ⟨a0⟩ : Nonempty α := inferInstance
  obtain ⟨b0⟩ : Nonempty β := inferInstance
  have h1 : QAlgorithms.vnEntropy (redistributionMarginal (S193T_pure Ψ)
      ((fun p : β × ((α × β) × Unit) => (p.1, p.2.2)) ∘ k)
      (fun y => ((fun p : β × ((α × β) × Unit) => p.2.1) (k y), f y))) =
      QAlgorithms.vnEntropy (redistributionMarginal (S193T_pure Ψ) (Prod.snd ∘ Prod.fst)
        (fun y => (Prod.fst (Prod.fst y), Prod.snd y))) := by
    apply S193T_vn_eq
    · intro y y'; simp [hk]
    · rintro ⟨b, u⟩; exact ⟨((a0, b), (a0, b0)), rfl⟩
    · intro b; exact ⟨((a0, b), (a0, b0)), rfl⟩
    · intro y y'; simp [hk, hf]; tauto
  have h2 : QAlgorithms.vnEntropy (redistributionMarginal (S193T_pure Ψ)
      ((fun p : β × ((α × β) × Unit) => p.2) ∘ k)
      (fun y => ((fun p : β × ((α × β) × Unit) => p.1) (k y), f y))) =
      QAlgorithms.vnEntropy (redistributionMarginal (S193T_pure Ψ) Prod.fst Prod.snd) := by
    rw [S193T_vn_swap (inst' := iab) Ψ Prod.fst Prod.snd]
    apply S193T_vn_eq
    · intro y y'; simp [hk]
    · rintro ⟨e, u⟩; exact ⟨((a0, b0), e), rfl⟩
    · intro e; exact ⟨((a0, b0), e), rfl⟩
    · intro y y'; simp [hk, hf]
      constructor
      · rintro ⟨h1, h2⟩; exact Prod.ext h2 h1
      · intro h; rw [h]; exact ⟨rfl, rfl⟩
  have h3 : QAlgorithms.vnEntropy (redistributionMarginal (S193T_pure Ψ)
      ((fun p : β × ((α × β) × Unit) => p.2.2) ∘ k)
      (fun y => ((fun p : β × ((α × β) × Unit) => (p.1, p.2.1)) (k y), f y))) = 0 := by
    apply S193T_vn_unit
    rw [S193T_marg_trace, htr]
    intro y y' h
    simp only [hk, hf, Function.comp, Prod.mk.injEq, true_and] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact Prod.ext (Prod.ext h3 h1) h2
  have h4 : QAlgorithms.vnEntropy (redistributionMarginal (S193T_pure Ψ) k f) =
      QAlgorithms.vnEntropy (redistributionMarginal (S193T_pure Ψ) (Prod.fst ∘ Prod.fst)
        (fun y => (Prod.snd (Prod.fst y), Prod.snd y))) := by
    rw [S193T_vn_swap (inst' := ia) Ψ k f]
    apply S193T_vn_eq
    · intro y y'; simp [hf]
    · intro a; exact ⟨((a, b0), (a0, b0)), rfl⟩
    · intro a; exact ⟨((a, b0), (a0, b0)), rfl⟩
    · intro y y'; simp [hk]
  beta_reduce at h1 h2 h3
  simp only [S193T_toS] at hssa h1 h2 h3 h4 ⊢
  rw [h1, h2, h3, h4] at hssa
  linarith

lemma S193T_AL2 {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    {ia : DecidableEq α} {ib : DecidableEq β} {iab : DecidableEq (α × β)}
    (ρ : Matrix (α × β) (α × β) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) :
    QAlgorithms.vnEntropy (redistributionMarginal ρ Prod.snd Prod.fst) ≤
      QAlgorithms.vnEntropy (redistributionMarginal ρ Prod.fst Prod.snd) +
        QAlgorithms.vnEntropy ρ := by
  classical
  set e : β × α ≃ α × β := Equiv.prodComm β α
  have hd : QAlgorithms.IsDensityMatrix (ρ.submatrix e e) := by
    refine ⟨hρ.1.submatrix _, ?_⟩
    rw [← hρ.2]; simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
    exact e.sum_comp (fun i => ρ i i)
  have hm1 : redistributionMarginal (ρ.submatrix e e) Prod.fst Prod.snd =
      redistributionMarginal ρ Prod.snd Prod.fst := by
    ext a b
    simp only [redistributionMarginal, Matrix.submatrix_apply]
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← e.sum_comp]
    rfl
  have hm2 : redistributionMarginal (ρ.submatrix e e) Prod.snd Prod.fst =
      redistributionMarginal ρ Prod.fst Prod.snd := by
    ext a b
    simp only [redistributionMarginal, Matrix.submatrix_apply]
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← e.sum_comp]
    rfl
  have := S193T_AL1 (ia := ib) (ib := ia) (iab := inferInstance) (ρ.submatrix e e) hd
  rw [hm1, hm2, S193T_vn_submatrix ρ hρ.1.1 e] at this
  exact this

end S193T_AL


section S198cap
open Matrix
lemma S198_vn_eig2 {ι : Type*} [Fintype ι] {inst : DecidableEq ι} (X : Matrix ι ι ℂ) (hX : X.IsHermitian) :
    QAlgorithms.vnEntropy X = -∑ i, hX.eigenvalues i * Real.logb 2 (hX.eigenvalues i) := by
  unfold QAlgorithms.vnEntropy
  rw [hX.cfc_eq, Matrix.IsHermitian.cfc]
  have hU := hX.eigenvectorUnitary.2
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Matrix.mem_unitaryGroup_iff'.mp hU, Matrix.one_mul, Matrix.trace_diagonal]
  simp

lemma S198_ent_bounds {ι : Type*} [Fintype ι] {inst : DecidableEq ι} (X : Matrix ι ι ℂ) (hX : X.PosSemidef)
    (ht : X.trace = 1) : 0 ≤ QAlgorithms.vnEntropy X ∧ QAlgorithms.vnEntropy X ≤ Real.logb 2 (Fintype.card ι) := by
  rw [S198_vn_eig2 X hX.1]
  set l := hX.1.eigenvalues with hldef
  have hl0 : ∀ i, 0 ≤ l i := hX.eigenvalues_nonneg
  have hl1 : ∑ i, l i = 1 := by
    have h := hX.1.trace_eq_sum_eigenvalues
    rw [ht] at h
    have h' : ((∑ i, l i : ℝ) : ℂ) = 1 := by push_cast; exact h.symm
    exact_mod_cast h'
  have hle : ∀ i, l i ≤ 1 := fun i => by
    rw [← hl1]; exact Finset.single_le_sum (fun j _ => hl0 j) (Finset.mem_univ i)
  have hrw : -∑ i, l i * Real.logb 2 (l i) = (∑ i, Real.negMulLog (l i)) / Real.log 2 := by
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.negMulLog, Real.logb]; ring
  rw [hrw]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun i _ => Real.negMulLog_nonneg (hl0 i) (hle i)) hlog2.le
  · rw [Real.logb, div_le_div_iff_of_pos_right hlog2]
    have hne : Nonempty ι := by
      by_contra h
      rw [not_nonempty_iff] at h
      simp at hl1
    have hd : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have hJ := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
      (w := fun _ => (Fintype.card ι : ℝ)⁻¹)
      (p := l) (fun _ _ => by positivity)
      (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp)
      (fun i _ => Set.mem_Ici.mpr (hl0 i))
    simp only [smul_eq_mul, ← Finset.mul_sum, hl1, mul_one] at hJ
    rw [Real.negMulLog, Real.log_inv] at hJ
    have := mul_le_mul_of_nonneg_left hJ hd.le
    have h2 : (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ)⁻¹ * ∑ i, Real.negMulLog (l i)) =
        ∑ i, Real.negMulLog (l i) := by field_simp
    have h3 : (Fintype.card ι : ℝ) * (-(Fintype.card ι : ℝ)⁻¹ * -Real.log (Fintype.card ι)) =
        Real.log (Fintype.card ι) := by field_simp
    linarith
end S198cap

namespace S198R2
open Matrix
open QAlgorithms.Papers.Independent.Information100.P54
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal)

variable {Y : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y]

def half2 : Matrix (Fin 2) (Fin 2) ℂ := ((1/2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)

lemma half2_dens : QAlgorithms.IsDensityMatrix half2 := by
  refine ⟨Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (by norm_num)), ?_⟩
  rw [half2, trace_smul, trace_one]; norm_num

def blk (M : Matrix (Fin 2 × Y) (Fin 2 × Y) ℂ) (g : Fin 2) : Matrix Y Y ℂ :=
  M.submatrix (fun y => (g, y)) (fun y => (g, y))

def trL (M : Matrix (Fin 2 × Y) (Fin 2 × Y) ℂ) : Matrix Y Y ℂ := ∑ g, blk M g

lemma trL_dens (M : Matrix (Fin 2 × Y) (Fin 2 × Y) ℂ) (hM : QAlgorithms.IsDensityMatrix M) :
    QAlgorithms.IsDensityMatrix (trL M) := by
  refine ⟨posSemidef_sum _ fun g _ => hM.1.submatrix _, ?_⟩
  rw [← hM.2, trL, trace_sum]
  simp only [blk, Matrix.trace, Matrix.diag, submatrix_apply]
  rw [Fintype.sum_prod_type]

lemma blk_entry (M : Matrix (Fin 2 × Y) (Fin 2 × Y) ℂ) (V : Matrix Y Y ℂ) (g : Fin 2) (k : Y) :
    ((kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) V)ᴴ * M * kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) V :
      Matrix (Fin 2 × Y) (Fin 2 × Y) ℂ) (g, k) (g, k) =
      (Vᴴ * blk M g * V) k k := by
  simp only [S198R.kr, conjTranspose_kronecker, conjTranspose_one]
  simp [Matrix.mul_apply, Fintype.sum_prod_type, one_apply, blk]

lemma trL_entry (M : Matrix (Fin 2 × Y) (Fin 2 × Y) ℂ) (V : Matrix Y Y ℂ) (k : Y) :
    (Vᴴ * trL M * V) k k = ∑ g, (Vᴴ * blk M g * V) k k := by
  simp only [trL, Finset.mul_sum, Finset.sum_mul, Matrix.sum_apply]

lemma margSF (M : Matrix (Fin 2 × Y) (Fin 2 × Y) ℂ) :
    redistributionMarginal M Prod.snd Prod.fst = trL M := by
  ext a b
  simp [redistributionMarginal, trL, blk, Matrix.sum_apply, Fintype.sum_prod_type, ite_and]

lemma margFS (M : Matrix (Fin 2 × Y) (Fin 2 × Y) ℂ) :
    redistributionMarginal M Prod.fst Prod.snd =
      ∑ y, M.submatrix (fun f => (f, y)) (fun f => (f, y)) := by
  ext a b
  simp [redistributionMarginal, Matrix.sum_apply, Fintype.sum_prod_type, ite_and]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single x (fun y _ hy => by simp [Ne.symm hy]) (by simp)]
  simp

lemma AL_bound (M : Matrix (Fin 2 × Y) (Fin 2 × Y) ℂ) (hM : QAlgorithms.IsDensityMatrix M) :
    QAlgorithms.vnEntropy (trL M) ≤ QAlgorithms.vnEntropy M + 1 := by
  have h1 := S193T_AL2 (ia := inferInstance) (ib := inferInstance) (iab := inferInstance) M hM
  rw [margSF] at h1
  have hd : QAlgorithms.IsDensityMatrix (redistributionMarginal M Prod.fst Prod.snd) := by
    refine ⟨?_, ?_⟩
    · rw [margFS]; exact posSemidef_sum _ fun y _ => hM.1.submatrix _
    · rw [S193T_marg_trace, hM.2]
      intro x y h; simpa using h
  have h2 := (S198_ent_bounds (inst := inferInstance) _ hd.1 hd.2).2
  rw [Fintype.card_fin, Nat.cast_ofNat, Real.logb_self_eq_one (by norm_num)] at h2
  linarith

lemma key2 (ρ : Matrix (Fin 2 × Y) (Fin 2 × Y) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ)
    (σ' : Matrix Y Y ℂ) (hσ' : QAlgorithms.IsDensityMatrix σ')
    (hker : LinearMap.ker σ'.mulVecLin ≤ LinearMap.ker (trL ρ).mulVecLin) :
    relativeEntropyBits ρ (kronecker half2 σ') ≤ relativeEntropyBits (trL ρ) σ' + 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hH := hσ'.1.1
  set V : Matrix Y Y ℂ := (hH.eigenvectorUnitary : Matrix Y Y ℂ) with hVdef
  set d' := hH.eigenvalues with hd'def
  have hV1 : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2
  have hV2 : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
  have hσV : σ' = V * diagonal (fun i => (d' i : ℂ)) * Vᴴ := S198R.spec_eq σ' hH
  set W : Matrix (Fin 2 × Y) (Fin 2 × Y) ℂ := kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) V with hWdef
  have hW1 : Wᴴ * W = 1 := by
    simp only [W, S198R.kr]
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, hV1, Matrix.one_mul,
      one_kronecker_one]
  have hW2 : W * Wᴴ = 1 := by
    simp only [W, S198R.kr]
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, hV2, Matrix.one_mul,
      one_kronecker_one]
  set d : Fin 2 × Y → ℝ := fun k => d' k.2 / 2 with hddef
  have hτ : kronecker half2 σ' = W * diagonal (fun k => (d k : ℂ)) * Wᴴ := by
    have hD : diagonal (fun k => (d k : ℂ)) = kronecker half2 (diagonal (fun i => (d' i : ℂ))) := by
      ext ⟨a, i⟩ ⟨b, j⟩
      simp only [d, half2, diagonal_apply, Matrix.kronecker, kroneckerMap_apply, Matrix.smul_apply,
        one_apply, Prod.mk.injEq, smul_eq_mul]
      by_cases h1 : a = b <;> by_cases h2 : i = j <;> simp [h1, h2]
      ring
    rw [hD]
    simp only [W, S198R.kr]
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, ← mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one, ← hσV]
  have hr : ∀ g k, (Wᴴ * ρ * W) (g, k) (g, k) = (Vᴴ * blk ρ g * V) k k :=
    fun g k => blk_entry ρ V g k
  have hnn : ∀ g k, 0 ≤ (Vᴴ * blk ρ g * V) k k := fun g k =>
    ((hρ.1.submatrix _).conjTranspose_mul_mul_same V).diag_nonneg
  have hdtr := trL_dens ρ hρ
  have H0' : ∀ k, d' k = 0 → (Vᴴ * trL ρ * V) k k = 0 := by
    intro k hk
    have hcol : σ' *ᵥ (fun x => V x k) = 0 := by
      have e1 : σ' * V = V * diagonal (fun i => (d' i : ℂ)) := by
        rw [hσV, Matrix.mul_assoc, Matrix.mul_assoc, hV1, Matrix.mul_one]
      funext x
      have := congrFun (congrFun e1 x) k
      simp only [mul_diagonal, hk, Complex.ofReal_zero, mul_zero] at this
      simp only [Pi.zero_apply]
      rw [← this]; simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    have h2 := hker (show (fun x => V x k) ∈ LinearMap.ker σ'.mulVecLin by simpa using hcol)
    simp only [LinearMap.mem_ker, mulVecLin_apply] at h2
    have e2 : (Vᴴ * trL ρ * V) k k = ∑ x, star (V x k) * ((trL ρ) *ᵥ (fun x => V x k)) x := by
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, conjTranspose_apply, Finset.mul_sum,
        Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
    rw [e2, h2]; simp
  have hzero : ∀ g k, d' k = 0 → (Vᴴ * blk ρ g * V) k k = 0 := by
    intro g k hk
    have hs := H0' k hk
    rw [trL_entry, Fin.sum_univ_two] at hs
    have := (add_eq_zero_iff_of_nonneg (hnn 0 k) (hnn 1 k)).mp hs
    fin_cases g
    · exact this.1
    · exact this.2
  have H0 : ∀ k, d k = 0 → (Wᴴ * ρ * W) k k = 0 := by
    rintro ⟨g, k⟩ hk
    have : d' k = 0 := by simp only [d] at hk; linarith
    rw [hr]; exact hzero g k this
  have hd'nn : ∀ k, 0 ≤ d' k := hσ'.1.eigenvalues_nonneg
  have hd'sum : ∑ k, d' k = 1 := by
    have := congrArg Complex.re hH.trace_eq_sum_eigenvalues
    rw [hσ'.2] at this; simpa [hd'def] using this.symm
  have hd : ∀ k, 0 ≤ d k := fun k => div_nonneg (hd'nn _) (by norm_num)
  have hdsum : ∑ k, d k = 1 := by
    simp only [d]
    rw [Fintype.sum_prod_type, Fin.sum_univ_two, ← Finset.sum_div, hd'sum]; norm_num
  obtain ⟨R1d, R1k, R1e, -⟩ := S198R.relW ρ hρ W hW1 hW2 d hd hdsum H0
  obtain ⟨-, -, R2e, -⟩ := S198R.relW (trL ρ) hdtr V hV1 hV2 d' hd'nn hd'sum H0'
  rw [← hτ] at R1d R1k R1e
  rw [← hσV] at R2e
  have hr'sum : ∑ k, ((Vᴴ * trL ρ * V) k k).re = 1 := by
    rw [← Complex.re_sum]
    have : ∑ k, (Vᴴ * trL ρ * V) k k = (Vᴴ * trL ρ * V).trace := rfl
    rw [this, Matrix.trace_mul_cycle, hV2, Matrix.one_mul, hdtr.2,
      Complex.one_re]
  have hsum : ∑ k, ((Wᴴ * ρ * W) k k).re * Real.log (d k) =
      ∑ k, ((Vᴴ * trL ρ * V) k k).re * Real.log (d' k) - Real.log 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have e3 : Real.log 2 = ∑ k, ((Vᴴ * trL ρ * V) k k).re * Real.log 2 := by
      rw [← Finset.sum_mul, hr'sum, one_mul]
    rw [e3, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hr, d]
    by_cases hk : d' k = 0
    · simp [hk, H0' k hk, hzero _ k hk]
    · rw [Real.log_div hk two_ne_zero, ← Finset.sum_mul, trL_entry, Complex.re_sum]; ring
  have hAL := AL_bound ρ hρ
  set T := (cfc (fun x : ℝ => x * Real.log x) ρ - ρ * cfc Real.log (kronecker half2 σ')).trace.re
  set T' := (cfc (fun x : ℝ => x * Real.log x) (trL ρ) - trL ρ * cfc Real.log σ').trace.re
  have hT : T ≤ T' + 2 * Real.log 2 := by
    rw [R1e, R2e, hsum]
    have := mul_le_mul_of_nonneg_right hAL hl2.le
    nlinarith
  unfold relativeEntropyBits
  rw [dif_pos ⟨hρ, R1d⟩, dif_pos ⟨hdtr, hσ'⟩]
  unfold QAlgorithms.QuantumLoss.umegakiEntropy
  rw [if_pos R1k, if_pos hker]
  calc ENNReal.ofReal T / ENNReal.ofReal (Real.log 2)
      ≤ ENNReal.ofReal (T' + 2 * Real.log 2) / ENNReal.ofReal (Real.log 2) := by
        gcongr
    _ ≤ (ENNReal.ofReal T' + ENNReal.ofReal (2 * Real.log 2)) / ENNReal.ofReal (Real.log 2) := by
        gcongr; exact ENNReal.ofReal_add_le
    _ = ENNReal.ofReal T' / ENNReal.ofReal (Real.log 2) + 2 := by
        rw [ENNReal.add_div, ← ENNReal.ofReal_div_of_pos (x := 2 * Real.log 2) hl2, mul_div_assoc, div_self hl2.ne',
          mul_one, ENNReal.ofReal_ofNat]

end S198R2

namespace QAlgorithms.Papers.Independent.Frontier30.P30
open scoped Matrix ComplexConjugate
open Filter
open QAlgorithms
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Information100.P54
open Matrix

def S198Pq (U : Matrix (Fin 2) (Fin 2) ℂ) (q : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => U i q * conj (U j q)

lemma S198_Pq_facts (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    (∀ q, (S198Pq U q)ᴴ = S198Pq U q) ∧
    (∀ q l, S198Pq U q * S198Pq U l = if q = l then S198Pq U q else 0) ∧
    ∑ q, S198Pq U q = 1 := by
  have h1 : star (U : Matrix (Fin 2) (Fin 2) ℂ) * U = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
  have h2 : (U : Matrix (Fin 2) (Fin 2) ℂ) * star U = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
  refine ⟨?_, ?_, ?_⟩
  · intro q; ext i j; simp [S198Pq, mul_comm]
  · intro q l; ext i j
    have hs : (S198Pq U q * S198Pq U l) i j =
        U i q * conj (U j l) * (star (U : Matrix (Fin 2) (Fin 2) ℂ) * U) q l := by
      simp only [S198Pq, Matrix.mul_apply, Matrix.star_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [RCLike.star_def]; ring
    rw [hs, h1]
    by_cases hql : q = l
    · subst hql; simp [S198Pq]
    · simp [hql, Matrix.one_apply]
  · ext i j
    rw [Matrix.sum_apply, ← h2]
    simp [S198Pq, Matrix.mul_apply, RCLike.star_def]

lemma S198_P_facts {A : Type} [Fintype A] (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    (∀ q, (kronecker (S198Pq U q) (1 : Matrix A A ℂ))ᴴ = kronecker (S198Pq U q) 1) ∧
    (∀ q, kronecker (S198Pq U q) (1 : Matrix A A ℂ) * kronecker (S198Pq U q) 1 =
      kronecker (S198Pq U q) 1) ∧
    (∀ q l, q ≠ l → kronecker (S198Pq U q) (1 : Matrix A A ℂ) * kronecker (S198Pq U l) 1 = 0) ∧
    ∑ q, kronecker (S198Pq U q) (1 : Matrix A A ℂ) = 1 := by
  obtain ⟨f1, f2, f3⟩ := S198_Pq_facts U
  simp only [S198R.kr]
  refine ⟨fun q => ?_, fun q => ?_, fun q l h => ?_, ?_⟩
  · rw [conjTranspose_kronecker, conjTranspose_one, f1]
  · rw [← mul_kronecker_mul, f2, if_pos rfl, Matrix.one_mul]
  · rw [← mul_kronecker_mul, f2, if_neg h, zero_kronecker]
  · have : ∑ q, kroneckerMap (· * ·) (S198Pq U q) (1 : Matrix A A ℂ) =
        kroneckerMap (· * ·) (∑ q, S198Pq U q) (1 : Matrix A A ℂ) := by
      ext x y; simp [Matrix.sum_apply, add_mul]
    rw [this, f3, one_kronecker_one]

lemma S198_mf {A B : Type} [Fintype A] [Fintype B] (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (rho : Op ((Fin 2 × A) × B)) :
    (measureFlag U rho).submatrix (Equiv.prodComm B (Fin 2 × A)) (Equiv.prodComm B (Fin 2 × A)) =
      bobPinching (fun q => kronecker (S198Pq U q) (1 : Matrix A A ℂ))
        (rho.submatrix (Equiv.prodComm B (Fin 2 × A)) (Equiv.prodComm B (Fin 2 × A))) := by
  set c := Equiv.prodComm B (Fin 2 × A)
  have hL : ∀ q, (kronecker (kronecker (S198Pq U q) (1 : Matrix A A ℂ)) (1 : Matrix B B ℂ)).submatrix
      c c = kronecker (1 : Matrix B B ℂ) (kronecker (S198Pq U q) (1 : Matrix A A ℂ)) := by
    intro q; ext ⟨b, f, a⟩ ⟨b', g, a'⟩
    simp [c, Matrix.kronecker, mul_comm]
  have hsum : ∀ (M : Fin 2 → Op ((Fin 2 × A) × B)), (∑ q, M q).submatrix c c =
      ∑ q, (M q).submatrix c c := by
    intro M; ext x y; simp [Matrix.sum_apply]
  unfold measureFlag bobPinching
  rw [hsum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← hL q, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]
  rfl

theorem S198_part1 {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (rho : Op ((Fin 2 × A) × B)) (hrho : IsDensityMatrix rho)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    relativeE rho - relativeE (measureFlag U rho) ≤ 1 := by
  set c := Equiv.prodComm B (Fin 2 × A)
  obtain ⟨p1, p2, p3, p4⟩ := S198_P_facts (A := A) U
  have hρ' : IsDensityMatrix (rho.submatrix c c) := S198R.dens_sub rho hrho c
  obtain ⟨L1, L2⟩ := local_pinching_penalty (rho.submatrix c c) hρ'
    (fun q => kronecker (S198Pq U q) (1 : Matrix A A ℂ)) p1 p2 p3 p4
  have hmf := S198_mf U rho
  have hbp := S198R.pinch_dens (rho.submatrix c c) hρ'
    (fun q => kronecker (S198Pq U q) (1 : Matrix A A ℂ)) p1 p2 p4
  have hM : IsDensityMatrix (measureFlag U rho) := by
    have := S198R.dens_sub _ hbp c.symm
    rw [← hmf, submatrix_submatrix] at this
    convert this using 1
    ext ⟨⟨f, a⟩, b⟩ ⟨⟨g, a'⟩, b'⟩; rfl
  have hH : shannonEntropy (pinchingProbability
      (fun q => kronecker (S198Pq U q) (1 : Matrix A A ℂ)) (rho.submatrix c c)) ≤ 1 := by
    apply S198R.shannon_le_one
    · intro k; exact S198R.prob_nonneg _ hρ' _ (p1 k) (p2 k)
    · have := S198R.prob_sum _ hρ' _ p4
      rw [Fin.sum_univ_two] at this; exact this
  have key : relativeEntanglement rho ≤ relativeEntanglement (measureFlag U rho) + 1 := by
    rw [← S198R.RE_swap rho, ← S198R.RE_swap (measureFlag U rho), hmf]
    exact (L1.trans L2).trans (add_le_add (le_refl _) hH)
  unfold relativeE
  have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨S198R.RE_ne_top _ hM, ENNReal.one_ne_top⟩) key
  rw [ENNReal.toReal_add (S198R.RE_ne_top _ hM) ENNReal.one_ne_top, ENNReal.toReal_one] at this
  rw [sub_le_iff_le_add, add_comm]
  convert this using 4

lemma S198_sep_lift {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (σ' : Op (A × B)) (hσ : QAlgorithms.Entanglement.IsSeparableDensity σ') :
    QAlgorithms.Entanglement.IsSeparableDensity
      ((kronecker S198R2.half2 σ').submatrix (Equiv.prodAssoc (Fin 2) A B)
        (Equiv.prodAssoc (Fin 2) A B)) := by
  obtain ⟨q, w, Aj, Bj, hw, hs, hd, rfl⟩ := hσ
  refine ⟨q, w, fun j => kronecker S198R2.half2 (Aj j), Bj, hw, hs, fun j => ⟨⟨?_, ?_⟩, (hd j).2⟩, ?_⟩
  · exact S198R2.half2_dens.1.kronecker (hd j).1.1
  · show (kronecker S198R2.half2 (Aj j)).trace = 1
    rw [S198R.kr, trace_kronecker, S198R2.half2_dens.2, (hd j).1.2, one_mul]
  · ext ⟨⟨f, a⟩, b⟩ ⟨⟨g, a'⟩, b'⟩
    simp only [submatrix_apply, Equiv.prodAssoc_apply, Matrix.sum_apply, Matrix.kronecker,
      kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

theorem S198_part2 {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (rho : Op ((Fin 2 × A) × B)) (hrho : IsDensityMatrix rho) :
    relativeE rho - relativeE (eraseFlag rho) ≤ 2 := by
  set e := Equiv.prodAssoc (Fin 2) A B
  set rt := rho.submatrix e.symm e.symm
  have hrt : IsDensityMatrix rt := S198R.dens_sub rho hrho e.symm
  have herase : eraseFlag rho = S198R2.trL rt := by
    ext x y
    simp [eraseFlag, S198R2.trL, S198R2.blk, Matrix.sum_apply, rt, e]
  have hback : rt.submatrix e e = rho := by
    ext x y; simp [rt]
  have hdE : IsDensityMatrix (eraseFlag rho) := herase ▸ S198R2.trL_dens rt hrt
  have key : relativeEntanglement rho ≤ relativeEntanglement (eraseFlag rho) + 2 := by
    rw [show relativeEntanglement (eraseFlag rho) = sInf {x | ∃ σ : Op (A × B),
      QAlgorithms.Entanglement.IsSeparableDensity σ ∧ x = relativeEntropyBits (eraseFlag rho) σ}
      from rfl, ENNReal.sInf_add]
    refine le_iInf₂ fun b hb => ?_
    obtain ⟨σ', hsep, rfl⟩ := hb
    by_cases htop : relativeEntropyBits (eraseFlag rho) σ' = ⊤
    · rw [htop, top_add]; exact le_top
    have hcond : IsDensityMatrix (eraseFlag rho) ∧ IsDensityMatrix σ' := by
      by_contra h; apply htop; unfold relativeEntropyBits; rw [dif_neg h]
    have hker : LinearMap.ker σ'.mulVecLin ≤ LinearMap.ker (eraseFlag rho).mulVecLin := by
      by_contra h; apply htop; unfold relativeEntropyBits; rw [dif_pos hcond]
      unfold QAlgorithms.QuantumLoss.umegakiEntropy; rw [if_neg h]
      exact ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top
    rw [herase] at hker
    calc relativeEntanglement rho
        ≤ relativeEntropyBits rho ((kronecker S198R2.half2 σ').submatrix e e) :=
          sInf_le ⟨_, S198_sep_lift σ' hsep, rfl⟩
      _ = relativeEntropyBits (rt.submatrix e e) ((kronecker S198R2.half2 σ').submatrix e e) := by
          rw [hback]
      _ ≤ relativeEntropyBits rt (kronecker S198R2.half2 σ') := S198R.reb_sub_le _ _ _
      _ ≤ relativeEntropyBits (S198R2.trL rt) σ' + 2 := S198R2.key2 rt hrt σ' hcond.2 hker
      _ = relativeEntropyBits (eraseFlag rho) σ' + 2 := by rw [herase]
  unfold relativeE
  have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨S198R.RE_ne_top _ hdE, ENNReal.ofNat_ne_top⟩) key
  rw [ENNReal.toReal_add (S198R.RE_ne_top _ hdE) ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat] at this
  rw [sub_le_iff_le_add, add_comm]
  convert this using 4

end QAlgorithms.Papers.Independent.Frontier30.P30

open QAlgorithms.Papers.Independent.Frontier30.P30 in
open QAlgorithms.Papers.Independent.Information100.P21 (Op) in
theorem solution {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (rho : Op ((Fin 2 × A) × B)) (hrho : QAlgorithms.IsDensityMatrix rho)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    relativeE rho - relativeE (measureFlag U rho) ≤ 1 ∧
    relativeE rho - relativeE (eraseFlag rho) ≤ 2 :=
  ⟨S198_part1 rho hrho U, S198_part2 rho hrho⟩

#print axioms solution
