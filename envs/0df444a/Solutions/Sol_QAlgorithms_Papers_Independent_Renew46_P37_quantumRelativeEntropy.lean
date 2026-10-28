-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P37.quantumRelativeEntropy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T22:17:21.573795+00:00
-- url     : https://prove2.me/submissions/26e5c4ab-e2cf-41bc-9066-2a89d7f95d76

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P37

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

set_option linter.unusedSectionVars false

section S193Q_gen
open Matrix Polynomial

variable {X K : Type*} [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K]

def S193Q_conj (W : Matrix X K ℂ) (h1 : Wᴴ * W = 1) (h2 : W * Wᴴ = 1) :
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

lemma S193Q_herm (W : Matrix X K ℂ) (d : K → ℝ) :
    (W * diagonal (fun k => (d k : ℂ)) * Wᴴ).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose,
    Matrix.mul_assoc]
  congr 3
  funext k
  simp

lemma S193Q_cfc (W : Matrix X K ℂ) (h1 : Wᴴ * W = 1) (h2 : W * Wᴴ = 1) (d : K → ℝ)
    (f : ℝ → ℝ) :
    cfc f (W * diagonal (fun k => (d k : ℂ)) * Wᴴ) =
      W * diagonal (fun k => (f (d k) : ℂ)) * Wᴴ := by
  have hσ := S193Q_herm W d
  set σ := W * diagonal (fun k => (d k : ℂ)) * Wᴴ with hσdef
  set s : Finset ℝ := Finset.univ.image d ∪ Finset.univ.image hσ.eigenvalues with hs
  set p : ℝ[X] := Lagrange.interpolate s id f with hpdef
  have hp : ∀ x ∈ s, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) _ (Set.injOn_id _) hx
  rw [cfc_congr (g := fun x => p.eval x) (fun x hx => (hp x ?_).symm),
    cfc_polynomial p σ hσ.isSelfAdjoint]
  · have : σ = S193Q_conj W h1 h2 (diagonalAlgHom ℝ (fun k => (d k : ℂ))) := rfl
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

lemma S193Q_tr (ρ : Matrix X X ℂ) (W : Matrix X K ℂ) (e : K → ℂ) :
    (ρ * (W * diagonal e * Wᴴ)).trace = ∑ k, (Wᴴ * ρ * W) k k * e k := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag, mul_diagonal]

lemma S193Q_ker (ρ : Matrix X X ℂ) (hρ : ρ.PosSemidef) (W : Matrix X K ℂ) (h1 : Wᴴ * W = 1)
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

lemma S193Q_klein {I : Type*} [Fintype I] (p : I → ℝ) (d : K → ℝ) (M : I → K → ℝ)
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


lemma S193Q_cfc_trace {Y : Matrix X X ℂ} (hY : Y.IsHermitian) (f : ℝ → ℝ) :
    (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma S193Q_vn_eig {Y : Matrix X X ℂ} (hY : Y.IsHermitian) :
    QAlgorithms.vnEntropy Y = (∑ i, Real.negMulLog (hY.eigenvalues i)) / Real.log 2 := by
  unfold QAlgorithms.vnEntropy
  rw [S193Q_cfc_trace hY, Complex.re_sum, Finset.sum_div]
  simp only [Complex.ofReal_re]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Real.negMulLog, Real.logb]; ring_nf

lemma S193Q_relW (ρ : Matrix X X ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) (W : Matrix X K ℂ)
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
    rw [S193Q_vn_eig hH, div_mul_cancel₀ _ hl2.ne', ← Finset.sum_neg_distrib]
    simp [Real.negMulLog, hpdef]
  have hplog : (cfc (fun x : ℝ => x * Real.log x) ρ).trace.re = ∑ i, p i * Real.log (p i) := by
    rw [S193Q_cfc_trace hH, Complex.re_sum]
    simp [hpdef]
  have hlog : (ρ * cfc Real.log (W * diagonal (fun k => (d k : ℂ)) * Wᴴ)).trace.re =
      ∑ k, ((Wᴴ * ρ * W) k k).re * Real.log (d k) := by
    rw [S193Q_cfc W h1 h2, S193Q_tr, Complex.re_sum]
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
  have hK := S193Q_klein p d (fun i k => Complex.normSq (B i k)) hpsd.eigenvalues_nonneg hd
    (fun i k => Complex.normSq_nonneg _) hrow hcol (by rw [hpsum, hdsum])
    (fun k hk => by rw [← hr, H0 k hk, Complex.zero_re])
  refine ⟨⟨?_, ?_⟩, S193Q_ker ρ hpsd W h1 h2 d H0, ?_, ?_⟩
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

end S193Q_gen

section S193Q_prod
open Matrix
attribute [local instance] Classical.propDecidable

def S193Q_marg {X K F : Type*} [Fintype X] (ρ : Matrix X X ℂ) (k : X → K) (f : X → F) :
    Matrix K K ℂ :=
  fun a b => ∑ x, ∑ y, if k x = a ∧ k y = b ∧ f x = f y then ρ x y else 0

lemma S193Q_marg_herm {X K F : Type*} [Fintype X] (ρ : Matrix X X ℂ) (hρ : ρ.IsHermitian)
    (k : X → K) (f : X → F) : (S193Q_marg ρ k f).IsHermitian := by
  ext a b
  simp only [conjTranspose_apply, S193Q_marg, star_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  by_cases h : k x = a ∧ k y = b ∧ f x = f y
  · rw [if_pos ⟨h.2.1, h.1, h.2.2.symm⟩, if_pos h]
    exact congrFun (congrFun hρ x) y
  · rw [if_neg (fun h' => h ⟨h'.2.1, h'.1, h'.2.2.symm⟩), if_neg h, star_zero]

lemma S193Q_collapse {X K F : Type*} [Fintype X] [Fintype K] (ρ : Matrix X X ℂ) (k : X → K)
    (f : X → F) (A : K → K → ℂ) :
    ∑ u, ∑ v, A u v * S193Q_marg ρ k f u v =
      ∑ x, ∑ y, if f x = f y then A (k x) (k y) * ρ x y else 0 := by
  simp only [S193Q_marg, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun u _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_congr rfl (fun u _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_eq_single (k x)]
  · rw [Finset.sum_eq_single (k y)]
    · by_cases h : f x = f y
      · rw [if_pos ⟨rfl, rfl, h⟩, if_pos h]
      · rw [if_neg (fun h' => h h'.2.2), if_neg h, mul_zero]
    · intro v _ hv; rw [if_neg (fun h' => hv h'.2.1.symm), mul_zero]
    · simp
  · intro u _ hu
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [if_neg (fun h' => hu h'.1.symm), mul_zero]
  · simp

variable {X J : Type*} [Fintype X] [DecidableEq X] [Fintype J] [DecidableEq J]
  {Y : J → Type*} [∀ j, Fintype (Y j)] [∀ j, DecidableEq (Y j)]

def S193Q_W (g : (j : J) → X → Y j) (U : (j : J) → Matrix (Y j) (Y j) ℂ) :
    Matrix X ((j : J) → Y j) ℂ := fun x κ => ∏ j, U j (g j x) (κ j)

lemma S193Q_W1 (g : (j : J) → X → Y j) (U : (j : J) → Matrix (Y j) (Y j) ℂ)
    (hU1 : ∀ j, (U j)ᴴ * U j = 1) (hg : Function.Bijective (fun x j => g j x)) :
    (S193Q_W g U)ᴴ * S193Q_W g U = 1 := by
  ext κ κ'
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [conjTranspose_apply, S193Q_W, Complex.star_def, map_prod, ← Finset.prod_mul_distrib]
  rw [hg.sum_comp (fun z : (j : J) → Y j =>
    ∏ j, (starRingEnd ℂ) (U j (z j) (κ j)) * U j (z j) (κ' j)),
    ← Fintype.prod_sum (fun j c => (starRingEnd ℂ) (U j c (κ j)) * U j c (κ' j))]
  have : ∀ j, ∑ c, (starRingEnd ℂ) (U j c (κ j)) * U j c (κ' j) =
      if κ j = κ' j then 1 else 0 := by
    intro j
    rw [← Matrix.one_apply, ← hU1 j, Matrix.mul_apply]
    rfl
  simp only [this]
  rw [Fintype.prod_boole]
  simp only [funext_iff]

lemma S193Q_W2 (g : (j : J) → X → Y j) (U : (j : J) → Matrix (Y j) (Y j) ℂ)
    (hU2 : ∀ j, U j * (U j)ᴴ = 1) (hg : Function.Bijective (fun x j => g j x)) :
    S193Q_W g U * (S193Q_W g U)ᴴ = 1 := by
  ext x y
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [conjTranspose_apply, S193Q_W, Complex.star_def, map_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun j c => U j (g j x) c * (starRingEnd ℂ) (U j (g j y) c))]
  have : ∀ j, ∑ c, U j (g j x) c * (starRingEnd ℂ) (U j (g j y) c) =
      if g j x = g j y then 1 else 0 := by
    intro j
    rw [← Matrix.one_apply, ← hU2 j, Matrix.mul_apply]
    rfl
  simp only [this]
  rw [Fintype.prod_boole]
  congr 1
  apply propext
  constructor
  · intro h; exact hg.1 (funext h)
  · rintro rfl j; rfl

lemma S193Q_mdm {m n : Type*} [Fintype n] [DecidableEq n] (A : Matrix m n ℂ) (d : n → ℂ)
    (B : Matrix n m ℂ) (x y : m) : (A * diagonal d * B) x y = ∑ k, A x k * d k * B k y := by
  rw [Matrix.mul_apply]; simp [mul_diagonal]

lemma S193Q_W3 (g : (j : J) → X → Y j) (U : (j : J) → Matrix (Y j) (Y j) ℂ)
    (a : (j : J) → Y j → ℝ) (x y : X) :
    (S193Q_W g U * diagonal (fun κ : (j : J) → Y j => ((∏ j, a j (κ j) : ℝ) : ℂ)) *
      (S193Q_W g U)ᴴ) x y =
      ∏ j, (U j * diagonal (fun c => (a j c : ℂ)) * (U j)ᴴ) (g j x) (g j y) := by
  simp only [S193Q_mdm, conjTranspose_apply, S193Q_W, Complex.star_def, map_prod]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  push_cast
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

lemma S193Q_inner (g : (j : J) → X → Y j) (U : (j : J) → Matrix (Y j) (Y j) ℂ)
    (hU2 : ∀ j, U j * (U j)ᴴ = 1) (j0 : J) (ψ : Y j0 → ℂ) (x y : X) :
    ∑ κ : (j : J) → Y j, star (S193Q_W g U x κ) * S193Q_W g U y κ * ψ (κ j0) =
      (∑ c, star (U j0 (g j0 x) c) * U j0 (g j0 y) c * ψ c) *
        (if ∀ j ∈ Finset.univ.erase j0, g j y = g j x then 1 else 0) := by
  set upd : (j : J) → Y j → ℂ := Function.update (fun j (_ : Y j) => (1 : ℂ)) j0 ψ with hupd
  have hu : ∀ κ : (j : J) → Y j, ∏ j, upd j (κ j) = ψ (κ j0) := by
    intro κ
    rw [Finset.prod_eq_single j0]
    · simp [hupd]
    · intro j _ hj; simp [hupd, Function.update_of_ne hj]
    · simp
  have h1 : ∀ κ : (j : J) → Y j, star (S193Q_W g U x κ) * S193Q_W g U y κ * ψ (κ j0) =
      ∏ j, (star (U j (g j x) (κ j)) * U j (g j y) (κ j) * upd j (κ j)) := by
    intro κ
    simp only [S193Q_W, Complex.star_def, map_prod, Finset.prod_mul_distrib, hu]
  simp only [h1]
  rw [← Fintype.prod_sum (fun j c => star (U j (g j x) c) * U j (g j y) c * upd j c),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ j0)]
  congr 1
  · refine Finset.sum_congr rfl fun c _ => ?_
    simp [hupd]
  · have hf : ∀ j ∈ Finset.univ.erase j0,
        ∑ c, star (U j (g j x) c) * U j (g j y) c * upd j c = if g j y = g j x then 1 else 0 := by
      intro j hj
      have hj' : j ≠ j0 := Finset.ne_of_mem_erase hj
      simp only [hupd, Function.update_of_ne hj', mul_one]
      rw [← Matrix.one_apply, ← hU2 j, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [conjTranspose_apply, mul_comm]
    rw [Finset.prod_congr rfl hf, Finset.prod_boole]
    try congr 1

lemma S193Q_P3 (ρ : Matrix X X ℂ) (g : (j : J) → X → Y j) (U : (j : J) → Matrix (Y j) (Y j) ℂ)
    (hU2 : ∀ j, U j * (U j)ᴴ = 1) {F : J → Type*} (f : (j : J) → X → F j)
    (hf : ∀ j x y, f j x = f j y ↔ ∀ j' ∈ Finset.univ.erase j, g j' y = g j' x)
    (j0 : J) (ψ : Y j0 → ℂ) :
    ∑ κ, ((S193Q_W g U)ᴴ * ρ * S193Q_W g U) κ κ * ψ (κ j0) =
      ∑ c, ψ c * ((U j0)ᴴ * S193Q_marg ρ (g j0) (f j0) * U j0) c c := by
  have hL : ∑ κ, ((S193Q_W g U)ᴴ * ρ * S193Q_W g U) κ κ * ψ (κ j0) =
      ∑ x, ∑ y, ρ x y * ∑ κ : (j : J) → Y j,
        star (S193Q_W g U x κ) * S193Q_W g U y κ * ψ (κ j0) := by
    simp only [Matrix.mul_apply, conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun y _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun κ _ => ?_
    ring
  set A : Y j0 → Y j0 → ℂ := fun u v => ∑ c, star (U j0 u c) * U j0 v c * ψ c with hA
  have hR : ∑ c, ψ c * ((U j0)ᴴ * S193Q_marg ρ (g j0) (f j0) * U j0) c c =
      ∑ u, ∑ v, A u v * S193Q_marg ρ (g j0) (f j0) u v := by
    simp only [hA, Matrix.mul_apply, conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun v _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ =>
      Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [hL, hR, S193Q_collapse]
  simp only [S193Q_inner g U hU2 j0 ψ]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  by_cases h : f j0 x = f j0 y
  · rw [if_pos h, if_pos ((hf j0 x y).1 h), hA]; ring
  · rw [if_neg h, if_neg (fun h' => h ((hf j0 x y).2 h')), mul_zero, mul_zero]

def S193Q_sig (ρ : Matrix X X ℂ) (g : (j : J) → X → Y j) {F : J → Type*}
    (f : (j : J) → X → F j) : Matrix X X ℂ :=
  fun x y => ∏ j, S193Q_marg ρ (g j) (f j) (g j x) (g j y)

theorem S193Q_prodthm (ρ : Matrix X X ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ)
    (g : (j : J) → X → Y j) (hg : Function.Bijective (fun x j => g j x))
    {F : J → Type*} (f : (j : J) → X → F j)
    (hf : ∀ j x y, f j x = f j y ↔ ∀ j' ∈ Finset.univ.erase j, g j' y = g j' x) :
    QAlgorithms.IsDensityMatrix (S193Q_sig ρ g f) ∧
    LinearMap.ker (S193Q_sig ρ g f).mulVecLin ≤ LinearMap.ker ρ.mulVecLin ∧
    (cfc (fun x : ℝ => x * Real.log x) ρ - ρ * cfc Real.log (S193Q_sig ρ g f)).trace.re =
      (∑ j, QAlgorithms.vnEntropy (S193Q_marg ρ (g j) (f j)) - QAlgorithms.vnEntropy ρ) *
        Real.log 2 ∧
    0 ≤ ∑ j, QAlgorithms.vnEntropy (S193Q_marg ρ (g j) (f j)) - QAlgorithms.vnEntropy ρ ∧
    ∀ j, QAlgorithms.IsDensityMatrix (S193Q_marg ρ (g j) (f j)) := by
  have hH := hρ.1.isHermitian
  have hPh : ∀ j, (S193Q_marg ρ (g j) (f j)).IsHermitian := fun j =>
    S193Q_marg_herm ρ hH (g j) (f j)
  set U : (j : J) → Matrix (Y j) (Y j) ℂ := fun j => ((hPh j).eigenvectorUnitary : Matrix _ _ ℂ)
    with hUdef
  set a : (j : J) → Y j → ℝ := fun j => (hPh j).eigenvalues with hadef
  have hU1 : ∀ j, (U j)ᴴ * U j = 1 := fun j =>
    Matrix.mem_unitaryGroup_iff'.mp (hPh j).eigenvectorUnitary.2
  have hU2 : ∀ j, U j * (U j)ᴴ = 1 := fun j =>
    Matrix.mem_unitaryGroup_iff.mp (hPh j).eigenvectorUnitary.2
  have hspec : ∀ j, S193Q_marg ρ (g j) (f j) = U j * diagonal (fun c => (a j c : ℂ)) * (U j)ᴴ := by
    intro j
    conv_lhs => rw [(hPh j).spectral_theorem]
    rfl
  have hPU : ∀ j, (U j)ᴴ * S193Q_marg ρ (g j) (f j) * U j = diagonal (fun c => (a j c : ℂ)) := by
    intro j
    rw [hspec j, Matrix.mul_assoc, Matrix.mul_assoc, hU1 j, Matrix.mul_one, ← Matrix.mul_assoc,
      hU1 j, Matrix.one_mul]
  set W := S193Q_W g U with hW
  have h1 : Wᴴ * W = 1 := S193Q_W1 g U hU1 hg
  have h2 : W * Wᴴ = 1 := S193Q_W2 g U hU2 hg
  set d : ((j : J) → Y j) → ℝ := fun κ => ∏ j, a j (κ j) with hd
  have hσ : S193Q_sig ρ g f = W * diagonal (fun κ => (d κ : ℂ)) * Wᴴ := by
    ext x y
    rw [hW, hd, S193Q_W3]
    simp only [S193Q_sig]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [hspec j]
  set r : ((j : J) → Y j) → ℂ := fun κ => (Wᴴ * ρ * W) κ κ with hr
  have hr0 : ∀ κ, 0 ≤ r κ := fun κ => (hρ.1.conjTranspose_mul_mul_same W).diag_nonneg
  have hM : ∀ j0 (ψ : Y j0 → ℂ), ∑ κ, r κ * ψ (κ j0) = ∑ c, ψ c * (a j0 c : ℂ) := by
    intro j0 ψ
    rw [hr, hW, S193Q_P3 ρ g U hU2 f hf j0 ψ, hPU j0]
    simp [Matrix.diagonal_apply_eq]
  have hind : ∀ j (c : Y j), (a j c : ℂ) = ∑ κ, r κ * (if κ j = c then 1 else 0) := by
    intro j c
    rw [hM j (fun c' => if c' = c then 1 else 0)]
    simp
  have ha0 : ∀ j c, 0 ≤ a j c := by
    intro j c
    have : (0 : ℂ) ≤ (a j c : ℂ) := by
      rw [hind j c]
      refine Finset.sum_nonneg fun κ _ => mul_nonneg (hr0 κ) ?_
      split_ifs <;> norm_num
    exact_mod_cast this
  have hd0 : ∀ κ, 0 ≤ d κ := fun κ => Finset.prod_nonneg fun j _ => ha0 j (κ j)
  have H0 : ∀ κ, d κ = 0 → (Wᴴ * ρ * W) κ κ = 0 := by
    intro κ hκ
    obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.1 hκ
    have hs := hind j (κ j)
    rw [hj, Complex.ofReal_zero] at hs
    have hnn : ∀ κ' ∈ Finset.univ, 0 ≤ r κ' * (if κ' j = κ j then 1 else 0) := by
      intro κ' _
      refine mul_nonneg (hr0 κ') ?_
      split_ifs <;> norm_num
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hs.symm κ (Finset.mem_univ _)
    simpa [hr] using this
  have htrr : ∑ κ, r κ = 1 := by
    have : ∑ κ, r κ = (Wᴴ * ρ * W).trace := rfl
    rw [this, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, h2, Matrix.mul_one,
      hρ.2]
  have hasum : ∀ j, ∑ c, a j c = 1 := by
    intro j
    have := hM j (fun _ => 1)
    simp only [mul_one, one_mul] at this
    rw [htrr] at this
    exact_mod_cast this.symm
  have hdsum : ∑ κ, d κ = 1 := by
    rw [hd]
    simp only
    rw [← Fintype.prod_sum (fun j c => a j c)]
    simp [hasum]
  obtain ⟨hden, hker, htr, hle⟩ := S193Q_relW ρ hρ W h1 h2 d hd0 hdsum H0
  have hq : ∑ κ, ((Wᴴ * ρ * W) κ κ).re * Real.log (d κ) =
      ∑ j, ∑ c, a j c * Real.log (a j c) := by
    have e1 : ∀ κ, ((Wᴴ * ρ * W) κ κ).re * Real.log (d κ) =
        ∑ j, (r κ).re * Real.log (a j (κ j)) := by
      intro κ
      by_cases hz : r κ = 0
      · simp [hr] at hz; simp [hr, hz]
      · have hdκ : d κ ≠ 0 := fun h => hz (H0 κ h)
        rw [hd, Real.log_prod (fun j _ => (Finset.prod_ne_zero_iff.1 hdκ) j
          (Finset.mem_univ _)), Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun κ _ => e1 κ), Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := congrArg Complex.re (hM j (fun c => ((Real.log (a j c) : ℝ) : ℂ)))
    simp only [Complex.re_sum] at this
    convert this using 2 with κ _ c _
    · simp
    · simp [mul_comm]
  have hvnP : ∀ j, QAlgorithms.vnEntropy (S193Q_marg ρ (g j) (f j)) * Real.log 2 =
      -∑ c, a j c * Real.log (a j c) := by
    intro j
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [S193Q_vn_eig (hPh j), div_mul_cancel₀ _ hl2.ne', ← Finset.sum_neg_distrib]
    simp [Real.negMulLog, hadef]
  have hsumP : (∑ j, QAlgorithms.vnEntropy (S193Q_marg ρ (g j) (f j))) * Real.log 2 =
      -∑ j, ∑ c, a j c * Real.log (a j c) := by
    rw [Finset.sum_mul, Finset.sum_congr rfl (fun j _ => hvnP j), Finset.sum_neg_distrib]
  have hmden : ∀ j, QAlgorithms.IsDensityMatrix (S193Q_marg ρ (g j) (f j)) := by
    intro j
    refine ⟨?_, ?_⟩
    · rw [hspec j]
      apply Matrix.PosSemidef.mul_mul_conjTranspose_same
      rw [Matrix.posSemidef_diagonal_iff]
      intro c
      exact_mod_cast ha0 j c
    · rw [hspec j, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU1 j, Matrix.one_mul,
        Matrix.trace_diagonal]
      exact_mod_cast hasum j
  rw [hσ]
  refine ⟨hden, hker, ?_, ?_, hmden⟩
  · rw [htr, hq, sub_mul, hsumP]; ring
  · have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [hq] at hle
    have : 0 ≤ (∑ j, QAlgorithms.vnEntropy (S193Q_marg ρ (g j) (f j)) -
        QAlgorithms.vnEntropy ρ) * Real.log 2 := by
      rw [sub_mul, hsumP]; linarith
    exact nonneg_of_mul_nonneg_left this hl2

def S193Q_pd (g : (j : J) → X → Y j) (η : (j : J) → Matrix (Y j) (Y j) ℂ) : Matrix X X ℂ :=
  fun x y => ∏ j, η j (g j x) (g j y)

lemma S193Q_ite {P Q : Prop} {_ : Decidable P} {_ : Decidable Q} (h : P ↔ Q) (a : ℂ) :
    (if P then a else 0) = (if Q then a else 0) := by
  by_cases hP : P
  · rw [if_pos hP, if_pos (h.1 hP)]
  · rw [if_neg hP, if_neg (fun hQ => hP (h.2 hQ))]

lemma S193Q_vn1 {ι : Type*} [Fintype ι] [DecidableEq ι] :
    QAlgorithms.vnEntropy (1 : Matrix ι ι ℂ) = 0 := by
  unfold QAlgorithms.vnEntropy
  rw [cfc_apply_one]
  simp

theorem S193Q_minthm (ρ : Matrix X X ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ)
    (g : (j : J) → X → Y j) (hg : Function.Bijective (fun x j => g j x))
    {F : J → Type*} (f : (j : J) → X → F j)
    (hf : ∀ j x y, f j x = f j y ↔ ∀ j' ∈ Finset.univ.erase j, g j' y = g j' x)
    (η : (j : J) → Matrix (Y j) (Y j) ℂ) (hη : ∀ j, QAlgorithms.IsDensityMatrix (η j)) :
    QAlgorithms.IsDensityMatrix (S193Q_pd g η) ∧
    (LinearMap.ker (S193Q_pd g η).mulVecLin ≤
        LinearMap.ker ρ.mulVecLin →
      (∑ j, QAlgorithms.vnEntropy (S193Q_marg ρ (g j) (f j)) - QAlgorithms.vnEntropy ρ) *
          Real.log 2 ≤
        (cfc (fun x : ℝ => x * Real.log x) ρ -
          ρ * cfc Real.log (S193Q_pd g η)).trace.re) := by
  have hmden := (S193Q_prodthm ρ hρ g hg f hf).2.2.2.2
  have hHj : ∀ j, (η j).IsHermitian := fun j => (hη j).1.isHermitian
  set U : (j : J) → Matrix (Y j) (Y j) ℂ := fun j => ((hHj j).eigenvectorUnitary : Matrix _ _ ℂ)
    with hUdef
  set a : (j : J) → Y j → ℝ := fun j => (hHj j).eigenvalues with hadef
  have hU1 : ∀ j, (U j)ᴴ * U j = 1 := fun j =>
    Matrix.mem_unitaryGroup_iff'.mp (hHj j).eigenvectorUnitary.2
  have hU2 : ∀ j, U j * (U j)ᴴ = 1 := fun j =>
    Matrix.mem_unitaryGroup_iff.mp (hHj j).eigenvectorUnitary.2
  have hspec : ∀ j, η j = U j * diagonal (fun c => (a j c : ℂ)) * (U j)ᴴ := by
    intro j
    conv_lhs => rw [(hHj j).spectral_theorem]
    rfl
  have ha0 : ∀ j c, 0 ≤ a j c := fun j c => (hη j).1.eigenvalues_nonneg c
  have hasum : ∀ j, ∑ c, a j c = 1 := by
    intro j
    have := congrArg Complex.re (hHj j).trace_eq_sum_eigenvalues
    rw [(hη j).2] at this
    simpa [hadef] using this.symm
  set W := S193Q_W g U with hW
  have h1 : Wᴴ * W = 1 := S193Q_W1 g U hU1 hg
  have h2 : W * Wᴴ = 1 := S193Q_W2 g U hU2 hg
  set d : ((j : J) → Y j) → ℝ := fun κ => ∏ j, a j (κ j) with hd
  have hd0 : ∀ κ, 0 ≤ d κ := fun κ => Finset.prod_nonneg fun j _ => ha0 j (κ j)
  have hdsum : ∑ κ, d κ = 1 := by
    rw [hd]
    simp only
    rw [← Fintype.prod_sum (fun j c => a j c)]
    simp [hasum]
  have hσ : (S193Q_pd g η) =
      W * diagonal (fun κ => (d κ : ℂ)) * Wᴴ := by
    ext x y
    rw [hW, hd, S193Q_W3]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← hspec j]
  have hσden : QAlgorithms.IsDensityMatrix (W * diagonal (fun κ => (d κ : ℂ)) * Wᴴ) := by
    refine ⟨?_, ?_⟩
    · apply Matrix.PosSemidef.mul_mul_conjTranspose_same
      rw [Matrix.posSemidef_diagonal_iff]
      intro k
      exact_mod_cast hd0 k
    · rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.trace_diagonal]
      exact_mod_cast hdsum
  rw [hσ]
  refine ⟨hσden, fun hker => ?_⟩
  have H0 : ∀ κ, d κ = 0 → (Wᴴ * ρ * W) κ κ = 0 := by
    intro κ hκ
    set w : X → ℂ := fun x => W x κ with hw
    have hσW : (W * diagonal (fun κ => (d κ : ℂ)) * Wᴴ) * W =
        W * diagonal (fun κ => (d κ : ℂ)) := by
      rw [Matrix.mul_assoc, h1, Matrix.mul_one]
    have hσw : (W * diagonal (fun κ => (d κ : ℂ)) * Wᴴ) *ᵥ w = 0 := by
      funext x
      have := congrFun (congrFun hσW x) κ
      rw [Matrix.mul_diagonal, hκ, Complex.ofReal_zero, mul_zero] at this
      rw [Pi.zero_apply, ← this]
      rfl
    have hρw : ρ *ᵥ w = 0 := by
      have hm : w ∈ LinearMap.ker (W * diagonal (fun κ => (d κ : ℂ)) * Wᴴ).mulVecLin := by
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hσw
      have := hker hm
      rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at this
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun x _ => ?_
    have : (ρ * W) x κ = (ρ *ᵥ w) x := rfl
    rw [this, hρw]
    simp
  obtain ⟨_, _, htr, _⟩ := S193Q_relW ρ hρ W h1 h2 d hd0 hdsum H0
  set r : ((j : J) → Y j) → ℂ := fun κ => (Wᴴ * ρ * W) κ κ with hr
  have hM : ∀ j0 (ψ : Y j0 → ℂ), ∑ κ, r κ * ψ (κ j0) =
      ∑ c, ψ c * ((U j0)ᴴ * S193Q_marg ρ (g j0) (f j0) * U j0) c c := by
    intro j0 ψ
    rw [hr, hW, S193Q_P3 ρ g U hU2 f hf j0 ψ]
  have hq : ∑ κ, ((Wᴴ * ρ * W) κ κ).re * Real.log (d κ) =
      ∑ j, ∑ c, (((U j)ᴴ * S193Q_marg ρ (g j) (f j) * U j) c c).re * Real.log (a j c) := by
    have e1 : ∀ κ, ((Wᴴ * ρ * W) κ κ).re * Real.log (d κ) =
        ∑ j, (r κ).re * Real.log (a j (κ j)) := by
      intro κ
      by_cases hz : r κ = 0
      · simp [hr] at hz; simp [hr, hz]
      · have hdκ : d κ ≠ 0 := fun h => hz (H0 κ h)
        rw [hd, Real.log_prod (fun j _ => (Finset.prod_ne_zero_iff.1 hdκ) j
          (Finset.mem_univ _)), Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun κ _ => e1 κ), Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := congrArg Complex.re (hM j (fun c => ((Real.log (a j c) : ℝ) : ℂ)))
    simp only [Complex.re_sum] at this
    convert this using 2 with κ _ c _
    · simp
    · simp [mul_comm]
  have hK : ∀ j, ∑ c, (((U j)ᴴ * S193Q_marg ρ (g j) (f j) * U j) c c).re * Real.log (a j c) ≤
      -(QAlgorithms.vnEntropy (S193Q_marg ρ (g j) (f j)) * Real.log 2) := by
    intro j
    refine (S193Q_relW (S193Q_marg ρ (g j) (f j)) (hmden j) (U j) (hU1 j) (hU2 j) (a j) (ha0 j)
      (hasum j) ?_).2.2.2
    intro c hc
    have h := hM j (fun c' => if c' = c then 1 else 0)
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      mul_ite, mul_one, mul_zero] at h
    rw [← h]
    refine Finset.sum_eq_zero fun κ _ => ?_
    split_ifs with hκ
    · have : d κ = 0 := Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hκ]; exact hc)
      exact H0 κ this
    · rfl
  have hsumK := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hK j
  rw [Finset.sum_neg_distrib, ← Finset.sum_mul] at hsumK
  rw [htr, hq, sub_mul]
  linarith

end S193Q_prod

section S193Q_vn
open Matrix Polynomial

lemma S193Q_inst {ι : Type*} [Fintype ι] (i1 i2 : DecidableEq ι) (A : Matrix ι ι ℂ) :
    @QAlgorithms.vnEntropy ι _ i1 A = @QAlgorithms.vnEntropy ι _ i2 A := by
  congr

lemma S193Q_vn_poly {ι : Type*} [Fintype ι] {inst : DecidableEq ι} (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (p : ℝ[X])
    (hp : ∀ x ∈ spectrum ℝ A, p.eval x = x * Real.logb 2 x) :
    QAlgorithms.vnEntropy A = -(aeval A p).trace.re := by
  unfold QAlgorithms.vnEntropy
  rw [cfc_congr (g := fun x => p.eval x) (fun x hx => (hp x hx).symm),
    cfc_polynomial p A hA.isSelfAdjoint]

lemma S193Q_spec_finite {ι : Type*} [Fintype ι] {inst : DecidableEq ι} (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) : (spectrum ℝ A).Finite := by
  rw [hA.spectrum_real_eq_range_eigenvalues]; exact Set.finite_range _

def S193Q_interp (s : Finset ℝ) : ℝ[X] :=
  Lagrange.interpolate s id (fun x => x * Real.logb 2 x)

lemma S193Q_interp_eval (s : Finset ℝ) {x : ℝ} (hx : x ∈ s) :
    (S193Q_interp s).eval x = x * Real.logb 2 x :=
  Lagrange.eval_interpolate_at_node (v := id) _ (Set.injOn_id _) hx

lemma S193Q_vn_submatrix {ι κ : Type*} [Fintype ι] [Fintype κ] {inst : DecidableEq ι}
    {inst' : DecidableEq κ} (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (e : κ ≃ ι) :
    QAlgorithms.vnEntropy (A.submatrix e e) = QAlgorithms.vnEntropy A := by
  set s := (S193Q_spec_finite A hA).toFinset
  have hsub : A.submatrix e e = Matrix.reindexAlgEquiv ℝ ℂ e.symm A := by
    ext a b; simp [Matrix.coe_reindexAlgEquiv]
  have hspec : spectrum ℝ (A.submatrix e e) = spectrum ℝ A := by
    rw [hsub]; exact AlgEquiv.spectrum_eq _ _
  rw [S193Q_vn_poly A hA (S193Q_interp s)
      (fun x hx => S193Q_interp_eval s (by simpa [s] using hx)),
    S193Q_vn_poly _ (hA.submatrix e) (S193Q_interp s)
      (fun x hx => S193Q_interp_eval s (by rw [hspec] at hx; simpa [s] using hx))]
  rw [hsub, Polynomial.aeval_algEquiv, AlgHom.comp_apply]
  congr 2
  simp only [AlgEquiv.coe_toAlgHom, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Equiv.symm_symm, Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact e.sum_comp (fun i => (aeval A (S193Q_interp s)) i i)

end S193Q_vn

section S193Q_reg
open Matrix
open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis registerMarginal
  trivialExtension entropyAt)
attribute [local instance] Classical.propDecidable Classical.decEq

variable {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]

def S193Q_e1 (i : Fin n) : SubBasis D {i} × Unit ≃ D i :=
  Equiv.ofBijective (fun p => p.1 ⟨i, Finset.mem_singleton_self i⟩) (by
    constructor
    · rintro ⟨a, u⟩ ⟨b, w⟩ h
      cases u; cases w
      congr 1
      funext ⟨k, hk⟩
      obtain rfl := Finset.mem_singleton.1 hk
      exact h
    · intro c
      exact ⟨(fun k => cast (congrArg D (Finset.mem_singleton.1 k.2).symm) c, ()), rfl⟩)

lemma S193Q_ent1 (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hρ : ρ.IsHermitian)
    (i : Fin n) :
    entropyAt (trivialExtension ρ) {i} =
      QAlgorithms.vnEntropy (S193Q_marg ρ (fun x : RegisterBasis D => x i)
        (fun x (k : {k : Fin n // k ≠ i}) => x k.1)) := by
  have hR : registerMarginal (trivialExtension ρ) {i} =
      (S193Q_marg ρ (fun x : RegisterBasis D => x i)
        (fun x (k : {k : Fin n // k ≠ i}) => x k.1)).submatrix (S193Q_e1 i) (S193Q_e1 i) := by
    ext ⟨a, u⟩ ⟨b, w⟩
    simp only [registerMarginal, trivialExtension, submatrix_apply, S193Q_marg]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => S193Q_ite ?_ _
    change _ ↔ x i = a ⟨i, Finset.mem_singleton_self i⟩ ∧ y i = b ⟨i, Finset.mem_singleton_self i⟩ ∧ _
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(h1 i (Finset.mem_singleton_self i)).1, (h1 i (Finset.mem_singleton_self i)).2,
        funext fun k => h2 k.1 (by simpa using k.2)⟩
    · rintro ⟨ha, hb, hf⟩
      refine ⟨fun k hk => ?_, fun k hk => congrFun hf ⟨k, by simpa using hk⟩⟩
      obtain rfl := Finset.mem_singleton.1 hk
      exact ⟨ha, hb⟩
  unfold entropyAt
  rw [hR, S193Q_vn_submatrix _ (S193Q_marg_herm ρ hρ _ _)]

def S193Q_univE : SubBasis D (Finset.univ : Finset (Fin n)) × Unit ≃ RegisterBasis D where
  toFun p := fun i => p.1 ⟨i, Finset.mem_univ i⟩
  invFun x := (fun k => x k.1, ())
  left_inv p := by
    obtain ⟨a, u⟩ := p
    cases u
    rfl
  right_inv x := rfl

lemma S193Q_S_univ (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hρ : ρ.IsHermitian) :
    entropyAt (trivialExtension ρ) Finset.univ = QAlgorithms.vnEntropy ρ := by
  have hR : registerMarginal (trivialExtension ρ) Finset.univ =
      ρ.submatrix S193Q_univE S193Q_univE := by
    ext ⟨a, u⟩ ⟨b, w⟩
    simp only [registerMarginal, trivialExtension, submatrix_apply]
    rw [Finset.sum_eq_single (S193Q_univE (a, u))]
    · rw [Finset.sum_eq_single (S193Q_univE (b, w))]
      · rw [if_pos]
        exact ⟨fun i hi => ⟨rfl, rfl⟩, fun i hi => absurd (Finset.mem_univ i) hi⟩
      · intro y _ hy
        rw [if_neg]
        rintro ⟨h1, _⟩
        exact hy (funext fun i => (h1 i (Finset.mem_univ i)).2)
      · simp
    · intro x _ hx
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [if_neg]
      rintro ⟨h1, _⟩
      exact hx (funext fun i => (h1 i (Finset.mem_univ i)).1)
    · simp
  unfold entropyAt
  rw [hR, S193Q_vn_submatrix _ hρ]

lemma S193Q_S_empty (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hρ : ρ.trace = 1) :
    entropyAt (trivialExtension ρ) ∅ = 0 := by
  have hR : registerMarginal (trivialExtension ρ) ∅ = 1 := by
    ext a b
    have hab : a = b := Prod.ext (funext fun k => absurd k.2 (Finset.notMem_empty _)) rfl
    subst hab
    rw [Matrix.one_apply_eq]
    simp only [registerMarginal, trivialExtension]
    rw [← hρ]
    unfold Matrix.trace
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single x]
    · rw [if_pos]; · rfl
      exact ⟨fun i hi => absurd hi (Finset.notMem_empty _), fun i _ => rfl⟩
    · intro y _ hy
      rw [if_neg]
      rintro ⟨_, h2⟩
      exact hy (funext fun i => (h2 i (Finset.notMem_empty _)).symm)
    · simp
  unfold entropyAt
  rw [hR]
  convert (S193Q_vn1 (ι := SubBasis D ∅ × Unit))

end S193Q_reg

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P37
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)
open QAlgorithms.Papers.Independent.Claimed50.P33
  (InformationKind RegisterBasis FiniteState singleParties allParties
   info entropyAt trivialExtension informationFunctional LocalInstrument
   IsContinuousFunctional partyProduct registerMarginal)

theorem solution {n : ℕ} (hn : 2 ≤ n) (s : FiniteState n) :
    (∀ i, IsDensityMatrix (localDensity s i)) ∧
    IsDensityMatrix (labelledProductDensity (localDensity s)) ∧
    quantumKL s.rho (labelledProductDensity (localDensity s)) = ENNReal.ofReal (qValue .total s) ∧
    ∀ eta : (i : Fin n) → Matrix (Fin (s.dims i)) (Fin (s.dims i)) ℂ,
      (∀ i, IsDensityMatrix (eta i)) →
      IsDensityMatrix (labelledProductDensity eta) ∧
      ENNReal.ofReal (qValue .total s) ≤ quantumKL s.rho (labelledProductDensity eta) := by
  have hρ := s.normalized
  have hH := hρ.1.isHermitian
  have hg : Function.Bijective (fun (x : RegisterBasis (fun i => Fin (s.dims i))) j =>
      (fun (j : Fin n) (x : RegisterBasis (fun i => Fin (s.dims i))) => x j) j x) :=
    Function.bijective_id
  have hf : ∀ j (x y : RegisterBasis (fun i => Fin (s.dims i))),
      (fun x (k : {k : Fin n // k ≠ j}) => x k.1) x =
          (fun x (k : {k : Fin n // k ≠ j}) => x k.1) y ↔
        ∀ j' ∈ Finset.univ.erase j, y j' = x j' := by
    intro j x y
    constructor
    · intro h j' hj'
      exact (congrFun h ⟨j', (Finset.mem_erase.1 hj').1⟩).symm
    · intro h
      funext k
      exact (h k.1 (Finset.mem_erase.2 ⟨k.2, Finset.mem_univ _⟩)).symm
  have hloc : ∀ i, localDensity s i = S193Q_marg s.rho
      (fun x : RegisterBasis (fun i => Fin (s.dims i)) => x i)
      (fun x (k : {k : Fin n // k ≠ i}) => x k.1) := by
    intro i
    ext a b
    simp only [localDensity, S193Q_marg]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => S193Q_ite ?_ _
    refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
    constructor
    · intro h; funext k; exact h k.1 k.2
    · intro h j hj; exact congrFun h ⟨j, hj⟩
  obtain ⟨hden, hker, htr, hnn, hmden⟩ := S193Q_prodthm s.rho hρ
    (fun (j : Fin n) (x : RegisterBasis (fun i => Fin (s.dims i))) => x j) hg
    (fun j x (k : {k : Fin n // k ≠ j}) => x k.1) hf
  have hq : qValue .total s = ∑ i, vnEntropy (S193Q_marg s.rho
      (fun x : RegisterBasis (fun i => Fin (s.dims i)) => x i)
      (fun x (k : {k : Fin n // k ≠ i}) => x k.1)) - vnEntropy s.rho := by
    have hU : allParties (singleParties n) ∪ ∅ = Finset.univ := by
      ext k; simp [allParties, singleParties]
    unfold qValue informationFunctional info
      QAlgorithms.Papers.Independent.Claimed50.P33.conditionalMultipartiteInformation
    simp only [Finset.union_empty] at hU ⊢
    rw [hU, S193Q_S_univ _ hH, S193Q_S_empty _ hρ.2, mul_zero, sub_zero]
    congr 1
    all_goals first
      | exact S193Q_inst _ _ _
      | exact Finset.sum_congr rfl fun i _ => (S193Q_ent1 _ hH i).trans (S193Q_inst _ _ _)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hP : labelledProductDensity (localDensity s) = S193Q_sig s.rho
      (fun (j : Fin n) (x : RegisterBasis (fun i => Fin (s.dims i))) => x j)
      (fun j x (k : {k : Fin n // k ≠ j}) => x k.1) := by
    funext x y
    simp only [labelledProductDensity, S193Q_sig, hloc]
  refine ⟨fun i => hloc i ▸ hmden i, hP ▸ hden, ?_, ?_⟩
  · unfold quantumKL
    rw [dif_pos hρ, dif_pos (hP ▸ hden)]
    unfold QAlgorithms.QuantumLoss.umegakiEntropy
    rw [hP, if_pos hker]
    have key : ∀ t : ℝ, t = (∑ j, vnEntropy (S193Q_marg s.rho
        (fun x : RegisterBasis (fun i => Fin (s.dims i)) => x j)
        (fun x (k : {k : Fin n // k ≠ j}) => x k.1)) - vnEntropy s.rho) * Real.log 2 →
        ENNReal.ofReal t / ENNReal.ofReal (Real.log 2) = ENNReal.ofReal (qValue .total s) := by
      intro t ht
      rw [ht, hq, ENNReal.ofReal_mul hnn, ENNReal.mul_div_cancel_right (by simpa using hl2)
        ENNReal.ofReal_ne_top]
    exact key _ (by convert htr)
  · intro η hη
    obtain ⟨hd, hmin⟩ := S193Q_minthm s.rho hρ
      (fun (j : Fin n) (x : RegisterBasis (fun i => Fin (s.dims i))) => x j) hg
      (fun j x (k : {k : Fin n // k ≠ j}) => x k.1) hf η hη
    have hd' : IsDensityMatrix (labelledProductDensity η) := hd
    refine ⟨hd', ?_⟩
    unfold quantumKL
    rw [dif_pos hρ, dif_pos hd']
    unfold QAlgorithms.QuantumLoss.umegakiEntropy
    split_ifs with hk
    · rw [← ENNReal.ofReal_div_of_pos hl2]
      apply ENNReal.ofReal_le_ofReal
      rw [le_div_iff₀ hl2, hq]
      refine (hmin hk).trans_eq ?_
      congr
      all_goals exact Subsingleton.elim _ _
    · rw [ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top]
      exact le_top
