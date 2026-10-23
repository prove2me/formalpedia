-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P46.direct_sum_information
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T15:17:14.328227+00:00
-- url     : https://prove2.me/submissions/65abe336-20ae-4bb1-b44c-65bef3285bc1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P46

open scoped Matrix ComplexConjugate ComplexOrder Kronecker
open Matrix Polynomial

namespace X8P46
open QAlgorithms

theorem x8_pow {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (W : Matrix ι κ ℂ) (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1) (d : κ → ℂ)
    (h : A = W * diagonal d * Wᴴ) (n : ℕ) : A ^ n = W * diagonal (d ^ n) * Wᴴ := by
  induction n with
  | zero => simp [hW2]
  | succ n ih =>
    rw [pow_succ, ih, h]
    have : W * diagonal (d ^ n) * Wᴴ * (W * diagonal d * Wᴴ) =
        W * (diagonal (d ^ n) * (Wᴴ * W) * diagonal d) * Wᴴ := by
      simp only [Matrix.mul_assoc]
    rw [this, hW1, Matrix.mul_one, diagonal_mul_diagonal, pow_succ]
    rfl

theorem x8_aeval {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (W : Matrix ι κ ℂ) (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1) (d : κ → ℝ)
    (h : A = W * diagonal (fun k => (d k : ℂ)) * Wᴴ) (p : ℝ[X]) :
    aeval A p = W * diagonal (fun k => ((p.eval (d k) : ℝ) : ℂ)) * Wᴴ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, hp, hq, ← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]
    congr 3; ext k; simp
  | monomial n c =>
    rw [aeval_monomial, x8_pow A W hW1 hW2 _ h n]
    simp only [eval_monomial]
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.one_mul, ← Matrix.smul_mul,
      ← Matrix.mul_smul, ← diagonal_smul]
    congr 3; ext k; simp [Pi.pow_apply]

theorem x8_trace_cfc {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (W : Matrix ι κ ℂ) (hW1 : Wᴴ * W = 1)
    (hW2 : W * Wᴴ = 1) (d : κ → ℝ)
    (h : A = W * diagonal (fun k => (d k : ℂ)) * Wᴴ) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ k, ((f (d k) : ℝ) : ℂ) := by
  classical
  let S : Finset ℝ := Finset.univ.image d ∪ Finset.univ.image hA.eigenvalues
  let p : ℝ[X] := Lagrange.interpolate S id f
  have hp : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) (r := f) (Set.injOn_id _) hx
  have h1 : cfc f A = cfc (fun x => p.eval x) A := by
    apply cfc_congr
    intro x hx
    rw [hA.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (hp _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))).symm
  rw [h1, cfc_polynomial p A, x8_aeval A W hW1 hW2 d h p, Matrix.trace_mul_cycle, hW1,
    Matrix.one_mul, trace_diagonal]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hp _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))]


theorem x8_spec {α : Type*} [Fintype α] [DecidableEq α] {A : Matrix α α ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix α α ℂ) *
      diagonal (fun k => ((hA.eigenvalues k : ℝ) : ℂ)) * (hA.eigenvectorUnitary : Matrix α α ℂ)ᴴ := by
  conv_lhs => rw [hA.spectral_theorem]
  rfl

theorem x8_U1 {α : Type*} [Fintype α] [DecidableEq α] {A : Matrix α α ℂ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix α α ℂ)ᴴ * (hA.eigenvectorUnitary : Matrix α α ℂ) = 1 :=
  Unitary.coe_star_mul_self _

theorem x8_U2 {α : Type*} [Fintype α] [DecidableEq α] {A : Matrix α α ℂ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix α α ℂ) * (hA.eigenvectorUnitary : Matrix α α ℂ)ᴴ = 1 :=
  Unitary.coe_mul_star_self _

theorem x8_ent_eig {α : Type*} [Fintype α] [DecidableEq α] {A : Matrix α α ℂ} (hA : A.IsHermitian) :
    vnEntropy A = -∑ k, hA.eigenvalues k * Real.logb 2 (hA.eigenvalues k) := by
  unfold vnEntropy
  rw [x8_trace_cfc A hA _ (x8_U1 hA) (x8_U2 hA) _ (x8_spec hA)]
  simp [Complex.re_sum]

theorem x8_sum_eig {α : Type*} [Fintype α] [DecidableEq α] {A : Matrix α α ℂ} (hA : A.IsHermitian)
    (ht : A.trace = 1) : ∑ k, hA.eigenvalues k = 1 := by
  have := hA.trace_eq_sum_eigenvalues
  rw [ht] at this
  have h2 := congrArg Complex.re this
  simpa [Complex.re_sum] using h2.symm

theorem x8_flog (x y : ℝ) : x * y * Real.logb 2 (x * y) =
    x * (y * Real.logb 2 y) + y * (x * Real.logb 2 x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  rw [Real.logb_mul hx hy]; ring


theorem x8_ent_sigma {ι γ : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ j, Fintype (α j)] [∀ j, DecidableEq (α j)] [Fintype γ] [DecidableEq γ]
    (N : (j : ι) → Matrix (α j) (α j) ℂ) (hN : ∀ j, (N j).IsHermitian)
    (ht : ∀ j, (N j).trace = 1) (p : ι → ℝ) (e : γ ≃ Σ j, α j) :
    vnEntropy ((blockDiagonal' fun j => ((p j : ℂ) • N j)).submatrix e e) =
      -∑ j, p j * Real.logb 2 (p j) + ∑ j, p j * vnEntropy (N j) := by
  set U : (j : ι) → Matrix (α j) (α j) ℂ := fun j => ((hN j).eigenvectorUnitary : Matrix (α j) (α j) ℂ)
    with hU
  set BU : Matrix (Σ j, α j) (Σ j, α j) ℂ := blockDiagonal' U with hBU
  set W : Matrix γ (Σ j, α j) ℂ := BU.submatrix e (Equiv.refl _) with hWd
  have hWc : Wᴴ = BUᴴ.submatrix (Equiv.refl _) e := by
    rw [hWd, conjTranspose_submatrix]
  have hB1 : BUᴴ * BU = 1 := by
    rw [hBU, blockDiagonal'_conjTranspose, ← blockDiagonal'_mul]
    simp only [hU, x8_U1]
    exact blockDiagonal'_one
  have hB2 : BU * BUᴴ = 1 := by
    rw [hBU, blockDiagonal'_conjTranspose, ← blockDiagonal'_mul]
    simp only [hU, x8_U2]
    exact blockDiagonal'_one
  have hW1 : Wᴴ * W = 1 := by
    rw [hWc, hWd, submatrix_mul_equiv, hB1, submatrix_one_equiv]
  have hW2 : W * Wᴴ = 1 := by
    rw [hWc, hWd, submatrix_mul_equiv, hB2, submatrix_one_equiv]
  set D := diagonal (fun k : Σ j, α j => ((p k.1 * (hN k.1).eigenvalues k.2 : ℝ) : ℂ)) with hD
  have hM : (blockDiagonal' fun j => ((p j : ℂ) • N j)).submatrix e e = W * D * Wᴴ := by
    have hk : (blockDiagonal' fun j => ((p j : ℂ) • N j)) = BU * D * BUᴴ := by
      have hj : ∀ j, ((p j : ℂ) • N j) = U j *
          diagonal (fun k => ((p j * (hN j).eigenvalues k : ℝ) : ℂ)) * (U j)ᴴ := by
        intro j
        conv_lhs => rw [x8_spec (hN j)]
        rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
        congr 3; ext k; push_cast; simp
      simp_rw [hj]
      rw [blockDiagonal'_mul, blockDiagonal'_mul, hD, blockDiagonal'_diagonal, hBU,
        blockDiagonal'_conjTranspose]
    rw [hk, hWc, hWd, ← submatrix_mul_equiv _ _ e (Equiv.refl (Σ j, α j)) e,
      ← submatrix_mul_equiv _ _ e (Equiv.refl (Σ j, α j)) (Equiv.refl (Σ j, α j))]
    simp
  have hH : ((blockDiagonal' fun j => ((p j : ℂ) • N j)).submatrix e e).IsHermitian := by
    have : (blockDiagonal' fun j => ((p j : ℂ) • N j)).IsHermitian := by
      rw [IsHermitian, blockDiagonal'_conjTranspose]
      congr 1; funext j
      rw [conjTranspose_smul, (hN j).eq]
      simp
    exact this.submatrix e
  have hE : ∀ j, vnEntropy (N j) =
      -∑ k, (hN j).eigenvalues k * Real.logb 2 ((hN j).eigenvalues k) := fun j => x8_ent_eig (hN j)
  simp_rw [hE]
  unfold vnEntropy
  rw [x8_trace_cfc _ hH W hW1 hW2 (fun k : Σ j, α j => p k.1 * (hN k.1).eigenvalues k.2) hM]
  simp only [Complex.re_sum, Complex.ofReal_re]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  simp_rw [x8_flog, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    x8_sum_eig (hN _) (ht _)]
  simp only [one_mul, Finset.sum_neg_distrib, Finset.sum_add_distrib, mul_neg]
  ring

end X8P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P46

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P08
  (Ensemble ensembleAverage outputHolevo mixedRoof)

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

theorem x8_ch_herm {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] {Phi : Superop A B}
    (h : IsChannel Phi) {X : Matrix A A ℂ} (hX : X.IsHermitian) : (Phi X).IsHermitian := by
  obtain ⟨m, E, -, hE⟩ := h
  rw [hE X, Matrix.IsHermitian, krausApply, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hX.eq,
    Matrix.mul_assoc]

theorem x8_ch_trace {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] {Phi : Superop A B}
    (h : IsChannel Phi) (X : Matrix A A ℂ) : (Phi X).trace = X.trace := by
  obtain ⟨m, E, hK, hE⟩ := h
  rw [hE X, krausApply, Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (E _) X]
  rw [← Matrix.trace_sum, ← Finset.sum_mul]
  unfold IsKrausFamily at hK
  rw [hK, Matrix.one_mul]

theorem x8_avg_herm (e : Ensemble I) : (ensembleAverage e).IsHermitian := by
  unfold ensembleAverage
  rw [Matrix.IsHermitian, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.conjTranspose_smul, (e.density x).1.1.eq, star_trivial]

theorem x8_avg_trace (e : Ensemble I) : (ensembleAverage e).trace = 1 := by
  unfold ensembleAverage
  rw [Matrix.trace_sum]
  have h : ∀ x, (e.prob x • e.state x).trace = (e.prob x : ℂ) := fun x => by
    rw [Matrix.trace_smul, (e.density x).2]; simp [Complex.real_smul]
  simp_rw [h]
  exact_mod_cast e.total

theorem x8_flag {T : Type} [Fintype T] [DecidableEq T] {B : T → Type} [∀ t, Fintype (B t)]
    [∀ t, DecidableEq (B t)] (q : T → ℝ) (Phi : (t : T) → Superop I (B t)) (X : Matrix I I ℂ) :
    flaggedChannelSum q Phi X =
      (Matrix.blockDiagonal' fun t => ((q t : ℂ) • Phi t X)).submatrix (Equiv.refl _) (Equiv.refl _) := by
  ext ⟨k, i⟩ ⟨k', j⟩
  simp only [Matrix.submatrix_apply, Equiv.refl_apply, Matrix.blockDiagonal'_apply']
  unfold flaggedChannelSum
  by_cases h : k = k'
  · subst h; simp
  · simp [h]

theorem x8_flag_ent {T : Type} [Fintype T] [DecidableEq T] {B : T → Type} [∀ t, Fintype (B t)]
    [∀ t, DecidableEq (B t)] (q : T → ℝ) (Phi : (t : T) → Superop I (B t))
    (hPhi : ∀ t, IsChannel (Phi t)) (X : Matrix I I ℂ) (hX : X.IsHermitian) (htr : X.trace = 1) :
    vnEntropy (flaggedChannelSum q Phi X) =
      -∑ t, q t * Real.logb 2 (q t) + ∑ t, q t * vnEntropy (Phi t X) := by
  rw [x8_flag]
  exact X8P46.x8_ent_sigma (fun t => Phi t X) (fun t => x8_ch_herm (hPhi t) hX)
    (fun t => by rw [x8_ch_trace (hPhi t), htr]) q (Equiv.refl _)

theorem x8_main [Nonempty I] {T : Type} [Fintype T] [DecidableEq T]
    [Nonempty T] {B : T → Type} [∀ t, Fintype (B t)] [∀ t, DecidableEq (B t)]
    [∀ t, Nonempty (B t)] (q : T → ℝ) (hq : ∀ t, 0 ≤ q t) (hsum : ∑ t, q t = 1)
    (Phi : (t : T) → Superop I (B t)) (hPhi : ∀ t, IsChannel (Phi t)) (e : Ensemble I) :
    outputHolevo (flaggedChannelSum q Phi) e = ∑ t, q t * outputHolevo (Phi t) e := by
  unfold outputHolevo
  rw [x8_flag_ent q Phi hPhi _ (x8_avg_herm e) (x8_avg_trace e)]
  simp_rw [x8_flag_ent q Phi hPhi _ (e.density _).1.1 (e.density _).2]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, e.total, one_mul, mul_sub,
    Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun x t => e.prob x * (q t * vnEntropy (Phi t (e.state x))))]
  ring_nf
  congr 1
  exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun x _ => by ring

end QAlgorithms.Papers.Independent.Gap48.P46

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P46 in
open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage outputHolevo) in
theorem solution {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {T : Type} [Fintype T]
    [DecidableEq T] [Nonempty T] {B : T → Type} [∀ t, Fintype (B t)] [∀ t, DecidableEq (B t)]
    [∀ t, Nonempty (B t)] (q : T → ℝ) (hq : ∀ t, 0 ≤ q t) (hsum : ∑ t, q t = 1)
    (Phi : (t : T) → Superop I (B t)) (hPhi : ∀ t, IsChannel (Phi t)) (e : Ensemble I) :
    outputHolevo (flaggedChannelSum q Phi) e = ∑ t, q t * outputHolevo (Phi t) e :=
  x8_main q hq hsum Phi hPhi e
