-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P46.shor_extension_channel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T15:34:16.803002+00:00
-- url     : https://prove2.me/submissions/83522813-994d-42d6-a1f5-9d8e5b960e5f

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

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P46

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

theorem x8_isChannel_of {A B κ : Type} [Fintype A] [Fintype B] [DecidableEq A] [Fintype κ]
    (Phi : Superop A B) (F : κ → Matrix B A ℂ) (hF : ∑ k, (F k)ᴴ * F k = 1)
    (hPhi : ∀ X, Phi X = ∑ k, F k * X * (F k)ᴴ) : IsChannel Phi := by
  let e := Fintype.equivFin κ
  refine ⟨Fintype.card κ, fun n => F (e.symm n), ?_, fun X => ?_⟩
  · unfold IsKrausFamily; rw [← hF, ← e.symm.sum_comp]
  · rw [hPhi X, krausApply, ← e.symm.sum_comp]

theorem x8_shor_ll (Phi : Superop I O) (E : Matrix I I ℂ) (q : ℝ) (d : ℕ)
    (X : Matrix (I × Fin d) (I × Fin d) ℂ) (i j : O) :
    shor Phi E q d X (.inl i) (.inl j) = ((1 - q : ℝ) : ℂ) * Phi (traceRight X) i j := rfl

theorem x8_shor_lr (Phi : Superop I O) (E : Matrix I I ℂ) (q : ℝ) (d : ℕ)
    (X : Matrix (I × Fin d) (I × Fin d) ℂ) (i : O) (j : Option (Fin d)) :
    shor Phi E q d X (.inl i) (.inr j) = 0 := rfl

theorem x8_shor_rl (Phi : Superop I O) (E : Matrix I I ℂ) (q : ℝ) (d : ℕ)
    (X : Matrix (I × Fin d) (I × Fin d) ℂ) (i : Option (Fin d)) (j : O) :
    shor Phi E q d X (.inr i) (.inl j) = 0 := rfl

theorem x8_shor_nn (Phi : Superop I O) (E : Matrix I I ℂ) (q : ℝ) (d : ℕ)
    (X : Matrix (I × Fin d) (I × Fin d) ℂ) :
    shor Phi E q d X (.inr none) (.inr none) = (q : ℂ) * ((1 - E) * traceRight X).trace := by
  simp [shor]

theorem x8_shor_ns (Phi : Superop I O) (E : Matrix I I ℂ) (q : ℝ) (d : ℕ)
    (X : Matrix (I × Fin d) (I × Fin d) ℂ) (k : Fin d) :
    shor Phi E q d X (.inr none) (.inr (some k)) = 0 := by
  simp [shor]

theorem x8_shor_sn (Phi : Superop I O) (E : Matrix I I ℂ) (q : ℝ) (d : ℕ)
    (X : Matrix (I × Fin d) (I × Fin d) ℂ) (k : Fin d) :
    shor Phi E q d X (.inr (some k)) (.inr none) = 0 := by
  simp [shor]

theorem x8_shor_ss (Phi : Superop I O) (E : Matrix I I ℂ) (q : ℝ) (d : ℕ)
    (X : Matrix (I × Fin d) (I × Fin d) ℂ) (k k' : Fin d) :
    shor Phi E q d X (.inr (some k)) (.inr (some k')) =
      if k = k' then (q : ℂ) * (E * (Matrix.of fun i j => X (i,k) (j,k))).trace else 0 := by
  simp [shor]

theorem x8_dephase (Phi : Superop I O) (E : Matrix I I ℂ) (q : ℝ) (d : ℕ)
    (X : Matrix (I × Fin d) (I × Fin d) ℂ) :
    shor Phi E q d X = shor Phi E q d (dephaseLabel d X) := by
  have htr : traceRight (dephaseLabel d X) = traceRight X := by
    ext i j; simp [traceRight, dephaseLabel]
  ext (a | a) (b | b)
  · rw [x8_shor_ll, x8_shor_ll, htr]
  · rfl
  · rfl
  · rcases a with _ | k <;> rcases b with _ | k'
    · rw [x8_shor_nn, x8_shor_nn, htr]
    · rw [x8_shor_ns, x8_shor_ns]
    · rw [x8_shor_sn, x8_shor_sn]
    · rw [x8_shor_ss, x8_shor_ss]
      congr 3
      ext i j; simp [dephaseLabel]

section kraus
variable {d : ℕ}

def x8R (k : Fin d) : Matrix I (I × Fin d) ℂ := Matrix.of fun i p => if p = (i, k) then 1 else 0

theorem x8_R1 (M : Matrix I I ℂ) :
    ∑ k : Fin d, (x8R (I := I) k)ᴴ * M * x8R (I := I) k = Matrix.kronecker M (1 : Matrix (Fin d) (Fin d) ℂ) := by
  ext ⟨i1, k1⟩ ⟨i2, k2⟩
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, x8R, Matrix.of_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq,
    apply_ite (star : ℂ → ℂ), star_one, star_zero, ite_mul, mul_ite, one_mul, zero_mul, mul_one,
    mul_zero, ite_and]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel,
    Finset.sum_const_zero]

theorem x8_R2 (k : Fin d) (X : Matrix (I × Fin d) (I × Fin d) ℂ) :
    x8R (I := I) k * X * (x8R (I := I) k)ᴴ = Matrix.of fun i j => X (i, k) (j, k) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, x8R, Matrix.of_apply,
    apply_ite (star : ℂ → ℂ), star_one, star_zero, ite_mul, mul_ite, one_mul, zero_mul, mul_one,
    mul_zero]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem x8_R3 (X : Matrix (I × Fin d) (I × Fin d) ℂ) :
    ∑ k : Fin d, (Matrix.of fun i j => X (i, k) (j, k) : Matrix I I ℂ) = traceRight X := by
  ext i j; simp [traceRight, Matrix.sum_apply]

def x8L : Matrix (O ⊕ Option (Fin d)) O ℂ := Matrix.of fun a o => if a = .inl o then 1 else 0

def x8e (r : Option (Fin d)) : O ⊕ Option (Fin d) → ℂ := fun a => if a = .inr r then 1 else 0

theorem x8_LL : (x8L (O := O) (d := d))ᴴ * x8L (O := O) (d := d) = 1 := by
  ext o o'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, x8L, Matrix.of_apply, Matrix.one_apply,
    apply_ite (star : ℂ → ℂ), star_one, star_zero, ite_mul, one_mul, zero_mul,
    Fintype.sum_sum_type, Sum.inl.injEq, reduceCtorEq, if_false, Finset.sum_const_zero, add_zero]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]

theorem x8_ee (r : Option (Fin d)) : star (x8e (O := O) r) ⬝ᵥ x8e r = 1 := by
  simp [dotProduct, x8e, apply_ite (star : ℂ → ℂ)]

theorem x8_LYL (Y : Matrix O O ℂ) (a b : O ⊕ Option (Fin d)) :
    (x8L (O := O) (d := d) * Y * (x8L (O := O) (d := d))ᴴ) a b =
      match a, b with
      | .inl o, .inl o' => Y o o'
      | _, _ => 0 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, x8L, Matrix.of_apply,
    apply_ite (star : ℂ → ℂ), star_one, star_zero, ite_mul, mul_ite, one_mul, zero_mul, mul_one,
    mul_zero]
  rcases a with o | r <;> rcases b with o' | r' <;>
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem x8_vv (a b : O ⊕ Option (Fin d)) (r r' : Option (Fin d)) :
    Matrix.vecMulVec (x8e (O := O) r) (star (x8e r')) a b =
      if a = .inr r ∧ b = .inr r' then 1 else 0 := by
  by_cases ha : a = .inr r <;> by_cases hb : b = .inr r' <;>
    simp [Matrix.vecMulVec_apply, x8e, apply_ite (star : ℂ → ℂ), ha, hb]

end kraus

end QAlgorithms.Papers.Independent.Gap48.P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P46

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

theorem x8_vtr (v : I → ℂ) (Y : Matrix I I ℂ) :
    (star v ᵥ* Y) ⬝ᵥ v = (Matrix.vecMulVec v (star v) * Y).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct,
    Matrix.vecMul, Pi.star_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem x8_vsandwich {d : ℕ} (v : I → ℂ) (r : Option (Fin d)) (Y : Matrix I I ℂ) :
    Matrix.vecMulVec (x8e (O := O) r) (star v) * Y * (Matrix.vecMulVec (x8e (O := O) r) (star v))ᴴ =
      (Matrix.vecMulVec v (star v) * Y).trace • Matrix.vecMulVec (x8e (O := O) r) (star (x8e r)) := by
  rw [Matrix.conjTranspose_vecMulVec, star_star, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul_vecMulVec,
    x8_vtr]
  ext a b
  simp [Matrix.vecMulVec_apply]; ring

theorem x8_vnorm {d : ℕ} (v : I → ℂ) (r : Option (Fin d)) :
    (Matrix.vecMulVec (x8e (O := O) r) (star v))ᴴ * Matrix.vecMulVec (x8e (O := O) r) (star v) =
      Matrix.vecMulVec v (star v) := by
  rw [Matrix.conjTranspose_vecMulVec, star_star, Matrix.vecMulVec_mul_vecMulVec, x8_ee, one_smul]

theorem x8_N1 {m d : ℕ} (Ek : Fin m → Matrix O I ℂ) (hK : ∑ μ, (Ek μ)ᴴ * Ek μ = 1) (c r : ℂ)
    (hc : c * star c = r) :
    ∑ x : Fin m × Fin d, (c • (x8L (O := O) (d := d) * Ek x.1 * x8R (I := I) x.2))ᴴ *
      (c • (x8L (O := O) (d := d) * Ek x.1 * x8R (I := I) x.2)) = r • 1 := by
  have h : ∀ x : Fin m × Fin d, (c • (x8L (O := O) (d := d) * Ek x.1 * x8R (I := I) x.2))ᴴ *
      (c • (x8L (O := O) (d := d) * Ek x.1 * x8R (I := I) x.2)) =
      r • ((x8R (I := I) x.2)ᴴ * ((Ek x.1)ᴴ * Ek x.1) * x8R (I := I) x.2 :
        Matrix (I × Fin d) (I × Fin d) ℂ) := by
    intro x
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (x8L (O := O) (d := d))ᴴ, x8_LL, Matrix.one_mul, hc]
  simp only [h]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [← Finset.smul_sum]
  congr 1
  have : ∀ k : Fin d, ∑ μ, ((x8R (I := I) k)ᴴ * ((Ek μ)ᴴ * Ek μ) * x8R (I := I) k :
        Matrix (I × Fin d) (I × Fin d) ℂ) =
      (x8R (I := I) k)ᴴ * (1 : Matrix I I ℂ) * x8R (I := I) k := by
    intro k; rw [← Matrix.sum_mul, ← Matrix.mul_sum, hK]
  simp only [this]
  rw [x8_R1]
  unfold Matrix.kronecker
  exact Matrix.one_kronecker_one

theorem x8_N2 {n d : ℕ} (v : Fin n → I → ℂ) (r : Fin d → Option (Fin d)) (c t : ℂ)
    (hc : c * star c = t) :
    ∑ x : Fin n × Fin d, (c • (Matrix.vecMulVec (x8e (O := O) (r x.2)) (star (v x.1)) * x8R (I := I) x.2))ᴴ *
      (c • (Matrix.vecMulVec (x8e (O := O) (r x.2)) (star (v x.1)) * x8R (I := I) x.2)) =
      t • Matrix.kronecker (∑ l, Matrix.vecMulVec (v l) (star (v l))) (1 : Matrix (Fin d) (Fin d) ℂ) := by
  have h : ∀ x : Fin n × Fin d,
      (c • (Matrix.vecMulVec (x8e (O := O) (r x.2)) (star (v x.1)) * x8R (I := I) x.2))ᴴ *
      (c • (Matrix.vecMulVec (x8e (O := O) (r x.2)) (star (v x.1)) * x8R (I := I) x.2)) =
      t • ((x8R (I := I) x.2)ᴴ * Matrix.vecMulVec (v x.1) (star (v x.1)) * x8R (I := I) x.2 :
        Matrix (I × Fin d) (I × Fin d) ℂ) := by
    intro x
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.conjTranspose_mul]
    rw [hc]
    congr 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.vecMulVec _ _)ᴴ, x8_vnorm, Matrix.mul_assoc]
  simp only [h]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [← Finset.smul_sum]
  congr 1
  have : ∀ k : Fin d, ∑ l, ((x8R (I := I) k)ᴴ * Matrix.vecMulVec (v l) (star (v l)) * x8R (I := I) k :
        Matrix (I × Fin d) (I × Fin d) ℂ) =
      (x8R (I := I) k)ᴴ * (∑ l, Matrix.vecMulVec (v l) (star (v l))) * x8R (I := I) k := by
    intro k; rw [← Matrix.sum_mul, ← Matrix.mul_sum]
  simp only [this]
  rw [x8_R1]

theorem x8_A1 {m d : ℕ} (Ek : Fin m → Matrix O I ℂ) (c r : ℂ) (hc : c * star c = r)
    (X : Matrix (I × Fin d) (I × Fin d) ℂ) :
    ∑ x : Fin m × Fin d, (c • (x8L (O := O) (d := d) * Ek x.1 * x8R (I := I) x.2)) * X *
      (c • (x8L (O := O) (d := d) * Ek x.1 * x8R (I := I) x.2))ᴴ =
      r • (x8L (O := O) (d := d) * (∑ μ, Ek μ * traceRight X * (Ek μ)ᴴ) * (x8L (O := O) (d := d))ᴴ) := by
  have h : ∀ x : Fin m × Fin d, (c • (x8L (O := O) (d := d) * Ek x.1 * x8R (I := I) x.2)) * X *
      (c • (x8L (O := O) (d := d) * Ek x.1 * x8R (I := I) x.2))ᴴ =
      r • (x8L (O := O) (d := d) * (Ek x.1 * (Matrix.of fun i j => X (i, x.2) (j, x.2)) * (Ek x.1)ᴴ) *
        (x8L (O := O) (d := d))ᴴ) := by
    intro x
    rw [← x8_R2]
    have hc' : star c * c = r := by rw [mul_comm]; exact hc
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.conjTranspose_mul, hc', Matrix.mul_assoc]
  simp only [h]
  rw [Fintype.sum_prod_type]
  dsimp only
  simp only [← Finset.smul_sum]
  congr 1
  simp only [← Matrix.mul_sum, ← Matrix.sum_mul, x8_R3]

theorem x8_A2 {n d : ℕ} (v : Fin n → I → ℂ) (r : Fin d → Option (Fin d)) (c t : ℂ)
    (hc : c * star c = t) (X : Matrix (I × Fin d) (I × Fin d) ℂ) :
    ∑ x : Fin n × Fin d, (c • (Matrix.vecMulVec (x8e (O := O) (r x.2)) (star (v x.1)) * x8R (I := I) x.2)) * X *
      (c • (Matrix.vecMulVec (x8e (O := O) (r x.2)) (star (v x.1)) * x8R (I := I) x.2))ᴴ =
      ∑ k : Fin d, (t * ((∑ l, Matrix.vecMulVec (v l) (star (v l))) *
        (Matrix.of fun i j => X (i, k) (j, k))).trace) •
          Matrix.vecMulVec (x8e (O := O) (r k)) (star (x8e (r k))) := by
  have h : ∀ x : Fin n × Fin d,
      (c • (Matrix.vecMulVec (x8e (O := O) (r x.2)) (star (v x.1)) * x8R (I := I) x.2)) * X *
      (c • (Matrix.vecMulVec (x8e (O := O) (r x.2)) (star (v x.1)) * x8R (I := I) x.2))ᴴ =
      (t * (Matrix.vecMulVec (v x.1) (star (v x.1)) * (Matrix.of fun i j => X (i, x.2) (j, x.2))).trace) •
        Matrix.vecMulVec (x8e (O := O) (r x.2)) (star (x8e (r x.2))) := by
    intro x
    rw [← smul_smul, ← hc, ← x8_vsandwich, ← x8_R2]
    have hc' : star c * c = c * star c := mul_comm _ _
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.conjTranspose_mul, Matrix.mul_assoc, hc']
  simp only [h]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  dsimp only
  rw [← Finset.sum_smul, Finset.sum_mul, Matrix.trace_sum, Finset.mul_sum]

theorem x8_ss (x : ℝ) (hx : 0 ≤ x) :
    ((Real.sqrt x : ℝ) : ℂ) * star ((Real.sqrt x : ℝ) : ℂ) = (x : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hx]

theorem x8_shor_channel (Phi : Superop I O) (hPhi : IsChannel Phi) (E : Matrix I I ℂ)
    (hE : IsEffect E) (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) (d : ℕ) :
    IsChannel (shor Phi E q d) := by
  obtain ⟨m, Ek, hK, hEk⟩ := hPhi
  obtain ⟨n1, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hE.2
  obtain ⟨n2, w, hw⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hE.1
  set s1 : ℂ := ((Real.sqrt (1 - q) : ℝ) : ℂ) with hs1
  set s2 : ℂ := ((Real.sqrt q : ℝ) : ℂ) with hs2
  have h1 : s1 * star s1 = ((1 - q : ℝ) : ℂ) := x8_ss _ (by linarith [hq.2])
  have h2 : s2 * star s2 = (q : ℂ) := x8_ss _ hq.1
  let F : (Fin m × Fin d) ⊕ ((Fin n1 × Fin d) ⊕ (Fin n2 × Fin d)) →
      Matrix (O ⊕ Option (Fin d)) (I × Fin d) ℂ :=
    Sum.elim (fun x => s1 • (x8L (O := O) (d := d) * Ek x.1 * x8R (I := I) x.2))
      (Sum.elim (fun x => s2 • (Matrix.vecMulVec (x8e (O := O) none) (star (v x.1)) * x8R (I := I) x.2))
        (fun x => s2 • (Matrix.vecMulVec (x8e (O := O) (some x.2)) (star (w x.1)) * x8R (I := I) x.2)))
  refine x8_isChannel_of _ F ?_ ?_
  · rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [F, Sum.elim_inl, Sum.elim_inr]
    have e1 := x8_N1 (O := O) (d := d) Ek hK s1 _ h1
    have e2 := x8_N2 (O := O) v (fun _ : Fin d => none) s2 _ h2
    have e3 := x8_N2 (O := O) w (fun k : Fin d => some k) s2 _ h2
    rw [e1, e2, e3, ← hv, ← hw, ← smul_add]
    unfold Matrix.kronecker
    rw [← Matrix.add_kronecker, sub_add_cancel, Matrix.one_kronecker_one, ← add_smul]
    push_cast; simp
  · intro X
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [F, Sum.elim_inl, Sum.elim_inr]
    have e1 := x8_A1 (O := O) Ek s1 _ h1 X
    have e2 := x8_A2 (O := O) v (fun _ : Fin d => none) s2 _ h2 X
    have e3 := x8_A2 (O := O) w (fun k : Fin d => some k) s2 _ h2 X
    rw [e1, e2, e3, ← hv, ← hw]
    have hPhiX : Phi (traceRight X) = ∑ μ, Ek μ * traceRight X * (Ek μ)ᴴ := hEk _
    rw [← hPhiX]
    have htr : ∑ k : Fin d, (((1 : Matrix I I ℂ) - E) * Matrix.of fun i j => X (i, k) (j, k)).trace =
        (((1 : Matrix I I ℂ) - E) * traceRight X).trace := by
      rw [← x8_R3, Matrix.mul_sum, Matrix.trace_sum]
    ext a b
    rcases a with o | r <;> rcases b with o' | r'
    · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, x8_LYL, x8_vv, x8_shor_ll,
        smul_eq_mul, reduceCtorEq, false_and, if_false, mul_zero, Finset.sum_const_zero, add_zero]
    · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, x8_LYL, x8_vv, x8_shor_lr,
        smul_eq_mul, reduceCtorEq, false_and, if_false, mul_zero, Finset.sum_const_zero, add_zero]
    · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, x8_LYL, x8_vv, x8_shor_rl,
        smul_eq_mul, reduceCtorEq, and_false, if_false, mul_zero, Finset.sum_const_zero, add_zero]
    · rcases r with _ | k <;> rcases r' with _ | k'
      · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, x8_LYL, x8_vv, x8_shor_nn,
          smul_eq_mul, reduceCtorEq, and_self, if_true, if_false, mul_one, mul_zero,
          Finset.sum_const_zero, add_zero, zero_add, Sum.inr.injEq, and_false, false_and]
        rw [← Finset.mul_sum, htr]
      · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, x8_LYL, x8_vv, x8_shor_ns,
          smul_eq_mul, reduceCtorEq, and_self, if_true, if_false, mul_one, mul_zero,
          Finset.sum_const_zero, add_zero, zero_add, Sum.inr.injEq, and_false, false_and]
      · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, x8_LYL, x8_vv, x8_shor_sn,
          smul_eq_mul, reduceCtorEq, and_self, if_true, if_false, mul_one, mul_zero,
          Finset.sum_const_zero, add_zero, zero_add, Sum.inr.injEq, and_false, false_and]
      · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, x8_LYL, x8_vv, x8_shor_ss,
          smul_eq_mul, reduceCtorEq, if_false, mul_one, mul_zero,
          Finset.sum_const_zero, add_zero, zero_add, Sum.inr.injEq, and_false, false_and,
          Option.some.injEq, mul_ite]
        by_cases hk : k = k'
        · subst hk; simp [Finset.sum_ite_eq']
        · simp only [hk, if_false]
          symm; refine Finset.sum_eq_zero fun x _ => ?_
          rw [if_neg]; rintro ⟨h1, h2⟩; exact hk (h1.trans h2.symm)

theorem x8_shor_ext [Nonempty I] [Nonempty O]
    (Phi : Superop I O) (hPhi : IsChannel Phi) (E : Matrix I I ℂ) (hE : IsEffect E)
    (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) (d : ℕ) (hd : 1 ≤ d) :
    IsChannel (shor Phi E q d) ∧ ∀ X,
      shor Phi E q d X = shor Phi E q d (dephaseLabel d X) :=
  ⟨x8_shor_channel Phi hPhi E hE q hq d, x8_dephase Phi E q d⟩

end QAlgorithms.Papers.Independent.Gap48.P46

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P46 in
theorem solution {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    [Nonempty I] [Nonempty O]
    (Phi : Superop I O) (hPhi : IsChannel Phi) (E : Matrix I I ℂ) (hE : IsEffect E)
    (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) (d : ℕ) (hd : 1 ≤ d) :
    IsChannel (shor Phi E q d) ∧ ∀ X,
      shor Phi E q d X = shor Phi E q d (dephaseLabel d X) :=
  x8_shor_ext Phi hPhi E hE q hq d hd
