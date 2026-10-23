-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P47.entropy_hull_properties
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T12:47:53.647919+00:00
-- url     : https://prove2.me/submissions/3c0e3706-2979-4212-98db-34ba093521de

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P47

open scoped Matrix ComplexConjugate ComplexOrder Kronecker
open Matrix Polynomial

namespace X8P47
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

theorem x8_ent_diag {α : Type*} [Fintype α] [DecidableEq α] (q : α → ℝ) :
    vnEntropy (diagonal (fun i => (q i : ℂ))) = -∑ i, q i * Real.logb 2 (q i) := by
  unfold vnEntropy
  rw [x8_trace_cfc _ (isHermitian_diagonal_of_self_adjoint _ (by ext i; simp [Pi.star_apply]))
    (1 : Matrix α α ℂ) (by simp) (by simp) q (by simp)]
  simp [Complex.re_sum]

theorem x8_ent_blocks2 {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] {A : Matrix α α ℂ} {B : Matrix β β ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (htA : A.trace = 1) (htB : B.trace = 1)
    (a b : ℝ) (g : γ ≃ α ⊕ β) :
    vnEntropy ((fromBlocks ((a : ℂ) • A) 0 0 ((b : ℂ) • B)).submatrix g g) =
      -(a * Real.logb 2 a + b * Real.logb 2 b) + a * vnEntropy A + b * vnEntropy B := by
  set U := (hA.eigenvectorUnitary : Matrix α α ℂ) with hU
  set V := (hB.eigenvectorUnitary : Matrix β β ℂ) with hV
  set BU : Matrix (α ⊕ β) (α ⊕ β) ℂ := fromBlocks U 0 0 V with hBU
  set W : Matrix γ (α ⊕ β) ℂ := BU.submatrix g (Equiv.refl _) with hWd
  have hWc : Wᴴ = BUᴴ.submatrix (Equiv.refl _) g := by
    rw [hWd, conjTranspose_submatrix]
  have hB1 : BUᴴ * BU = 1 := by
    rw [hBU, fromBlocks_conjTranspose, fromBlocks_multiply]
    simp [hU, hV, x8_U1, fromBlocks_one]
  have hB2 : BU * BUᴴ = 1 := by
    rw [hBU, fromBlocks_conjTranspose, fromBlocks_multiply]
    simp [hU, hV, x8_U2, fromBlocks_one]
  have hW1 : Wᴴ * W = 1 := by
    rw [hWc, hWd, submatrix_mul_equiv, hB1, submatrix_one_equiv]
  have hW2 : W * Wᴴ = 1 := by
    rw [hWc, hWd, submatrix_mul_equiv, hB2, submatrix_one_equiv]
  set d : α ⊕ β → ℝ := Sum.elim (fun k => a * hA.eigenvalues k) (fun k => b * hB.eigenvalues k)
    with hd
  have hM : (fromBlocks ((a : ℂ) • A) 0 0 ((b : ℂ) • B)).submatrix g g =
      W * diagonal (fun k => (d k : ℂ)) * Wᴴ := by
    have hk : fromBlocks ((a : ℂ) • A) 0 0 ((b : ℂ) • B) =
        BU * diagonal (fun k => (d k : ℂ)) * BUᴴ := by
      have e1 : (a : ℂ) • A = U * diagonal (fun k => ((a * hA.eigenvalues k : ℝ) : ℂ)) * Uᴴ := by
        conv_lhs => rw [x8_spec hA]
        rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
        congr 3; ext k; push_cast; simp
      have e2 : (b : ℂ) • B = V * diagonal (fun k => ((b * hB.eigenvalues k : ℝ) : ℂ)) * Vᴴ := by
        conv_lhs => rw [x8_spec hB]
        rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
        congr 3; ext k; push_cast; simp
      have hdd : diagonal (fun k => (d k : ℂ)) = fromBlocks
          (diagonal (fun k => ((a * hA.eigenvalues k : ℝ) : ℂ))) 0 0
          (diagonal (fun k => ((b * hB.eigenvalues k : ℝ) : ℂ))) := by
        rw [fromBlocks_diagonal]
        congr 1; ext k; cases k <;> simp [hd]
      rw [e1, e2, hdd, hBU, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
      simp
    rw [hk, hWc, hWd, ← submatrix_mul_equiv _ _ g (Equiv.refl (α ⊕ β)) g,
      ← submatrix_mul_equiv _ _ g (Equiv.refl (α ⊕ β)) (Equiv.refl (α ⊕ β))]
    simp
  have hH : ((fromBlocks ((a : ℂ) • A) 0 0 ((b : ℂ) • B)).submatrix g g).IsHermitian := by
    have : (fromBlocks ((a : ℂ) • A) 0 0 ((b : ℂ) • B)).IsHermitian := by
      rw [IsHermitian, fromBlocks_conjTranspose, conjTranspose_smul, conjTranspose_smul, hA.eq,
        hB.eq]
      simp
    exact this.submatrix g
  rw [x8_ent_eig hA, x8_ent_eig hB]
  unfold vnEntropy
  rw [x8_trace_cfc _ hH W hW1 hW2 d hM]
  simp only [Complex.re_sum, Complex.ofReal_re, Fintype.sum_sum_type, hd, Sum.elim_inl,
    Sum.elim_inr]
  rw [Complex.add_re, Complex.re_sum, Complex.re_sum]
  simp only [Complex.ofReal_re]
  simp_rw [mul_comm a, mul_comm b, x8_flog, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, x8_sum_eig hA htA, x8_sum_eig hB htB]
  ring

end X8P47


open scoped Matrix ComplexConjugate ComplexOrder
open Matrix

namespace X8P47
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P47
open QAlgorithms.Papers.Independent.Information100.P27 (shannon average)
open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)

theorem x8_ite_sum {ι : Type*} [Fintype ι] (c : Prop) [Decidable c] (g : ι → ℂ) :
    ∑ i, (if c then g i else 0) = if c then ∑ i, g i else 0 := by
  split_ifs <;> simp

theorem x8_trace_sub {α γ : Type*} [Fintype α] [Fintype γ] (A : Matrix α α ℂ) (e : γ ≃ α) :
    (A.submatrix e e).trace = A.trace := by
  simp only [trace, diag, submatrix_apply]
  exact e.sum_comp (fun i => A i i)

theorem x8_trace_fb {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α α ℂ) (B : Matrix β β ℂ) :
    (fromBlocks A 0 0 B).trace = A.trace + B.trace := by
  simp [trace, Fintype.sum_sum_type]

theorem x8_fb_psd {α β : Type*} [Fintype α] [Fintype β] {A : Matrix α α ℂ} {B : Matrix β β ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (fromBlocks A 0 0 B).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec] at hA hB ⊢
  refine ⟨?_, fun x => ?_⟩
  · rw [IsHermitian, fromBlocks_conjTranspose, hA.1.eq, hB.1.eq]; simp
  · rw [fromBlocks_mulVec]
    have h1 := hA.2 (x ∘ Sum.inl)
    have h2 := hB.2 (x ∘ Sum.inr)
    simp only [zero_mulVec, add_zero, zero_add] at *
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.star_apply] at *
    exact add_nonneg h1 h2

theorem x8_cq_herm {X Y D : Type} [Fintype X] [DecidableEq Y] (p : X → ℝ)
    (rho : X → Matrix D D ℂ) (hρ : ∀ x, (rho x).IsHermitian) (f : X → Y) :
    (cqMatrix p rho f).IsHermitian := by
  ext a b
  simp only [conjTranspose_apply, cqMatrix]
  by_cases h : a.1 = b.1
  · rw [if_pos h.symm, if_pos h, star_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [apply_ite star, star_zero, h]
    congr 1
    rw [star_mul', Complex.star_def, Complex.conj_ofReal]
    congr 1
    exact (hρ x).apply a.2 b.2
  · rw [if_neg (Ne.symm h), if_neg h, star_zero]

theorem x8_cq_trace {X Y D : Type} [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype D]
    (p : X → ℝ) (hp : ∑ x, p x = 1) (rho : X → Matrix D D ℂ) (ht : ∀ x, (rho x).trace = 1)
    (f : X → Y) : (cqMatrix p rho f).trace = 1 := by
  simp only [trace, diag, cqMatrix, if_true]
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.sum_comm (γ := D) (s := Finset.univ) (t := Finset.univ)]
  rw [Finset.sum_comm]
  simp_rw [x8_ite_sum, ← Finset.mul_sum]
  have : ∀ x, ∑ i, rho x i i = 1 := ht
  simp_rw [this, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact_mod_cast hp

theorem x8_avg_herm {X D : Type} [Fintype X] (p : X → ℝ)
    (rho : X → Matrix D D ℂ) (hρ : ∀ x, (rho x).IsHermitian) : (average p rho).IsHermitian := by
  unfold average
  rw [IsHermitian, conjTranspose_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [conjTranspose_smul, (hρ x).eq]
  simp

theorem x8_avg_trace {X D : Type} [Fintype X] [Fintype D]
    (p : X → ℝ) (hp : ∑ x, p x = 1) (rho : X → Matrix D D ℂ) (ht : ∀ x, (rho x).trace = 1) :
    (average p rho).trace = 1 := by
  unfold average
  rw [trace_sum]
  simp_rw [trace_smul, ht, smul_eq_mul, mul_one]
  exact_mod_cast hp

def x8g {Y α β δ : Type} (e : δ ≃ α ⊕ β) : Y × δ ≃ (Y × α) ⊕ (Y × β) :=
  (Equiv.prodCongr (Equiv.refl Y) e).trans (Equiv.prodSumDistrib Y α β)

theorem x8_cast_mul (p c a q : ℝ) (h : p * c = a * q) (r : ℂ) :
    (p : ℂ) * ((c : ℂ) * r) = (a : ℂ) * ((q : ℂ) * r) := by
  have h' : ((p * c : ℝ) : ℂ) = ((a * q : ℝ) : ℂ) := by rw [h]
  push_cast at h'
  rw [← mul_assoc, h', mul_assoc]

theorem x8_cq_blocks {X Y α β δ : Type} [Fintype X] [DecidableEq Y]
    (e : δ ≃ α ⊕ β) (p p1 p2 c c' : X → ℝ) (a b : ℝ)
    (hc : ∀ x, p x * c x = a * p1 x) (hc' : ∀ x, p x * c' x = b * p2 x)
    (ρ1 : X → Matrix α α ℂ) (ρ2 : X → Matrix β β ℂ) (f : X → Y) :
    cqMatrix p (fun x => (fromBlocks ((c x : ℂ) • ρ1 x) 0 0 ((c' x : ℂ) • ρ2 x)).submatrix e e) f =
      (fromBlocks ((a : ℂ) • cqMatrix p1 ρ1 f) 0 0 ((b : ℂ) • cqMatrix p2 ρ2 f)).submatrix
        (x8g e) (x8g e) := by
  ext ⟨y, i⟩ ⟨y', j⟩
  obtain ⟨i', rfl⟩ := e.symm.surjective i
  obtain ⟨j', rfl⟩ := e.symm.surjective j
  cases i' <;> cases j' <;>
  · simp only [cqMatrix, x8g, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl,
      Prod.map_apply, id, Equiv.apply_symm_apply, Equiv.prodSumDistrib_apply_left,
      Equiv.prodSumDistrib_apply_right, submatrix_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, mul_zero]
    split_ifs <;> simp only [Finset.mul_sum, mul_ite, mul_zero, ite_self, Finset.sum_const_zero]
    all_goals refine Finset.sum_congr rfl fun x _ => ?_
    all_goals split_ifs <;> first | rfl | exact x8_cast_mul _ _ _ _ (hc x) _ |
      exact x8_cast_mul _ _ _ _ (hc' x) _

theorem x8_avg_blocks {X α β δ : Type} [Fintype X]
    (e : δ ≃ α ⊕ β) (p p1 p2 c c' : X → ℝ) (a b : ℝ)
    (hc : ∀ x, p x * c x = a * p1 x) (hc' : ∀ x, p x * c' x = b * p2 x)
    (ρ1 : X → Matrix α α ℂ) (ρ2 : X → Matrix β β ℂ) :
    average p (fun x => (fromBlocks ((c x : ℂ) • ρ1 x) 0 0 ((c' x : ℂ) • ρ2 x)).submatrix e e) =
      (fromBlocks ((a : ℂ) • average p1 ρ1) 0 0 ((b : ℂ) • average p2 ρ2)).submatrix e e := by
  ext i j
  obtain ⟨i', rfl⟩ := e.symm.surjective i
  obtain ⟨j', rfl⟩ := e.symm.surjective j
  cases i' <;> cases j' <;>
  · simp only [average, Matrix.sum_apply, Matrix.smul_apply, submatrix_apply, Equiv.apply_symm_apply,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      smul_eq_mul, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, Finset.mul_sum]
    try (refine Finset.sum_congr rfl fun x _ => ?_)
    try exact x8_cast_mul _ _ _ _ (hc x) _
    try exact x8_cast_mul _ _ _ _ (hc' x) _

end X8P47


open scoped Matrix ComplexConjugate ComplexOrder
open Matrix

namespace X8P47
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P47
open QAlgorithms.Papers.Independent.Information100.P27 (shannon average)
open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)

theorem x8_qcond_mix {X Y α β δ : Type} [Fintype X] [Fintype Y] [DecidableEq Y]
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype δ] [DecidableEq δ]
    (e : δ ≃ α ⊕ β) (p p1 p2 c c' : X → ℝ) (a b : ℝ)
    (hp1 : ∑ x, p1 x = 1) (hp2 : ∑ x, p2 x = 1)
    (hc : ∀ x, p x * c x = a * p1 x) (hc' : ∀ x, p x * c' x = b * p2 x)
    (ρ1 : X → Matrix α α ℂ) (ρ2 : X → Matrix β β ℂ)
    (h1 : ∀ x, IsDensityMatrix (ρ1 x)) (h2 : ∀ x, IsDensityMatrix (ρ2 x)) (f : X → Y) :
    qCond p (fun x => (fromBlocks ((c x : ℂ) • ρ1 x) 0 0 ((c' x : ℂ) • ρ2 x)).submatrix e e) f =
      a * qCond p1 ρ1 f + b * qCond p2 ρ2 f := by
  unfold qCond
  rw [x8_cq_blocks e p p1 p2 c c' a b hc hc', x8_avg_blocks e p p1 p2 c c' a b hc hc',
    x8_ent_blocks2 (x8_cq_herm _ _ (fun x => (h1 x).1.1) f) (x8_cq_herm _ _ (fun x => (h2 x).1.1) f)
      (x8_cq_trace _ hp1 _ (fun x => (h1 x).2) f) (x8_cq_trace _ hp2 _ (fun x => (h2 x).2) f),
    x8_ent_blocks2 (x8_avg_herm _ _ (fun x => (h1 x).1.1)) (x8_avg_herm _ _ (fun x => (h2 x).1.1))
      (x8_avg_trace _ hp1 _ (fun x => (h1 x).2)) (x8_avg_trace _ hp2 _ (fun x => (h2 x).2))]
  ring

theorem x8_convex (m : ℕ) (s : Fin m → ℕ) : Convex ℝ (quantumHull m s) := by
  intro v hv w hw a b ha hb hab
  obtain ⟨p1, d1, hd1, Q1, hv1, hv2⟩ := hv
  obtain ⟨p2, d2, hd2, Q2, hw1, hw2⟩ := hw
  set P : Alphabet m s → ℝ := fun x => a * p1.prob x + b * p2.prob x with hP
  have hP0 : ∀ x, P x = 0 → a * p1.prob x = 0 ∧ b * p2.prob x = 0 := by
    intro x hx
    have := mul_nonneg ha (p1.nonneg x)
    have := mul_nonneg hb (p2.nonneg x)
    constructor <;> linarith
  let c : Alphabet m s → ℝ := fun x => if P x = 0 then 1 else a * p1.prob x / P x
  let c' : Alphabet m s → ℝ := fun x => if P x = 0 then 0 else b * p2.prob x / P x
  have hc : ∀ x, P x * c x = a * p1.prob x := by
    intro x
    by_cases h : P x = 0
    · simp only [c, if_pos h, h, zero_mul]; exact (hP0 x h).1.symm
    · simp only [c, if_neg h]; field_simp
  have hc' : ∀ x, P x * c' x = b * p2.prob x := by
    intro x
    by_cases h : P x = 0
    · simp only [c', if_pos h, h, zero_mul]; exact (hP0 x h).2.symm
    · simp only [c', if_neg h]; field_simp
  have hcn : ∀ x, 0 ≤ c x := by
    intro x; simp only [c]; split_ifs with h
    · exact zero_le_one
    · exact div_nonneg (mul_nonneg ha (p1.nonneg x)) (by
        have := mul_nonneg ha (p1.nonneg x); have := mul_nonneg hb (p2.nonneg x)
        simp only [hP]; linarith)
  have hcn' : ∀ x, 0 ≤ c' x := by
    intro x; simp only [c']; split_ifs with h
    · exact le_refl _
    · exact div_nonneg (mul_nonneg hb (p2.nonneg x)) (by
        have := mul_nonneg ha (p1.nonneg x); have := mul_nonneg hb (p2.nonneg x)
        simp only [hP]; linarith)
  have hcs : ∀ x, c x + c' x = 1 := by
    intro x
    by_cases h : P x = 0
    · simp [c, c', h]
    · simp only [c, c', if_neg h]
      rw [← add_div, div_eq_one_iff_eq h]
  let law : Law (Alphabet m s) :=
    { prob := P
      nonneg := fun x => add_nonneg (mul_nonneg ha (p1.nonneg x)) (mul_nonneg hb (p2.nonneg x))
      total := by
        simp only [hP, Finset.sum_add_distrib, ← Finset.mul_sum, p1.total, p2.total]
        linarith }
  let e : Fin (d1 + d2) ≃ Fin d1 ⊕ Fin d2 := finSumFinEquiv.symm
  let Q : QChannel (Alphabet m s) (Fin (d1 + d2)) :=
    { rho := fun x =>
        (fromBlocks ((c x : ℂ) • Q1.rho x) 0 0 ((c' x : ℂ) • Q2.rho x)).submatrix e e
      valid := by
        intro x
        refine ⟨(x8_fb_psd ((Q1.valid x).1.smul (by exact_mod_cast hcn x))
          ((Q2.valid x).1.smul (by exact_mod_cast hcn' x))).submatrix e, ?_⟩
        rw [x8_trace_sub, x8_trace_fb, trace_smul, trace_smul, (Q1.valid x).2, (Q2.valid x).2]
        simp only [smul_eq_mul, mul_one]
        exact_mod_cast hcs x }
  refine ⟨law, d1 + d2, by omega, Q, ?_, ?_⟩
  · simp only [Prod.fst_add, Prod.smul_fst, hv1, hw1]
    ext x; simp [law, hP]
  · intro i
    simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv2, hw2]
    exact (x8_qcond_mix e P p1.prob p2.prob c c' a b p1.total p2.total hc hc' Q1.rho Q2.rho
      Q1.valid Q2.valid (fun x => x i)).symm

theorem x8_cq_diag {X Y C : Type} [Fintype X] [Fintype C] [DecidableEq Y] [DecidableEq C]
    (p : X → ℝ) (K : X → C → ℝ) (f : X → Y) :
    cqMatrix p (fun x => diagonal (fun c => (K x c : ℂ))) f =
      diagonal (fun z : Y × C =>
        ((pushLaw (fun z : X × C => p z.1 * K z.1 z.2) (fun z => (f z.1, z.2)) z : ℝ) : ℂ)) := by
  ext ⟨y, c⟩ ⟨y', c'⟩
  simp only [cqMatrix, diagonal_apply, pushLaw, Prod.mk.injEq]
  by_cases hy : y = y'
  · subst hy
    by_cases hc : c = c'
    · subst hc
      simp only [and_self, if_true]
      rw [Fintype.sum_prod_type]
      push_cast
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : f x = y
      · simp only [hx, true_and, if_true]
        rw [Finset.sum_eq_single c (by intro b _ hb; simp [hb]) (by simp)]
        simp
      · simp [hx]
    · simp [hc]
  · simp [hy]

theorem x8_avg_diag {X C : Type} [Fintype X] [Fintype C] [DecidableEq C]
    (p : X → ℝ) (K : X → C → ℝ) :
    average p (fun x => diagonal (fun c => (K x c : ℂ))) =
      diagonal (fun c : C =>
        ((pushLaw (fun z : X × C => p z.1 * K z.1 z.2) Prod.snd c : ℝ) : ℂ)) := by
  ext c c'
  simp only [average, Matrix.sum_apply, Matrix.smul_apply, diagonal_apply, pushLaw, smul_eq_mul]
  by_cases hc : c = c'
  · subst hc
    simp only [if_true]
    rw [Fintype.sum_prod_type]
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single c (by intro b _ hb; simp [hb]) (by simp)]
    simp
  · simp [hc]

theorem x8_incl (m : ℕ) (s : Fin m → ℕ) : classicalHull m s ⊆ quantumHull m s := by
  rintro v ⟨p, k, hk, K, hv1, hv2⟩
  let Q : QChannel (Alphabet m s) (Fin k) :=
    { rho := fun x => diagonal (fun c => ((K x).prob c : ℂ))
      valid := by
        intro x
        refine ⟨PosSemidef.diagonal (fun c => by
          simp only [Pi.zero_apply]; exact_mod_cast (K x).nonneg c), ?_⟩
        rw [trace_diagonal]
        exact_mod_cast (K x).total }
  refine ⟨p, k, hk, Q, hv1, fun i => ?_⟩
  rw [hv2 i]
  unfold cCond qCond
  rw [x8_cq_diag p.prob (fun x c => (K x).prob c) (fun x => x i),
    x8_avg_diag p.prob (fun x c => (K x).prob c), x8_ent_diag, x8_ent_diag]
  rfl

end X8P47

open QAlgorithms.Papers.Independent.Dependency50.P47 in
theorem solution (m : ℕ) (s : Fin m → ℕ) (hs : ∀ i, 0 < s i) :
    Convex ℝ (quantumHull m s) ∧ classicalHull m s ⊆ quantumHull m s :=
  ⟨X8P47.x8_convex m s, X8P47.x8_incl m s⟩

