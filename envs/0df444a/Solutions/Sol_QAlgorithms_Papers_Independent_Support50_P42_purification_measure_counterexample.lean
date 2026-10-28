-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P42.purification_measure_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:15:33.088462+00:00
-- url     : https://prove2.me/submissions/cac2f3a8-8d0b-456d-b341-f0a9c553f40e

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

-- ===== ZEA =====

noncomputable section

namespace X4ZE
open Matrix QAlgorithms Real
open scoped Matrix ComplexConjugate ComplexOrder

/-- a unit vector `v` with `v v† = Σ φ_k φ_k†` forces every `φ_k ∈ span v`. -/
lemma rank1_split {α ι : Type*} [Fintype α] [Fintype ι] (v : α → ℂ) (hv : ∑ a, v a * conj (v a) = 1)
    (φ : ι → α → ℂ) (h : ∀ a b, v a * conj (v b) = ∑ k, φ k a * conj (φ k b)) (k : ι) :
    ∀ a, φ k a = (∑ b, conj (v b) * φ k b) * v a := by
  set c := ∑ b, conj (v b) * φ k b
  set ψ : α → ℂ := fun a => φ k a - c * v a
  have nsq : ∀ u w : α → ℂ, ((Complex.normSq (∑ a, conj (u a) * w a) : ℝ) : ℂ) =
      ∑ a, ∑ b, conj (u a) * (w a * conj (w b)) * u b := by
    intro u w
    rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [map_mul, Complex.conj_conj]; ring
  have hQ : ∀ ψ : α → ℂ, Complex.normSq (∑ a, conj (ψ a) * v a) =
      ∑ j, Complex.normSq (∑ a, conj (ψ a) * φ j a) := by
    intro ψ
    have : ((Complex.normSq (∑ a, conj (ψ a) * v a) : ℝ) : ℂ) =
        ((∑ j, Complex.normSq (∑ a, conj (ψ a) * φ j a) : ℝ) : ℂ) := by
      rw [nsq]; push_cast; simp_rw [nsq, h, Finset.mul_sum, Finset.sum_mul]
      calc ∑ a, ∑ b, ∑ j, conj (ψ a) * (φ j a * conj (φ j b)) * ψ b
          = ∑ a, ∑ j, ∑ b, conj (ψ a) * (φ j a * conj (φ j b)) * ψ b :=
            Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
    exact_mod_cast this
  have hψv : ∑ a, conj (ψ a) * v a = 0 := by
    have : ∑ a, conj (v a) * ψ a = 0 := by
      simp only [ψ, mul_sub, Finset.sum_sub_distrib]
      have : ∑ a, conj (v a) * (c * v a) = c * ∑ a, v a * conj (v a) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
      rw [this, hv, mul_one]; simp [c]
    have := congrArg conj this
    rw [map_sum, map_zero] at this
    rw [← this]; exact Finset.sum_congr rfl fun a _ => by simp [mul_comm]
  have hψφ : ∑ a, conj (ψ a) * φ k a = ∑ a, conj (ψ a) * ψ a := by
    have : ∀ a, φ k a = ψ a + c * v a := fun a => by simp [ψ]
    simp_rw [this, mul_add, Finset.sum_add_distrib]
    have : ∑ a, conj (ψ a) * (c * v a) = c * ∑ a, conj (ψ a) * v a := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
    rw [this, hψv, mul_zero, add_zero]
  have hz := hQ ψ
  rw [hψv, map_zero] at hz
  have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg _)).1 hz.symm k
    (Finset.mem_univ k)
  rw [hψφ, Complex.normSq_eq_zero] at hk
  have hn : ∑ a, Complex.normSq (ψ a) = 0 := by
    have : ((∑ a, Complex.normSq (ψ a) : ℝ) : ℂ) = 0 := by
      push_cast; rw [← hk]
      exact Finset.sum_congr rfl fun a _ => by rw [Complex.normSq_eq_conj_mul_self]
    exact_mod_cast this
  intro a
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Complex.normSq_nonneg _)).1 hn a
    (Finset.mem_univ a)
  rw [Complex.normSq_eq_zero] at this
  simp only [ψ, sub_eq_zero] at this
  exact this

/-- spectral decomposition as a sum of eigenprojectors. -/
lemma spec_sum {I : Type*} [Fintype I] [DecidableEq I] {ρ : Matrix I I ℂ} (h : ρ.IsHermitian) :
    ρ = ∑ k, ((h.eigenvalues k : ℝ) : ℂ) • pureDensity (h.eigenvectorBasis k) := by
  conv_lhs => rw [h.spectral_theorem, Unitary.conjStarAlgAut_apply]
  ext a b
  simp only [Matrix.mul_apply, diagonal, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    pureDensity, smul_eq_mul, Function.comp_apply, Matrix.star_apply, RCLike.star_def,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, zero_mul,
    Finset.sum_ite_eq, Matrix.IsHermitian.eigenvectorUnitary_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [RCLike.ofReal_eq_complex_ofReal]
  ring

lemma cfc_trace {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma vn_eig {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian) :
    vnEntropy Y = (∑ i, negMulLog (hY.eigenvalues i)) / Real.log 2 := by
  unfold vnEntropy
  rw [cfc_trace hY]
  simp only [Complex.re_sum, Complex.ofReal_re, negMulLog, Real.logb, Finset.sum_div,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- zero entropy density matrix is a pure projector. -/
lemma pure_of_vn {I : Type*} [Fintype I] [DecidableEq I] {ρ : Matrix I I ℂ} (hρ : ρ.PosSemidef)
    (h1 : ρ.trace = 1) (h0 : vnEntropy ρ = 0) :
    ∃ w : EuclideanSpace ℂ I, ‖w‖ = 1 ∧ ρ = pureDensity w := by
  set h := hρ.1
  set lam := h.eigenvalues
  set v := h.eigenvectorBasis
  have hv : ∀ k, ‖v k‖ = 1 := fun k => v.orthonormal.1 k
  have hl0 : ∀ k, 0 ≤ lam k := hρ.eigenvalues_nonneg
  have hsum : ∑ k, lam k = 1 := by
    have := h.trace_eq_sum_eigenvalues
    rw [h1] at this
    have h3 : ((∑ k, lam k : ℝ) : ℂ) = 1 := by push_cast; exact this.symm
    exact_mod_cast h3
  have hle1 : ∀ k, lam k ≤ 1 := fun k => by
    rw [← hsum]; exact Finset.single_le_sum (fun j _ => hl0 j) (Finset.mem_univ k)
  have hS : ∑ k, negMulLog (lam k) = 0 := by
    rw [vn_eig h] at h0
    rcases div_eq_zero_iff.1 h0 with h0 | h0
    · exact h0
    · exfalso; exact (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne' h0
  have h01 : ∀ k, lam k = 0 ∨ lam k = 1 := by
    intro k
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Real.negMulLog_nonneg (hl0 j) (hle1 j))).1
      hS k (Finset.mem_univ k)
    rcases (hl0 k).eq_or_lt with h | h
    · exact Or.inl h.symm
    rcases (hle1 k).eq_or_lt with h' | h'
    · exact Or.inr h'
    exfalso
    have : lam k * Real.log (lam k) < 0 := mul_neg_of_pos_of_neg h (Real.log_neg h h')
    rw [Real.negMulLog] at *; linarith
  obtain ⟨i0, hi0⟩ : ∃ i0, lam i0 = 1 := by
    by_contra hc
    push Not at hc
    have : ∑ k, lam k = 0 := Finset.sum_eq_zero fun k _ => (h01 k).resolve_right (hc k)
    linarith
  have hother : ∀ k, k ≠ i0 → lam k = 0 := by
    have hs := Finset.add_sum_erase Finset.univ lam (Finset.mem_univ i0)
    rw [hsum, hi0] at hs
    have h0 : ∑ k ∈ Finset.univ.erase i0, lam k = 0 := by linarith
    intro k hk
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hl0 k)).1 h0 k
      (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩)
  refine ⟨v i0, hv i0, ?_⟩
  rw [spec_sum h]
  rw [Finset.sum_eq_single i0 (fun k _ hk => by simp [lam, hother k hk]) (by simp)]
  simp [lam, hi0]
  rfl

lemma unit_sum {I : Type*} [Fintype I] (v : EuclideanSpace ℂ I) (hv : ‖v‖ = 1) :
    ∑ i, v i * conj (v i) = 1 := by
  have h1 : ∑ i, ‖v i‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, hv, one_pow]
  have : ∑ i, v i * conj (v i) = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  rw [this, h1]; simp

end X4ZE

-- ===== PCA =====

noncomputable section

namespace X4PC
open Matrix QAlgorithms Real
open QAlgorithms.Papers.Independent.Support50.P42
open scoped Matrix ComplexConjugate ComplexOrder

lemma cs {ι : Type*} [Fintype ι] (f g : ι → ℂ) :
    ‖∑ i, f i * g i‖ ^ 2 ≤ (∑ i, ‖f i‖ ^ 2) * (∑ i, ‖g i‖ ^ 2) := by
  have h1 : ‖∑ i, f i * g i‖ ≤ ∑ i, ‖f i‖ * ‖g i‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => norm_mul _ _))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖f i‖) (fun i => ‖g i‖)
  calc ‖∑ i, f i * g i‖ ^ 2 ≤ (∑ i, ‖f i‖ * ‖g i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

lemma cp_apply (x y : Fin 2 × Fin 2) :
    classicalPair x y = if x = y ∧ x.1 = x.2 then (1 / 2 : ℂ) else 0 := by
  fin_cases x <;> fin_cases y <;> simp [classicalPair, pureDensity, ket, EuclideanSpace.single_apply]

lemma nsq (z : ℂ) : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma tl_psd {α β : Type*} [Fintype α] [Fintype β] (v : EuclideanSpace ℂ (α × β)) (hv : ‖v‖ = 1) :
    (traceLeft (pureDensity v)).PosSemidef ∧ (traceLeft (pureDensity v)).trace = 1 := by
  set W : Matrix β α ℂ := Matrix.of fun b a => v (a, b)
  have hW : traceLeft (pureDensity v) = W * Wᴴ := by
    ext b b'
    simp [traceLeft, pureDensity, W, Matrix.mul_apply, conjTranspose_apply]
  refine ⟨hW ▸ posSemidef_self_mul_conjTranspose W, ?_⟩
  rw [← X4ZE.unit_sum v hv, Fintype.sum_prod_type, Finset.sum_comm]
  simp [Matrix.trace, traceLeft, pureDensity]

variable {c d : ℕ} (v : EuclideanSpace ℂ ((Fin 2 × Fin c) × (Fin 2 × Fin d)))

/-- Bob's purified marginal has all Rayleigh quotients at most one half. -/
lemma quad_bound (h : ∀ x y : Fin 2 × Fin 2, classicalPair x y =
      ∑ u : Fin c, ∑ w : Fin d, pureDensity v ((x.1, u), (x.2, w)) ((y.1, u), (y.2, w)))
    (φ : Fin 2 × Fin d → ℂ) :
    (star φ ⬝ᵥ (traceLeft (pureDensity v)) *ᵥ φ).re ≤ 1 / 2 * ∑ b, ‖φ b‖ ^ 2 := by
  -- vanishing off-diagonal blocks
  have hsum : ∀ x1 x2 : Fin 2, ∑ u : Fin c, ∑ w : Fin d, ‖v ((x1, u), (x2, w))‖ ^ 2 =
      if x1 = x2 then 1 / 2 else 0 := by
    intro x1 x2
    have := h (x1, x2) (x1, x2)
    rw [cp_apply] at this
    simp only [pureDensity, Matrix.of_apply, nsq] at this
    have e : ((∑ u : Fin c, ∑ w : Fin d, ‖v ((x1, u), (x2, w))‖ ^ 2 : ℝ) : ℂ) =
        ((if x1 = x2 then 1 / 2 else 0 : ℝ) : ℂ) := by
      simp only [true_and] at this
      push_cast at this ⊢; rw [← this]; split_ifs <;> simp
    exact_mod_cast e
  have hz : ∀ x1 x2 u w, x1 ≠ x2 → v ((x1, u), (x2, w)) = 0 := by
    intro x1 x2 u w hne
    have h0 := hsum x1 x2
    rw [if_neg hne] at h0
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun u _ => Finset.sum_nonneg fun w _ =>
      sq_nonneg ‖v ((x1, u), (x2, w))‖)).1 h0 u (Finset.mem_univ u)
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => sq_nonneg ‖v ((x1, u), (x2, w))‖)).1 this w
      (Finset.mem_univ w)
    simpa using this
  -- quadratic form as a sum of squares
  set s : (Fin 2 × Fin c) → ℂ := fun a => ∑ b, conj (φ b) * v (a, b)
  have hq : star φ ⬝ᵥ (traceLeft (pureDensity v)) *ᵥ φ = ∑ a, s a * conj (s a) := by
    simp only [dotProduct, mulVec, traceLeft, pureDensity, Matrix.of_apply, Pi.star_apply,
      RCLike.star_def, s, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
    conv_lhs => arg 2; ext b'; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hs : ∀ x1 u, s (x1, u) = ∑ w, conj (φ (x1, w)) * v ((x1, u), (x1, w)) := by
    intro x1 u
    simp only [s, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single x1]
    · intro x2 _ hne
      exact Finset.sum_eq_zero fun w _ => by rw [hz x1 x2 u w (Ne.symm hne), mul_zero]
    · simp
  have hre : (∑ a, s a * conj (s a)).re = ∑ a, ‖s a‖ ^ 2 := by
    simp only [nsq, Complex.re_sum, Complex.ofReal_re]
  rw [hq, hre, Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_le_sum fun x1 _ => ?_
  calc ∑ u, ‖s (x1, u)‖ ^ 2
      ≤ ∑ u, (∑ w, ‖conj (φ (x1, w))‖ ^ 2) * (∑ w, ‖v ((x1, u), (x1, w))‖ ^ 2) :=
        Finset.sum_le_sum fun u _ => by rw [hs]; exact cs _ _
    _ = (∑ w, ‖φ (x1, w)‖ ^ 2) * (∑ u, ∑ w, ‖v ((x1, u), (x1, w))‖ ^ 2) := by
        rw [Finset.mul_sum]; simp
    _ = 1 / 2 * ∑ w, ‖φ (x1, w)‖ ^ 2 := by rw [hsum, if_pos rfl]; ring

lemma ent_ge {ι : Type*} [Fintype ι] [DecidableEq ι] {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) (hle : ∀ k, hρ.1.eigenvalues k ≤ 1 / 2) : 1 ≤ vnEntropy ρ := by
  rw [X4ZE.vn_eig hρ.1]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hl2, one_mul]
  have hsum : ∑ k, hρ.1.eigenvalues k = 1 := by
    have := hρ.1.trace_eq_sum_eigenvalues
    rw [htr] at this
    have h3 : ((∑ k, hρ.1.eigenvalues k : ℝ) : ℂ) = 1 := by push_cast; exact this.symm
    exact_mod_cast h3
  calc Real.log 2 = ∑ k, hρ.1.eigenvalues k * Real.log 2 := by rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun k _ => by
      set l := hρ.1.eigenvalues k
      have h0 : 0 ≤ l := hρ.eigenvalues_nonneg k
      rcases h0.eq_or_lt with e | e
      · rw [← e]; simp
      · have : Real.log l ≤ -Real.log 2 := by
          rw [← Real.log_inv]; exact Real.log_le_log e (by linarith [hle k])
        rw [Real.negMulLog]; nlinarith

lemma score_ge (e : ℝ) (he : e ∈ purificationScores classicalPair) : 1 ≤ e := by
  obtain ⟨c, d, _, _, v, hv, h, rfl⟩ := he
  obtain ⟨hpsd, htr⟩ := tl_psd v hv
  refine ent_ge hpsd htr fun k => ?_
  rw [hpsd.1.eigenvalues_eq]
  have hb := quad_bound v h (hpsd.1.eigenvectorBasis k)
  have hn : ∑ b, ‖(hpsd.1.eigenvectorBasis k) b‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, (hpsd.1.eigenvectorBasis).orthonormal.1 k, one_pow]
  rw [hn, mul_one] at hb
  exact hb

end X4PC

-- ===== PCB =====

noncomputable section

namespace X4PC
open Matrix QAlgorithms Real
open QAlgorithms.Papers.Independent.Support50.P42
open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)
open scoped Matrix ComplexConjugate ComplexOrder Kronecker

lemma kronL {a b h : ℕ} (E : Matrix (Fin h) (Fin a) ℂ) (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (xa ya : Fin h) (xb yb : Fin b) :
    ((Matrix.kronecker E (1 : Matrix (Fin b) (Fin b) ℂ) * X : Matrix (Fin h × Fin b) (Fin a × Fin b) ℂ) *
      (Matrix.kronecker E (1 : Matrix (Fin b) (Fin b) ℂ))ᴴ) (xa, xb) (ya, yb) =
      ∑ pa, ∑ qa, E xa pa * X (pa, xb) (qa, yb) * conj (E ya qa) := by
  simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.kronecker, kroneckerMap_apply,
    Fintype.sum_prod_type, one_apply, RCLike.star_def, mul_ite, ite_mul, mul_one, mul_zero,
    zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_one, map_zero,
    apply_ite (starRingEnd ℂ), Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

lemma kronR {a b h : ℕ} (E : Matrix (Fin h) (Fin b) ℂ) (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (xa ya : Fin a) (xb yb : Fin h) :
    ((Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) E * X : Matrix (Fin a × Fin h) (Fin a × Fin b) ℂ) *
      (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) E)ᴴ) (xa, xb) (ya, yb) =
      ∑ pb, ∑ qb, E xb pb * X (xa, pb) (ya, qb) * conj (E yb qb) := by
  simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.kronecker, kroneckerMap_apply,
    Fintype.sum_prod_type, one_apply, RCLike.star_def, mul_ite, ite_mul, mul_one, mul_zero,
    zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_one, map_zero, one_mul,
    apply_ite (starRingEnd ℂ), Finset.sum_mul, Finset.mul_sum, Finset.sum_ite_irrel,
    Finset.sum_const_zero]
  exact Finset.sum_comm

def r : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

lemma r_conj : conj r = r := by simp [r]

lemma r_sq : r * r = 1 / 2 := by
  unfold r
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]; push_cast; ring

lemma r_nsq : ‖r‖ ^ 2 = 1 / 2 := by
  have : ((‖r‖ ^ 2 : ℝ) : ℂ) = 1 / 2 := by rw [← nsq, r_conj, r_sq]
  exact Complex.ofReal_injective (by rw [this]; push_cast; ring)

def wv : EuclideanSpace ℂ ((Fin 2 × Fin 2) × (Fin 2 × Fin 1)) :=
  WithLp.toLp 2 fun p => if p.1.1 = p.2.1 ∧ p.1.2 = p.1.1 then r else 0

lemma wv_norm : ‖wv‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [wv, PiLp.toLp_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.isValue]
  simp [r_nsq]
  norm_num

lemma wv_pur (x y : Fin 2 × Fin 2) : classicalPair x y =
    ∑ u : Fin 2, ∑ w : Fin 1, pureDensity wv ((x.1, u), (x.2, w)) ((y.1, u), (y.2, w)) := by
  rw [cp_apply]
  fin_cases x <;> fin_cases y <;>
    simp [pureDensity, wv, Fin.sum_univ_two, r_conj, r_sq]

lemma ket_density (j : Fin 2) : IsDensityMatrix (pureDensity (ket j)) := by
  refine ⟨?_, ?_⟩
  · have : pureDensity (ket j) = vecMulVec ((ket j : EuclideanSpace ℂ (Fin 2)) : Fin 2 → ℂ)
        (star ((ket j : EuclideanSpace ℂ (Fin 2)) : Fin 2 → ℂ)) := by
      ext a b; simp [pureDensity, vecMulVec]
    rw [this]; exact posSemidef_vecMulVec_self_star _
  · fin_cases j <;> simp [Matrix.trace, pureDensity, ket, Fin.sum_univ_two, EuclideanSpace.single_apply]

lemma sep : Entanglement.IsSeparablePositive classicalPair := by
  refine ⟨2, fun _ => 1 / 2, fun j => pureDensity (ket j), fun j => pureDensity (ket j),
    fun _ => by norm_num, fun j => ⟨ket_density j, ket_density j⟩, ?_⟩
  ext x y
  rw [cp_apply, Matrix.sum_apply]
  fin_cases x <;> fin_cases y <;>
    simp [Matrix.kronecker, kroneckerMap_apply, pureDensity, ket, EuclideanSpace.single_apply,
      Fin.sum_univ_two]

def EA (i : Fin 2) : Matrix (Fin 2) (Fin 1) ℂ := fun x _ => if x = i then r else 0

def FB (i : Fin 2) (_ : Fin 1) : Matrix (Fin 2) (Fin 1) ℂ := fun x _ => if x = i then 1 else 0

lemma EA_kraus : IsKrausFamily EA := by
  unfold IsKrausFamily
  ext a b
  fin_cases a; fin_cases b
  simp [EA, Matrix.mul_apply, Fin.sum_univ_two, r_conj, r_sq]
  norm_num

lemma FB_kraus (i : Fin 2) : IsKrausFamily (FB i) := by
  unfold IsKrausFamily
  ext a b
  fin_cases a; fin_cases b
  fin_cases i <;> simp [FB, Matrix.mul_apply, Fin.sum_univ_two]

lemma prep : ∃ L : Superop (Fin 1 × Fin 1) (Fin 2 × Fin 2),
    FiniteLOCC L ∧ L (1 : Op (Fin 1 × Fin 1)) = classicalPair := by
  refine ⟨_, FiniteLOCC.alice EA EA_kraus _
    (fun i => FiniteLOCC.bob (FB i) (FB_kraus i) _ (fun _ => FiniteLOCC.identity _ _)), ?_⟩
  ext ⟨xa, xb⟩ ⟨ya, yb⟩
  simp only [Matrix.sum_apply]
  simp only [kronR, kronL]
  rw [cp_apply]
  fin_cases xa <;> fin_cases xb <;> fin_cases ya <;> fin_cases yb <;>
    simp [EA, FB, Fin.sum_univ_two, r_conj, r_sq]

end X4PC

-- ===== PCSol =====

noncomputable section

section
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P42
open QAlgorithms.Papers.Independent.Information100.P21 (Op Vec FiniteLOCC)
open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution :
    (purificationScores classicalPair).Nonempty ∧ BddBelow (purificationScores classicalPair) ∧
    0<purificationMinimum classicalPair ∧ Entanglement.IsSeparablePositive classicalPair ∧
    ∃ L : Superop (Fin 1 × Fin 1) (Fin 2 × Fin 2),
      FiniteLOCC L ∧ L (1 : Op (Fin 1 × Fin 1))=classicalPair := by
  have hne : (purificationScores classicalPair).Nonempty :=
    ⟨_, 2, 1, by norm_num, by norm_num, X4PC.wv, X4PC.wv_norm, X4PC.wv_pur, rfl⟩
  refine ⟨hne, ⟨1, fun e he => X4PC.score_ge e he⟩, ?_, X4PC.sep, X4PC.prep⟩
  have : 1 ≤ purificationMinimum classicalPair := le_csInf hne X4PC.score_ge
  linarith

end
end
