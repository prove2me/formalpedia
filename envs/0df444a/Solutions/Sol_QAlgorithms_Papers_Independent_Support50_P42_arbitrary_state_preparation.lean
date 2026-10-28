-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P42.arbitrary_state_preparation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:35:28.150844+00:00
-- url     : https://prove2.me/submissions/1c61873c-1ee8-434c-a010-3f59f8df135b

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

-- ===== ASA =====

noncomputable section

namespace X4AS
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Support50.P42
open QAlgorithms.Papers.Independent.Dependency50.P42 (copyIndex singletState singletVector singlets
  dimensionedPower)
open scoped Matrix ComplexConjugate

/-- qubit labels of a basis index. -/
def lab (q : ℕ) : Fin (2 ^ q) ≃ (Fin q → Fin 2) := (copyIndex 2 q).symm

variable {q : ℕ}

lemma sum_prod_lab (f : Fin q → Fin 2 → ℂ) :
    ∑ x : Fin (2 ^ q), ∏ i, f i (lab q x i) = ∏ i, ∑ t, f i t := by
  rw [Equiv.sum_comp (lab q) (fun g => ∏ i, f i (g i)), Fintype.prod_sum]

lemma sum2_prod_lab (f : Fin q → Fin 2 → Fin 2 → ℂ) :
    ∑ m : Fin (2 ^ q), ∑ n : Fin (2 ^ q), ∏ i, f i (lab q m i) (lab q n i) =
      ∏ i, ∑ a, ∑ b, f i a b := by
  calc ∑ m : Fin (2 ^ q), ∑ n : Fin (2 ^ q), ∏ i, f i (lab q m i) (lab q n i)
      = ∑ m : Fin (2 ^ q), ∏ i, ∑ b, f i (lab q m i) b :=
        Finset.sum_congr rfl fun m _ => sum_prod_lab (fun i t => f i (lab q m i) t)
    _ = _ := sum_prod_lab (fun i a => ∑ b, f i a b)

lemma prod_delta (x y : Fin (2 ^ q)) :
    ∏ i, (if lab q x i = lab q y i then (1:ℂ) else 0) = if x = y then 1 else 0 := by
  rw [Finset.prod_boole]
  congr 1
  apply propext
  constructor
  · intro h; exact (lab q).injective (funext fun i => h i (Finset.mem_univ i))
  · rintro rfl i _; rfl

def σ1 (t y : Fin 2) : ℂ := if t = 0 ∧ y = 1 then 1 else if t = 1 ∧ y = 0 then -1 else 0

lemma σ1_conj (t y : Fin 2) : conj (σ1 t y) = σ1 t y := by
  unfold σ1; split_ifs <;> simp

def S (q : ℕ) : Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℂ := fun x y => ∏ i, σ1 (lab q x i) (lab q y i)

lemma S_conj (x y : Fin (2 ^ q)) : conj (S q x y) = S q x y := by
  simp [S, map_prod, σ1_conj]

lemma S_unit : (S q)ᴴ * S q = 1 := by
  ext y y'
  simp only [Matrix.mul_apply, conjTranspose_apply, RCLike.star_def, S_conj]
  simp only [S, ← Finset.prod_mul_distrib]
  rw [sum_prod_lab (fun i t => σ1 t (lab q y i) * σ1 t (lab q y' i)), Matrix.one_apply, ← prod_delta]
  refine Finset.prod_congr rfl fun i _ => ?_
  generalize lab q y i = a; generalize lab q y' i = b
  fin_cases a <;> fin_cases b <;> simp [σ1, Fin.sum_univ_two]

lemma S_unit' : S q * (S q)ᴴ = 1 := by
  ext x x'
  simp only [Matrix.mul_apply, conjTranspose_apply, RCLike.star_def, S_conj]
  simp only [S, ← Finset.prod_mul_distrib]
  rw [sum_prod_lab (fun i t => σ1 (lab q x i) t * σ1 (lab q x' i) t), Matrix.one_apply, ← prod_delta]
  refine Finset.prod_congr rfl fun i _ => ?_
  generalize lab q x i = a; generalize lab q x' i = b
  fin_cases a <;> fin_cases b <;> simp [σ1, Fin.sum_univ_two]

lemma singlet_entry (t y t' y' : Fin 2) :
    singletState (t, y) (t', y') = (1 / 2 : ℂ) * σ1 t y * σ1 t' y' := by
  have h : ((Real.sqrt 2 / 2 : ℝ) : ℂ) * ((Real.sqrt 2 / 2 : ℝ) : ℂ) = 1 / 2 := by
    rw [← Complex.ofReal_mul]
    have : Real.sqrt 2 / 2 * (Real.sqrt 2 / 2) = 1 / 2 := by
      rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num)]; norm_num
    rw [this]; push_cast; ring
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  fin_cases t <;> fin_cases y <;> fin_cases t' <;> fin_cases y' <;>
    simp [singletState, pureDensity, singletVector, σ1, Complex.conj_ofReal] <;>
    (rw [show (starRingEnd ℂ) 2 = 2 from map_ofNat _ 2]; linear_combination (1 / 4 : ℂ) * hs)

lemma singlets_eq (x0 y0 x1 y1 : Fin (2 ^ q)) :
    singlets q (x0, y0) (x1, y1) = ((2 : ℂ) ^ q)⁻¹ * (S q x0 y0 * S q x1 y1) := by
  simp only [singlets, dimensionedPower, QAlgorithms.Papers.Independent.Information100.P80.groupedPower]
  simp only [singlet_entry]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, S, S]
  simp only [lab]
  rw [one_div, inv_pow]; ring

/-- single-qubit Pauli X^m Z^n. -/
def u1 (m n x k : Fin 2) : ℂ := if x = k + m then (if n = 1 ∧ k = 1 then -1 else 1) else 0

lemma u1_conj (m n x k : Fin 2) : conj (u1 m n x k) = u1 m n x k := by
  unfold u1; split_ifs <;> simp

def U (m n : Fin (2 ^ q)) : Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℂ :=
  fun x k => ∏ i, u1 (lab q m i) (lab q n i) (lab q x i) (lab q k i)

lemma U_conj (m n x k : Fin (2 ^ q)) : conj (U m n x k) = U m n x k := by
  simp [U, map_prod, u1_conj]

lemma U_unit (m n : Fin (2 ^ q)) : (U m n)ᴴ * U m n = 1 := by
  ext k k'
  simp only [Matrix.mul_apply, conjTranspose_apply, RCLike.star_def, U_conj]
  simp only [U, ← Finset.prod_mul_distrib]
  rw [sum_prod_lab (fun i t => u1 (lab q m i) (lab q n i) t (lab q k i) *
    u1 (lab q m i) (lab q n i) t (lab q k' i)), Matrix.one_apply, ← prod_delta]
  refine Finset.prod_congr rfl fun i _ => ?_
  generalize lab q m i = a; generalize lab q n i = b
  generalize lab q k i = c; generalize lab q k' i = d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp [u1, Fin.sum_univ_two]

lemma U_unit' (m n : Fin (2 ^ q)) : U m n * (U m n)ᴴ = 1 := by
  ext x x'
  simp only [Matrix.mul_apply, conjTranspose_apply, RCLike.star_def, U_conj]
  simp only [U, ← Finset.prod_mul_distrib]
  rw [sum_prod_lab (fun i t => u1 (lab q m i) (lab q n i) (lab q x i) t *
    u1 (lab q m i) (lab q n i) (lab q x' i) t), Matrix.one_apply, ← prod_delta]
  refine Finset.prod_congr rfl fun i _ => ?_
  generalize lab q m i = a; generalize lab q n i = b
  generalize lab q x i = c; generalize lab q x' i = d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp [u1, Fin.sum_univ_two]

lemma twirl (X : Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℂ) :
    ∑ m, ∑ n, (U m n)ᴴ * X * U m n = ((2 : ℂ) ^ q * X.trace) • (1 : Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℂ) := by
  ext k l
  simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, RCLike.star_def, U_conj,
    Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
  have e : ∀ x y : Fin (2 ^ q), ∑ m : Fin (2 ^ q), ∑ n : Fin (2 ^ q), U m n x k * U m n y l =
      (2 : ℂ) ^ q * ((if x = y then 1 else 0) * (if k = l then 1 else 0)) := by
    intro x y
    simp only [U, ← Finset.prod_mul_distrib]
    rw [sum2_prod_lab (fun i a b => u1 a b (lab q x i) (lab q k i) * u1 a b (lab q y i) (lab q l i)),
      ← prod_delta x y, ← prod_delta k l, ← Finset.prod_mul_distrib]
    rw [show (2 : ℂ) ^ q = ∏ _i : Fin q, (2 : ℂ) by simp, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    generalize lab q x i = a; generalize lab q y i = b
    generalize lab q k i = c; generalize lab q l i = d
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp [u1, Fin.sum_univ_two] <;> norm_num
  calc ∑ m, ∑ n, ∑ y, ∑ x, U m n x k * X x y * U m n y l
      = ∑ m : Fin (2 ^ q), ∑ n : Fin (2 ^ q), ∑ x, ∑ y, U m n x k * X x y * U m n y l :=
        Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => Finset.sum_comm
    _ = ∑ m : Fin (2 ^ q), ∑ x, ∑ n : Fin (2 ^ q), ∑ y, U m n x k * X x y * U m n y l :=
        Finset.sum_congr rfl fun m _ => Finset.sum_comm
    _ = ∑ x, ∑ m : Fin (2 ^ q), ∑ n : Fin (2 ^ q), ∑ y, U m n x k * X x y * U m n y l := Finset.sum_comm
    _ = ∑ x, ∑ m : Fin (2 ^ q), ∑ y, ∑ n : Fin (2 ^ q), U m n x k * X x y * U m n y l :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun m _ => Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ m : Fin (2 ^ q), ∑ n : Fin (2 ^ q), U m n x k * X x y * U m n y l :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x, ∑ y, X x y * ((2 : ℂ) ^ q * ((if x = y then 1 else 0) * (if k = l then 1 else 0))) := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [← e, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        ring
    _ = _ := by
        simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
          if_true, Matrix.one_apply]
        split_ifs
        · simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.trace, Matrix.diag,
            Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => mul_comm _ _
        · simp

end X4AS

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

-- ===== ASB =====

noncomputable section

namespace X4AS
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Support50.P42
open scoped Matrix ComplexConjugate

variable {a b q : ℕ}

/-- embedding of Bob's target space into the singlet register. -/
def J (b q : ℕ) : Matrix (Fin b) (Fin (2 ^ q)) ℂ := fun x m => if x.val = m.val then 1 else 0

lemma J_mul (hbq : b ≤ 2 ^ q) : J b q * (J b q)ᴴ = 1 := by
  ext x y
  simp only [J, Matrix.mul_apply, conjTranspose_apply, RCLike.star_def, apply_ite (starRingEnd ℂ),
    map_one, map_zero, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Matrix.one_apply]
  rw [Finset.sum_eq_single ⟨x.val, lt_of_lt_of_le x.isLt hbq⟩]
  · by_cases h : x = y
    · subst h; simp
    · have : ¬ y.val = x.val := fun e => h (Fin.ext e.symm)
      simp [h, this]
  · intro m _ hm
    have : ¬ x.val = m.val := fun e => hm (Fin.ext e.symm)
    simp [this]
  · simp

/-- Bob's decoding Kraus family `Fin (2^q) → Fin b`. -/
def Q (b q : ℕ) (j : Fin (2 ^ q)) : Matrix (Fin b) (Fin (2 ^ q)) ℂ := fun x m =>
  if m.val < b then (if j.val = 0 ∧ x.val = m.val then 1 else 0) else
    (if m = j ∧ x.val = 0 then 1 else 0)

lemma Q_real (j : Fin (2 ^ q)) (x m) : conj (Q b q j x m) = Q b q j x m := by
  unfold Q; split_ifs <;> simp

lemma Q_complete (hb : 0 < b) : ∑ j, (Q b q j)ᴴ * Q b q j = 1 := by
  ext m m'
  simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, RCLike.star_def, Q_real,
    Matrix.one_apply]
  have h0 : (0 : ℕ) < 2 ^ q := by positivity
  by_cases hm : m.val < b <;> by_cases hm' : m'.val < b
  · rw [Finset.sum_eq_single ⟨0, h0⟩]
    · rw [Finset.sum_eq_single ⟨m.val, hm⟩]
      · by_cases e : m = m'
        · subst e; simp [Q, hm]
        · have : ¬ m.val = m'.val := fun h => e (Fin.ext h)
          simp [Q, hm, hm', e, this]
      · intro x _ hx
        have : ¬ x.val = m.val := fun h => hx (Fin.ext h)
        simp [Q, hm, this]
      · simp
    · intro j _ hj
      have : ¬ j.val = 0 := fun h => hj (Fin.ext h)
      simp [Q, hm, hm', this]
    · simp
  · have e : m ≠ m' := fun h => hm' (h ▸ hm)
    rw [if_neg e]
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun x _ => ?_
    simp only [Q, hm, hm', if_true, if_false]
    split_ifs with h1 h2 <;> try simp
    exact absurd (h2.1 ▸ h1.1) (by omega)
  · have e : m ≠ m' := fun h => hm (h ▸ hm')
    rw [if_neg e]
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun x _ => ?_
    simp only [Q, hm, hm', if_true, if_false]
    split_ifs with h1 h2 <;> try simp
    exact absurd (h1.1 ▸ h2.1) (by omega)
  · rw [Finset.sum_eq_single m]
    · rw [Finset.sum_eq_single ⟨0, hb⟩]
      · by_cases e : m = m'
        · subst e; simp [Q, hm]
        · simp [Q, hm, hm', e, Ne.symm e]
      · intro x _ hx
        have : ¬ x.val = 0 := fun h => hx (Fin.ext h)
        simp [Q, hm, this]
      · simp
    · intro j _ hj
      simp [Q, hm, Ne.symm hj]
    · simp

lemma JQ (hbq : b ≤ 2 ^ q) (j : Fin (2 ^ q)) (x y : Fin b) :
    ∑ m, J b q x m * Q b q j y m = if j.val = 0 ∧ x = y then 1 else 0 := by
  have hx : x.val < b := x.isLt
  rw [Finset.sum_eq_single ⟨x.val, lt_of_lt_of_le x.isLt hbq⟩]
  · rcases eq_or_ne x y with rfl | h
    · simp [J, Q, hx]
    · have : ¬ y.val = x.val := fun e => h (Fin.ext e.symm)
      simp [J, Q, hx, h, this]
  · intro m _ hm
    have : ¬ x.val = m.val := fun e => hm (Fin.ext e.symm)
    simp [J, this]
  · simp

end X4AS

-- ===== ASC =====

noncomputable section

namespace X4AS
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Support50.P42
open scoped Matrix ComplexConjugate ComplexOrder

variable {a b q : ℕ} {rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ}

/-- amplitudes of an eigen-decomposition `ρ = Σ_z ψ_z ψ_z†`. -/
def ψ (hρ : rho.PosSemidef) (z p : Fin a × Fin b) : ℂ :=
  (Real.sqrt (hρ.1.eigenvalues z) : ℂ) * hρ.1.eigenvectorBasis z p

lemma rho_dec (hρ : rho.PosSemidef) (x y : Fin a × Fin b) :
    rho x y = ∑ z, ψ hρ z x * conj (ψ hρ z y) := by
  conv_lhs => rw [X4ZE.spec_sum hρ.1]
  rw [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun z _ => ?_
  have h0 := hρ.eigenvalues_nonneg z
  have hs : ((Real.sqrt (hρ.1.eigenvalues z) : ℝ) : ℂ) * (Real.sqrt (hρ.1.eigenvalues z) : ℂ) =
      (hρ.1.eigenvalues z : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt h0]
  simp only [Matrix.smul_apply, pureDensity, Matrix.of_apply, smul_eq_mul, ψ, map_mul,
    Complex.conj_ofReal]
  rw [← hs]; ring

lemma psi_tr (hρ : rho.PosSemidef) (htr : rho.trace = 1) :
    ∑ z, ∑ p, ψ hρ z p * conj (ψ hρ z p) = 1 := by
  rw [← htr, Matrix.trace]
  calc ∑ z, ∑ p, ψ hρ z p * conj (ψ hρ z p) = ∑ p, ∑ z, ψ hρ z p * conj (ψ hρ z p) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun p _ => (rho_dec hρ p p).symm

def Ψ (hρ : rho.PosSemidef) (z : Fin a × Fin b) : Matrix (Fin a) (Fin b) ℂ :=
  Matrix.of fun x y => ψ hρ z (x, y)

def cD (q : ℕ) : ℂ := ((Real.sqrt (2 ^ q))⁻¹ : ℝ)

lemma cD_sq : cD q * cD q = ((2 : ℂ) ^ q)⁻¹ := by
  have : (Real.sqrt (2 ^ q))⁻¹ * (Real.sqrt (2 ^ q))⁻¹ = ((2 : ℝ) ^ q)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  unfold cD; rw [← Complex.ofReal_mul, this]; push_cast; ring

lemma cD_conj : conj (cD q) = cD q := by simp [cD]

/-- Alice's steering Kraus operator for Pauli outcome `(m,n)` and mixture label `z`. -/
def A (hρ : rho.PosSemidef) (m n : Fin (2 ^ q)) (z : Fin a × Fin b) : Matrix (Fin a) (Fin (2 ^ q)) ℂ :=
  cD q • (Ψ hρ z * J b q * U m n * (S q)ᴴ)

/-- Bob's correction-and-decoding Kraus operators. -/
def V (b : ℕ) (m n j : Fin (2 ^ q)) : Matrix (Fin b) (Fin (2 ^ q)) ℂ := Q b q j * U m n

lemma U_T (m n : Fin (2 ^ q)) : (U m n)ᴴ = (U m n)ᵀ := by
  ext x y; simp [conjTranspose_apply, U_conj]

lemma S_T : (S q)ᴴ = (S q)ᵀ := by
  ext x y; simp [conjTranspose_apply, S_conj]

lemma V_complete (m n : Fin (2 ^ q)) (hb : 0 < b) : ∑ j, (V b m n j)ᴴ * V b m n j = 1 := by
  simp only [V, conjTranspose_mul]
  have : ∑ j, (U m n)ᴴ * (Q b q j)ᴴ * (Q b q j * U m n) = (U m n)ᴴ * (∑ j, (Q b q j)ᴴ * Q b q j) * U m n := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by simp only [Matrix.mul_assoc]
  rw [this, Q_complete hb, Matrix.mul_one, U_unit]

lemma trJ (hbq : b ≤ 2 ^ q) (P : Matrix (Fin a) (Fin b) ℂ) :
    ((J b q)ᴴ * Pᴴ * P * J b q).trace = (P * Pᴴ).trace := by
  rw [show (J b q)ᴴ * Pᴴ * P * J b q = (J b q)ᴴ * (Pᴴ * P * J b q) by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm, Matrix.mul_assoc, J_mul hbq, Matrix.mul_one, Matrix.trace_mul_comm]

lemma A_complete (hρ : rho.PosSemidef) (htr : rho.trace = 1) (hbq : b ≤ 2 ^ q) :
    ∑ m : Fin (2 ^ q), ∑ n : Fin (2 ^ q), ∑ z, (A hρ m n z)ᴴ * A hρ m n z = 1 := by
  have e1 : ∀ m n z, (A hρ m n z)ᴴ * A hρ m n z = ((2 : ℂ) ^ q)⁻¹ •
      (S q * ((U m n)ᴴ * ((J b q)ᴴ * (Ψ hρ z)ᴴ * Ψ hρ z * J b q) * U m n) * (S q)ᴴ) := by
    intro m n z
    simp only [A, conjTranspose_smul, conjTranspose_mul, conjTranspose_conjTranspose,
      RCLike.star_def, cD_conj, Matrix.smul_mul, Matrix.mul_smul, smul_smul, cD_sq]
    congr 1
    simp only [Matrix.mul_assoc]
  simp_rw [e1]
  conv_lhs => arg 2; ext m; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  have e2 : ∀ z, ∑ m : Fin (2 ^ q), ∑ n : Fin (2 ^ q), ((2 : ℂ) ^ q)⁻¹ •
      (S q * ((U m n)ᴴ * ((J b q)ᴴ * (Ψ hρ z)ᴴ * Ψ hρ z * J b q) * U m n) * (S q)ᴴ) =
      ((Ψ hρ z) * (Ψ hρ z)ᴴ).trace • (1 : Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℂ) := by
    intro z
    simp_rw [← Finset.smul_sum]
    have : ∑ m : Fin (2 ^ q), ∑ n : Fin (2 ^ q),
        S q * ((U m n)ᴴ * ((J b q)ᴴ * (Ψ hρ z)ᴴ * Ψ hρ z * J b q) * U m n) * (S q)ᴴ =
        S q * (∑ m, ∑ n, (U m n)ᴴ * ((J b q)ᴴ * (Ψ hρ z)ᴴ * Ψ hρ z * J b q) * U m n) * (S q)ᴴ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [this, twirl, trJ hbq, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, S_unit', smul_smul,
      ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero), one_mul]
  simp_rw [e2]
  rw [← Finset.sum_smul]
  have : ∑ z, ((Ψ hρ z) * (Ψ hρ z)ᴴ).trace = 1 := by
    rw [← psi_tr hρ htr]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp [Matrix.trace, Matrix.mul_apply, Ψ, conjTranspose_apply, Fintype.sum_prod_type]
  rw [this, one_smul]

lemma phi (hρ : rho.PosSemidef) (hbq : b ≤ 2 ^ q) (m n : Fin (2 ^ q)) (z : Fin a × Fin b)
    (j : Fin (2 ^ q)) (x : Fin a) (y : Fin b) :
    ∑ pb, (∑ pa, A hρ m n z x pa * S q pa pb) * V b m n j y pb =
      (if j.val = 0 then cD q else 0) * ψ hρ z (x, y) := by
  have e : ∑ pb, (∑ pa, A hρ m n z x pa * S q pa pb) * V b m n j y pb =
      (A hρ m n z * S q * (V b m n j)ᵀ) x y := by
    simp [Matrix.mul_apply, transpose_apply]
  rw [e]
  have e2 : A hρ m n z * S q * (V b m n j)ᵀ = cD q • (Ψ hρ z * (J b q * (Q b q j)ᵀ)) := by
    simp only [A, V, Matrix.smul_mul, transpose_mul]
    congr 1
    rw [← U_T, S_T]
    have hS : (S q)ᵀ * S q = 1 := by rw [← S_T]; exact S_unit
    calc Ψ hρ z * J b q * U m n * (S q)ᵀ * S q * ((U m n)ᴴ * (Q b q j)ᵀ)
        = Ψ hρ z * J b q * (U m n * ((S q)ᵀ * S q) * (U m n)ᴴ) * (Q b q j)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hS, Matrix.mul_one, U_unit', Matrix.mul_one, Matrix.mul_assoc]
  rw [e2, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  simp only [Matrix.mul_apply, transpose_apply, JQ hbq]
  by_cases hj : j.val = 0
  · simp [hj, Ψ, Finset.sum_ite_eq']
  · simp [hj]

end X4AS

-- ===== ASD =====

noncomputable section

namespace X4AS
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Support50.P42
open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)
open QAlgorithms.Papers.Independent.Dependency50.P42 (singlets)
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

lemma factor {α β : Type} [Fintype α] [Fintype β] (A1 A2 : α → ℂ) (V1 V2 : β → ℂ) (S : α → β → ℂ)
    (hS : ∀ x y, conj (S x y) = S x y) (c : ℂ) :
    ∑ pb, ∑ qb, V1 pb * (∑ pa, ∑ qa, A1 pa * (c * (S pa pb * S qa qb)) * conj (A2 qa)) * conj (V2 qb) =
      c * ((∑ pb, (∑ pa, A1 pa * S pa pb) * V1 pb) * conj (∑ qb, (∑ qa, A2 qa * S qa qb) * V2 qb)) := by
  simp only [map_sum, map_mul, hS, Finset.mul_sum, Finset.sum_mul]
  calc ∑ pb, ∑ qb, ∑ pa, ∑ qa, V1 pb * (A1 pa * (c * (S pa pb * S qa qb)) * conj (A2 qa)) * conj (V2 qb)
      = ∑ qb, ∑ pb, ∑ pa, ∑ qa, V1 pb * (A1 pa * (c * (S pa pb * S qa qb)) * conj (A2 qa)) * conj (V2 qb) :=
        Finset.sum_comm
    _ = ∑ qb, ∑ pb, ∑ qa, ∑ pa, V1 pb * (A1 pa * (c * (S pa pb * S qa qb)) * conj (A2 qa)) * conj (V2 qb) :=
        Finset.sum_congr rfl fun qb _ => Finset.sum_congr rfl fun pb _ => Finset.sum_comm
    _ = ∑ qb, ∑ qa, ∑ pb, ∑ pa, V1 pb * (A1 pa * (c * (S pa pb * S qa qb)) * conj (A2 qa)) * conj (V2 qb) :=
        Finset.sum_congr rfl fun qb _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun qb _ => Finset.sum_congr rfl fun qa _ =>
          Finset.sum_congr rfl fun pb _ => Finset.sum_congr rfl fun pa _ => ?_
        ring

lemma reorder {r d n : ℕ} (G : Fin r → Fin n → Fin n → ℂ) (w1 w2 : Fin d → Fin n → ℂ) :
    ∑ z, ∑ j, ∑ pb, ∑ qb, (w1 j pb * G z pb qb) * conj (w2 j qb) =
      ∑ j, ∑ qb, (∑ pb, w1 j pb * ∑ z, G z pb qb) * conj (w2 j qb) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul]
  calc ∑ z, ∑ pb, ∑ qb, w1 j pb * G z pb qb * conj (w2 j qb)
      = ∑ z, ∑ qb, ∑ pb, w1 j pb * G z pb qb * conj (w2 j qb) :=
        Finset.sum_congr rfl fun z _ => Finset.sum_comm
    _ = ∑ qb, ∑ z, ∑ pb, w1 j pb * G z pb qb * conj (w2 j qb) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun qb _ => Finset.sum_comm

/-- a superoperator in LOCC-tree form equals its one-way-bits form. -/
lemma tree_eq {a1 b1 a2 b2 k r d : ℕ} (E : Fin k → Fin r → Matrix (Fin a2) (Fin a1) ℂ)
    (W : Fin k → Fin d → Matrix (Fin b2) (Fin b1) ℂ) (X : Matrix (Fin a1 × Fin b1) (Fin a1 × Fin b1) ℂ) :
    (∑ t : Fin (k * r), ∑ j, ((Matrix.kronecker (1 : Matrix (Fin a2) (Fin a2) ℂ)
      (W (finProdFinEquiv.symm t).1 j) *
      ((Matrix.kronecker (E (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2)
        (1 : Matrix (Fin b1) (Fin b1) ℂ) * X : Matrix (Fin a2 × Fin b1) (Fin a1 × Fin b1) ℂ) *
        (Matrix.kronecker (E (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2)
          (1 : Matrix (Fin b1) (Fin b1) ℂ))ᴴ) : Matrix (Fin a2 × Fin b2) (Fin a2 × Fin b1) ℂ) *
      (Matrix.kronecker (1 : Matrix (Fin a2) (Fin a2) ℂ) (W (finProdFinEquiv.symm t).1 j))ᴴ)) =
    ∑ i, idTensorSuperop (krausApply (W i))
      (∑ z, conjSuperop (Matrix.kronecker (E i z) (1 : Matrix (Fin b1) (Fin b1) ℂ)) X) := by
  ext ⟨xa, xb⟩ ⟨ya, yb⟩
  simp only [Matrix.sum_apply, kronR, kronL]
  rw [← Equiv.sum_comp finProdFinEquiv (fun t => ∑ j, ∑ pb, ∑ qb,
    W (finProdFinEquiv.symm t).1 j xb pb *
      (∑ pa, ∑ qa, E (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2 xa pa * X (pa, pb) (qa, qb) *
        conj (E (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2 ya qa)) * conj (W (finProdFinEquiv.symm t).1 j yb qb))]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [idTensorSuperop, krausApply, conjSuperop, Matrix.of_apply, Matrix.sum_apply]
  simp only [kronL]
  simp only [Matrix.mul_apply, conjTranspose_apply, RCLike.star_def, Matrix.of_apply]
  exact reorder (fun z pb qb => ∑ pa, ∑ qa, E i z xa pa * X (pa, pb) (qa, qb) * conj (E i z ya qa))
    (fun j pb => W i j xb pb) (fun j qb => W i j yb qb)

end X4AS

-- ===== ASE =====

noncomputable section

namespace X4AS
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Support50.P42
open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)
open QAlgorithms.Papers.Independent.Dependency50.P42 (singlets)
open scoped Matrix ComplexConjugate ComplexOrder Kronecker

variable {a b q : ℕ} {rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ}

def AK (hρ : rho.PosSemidef) (i : Fin (2 ^ q * 2 ^ q)) (z : Fin (a * b)) : Matrix (Fin a) (Fin (2 ^ q)) ℂ :=
  A hρ (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm z)

def VK (b : ℕ) (i : Fin (2 ^ q * 2 ^ q)) (j : Fin (2 ^ q)) : Matrix (Fin b) (Fin (2 ^ q)) ℂ :=
  V b (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 j

lemma sum_fp {M : Type*} [AddCommMonoid M] {k r : ℕ} (F : Fin k → Fin r → M) :
    ∑ t : Fin (k * r), F (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2 = ∑ i, ∑ z, F i z := by
  rw [← Equiv.sum_comp finProdFinEquiv (fun t => F (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2)]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]

lemma sum_fp1 {M : Type*} [AddCommMonoid M] {k r : ℕ} (F : Fin k × Fin r → M) :
    ∑ t : Fin (k * r), F (finProdFinEquiv.symm t) = ∑ p, F p :=
  by rw [← Equiv.sum_comp finProdFinEquiv]; simp

lemma AK_complete (hρ : rho.PosSemidef) (htr : rho.trace = 1) (hbq : b ≤ 2 ^ q) :
    ∑ i : Fin (2 ^ q * 2 ^ q), ∑ z, (AK hρ i z)ᴴ * AK hρ i z = 1 := by
  simp only [AK]
  rw [sum_fp1 (fun p => ∑ z : Fin (a * b), (A hρ p.1 p.2 (finProdFinEquiv.symm z))ᴴ *
    A hρ p.1 p.2 (finProdFinEquiv.symm z)), Fintype.sum_prod_type, ← A_complete hρ htr hbq]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  exact sum_fp1 (fun z => (A hρ m n z)ᴴ * A hρ m n z)

lemma EK_complete (hρ : rho.PosSemidef) (htr : rho.trace = 1) (hbq : b ≤ 2 ^ q) :
    IsKrausFamily (fun t : Fin (2 ^ q * 2 ^ q * (a * b)) =>
      AK hρ (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2) := by
  unfold IsKrausFamily
  rw [sum_fp (fun i z => (AK hρ i z)ᴴ * AK hρ i z)]
  exact AK_complete hρ htr hbq

lemma VK_complete (hb : 0 < b) (i : Fin (2 ^ q * 2 ^ q)) : IsKrausFamily (VK (q := q) b i) := by
  unfold IsKrausFamily VK
  exact V_complete _ _ hb

theorem prep_q (hb : 0 < b) (hbq : b ≤ 2 ^ q) (hrho : IsDensityMatrix rho) :
    ∃ L : Superop (Fin (2 ^ q) × Fin (2 ^ q)) (Fin a × Fin b),
      FiniteLOCC L ∧ OneWayBits (2 * q) L ∧ L (singlets q) = rho := by
  obtain ⟨hρ, htr⟩ := hrho
  refine ⟨_, FiniteLOCC.alice _ (EK_complete hρ htr hbq) _
    (fun t => FiniteLOCC.bob (VK b (finProdFinEquiv.symm t).1) (VK_complete hb _) _
      (fun _ => FiniteLOCC.identity _ _)), ?_, ?_⟩
  · refine ⟨2 ^ q * 2 ^ q, a * b, by rw [two_mul, pow_add], AK hρ, AK_complete hρ htr hbq,
      fun i => krausApply (VK b i), fun i => ⟨_, VK b i, VK_complete hb i, fun _ => rfl⟩, fun X => ?_⟩
    exact tree_eq (AK hρ) (VK b) X
  · ext ⟨xa, xb⟩ ⟨ya, yb⟩
    simp only [Matrix.sum_apply]
    simp only [kronR, kronL]
    simp_rw [singlets_eq]
    have h1 : ∀ (t : Fin (2 ^ q * 2 ^ q * (a * b))) (j : Fin (2 ^ q)),
        ∑ pb, ∑ qb, VK b (finProdFinEquiv.symm t).1 j xb pb *
          (∑ pa, ∑ qa, AK hρ (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2 xa pa *
            (((2 : ℂ) ^ q)⁻¹ * (S q pa pb * S q qa qb)) *
            conj (AK hρ (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2 ya qa)) *
          conj (VK b (finProdFinEquiv.symm t).1 j yb qb) =
        ((2 : ℂ) ^ q)⁻¹ * (((if j.val = 0 then cD q else 0) *
          ψ hρ (finProdFinEquiv.symm (finProdFinEquiv.symm t).2) (xa, xb)) *
          conj ((if j.val = 0 then cD q else 0) *
            ψ hρ (finProdFinEquiv.symm (finProdFinEquiv.symm t).2) (ya, yb))) := by
      intro t j
      rw [factor _ _ _ _ (S q) S_conj]
      simp only [AK, VK]
      rw [phi hρ hbq, phi hρ hbq]
    simp_rw [h1]
    rw [sum_fp (fun i z => ∑ j : Fin (2 ^ q), ((2 : ℂ) ^ q)⁻¹ * (((if j.val = 0 then cD q else 0) *
          ψ hρ (finProdFinEquiv.symm z) (xa, xb)) *
          conj ((if j.val = 0 then cD q else 0) * ψ hρ (finProdFinEquiv.symm z) (ya, yb))))]
    have h0 : (0 : ℕ) < 2 ^ q := by positivity
    have h2 : ∀ z : Fin (a * b), ∑ j : Fin (2 ^ q), ((2 : ℂ) ^ q)⁻¹ * (((if j.val = 0 then cD q else 0) *
          ψ hρ (finProdFinEquiv.symm z) (xa, xb)) *
          conj ((if j.val = 0 then cD q else 0) * ψ hρ (finProdFinEquiv.symm z) (ya, yb))) =
        ((2 : ℂ) ^ q)⁻¹ * ((2 : ℂ) ^ q)⁻¹ *
          (ψ hρ (finProdFinEquiv.symm z) (xa, xb) * conj (ψ hρ (finProdFinEquiv.symm z) (ya, yb))) := by
      intro z
      rw [Finset.sum_eq_single ⟨0, h0⟩]
      · simp only [if_true, map_mul, cD_conj]
        rw [← cD_sq]; ring
      · intro j _ hj
        have : ¬ j.val = 0 := fun h => hj (Fin.ext h)
        simp [this]
      · simp
    simp_rw [h2]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      sum_fp1 (fun z => ((2 : ℂ) ^ q)⁻¹ * ((2 : ℂ) ^ q)⁻¹ * (ψ hρ z (xa, xb) * conj (ψ hρ z (ya, yb)))),
      ← Finset.mul_sum, ← rho_dec hρ]
    push_cast
    field_simp

end X4AS

-- ===== ASSol =====

noncomputable section

section
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P42
open QAlgorithms.Papers.Independent.Information100.P21 (Op Vec FiniteLOCC)
open QAlgorithms.Papers.Independent.Dependency50.P42 (dimensionedPower singlets)
open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution (a b : ℕ) (ha : 0<a) (hb : 0<b)
    (rho : Op (Fin a × Fin b)) (hrho : IsDensityMatrix rho) :
    (∃ L : Superop (Fin (2^(Nat.clog 2 b)) × Fin (2^(Nat.clog 2 b))) (Fin a × Fin b),
      FiniteLOCC L ∧ OneWayBits (2*Nat.clog 2 b) L ∧ L (singlets (Nat.clog 2 b))=rho) ∧
    (∀ q : ℕ, b=2^q → Nat.clog 2 b=q) := by
  refine ⟨X4AS.prep_q hb (Nat.le_pow_clog (by norm_num) b) hrho, ?_⟩
  rintro q rfl
  exact Nat.clog_pow 2 q (by norm_num)

end
end
