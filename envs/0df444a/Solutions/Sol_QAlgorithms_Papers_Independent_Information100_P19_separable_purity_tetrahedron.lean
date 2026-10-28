-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.separable_purity_tetrahedron
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:44:26.107395+00:00
-- url     : https://prove2.me/submissions/29f6be3a-324c-408c-8791-858637991ef3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19
open Matrix Finset WithLp QAlgorithms.Papers.Independent.Information100.P19
open scoped ComplexOrder MatrixOrder

section
variable {n : Type*} [Fintype n] [DecidableEq n]
lemma S180_tr_sq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (A ^ 2).trace = ∑ i, ((hA.eigenvalues i : ℂ)) ^ 2 := by
  have h := hA.spectral_theorem
  conv_lhs => rw [h]
  rw [← map_pow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
    Matrix.one_mul, diagonal_pow, trace_diagonal]
  simp

lemma S180_frob {A : Matrix n n ℂ} (hA : A.PosSemidef) (htr : A.trace = 1) :
    ∑ i, ∑ k, ‖A i k‖ ^ 2 ≤ 1 := by
  have hH := hA.1
  have e1 : ((A ^ 2).trace).re = ∑ i, ∑ k, ‖A i k‖ ^ 2 := by
    have : A ^ 2 = A * Aᴴ := by rw [hH.eq, sq]
    rw [this]
    simp only [Matrix.trace, Matrix.diag, mul_apply, conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; norm_cast
  rw [← e1, S180_tr_sq hH]
  have hl : ∀ i, 0 ≤ hH.eigenvalues i := hA.eigenvalues_nonneg
  have hs : ∑ i, hH.eigenvalues i = 1 := by
    have := congrArg Complex.re (hH.trace_eq_sum_eigenvalues)
    rw [htr] at this; simpa using this.symm
  have : ∑ i, hH.eigenvalues i ^ 2 ≤ (∑ i, hH.eigenvalues i) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hl i)
  rw [hs] at this
  simpa [← Complex.ofReal_pow] using this

end
section
variable {n : Type*} [Fintype n] [DecidableEq n]
lemma g53h_sqrt_sq {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    cfc Real.sqrt A * cfc Real.sqrt A = A := by
  rw [← cfcₙ_eq_cfc (hf0 := Real.sqrt_zero), ← CFC.sqrt_eq_real_sqrt A hA.nonneg]
  exact CFC.sqrt_mul_sqrt_self A hA.nonneg

lemma g53h_tr_psd_mul {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace.re := by
  have hs : (cfc Real.sqrt A).IsHermitian := by
    have : (cfc Real.sqrt A).PosSemidef := by
      rw [← Matrix.nonneg_iff_posSemidef]; exact cfc_nonneg (fun x _ => Real.sqrt_nonneg x)
    exact this.1
  rw [← g53h_sqrt_sq hA, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have h := hB.conjTranspose_mul_mul_same (cfc Real.sqrt A)
  rw [hs.eq] at h
  have := h.trace_nonneg
  rw [← Matrix.mul_assoc]
  exact (Complex.nonneg_iff.1 this).1


lemma S180Q_tr_real {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (((A * B).trace.re : ℝ) : ℂ) = (A * B).trace := by
  have : (starRingEnd ℂ) (A * B).trace = (A * B).trace := by
    rw [← Complex.star_def, ← trace_conjTranspose, conjTranspose_mul, hA.eq, hB.eq,
      trace_mul_comm]
  exact Complex.conj_eq_iff_re.mp this

lemma S180Q_tr_le_one {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hAt : A.trace = 1)
    (hB : B.PosSemidef) (hBt : B.trace = 1) : (A * B).trace.re ≤ 1 := by
  have h1 : (A * B).trace.re ≤ ∑ i, ∑ k, ‖A i k‖ * ‖B i k‖ := by
    simp only [Matrix.trace, Matrix.diag, mul_apply, Complex.re_sum]
    refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun k _ => ?_))
    have : ‖B k i‖ = ‖B i k‖ := by rw [← hB.1.apply i k, norm_star]
    calc (A i k * B k i).re ≤ ‖A i k * B k i‖ := Complex.re_le_norm _
      _ = _ := by rw [norm_mul, this]
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (n × n))
    (fun p => ‖A p.1 p.2‖) (fun p => ‖B p.1 p.2‖)
  simp only [Fintype.sum_prod_type] at h2
  have fa := Real.sqrt_le_one.mpr (S180_frob hA hAt)
  have fb := Real.sqrt_le_one.mpr (S180_frob hB hBt)
  have := mul_le_mul fa fb (Real.sqrt_nonneg _) zero_le_one
  linarith

lemma S180Q_tr_nonneg {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := g53h_tr_psd_mul hA hB

end

variable {a b : ℕ}

lemma S180Q_sqtrace {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} (w : Fin q → ℝ)
    (A : Fin q → Matrix ι ι ℂ) (hA : ∀ j, (A j).IsHermitian) :
    ((((∑ j, (w j : ℂ) • A j) ^ 2).trace).re) =
      ∑ j, ∑ k, w j * w k * (A j * A k).trace.re := by
  rw [sq, Finset.sum_mul_sum, trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [smul_mul_smul_comm, trace_smul, smul_eq_mul, ← Complex.ofReal_mul, Complex.re_ofReal_mul]

lemma S180Q_formula {q : ℕ} (w : Fin q → ℝ) (A : Fin q → Matrix (Fin a) (Fin a) ℂ)
    (B : Fin q → Matrix (Fin b) (Fin b) ℂ)
    (hA : ∀ j, (A j).PosSemidef ∧ (A j).trace = 1) (hB : ∀ j, (B j).PosSemidef ∧ (B j).trace = 1)
    (c : Fin 4 → ℝ) :
    quadEval c (∑ j, (w j : ℂ) • kronecker (A j) (B j)) =
      ∑ j, ∑ k, w j * w k * (c 0 + c 1 * ((A j * A k).trace.re * (B j * B k).trace.re) +
        c 2 * (A j * A k).trace.re + c 3 * (B j * B k).trace.re) := by
  set X := ∑ j, (w j : ℂ) • kronecker (A j) (B j) with hX
  have hmass : mass X = ∑ j, w j := by
    rw [mass, powerTrace, pow_one, hX, trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [trace_smul, Matrix.kronecker, trace_kronecker, (hA j).2, (hB j).2]
    simp
  have hpi : powerTrace X 2 = ∑ j, ∑ k, w j * w k *
      ((A j * A k).trace.re * (B j * B k).trace.re) := by
    rw [powerTrace, hX, sq, Finset.sum_mul_sum, trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [smul_mul_smul_comm, Matrix.kronecker, ← mul_kronecker_mul, trace_smul, trace_kronecker,
      ← S180Q_tr_real (hA j).1.1 (hA k).1.1, ← S180Q_tr_real (hB j).1.1 (hB k).1.1, smul_eq_mul]
    simp only [← Complex.ofReal_mul, Complex.ofReal_re]
  have hmA : marginalA X = ∑ j, (w j : ℂ) • A j := by
    ext i i'
    simp only [marginalA, hX, Matrix.sum_apply, Matrix.smul_apply, kronecker, kroneckerMap_apply,
      smul_eq_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have := (hB j).2; simp only [Matrix.trace, Matrix.diag] at this
    rw [← Finset.mul_sum, ← Finset.mul_sum, this, mul_one]
  have hmB : marginalB X = ∑ j, (w j : ℂ) • B j := by
    ext i i'
    simp only [marginalB, hX, Matrix.sum_apply, Matrix.smul_apply, kronecker, kroneckerMap_apply,
      smul_eq_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have := (hA j).2; simp only [Matrix.trace, Matrix.diag] at this
    simp_rw [mul_comm (A j _ _) (B j i i')]
    rw [← Finset.mul_sum, ← Finset.mul_sum, this, mul_one]
  have hpA : purityA X = ∑ j, ∑ k, w j * w k * (A j * A k).trace.re := by
    rw [purityA, powerTrace, hmA, S180Q_sqtrace w A (fun j => (hA j).1.1)]
  have hpB : purityB X = ∑ j, ∑ k, w j * w k * (B j * B k).trace.re := by
    rw [purityB, powerTrace, hmB, S180Q_sqtrace w B (fun j => (hB j).1.1)]
  rw [quadEval, hmass, hpi, hpA, hpB, sq, Finset.sum_mul_sum]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  ring

lemma S180Q_suff (c : Fin 4 → ℝ) (h0 : 0 ≤ c 0) (h2 : 0 ≤ c 0 + c 2) (h3 : 0 ≤ c 0 + c 3)
    (h4 : 0 ≤ c 0 + c 1 + c 2 + c 3) (X : Bip a b)
    (hX : QAlgorithms.Entanglement.IsSeparablePositive X) : 0 ≤ quadEval c X := by
  obtain ⟨q, w, A, B, hw, hAB, rfl⟩ := hX
  rw [S180Q_formula w A B (fun j => (hAB j).1) (fun j => (hAB j).2)]
  refine Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => ?_))
  refine mul_nonneg (mul_nonneg (hw j) (hw k)) ?_
  set x := (A j * A k).trace.re
  set y := (B j * B k).trace.re
  have x0 : 0 ≤ x := S180Q_tr_nonneg (hAB j).1.1 (hAB k).1.1
  have y0 : 0 ≤ y := S180Q_tr_nonneg (hAB j).2.1 (hAB k).2.1
  have x1 : x ≤ 1 := S180Q_tr_le_one (hAB j).1.1 (hAB j).1.2 (hAB k).1.1 (hAB k).1.2
  have y1 : y ≤ 1 := S180Q_tr_le_one (hAB j).2.1 (hAB j).2.2 (hAB k).2.1 (hAB k).2.2
  have e : c 0 + c 1 * (x * y) + c 2 * x + c 3 * y =
      (1 - x) * (1 - y) * c 0 + x * (1 - y) * (c 0 + c 2) + (1 - x) * y * (c 0 + c 3) +
        x * y * (c 0 + c 1 + c 2 + c 3) := by ring
  rw [e]
  have p1 := mul_nonneg (mul_nonneg (sub_nonneg.2 x1) (sub_nonneg.2 y1)) h0
  have p2 := mul_nonneg (mul_nonneg x0 (sub_nonneg.2 y1)) h2
  have p3 := mul_nonneg (mul_nonneg (sub_nonneg.2 x1) y0) h3
  have p4 := mul_nonneg (mul_nonneg x0 y0) h4
  linarith

/-- density matrix (1/N) • 1 -/
lemma S180Q_mixed (N : ℕ) (hN : 0 < N) :
    ((1 / (N : ℂ)) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef ∧
    ((1 / (N : ℂ)) • (1 : Matrix (Fin N) (Fin N) ℂ)).trace = 1 ∧
    (((1 / (N : ℂ)) • (1 : Matrix (Fin N) (Fin N) ℂ)) *
      ((1 / (N : ℂ)) • (1 : Matrix (Fin N) (Fin N) ℂ))).trace.re = 1 / N := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨?_, ?_, ?_⟩
  · have : (1 / (N : ℂ)) = ((1 / (N : ℝ) : ℝ) : ℂ) := by push_cast; rfl
    rw [this]
    exact Matrix.PosSemidef.one.smul (by positivity)
  · rw [trace_smul, trace_one]; simp [hN']
  · rw [smul_mul_smul_comm, Matrix.one_mul, trace_smul, trace_one]
    simp
    field_simp

lemma S180Q_pure : (1 : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef ∧
    (1 : Matrix (Fin 1) (Fin 1) ℂ).trace = 1 ∧
    ((1 : Matrix (Fin 1) (Fin 1) ℂ) * 1).trace.re = 1 := by
  refine ⟨Matrix.PosSemidef.one, by simp, by simp⟩

lemma S180Q_test {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (A : Matrix (Fin a) (Fin a) ℂ)
    (B : Matrix (Fin b) (Fin b) ℂ) (hA : A.PosSemidef ∧ A.trace = 1)
    (hB : B.PosSemidef ∧ B.trace = 1) (c : Fin 4 → ℝ) (hc : c ∈ quadCone) :
    0 ≤ c 0 + c 1 * ((A * A).trace.re * (B * B).trace.re) + c 2 * (A * A).trace.re +
      c 3 * (B * B).trace.re := by
  have hsep : QAlgorithms.Entanglement.IsSeparablePositive
      (∑ j : Fin 1, ((fun _ => (1 : ℝ)) j : ℂ) • kronecker ((fun _ => A) j) ((fun _ => B) j)) :=
    ⟨1, fun _ => 1, fun _ => A, fun _ => B, fun _ => zero_le_one, fun _ => ⟨hA, hB⟩, rfl⟩
  have := hc a b ha hb _ hsep
  rw [S180Q_formula (fun _ => (1 : ℝ)) (fun _ => A) (fun _ => B) (fun _ => hA) (fun _ => hB)] at this
  simpa using this

lemma S180Q_lim {x K : ℝ} (hK : 0 ≤ K) (h : ∀ N : ℕ, 0 < N → -(K / N) ≤ x) : 0 ≤ x := by
  by_contra hx; push_neg at hx
  obtain ⟨N, hN⟩ := exists_nat_gt (K / (-x))
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg hK (by linarith)) hN
  have := h N (by exact_mod_cast hNpos)
  rw [div_lt_iff₀ (by linarith)] at hN
  rw [neg_le, le_div_iff₀ hNpos] at this
  nlinarith


def S180T_H : Set (Fin 3 → ℝ) := {v | 0 ≤ v 0 ∧ v 0 ≤ v 1 ∧ v 0 ≤ v 2 ∧ v 1+v 2 ≤ 1+v 0}

lemma S180T_K2_sub : K2 ⊆ S180T_H := by
  rintro v ⟨a, b, ha, hb, X, hX, hm, rfl⟩
  have q0 := S180Q_suff ![0,1,0,0] (by simp <;> norm_num) (by simp <;> norm_num) (by simp <;> norm_num) (by simp <;> norm_num) X hX
  have q1 := S180Q_suff ![0,-1,1,0] (by simp <;> norm_num) (by simp <;> norm_num) (by simp <;> norm_num) (by simp <;> norm_num) X hX
  have q2 := S180Q_suff ![0,-1,0,1] (by simp <;> norm_num) (by simp <;> norm_num) (by simp <;> norm_num) (by simp <;> norm_num) X hX
  have q3 := S180Q_suff ![1,1,-1,-1] (by simp <;> norm_num) (by simp <;> norm_num) (by simp <;> norm_num) (by simp <;> norm_num) X hX
  simp only [quadEval, hm] at q0 q1 q2 q3
  simp at q0 q1 q2 q3
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith

lemma S180T_H_convex : Convex ℝ S180T_H := by
  intro x hx y hy s t hs ht hst
  obtain ⟨x0, x1, x2, x3⟩ := hx
  obtain ⟨y0, y1, y2, y3⟩ := hy
  simp only [S180T_H, Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine ⟨by positivity, by nlinarith, by nlinarith, by nlinarith⟩

lemma S180T_H_closed : IsClosed S180T_H := by
  have c0 : Continuous (fun v : Fin 3 → ℝ => v 0) := continuous_apply 0
  have c1 : Continuous (fun v : Fin 3 → ℝ => v 1) := continuous_apply 1
  have c2 : Continuous (fun v : Fin 3 → ℝ => v 2) := continuous_apply 2
  have h := ((isClosed_le (continuous_const (y := (0:ℝ))) c0).inter (isClosed_le c0 c1)).inter
    ((isClosed_le c0 c2).inter (isClosed_le (c1.add c2) ((continuous_const (y := (1:ℝ))).add c0)))
  convert h using 1
  ext v; simp [S180T_H, and_assoc]

lemma S180T_H_eq : S180T_H = convexHull ℝ
    ({![0,0,0],![0,1,0],![0,0,1],![1,1,1]} : Set (Fin 3 → ℝ)) := by
  apply le_antisymm
  · rintro v ⟨h0, h1, h2, h3⟩
    have hv : v = (1 - v 1 - v 2 + v 0) • ![0,0,0] + (v 1 - v 0) • ![0,1,0] +
        (v 2 - v 0) • ![0,0,1] + v 0 • ![(1:ℝ),1,1] := by
      funext k; fin_cases k <;> simp <;> ring
    rw [hv]
    have hc := convex_convexHull ℝ ({![0,0,0],![0,1,0],![0,0,1],![1,1,1]} : Set (Fin 3 → ℝ))
    have m0 : ![(0:ℝ),0,0] ∈ convexHull ℝ ({![0,0,0],![0,1,0],![0,0,1],![1,1,1]} : Set (Fin 3 → ℝ)) :=
      subset_convexHull ℝ _ (by simp)
    have m1 : ![(0:ℝ),1,0] ∈ convexHull ℝ ({![0,0,0],![0,1,0],![0,0,1],![1,1,1]} : Set (Fin 3 → ℝ)) :=
      subset_convexHull ℝ _ (by simp)
    have m2 : ![(0:ℝ),0,1] ∈ convexHull ℝ ({![0,0,0],![0,1,0],![0,0,1],![1,1,1]} : Set (Fin 3 → ℝ)) :=
      subset_convexHull ℝ _ (by simp)
    have m3 : ![(1:ℝ),1,1] ∈ convexHull ℝ ({![0,0,0],![0,1,0],![0,0,1],![1,1,1]} : Set (Fin 3 → ℝ)) :=
      subset_convexHull ℝ _ (by simp)
    have e := hc.sum_mem (t := Finset.univ) (w := ![1 - v 1 - v 2 + v 0, v 1 - v 0, v 2 - v 0, v 0])
      (z := ![![0,0,0],![0,1,0],![0,0,1],![1,1,1]])
      (by intro i _; fin_cases i <;> simp <;> linarith)
      (by simp [Fin.sum_univ_four]; ring)
      (by intro i _; fin_cases i <;> simpa)
    simpa [Fin.sum_univ_four] using e
  · refine convexHull_min ?_ S180T_H_convex
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> simp [S180T_H]

lemma S180Q_prod_vals {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ)
    (hA : A.PosSemidef ∧ A.trace = 1) (hB : B.PosSemidef ∧ B.trace = 1) :
    (∑ j : Fin 1, ((fun _ => (1 : ℝ)) j : ℂ) • kronecker ((fun _ => A) j) ((fun _ => B) j)) =
      kronecker A B ∧
    mass (kronecker A B) = 1 ∧
    powerTrace (kronecker A B) 2 = (A * A).trace.re * (B * B).trace.re ∧
    purityA (kronecker A B) = (A * A).trace.re ∧ purityB (kronecker A B) = (B * B).trace.re ∧
    QAlgorithms.Entanglement.IsSeparablePositive (kronecker A B) := by
  have hs : (∑ j : Fin 1, ((fun _ => (1 : ℝ)) j : ℂ) • kronecker ((fun _ => A) j) ((fun _ => B) j))
      = kronecker A B := by simp
  have f := fun c : Fin 4 → ℝ => S180Q_formula (q := 1) (fun _ : Fin 1 => (1 : ℝ))
    (fun _ : Fin 1 => A) (fun _ : Fin 1 => B) (fun _ => hA) (fun _ => hB) c
  rw [hs] at f
  have fm : mass (kronecker A B) = 1 := by
    rw [mass, powerTrace, pow_one, Matrix.kronecker, trace_kronecker, hA.2, hB.2]; simp
  have f1 := f ![0,1,0,0]
  have f2 := f ![0,0,1,0]
  have f3 := f ![0,0,0,1]
  simp [quadEval] at f1 f2 f3
  refine ⟨hs, fm, f1, f2, f3, ?_⟩
  rw [← hs]
  exact ⟨1, fun _ => 1, fun _ => A, fun _ => B, fun _ => zero_le_one, fun _ => ⟨hA, hB⟩, rfl⟩

lemma S180T_mem_K2 {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (A : Matrix (Fin a) (Fin a) ℂ)
    (B : Matrix (Fin b) (Fin b) ℂ) (hA : A.PosSemidef ∧ A.trace = 1)
    (hB : B.PosSemidef ∧ B.trace = 1) :
    ![(A * A).trace.re * (B * B).trace.re, (A * A).trace.re, (B * B).trace.re] ∈ K2 := by
  obtain ⟨-, h1, h2, h3, h4, h5⟩ := S180Q_prod_vals A B hA hB
  exact ⟨a, b, ha, hb, kronecker A B, h5, h1, by rw [h2, h3, h4]⟩

lemma S180T_tend (x y z : ℕ → ℝ) (x0 y0 z0 : ℝ) (hx : Filter.Tendsto x Filter.atTop (nhds x0))
    (hy : Filter.Tendsto y Filter.atTop (nhds y0)) (hz : Filter.Tendsto z Filter.atTop (nhds z0)) :
    Filter.Tendsto (fun N => ![x N, y N, z N]) Filter.atTop (nhds ![x0, y0, z0]) := by
  rw [tendsto_pi_nhds]; intro k; fin_cases k <;> simpa

lemma S180T_vert_closure : ({![0,0,0],![0,1,0],![0,0,1],![1,1,1]} : Set (Fin 3 → ℝ)) ⊆
    closure K2 := by
  have hP := S180Q_pure
  have t0 : Filter.Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have mixN := fun N : ℕ => S180Q_mixed (N + 1) (Nat.succ_pos N)
  have cast : ∀ N : ℕ, ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := fun N => by push_cast; ring
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · refine mem_closure_of_tendsto (b := Filter.atTop) (f := fun N : ℕ =>
      ![(1 / ((N : ℝ) + 1)) * (1 / ((N : ℝ) + 1)), 1 / ((N : ℝ) + 1), 1 / ((N : ℝ) + 1)]) ?_ ?_
    · have := S180T_tend _ _ _ _ _ _ (by simpa using t0.mul t0) t0 t0
      simpa using this
    · refine Filter.Eventually.of_forall (fun N => ?_)
      obtain ⟨m1, m2, m3⟩ := mixN N
      have := S180T_mem_K2 (Nat.succ_pos N) (Nat.succ_pos N) _ _ ⟨m1, m2⟩ ⟨m1, m2⟩
      rw [m3, cast] at this; exact this
  · refine mem_closure_of_tendsto (b := Filter.atTop) (f := fun N : ℕ =>
      ![1 * (1 / ((N : ℝ) + 1)), 1, 1 / ((N : ℝ) + 1)]) ?_ ?_
    · have := S180T_tend (fun N : ℕ => 1 * (1 / ((N : ℝ) + 1))) (fun _ => 1)
        (fun N : ℕ => 1 / ((N : ℝ) + 1)) 0 1 0 (by simpa using t0) tendsto_const_nhds t0
      simpa using this
    · refine Filter.Eventually.of_forall (fun N => ?_)
      obtain ⟨m1, m2, m3⟩ := mixN N
      have := S180T_mem_K2 one_pos (Nat.succ_pos N) _ _ ⟨hP.1, hP.2.1⟩ ⟨m1, m2⟩
      rw [m3, hP.2.2, cast] at this; exact this
  · refine mem_closure_of_tendsto (b := Filter.atTop) (f := fun N : ℕ =>
      ![(1 / ((N : ℝ) + 1)) * 1, 1 / ((N : ℝ) + 1), 1]) ?_ ?_
    · have := S180T_tend (fun N : ℕ => (1 / ((N : ℝ) + 1)) * 1) (fun N : ℕ => 1 / ((N : ℝ) + 1))
        (fun _ => 1) 0 0 1 (by simpa using t0) t0 tendsto_const_nhds
      simpa using this
    · refine Filter.Eventually.of_forall (fun N => ?_)
      obtain ⟨m1, m2, m3⟩ := mixN N
      have := S180T_mem_K2 (Nat.succ_pos N) one_pos _ _ ⟨m1, m2⟩ ⟨hP.1, hP.2.1⟩
      rw [m3, hP.2.2, cast] at this; exact this
  · apply subset_closure
    have := S180T_mem_K2 one_pos one_pos _ _ ⟨hP.1, hP.2.1⟩ ⟨hP.1, hP.2.1⟩
    rw [hP.2.2] at this; simpa using this

theorem solution  :
    closure (convexHull ℝ K2) =
      {v | 0 ≤ v 0 ∧ v 0 ≤ v 1 ∧ v 0 ≤ v 2 ∧ v 1+v 2 ≤ 1+v 0} ∧
    closure (convexHull ℝ K2) = convexHull ℝ
      ({![0,0,0],![0,1,0],![0,0,1],![1,1,1]} : Set (Fin 3 → ℝ)) := by
  have h1 : closure (convexHull ℝ K2) ⊆ S180T_H :=
    closure_minimal (convexHull_min S180T_K2_sub S180T_H_convex) S180T_H_closed
  have h2 : S180T_H ⊆ closure (convexHull ℝ K2) := by
    rw [S180T_H_eq]
    refine convexHull_min ?_ (convex_convexHull ℝ K2).closure
    exact S180T_vert_closure.trans (closure_mono (subset_convexHull ℝ K2))
  have h := le_antisymm h1 h2
  exact ⟨h, h.trans S180T_H_eq⟩
