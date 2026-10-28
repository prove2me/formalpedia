-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.separable_quadratic_rays
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:41:07.05862+00:00
-- url     : https://prove2.me/submissions/863341a7-2c7f-4cf2-beb1-590f2ec582d5

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

def S180Q_L (c : Fin 4 → ℝ) : Fin 4 → ℝ := ![c 0 + c 1 + c 2 + c 3, c 0 + c 2, c 0 + c 3, c 0]

lemma S180Q_rec (c : Fin 4 → ℝ) : c = ∑ i, S180Q_L c i • quadGenerators i := by
  funext k; fin_cases k <;> simp [S180Q_L, quadGenerators, Fin.sum_univ_four] <;> ring

lemma S180Q_Lsum (w : Fin 4 → ℝ) : S180Q_L (∑ i, w i • quadGenerators i) = w := by
  funext k; fin_cases k <;> simp [S180Q_L, quadGenerators, Fin.sum_univ_four] <;> ring

lemma S180Q_Ladd (u v : Fin 4 → ℝ) : S180Q_L (u + v) = S180Q_L u + S180Q_L v := by
  funext k; fin_cases k <;> simp [S180Q_L] <;> ring

lemma S180Q_Lsmul (a : ℝ) (u : Fin 4 → ℝ) : S180Q_L (a • u) = a • S180Q_L u := by
  funext k; fin_cases k <;> simp [S180Q_L] <;> ring

lemma S180Q_Lgen (j : Fin 4) : S180Q_L (quadGenerators j) = Pi.single j 1 := by
  fin_cases j <;> funext k <;> fin_cases k <;> simp [S180Q_L, quadGenerators, Pi.single_apply]

lemma S180Q_Linj {u v : Fin 4 → ℝ} (h : S180Q_L u = S180Q_L v) : u = v := by
  rw [S180Q_rec u, S180Q_rec v, h]

lemma S180Q_ray_smul {v : Fin 4 → ℝ} {k : ℝ} (hk : 0 < k) : ray (k • v) = ray v := by
  ext w; simp only [ray, Set.mem_setOf_eq]
  constructor
  · rintro ⟨c, hc, rfl⟩; exact ⟨c * k, mul_nonneg hc hk.le, by rw [smul_smul]⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c / k, div_nonneg hc hk.le, by rw [smul_smul, div_mul_cancel₀ _ hk.ne']⟩

lemma S180Q_cone (C : Set (Fin 4 → ℝ)) (hC : ∀ c, c ∈ C ↔ ∀ i, 0 ≤ S180Q_L c i) :
    extremeRays C = {R | ∃ j : Fin 4, R = ray (quadGenerators j)} ∧
    (∀ c ∈ C, ∃! w : Fin 4 → ℝ, (∀ j, 0 ≤ w j) ∧ c = ∑ j, w j • quadGenerators j) := by
  refine ⟨?_, ?_⟩
  · ext R
    simp only [extremeRays, Set.mem_setOf_eq]
    constructor
    · rintro ⟨v, ⟨hv0, hvC, hext⟩, rfl⟩
      have hL := (hC v).1 hvC
      obtain ⟨i, hi⟩ : ∃ i, S180Q_L v i ≠ 0 := by
        by_contra h; simp only [ne_eq, not_exists, not_not] at h
        exact hv0 (S180Q_Linj (by funext k; rw [h k]; fin_cases k <;> simp [S180Q_L]))
      have hipos : 0 < S180Q_L v i := lt_of_le_of_ne (hL i) (Ne.symm hi)
      set u := S180Q_L v i • quadGenerators i
      have huC : u ∈ C := by
        rw [hC]; intro k
        simp only [u, S180Q_Lsmul, S180Q_Lgen, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
        split_ifs <;> nlinarith
      have hwC : v - u ∈ C := by
        rw [hC]; intro k
        have : S180Q_L (v - u) = S180Q_L v - S180Q_L u := by
          have := S180Q_Ladd (v - u) u; simp at this; rw [this]; ring
        rw [this]
        simp only [u, S180Q_Lsmul, S180Q_Lgen, Pi.sub_apply, Pi.smul_apply, Pi.single_apply,
          smul_eq_mul]
        split_ifs with h
        · subst h; simp
        · simpa using hL k
      obtain ⟨a, b, ha, hb, hua, -⟩ := hext u huC (v - u) hwC (by abel)
      have ha0 : a ≠ 0 := by
        rintro rfl
        have h1 : S180Q_L u i = S180Q_L v i := by
          simp only [u, S180Q_Lsmul, S180Q_Lgen, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
            mul_one]
        rw [hua, zero_smul] at h1
        exact hi (by rw [← h1]; fin_cases i <;> simp [S180Q_L])
      have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      refine ⟨i, ?_⟩
      have hv : v = (S180Q_L v i / a) • quadGenerators i := by
        have h2 : a • v = S180Q_L v i • quadGenerators i := hua.symm
        calc v = a⁻¹ • (a • v) := by rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]
          _ = _ := by rw [h2, smul_smul, div_eq_inv_mul]
      rw [hv, S180Q_ray_smul (div_pos hipos hapos)]
    · rintro ⟨j, rfl⟩
      refine ⟨quadGenerators j, ⟨?_, ?_, ?_⟩, rfl⟩
      · intro h; have := congrArg (fun x => S180Q_L x j) h
        simp only [S180Q_Lgen, Pi.single_eq_same] at this
        fin_cases j <;> simp [S180Q_L] at this
      · rw [hC, S180Q_Lgen]; intro k; simp [Pi.single_apply]; split_ifs <;> norm_num
      · intro u hu w hw huw
        have hLu := (hC u).1 hu
        have hLw := (hC w).1 hw
        have hs : S180Q_L u + S180Q_L w = Pi.single j 1 := by
          rw [← S180Q_Ladd, huw, S180Q_Lgen]
        have hzero : ∀ k, k ≠ j → S180Q_L u k = 0 ∧ S180Q_L w k = 0 := by
          intro k hk
          have := congrFun hs k
          simp [Pi.single_apply, hk] at this
          constructor <;> linarith [hLu k, hLw k]
        refine ⟨S180Q_L u j, S180Q_L w j, hLu j, hLw j, ?_, ?_⟩
        · apply S180Q_Linj; rw [S180Q_Lsmul, S180Q_Lgen]; funext k
          by_cases hk : k = j
          · subst hk; simp
          · simp [Pi.single_apply, hk, (hzero k hk).1]
        · apply S180Q_Linj; rw [S180Q_Lsmul, S180Q_Lgen]; funext k
          by_cases hk : k = j
          · subst hk; simp
          · simp [Pi.single_apply, hk, (hzero k hk).2]
  · intro c hc
    refine ⟨S180Q_L c, ⟨(hC c).1 hc, S180Q_rec c⟩, ?_⟩
    rintro w ⟨-, rfl⟩
    exact (S180Q_Lsum w).symm

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

lemma S180Q_nec (c : Fin 4 → ℝ) (hc : c ∈ quadCone) :
    0 ≤ c 0 ∧ 0 ≤ c 0 + c 2 ∧ 0 ≤ c 0 + c 3 ∧ 0 ≤ c 0 + c 1 + c 2 + c 3 := by
  set K := |c 1| + |c 2| + |c 3|
  have hK : 0 ≤ K := by positivity
  have hP := S180Q_pure
  have hKN : ∀ N : ℕ, -(K / N) = -(|c 1| * (1 / N) + |c 2| * (1 / N) + |c 3| * (1 / N)) := by
    intro N; simp only [K]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine S180Q_lim hK (fun N hN => ?_)
    obtain ⟨m1, m2, m3⟩ := S180Q_mixed N hN
    have := S180Q_test hN hN _ _ ⟨m1, m2⟩ ⟨m1, m2⟩ c hc
    rw [m3] at this
    have hu : (0 : ℝ) < 1 / N := by positivity
    have hu1 : (1 : ℝ) / N ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hN)]; exact_mod_cast hN
    have q1 : c 1 * (1 / N * (1 / N)) ≤ |c 1| * (1 / N) := by
      have h1 : c 1 * (1 / N * (1 / N)) ≤ |c 1| * (1 / N * (1 / N)) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      have h2 : |c 1| * (1 / N * (1 / N)) ≤ |c 1| * (1 / N) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg _)
      linarith
    have q2 := mul_le_mul_of_nonneg_right (le_abs_self (c 2)) hu.le
    have q3 := mul_le_mul_of_nonneg_right (le_abs_self (c 3)) hu.le
    rw [hKN]; linarith
  · refine S180Q_lim hK (fun N hN => ?_)
    obtain ⟨m1, m2, m3⟩ := S180Q_mixed N hN
    have := S180Q_test one_pos hN _ _ ⟨hP.1, hP.2.1⟩ ⟨m1, m2⟩ c hc
    rw [m3, hP.2.2] at this
    have hu : (0 : ℝ) < 1 / N := by positivity
    have q1 := mul_le_mul_of_nonneg_right (le_abs_self (c 1)) hu.le
    have q3 := mul_le_mul_of_nonneg_right (le_abs_self (c 3)) hu.le
    have q2 := mul_nonneg (abs_nonneg (c 2)) hu.le
    simp only [one_mul, mul_one] at this
    rw [hKN]; linarith
  · refine S180Q_lim hK (fun N hN => ?_)
    obtain ⟨m1, m2, m3⟩ := S180Q_mixed N hN
    have := S180Q_test hN one_pos _ _ ⟨m1, m2⟩ ⟨hP.1, hP.2.1⟩ c hc
    rw [m3, hP.2.2] at this
    have hu : (0 : ℝ) < 1 / N := by positivity
    have q1 := mul_le_mul_of_nonneg_right (le_abs_self (c 1)) hu.le
    have q2 := mul_le_mul_of_nonneg_right (le_abs_self (c 2)) hu.le
    have q3 := mul_nonneg (abs_nonneg (c 3)) hu.le
    simp only [one_mul, mul_one] at this
    rw [hKN]; linarith
  · have := S180Q_test one_pos one_pos _ _ ⟨hP.1, hP.2.1⟩ ⟨hP.1, hP.2.1⟩ c hc
    rw [hP.2.2] at this
    linarith

theorem solution  :
    extremeRays quadCone = {R | ∃ j : Fin 4, R = ray (quadGenerators j)} ∧
    (∀ c : Fin 4 → ℝ, c ∈ quadCone ↔
      0 ≤ c 0 ∧ 0 ≤ c 0+c 2 ∧ 0 ≤ c 0+c 3 ∧ 0 ≤ c 0+c 1+c 2+c 3) ∧
    (∀ c ∈ quadCone, ∃! w : Fin 4 → ℝ,
      (∀ j, 0 ≤ w j) ∧ c = ∑ j, w j • quadGenerators j) := by
  have hmem : ∀ c : Fin 4 → ℝ, c ∈ quadCone ↔
      0 ≤ c 0 ∧ 0 ≤ c 0+c 2 ∧ 0 ≤ c 0+c 3 ∧ 0 ≤ c 0+c 1+c 2+c 3 := by
    intro c
    refine ⟨S180Q_nec c, fun ⟨h0, h2, h3, h4⟩ => ?_⟩
    intro a b _ _ X hX
    exact S180Q_suff c h0 h2 h3 h4 X hX
  have hC : ∀ c, c ∈ quadCone ↔ ∀ i, 0 ≤ S180Q_L c i := by
    intro c
    rw [hmem]
    constructor
    · rintro ⟨h0, h2, h3, h4⟩ i
      fin_cases i <;> simp [S180Q_L] <;> linarith
    · intro h
      have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
      simp [S180Q_L] at h0 h1 h2 h3
      exact ⟨h3, h1, h2, by linarith⟩
  obtain ⟨r1, r3⟩ := S180Q_cone quadCone hC
  exact ⟨r1, hmem, r3⟩
