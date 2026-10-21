-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P13.qft_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T05:03:52.586467+00:00
-- url     : https://prove2.me/submissions/c6cca238-2dac-475e-b909-3006ddd57d26

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P13
noncomputable section
open scoped Classical
open QAlgorithms.Papers.Independent.Support21.P13

lemma g66i_omega_eq : QAlgorithms.gateT true true =
    ((Real.sqrt 2 / 2 : ℝ) : ℂ) + ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I := by
  simp only [QAlgorithms.gateT, Matrix.diagonal_apply_eq, if_true]
  rw [show Complex.I * (Real.pi : ℂ) / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
    Real.sin_pi_div_four]

lemma g66i_omega_prim : IsPrimitiveRoot (QAlgorithms.gateT true true) 8 := by
  have h := Complex.isPrimitiveRoot_exp 8 (by norm_num)
  convert h using 1
  simp only [QAlgorithms.gateT, Matrix.diagonal_apply_eq, if_true]
  congr 1; push_cast; ring

lemma g66i_I_eq : Complex.I = (QAlgorithms.gateT true true) ^ 2 := by
  rw [g66i_omega_eq]
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  push_cast
  linear_combination (-Complex.I / 2) * h2 - (((Real.sqrt 2 : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq

lemma g66i_sqrt2_eq : ((Real.sqrt 2 : ℝ) : ℂ) =
    QAlgorithms.gateT true true - (QAlgorithms.gateT true true) ^ 3 := by
  rw [g66i_omega_eq]
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  push_cast
  linear_combination (-((Real.sqrt 2 : ℝ) : ℂ) / 4 * (1 - Complex.I)) * h2 + (((Real.sqrt 2 : ℝ) : ℂ) ^ 3 / 8 * (3 + Complex.I)) * Complex.I_sq

abbrev g66i_K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {QAlgorithms.gateT true true}

lemma g66i_ring_le : synthesisRing ≤ g66i_K.toSubring := by
  have hw : QAlgorithms.gateT true true ∈ g66i_K :=
    IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
  unfold synthesisRing
  rw [Subring.closure_le]
  intro x hx
  rcases hx with rfl | rfl
  · show _ ∈ g66i_K
    apply inv_mem
    rw [g66i_sqrt2_eq]; exact sub_mem hw (pow_mem hw 3)
  · show _ ∈ g66i_K
    rw [g66i_I_eq]; exact pow_mem hw 2

lemma g66i_finrank : Module.finrank ℚ g66i_K = 4 := by
  have hint : IsIntegral ℚ (QAlgorithms.gateT true true) :=
    g66i_omega_prim.isIntegral (by norm_num) |>.tower_top
  rw [IntermediateField.adjoin.finrank hint, ← Polynomial.cyclotomic_eq_minpoly_rat g66i_omega_prim (by norm_num),
    Polynomial.natDegree_cyclotomic]
  decide

lemma g66i_deg_le (a : ℂ) (ha : a ∈ synthesisRing) : (minpoly ℚ a).natDegree ≤ 4 := by
  have hint : IsIntegral ℚ (QAlgorithms.gateT true true) :=
    g66i_omega_prim.isIntegral (by norm_num) |>.tower_top
  have : FiniteDimensional ℚ g66i_K := IntermediateField.adjoin.finiteDimensional hint
  have hK : a ∈ g66i_K := g66i_ring_le ha
  have := minpoly.natDegree_le (A := ℚ) (⟨a, hK⟩ : g66i_K)
  rw [g66i_finrank] at this
  have e := minpoly.algebraMap_eq (A := ℚ) (algebraMap g66i_K ℂ).injective (⟨a, hK⟩ : g66i_K)
  rw [← e] at this
  convert this using 3
  rfl

lemma g66i_prim_root_bound (a : ℂ) (ha : a ∈ synthesisRing) (N : ℕ) (hN : 0 < N)
    (hp : IsPrimitiveRoot a N) : N.totient ≤ 4 := by
  have := g66i_deg_le a ha
  rwa [← Polynomial.cyclotomic_eq_minpoly_rat hp hN, Polynomial.natDegree_cyclotomic] at this

lemma g66i_isqrt_mem : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ∈ synthesisRing :=
  Subring.subset_closure (by simp)

lemma g66i_I_mem : Complex.I ∈ synthesisRing :=
  Subring.subset_closure (by simp)

lemma g66i_sqrt_mem : ((Real.sqrt 2 : ℝ) : ℂ) ∈ synthesisRing := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) = 2 * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
    field_simp; linear_combination h2
  rw [h]; exact mul_mem (by simpa using (synthesisRing.natCast_mem 2)) g66i_isqrt_mem

lemma g66i_omega_mem : QAlgorithms.gateT true true ∈ synthesisRing := by
  have h : QAlgorithms.gateT true true =
      ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ + Complex.I * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    simp only [QAlgorithms.gateT, Matrix.diagonal_apply_eq, if_true]
    rw [show Complex.I * (Real.pi : ℂ) / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
      Real.sin_pi_div_four]
    have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
    push_cast
    field_simp
    linear_combination (1 + Complex.I) * h2
  rw [h]; exact add_mem g66i_isqrt_mem (mul_mem g66i_I_mem g66i_isqrt_mem)

def g66i_P {ι : Type*} (M : Matrix ι ι ℂ) : Prop := ∀ i j, M i j ∈ synthesisRing

lemma g66i_prod_mem {ι : Type*} [Fintype ι] [DecidableEq ι] (L : List (Matrix ι ι ℂ))
    (h : ∀ M ∈ L, g66i_P M) : g66i_P L.prod := by
  induction L with
  | nil =>
    intro i j; simp only [List.prod_nil, Matrix.one_apply]
    split_ifs
    · exact synthesisRing.one_mem
    · exact synthesisRing.zero_mem
  | cons M L ih =>
    intro i j
    rw [List.prod_cons, Matrix.mul_apply]
    refine Subring.sum_mem _ (fun k _ => mul_mem (h M (by simp) i k) (ih (fun N hN => h N (by simp [hN])) k j))

lemma g66i_embed_mem {k n : ℕ} (M : Matrix (QAlgorithms.Qubits k) (QAlgorithms.Qubits k) ℂ)
    (w : Fin k ↪ Fin n) (hM : g66i_P M) : g66i_P (QAlgorithms.embedOp M w) := by
  intro i j
  simp only [QAlgorithms.embedOp, Matrix.of_apply]
  split_ifs
  · exact hM _ _
  · exact synthesisRing.zero_mem

lemma g66i_of1 (M : Matrix Bool Bool ℂ) (hM : g66i_P M) : g66i_P (QAlgorithms.Gate.ofMatrix1 M).mat :=
  fun i j => hM _ _

lemma g66i_of2 (M : Matrix (Bool × Bool) (Bool × Bool) ℂ) (hM : g66i_P M) :
    g66i_P (QAlgorithms.Gate.ofMatrix2 M).mat :=
  fun i j => hM _ _

lemma g66i_gate_mem {n : ℕ} (g : QAlgorithms.GateApp cliffordTLibrary n) : g66i_P g.gate.mat := by
  obtain ⟨gate, mem, wires⟩ := g
  simp only [cliffordTLibrary, Set.mem_insert_iff, Set.mem_singleton_iff] at mem
  rcases mem with rfl | rfl | rfl | rfl
  · apply g66i_of1; intro i j
    simp only [QAlgorithms.hadamard, Matrix.of_apply]
    split_ifs
    · exact neg_mem g66i_isqrt_mem
    · exact g66i_isqrt_mem
  · apply g66i_of1; intro i j
    simp only [QAlgorithms.phaseS, Matrix.diagonal_apply]
    split_ifs
    · exact g66i_I_mem
    · exact synthesisRing.one_mem
    · exact synthesisRing.zero_mem
  · apply g66i_of1; intro i j
    have hw := g66i_omega_mem
    simp only [QAlgorithms.gateT, Matrix.diagonal_apply] at hw ⊢
    split_ifs
    · simpa using hw
    · exact synthesisRing.one_mem
    · exact synthesisRing.zero_mem
  · apply g66i_of2; intro i j
    simp only [QAlgorithms.cnot, Matrix.of_apply]
    split_ifs
    · exact synthesisRing.one_mem
    · exact synthesisRing.zero_mem

lemma g66i_circ_mem {n : ℕ} (c : QAlgorithms.Circuit cliffordTLibrary n) : g66i_P c.unitary := by
  unfold QAlgorithms.Circuit.unitary
  apply g66i_prod_mem
  intro M hM
  rw [List.mem_reverse, List.mem_map] at hM
  obtain ⟨g, -, rfl⟩ := hM
  exact g66i_embed_mem _ _ (g66i_gate_mem g)

theorem solution (n : ℕ) (hn : 3 < n) :
    ¬ ∃ c : QAlgorithms.Circuit cliffordTLibrary n,
      c.unitary = QAlgorithms.qftQubits n := by
  rintro ⟨c, hc⟩
  have h1 : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  set y := (QAlgorithms.bitsEquivFin n).symm ⟨1, h1⟩ with hy
  have hmem := g66i_circ_mem c y y
  rw [hc] at hmem
  simp only [QAlgorithms.qftQubits, Matrix.submatrix_apply, hy, Equiv.apply_symm_apply,
    QAlgorithms.qftMatrix, Matrix.of_apply] at hmem
  have hs : Real.sqrt (((2 ^ n : ℕ) : ℝ)) = Real.sqrt 2 ^ n := by
    rw [show (((2 ^ n : ℕ) : ℝ)) = (Real.sqrt 2 ^ n) ^ 2 by
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]; push_cast; ring]
    exact Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg _) _)
  rw [hs] at hmem
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
  have hz : Complex.exp (2 * Real.pi * Complex.I / ((2 ^ n : ℕ) : ℂ)) ∈ synthesisRing := by
    have := mul_mem hmem (pow_mem g66i_sqrt_mem n)
    convert this using 1
    push_cast
    field_simp
  have hp := Complex.isPrimitiveRoot_exp (2 ^ n) (by positivity)
  have := g66i_prim_root_bound _ hz (2 ^ n) (by positivity) hp
  rw [Nat.totient_prime_pow Nat.prime_two (by omega)] at this
  have h8 : 2 ^ 3 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega
