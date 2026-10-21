-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P13.controlledT_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T05:09:31.900098+00:00
-- url     : https://prove2.me/submissions/f40371a0-67f4-497a-95bf-fdceea1737d3

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

lemma g66i_det_embed2' (M : Matrix (QAlgorithms.Qubits 2) (QAlgorithms.Qubits 2) ℂ)
    (w : Fin 2 ↪ Fin 2) : (QAlgorithms.embedOp M w).det = M.det := by
  have hb : Function.Bijective w := Finite.injective_iff_bijective.mp w.injective
  let σ : Fin 2 ≃ Fin 2 := Equiv.ofBijective w hb
  let e : QAlgorithms.Qubits 2 ≃ QAlgorithms.Qubits 2 :=
    { toFun := fun y => y ∘ w, invFun := fun y => y ∘ σ.symm,
      left_inv := fun y => by
        funext c
        show y (σ (σ.symm c)) = y c
        rw [Equiv.apply_symm_apply],
      right_inv := fun y => by
        funext c
        show y (σ.symm (σ c)) = y c
        rw [Equiv.symm_apply_apply] }
  have : QAlgorithms.embedOp M w = M.submatrix e e := by
    ext y z
    simp only [QAlgorithms.embedOp, Matrix.of_apply, Matrix.submatrix_apply]
    rw [if_pos]
    · rfl
    · intro a ha; exact absurd (hb.2 a) ha
  rw [this, Matrix.det_submatrix_equiv_self]

lemma g66i_det_embed2 {k : ℕ} (hk : k = 2) (M : Matrix (QAlgorithms.Qubits k) (QAlgorithms.Qubits k) ℂ)
    (w : Fin k ↪ Fin 2) : (QAlgorithms.embedOp M w).det = M.det := by
  subst hk; exact g66i_det_embed2' M w

lemma g66i_fin2 : ∀ a c : Fin 2, c ≠ a ↔ c = (if a = 0 then 1 else 0) := by decide

lemma g66i_det_embed1' (M : Matrix (QAlgorithms.Qubits 1) (QAlgorithms.Qubits 1) ℂ)
    (w : Fin 1 ↪ Fin 2) : (QAlgorithms.embedOp M w).det = M.det ^ 2 := by
  set a := w 0 with ha
  set b : Fin 2 := if a = 0 then 1 else 0 with hbdef
  have hab : ∀ c : Fin 2, c ≠ a ↔ c = b := by
    intro c
    rw [hbdef]
    exact g66i_fin2 a c
  have hrange : ∀ c : Fin 2, c ∈ Set.range w ↔ c = a := by
    intro c; constructor
    · rintro ⟨i, rfl⟩; rw [ha, Subsingleton.elim i 0]
    · rintro rfl; exact ⟨0, rfl⟩
  have hba : b ≠ a := fun h => ((hab b).mpr rfl) h
  let e : QAlgorithms.Qubits 2 ≃ QAlgorithms.Qubits 1 × Bool :=
    { toFun := fun y => (fun _ => y a, y b),
      invFun := fun p c => if c = a then p.1 0 else p.2,
      left_inv := fun y => by
        funext c
        by_cases h : c = a
        · simp [h]
        · have := (hab c).mp h; simp [this, hba],
      right_inv := fun p => by
        obtain ⟨u, t⟩ := p
        ext1
        · funext i; simp [Subsingleton.elim i 0]
        · simp [hba] }
  have : QAlgorithms.embedOp M w = (Matrix.blockDiagonal fun _ : Bool => M).submatrix e e := by
    ext y z
    simp only [QAlgorithms.embedOp, Matrix.of_apply, Matrix.submatrix_apply,
      Matrix.blockDiagonal_apply, e, Equiv.coe_fn_mk]
    have hcond : (∀ c : Fin 2, c ∉ Set.range w → y c = z c) ↔ y b = z b := by
      constructor
      · intro h; apply h; rw [hrange]; exact (hab b).mpr rfl
      · intro h c hc; rw [hrange] at hc; rw [(hab c).mp hc]; exact h
    have hy : y ∘ w = fun _ => y a := by funext i; simp [ha, Subsingleton.elim i 0]
    have hz : z ∘ w = fun _ => z a := by funext i; simp [ha, Subsingleton.elim i 0]
    by_cases h : y b = z b
    · rw [if_pos (hcond.mpr h), if_pos h, hy, hz]
    · rw [if_neg (fun h' => h (hcond.mp h')), if_neg h]
  rw [this, Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal, Fintype.prod_bool, sq]

lemma g66i_det_embed1 {k : ℕ} (hk : k = 1) (M : Matrix (QAlgorithms.Qubits k) (QAlgorithms.Qubits k) ℂ)
    (w : Fin k ↪ Fin 2) : (QAlgorithms.embedOp M w).det = M.det ^ 2 := by
  subst hk; exact g66i_det_embed1' M w

lemma g66i_det_of1 (M : Matrix Bool Bool ℂ) : (QAlgorithms.Gate.ofMatrix1 M).mat.det = M.det :=
  Matrix.det_submatrix_equiv_self (Equiv.funUnique (Fin 1) Bool) M

def g66i_e2 : QAlgorithms.Qubits 2 ≃ Bool × Bool :=
  { toFun := fun b => (b 0, b 1), invFun := fun p => ![p.1, p.2],
    left_inv := fun b => by funext i; fin_cases i <;> rfl,
    right_inv := fun p => rfl }

lemma g66i_det_of2 (M : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    (QAlgorithms.Gate.ofMatrix2 M).mat.det = M.det :=
  Matrix.det_submatrix_equiv_self g66i_e2 M

lemma g66i_omega_pow8 : (QAlgorithms.gateT true true) ^ 8 = 1 := by
  have h := Complex.isPrimitiveRoot_exp 8 (by norm_num)
  have : QAlgorithms.gateT true true = Complex.exp (2 * Real.pi * Complex.I / (8 : ℕ)) := by
    simp only [QAlgorithms.gateT, Matrix.diagonal_apply_eq, if_true]
    congr 1; push_cast; ring
  rw [this]; exact h.pow_eq_one

lemma g66i_omega_pow4 : (QAlgorithms.gateT true true) ^ 4 = -1 := by
  have h := Complex.isPrimitiveRoot_exp 8 (by norm_num)
  have : QAlgorithms.gateT true true = Complex.exp (2 * Real.pi * Complex.I / (8 : ℕ)) := by
    simp only [QAlgorithms.gateT, Matrix.diagonal_apply_eq, if_true]
    congr 1; push_cast; ring
  rw [this]
  have h1 : (Complex.exp (2 * Real.pi * Complex.I / (8 : ℕ)) ^ 4) ^ 2 = 1 := by
    rw [← pow_mul]; exact h.pow_eq_one
  have h2 : Complex.exp (2 * Real.pi * Complex.I / (8 : ℕ)) ^ 4 ≠ 1 :=
    h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have h3 : (Complex.exp (2 * Real.pi * Complex.I / (8 : ℕ)) ^ 4 - 1) *
      (Complex.exp (2 * Real.pi * Complex.I / (8 : ℕ)) ^ 4 + 1) = 0 := by
    linear_combination h1
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact absurd (sub_eq_zero.mp h4) h2
  · linear_combination h4

lemma g66i_det_pow8 (M : Matrix Bool Bool ℂ) (h : M ^ 8 = 1) : M.det ^ 8 = 1 := by
  rw [← Matrix.det_pow, h, Matrix.det_one]

lemma g66i_gate_det (g : QAlgorithms.GateApp cliffordTLibrary 2) :
    (QAlgorithms.embedOp g.gate.mat g.wires).det ^ 4 = 1 := by
  obtain ⟨gate, mem, wires⟩ := g
  simp only [cliffordTLibrary, Set.mem_insert_iff, Set.mem_singleton_iff] at mem
  have one : ∀ M : Matrix Bool Bool ℂ, M ^ 8 = 1 → ∀ w : Fin (QAlgorithms.Gate.ofMatrix1 M).arity ↪ Fin 2,
      (QAlgorithms.embedOp (QAlgorithms.Gate.ofMatrix1 M).mat w).det ^ 4 = 1 := by
    intro M hM w
    have h := g66i_det_embed1 (k := (QAlgorithms.Gate.ofMatrix1 M).arity) rfl
      (QAlgorithms.Gate.ofMatrix1 M).mat w
    rw [h, g66i_det_of1, ← pow_mul]
    exact g66i_det_pow8 M hM
  rcases mem with rfl | rfl | rfl | rfl
  · apply one
    rw [show (8 : ℕ) = 2 * 4 by rfl, pow_mul, sq, QAlgorithms.hadamard_mul_self, one_pow]
  · apply one
    rw [QAlgorithms.phaseS, Matrix.diagonal_pow, ← Matrix.diagonal_one]
    congr 1; funext x; cases x <;> simp [show Complex.I ^ 8 = (Complex.I ^ 4) ^ 2 by ring]
  · apply one
    rw [QAlgorithms.gateT, Matrix.diagonal_pow, ← Matrix.diagonal_one]
    congr 1; funext x; cases x
    · simp
    · have := g66i_omega_pow8
      simpa [QAlgorithms.gateT] using this
  · show (QAlgorithms.embedOp (QAlgorithms.Gate.ofMatrix2 QAlgorithms.cnot).mat wires).det ^ 4 = 1
    have h := g66i_det_embed2 (k := (QAlgorithms.Gate.ofMatrix2 QAlgorithms.cnot).arity) rfl
      (QAlgorithms.Gate.ofMatrix2 QAlgorithms.cnot).mat wires
    rw [h, g66i_det_of2]
    have h2 : QAlgorithms.cnot * QAlgorithms.cnot = 1 := by
      ext ⟨a, b⟩ ⟨c, d⟩
      cases a <;> cases b <;> cases c <;> cases d <;>
        simp [QAlgorithms.cnot, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply]
    have : QAlgorithms.cnot.det ^ 2 = 1 := by rw [sq, ← Matrix.det_mul, h2, Matrix.det_one]
    rw [show (4:ℕ) = 2 * 2 by rfl, pow_mul, this, one_pow]

lemma g66i_list_det (L : List (Matrix (QAlgorithms.Qubits 2) (QAlgorithms.Qubits 2) ℂ))
    (h : ∀ M ∈ L, M.det ^ 4 = 1) : L.prod.det ^ 4 = 1 := by
  induction L with
  | nil => simp
  | cons M L ih =>
    rw [List.prod_cons, Matrix.det_mul, mul_pow, h M (by simp),
      ih (fun N hN => h N (by simp [hN])), one_mul]

lemma g66i_circ_det (c : QAlgorithms.Circuit cliffordTLibrary 2) : c.unitary.det ^ 4 = 1 := by
  unfold QAlgorithms.Circuit.unitary
  apply g66i_list_det
  intro M hM
  rw [List.mem_reverse, List.mem_map] at hM
  obtain ⟨g, -, rfl⟩ := hM
  exact g66i_gate_det g

lemma g66i_cT_diag : QAlgorithms.controlled QAlgorithms.gateT =
    Matrix.diagonal (fun p : Bool × Bool => if p = (true, true) then QAlgorithms.gateT true true else 1) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [QAlgorithms.controlled, QAlgorithms.gateT, Matrix.diagonal_apply]

lemma g66i_det_cT : controlledT.det = QAlgorithms.gateT true true := by
  have e : controlledT.det = (QAlgorithms.controlled QAlgorithms.gateT).det :=
    Matrix.det_submatrix_equiv_self g66i_e2 _
  rw [e, g66i_cT_diag, Matrix.det_diagonal, Fintype.prod_prod_type]
  simp [Fintype.prod_bool]

theorem solution (c : QAlgorithms.Circuit cliffordTLibrary 2) :
    c.unitary ≠ controlledT ∧
      ¬ ∃ a : ℂ, ‖a‖ = 1 ∧ c.unitary = a • controlledT := by
  constructor
  · intro h
    have hd := g66i_circ_det c
    rw [h, g66i_det_cT, g66i_omega_pow4] at hd
    norm_num at hd
  · rintro ⟨a, -, h⟩
    have hd := g66i_circ_det c
    rw [h, Matrix.det_smul, g66i_det_cT] at hd
    have hcard : Fintype.card (QAlgorithms.Qubits 2) = 4 := by simp
    rw [hcard] at hd
    have h16 : a ^ 16 = -1 := by
      have : a ^ 16 * (QAlgorithms.gateT true true) ^ 4 = 1 := by rw [← hd]; ring
      rw [g66i_omega_pow4] at this
      linear_combination -this
    have hmem := g66i_circ_mem c (fun _ => false) (fun _ => false)
    have hCT : controlledT (fun _ => false) (fun _ => false) = 1 := by
      unfold controlledT
      simp [QAlgorithms.Gate.ofMatrix2, QAlgorithms.controlled]
    rw [h, Matrix.smul_apply, hCT, smul_eq_mul, mul_one] at hmem
    have h32 : a ^ 32 = 1 := by
      rw [show (32:ℕ) = 16 * 2 by rfl, pow_mul, h16]; norm_num
    have hdvd : orderOf a ∣ 2 ^ 5 := orderOf_dvd_of_pow_eq_one (by simpa using h32)
    obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hi5 : i = 5 := by
      by_contra hne
      have : orderOf a ∣ 16 := by
        rw [hio, show (16:ℕ) = 2 ^ 4 by rfl]; exact Nat.pow_dvd_pow 2 (by omega)
      have := orderOf_dvd_iff_pow_eq_one.mp this
      rw [h16] at this; norm_num at this
    subst hi5
    have hp := IsPrimitiveRoot.orderOf a
    rw [hio] at hp
    have := g66i_prim_root_bound a hmem _ (by norm_num) hp
    rw [Nat.totient_prime_pow Nat.prime_two (by norm_num)] at this
    norm_num at this
