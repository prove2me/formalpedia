-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P03.lemma9_pauliShadow
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:58:55.703373+00:00
-- url     : https://prove2.me/submissions/97d2ba38-6185-4c3f-866b-216c13005668

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate ComplexOrder

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace


lemma g58a_nwt_mul {I : Type*} [Fintype I] [DecidableEq I] (A B : I → Matrix Bool Bool ℂ) :
    namedWireTensor A * namedWireTensor B = namedWireTensor (fun i => A i * B i) := by
  ext x y
  simp only [Matrix.mul_apply, namedWireTensor]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.prod_mul_distrib]

lemma g58a_nwt_trace {I : Type*} [Fintype I] [DecidableEq I] (A : I → Matrix Bool Bool ℂ) :
    (namedWireTensor A).trace = ∏ i, (A i).trace := by
  simp only [Matrix.trace, Matrix.diag, namedWireTensor]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

lemma g58a_nwt_sum {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    (g : I → X → ℂ) (F : I → X → Matrix Bool Bool ℂ) :
    ∑ s : I → X, (∏ i, g i (s i)) • namedWireTensor (fun i => F i (s i)) =
      namedWireTensor (fun i => ∑ x, g i x • F i x) := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, namedWireTensor]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← Finset.prod_mul_distrib]

lemma g58a_nwt_scal {I : Type*} [Fintype I] [DecidableEq I] (c : I → ℂ) :
    namedWireTensor (fun i => c i • (1 : Matrix Bool Bool ℂ)) =
      (∏ i, c i) • (1 : Matrix (I → Bool) (I → Bool) ℂ) := by
  ext a b
  simp only [namedWireTensor, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- per-wire snapshot value -/
def g58a_f (p : Fin 4) (x : Fin 3 × Bool) : ℝ :=
  if p = 0 then 1 else if p.val = x.1.val + 1 then 3 * rademacherValue x.2 else 0

def g58a_g (p : Fin 4) (x : Fin 3 × Bool) : ℝ :=
  if p = 0 then 1 else if p.val = x.1.val + 1 then 9 else 0

def g58a_snap1 (x : Fin 3 × Bool) : Matrix Bool Bool ℂ :=
  (2⁻¹ : ℂ) • (1 + (if (!x.2) then (3 : ℂ) else -3) •
    (if x.1 = 0 then GroundStateLearning.Axis.X
     else if x.1 = 1 then GroundStateLearning.Axis.Y
     else GroundStateLearning.Axis.Z).mat)

lemma g58a_snap_eq {n : ℕ} (s : Shot n) :
    pauliSnapshot s = namedWireTensor (fun i => g58a_snap1 (s i)) := by
  ext x y; rfl

lemma g58a_wire_trace (p : Fin 4) (x : Fin 3 × Bool) :
    (singlePauli p * g58a_snap1 x).trace = (g58a_f p x : ℂ) := by
  obtain ⟨a, b⟩ := x
  fin_cases p <;> fin_cases a <;> cases b <;>
    simp [g58a_f, g58a_snap1, singlePauli, GroundStateLearning.Axis.mat, pauliX, pauliY, pauliZ,
      Matrix.trace, Fintype.sum_bool, Matrix.mul_apply, rademacherValue] <;> ring_nf <;>
    simp [Complex.I_sq] <;> norm_num

lemma g58a_wire_sum (p : Fin 4) :
    ∑ x : Fin 3 × Bool, ((g58a_g p x : ℝ) : ℂ) • shotProjector x =
      ((if p = 0 then (3 : ℝ) else 9 : ℝ) : ℂ) • (1 : Matrix Bool Bool ℂ) := by
  ext i j
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fintype.sum_bool, Matrix.add_apply,
    Matrix.sum_apply, Matrix.smul_apply]
  fin_cases p <;> cases i <;> cases j <;>
    simp [g58a_g, shotProjector, singlePauli, pauliX, pauliY, pauliZ, rademacherValue] <;> ring_nf

lemma g58a_main {n : ℕ} (P : Fin n → Fin 4) (rho : Matrix (Qubits n) (Qubits n) ℂ)
    (hrho : IsDensityMatrix rho) :
    ∑ s : Shot n, shotWeight rho s * effectProb (wordMatrix P) (pauliSnapshot s) ^ 2 =
      (3 : ℝ) ^ pauliWeight P := by
  have hval : ∀ s : Shot n, effectProb (wordMatrix P) (pauliSnapshot s) ^ 2 =
      ∏ i, g58a_g (P i) (s i) := by
    intro s
    unfold effectProb wordMatrix
    rw [g58a_snap_eq, g58a_nwt_mul, g58a_nwt_trace]
    simp only [g58a_wire_trace]
    rw [← Complex.ofReal_prod, Complex.ofReal_re, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [g58a_f, g58a_g]
    split_ifs <;> simp [rademacherValue] <;> (try split_ifs) <;> norm_num
  simp only [hval]
  simp only [shotWeight, effectProb]
  have : ∀ s : Shot n, (namedWireTensor (fun i => shotProjector (s i)) * rho).trace.re / 3 ^ n *
      ∏ i, g58a_g (P i) (s i) =
      (((∏ i, ((g58a_g (P i) (s i) : ℝ) : ℂ)) • namedWireTensor (fun i => shotProjector (s i))) *
        rho).trace.re / 3 ^ n := by
    intro s
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← Complex.ofReal_prod, Complex.re_ofReal_mul]
    ring
  simp only [this]
  rw [← Finset.sum_div, ← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul,
    g58a_nwt_sum (fun i x => ((g58a_g (P i) x : ℝ) : ℂ)) (fun _ x => shotProjector x)]
  simp only [g58a_wire_sum]
  rw [g58a_nwt_scal, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, hrho.2, smul_eq_mul, mul_one,
    ← Complex.ofReal_prod, Complex.ofReal_re]
  rw [div_eq_iff (by positivity)]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have hc : (Finset.univ.filter fun i => P i = 0).card + pauliWeight P = n := by
    unfold pauliWeight wordSupport
    rw [Finset.card_filter_add_card_filter_not]; simp
  have hw : (Finset.univ.filter fun i => ¬ P i = 0).card = pauliWeight P := rfl
  rw [hw]
  have h3 : (3 : ℝ) ^ n = 3 ^ (Finset.univ.filter fun i => P i = 0).card * 3 ^ pauliWeight P := by
    rw [← pow_add, hc]
  rw [h3, show (9 : ℝ) = 3 * 3 by norm_num, mul_pow]
  ring

theorem solution (n : ℕ) (P : (Fin n → Fin 4)) :
    localPauliShadowNorm (wordMatrix P) = Real.rpow 3 ((pauliWeight P : ℝ) / 2) := by
  have hd0 : IsDensityMatrix (Matrix.single (fun _ : Fin n => false) (fun _ => false) (1 : ℂ)) := by
    refine ⟨?_, by simp⟩
    have := Matrix.posSemidef_vecMulVec_self_star (Pi.single (fun _ : Fin n => false) (1 : ℂ))
    convert this using 1
    ext i j
    simp only [Matrix.vecMulVec_apply, Matrix.single_apply, Pi.single_apply, Pi.star_apply]
    by_cases hi : i = (fun _ => false) <;> by_cases hj : j = (fun _ => false) <;>
      simp [hi, hj, eq_comm]
  have hset : {v : ℝ | ∃ rho : (Matrix (Qubits n) (Qubits n) ℂ), IsDensityMatrix rho ∧
      v = Real.sqrt (∑ s : Shot n, shotWeight rho s * effectProb (wordMatrix P) (pauliSnapshot s) ^ 2)} =
      {Real.sqrt ((3 : ℝ) ^ pauliWeight P)} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨rho, hrho, rfl⟩; rw [g58a_main P rho hrho]
    · rintro rfl
      exact ⟨_, hd0, by rw [g58a_main P _ hd0]⟩
  unfold localPauliShadowNorm
  rw [hset, csSup_singleton, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  ring

end
