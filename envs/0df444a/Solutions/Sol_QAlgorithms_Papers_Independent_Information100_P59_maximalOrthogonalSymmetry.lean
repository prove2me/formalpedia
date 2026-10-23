-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P59.maximalOrthogonalSymmetry
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:13:42.28936+00:00
-- url     : https://prove2.me/submissions/53ff80d7-a3e7-486a-9487-5e6601ea59c8

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P59
noncomputable section
open scoped Matrix ComplexOrder

namespace X4P59
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P59

lemma jump_apply (a : Cvec) (i j : Bool) : jump a i j =
    a 0 * (if i = j then 0 else 1) + a 1 * (if i = j then 0 else if i then Complex.I else -Complex.I)
    + a 2 * (if i = j then (if i then -1 else 1) else 0) := by
  simp [jump, Fin.sum_univ_three, QubitChannels.sigma, pauliX, pauliY, pauliZ, Matrix.sum_apply,
    Matrix.diagonal_apply]


set_option maxHeartbeats 1000000 in
lemma opB (a : Cvec) (i : Fin 3) : operatorB a i =
    4 * ((a (i + 1)).re * (a (i + 2)).im - (a (i + 2)).re * (a (i + 1)).im) := by
  fin_cases i <;>
  simp [operatorB, dissipator, QubitChannels.sigma, Matrix.trace, Fintype.sum_bool, Matrix.mul_apply,
    jump_apply, pauliX, pauliY, pauliZ, Matrix.conjTranspose_apply, Matrix.diagonal_apply] <;> ring_nf

set_option maxHeartbeats 1000000 in
lemma opQ (a : Cvec) (i j : Fin 3) : operatorQ a i j =
    2 * ((a i).re * (a j).re + (a i).im * (a j).im) - (if i = j then 2 * amplitudeSq a else 0) := by
  fin_cases i <;> fin_cases j <;>
  simp [operatorQ, dissipator, QubitChannels.sigma, Matrix.trace, Fintype.sum_bool, Matrix.mul_apply,
    jump_apply, pauliX, pauliY, pauliZ, Matrix.conjTranspose_apply, Matrix.diagonal_apply, amplitudeSq,
    Fin.sum_univ_three, Complex.normSq_apply] <;> ring_nf


/-! ### affine blocks -/

def abHom : (Mat × Vec) →+ Block where
  toFun p := affineBlock p.1 p.2
  map_zero' := by ext i j; simp [affineBlock]
  map_add' p q := by
    ext i j; simp only [affineBlock, Matrix.add_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    split_ifs <;> simp

lemma ab_inj {Q Q' : Mat} {b b' : Vec} (h : affineBlock Q b = affineBlock Q' b') : Q = Q' ∧ b = b' := by
  constructor
  · ext i j
    have := congrFun (congrFun h ⟨i.val, by omega⟩) ⟨j.val, by omega⟩
    simpa [affineBlock] using this
  · ext i
    have := congrFun (congrFun h ⟨i.val, by omega⟩) 3
    simpa [affineBlock] using this

def chQB (a : Cvec) : Mat × Vec := (operatorQ a, operatorB a)

lemma gkls_iff (X : Block) : IsGKLS X ↔ ∃ (n : Vec) (k : ℕ) (a : Fin k → Cvec),
    X = affineBlock (rotationGenerator n + ∑ j, operatorQ (a j)) (∑ j, operatorB (a j)) := by
  have key : ∀ (n : Vec) (k : ℕ) (a : Fin k → Cvec), controlBlock n + ∑ j, channelBlock (a j) =
      affineBlock (rotationGenerator n + ∑ j, operatorQ (a j)) (∑ j, operatorB (a j)) := by
    intro n k a
    have h1 : ∑ j, channelBlock (a j) = abHom (∑ j, chQB (a j)) := by
      rw [map_sum]; rfl
    have h2 : affineBlock (rotationGenerator n + ∑ j, operatorQ (a j)) (∑ j, operatorB (a j)) =
        abHom ((rotationGenerator n, 0) + ∑ j, chQB (a j)) := by
      simp [abHom, chQB, Prod.fst_sum, Prod.snd_sum]
    rw [h1, h2, map_add]; rfl
  unfold IsGKLS
  simp only [key]

lemma ampl_nonneg (a : Cvec) : 0 ≤ amplitudeSq a :=
  Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _

lemma tr_opQ (a : Cvec) : Matrix.trace (operatorQ a) = -4 * amplitudeSq a := by
  simp only [Matrix.trace, Matrix.diag, opQ, Fin.sum_univ_three]
  simp [amplitudeSq, Fin.sum_univ_three, Complex.normSq_apply]; ring

lemma tr_rot (n : Vec) : Matrix.trace (rotationGenerator n) = 0 := by
  simp [Matrix.trace, rotationGenerator, Fin.sum_univ_three]

lemma rot_transpose (n : Vec) : (rotationGenerator n)ᵀ = -rotationGenerator n := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotationGenerator]

local notation "E" v => (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3))

lemma normE_sq (v : Vec) : ‖E v‖ = Real.sqrt (∑ i, v i ^ 2) := by
  rw [EuclideanSpace.norm_eq]; simp

lemma norm_opB (a : Cvec) : ‖E (operatorB a)‖ ≤ 2 * amplitudeSq a := by
  rw [normE_sq, Real.sqrt_le_iff]
  refine ⟨by linarith [ampl_nonneg a], ?_⟩
  simp only [Fin.sum_univ_three, opB, amplitudeSq, Complex.normSq_apply]
  simp
  set x0 := (a 0).re; set x1 := (a 1).re; set x2 := (a 2).re
  set y0 := (a 0).im; set y1 := (a 1).im; set y2 := (a 2).im
  nlinarith [sq_nonneg (x0*y0 + x1*y1 + x2*y2), sq_nonneg (x0^2+x1^2+x2^2 - y0^2-y1^2-y2^2)]

lemma norm_sum_le' {k : ℕ} (f : Fin k → Vec) : ‖E (∑ j, f j)‖ ≤ ∑ j, ‖E (f j)‖ := by
  have : (E (∑ j, f j)) = ∑ j, E (f j) := by
    ext i; simp
  rw [this]; exact norm_sum_le _ _

lemma inv (n : Vec) (k : ℕ) (a : Fin k → Cvec) :
    ‖E (∑ j, operatorB (a j))‖ ≤ -Matrix.trace (rotationGenerator n + ∑ j, operatorQ (a j)) / 2 := by
  rw [Matrix.trace_add, tr_rot, Matrix.trace_sum]
  simp only [tr_opQ]
  calc _ ≤ ∑ j, ‖E (operatorB (a j))‖ := norm_sum_le' _
    _ ≤ ∑ j, 2 * amplitudeSq (a j) := Finset.sum_le_sum fun j _ => norm_opB _
    _ = _ := by rw [zero_add, ← Finset.mul_sum, ← Finset.mul_sum]; ring

end X4P59

noncomputable section
open scoped Matrix ComplexOrder

namespace X4P59
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P59

set_option maxHeartbeats 2000000 in
lemma conj_ab (T Q : Mat) (b : Vec) :
    blochConjugate T (affineBlock Q b) = affineBlock (T * Q * T⁻¹) (T *ᵥ b) := by
  ext i j
  simp only [blochConjugate, coordinateChange, Matrix.mul_apply, Fin.sum_univ_four, Matrix.add_apply,
    Matrix.single_apply]
  fin_cases i <;> fin_cases j <;>
    simp [affineBlock, Matrix.mul_apply, Fin.sum_univ_three, Matrix.mulVec, dotProduct] <;> ring

lemma rot_neg (n : Vec) : rotationGenerator (-n) = -rotationGenerator n := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotationGenerator]

lemma ctrl_gkls (n : Vec) : IsGKLS (affineBlock (rotationGenerator n) 0) := by
  rw [gkls_iff]; exact ⟨n, 0, Fin.elim0, by simp⟩

lemma ampl_zero {a : Cvec} (h : amplitudeSq a = 0) : operatorQ a = 0 ∧ operatorB a = 0 := by
  have hi : ∀ i, a i = 0 := by
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (a i))).mp h i
      (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.mp this
  constructor
  · ext i j; rw [opQ, h]; simp [hi]
  · ext i; rw [opB]; simp [hi]

/-- lineality: a cone element whose negative is also in the cone has skew linear part -/
lemma lineal (Q : Mat) (b : Vec) (h1 : IsGKLS (affineBlock Q b)) (h2 : IsGKLS (-affineBlock Q b)) :
    ∃ n, Q = rotationGenerator n := by
  rw [gkls_iff] at h1 h2
  obtain ⟨n, k, a, ha⟩ := h1
  obtain ⟨n', k', a', ha'⟩ := h2
  have hneg : -affineBlock Q b = affineBlock (-Q) (-b) := by
    ext i j; simp only [affineBlock, Matrix.neg_apply]; split_ifs <;> simp
  rw [hneg] at ha'
  obtain ⟨hQ, -⟩ := ab_inj ha
  obtain ⟨hQ', -⟩ := ab_inj ha'
  have t1 := congrArg Matrix.trace hQ
  have t2 := congrArg Matrix.trace hQ'
  rw [Matrix.trace_add, tr_rot, Matrix.trace_sum] at t1 t2
  simp only [tr_opQ, Matrix.trace_neg] at t1 t2
  have s1 : 0 ≤ ∑ j, amplitudeSq (a j) := Finset.sum_nonneg fun j _ => ampl_nonneg _
  have s2 : 0 ≤ ∑ j, amplitudeSq (a' j) := Finset.sum_nonneg fun j _ => ampl_nonneg _
  rw [← Finset.mul_sum] at t1 t2
  have z : ∑ j, amplitudeSq (a j) = 0 := by linarith
  have zj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => ampl_nonneg (a j))).mp z
  refine ⟨n, ?_⟩
  rw [hQ]
  simp [fun j => (ampl_zero (zj j (Finset.mem_univ _))).1]

end X4P59

noncomputable section
open scoped Matrix ComplexOrder

namespace X4P59
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P59

lemma cone_bound {Q : Mat} {b : Vec} (h : IsGKLS (affineBlock Q b)) :
    Real.sqrt (∑ i, b i ^ 2) ≤ -Matrix.trace Q / 2 := by
  rw [gkls_iff] at h
  obtain ⟨n, k, a, ha⟩ := h
  obtain ⟨hQ, hb⟩ := ab_inj ha
  rw [hQ, hb, ← normE_sq]
  exact inv n k a

lemma trace_conj (T Q : Mat) (hT : T.det ≠ 0) : Matrix.trace (T * Q * T⁻¹) = Matrix.trace Q := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul T (isUnit_iff_ne_zero.mpr hT),
    Matrix.one_mul]

lemma quad (T : Mat) (c : ℝ) (hS : T.transpose * T = c • 1) (v : Vec) :
    ∑ i, (T *ᵥ v) i ^ 2 = c * ∑ i, v i ^ 2 := by
  have h1 : ∑ i, (T *ᵥ v) i ^ 2 = (T *ᵥ v) ⬝ᵥ (T *ᵥ v) := by simp [dotProduct, sq]
  have h2 : ∑ i, v i ^ 2 = v ⬝ᵥ v := by simp [dotProduct, sq]
  rw [h1, h2]
  conv_lhs => arg 1; rw [← Matrix.vecMul_transpose]
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hS,
    Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]

lemma damp_eq : dampingBlock = affineBlock (Matrix.diagonal ![-(1/2 : ℝ), -(1/2 : ℝ), -1]) ![0, 0, -1] := rfl

lemma damp_gkls : IsGKLS dampingBlock := by
  rw [gkls_iff]
  refine ⟨0, 1, fun _ => ![(1/2 : ℂ), -(Complex.I / 2), 0], ?_⟩
  rw [damp_eq]
  congr 1
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [opQ, rotationGenerator, amplitudeSq, Fin.sum_univ_three, Complex.normSq_apply] <;> norm_num
  · ext i
    fin_cases i <;> simp [opB] <;> norm_num

lemma neg_ab (Q : Mat) : affineBlock (-Q) 0 = -affineBlock Q 0 := by
  ext i j; simp only [affineBlock, Matrix.neg_apply]; split_ifs <;> simp

lemma comm_scalar (S : Mat) (h : ∀ n : Vec, S * rotationGenerator n = rotationGenerator n * S) :
    S = S 0 0 • 1 := by
  have h0 := h ![1, 0, 0]
  have h1 := h ![0, 1, 0]
  have h2 := h ![0, 0, 1]
  simp only [← Matrix.ext_iff, Fin.forall_fin_succ, Matrix.mul_apply, Fin.sum_univ_three,
    rotationGenerator] at h0 h1 h2
  simp at h0 h1 h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> linarith [h0, h1, h2]

theorem part1 (T : Mat) (hT : T.det ≠ 0)
    (himg : blochConjugate T '' {X : Block | IsGKLS X} = {X : Block | IsGKLS X}) :
    T.transpose * T = 1 := by
  have hU : IsUnit T.det := isUnit_iff_ne_zero.mpr hT
  have hTi : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul T hU
  have inC : ∀ X, IsGKLS X → IsGKLS (blochConjugate T X) := by
    intro X hX
    have : blochConjugate T X ∈ blochConjugate T '' {X : Block | IsGKLS X} := Set.mem_image_of_mem _ hX
    rw [himg] at this; exact this
  set S := T.transpose * T with hSdef
  -- S commutes with every rotation generator
  have hcomm : ∀ n : Vec, S * rotationGenerator n = rotationGenerator n * S := by
    intro n
    have a1 := inC _ (ctrl_gkls n)
    have a2 := inC _ (ctrl_gkls (-n))
    rw [conj_ab, Matrix.mulVec_zero] at a1 a2
    rw [rot_neg, Matrix.mul_neg, Matrix.neg_mul, neg_ab] at a2
    obtain ⟨m, hm⟩ := lineal _ 0 a1 a2
    have hskew : (T * rotationGenerator n * T⁻¹).transpose = -(T * rotationGenerator n * T⁻¹) := by
      rw [hm, rot_transpose]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, rot_transpose] at hskew
    have e := congrArg (fun M => T.transpose * M * T) hskew
    have l1 : T.transpose * (T⁻¹.transpose * (-rotationGenerator n * T.transpose)) * T =
        -(rotationGenerator n * S) := by
      rw [hSdef, ← Matrix.mul_assoc, ← Matrix.transpose_mul, hTi, Matrix.transpose_one, Matrix.one_mul]
      simp [Matrix.mul_assoc]
    have l2 : T.transpose * -(T * rotationGenerator n * T⁻¹) * T = -(S * rotationGenerator n) := by
      rw [hSdef]; simp [Matrix.mul_assoc, hTi]
    rw [l1, l2] at e
    exact (neg_inj.mp e).symm
  have hS := comm_scalar S hcomm
  set c := S 0 0
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hS
    have := congrArg Matrix.det hS
    rw [hSdef, Matrix.det_mul, Matrix.det_transpose, Matrix.det_zero] at this
    exact hT (mul_self_eq_zero.mp this)
  have hcpos : 0 < c := by
    have : 0 ≤ c := by
      show 0 ≤ (T.transpose * T) 0 0
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
      exact Finset.sum_nonneg fun k _ => mul_self_nonneg _
    exact lt_of_le_of_ne this (Ne.symm hc0)
  have hd : Matrix.trace (Matrix.diagonal ![-(1/2 : ℝ), -(1/2 : ℝ), -1]) = -2 := by
    simp [Matrix.trace, Fin.sum_univ_three]; norm_num
  have hbd : ∑ i, (![0, 0, -1] : Vec) i ^ 2 = 1 := by simp [Fin.sum_univ_three]
  rcases lt_trichotomy c 1 with hlt | heq | hgt
  · -- the damping block must have a preimage in the cone
    have : dampingBlock ∈ blochConjugate T '' {X : Block | IsGKLS X} := by rw [himg]; exact damp_gkls
    obtain ⟨Y, hY, hYe⟩ := this
    have hY' := hY
    simp only [Set.mem_setOf_eq] at hY'
    rw [gkls_iff] at hY'
    obtain ⟨n, k, a, rfl⟩ := hY'
    rw [conj_ab, damp_eq] at hYe
    obtain ⟨hQ, hb⟩ := ab_inj hYe
    have hb2 := quad T c hS (∑ j, operatorB (a j))
    rw [hb, hbd] at hb2
    have htr := trace_conj T (rotationGenerator n + ∑ j, operatorQ (a j)) hT
    rw [hQ, hd] at htr
    have hcb := cone_bound (show IsGKLS _ from hY)
    rw [← htr] at hcb
    have hs1 : Real.sqrt (∑ i, (∑ j, operatorB (a j)) i ^ 2) ≤ 1 := by linarith
    rw [Real.sqrt_le_one] at hs1
    nlinarith
  · rw [hS, heq, one_smul]
  · have h := inC _ damp_gkls
    rw [damp_eq, conj_ab] at h
    have hcb := cone_bound h
    rw [trace_conj T _ hT, hd, quad T c hS, hbd, mul_one] at hcb
    have : 1 < Real.sqrt c := by rw [Real.lt_sqrt zero_le_one]; linarith
    linarith

lemma two_eq : (2 • (1 : Mat)) = (2:ℝ) • (1:Mat) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]

theorem part2 : ¬ IsGKLS (blochConjugate (2 • (1 : Mat)) dampingBlock) := by
  intro h
  rw [two_eq, damp_eq, conj_ab] at h
  have hdet : ((2:ℝ) • (1 : Mat)).det ≠ 0 := by
    rw [Matrix.det_smul]; simp
  have hS : ((2:ℝ) • (1 : Mat)).transpose * ((2:ℝ) • (1 : Mat)) = (4 : ℝ) • 1 := by
    rw [Matrix.transpose_smul, Matrix.transpose_one, smul_mul_smul_comm, Matrix.one_mul]
    norm_num
  have hcb := cone_bound h
  rw [trace_conj _ _ hdet, quad _ 4 hS] at hcb
  have hd : Matrix.trace (Matrix.diagonal ![-(1/2 : ℝ), -(1/2 : ℝ), -1]) = -2 := by
    simp [Matrix.trace, Fin.sum_univ_three]; norm_num
  have hbd : ∑ i, (![0, 0, -1] : Vec) i ^ 2 = 1 := by simp [Fin.sum_univ_three]
  rw [hd, hbd] at hcb
  have : (2 : ℝ) = Real.sqrt (4 * 1) := by
    rw [mul_one, show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
  linarith

end X4P59

section
open QAlgorithms.Papers.Independent.Information100.P59
attribute [local instance 100] LieRing.ofAssociativeRing

theorem solution (T : QAlgorithms.Papers.Independent.Information100.P59.Mat) (hT : T.det ≠ 0) :
    ((blochConjugate T '' {X : Block | IsGKLS X}) = {X : Block | IsGKLS X} →
      T.transpose * T = 1) ∧
    ¬ IsGKLS (blochConjugate (2 • (1 : QAlgorithms.Papers.Independent.Information100.P59.Mat)) dampingBlock) :=
  ⟨X4P59.part1 T hT, X4P59.part2⟩

end
