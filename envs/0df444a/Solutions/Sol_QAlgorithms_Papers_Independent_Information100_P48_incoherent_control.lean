-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P48.incoherent_control
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T03:40:14.9054+00:00
-- url     : https://prove2.me/submissions/1323637d-1b90-47f7-aaa4-404cca636dd7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P48

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P48

open scoped Matrix ComplexConjugate

noncomputable section
lemma g53e_joint {E : Type*} [Fintype E] [DecidableEq E] (U V : Matrix (Bool × E) (Bool × E) ℂ) (e : E)
    (rho : QOp) (c c' s t : Bool) :
    jointCS ((1 / 2 : ℂ) • (1 : QOp)) U V e rho (c, s) (c', t) =
      if c = c' then (1 / 2 : ℂ) * (if c then cross V V e rho s t else cross U U e rho s t) else 0 := by
  unfold jointCS cross traceEnv
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    controlledPair, Fintype.sum_prod_type, Fintype.sum_bool, Matrix.smul_apply, Matrix.one_apply]
  cases c <;> cases c' <;> simp [Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm] <;>
    simp only [Finset.mul_sum, Finset.sum_mul, add_mul, mul_add, Finset.sum_add_distrib, mul_assoc]

lemma g53e_select (A B : QOp) (R : QQOp)
    (hR : ∀ c c' s t, R (c, s) (c', t) = if c = c' then (1 / 2 : ℂ) * (if c then B s t else A s t) else 0)
    (minus : Bool) : selectControl R minus = (1 / 4 : ℂ) • (A + B) := by
  ext s t
  have hk : ∀ x y, Matrix.kronecker (hadamardProjector minus) (1 : QOp) x y =
      hadamardProjector minus x.1 y.1 * (1 : QOp) x.2 y.2 := fun _ _ => rfl
  unfold selectControl traceLeft
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, hk,
    Fintype.sum_prod_type, Fintype.sum_bool, hR, Matrix.smul_apply, Matrix.add_apply]
  unfold hadamardProjector
  cases minus <;> cases s <;> cases t <;> simp [outcomeSign, Matrix.one_apply] <;> ring

lemma g53e_cross_gen {E : Type*} [Fintype E] [DecidableEq E] (U V : Matrix (Bool × E) (Bool × E) ℂ)
    (e : E) (rho : QOp) (s t : Bool) :
    cross U V e rho s t = ∑ f, ∑ a, ∑ b, U (s, f) (a, e) * rho a b * conj (V (t, f) (b, e)) := by
  unfold cross traceEnv cleanInput
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.single_apply]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp [ite_and, Finset.sum_mul, Finset.mul_sum, Finset.sum_ite_eq', Finset.sum_ite_eq, mul_assoc, Fintype.sum_bool]
  ring

lemma g53e_dil_apply (g : ℝ) (a x b y : Bool) :
    dilation g (a, x) (b, y) =
      if a = b ∧ x = y then (if a = x then 1 else (Real.cos (principalAngle g) : ℂ))
      else if a = false ∧ x = true ∧ b = true ∧ y = false then (Real.sin (principalAngle g) : ℂ)
      else if a = true ∧ x = false ∧ b = false ∧ y = true then -(Real.sin (principalAngle g) : ℂ)
      else 0 := by
  cases a <;> cases x <;> cases b <;> cases y <;> rfl

lemma g53e_trig (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    Real.sin (principalAngle g) = Real.sqrt g ∧ Real.cos (principalAngle g) = Real.sqrt (1 - g) := by
  unfold principalAngle
  refine ⟨Real.sin_arcsin (by linarith [Real.sqrt_nonneg g]) (Real.sqrt_le_one.mpr hg1), ?_⟩
  rw [Real.cos_arcsin, Real.sq_sqrt hg0]

lemma g53e_cross_dil (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (rho : QOp) :
    cross (dilation g) (dilation g) false rho = adc g rho := by
  obtain ⟨hs, hc⟩ := g53e_trig g hg0 hg1
  ext s t
  rw [g53e_cross_gen]
  simp only [g53e_dil_apply, hs, hc, Fintype.sum_bool]
  have hk1 : ∀ a b, k1 g a b = if a = false ∧ b = true then (Real.sqrt g : ℂ) else 0 := fun _ _ => rfl
  unfold adc
  cases s <;> cases t <;> simp [Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal_apply, hk1, k0,
    Matrix.conjTranspose_apply]
  all_goals ring

lemma g53e_cross_dilH (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (rho : QOp) :
    cross (dilation g)ᴴ (dilation g)ᴴ false rho = adc g rho := by
  obtain ⟨hs, hc⟩ := g53e_trig g hg0 hg1
  ext s t
  rw [g53e_cross_gen]
  simp only [Matrix.conjTranspose_apply, g53e_dil_apply, hs, hc, Fintype.sum_bool]
  have hk1 : ∀ a b, k1 g a b = if a = false ∧ b = true then (Real.sqrt g : ℂ) else 0 := fun _ _ => rfl
  unfold adc
  cases s <;> cases t <;> simp [Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal_apply, hk1, k0,
    Matrix.conjTranspose_apply]
  all_goals ring

lemma g53e_cross_e0 (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (rho : QOp) :
    cross (embed0 (E1 := Bool) (dilation g)) (embed0 (E1 := Bool) (dilation g)) (false, false) rho = adc g rho := by
  ext s t
  rw [g53e_cross_gen, ← g53e_cross_dil g hg0 hg1 rho, g53e_cross_gen]
  simp only [embed0, Fintype.sum_prod_type, Fintype.sum_bool]
  simp

lemma g53e_cross_e1 (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (rho : QOp) :
    cross (embed1 (E0 := Bool) (dilation g)) (embed1 (E0 := Bool) (dilation g)) (false, false) rho = adc g rho := by
  ext s t
  rw [g53e_cross_gen, ← g53e_cross_dil g hg0 hg1 rho, g53e_cross_gen]
  simp only [embed1, Fintype.sum_prod_type, Fintype.sum_bool]
  simp

lemma g53e_indep (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (minus : Bool) (rho : QOp) :
    incoherentIndependent g minus rho = (1 / 2 : ℂ) • adc g rho := by
  unfold incoherentIndependent
  rw [g53e_select (adc g rho) (adc g rho) _ (fun c c' s t => by
    rw [g53e_joint, g53e_cross_e0 g hg0 hg1, g53e_cross_e1 g hg0 hg1])]
  rw [← two_smul ℂ (adc g rho), smul_smul]; norm_num

lemma g53e_shared (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (minus : Bool) (rho : QOp) :
    incoherentShared g minus rho = (1 / 2 : ℂ) • adc g rho := by
  unfold incoherentShared
  rw [g53e_select (adc g rho) (adc g rho) _ (fun c c' s t => by
    rw [g53e_joint, g53e_cross_dil g hg0 hg1, g53e_cross_dilH g hg0 hg1])]
  rw [← two_smul ℂ (adc g rho), smul_smul]; norm_num

lemma g53e_adc_apply (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (rho : QOp) (s t : Bool) :
    adc g rho s t =
      if s = false ∧ t = false then rho false false + (g : ℂ) * rho true true
      else if s = true ∧ t = true then ((1 - g : ℝ) : ℂ) * rho true true
      else (Real.sqrt (1 - g) : ℂ) * rho s t := by
  have hk1 : ∀ a b, k1 g a b = if a = false ∧ b = true then (Real.sqrt g : ℂ) else 0 := fun _ _ => rfl
  have e1 : (Real.sqrt g : ℂ) ^ 2 = g := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hg0]
  have e2 : (Real.sqrt (1 - g) : ℂ) ^ 2 = 1 - (g : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]; push_cast; ring
  unfold adc
  cases s <;> cases t <;> simp [Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal_apply, hk1, k0,
    Matrix.conjTranspose_apply] <;> ring_nf <;> simp only [e1, e2] <;> ring

lemma g53e_temporal (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    temporal (fun rho => (1 / 2 : ℂ) • adc g rho) = 2 * Real.sqrt (2 * (1 - g)) := by
  unfold temporal correlator conditionalJoint rawJoint success projector mixedQubit
  simp only [Matrix.smul_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_bool, g53e_adc_apply g hg0 hg1,
    Matrix.add_apply, Matrix.one_apply, pauliX, pauliY, Matrix.of_apply, Matrix.sub_apply]
  simp [outcomeSign]
  have hD : (2⁻¹ * ((1 - g) * 2⁻¹) + 2⁻¹ * (2⁻¹ + g * 2⁻¹) : ℝ) = 2⁻¹ := by ring
  rw [hD]
  ring

lemma g53e_tr (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (rho : QOp) (h : IsDensityMatrix rho) :
    ((1 / 2 : ℂ) • adc g rho).trace.re = 1 / 2 ∧ P48.normalize ((1 / 2 : ℂ) • adc g rho) = adc g rho := by
  have ht : (adc g rho).trace = 1 := by
    rw [← h.2]
    simp only [Matrix.trace, Matrix.diag, Fintype.sum_bool, g53e_adc_apply g hg0 hg1]
    simp; push_cast; ring
  have h1 : ((1 / 2 : ℂ) • adc g rho).trace.re = 1 / 2 := by
    rw [Matrix.trace_smul, ht]; norm_num
  refine ⟨h1, ?_⟩
  unfold P48.normalize
  rw [h1, smul_smul]; norm_num

lemma g53e_iff (g : ℝ) : 2 < 2 * Real.sqrt (2 * (1 - g)) ↔ g < 1 / 2 := by
  constructor
  · intro h
    have : 1 < Real.sqrt (2 * (1 - g)) := by linarith
    rw [Real.lt_sqrt (by norm_num)] at this
    linarith
  · intro h
    have : 1 < Real.sqrt (2 * (1 - g)) := by
      rw [Real.lt_sqrt (by norm_num)]; linarith
    linarith

/-- §III A–B, PDF pp.5,6,8: either incoherent outcome is half the deterministic
ADC, with success 1/2 on every density input and unchanged temporal threshold. -/
theorem solution (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    (∀ (rho : QOp) (minus : Bool),
      incoherentIndependent g minus rho = (1 / 2 : ℂ) • adc g rho ∧
      incoherentShared g minus rho = (1 / 2 : ℂ) • adc g rho) ∧
    (∀ rho : QOp, IsDensityMatrix rho → ∀ minus : Bool,
      (incoherentIndependent g minus rho).trace.re = 1 / 2 ∧
      (incoherentShared g minus rho).trace.re = 1 / 2 ∧
      normalize (incoherentIndependent g minus rho) = adc g rho ∧
      normalize (incoherentShared g minus rho) = adc g rho) ∧
    (∀ minus : Bool,
      temporal (incoherentIndependent g minus) = 2 * Real.sqrt (2 * (1 - g)) ∧
      temporal (incoherentShared g minus) = 2 * Real.sqrt (2 * (1 - g)) ∧
      (2 < temporal (incoherentIndependent g minus) ↔ g < 1 / 2) ∧
      (2 < temporal (incoherentShared g minus) ↔ g < 1 / 2)) := by
  have hI : ∀ minus, incoherentIndependent g minus = fun rho => (1 / 2 : ℂ) • adc g rho :=
    fun minus => funext (g53e_indep g hg0 hg1 minus)
  have hS : ∀ minus, incoherentShared g minus = fun rho => (1 / 2 : ℂ) • adc g rho :=
    fun minus => funext (g53e_shared g hg0 hg1 minus)
  refine ⟨fun rho minus => ⟨g53e_indep g hg0 hg1 minus rho, g53e_shared g hg0 hg1 minus rho⟩, ?_, ?_⟩
  · intro rho hrho minus
    rw [hI, hS]
    obtain ⟨a, b⟩ := g53e_tr g hg0 hg1 rho hrho
    exact ⟨a, a, b, b⟩
  · intro minus
    rw [hI, hS, g53e_temporal g hg0 hg1]
    exact ⟨rfl, rfl, g53e_iff g, g53e_iff g⟩

end
