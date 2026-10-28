-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P07.wastingBlocking_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:32:51.793906+00:00
-- url     : https://prove2.me/submissions/1315b7e0-ab59-4d4f-9e37-e36269e64f3e

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P07
noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap20.P07

open QAlgorithms

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel traceSize rankOne tensorApply)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation isometryCoeff conjugateKernel)

open QAlgorithms.Papers.Independent.Claimed50.P35
  (stabilizedTraceClassNorm traceClassTensorMap traceClassChannelPower
   transpose transposeBound TraceLinear tracePair MeasurePrepare)

open QAlgorithms.Papers.Independent.Gap48.P29 (fe FiniteCPMap)

/-- Base sequence. -/
def S170C_N (a : ℕ) : ℕ+ := ⟨4 ^ (a ^ 2), by positivity⟩

def S170C_eps (a : ℕ) : ℝ≥0 := (4⁻¹ : ℝ≥0) ^ (a + 1)

def S170C_n (a : ℕ) : ℕ+ := ⟨4 ^ (a ^ 2 + 2 * a), by positivity⟩

def S170C_m (a : ℕ) : ℕ+ := ⟨2 * 4 ^ (a ^ 2 + a), by positivity⟩

lemma S170C_mono : ErrorMonotone (blockingEnvelope S170C_N S170C_eps) := by
  intro n m
  constructor
  · apply min_le_min_left
    apply sInf_le_sInf
    rintro c ⟨bl, h1, h2, rfl⟩
    exact ⟨bl, h1, by rw [PNat.add_coe]; simp only [PNat.one_coe]; omega, rfl⟩
  · apply min_le_min_left
    apply sInf_le_sInf
    rintro c ⟨bl, h1, h2, rfl⟩
    exact ⟨bl, by rw [PNat.add_coe] at h1; simp only [PNat.one_coe] at h1; omega, h2, rfl⟩

lemma S170C_minle (x y z : ℝ≥0∞) (h : x ≤ y + z) : min 1 x ≤ min 1 y + min 1 z := by
  rcases le_total 1 y with hy | hy
  · rw [min_eq_left hy]; exact (min_le_left _ _).trans le_self_add
  rcases le_total 1 z with hz | hz
  · rw [min_eq_left hz]; exact (min_le_left _ _).trans le_add_self
  rw [min_eq_right hy, min_eq_right hz]; exact (min_le_right _ _).trans h

lemma S170C_subadd : ErrorSubadditive (blockingEnvelope S170C_N S170C_eps) := by
  intro n k m l
  apply S170C_minle
  rw [ENNReal.sInf_add]
  refine le_iInf₂ fun b hb => ?_
  rw [ENNReal.add_sInf]
  refine le_iInf₂ fun c hc => ?_
  obtain ⟨bl1, h1, h2, rfl⟩ := hb
  obtain ⟨bl2, h3, h4, rfl⟩ := hc
  apply sInf_le
  refine ⟨bl1 ++ bl2, ?_, ?_, ?_⟩
  · simp only [List.map_append, List.sum_append, PNat.add_coe]; omega
  · simp only [List.map_append, List.sum_append, PNat.add_coe]; omega
  · simp only [List.map_append, List.sum_append]

lemma S170C_idx (a j : ℕ) (h : 4 ^ (j ^ 2) ≤ 4 ^ (a ^ 2 + 2 * a)) : j ≤ a := by
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 4)).1 h
  nlinarith

lemma S170C_term (a j : ℕ) (hj : j ≤ a) :
    ((4 ^ (j ^ 2) : ℕ) : ℝ≥0) * (4⁻¹ : ℝ≥0) ^ (a ^ 2 + a + 1) ≤ S170C_eps j := by
  unfold S170C_eps
  have e : a ^ 2 + a + 1 = (j ^ 2 + (j + 1)) + (a ^ 2 + a - j ^ 2 - j) := by
    have : j ^ 2 + j ≤ a ^ 2 + a := by nlinarith
    omega
  rw [e, pow_add, pow_add, ← mul_assoc, ← mul_assoc]
  push_cast
  rw [← mul_pow, mul_inv_cancel₀ (by norm_num : (4 : ℝ≥0) ≠ 0), one_pow, one_mul]
  exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by positivity) (by first | exact inv_le_one_of_one_le₀ (by norm_num) | exact div_le_one_of_le₀ (by norm_num) (by positivity)))

lemma S170C_bad (a : ℕ) :
    (1 / 2 : ℝ≥0∞) ≤ blockingEnvelope S170C_N S170C_eps (S170C_n a) (S170C_m a) := by
  apply le_min (by norm_num)
  refine le_sInf ?_
  rintro c ⟨bl, h1, h2, rfl⟩
  simp only [S170C_n, S170C_m, PNat.mk_coe, S170C_N] at h1 h2
  have hidx : ∀ j ∈ bl, j ≤ a := fun j hj =>
    S170C_idx a j ((List.le_sum_of_mem (List.mem_map_of_mem (f := fun j => 4 ^ (j ^ 2)) hj)).trans h2)
  have key : (1 / 2 : ℝ≥0) ≤ (bl.map S170C_eps).sum := by
    calc (1 / 2 : ℝ≥0) = ((2 * 4 ^ (a ^ 2 + a) : ℕ) : ℝ≥0) * (4⁻¹ : ℝ≥0) ^ (a ^ 2 + a + 1) := by
          push_cast
          rw [pow_succ (4⁻¹ : ℝ≥0) (a ^ 2 + a), ← mul_assoc, mul_assoc 2, ← mul_pow, mul_inv_cancel₀ (by norm_num : (4 : ℝ≥0) ≠ 0),
            one_pow, mul_one]
          norm_num
      _ ≤ (((bl.map fun j => 4 ^ (j ^ 2)).sum : ℕ) : ℝ≥0) * (4⁻¹ : ℝ≥0) ^ (a ^ 2 + a + 1) := by
          gcongr
      _ = (bl.map fun j => ((4 ^ (j ^ 2) : ℕ) : ℝ≥0) * (4⁻¹ : ℝ≥0) ^ (a ^ 2 + a + 1)).sum := by
          rw [Nat.cast_list_sum, List.sum_map_mul_right, List.map_map]; rfl
      _ ≤ (bl.map S170C_eps).sum := List.sum_le_sum fun j hj => S170C_term a j (hidx j hj)
  have : ((bl.map fun j => (S170C_eps j : ℝ≥0∞))).sum = (((bl.map S170C_eps).sum : ℝ≥0) : ℝ≥0∞) := by
    rw [show (((bl.map S170C_eps).sum : ℝ≥0) : ℝ≥0∞) = ENNReal.ofNNRealHom (bl.map S170C_eps).sum from rfl,
      map_list_sum, List.map_map]; rfl
  rw [this]
  have k2 := ENNReal.coe_le_coe.2 key
  simpa using k2

lemma S170C_eps_eq (a : ℕ) : (S170C_eps a : ℝ) =
    Real.sqrt ((S170C_N a : ℝ) / (S170C_N (a + 1) : ℝ)) / 2 := by
  simp only [S170C_eps, S170C_N, PNat.mk_coe]
  push_cast
  have e : (4 : ℝ) ^ (a ^ 2) / 4 ^ ((a + 1) ^ 2) = (((2 : ℝ) ^ (2 * a + 1))⁻¹) ^ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
    field_simp
    ring
  rw [e, Real.sqrt_sq (by positivity)]
  rw [show (4 : ℝ)⁻¹ = ((2 : ℝ) ^ 2)⁻¹ by norm_num, inv_pow, ← pow_mul]
  field_simp
  ring

lemma S170C_rate : Tendsto (rateRatio S170C_n S170C_m) atTop (𝓝 0) := by
  have e : ∀ a, rateRatio S170C_n S170C_m a = 2 * ((4 : ℝ≥0∞)⁻¹) ^ a := by
    intro a
    simp only [rateRatio, S170C_n, S170C_m, PNat.mk_coe]
    rw [show ((2 * 4 ^ (a ^ 2 + a) : ℕ) : ℝ≥0∞) = 2 * 4 ^ (a ^ 2 + a) by push_cast; ring,
      show ((4 ^ (a ^ 2 + 2 * a) : ℕ) : ℝ≥0∞) = 4 ^ a * 4 ^ (a ^ 2 + a) by push_cast; ring,
      ENNReal.mul_div_mul_right _ _ (by positivity) (by simp), div_eq_mul_inv, ENNReal.inv_pow]
  rw [show rateRatio S170C_n S170C_m = fun a => 2 * ((4 : ℝ≥0∞)⁻¹) ^ a from funext e]
  have : Tendsto (fun a : ℕ => ((4 : ℝ≥0∞)⁻¹) ^ a) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_iff.2 (by
      rw [ENNReal.inv_lt_one]; norm_num)
  simpa using ENNReal.Tendsto.const_mul this (Or.inr (by simp))

lemma S170C_ntend : Tendsto (fun a => (S170C_n a : ℕ)) atTop atTop := by
  refine tendsto_atTop_mono (fun a => ?_) tendsto_id
  simp only [S170C_n, PNat.mk_coe, id]
  calc a ≤ a ^ 2 + 2 * a := by nlinarith
    _ ≤ 4 ^ (a ^ 2 + 2 * a) := (Nat.lt_pow_self (by norm_num)).le

lemma S170C_liminf :
    (1 / 2 : ℝ≥0∞) ≤ Filter.liminf
      (fun a => blockingEnvelope S170C_N S170C_eps (S170C_n a) (S170C_m a)) atTop :=
  Filter.le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall S170C_bad)

end QAlgorithms.Papers.Independent.Gap20.P07

open QAlgorithms.Papers.Independent.Gap20.P07

theorem solution :
    ∃ (N : ℕ → ℕ+) (epsilon : ℕ → ℝ≥0),
      Tendsto (fun a => (N a : ℕ)) atTop atTop ∧
      Tendsto (fun a => (N (a + 1) : ℝ) / (N a : ℝ)) atTop atTop ∧
      (∀ a, 0 < epsilon a ∧ (epsilon a : ℝ) =
        Real.sqrt ((N a : ℝ) / (N (a + 1) : ℝ)) / 2) ∧
      Tendsto epsilon atTop (𝓝 0) ∧
      ErrorMonotone (blockingEnvelope N epsilon) ∧
      ErrorSubadditive (blockingEnvelope N epsilon) ∧
      Tendsto (fun a => blockingEnvelope N epsilon (N a) (N a)) atTop (𝓝 0) ∧
      Sporadic (blockingEnvelope N epsilon) 1 ∧
      errorCapacity (blockingEnvelope N epsilon) = 0 ∧
      ∃ n m : ℕ → ℕ+, Tendsto (fun a => (n a : ℕ)) atTop atTop ∧
        Tendsto (rateRatio n m) atTop (𝓝 0) ∧
        (1 / 2 : ℝ≥0∞) ≤ Filter.liminf
          (fun a => blockingEnvelope N epsilon (n a) (m a)) atTop := by
  have hNt : Tendsto (fun a => (S170C_N a : ℕ)) atTop atTop := by
    refine tendsto_atTop_mono (fun a => ?_) tendsto_id
    simp only [S170C_N, PNat.mk_coe, id]
    calc a ≤ a ^ 2 := by nlinarith
      _ ≤ 4 ^ (a ^ 2) := (Nat.lt_pow_self (by norm_num)).le
  have heps : Tendsto S170C_eps atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (4⁻¹ : ℝ≥0)) bot_le
      (by first | exact inv_lt_one_of_one_lt₀ (by norm_num) | norm_num)
    exact this.comp (tendsto_add_atTop_nat 1)
  have hdiag : Tendsto (fun a => blockingEnvelope S170C_N S170C_eps (S170C_N a) (S170C_N a)) atTop (𝓝 0) := by
    have he : Tendsto (fun a => (S170C_eps a : ℝ≥0∞)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_coe.2 heps
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he (fun _ => bot_le) (fun a => ?_)
    refine (min_le_right _ _).trans (sInf_le ⟨[a], by simp, by simp, by simp⟩)
  have hcap : errorCapacity (blockingEnvelope S170C_N S170C_eps) = 0 := by
    unfold errorCapacity
    refine ENNReal.iSup_eq_zero.2 fun R => ?_
    exfalso
    obtain ⟨R, hR, hall⟩ := R
    have h0 := hall S170C_n S170C_m S170C_ntend (by rw [S170C_rate.limsup_eq]; exact bot_le)
    have := S170C_liminf
    rw [h0.liminf_eq] at this
    norm_num at this
  refine ⟨S170C_N, S170C_eps, hNt, ?_, fun a => ⟨by unfold S170C_eps; positivity, S170C_eps_eq a⟩, heps,
    S170C_mono, S170C_subadd, hdiag, ?_, hcap, S170C_n, S170C_m, S170C_ntend, S170C_rate, S170C_liminf⟩
  · have e : ∀ a, (S170C_N (a + 1) : ℝ) / (S170C_N a : ℝ) = (4 : ℝ) ^ (2 * a + 1) := by
      intro a
      simp only [S170C_N, PNat.mk_coe]
      push_cast
      rw [show (a + 1) ^ 2 = a ^ 2 + (2 * a + 1) by ring, pow_add]
      field_simp
    simp_rw [e]
    refine (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4)).comp ?_
    exact tendsto_atTop_mono (fun a => by simp only [id]; omega) tendsto_id
  · refine ⟨S170C_N, S170C_N, hNt, ?_, hdiag⟩
    have : rateRatio S170C_N S170C_N = fun _ => 1 := by
      funext a
      simp only [rateRatio]
      exact ENNReal.div_self (by simp) (by simp)
    rw [this, limsup_const]; simp
