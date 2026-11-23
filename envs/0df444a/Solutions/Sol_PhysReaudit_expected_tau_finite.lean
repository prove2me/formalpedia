-- Prove2me | solution 1 for PhysReaudit.expected_tau_finite
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T09:48:18.513751+00:00
-- url     : https://prove2.me/submissions/7ba7cf12-1eed-414e-a632-4badea0c779d

import Mathlib
import Definitions.Def_PhysReaudit_Delta
import Definitions.Def_PhysReaudit_lawQ
import Definitions.Def_PhysReaudit_sprtS

open MeasureTheory

namespace PRExpTauFinite

open PhysReaudit

/-- Deterministic block lemma: `K` equal increments `d` with `K|d| > 2A` force exit. -/
theorem tau_le_of_block {q₀ t δ : ℝ} (hA : 0 < Real.log (1 / δ)) (b : Bool) (K : ℕ)
    (hK : 2 * Real.log (1 / δ) < K * |sprtIncr q₀ t b|) (y : ℕ → Bool) (j : ℕ)
    (hy : ∀ k < K, y (j + k) = b) : sprtTau q₀ t δ y ≤ ((j + K : ℕ) : ℕ∞) := by
  set A := Real.log (1 / δ)
  by_contra hcon
  have hno : ∀ n, 1 ≤ n → n ≤ j + K → -A < sprtS q₀ t y n ∧ sprtS q₀ t y n < A := by
    intro n hn1 hn2
    by_contra hc
    apply hcon
    have hex : A ≤ sprtS q₀ t y n ∨ sprtS q₀ t y n ≤ -A := by
      by_contra h'
      rw [not_or, not_le, not_le] at h'
      exact hc ⟨h'.2, h'.1⟩
    calc sprtTau q₀ t δ y ≤ (n : ℕ∞) := iInf₂_le n ⟨hn1, hex⟩
      _ ≤ _ := by exact_mod_cast hn2
  have hKpos : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h; simp at hK; linarith
    · exact h
  have hj : |sprtS q₀ t y j| < A := by
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; simp [sprtS, hA]
    · have := hno j h (by omega); exact abs_lt.mpr this
  have hjK : |sprtS q₀ t y (j + K)| < A := abs_lt.mpr (hno (j + K) (by omega) le_rfl)
  have hdiff : sprtS q₀ t y (j + K) - sprtS q₀ t y j = K * sprtIncr q₀ t b := by
    unfold sprtS
    rw [Finset.sum_range_add, add_sub_cancel_left]
    rw [Finset.sum_congr rfl (fun k hk => by rw [hy k (Finset.mem_range.mp hk)])]
    simp
  have : |sprtS q₀ t y (j + K) - sprtS q₀ t y j| < 2 * A := by
    calc _ ≤ |sprtS q₀ t y (j + K)| + |sprtS q₀ t y j| := abs_sub _ _
      _ < A + A := add_lt_add hjK hj
      _ = 2 * A := by ring
  rw [hdiff, abs_mul, Nat.abs_cast] at this
  linarith


theorem bern_prob {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) : IsProbabilityMeasure (bern q) := by
  constructor
  simp only [bern, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hq.1 (by linarith [hq.2])]
  simp

theorem bern_single {q : ℝ} (b : Bool) :
    bern q {b} = if b then ENNReal.ofReal q else ENNReal.ofReal (1 - q) := by
  cases b <;> simp [bern]

/-- Extension of a finset-indexed tuple to all of `ℕ`. -/
noncomputable def extT (S : Finset ℕ) (v : S → Bool) (n : ℕ) : Bool :=
  if h : n ∈ S then v ⟨n, h⟩ else false

theorem extT_apply (S : Finset ℕ) (y : ℕ → Bool) {n : ℕ} (h : n ∈ S) :
    extT S (fun i : S => y i) n = y n := by
  simp [extT, h]

/-- Bad event of block `i`: all `K` entries equal `b`. -/
def C (b : Bool) (K i : ℕ) : Set (ℕ → Bool) := {y | ∀ k < K, y (i * K + k) = b}

/-- No bad block among the first `m`. -/
def E (b : Bool) (K m : ℕ) : Set (ℕ → Bool) := {y | ∀ i < m, y ∉ C b K i}

theorem measurableSet_C (b : Bool) (K i : ℕ) : MeasurableSet (C b K i) := by
  have : C b K i = ⋂ k ∈ Finset.range K, (fun y : ℕ → Bool => y (i * K + k)) ⁻¹' {b} := by
    ext y; simp [C]
  rw [this]
  exact Finset.measurableSet_biInter _ fun k _ => measurable_pi_apply _ (measurableSet_singleton b)

theorem measurableSet_E (b : Bool) (K m : ℕ) : MeasurableSet (E b K m) := by
  have : E b K m = ⋂ i ∈ Finset.range m, (C b K i)ᶜ := by
    ext y; simp [E]
  rw [this]
  exact Finset.measurableSet_biInter _ fun i _ => (measurableSet_C b K i).compl

theorem E_succ (b : Bool) (K m : ℕ) : E b K (m + 1) = E b K m ∩ (C b K m)ᶜ := by
  ext y
  simp only [E, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff]
  constructor
  · intro h; exact ⟨fun i hi => h i (by omega), h m (by omega)⟩
  · rintro ⟨h1, h2⟩ i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · exact h1 i h
    · subst h; exact h2

theorem measure_E_le {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) (b : Bool) (K : ℕ) (c : ENNReal)
    (hc : c ≤ bern q {b} ^ K) (m : ℕ) :
    Measure.infinitePi (fun _ : ℕ => bern q) (E b K m) ≤ (1 - c) ^ m := by
  have := bern_prob hq
  set μ := Measure.infinitePi (fun _ : ℕ => bern q)
  have hind : ProbabilityTheory.iIndepFun (fun i (ω : ℕ → Bool) => ω i) μ :=
    ProbabilityTheory.iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)
  induction m with
  | zero => simp [E]
  | succ m ih =>
    rw [E_succ]
    set S := Finset.range (m * K)
    set T := Finset.Ico (m * K) (m * K + K)
    have hST : Disjoint S T := by
      rw [Finset.disjoint_left]; intro a ha hb
      simp [S, T] at ha hb; omega
    have hI := hind.indepFun_finset S T hST (fun i => measurable_pi_apply i)
    have hE : E b K m = (fun ω (i : S) => ω i) ⁻¹'
        {v | ∀ i < m, ¬ ∀ k < K, extT S v (i * K + k) = b} := by
      ext y
      simp only [E, C, Set.mem_ofPred_eq, Set.mem_preimage]
      refine forall_congr' fun i => imp_congr_right fun hi => not_congr <|
        forall_congr' fun k => imp_congr_right fun hk => ?_
      have : (i + 1) * K ≤ m * K := Nat.mul_le_mul_right _ hi
      rw [extT_apply S y (by simp [S]; nlinarith)]
    have hC : (C b K m)ᶜ = (fun ω (i : T) => ω i) ⁻¹'
        {w | ¬ ∀ k < K, extT T w (m * K + k) = b} := by
      ext y
      simp only [C, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_preimage]
      refine not_congr <| forall_congr' fun k => imp_congr_right fun hk => ?_
      rw [extT_apply T y (by simp [T]; omega)]
    have hmul : μ (E b K m ∩ (C b K m)ᶜ) = μ (E b K m) * μ ((C b K m)ᶜ) := by
      rw [hE, hC]
      exact hI.measure_inter_preimage_eq_mul _ _ (Set.toFinite _).measurableSet
        (Set.toFinite _).measurableSet
    have hCm : μ (C b K m) = bern q {b} ^ K := by
      have : C b K m = Set.pi (↑T) (fun _ => {b}) := by
        ext y
        simp only [C, Set.mem_ofPred_eq, Set.mem_pi, Finset.mem_coe, Set.mem_singleton_iff, T,
          Finset.mem_Ico]
        constructor
        · intro h n hn
          have := h (n - m * K) (by omega)
          rwa [show m * K + (n - m * K) = n by omega] at this
        · intro h k hk; exact h _ ⟨by omega, by omega⟩
      rw [this, Measure.infinitePi_pi (μ := fun _ : ℕ => bern q) (mt := fun _ _ => measurableSet_singleton b)]
      simp [T]
    have hCc : μ ((C b K m)ᶜ) ≤ 1 - c := by
      rw [measure_compl (measurableSet_C b K m) (measure_ne_top _ _), measure_univ, hCm]
      exact tsub_le_tsub_left hc 1
    rw [hmul, pow_succ]
    exact mul_le_mul' ih hCc


theorem tau_le_of_notE {q₀ t δ : ℝ} (hA : 0 < Real.log (1 / δ)) (b : Bool) (K : ℕ)
    (hK : 2 * Real.log (1 / δ) < K * |sprtIncr q₀ t b|) (y : ℕ → Bool) (m : ℕ)
    (hy : y ∉ E b K m) : sprtTau q₀ t δ y ≤ ((m * K : ℕ) : ℕ∞) := by
  simp only [E, Set.mem_ofPred_eq, not_forall, not_not] at hy
  obtain ⟨i, hi, hiC⟩ := hy
  refine (tau_le_of_block hA b K hK y (i * K) hiC).trans ?_
  have : (i + 1) * K ≤ m * K := Nat.mul_le_mul_right _ hi
  exact_mod_cast (show i * K + K ≤ m * K by nlinarith)

theorem tau_pointwise {q₀ t δ : ℝ} (hA : 0 < Real.log (1 / δ)) (b : Bool) (K : ℕ)
    (hK : 2 * Real.log (1 / δ) < K * |sprtIncr q₀ t b|) (hK0 : K ≠ 0) (y : ℕ → Bool) :
    (sprtTau q₀ t δ y : ENNReal) ≤ (K : ENNReal) * ∑' m, (E b K m).indicator 1 y := by
  classical
  by_cases hex : ∃ m, y ∉ E b K m
  · let m := Nat.find hex
    have hm : y ∉ E b K m := Nat.find_spec hex
    have hlt : ∀ j < m, y ∈ E b K j := fun j hj => by
      have := Nat.find_min hex hj; simpa using this
    have h1 : (sprtTau q₀ t δ y : ENNReal) ≤ ((m * K : ℕ) : ENNReal) := by
      have := tau_le_of_notE hA b K hK y m hm
      have h' := ENat.toENNReal_le.mpr this
      simpa using h'
    have h2 : (m : ENNReal) ≤ ∑' j, (E b K j).indicator 1 y := by
      calc (m : ENNReal) = ∑ j ∈ Finset.range m, (E b K j).indicator 1 y := by
            rw [Finset.sum_congr rfl (fun j hj => Set.indicator_of_mem
              (hlt j (Finset.mem_range.mp hj)) _)]
            simp
        _ ≤ _ := ENNReal.sum_le_tsum _
    calc (sprtTau q₀ t δ y : ENNReal) ≤ ((m * K : ℕ) : ENNReal) := h1
      _ = (K : ENNReal) * m := by push_cast; ring
      _ ≤ _ := mul_le_mul' le_rfl h2
  · push Not at hex
    have : ∑' j, (E b K j).indicator (1 : (ℕ → Bool) → ENNReal) y = ⊤ := by
      simp only [Set.indicator_of_mem (hex _), Pi.one_apply]
      exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
    rw [this, ENNReal.mul_top (by exact_mod_cast hK0)]
    exact le_top

end PRExpTauFinite

open PhysReaudit in
theorem solution {q₀ t δ : ℝ} (h0 : 0 < q₀) (h1 : q₀ < t) (h2 : t < 1) (hδ : 0 < δ)
    (hδ1 : δ < 1 / 2) {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    ∫⁻ y, (sprtTau q₀ t δ y : ENNReal) ∂(Measure.infinitePi fun _ : ℕ => bern q) < ⊤ := by
  open PRExpTauFinite in
  have hA : 0 < Real.log (1 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  set b : Bool := decide (1 / 2 ≤ q)
  have hd : sprtIncr q₀ t b ≠ 0 := by
    unfold sprtIncr zMinus zPlus
    split_ifs
    · have : q₀ / t < 1 := (div_lt_one (by linarith)).mpr h1
      exact (Real.log_neg (div_pos h0 (by linarith)) this).ne
    · have : 1 < (1 - q₀) / (1 - t) := (one_lt_div (by linarith)).mpr (by linarith)
      exact (Real.log_pos this).ne'
  have hdpos : 0 < |sprtIncr q₀ t b| := abs_pos.mpr hd
  set K : ℕ := ⌈2 * Real.log (1 / δ) / |sprtIncr q₀ t b|⌉₊ + 1
  have hK : 2 * Real.log (1 / δ) < K * |sprtIncr q₀ t b| := by
    have h := Nat.le_ceil (2 * Real.log (1 / δ) / |sprtIncr q₀ t b|)
    rw [div_le_iff₀ hdpos] at h
    have : (K : ℝ) = ⌈2 * Real.log (1 / δ) / |sprtIncr q₀ t b|⌉₊ + 1 := by simp [K]
    rw [this]; nlinarith
  have hK0 : K ≠ 0 := by simp [K]
  set c : ENNReal := (2⁻¹ : ENNReal) ^ K
  have hr : (2⁻¹ : ENNReal) ≤ bern q {b} := by
    rw [bern_single]
    by_cases hq2 : 1 / 2 ≤ q
    · simp only [b, hq2, decide_true, if_true]
      rw [show (2⁻¹ : ENNReal) = ENNReal.ofReal 2⁻¹ by simp]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · simp only [b, hq2, decide_false]
      rw [show (2⁻¹ : ENNReal) = ENNReal.ofReal 2⁻¹ by simp]
      exact ENNReal.ofReal_le_ofReal (by push Not at hq2; linarith)
  have hc : c ≤ bern q {b} ^ K := pow_le_pow_left' hr K
  have hc0 : c ≠ 0 := by simp [c]
  have hc1 : c ≤ 1 := pow_le_one₀ (by simp) (by simp)
  set μ := Measure.infinitePi (fun _ : ℕ => bern q)
  calc ∫⁻ y, (sprtTau q₀ t δ y : ENNReal) ∂μ
      ≤ ∫⁻ y, (K : ENNReal) * ∑' m, (E b K m).indicator 1 y ∂μ :=
        lintegral_mono fun y => tau_pointwise hA b K hK hK0 y
    _ = (K : ENNReal) * ∑' m, μ (E b K m) := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_tsum
          (fun m => (measurable_one.indicator (measurableSet_E b K m)).aemeasurable)]
        simp_rw [lintegral_indicator_one (measurableSet_E b K _)]
    _ ≤ (K : ENNReal) * ∑' m, (1 - c) ^ m :=
        mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun m => measure_E_le hq b K c hc m)
    _ = (K : ENNReal) * c⁻¹ := by
        rw [ENNReal.tsum_geometric, ENNReal.sub_sub_cancel ENNReal.one_ne_top hc1]
    _ < ⊤ := ENNReal.mul_lt_top (by simp) (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hc0))
