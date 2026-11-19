-- Prove2me | solution 1 for StrictCompatLB.FullInhomogeneous.fluid_limit_random_initial_law_of_deterministic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-18T21:41:27.972197+00:00
-- url     : https://prove2.me/submissions/3fc84a27-2fa6-4a0c-bb29-2a6966697c68

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model
import Definitions.Def_StrictCompatLB_FullInhomogeneous_UniformizedLaw

set_option autoImplicit false

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace SC9aK6
open StrictCompatLB.FullInhomogeneous StrictCompatLB.MeanField

section
variable {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S] [DecidableEq S]

lemma mA (z : S) : MeasurableSet {ω : ChainSample S | ω.1 0 = z} :=
  (measurableSet_singleton z).preimage (f := fun ω : ChainSample S => ω.1 0)
    ((measurable_pi_apply 0).comp measurable_fst)

lemma PA {P : Measure (ChainSample S)} {K : S → S → ℝ} {rate : ℝ} {μ : S → ℝ}
    (h : IsUniformizedLaw P K rate μ) (z : S) :
    P {ω : ChainSample S | ω.1 0 = z} = ENNReal.ofReal (μ z) := by
  have := h.2.2.1 0 (fun _ => z)
  simpa using this

lemma cond_snd {P : Measure (ChainSample S)} {K : S → S → ℝ} {rate : ℝ} {μ : S → ℝ}
    (h : IsUniformizedLaw P K rate μ) (z : S) (hz : 0 < μ z)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
    cond P {ω : ChainSample S | ω.1 0 = z} ((fun ω : ChainSample S => ω.2) ⁻¹' B) =
      P ((fun ω : ChainSample S => ω.2) ⁻¹' B) := by
  have hpa := PA h z
  have h0 : P {ω : ChainSample S | ω.1 0 = z} ≠ 0 := by
    rw [hpa]; exact (ENNReal.ofReal_pos.2 hz).ne'
  have ht : P {ω : ChainSample S | ω.1 0 = z} ≠ ∞ := by rw [hpa]; exact ENNReal.ofReal_ne_top
  rw [cond_apply (mA z)]
  have hind : IndepFun (fun ω : ChainSample S => ω.1) (fun ω : ChainSample S => ω.2) P :=
    h.2.2.2.2.2.1
  have := hind.measure_inter_preimage_eq_mul {x : ℕ → S | x 0 = z} B
    ((measurableSet_singleton z).preimage (f := fun x : ℕ → S => x 0) (measurable_pi_apply 0)) hB
  have e : {ω : ChainSample S | ω.1 0 = z} ∩ (fun ω : ChainSample S => ω.2) ⁻¹' B =
      (fun ω : ChainSample S => ω.1) ⁻¹' {x : ℕ → S | x 0 = z} ∩
        (fun ω : ChainSample S => ω.2) ⁻¹' B := rfl
  have e2 : (fun ω : ChainSample S => ω.1) ⁻¹' {x : ℕ → S | x 0 = z} =
      {ω : ChainSample S | ω.1 0 = z} := rfl
  rw [e, this, e2, ← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]

lemma cond_law {P : Measure (ChainSample S)} {K : S → S → ℝ} {rate : ℝ} {μ : S → ℝ}
    (h : IsUniformizedLaw P K rate μ) (z : S) (hz : 0 < μ z) :
    IsUniformizedLaw (cond P {ω : ChainSample S | ω.1 0 = z}) K rate
      (fun z' => if z' = z then 1 else 0) := by
  have := h.1
  have hpa := PA h z
  have h0 : P {ω : ChainSample S | ω.1 0 = z} ≠ 0 := by
    rw [hpa]; exact (ENNReal.ofReal_pos.2 hz).ne'
  have hsnd := cond_snd h z hz
  refine ⟨cond_isProbabilityMeasure h0,
    ⟨fun z' => by beta_reduce; split_ifs <;> norm_num, hasSum_ite_eq z 1⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro n zs
    rw [cond_apply (mA z)]
    have hc := h.2.2.1 n zs
    by_cases hz0 : zs 0 = z
    · have e : {ω : ChainSample S | ω.1 0 = z} ∩ {ω : ChainSample S | ∀ j ≤ n, ω.1 j = zs j} =
          {ω : ChainSample S | ∀ j ≤ n, ω.1 j = zs j} := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · exact fun h' => h'.2
        · intro h'
          exact ⟨(h' 0 (Nat.zero_le n)).trans hz0, h'⟩
      beta_reduce
      rw [e, hc, hpa, if_pos hz0, one_mul, hz0, ENNReal.ofReal_mul hz.le, ← mul_assoc,
        ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hz).ne' ENNReal.ofReal_ne_top, one_mul]
    · have e : {ω : ChainSample S | ω.1 0 = z} ∩ {ω : ChainSample S | ∀ j ≤ n, ω.1 j = zs j} =
          ∅ := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
          not_and]
        intro h1 h2
        exact hz0 ((h2 0 (Nat.zero_le n)).symm.trans h1)
      beta_reduce
      rw [e, measure_empty, mul_zero, if_neg hz0, zero_mul, ENNReal.ofReal_zero]
  · rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro I sets hsets
    have hI := (iIndepFun_iff_measure_inter_preimage_eq_mul.1 h.2.2.2.1) I hsets
    have e1 : (⋂ i ∈ I, (fun ω : ChainSample S => ω.2 i) ⁻¹' sets i) =
        (fun ω : ChainSample S => ω.2) ⁻¹' (⋂ i ∈ I, (fun x : ℕ → ℝ => x i) ⁻¹' sets i) := by
      ext ω; simp
    have hm : MeasurableSet (⋂ i ∈ I, (fun x : ℕ → ℝ => x i) ⁻¹' sets i) :=
      Finset.measurableSet_biInter I (fun i hi => (measurable_pi_apply i) (hsets i hi))
    rw [e1, hsnd _ hm, ← e1, hI]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    exact (hsnd _ ((measurable_pi_apply i) (hsets i hi))).symm
  · intro k
    have hk : Measurable (fun ω : ChainSample S => ω.2 k) :=
      (measurable_pi_apply k).comp measurable_snd
    rw [← h.2.2.2.2.1 k]
    ext s hs
    rw [Measure.map_apply hk hs, Measure.map_apply hk hs]
    exact hsnd _ ((measurable_pi_apply k) hs)
  · rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro s t hs ht
    have hind : IndepFun (fun ω : ChainSample S => ω.1) (fun ω : ChainSample S => ω.2) P :=
      h.2.2.2.2.2.1
    have hE : MeasurableSet {x : ℕ → S | x 0 = z} :=
      (measurableSet_singleton z).preimage (f := fun x : ℕ → S => x 0) (measurable_pi_apply 0)
    rw [cond_apply (mA z), cond_apply (mA z), hsnd t ht]
    have e1 : {ω : ChainSample S | ω.1 0 = z} ∩ ((fun ω : ChainSample S => ω.1) ⁻¹' s ∩
        (fun ω : ChainSample S => ω.2) ⁻¹' t) =
        (fun ω : ChainSample S => ω.1) ⁻¹' ({x : ℕ → S | x 0 = z} ∩ s) ∩
          (fun ω : ChainSample S => ω.2) ⁻¹' t := by
      ext ω; simp [and_assoc]
    have e2 : {ω : ChainSample S | ω.1 0 = z} ∩ (fun ω : ChainSample S => ω.1) ⁻¹' s =
        (fun ω : ChainSample S => ω.1) ⁻¹' ({x : ℕ → S | x 0 = z} ∩ s) := by
      ext ω; simp
    rw [e1, e2, hind.measure_inter_preimage_eq_mul _ _ (hE.inter hs) ht]
    ring
  · have hac : cond P {ω : ChainSample S | ω.1 0 = z} ≪ P := by
      intro s hs
      rw [cond_apply (mA z), measure_mono_null Set.inter_subset_right hs, mul_zero]
    exact hac.ae_le h.2.2.2.2.2.2

lemma split [Countable S] {P : Measure (ChainSample S)} {K : S → S → ℝ} {rate : ℝ}
    {μ : S → ℝ} (h : IsUniformizedLaw P K rate μ) (B : Set (ChainSample S)) (F : Set S)
    (c : ℝ≥0∞) (hc : ∀ z, 0 < μ z → z ∉ F → cond P {ω : ChainSample S | ω.1 0 = z} B ≤ c) :
    P B ≤ ENNReal.ofReal (probOf μ F) + c := by
  classical
  have hμ0 := h.2.1.1
  have hμs := h.2.1.2
  have hcov : B ⊆ ⋃ z : S, (if z ∈ F then {ω : ChainSample S | ω.1 0 = z}
      else B ∩ {ω : ChainSample S | ω.1 0 = z}) := by
    intro ω hω
    refine Set.mem_iUnion.2 ⟨ω.1 0, ?_⟩
    split_ifs
    · rfl
    · exact ⟨hω, rfl⟩
  refine (measure_mono hcov).trans ((measure_iUnion_le _).trans ?_)
  have hpt : ∀ z : S, P (if z ∈ F then {ω : ChainSample S | ω.1 0 = z}
      else B ∩ {ω : ChainSample S | ω.1 0 = z}) ≤
      F.indicator (fun z => ENNReal.ofReal (μ z)) z + ENNReal.ofReal (μ z) * c := by
    intro z
    by_cases hzF : z ∈ F
    · rw [if_pos hzF, Set.indicator_of_mem hzF, PA h z]; exact le_self_add
    · rw [if_neg hzF, Set.indicator_of_notMem hzF, zero_add]
      rcases (hμ0 z).lt_or_eq with hz | hz
      · have := hc z hz hzF
        rw [cond_apply (mA z)] at this
        have h0 : P {ω : ChainSample S | ω.1 0 = z} ≠ 0 := by
          rw [PA h z]; exact (ENNReal.ofReal_pos.2 hz).ne'
        have ht : P {ω : ChainSample S | ω.1 0 = z} ≠ ∞ := by
          rw [PA h z]; exact ENNReal.ofReal_ne_top
        calc P (B ∩ {ω : ChainSample S | ω.1 0 = z})
            = P {ω : ChainSample S | ω.1 0 = z} * ((P {ω : ChainSample S | ω.1 0 = z})⁻¹ *
                P ({ω : ChainSample S | ω.1 0 = z} ∩ B)) := by
              rw [← mul_assoc, ENNReal.mul_inv_cancel h0 ht, one_mul, Set.inter_comm]
          _ ≤ P {ω : ChainSample S | ω.1 0 = z} * c := by gcongr
          _ = ENNReal.ofReal (μ z) * c := by rw [PA h z]
      · calc P (B ∩ {ω : ChainSample S | ω.1 0 = z}) ≤ P {ω : ChainSample S | ω.1 0 = z} :=
              measure_mono Set.inter_subset_right
          _ = 0 := by rw [PA h z, ← hz, ENNReal.ofReal_zero]
          _ ≤ _ := zero_le
  refine (ENNReal.tsum_le_tsum hpt).trans ?_
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
  have h1 : ∑' z, ENNReal.ofReal (μ z) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hμ0 hμs.summable, hμs.tsum_eq, ENNReal.ofReal_one]
  have h2 : ∑' z, F.indicator (fun z => ENNReal.ofReal (μ z)) z =
      ENNReal.ofReal (probOf μ F) := by
    unfold probOf
    rw [ENNReal.ofReal_tsum_of_nonneg (fun z => Set.indicator_nonneg (fun z _ => hμ0 z) z)
      (hμs.summable.indicator F)]
    refine tsum_congr (fun z => ?_)
    by_cases hz : z ∈ F <;> simp [hz]
  rw [h1, h2, one_mul]

end

theorem bridge {K : (N : ℕ) → (Fin N → ℕ) → (Fin N → ℕ) → ℝ} {rate : ℕ → ℝ} {N₀ : ℕ}
    (D : (N : ℕ) → (Fin N → ℕ) → ℝ≥0∞)
    (Bad : (N : ℕ) → Set (ChainSample (Fin N → ℕ)))
    (hdet : ∀ (z₀ : (N : ℕ) → Fin N → ℕ) (P : (N : ℕ) → Measure (ChainSample (Fin N → ℕ))),
      (∀ N ≥ N₀, IsUniformizedLaw (P N) (K N) (rate N) (fun z => if z = z₀ N then 1 else 0)) →
      Tendsto (fun N => D N (z₀ N)) atTop (𝓝 0) →
      Tendsto (fun N => P N (Bad N)) atTop (𝓝 0))
    (μ : (N : ℕ) → (Fin N → ℕ) → ℝ) (P : (N : ℕ) → Measure (ChainSample (Fin N → ℕ)))
    (hP : ∀ N ≥ N₀, IsUniformizedLaw (P N) (K N) (rate N) (μ N))
    (hμ : ∀ ε : ℝ, 0 < ε → Tendsto (fun N => probOf (μ N) {z | ENNReal.ofReal ε ≤ D N z})
      atTop (𝓝 0)) :
    Tendsto (fun N => P N (Bad N)) atTop (𝓝 0) := by
  classical
  rw [ENNReal.tendsto_atTop_zero]
  by_contra hne
  push_neg at hne
  obtain ⟨η, hη, hfr⟩ := hne
  have hη1 : η < 1 := by
    obtain ⟨n, hn, hηn⟩ := hfr N₀
    have := (hP n hn).1
    exact hηn.trans_le prob_le_one
  have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
  have hη21 : η / 2 < 1 := (ENNReal.half_le_self).trans_lt hη1
  have hη2top : η / 2 ≠ ∞ := (hη21.trans ENNReal.one_lt_top).ne
  set R : ℕ → ℕ → Prop := fun N k =>
    ENNReal.ofReal (probOf (μ N) {z | ENNReal.ofReal (1 / ((k : ℝ) + 1)) ≤ D N z}) < η / 2
    with hRdef
  have hR : ∀ k, ∀ᶠ N in atTop, R N k := by
    intro k
    have h1 := ENNReal.tendsto_ofReal (hμ (1 / ((k : ℝ) + 1)) (by positivity))
    rw [ENNReal.ofReal_zero] at h1
    exact h1.eventually (gt_mem_nhds hη2)
  set kN : ℕ → ℕ := fun N => Nat.findGreatest (R N) N with hkN
  have hk : ∀ k, ∀ᶠ N in atTop, k ≤ kN N ∧ R N (kN N) := by
    intro k
    filter_upwards [hR k, eventually_ge_atTop k] with N h1 h2
    exact ⟨Nat.le_findGreatest h2 h1, Nat.findGreatest_spec h2 h1⟩
  have hWex : ∀ N, N₀ ≤ N → R N (kN N) →
      ∃ z, 0 < μ N z ∧ D N z < ENNReal.ofReal (1 / ((kN N : ℝ) + 1)) := by
    intro N hN hRN
    by_contra hno
    push_neg at hno
    have hone : probOf (μ N) {z | ENNReal.ofReal (1 / ((kN N : ℝ) + 1)) ≤ D N z} = 1 := by
      unfold probOf
      have hs := (hP N hN).2.1.2
      refine (tsum_congr (fun z => ?_)).trans hs.tsum_eq
      by_cases hz : z ∈ {z | ENNReal.ofReal (1 / ((kN N : ℝ) + 1)) ≤ D N z}
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz]
        rcases ((hP N hN).2.1.1 z).lt_or_eq with h' | h'
        · exact (hz (hno z h')).elim
        · exact h'
    have hRN' : ENNReal.ofReal
        (probOf (μ N) {z | ENNReal.ofReal (1 / ((kN N : ℝ) + 1)) ≤ D N z}) < η / 2 := hRN
    rw [hone, ENNReal.ofReal_one] at hRN'
    exact absurd (hRN'.trans hη21) (lt_irrefl 1)
  have hpos : ∀ N, N₀ ≤ N → ∃ z, 0 < μ N z := by
    intro N hN
    by_contra hno
    push_neg at hno
    have hs := (hP N hN).2.1.2
    have h0 : μ N = 0 := funext (fun z => le_antisymm (hno z) ((hP N hN).2.1.1 z))
    rw [h0] at hs
    exact one_ne_zero (hs.unique hasSum_zero)
  have hchoice : ∀ N, ∃ z : Fin N → ℕ, (N₀ ≤ N → 0 < μ N z) ∧
      (N₀ ≤ N → R N (kN N) → D N z < ENNReal.ofReal (1 / ((kN N : ℝ) + 1))) ∧
      ((∃ z', 0 < μ N z' ∧ D N z' < ENNReal.ofReal (1 / ((kN N : ℝ) + 1)) ∧
          η / 2 < cond (P N) {ω : ChainSample (Fin N → ℕ) | ω.1 0 = z'} (Bad N)) →
        η / 2 < cond (P N) {ω : ChainSample (Fin N → ℕ) | ω.1 0 = z} (Bad N)) := by
    intro N
    by_cases h1 : ∃ z', 0 < μ N z' ∧ D N z' < ENNReal.ofReal (1 / ((kN N : ℝ) + 1)) ∧
        η / 2 < cond (P N) {ω : ChainSample (Fin N → ℕ) | ω.1 0 = z'} (Bad N)
    · obtain ⟨z, hz1, hz2, hz3⟩ := h1
      exact ⟨z, fun _ => hz1, fun _ _ => hz2, fun _ => hz3⟩
    · by_cases h2 : ∃ z', 0 < μ N z' ∧ D N z' < ENNReal.ofReal (1 / ((kN N : ℝ) + 1))
      · obtain ⟨z, hz1, hz2⟩ := h2
        exact ⟨z, fun _ => hz1, fun _ _ => hz2, fun h => absurd h h1⟩
      · by_cases hN : N₀ ≤ N
        · obtain ⟨z, hz⟩ := hpos N hN
          exact ⟨z, fun _ => hz, fun _ hRN => absurd (hWex N hN hRN) h2, fun h => absurd h h1⟩
        · exact ⟨fun _ => 0, fun h => absurd h hN, fun h => absurd h hN, fun h => absurd h h1⟩
  choose z₀ hz₀ using hchoice
  have hlaw : ∀ N ≥ N₀, IsUniformizedLaw
      (cond (P N) {ω : ChainSample (Fin N → ℕ) | ω.1 0 = z₀ N})
      (K N) (rate N) (fun z => if z = z₀ N then 1 else 0) :=
    fun N hN => cond_law (hP N hN) (z₀ N) ((hz₀ N).1 hN)
  have hD : Tendsto (fun N => D N (z₀ N)) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε
    have h1 := ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    rw [ENNReal.ofReal_zero] at h1
    obtain ⟨k, hk1⟩ := (h1.eventually (gt_mem_nhds hε)).exists
    obtain ⟨M, hM⟩ := eventually_atTop.1 ((hk k).and (eventually_ge_atTop N₀))
    refine ⟨M, fun N hN => ?_⟩
    obtain ⟨⟨hkle, hRN⟩, hN0⟩ := hM N hN
    refine ((hz₀ N).2.1 hN0 hRN).le.trans (le_trans ?_ hk1.le)
    apply ENNReal.ofReal_le_ofReal
    apply one_div_le_one_div_of_le (by positivity)
    have : (k : ℝ) ≤ (kN N : ℝ) := by exact_mod_cast hkle
    linarith
  have hlim := hdet z₀ _ hlaw hD
  obtain ⟨M2, hM2⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hη2))
  obtain ⟨M1, hM1⟩ := eventually_atTop.1 (hk 0)
  obtain ⟨n, hn, hηn⟩ := hfr (max M2 (max M1 N₀))
  have hn2 : M2 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : M1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn0 : N₀ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hRn := (hM1 n hn1).2
  have hex : ∃ z', 0 < μ n z' ∧ D n z' < ENNReal.ofReal (1 / ((kN n : ℝ) + 1)) ∧
      η / 2 < cond (P n) {ω : ChainSample (Fin n → ℕ) | ω.1 0 = z'} (Bad n) := by
    by_contra hno
    push_neg at hno
    have hsp := split (hP n hn0) (Bad n)
      {z | ENNReal.ofReal (1 / ((kN n : ℝ) + 1)) ≤ D n z} (η / 2)
      (fun z hz hzF => hno z hz (not_le.1 hzF))
    have hRn' : ENNReal.ofReal
        (probOf (μ n) {z | ENNReal.ofReal (1 / ((kN n : ℝ) + 1)) ≤ D n z}) < η / 2 := hRn
    have hlt : P n (Bad n) < η := by
      calc P n (Bad n) ≤ _ := hsp
        _ < η / 2 + η / 2 := ENNReal.add_lt_add_right hη2top hRn'
        _ = η := ENNReal.add_halves η
    exact absurd hηn (not_lt.2 hlt.le)
  have hfin := (hz₀ n).2.2 hex
  exact absurd (hM2 n hn2) (not_lt.2 hfin.le)

end SC9aK6

open StrictCompatLB.FullInhomogeneous StrictCompatLB.MeanField in
theorem solution (K : (N : ℕ) → (Fin N → ℕ) → (Fin N → ℕ) → ℝ) (rate : ℕ → ℝ) (N₀ : ℕ)
    (q₀ : ℕ → ℝ) (s : ℝ≥0 → ℕ → ℝ) (T ε : ℝ)
    (hdet : ∀ (z₀ : (N : ℕ) → Fin N → ℕ) (P : (N : ℕ) → Measure (ChainSample (Fin N → ℕ))),
      (∀ N ≥ N₀, IsUniformizedLaw (P N) (K N) (rate N) (fun z => if z = z₀ N then 1 else 0)) →
      Tendsto (fun N => PowerOfDUniversality.Fluid.l1dist (occ (z₀ N)) q₀) atTop (𝓝 0) →
      Tendsto (fun N => P N {a | ENNReal.ofReal ε ≤
          PowerOfDUniversality.Fluid.supDistL1
            (fun t => occ (taggedState a t)) (fun t => s (Real.toNNReal t)) T}) atTop (𝓝 0))
    (μ : (N : ℕ) → (Fin N → ℕ) → ℝ) (P : (N : ℕ) → Measure (ChainSample (Fin N → ℕ)))
    (hP : ∀ N ≥ N₀, IsUniformizedLaw (P N) (K N) (rate N) (μ N))
    (hμ : ∀ ε' : ℝ, 0 < ε' → Tendsto (fun N => probOf (μ N)
      {z | ENNReal.ofReal ε' ≤ PowerOfDUniversality.Fluid.l1dist (occ z) q₀}) atTop (𝓝 0)) :
    Tendsto (fun N => P N {a | ENNReal.ofReal ε ≤
        PowerOfDUniversality.Fluid.supDistL1
          (fun t => occ (taggedState a t)) (fun t => s (Real.toNNReal t)) T}) atTop (𝓝 0) := by
  exact SC9aK6.bridge (fun N z => PowerOfDUniversality.Fluid.l1dist (occ z) q₀) _ hdet μ P hP hμ
