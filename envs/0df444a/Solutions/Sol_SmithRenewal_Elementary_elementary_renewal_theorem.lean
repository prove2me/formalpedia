-- Prove2me | solution 1 for SmithRenewal.Elementary.elementary_renewal_theorem
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-21T01:56:17.592716+00:00
-- url     : https://prove2.me/submissions/5e1e399a-5ec8-4c23-87dc-abf45fc6446a

import Mathlib
import Definitions.Def_SmithRenewal_Elementary_RenewalProcess

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology BigOperators Classical
open SmithRenewal.Elementary

namespace RenewalProof

noncomputable def occupancy {Ω : Type*} (X : ℕ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∑' i : ℕ, if S X i ω ≤ t then 1 else 0

noncomputable def reward {Ω : Type*} (X : ℕ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∑' i : ℕ, ENNReal.ofReal (X i ω) * (if S X i ω ≤ t then 1 else 0)

end RenewalProof

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology BigOperators Classical
open SmithRenewal.Elementary

namespace RenewalProof
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ}

theorem measurable_S (hX : IsRenewalProcess P X) (i : ℕ) : Measurable (S X i) := by
  unfold S
  exact Finset.measurable_sum _ fun j _ => hX.measurable j

theorem measurable_occupancy (hX : IsRenewalProcess P X) (t : ℝ) :
    Measurable (occupancy X t) := by
  unfold occupancy
  exact Measurable.tsum fun i => measurable_const.ite
    (measurableSet_le (measurable_S hX i) measurable_const) measurable_const

theorem measurable_reward (hX : IsRenewalProcess P X) (t : ℝ) :
    Measurable (reward X t) := by
  unfold reward
  exact Measurable.tsum fun i => (hX.measurable i).ennreal_ofReal.mul
    (measurable_const.ite (measurableSet_le (measurable_S hX i) measurable_const)
      measurable_const)

omit [MeasurableSpace Ω] in
theorem occupancy_eq {t : ℝ} (ht : 0 ≤ t) (ω : Ω) :
    occupancy X t ω = 1 + (N X t ω : ℝ≥0∞) := by
  have hs : {i : ℕ | S X i ω ≤ t} = insert 0 {i : ℕ | 1 ≤ i ∧ S X i ω ≤ t} := by
    ext i
    by_cases hi : i = 0
    · subst i; simp [S, ht]
    · simp [hi, Nat.one_le_iff_ne_zero.mpr hi]
  have hc : occupancy X t ω = ({i : ℕ | S X i ω ≤ t}.encard : ℝ≥0∞) := by
    rw [← ENNReal.tsum_set_one]
    have hh := tsum_subtype {i : ℕ | S X i ω ≤ t} (fun _ : ℕ => (1 : ℝ≥0∞))
    exact hh.symm
  rw [hc, hs, Set.encard_insert_of_notMem (by simp)]
  simp [N, add_comm]

variable [IsProbabilityMeasure P]
theorem integral_occupancy (hX : IsRenewalProcess P X) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, occupancy X t ω ∂P = 1 + H X P t := by
  have _ := hX
  simp_rw [occupancy_eq ht]
  rw [lintegral_add_left measurable_const]
  simp [H]

end RenewalProof

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology BigOperators Classical
open SmithRenewal.Elementary

namespace RenewalProof

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ}

theorem mean_pos (hX : IsRenewalProcess P X) : 0 < mu1 X P := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have hae : (fun ω => ENNReal.ofReal (X 0 ω)) =ᵐ[P] 0 :=
    (lintegral_eq_zero_iff (hX.measurable 0).ennreal_ofReal).mp hz
  have hz' : ∀ᵐ ω ∂P, X 0 ω = 0 := by
    filter_upwards [hae] with ω hω
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp hω) (hX.nonneg 0 ω)
  have hmeasure : P {ω | X 0 ω = 0} = 1 :=
    (mem_ae_iff_prob_eq_one (measurableSet_eq_fun (hX.measurable 0) measurable_const)).mp hz'
  exact (ne_of_lt hX.not_ae_zero) hmeasure

theorem integral_reward (hX : IsRenewalProcess P X) {t : ℝ} (ht : 0 ≤ t) :
    (∫⁻ ω, reward X t ω ∂P) = mu1 X P * (1 + H X P t) := by
  classical
  let I : ℕ → Ω → ℝ≥0∞ := fun i ω => if S X i ω ≤ t then 1 else 0
  have hmI : ∀ i, Measurable (I i) := by
    intro i
    exact Measurable.ite (measurableSet_le (measurable_S hX i) measurable_const)
      measurable_const measurable_const
  have hmean : ∀ i, (∫⁻ ω, ENNReal.ofReal (X i ω) ∂P) = mu1 X P := by
    intro i
    exact ((hX.identDistrib i).comp ENNReal.measurable_ofReal).lintegral_eq
  have hf : ∀ i, (∫⁻ ω, ENNReal.ofReal (X i ω) * I i ω ∂P) =
      mu1 X P * ∫⁻ ω, I i ω ∂P := by
    intro i
    have hi := hX.indep.indepFun_finsetSum_of_notMem hX.measurable
      (Finset.notMem_range_self (n := i))
    have hi' : IndepFun (X i) (fun ω => S X i ω) P := by
      have he : (∑ j ∈ Finset.range i, X j) = (fun ω => S X i ω) := by
        funext ω
        simp [S]
      rw [← he]
      exact hi.symm
    have hthreshold : Measurable (fun z : ℝ => if z ≤ t then (1 : ℝ≥0∞) else 0) :=
      Measurable.ite measurableSet_Iic measurable_const measurable_const
    have hind : IndepFun (fun ω => ENNReal.ofReal (X i ω)) (I i) P :=
      hi'.comp ENNReal.measurable_ofReal hthreshold
    rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
      (hX.measurable i).ennreal_ofReal.aemeasurable (hmI i).aemeasurable hind, hmean i]
  change (∫⁻ ω, ∑' i, ENNReal.ofReal (X i ω) * I i ω ∂P) = _
  rw [lintegral_tsum (f := fun i ω => ENNReal.ofReal (X i ω) * I i ω)
    (fun i => ((hX.measurable i).ennreal_ofReal.mul (hmI i)).aemeasurable)]
  simp_rw [hf]
  rw [ENNReal.tsum_mul_left]
  have hocc : (∑' i, ∫⁻ ω, I i ω ∂P) = 1 + H X P t := by
    rw [← lintegral_tsum (fun i => (hmI i).aemeasurable)]
    exact integral_occupancy hX ht
  rw [hocc]

end RenewalProof

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology BigOperators Classical
open SmithRenewal.Elementary

namespace RenewalProof
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ}

theorem trunc_process (hX : IsRenewalProcess P X) {Δ : ℝ} (hΔ : 0 < Δ) :
    IsRenewalProcess P (trunc Δ X) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact (hX.measurable i).min measurable_const
  · exact hX.indep.comp (fun _ x => min x Δ) (fun _ => measurable_id.min measurable_const)
  · intro i
    exact (hX.identDistrib i).comp (measurable_id.min measurable_const)
  · intro i ω; exact le_min (hX.nonneg i ω) hΔ.le
  · have he : {ω | trunc Δ X 0 ω = 0} = {ω | X 0 ω = 0} := by
      ext ω
      simp only [mem_ofPred_eq, trunc]
      constructor
      · intro h; rcases le_total (X 0 ω) Δ with hle | hle
        · simpa [min_eq_left hle] using h
        · simp [min_eq_right hle, hΔ.ne'] at h
      · intro h; simp [h, hΔ.le]
    rw [he]; exact hX.not_ae_zero

omit [MeasurableSpace Ω] in
theorem S_trunc_le (Δ : ℝ) (i : ℕ) (ω : Ω) : S (trunc Δ X) i ω ≤ S X i ω := by
  exact Finset.sum_le_sum fun j _ => min_le_left _ _

theorem H_trunc_le (hX : IsRenewalProcess P X) {Δ : ℝ} (hΔ : 0 < Δ) (t : ℝ) :
    H X P t ≤ H (trunc Δ X) P t := by
  have _ := hX; have _ := hΔ
  apply lintegral_mono
  intro ω
  apply ENat.toENNReal_mono
  apply Set.encard_mono
  intro i hi
  exact ⟨hi.1, (S_trunc_le Δ i ω).trans hi.2⟩

variable [IsProbabilityMeasure P]
theorem truncated_mean_le (hX : IsRenewalProcess P X) {Δ : ℝ} (hΔ : 0 < Δ) :
    mu1 (trunc Δ X) P ≤ ENNReal.ofReal Δ := by
  have _ := hX; have _ := hΔ
  calc
    _ ≤ ∫⁻ _ : Ω, ENNReal.ofReal Δ ∂P := lintegral_mono fun _ => ENNReal.ofReal_le_ofReal (min_le_right _ _)
    _ = _ := by simp

omit [IsProbabilityMeasure P] in
theorem truncated_mean_tendsto (hX : IsRenewalProcess P X) :
    Tendsto (fun k : ℕ => mu1 (trunc (k+1 : ℝ) X) P) atTop (𝓝 (mu1 X P)) := by
  apply lintegral_tendsto_of_tendsto_of_monotone
  · intro k
    exact ((hX.measurable 0).min measurable_const).ennreal_ofReal.aemeasurable
  · exact Filter.Eventually.of_forall fun ω i j hij =>
      ENNReal.ofReal_le_ofReal (min_le_min_left _ (by exact_mod_cast Nat.add_le_add_right hij 1))
  · apply Filter.Eventually.of_forall
    intro ω
    obtain ⟨k, hk⟩ := exists_nat_gt (X 0 ω)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop k] with j hj
    change ENNReal.ofReal (X 0 ω) = ENNReal.ofReal (min (X 0 ω) (j+1 : ℝ))
    have hkj : (k : ℝ) ≤ j := by exact_mod_cast hj
    rw [min_eq_left (by linarith)]

end RenewalProof

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology BigOperators Classical
open SmithRenewal.Elementary

namespace RenewalProof

section Deterministic
variable {Ω : Type*} {X : ℕ → Ω → ℝ}

theorem sum_monotone (hn : ∀ i ω, 0 ≤ X i ω) (ω : Ω) :
    Monotone (fun n => S X n ω) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [S, Finset.sum_range_succ]
  exact le_add_of_nonneg_right (hn n ω)

theorem stopped_prefix_eq (hn : ∀ i ω, 0 ≤ X i ω) {t : ℝ} {m : ℕ}
    {ω : Ω} (hm : S X m ω ≤ t) :
    (∑ i ∈ Finset.range m, if S X i ω ≤ t then X i ω else 0) = S X m ω := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [if_pos (((sum_monotone hn ω) (Finset.mem_range.mp hi).le).trans hm)]

theorem stopped_prefix_upper (hn : ∀ i ω, 0 ≤ X i ω) {t Δ : ℝ}
    (hb : ∀ i ω, X i ω ≤ Δ) (ht : 0 ≤ t) (hΔ : 0 ≤ Δ) (m : ℕ) (ω : Ω) :
    (∑ i ∈ Finset.range m, if S X i ω ≤ t then X i ω else 0) ≤ t + Δ := by
  induction m with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; linarith
  | succ m ih =>
    rw [Finset.sum_range_succ]
    by_cases hm : S X m ω ≤ t
    · rw [if_pos hm, stopped_prefix_eq hn hm]
      linarith [hb m ω]
    · rw [if_neg hm, add_zero]
      exact ih

theorem stopped_prefix_ofReal (hn : ∀ i ω, 0 ≤ X i ω) (t : ℝ) (m : ℕ) (ω : Ω) :
    (∑ i ∈ Finset.range m, ENNReal.ofReal (X i ω) *
      (if S X i ω ≤ t then 1 else 0)) =
      ENNReal.ofReal (∑ i ∈ Finset.range m, if S X i ω ≤ t then X i ω else 0) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by
    split_ifs
    · exact hn i ω
    · exact le_rfl)]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

theorem reward_bounded (hn : ∀ i ω, 0 ≤ X i ω) {t Δ : ℝ}
    (hb : ∀ i ω, X i ω ≤ Δ) (ht : 0 ≤ t) (hΔ : 0 ≤ Δ) (ω : Ω) :
    reward X t ω ≤ ENNReal.ofReal (t + Δ) := by
  rw [reward, ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro m
  rw [stopped_prefix_ofReal hn]
  exact ENNReal.ofReal_le_ofReal (stopped_prefix_upper hn hb ht hΔ m ω)

theorem reward_lower_of_occupancy_finite (hn : ∀ i ω, 0 ≤ X i ω) {t : ℝ}
    {ω : Ω} (hfinite : occupancy X t ω ≠ ∞) :
    ENNReal.ofReal t ≤ reward X t ω := by
  have hex : ∃ m, t < S X m ω := by
    by_contra h
    push Not at h
    have he : occupancy X t ω = ∞ := by
      simp [occupancy, h]
    exact hfinite he
  let m := Nat.find hex
  have hm : t < S X m ω := Nat.find_spec hex
  have hbefore : ∀ i < m, S X i ω ≤ t := fun i hi => le_of_not_gt (Nat.find_min hex hi)
  have he : (∑ i ∈ Finset.range m, if S X i ω ≤ t then X i ω else 0) = S X m ω := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [if_pos (hbefore i (Finset.mem_range.mp hi))]
  calc
    ENNReal.ofReal t ≤ ENNReal.ofReal (S X m ω) := ENNReal.ofReal_le_ofReal hm.le
    _ = ∑ i ∈ Finset.range m, ENNReal.ofReal (X i ω) *
        (if S X i ω ≤ t then 1 else 0) := by rw [stopped_prefix_ofReal hn, he]
    _ ≤ reward X t ω := ENNReal.sum_le_tsum (Finset.range m)
end Deterministic

section Probability
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ}

theorem bounded_mean_count (hX : IsRenewalProcess P X) {t Δ : ℝ}
    (hb : ∀ i ω, X i ω ≤ Δ) (ht : 0 ≤ t) (hΔ : 0 ≤ Δ) :
    mu1 X P * (1 + H X P t) ≤ ENNReal.ofReal (t + Δ) := by
  rw [← integral_reward hX ht]
  calc
    _ ≤ ∫⁻ _ : Ω, ENNReal.ofReal (t + Δ) ∂P :=
      lintegral_mono (reward_bounded hX.nonneg hb ht hΔ)
    _ = _ := by simp

theorem truncation_upper (hX : IsRenewalProcess P X) {t Δ : ℝ}
    (ht : 0 ≤ t) (hΔ : 0 < Δ) :
    H X P t ≤ ENNReal.ofReal (t + Δ) / mu1 (trunc Δ X) P := by
  have hy := trunc_process hX hΔ
  have hm := mean_pos hy
  have hmfin : mu1 (trunc Δ X) P ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (truncated_mean_le hX hΔ)
  have hbound := bounded_mean_count hy (fun _ _ => min_le_right _ _) ht hΔ.le
  apply (H_trunc_le hX hΔ t).trans
  apply (ENNReal.le_div_iff_mul_le (Or.inl hm.ne') (Or.inl hmfin)).mpr
  calc
    H (trunc Δ X) P t * mu1 (trunc Δ X) P ≤
        (1 + H (trunc Δ X) P t) * mu1 (trunc Δ X) P :=
      by rw [add_mul, one_mul]; exact le_add_left le_rfl
    _ ≤ _ := by simpa only [mul_comm] using hbound

theorem finite_H (hX : IsRenewalProcess P X) {t : ℝ} (ht : 0 ≤ t) :
    H X P t ≠ ∞ := by
  apply ne_top_of_le_ne_top _ (truncation_upper hX ht (show (0 : ℝ) < 1 by norm_num))
  exact ENNReal.div_ne_top ENNReal.ofReal_ne_top (mean_pos (trunc_process hX zero_lt_one)).ne'

theorem lower_bound (hX : IsRenewalProcess P X) {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal t ≤ mu1 X P * (1 + H X P t) := by
  have hint : (∫⁻ ω, occupancy X t ω ∂P) ≠ ∞ := by
    rw [integral_occupancy hX ht]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, finite_H hX ht⟩
  have hae : ∀ᵐ ω ∂P, ENNReal.ofReal t ≤ reward X t ω := by
    filter_upwards [ae_lt_top (measurable_occupancy hX t) hint] with ω hω
    exact reward_lower_of_occupancy_finite hX.nonneg hω.ne
  calc
    _ = ∫⁻ _ : Ω, ENNReal.ofReal t ∂P := by simp
    _ ≤ ∫⁻ ω, reward X t ω ∂P := lintegral_mono_ae hae
    _ = _ := integral_reward hX ht

end Probability
end RenewalProof

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology BigOperators Classical
open SmithRenewal.Elementary

namespace RenewalProof

theorem real_ratio_squeeze (u : ℝ → ℝ) (a : ℝ) (v b : ℕ → ℝ)
    (hv : Tendsto v atTop (𝓝 a))
    (hlo : ∀ t : ℝ, 0 < t → a - 1/t ≤ u t)
    (hhi : ∀ k (t : ℝ), 0 < t → u t ≤ v k + b k / t) :
    Tendsto u atTop (𝓝 a) := by
  apply tendsto_order.mpr
  constructor
  · intro c hc
    have hl : Tendsto (fun t : ℝ => a - 1/t) atTop (𝓝 a) := by
      simpa using tendsto_const_nhds.sub (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0))
    filter_upwards [(tendsto_order.mp hl).1 c hc, eventually_gt_atTop (0 : ℝ)] with t ht ht0
    exact ht.trans_le (hlo t ht0)
  · intro c hc
    obtain ⟨k, hk⟩ := ((tendsto_order.mp hv).2 c hc).exists
    have hu : Tendsto (fun t : ℝ => v k + b k / t) atTop (𝓝 (v k)) := by
      simpa [div_eq_mul_inv] using tendsto_const_nhds.add
        (tendsto_const_nhds.mul (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0)))
    filter_upwards [(tendsto_order.mp hu).2 c hk, eventually_gt_atTop (0 : ℝ)] with t ht ht0
    exact (hhi k t ht0).trans_lt ht

theorem ennreal_ratio_limit (h : ℝ → ℝ≥0∞) (μ : ℝ≥0∞) (m : ℕ → ℝ≥0∞)
    (hμ : 0 < μ) (hm : ∀ k, 0 < m k) (hmfin : ∀ k, m k ≠ ∞)
    (hmt : Tendsto m atTop (𝓝 μ))
    (hf : ∀ t, 0 ≤ t → h t ≠ ∞)
    (hlo : ∀ t, 0 ≤ t → ENNReal.ofReal t ≤ μ * (1 + h t))
    (hhi : ∀ (k : ℕ) (t : ℝ), 0 ≤ t → h t ≤ ENNReal.ofReal (t + (k+1 : ℝ)) / m k) :
    Tendsto (fun t : ℝ => h t / ENNReal.ofReal t) atTop (𝓝 μ⁻¹) := by
  let a := (μ⁻¹).toReal
  let v := fun k => ((m k)⁻¹).toReal
  have hifin : μ⁻¹ ≠ ∞ := by simp [hμ.ne']
  have hv : Tendsto v atTop (𝓝 a) :=
    (ENNReal.tendsto_toReal hifin).comp (tendsto_inv_iff.mpr hmt)
  have hu : Tendsto (fun t : ℝ => (h t).toReal / t) atTop (𝓝 a) := by
    apply real_ratio_squeeze _ a v (fun k => (k+1 : ℝ) * v k) hv
    · intro t ht
      by_cases htop : μ = ∞
      · simp only [a, htop, ENNReal.inv_top, ENNReal.toReal_zero, zero_sub]
        exact (neg_nonpos.mpr (by positivity)).trans (by positivity)
      · have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top htop (by simp [hf t ht.le])) (hlo t ht.le)
        have hmpos : 0 < μ.toReal := ENNReal.toReal_pos hμ.ne' htop
        simp only [ENNReal.toReal_ofReal ht.le, ENNReal.toReal_mul,
          ENNReal.toReal_add ENNReal.one_ne_top (hf t ht.le), ENNReal.toReal_one] at hh
        change (μ⁻¹).toReal - 1 / t ≤ (h t).toReal / t
        rw [ENNReal.toReal_inv]
        have hh1 : t / μ.toReal ≤ 1 + (h t).toReal :=
          (div_le_iff₀ hmpos).mpr (by nlinarith [hh])
        have hh2 := div_le_div_of_nonneg_right hh1 ht.le
        have he : (t / μ.toReal) / t = μ.toReal⁻¹ := by field_simp
        rw [he, add_div] at hh2
        linarith
    · intro k t ht
      have hkr : 0 ≤ (k+1 : ℝ) := by positivity
      have hh := ENNReal.toReal_mono (ENNReal.div_ne_top ENNReal.ofReal_ne_top (hm k).ne') (hhi k t ht.le)
      simp only [ENNReal.toReal_div, ENNReal.toReal_ofReal (le_of_lt (add_pos_of_pos_of_nonneg ht hkr))] at hh
      have hmpos : 0 < (m k).toReal := ENNReal.toReal_pos (hm k).ne' (hmfin k)
      have hdiv := (div_le_div_of_nonneg_right hh ht.le)
      dsimp [v]
      rw [ENNReal.toReal_inv]
      calc
        (h t).toReal / t ≤ (t + (k+1 : ℝ)) / (m k).toReal / t := hdiv
        _ = (m k).toReal⁻¹ + (k+1 : ℝ) * (m k).toReal⁻¹ / t := by
          field_simp
  have hout := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hu
  have ha : ENNReal.ofReal a = μ⁻¹ := ENNReal.ofReal_toReal hifin
  rw [ha] at hout
  apply hout.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  change ENNReal.ofReal ((h t).toReal / t) = h t / ENNReal.ofReal t
  rw [ENNReal.ofReal_div_of_pos ht, ENNReal.ofReal_toReal (hf t ht.le)]

end RenewalProof

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SmithRenewal.Elementary

/-- The elementary renewal theorem (Smith, *Renewal Theory and Its Ramifications*, J. R. Statist. Soc. B 20(2):243–283 (1958), §1.2, p. 246, unnumbered display): "H(t)/t → μ₁⁻¹ as
t → ∞, where μ₁ = EX_i ≤ ∞, and the limit μ₁⁻¹ is interpreted as zero if μ₁ = ∞."

Formalization Note: `H(t) = E N_t` and `μ₁ = E X_i` are lower integrals in `[0, ∞]`, the ratio
is `H(t) / ofReal t` in `[0, ∞]` and the limit `μ₁⁻¹` is the inverse in `[0, ∞]`, so
`∞⁻¹ = 0` is exactly the paper's convention. No hypothesis on `μ₁` is made (`μ₁ > 0` follows
from `P {X_i = 0} < 1`). -/
theorem elementary_renewal_theorem {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hX : IsRenewalProcess P X) :
    Tendsto (fun t : ℝ => H X P t / ENNReal.ofReal t) atTop (𝓝 (mu1 X P)⁻¹) := by
  apply RenewalProof.ennreal_ratio_limit (H X P) (mu1 X P)
    (fun k : ℕ => mu1 (trunc (k+1 : ℝ) X) P) (RenewalProof.mean_pos hX)
  · intro k; exact RenewalProof.mean_pos (RenewalProof.trunc_process hX (by positivity))
  · intro k
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (RenewalProof.truncated_mean_le hX (by positivity))
  · exact RenewalProof.truncated_mean_tendsto hX
  · intro t ht; exact RenewalProof.finite_H hX ht
  · intro t ht; exact RenewalProof.lower_bound hX ht
  · intro k t ht; exact RenewalProof.truncation_upper hX ht (by positivity)

end SmithRenewal.Elementary

open SmithRenewal.Elementary
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hX : IsRenewalProcess P X) :
    Tendsto (fun t : ℝ => H X P t / ENNReal.ofReal t) atTop (𝓝 (mu1 X P)⁻¹) :=
  SmithRenewal.Elementary.elementary_renewal_theorem P X hX
