-- Prove2me | solution 1 for PalmQueueing.Loynes.loynes_stability
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T04:50:04.334039+00:00
-- url     : https://prove2.me/submissions/8ea9de17-7f38-457b-b389-4fb927f019fa

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess
import Definitions.Def_PalmQueueing_Loynes_SingleServerQueue
import Definitions.Def_PalmQueueing_Loynes_StationaryRegime
import Theorems.Thm_PalmQueueing_Loynes_ergodic_lemma
import Theorems.Thm_PalmQueueing_Loynes_queueing_ergodic_theorem

open MeasureTheory Filter Topology
open scoped ENNReal
open PalmQueueing.Palm
open PalmQueueing.Loynes

namespace LoynesRootProof

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Part 1: Flow and PointProcess shift identities -/

lemma flow_zero_apply (θ : Flow Ω) (ω : Ω) : θ 0 ω = ω := by
  have := congrFun θ.map_zero ω
  exact this

lemma flow_add_apply (θ : Flow Ω) (s t : ℝ) (ω : Ω) : θ (s + t) ω = θ s (θ t ω) := by
  have := congrFun (θ.map_add s t) ω
  exact this

lemma flow_neg_cancel (θ : Flow Ω) (t : ℝ) (ω : Ω) : θ (-t) (θ t ω) = ω := by
  rw [← flow_add_apply, neg_add_cancel, flow_zero_apply]

lemma flow_cancel_neg (θ : Flow Ω) (t : ℝ) (ω : Ω) : θ t (θ (-t) ω) = ω := by
  rw [← flow_add_apply, add_neg_cancel, flow_zero_apply]

lemma exists_unique_interval (N : PointProcess Ω) (t : ℝ) (ω : Ω) :
    ∃! k : ℤ, N.T k ω ≤ t ∧ t < N.T (k + 1) ω := by
  have htop := (N.tendsto_atTop ω).eventually (eventually_gt_atTop t)
  have hbot := (N.tendsto_atBot ω).eventually (eventually_le_atBot t)
  rw [Filter.eventually_atTop] at htop
  rw [Filter.eventually_atBot] at hbot
  obtain ⟨b, hb⟩ := htop
  obtain ⟨a, ha⟩ := hbot
  have hab : a ≤ b := by
    by_contra h
    push Not at h
    have h1 : N.T a ω ≤ t := ha a le_rfl
    have h2 : t < N.T b ω := hb b le_rfl
    have h3 : N.T b ω < N.T a ω := N.strictMono ω h
    linarith
  have hex : ∃ k : ℤ, N.T k ω ≤ t ∧ t < N.T (k + 1) ω := by
    let S : Finset ℤ := (Finset.Icc a b).filter (fun k => N.T k ω ≤ t)
    have hS : S.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hab⟩, ha a le_rfl⟩⟩
    let k := S.max' hS
    have hk_mem : k ∈ S := Finset.max'_mem S hS
    have hk_le : N.T k ω ≤ t := (Finset.mem_filter.mp hk_mem).2
    have hk_lt_b : k < b := by
      have hk_le_b : k ≤ b := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk_mem).1).2
      rcases lt_or_eq_of_le hk_le_b with hlt | heq
      · exact hlt
      · exfalso
        have := hb b le_rfl
        rw [heq] at hk_le
        linarith
    have hk1_gt : t < N.T (k + 1) ω := by
      by_contra h
      push Not at h
      have hk1_mem : k + 1 ∈ S := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, h⟩
        · have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk_mem).1).1
          omega
        · omega
      have := Finset.le_max' S (k + 1) hk1_mem
      omega
    exact ⟨k, hk_le, hk1_gt⟩
  obtain ⟨k, hk⟩ := hex
  refine ⟨k, hk, fun m hm => ?_⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hm1 : m + 1 ≤ k := by omega
    have : N.T (m + 1) ω ≤ N.T k ω := (N.strictMono ω).monotone hm1
    linarith [hk.1, hm.2]
  · have hk1 : k + 1 ≤ m := by omega
    have : N.T (k + 1) ω ≤ N.T m ω := (N.strictMono ω).monotone hk1
    linarith [hk.2, hm.1]

noncomputable def idx (N : PointProcess Ω) (t : ℝ) (ω : Ω) : ℤ :=
  (exists_unique_interval N t ω).choose

lemma idx_spec (N : PointProcess Ω) (t : ℝ) (ω : Ω) :
    N.T (idx N t ω) ω ≤ t ∧ t < N.T (idx N t ω + 1) ω :=
  (exists_unique_interval N t ω).choose_spec.1

lemma idx_unique (N : PointProcess Ω) (t : ℝ) (ω : Ω) {k : ℤ}
    (h1 : N.T k ω ≤ t) (h2 : t < N.T (k + 1) ω) : idx N t ω = k :=
  ((exists_unique_interval N t ω).choose_spec.2 k ⟨h1, h2⟩).symm

lemma idx_T (N : PointProcess Ω) (k : ℤ) (ω : Ω) : idx N (N.T k ω) ω = k :=
  idx_unique N (N.T k ω) ω le_rfl (N.strictMono ω (by omega))

lemma count_singleton_eq_one_iff (N : PointProcess Ω) (ω : Ω) (x : ℝ) :
    N.count ω {x} = 1 ↔ ∃ m : ℤ, N.T m ω = x := by
  rw [PointProcess.count, Measure.sum_apply _ (measurableSet_singleton x)]
  constructor
  · intro h
    by_contra hall
    push Not at hall
    have h0 : (∑' n : ℤ, Measure.dirac (N.T n ω) {x}) = 0 := by
      refine ENNReal.tsum_eq_zero.mpr fun n => ?_
      rw [Measure.dirac_apply' _ (measurableSet_singleton x)]
      simp [hall n]
    rw [h0] at h
    exact zero_ne_one h
  · rintro ⟨m, hm⟩
    rw [tsum_eq_single m]
    · rw [Measure.dirac_apply' _ (measurableSet_singleton x)]
      simp [hm]
    · intro n hnm
      rw [Measure.dirac_apply' _ (measurableSet_singleton x)]
      have hne : N.T n ω ≠ x := by
        rw [← hm]
        exact (N.strictMono ω).injective.ne hnm
      simp [hne]

lemma range_T_shift (N : PointProcess Ω) (θ : Flow Ω) (hcomp : N.Compatible θ)
    (t : ℝ) (ω : Ω) (x : ℝ) :
    (∃ n : ℤ, N.T n (θ t ω) = x) ↔ (∃ m : ℤ, N.T m ω - t = x) := by
  rw [← count_singleton_eq_one_iff, hcomp t ω {x} (measurableSet_singleton x)]
  have hpre : ((fun s : ℝ => s - t) ⁻¹' {x}) = {x + t} := by
    ext s; simp [sub_eq_iff_eq_add]
  rw [hpre, count_singleton_eq_one_iff]
  constructor
  · rintro ⟨m, hm⟩; exact ⟨m, by linarith⟩
  · rintro ⟨m, hm⟩; exact ⟨m, by linarith⟩

lemma strictMono_int_eq_of_same_range {f g : ℤ → ℝ}
    (hf : StrictMono f) (hg : StrictMono g)
    (hrange : ∀ x, (∃ n, f n = x) ↔ (∃ m, g m = x))
    (hf0 : f 0 ≤ 0) (hf1 : 0 < f 1) (hg0 : g 0 ≤ 0) (hg1 : 0 < g 1) :
    ∀ n : ℤ, f n = g n := by
  -- First show f 0 = g 0
  have h0 : f 0 = g 0 := by
    obtain ⟨m, hm⟩ : ∃ m, g m = f 0 := (hrange (f 0)).mp ⟨0, rfl⟩
    obtain ⟨n, hn⟩ : ∃ n, f n = g 0 := (hrange (g 0)).mpr ⟨0, rfl⟩
    have hm_le : m ≤ 0 := by
      by_contra h; push Not at h
      have : g 1 ≤ g m := hg.monotone (by omega)
      linarith
    have hn_le : n ≤ 0 := by
      by_contra h; push Not at h
      have : f 1 ≤ f n := hf.monotone (by omega)
      linarith
    have h1 : f 0 ≤ g 0 := by rw [← hm]; exact hg.monotone hm_le
    have h2 : g 0 ≤ f 0 := by rw [← hn]; exact hf.monotone hn_le
    linarith
  -- Helper: next element in range
  have hsucc : ∀ k : ℤ, f k = g k → f (k + 1) = g (k + 1) := by
    intro k hk
    obtain ⟨m, hm⟩ : ∃ m, g m = f (k + 1) := (hrange (f (k + 1))).mp ⟨k + 1, rfl⟩
    obtain ⟨n, hn⟩ : ∃ n, f n = g (k + 1) := (hrange (g (k + 1))).mpr ⟨k + 1, rfl⟩
    have hkm : k < m := by
      by_contra h; push Not at h
      have : g m ≤ g k := hg.monotone h
      have : f k < f (k + 1) := hf (by omega)
      linarith
    have hkn : k < n := by
      by_contra h; push Not at h
      have : f n ≤ f k := hf.monotone h
      have : g k < g (k + 1) := hg (by omega)
      linarith
    have h1 : g (k + 1) ≤ f (k + 1) := by rw [← hm]; exact hg.monotone (by omega)
    have h2 : f (k + 1) ≤ g (k + 1) := by rw [← hn]; exact hf.monotone (by omega)
    linarith
  have hpred : ∀ k : ℤ, f k = g k → f (k - 1) = g (k - 1) := by
    intro k hk
    obtain ⟨m, hm⟩ : ∃ m, g m = f (k - 1) := (hrange (f (k - 1))).mp ⟨k - 1, rfl⟩
    obtain ⟨n, hn⟩ : ∃ n, f n = g (k - 1) := (hrange (g (k - 1))).mpr ⟨k - 1, rfl⟩
    have hmk : m < k := by
      by_contra h; push Not at h
      have : g k ≤ g m := hg.monotone h
      have : f (k - 1) < f k := hf (by omega)
      linarith
    have hnk : n < k := by
      by_contra h; push Not at h
      have : f k ≤ f n := hf.monotone h
      have : g (k - 1) < g k := hg (by omega)
      linarith
    have h1 : f (k - 1) ≤ g (k - 1) := by rw [← hm]; exact hg.monotone (by omega)
    have h2 : g (k - 1) ≤ f (k - 1) := by rw [← hn]; exact hf.monotone (by omega)
    linarith
  intro n
  induction n using Int.induction_on with
  | zero => exact h0
  | succ i ih => exact hsucc i ih
  | pred i ih => exact hpred (-i) ih

lemma T_shift (N : PointProcess Ω) (θ : Flow Ω) (hcomp : N.Compatible θ)
    (t : ℝ) (ω : Ω) (n : ℤ) :
    N.T n (θ t ω) = N.T (n + idx N t ω) ω - t := by
  let k := idx N t ω
  have hk := idx_spec N t ω
  refine strictMono_int_eq_of_same_range
    (f := fun m => N.T m (θ t ω)) (g := fun m => N.T (m + k) ω - t)
    (N.strictMono (θ t ω)) ?_ ?_ (N.zero_le _) (N.lt_one _) ?_ ?_ n
  · intro a b hab
    exact sub_lt_sub_right (N.strictMono ω (by omega)) t
  · intro x
    rw [range_T_shift N θ hcomp t ω x]
    constructor
    · rintro ⟨m, hm⟩; exact ⟨m - k, by simpa [sub_add_cancel] using hm⟩
    · rintro ⟨m, hm⟩; exact ⟨m + k, hm⟩
  · simp [k]; linarith [hk.1]
  · simp [k, add_comm]; linarith [hk.2]

lemma T_shift_T (N : PointProcess Ω) (θ : Flow Ω) (hcomp : N.Compatible θ)
    (n k : ℤ) (ω : Ω) :
    N.T n (θ (N.T k ω) ω) = N.T (n + k) ω - N.T k ω := by
  rw [T_shift N θ hcomp (N.T k ω) ω n, idx_T]

lemma T_zero_shift_T (N : PointProcess Ω) (θ : Flow Ω) (hcomp : N.Compatible θ)
    (k : ℤ) (ω : Ω) :
    N.T 0 (θ (N.T k ω) ω) = 0 := by
  rw [T_shift_T N θ hcomp 0 k ω, zero_add, sub_self]

lemma flow_T_zero_shift (N : PointProcess Ω) (θ : Flow Ω) (hcomp : N.Compatible θ)
    (t : ℝ) (ω : Ω) :
    θ (N.T 0 (θ t ω)) (θ t ω) = θ (N.T (idx N t ω) ω) ω := by
  rw [T_shift N θ hcomp t ω 0, zero_add, ← flow_add_apply, sub_add_cancel]

lemma sigma_shift (Q : Queue Ω) (t : ℝ) (ω : Ω) (n : ℤ) :
    Q.sigma n (Q.toPalmSetting.θ t ω) = Q.sigma (n + idx Q.toPalmSetting.N t ω) ω := by
  let θ := Q.toPalmSetting.θ
  let N := Q.toPalmSetting.N
  have h1 : Q.sigma n (θ (N.T 0 (θ t ω)) (θ t ω)) = Q.sigma n (θ t ω) := by
    have := Q.sigma_marks.2 n 0 (θ t ω)
    simpa using this
  have h2 : Q.sigma n (θ (N.T (idx N t ω) ω) ω) = Q.sigma (n + idx N t ω) ω :=
    Q.sigma_marks.2 n (idx N t ω) ω
  rw [← h1, flow_T_zero_shift N θ Q.toPalmSetting.compatible t ω, h2]

lemma tau_shift (Q : Queue Ω) (t : ℝ) (ω : Ω) (n : ℤ) :
    Q.tau n (Q.toPalmSetting.θ t ω) = Q.tau (n + idx Q.toPalmSetting.N t ω) ω := by
  simp only [Queue.tau, T_shift Q.toPalmSetting.N Q.toPalmSetting.θ Q.toPalmSetting.compatible]
  have h : n + 1 + idx Q.toPalmSetting.N t ω = n + idx Q.toPalmSetting.N t ω + 1 := by omega
  rw [h]; ring

lemma tau_shift_T (Q : Queue Ω) (n k : ℤ) (ω : Ω) :
    Q.tau n (Q.toPalmSetting.θ (Q.toPalmSetting.N.T k ω) ω) = Q.tau (n + k) ω := by
  rw [tau_shift, idx_T]

lemma tau_pos (Q : Queue Ω) (n : ℤ) (ω : Ω) : 0 < Q.tau n ω := by
  simp only [Queue.tau]
  linarith [Q.toPalmSetting.N.strictMono ω (show n < n + 1 by omega)]

/-! ### Part 2: Palm probability, Palm shift, invariance, ergodicity, and E⁰[τ₀] = 1/λ -/

def zeroSet (N : PointProcess Ω) : Set Ω := {ω | N.T 0 ω = 0}

lemma measurableSet_zeroSet (N : PointProcess Ω) : MeasurableSet (zeroSet N) :=
  measurableSet_eq_fun (N.measurable_T 0) measurable_const

lemma measurable_flow_T (θ : Flow Ω) (N : PointProcess Ω) (k : ℤ) :
    Measurable (fun ω => θ (N.T k ω) ω) :=
  θ.measurable_uncurry.comp ((N.measurable_T k).prodMk measurable_id)

lemma P0_zeroSet (PS : PalmSetting Ω) : PS.P0 (zeroSet PS.N) = 1 := by
  have := PS.palm.1
  have hpalm := PS.palm.2 (zeroSet PS.N) (measurableSet_zeroSet PS.N) 1 one_pos
  have hsum : ∀ ω, (∑' n : ℤ,
      Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ≥0∞)) (PS.N.T n ω) *
      Set.indicator (zeroSet PS.N) (fun _ => (1 : ℝ≥0∞)) (PS.θ (PS.N.T n ω) ω)) =
      PS.N.count ω (Set.Ioc (0 : ℝ) 1) := by
    intro ω
    rw [PointProcess.count, Measure.sum_apply _ measurableSet_Ioc]
    refine tsum_congr fun n => ?_
    have hmem : PS.θ (PS.N.T n ω) ω ∈ zeroSet PS.N :=
      T_zero_shift_T PS.N PS.θ PS.compatible n ω
    rw [Set.indicator_of_mem hmem, mul_one, Measure.dirac_apply' _ measurableSet_Ioc]
    rfl
  simp_rw [hsum] at hpalm
  rw [mul_one, ← PS.intensity.2] at hpalm
  have hlam_ne0 : ENNReal.ofReal PS.lam ≠ 0 :=
    (ENNReal.ofReal_pos.mpr PS.intensity.1).ne'
  have hlam_ne_top : ENNReal.ofReal PS.lam ≠ ⊤ := ENNReal.ofReal_ne_top
  exact (ENNReal.mul_eq_left hlam_ne0 hlam_ne_top).mp hpalm

lemma ae_P0_zeroSet (PS : PalmSetting Ω) : ∀ᵐ ω ∂PS.P0, PS.N.T 0 ω = 0 := by
  have := PS.palm.1
  rw [ae_iff]
  have hcompl : {ω | ¬ PS.N.T 0 ω = 0} = (zeroSet PS.N)ᶜ := rfl
  rw [hcompl, prob_compl_eq_zero_iff (measurableSet_zeroSet PS.N)]
  exact P0_zeroSet PS

noncomputable def palmShiftFun (θ : Flow Ω) (N : PointProcess Ω) (ω : Ω) : Ω :=
  if N.T 0 ω = 0 then θ (N.T 1 ω) ω else ω

noncomputable def palmShiftInvFun (θ : Flow Ω) (N : PointProcess Ω) (ω : Ω) : Ω :=
  if N.T 0 ω = 0 then θ (N.T (-1) ω) ω else ω

lemma palmShiftFun_left_inv (θ : Flow Ω) (N : PointProcess Ω) (hcomp : N.Compatible θ) (ω : Ω) :
    palmShiftInvFun θ N (palmShiftFun θ N ω) = ω := by
  unfold palmShiftFun palmShiftInvFun
  by_cases h0 : N.T 0 ω = 0
  · rw [if_pos h0, if_pos (T_zero_shift_T N θ hcomp 1 ω)]
    have hT : N.T (-1) (θ (N.T 1 ω) ω) = - N.T 1 ω := by
      rw [T_shift_T N θ hcomp (-1) 1 ω]
      simp [h0]
    rw [hT, flow_neg_cancel]
  · rw [if_neg h0, if_neg h0]

lemma palmShiftFun_right_inv (θ : Flow Ω) (N : PointProcess Ω) (hcomp : N.Compatible θ) (ω : Ω) :
    palmShiftFun θ N (palmShiftInvFun θ N ω) = ω := by
  unfold palmShiftFun palmShiftInvFun
  by_cases h0 : N.T 0 ω = 0
  · rw [if_pos h0, if_pos (T_zero_shift_T N θ hcomp (-1) ω)]
    have hT : N.T 1 (θ (N.T (-1) ω) ω) = - N.T (-1) ω := by
      rw [T_shift_T N θ hcomp 1 (-1) ω]
      simp [h0]
    rw [hT, flow_neg_cancel]
  · rw [if_neg h0, if_neg h0]

noncomputable def palmShift (PS : PalmSetting Ω) : Ω ≃ᵐ Ω where
  toFun := palmShiftFun PS.θ PS.N
  invFun := palmShiftInvFun PS.θ PS.N
  left_inv := palmShiftFun_left_inv PS.θ PS.N PS.compatible
  right_inv := palmShiftFun_right_inv PS.θ PS.N PS.compatible
  measurable_toFun := by
    unfold palmShiftFun
    exact Measurable.ite (measurableSet_zeroSet PS.N) (measurable_flow_T PS.θ PS.N 1) measurable_id
  measurable_invFun := by
    unfold palmShiftInvFun
    exact Measurable.ite (measurableSet_zeroSet PS.N) (measurable_flow_T PS.θ PS.N (-1)) measurable_id

lemma palmShift_apply_of_zero (PS : PalmSetting Ω) {ω : Ω} (h0 : PS.N.T 0 ω = 0) :
    palmShift PS ω = PS.θ (PS.N.T 1 ω) ω := by
  change palmShiftFun PS.θ PS.N ω = _
  unfold palmShiftFun
  rw [if_pos h0]

lemma palmShift_symm_apply_of_zero (PS : PalmSetting Ω) {ω : Ω} (h0 : PS.N.T 0 ω = 0) :
    (palmShift PS).symm ω = PS.θ (PS.N.T (-1) ω) ω := by
  change palmShiftInvFun PS.θ PS.N ω = _
  unfold palmShiftInvFun
  rw [if_pos h0]

lemma palmShift_iterate_of_zero (PS : PalmSetting Ω) {ω : Ω} (h0 : PS.N.T 0 ω = 0) :
    ∀ k : ℕ, (palmShift PS)^[k] ω = PS.θ (PS.N.T k ω) ω := by
  intro k
  induction k with
  | zero => simp [h0, flow_zero_apply]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    have hk0 : PS.N.T 0 (PS.θ (PS.N.T k ω) ω) = 0 := T_zero_shift_T PS.N PS.θ PS.compatible k ω
    rw [palmShift_apply_of_zero PS hk0, T_shift_T PS.N PS.θ PS.compatible 1 k ω,
        ← flow_add_apply, sub_add_cancel]
    congr 2; omega

lemma palmShift_symm_iterate_of_zero (PS : PalmSetting Ω) {ω : Ω} (h0 : PS.N.T 0 ω = 0) :
    ∀ k : ℕ, ((palmShift PS).symm)^[k] ω = PS.θ (PS.N.T (-k : ℤ) ω) ω := by
  intro k
  induction k with
  | zero => simp [h0, flow_zero_apply]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    have hk0 : PS.N.T 0 (PS.θ (PS.N.T (-k : ℤ) ω) ω) = 0 :=
      T_zero_shift_T PS.N PS.θ PS.compatible (-k : ℤ) ω
    rw [palmShift_symm_apply_of_zero PS hk0, T_shift_T PS.N PS.θ PS.compatible (-1) (-k : ℤ) ω,
        ← flow_add_apply, sub_add_cancel]
    congr 2; omega

lemma indicator_one_le {α : Type*} (s : Set α) (x : α) :
    Set.indicator s (fun _ => (1 : ℝ≥0∞)) x ≤ 1 := by
  by_cases h : x ∈ s <;> simp [h]

/-- Campbell's formula for nonnegative measurable functions `f : Ω → ℝ≥0∞`,
directly from `IsPalmProbability` via simple function approximation. -/
lemma palm_lintegral (PS : PalmSetting Ω) {f : Ω → ℝ≥0∞} (hf : Measurable f) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (PS.lam * t) * ∫⁻ ω, f ω ∂PS.P0 =
      ∫⁻ ω, ∑' n : ℤ,
        Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T n ω) *
        f (PS.θ (PS.N.T n ω) ω) ∂PS.P := by
  -- First prove for SimpleFunc
  have hsf : ∀ g : SimpleFunc Ω ℝ≥0∞,
      ENNReal.ofReal (PS.lam * t) * ∫⁻ ω, g ω ∂PS.P0 =
        ∫⁻ ω, ∑' n : ℤ,
          Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T n ω) *
          g (PS.θ (PS.N.T n ω) ω) ∂PS.P := by
    intro g
    refine SimpleFunc.induction ?_ ?_ g
    · intro c s hs
      have hpw : ∀ x, (SimpleFunc.piecewise s hs (SimpleFunc.const Ω c) (SimpleFunc.const Ω 0) : SimpleFunc Ω ℝ≥0∞) x =
          c * Set.indicator s (fun _ => (1 : ℝ≥0∞)) x := by
        intro x
        by_cases hx : x ∈ s
        · rw [SimpleFunc.piecewise_apply, if_pos hx, Set.indicator_of_mem hx, mul_one]; rfl
        · rw [SimpleFunc.piecewise_apply, if_neg hx, Set.indicator_of_notMem hx, mul_zero]; rfl
      have hLHS : ∫⁻ ω, (SimpleFunc.piecewise s hs (SimpleFunc.const Ω c) (SimpleFunc.const Ω 0) : SimpleFunc Ω ℝ≥0∞) ω ∂PS.P0 =
          ∫⁻ ω, c * Set.indicator s (fun _ => (1 : ℝ≥0∞)) ω ∂PS.P0 :=
        lintegral_congr hpw
      have hRHS : ∫⁻ ω, ∑' n : ℤ,
            Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T n ω) *
            (SimpleFunc.piecewise s hs (SimpleFunc.const Ω c) (SimpleFunc.const Ω 0) : SimpleFunc Ω ℝ≥0∞) (PS.θ (PS.N.T n ω) ω) ∂PS.P =
          ∫⁻ ω, ∑' n : ℤ,
            Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T n ω) *
            (c * Set.indicator s (fun _ => (1 : ℝ≥0∞)) (PS.θ (PS.N.T n ω) ω)) ∂PS.P :=
        lintegral_congr fun ω => tsum_congr fun n => by rw [hpw]
      rw [hLHS, hRHS]
      rw [lintegral_const_mul _ (measurable_const.indicator hs), ← mul_assoc,
          mul_comm (ENNReal.ofReal (PS.lam * t)) c, mul_assoc]
      have hind_eq : (∫⁻ ω, Set.indicator s (fun _ => (1 : ℝ≥0∞)) ω ∂PS.P0) = PS.P0 s :=
        lintegral_indicator_one hs
      rw [hind_eq, PS.palm.2 s hs t ht]
      rw [← lintegral_const_mul]
      · refine lintegral_congr fun ω => ?_
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun n => ?_
        ring
      · refine Measurable.tsum fun n => ?_
        exact (measurable_const.indicator measurableSet_Ioc |>.comp (PS.N.measurable_T n)).mul
          ((measurable_const.indicator hs).comp (measurable_flow_T PS.θ PS.N n))
    · intro g1 g2 hdisj ih1 ih2
      simp only [SimpleFunc.coe_add, Pi.add_apply]
      rw [lintegral_add_left g1.measurable, mul_add, ih1, ih2]
      rw [← lintegral_add_left]
      · refine lintegral_congr fun ω => ?_
        rw [← ENNReal.tsum_add]
        refine tsum_congr fun n => ?_
        ring
      · refine Measurable.tsum fun n => ?_
        exact (measurable_const.indicator measurableSet_Ioc |>.comp (PS.N.measurable_T n)).mul
          (g1.measurable.comp (measurable_flow_T PS.θ PS.N n))
  -- Now approximate f by SimpleFunc.eapprox
  have hmono : Monotone (SimpleFunc.eapprox f) := SimpleFunc.monotone_eapprox f
  have hsup : ∀ ω, (⨆ k, (SimpleFunc.eapprox f k : Ω → ℝ≥0∞) ω) = f ω :=
    fun ω => SimpleFunc.iSup_eapprox_apply hf ω
  have hLHS : ENNReal.ofReal (PS.lam * t) * ∫⁻ ω, f ω ∂PS.P0 =
      ⨆ k, ENNReal.ofReal (PS.lam * t) * ∫⁻ ω, SimpleFunc.eapprox f k ω ∂PS.P0 := by
    rw [← ENNReal.mul_iSup]
    congr 1
    rw [← lintegral_iSup (fun k => (SimpleFunc.eapprox f k).measurable) hmono]
    exact lintegral_congr fun ω => (hsup ω).symm
  rw [hLHS]
  simp_rw [hsf]
  rw [← lintegral_iSup]
  · refine lintegral_congr fun ω => ?_
    rw [ENNReal.tsum_eq_iSup_sum]
    have hswap : (⨆ k : ℕ, ∑' n : ℤ,
        Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T n ω) *
        SimpleFunc.eapprox f k (PS.θ (PS.N.T n ω) ω)) =
        ∑' n : ℤ, ⨆ k : ℕ,
        Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T n ω) *
        SimpleFunc.eapprox f k (PS.θ (PS.N.T n ω) ω) := by
      rw [ENNReal.tsum_eq_iSup_sum]
      simp_rw [ENNReal.tsum_eq_iSup_sum]
      rw [iSup_comm]
      refine iSup_congr fun s => ?_
      clear hLHS hsf
      induction s using Finset.induction with
      | empty => simp
      | insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        rw [← ih]
        refine le_antisymm ?_ ?_
        · refine iSup_le fun k => add_le_add ?_ ?_
          · exact le_iSup (fun i : ℕ =>
              Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T a ω) *
              SimpleFunc.eapprox f i (PS.θ (PS.N.T a ω) ω)) k
          · exact le_iSup (fun i : ℕ =>
              ∑ n ∈ s, Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T n ω) *
              SimpleFunc.eapprox f i (PS.θ (PS.N.T n ω) ω)) k
        · rw [ENNReal.iSup_add]
          refine iSup_le fun k1 => ?_
          rw [ENNReal.add_iSup]
          refine iSup_le fun k2 => ?_
          refine le_iSup_of_le (max k1 k2) ?_
          refine add_le_add ?_ ?_
          · exact mul_le_mul_right (hmono (le_max_left k1 k2) _) _
          · exact Finset.sum_le_sum fun n _ => mul_le_mul_right (hmono (le_max_right k1 k2) _) _
    rw [hswap, ENNReal.tsum_eq_iSup_sum]
    refine iSup_congr fun s => Finset.sum_congr rfl fun n _ => ?_
    rw [← ENNReal.mul_iSup, hsup]
  · intro k
    refine Measurable.tsum fun n => ?_
    exact (measurable_const.indicator measurableSet_Ioc |>.comp (PS.N.measurable_T n)).mul
      ((SimpleFunc.eapprox f k).measurable.comp (measurable_flow_T PS.θ PS.N n))
  · intro k1 k2 hk ω
    exact ENNReal.tsum_le_tsum fun n => mul_le_mul_right (hmono hk _) _

lemma measurePreserving_palmShift (PS : PalmSetting Ω) :
    MeasurePreserving (palmShift PS) PS.P0 PS.P0 := by
  have := PS.isProb
  have := PS.palm.1
  refine ⟨(palmShift PS).measurable, ?_⟩
  ext A hA
  rw [Measure.map_apply (palmShift PS).measurable hA]
  -- For any t > 0, compare lam * t * P0 (S⁻¹' A) and lam * t * P0 A
  have hbound : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal (PS.lam * t) * PS.P0 (palmShift PS ⁻¹' A) ≤
        ENNReal.ofReal (PS.lam * t) * PS.P0 A + 1 ∧
      ENNReal.ofReal (PS.lam * t) * PS.P0 A ≤
        ENNReal.ofReal (PS.lam * t) * PS.P0 (palmShift PS ⁻¹' A) + 1 := by
    intro t ht
    have h1 := PS.palm.2 (palmShift PS ⁻¹' A) ((palmShift PS).measurable hA) t ht
    have h2 := PS.palm.2 A hA t ht
    -- Rewrite the integrand in h1 using S (θ (T n ω) ω) = θ (T (n+1) ω) ω
    have hrew : ∀ ω, (∑' n : ℤ,
        Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T n ω) *
        Set.indicator (palmShift PS ⁻¹' A) (fun _ => (1 : ℝ≥0∞)) (PS.θ (PS.N.T n ω) ω)) =
        ∑' m : ℤ,
        Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T (m - 1) ω) *
        Set.indicator A (fun _ => (1 : ℝ≥0∞)) (PS.θ (PS.N.T m ω) ω) := by
      intro ω
      rw [← (Equiv.subRight (1 : ℤ)).tsum_eq]
      refine tsum_congr fun m => ?_
      have hS : palmShift PS (PS.θ (PS.N.T (m - 1) ω) ω) = PS.θ (PS.N.T m ω) ω := by
        rw [palmShift_apply_of_zero PS (T_zero_shift_T PS.N PS.θ PS.compatible (m - 1) ω),
            T_shift_T PS.N PS.θ PS.compatible 1 (m - 1) ω, ← flow_add_apply, sub_add_cancel]
        congr 2; omega
      change Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T (m - 1) ω) *
          Set.indicator (palmShift PS ⁻¹' A) (fun _ => (1 : ℝ≥0∞)) (PS.θ (PS.N.T (m - 1) ω) ω) =
          Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T (m - 1) ω) *
          Set.indicator A (fun _ => (1 : ℝ≥0∞)) (PS.θ (PS.N.T m ω) ω)
      congr 1
      by_cases hx : PS.θ (PS.N.T m ω) ω ∈ A
      · have hx' : PS.θ (PS.N.T (m - 1) ω) ω ∈ palmShift PS ⁻¹' A := by
          change palmShift PS (PS.θ (PS.N.T (m - 1) ω) ω) ∈ A
          rwa [hS]
        rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx]
      · have hx' : PS.θ (PS.N.T (m - 1) ω) ω ∉ palmShift PS ⁻¹' A := by
          change palmShift PS (PS.θ (PS.N.T (m - 1) ω) ω) ∉ A
          rwa [hS]
        rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hx]
    simp_rw [hrew] at h1
    -- Pointwise comparison: the two tsums differ by at most 1
    have hle1 : ∀ ω, (∑' m : ℤ,
        Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T (m - 1) ω) *
        Set.indicator A (fun _ => (1 : ℝ≥0∞)) (PS.θ (PS.N.T m ω) ω)) ≤
        (∑' m : ℤ,
        Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T m ω) *
        Set.indicator A (fun _ => (1 : ℝ≥0∞)) (PS.θ (PS.N.T m ω) ω)) + 1 := by
      intro ω
      let k := idx PS.N t ω
      have hk := idx_spec PS.N t ω
      have hsplit : ∀ m : ℤ,
          Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T (m - 1) ω) *
          Set.indicator A (fun _ => (1 : ℝ≥0∞)) (PS.θ (PS.N.T m ω) ω) ≤
          Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T m ω) *
          Set.indicator A (fun _ => (1 : ℝ≥0∞)) (PS.θ (PS.N.T m ω) ω) +
          if m = k + 1 then (1 : ℝ≥0∞) else 0 := by
        intro m
        by_cases hm : m = k + 1
        · subst hm
          have hle_one : Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T (k + 1 - 1) ω) *
              Set.indicator A (fun _ => (1 : ℝ≥0∞)) (PS.θ (PS.N.T (k + 1) ω) ω) ≤ 1 := by
            calc _ ≤ 1 * 1 := mul_le_mul' (indicator_one_le _ _) (indicator_one_le _ _)
              _ = 1 := one_mul 1
          simp only [↓reduceIte]
          exact le_add_of_le_right hle_one
        · simp only [hm, ↓reduceIte, add_zero]
          refine mul_le_mul_left ?_ _
          by_cases hmem : PS.N.T (m - 1) ω ∈ Set.Ioc (0 : ℝ) t
          · have hm_lt : m ≤ k := by
              by_contra h; push Not at h
              have : k + 1 ≤ m - 1 := by omega
              have : PS.N.T (k + 1) ω ≤ PS.N.T (m - 1) ω := (PS.N.strictMono ω).monotone this
              linarith [hk.2, hmem.2]
            have hmem' : PS.N.T m ω ∈ Set.Ioc (0 : ℝ) t := by
              refine ⟨?_, ?_⟩
              · exact lt_trans hmem.1 (PS.N.strictMono ω (by omega))
              · exact le_trans ((PS.N.strictMono ω).monotone hm_lt) hk.1
            simp [hmem, hmem']
          · simp [hmem]
      calc _ ≤ ∑' m : ℤ, (Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T m ω) *
              Set.indicator A (fun _ => (1 : ℝ≥0∞)) (PS.θ (PS.N.T m ω) ω) +
              if m = k + 1 then (1 : ℝ≥0∞) else 0) := ENNReal.tsum_le_tsum hsplit
        _ = (∑' m : ℤ, Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T m ω) *
              Set.indicator A (fun _ => (1 : ℝ≥0∞)) (PS.θ (PS.N.T m ω) ω)) +
            ∑' m : ℤ, (if m = k + 1 then (1 : ℝ≥0∞) else 0) := ENNReal.tsum_add
        _ = _ := by rw [tsum_ite_eq]
    have hle2 : ∀ ω, (∑' m : ℤ,
        Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T m ω) *
        Set.indicator A (fun _ => (1 : ℝ≥0∞)) (PS.θ (PS.N.T m ω) ω)) ≤
        (∑' m : ℤ,
        Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T (m - 1) ω) *
        Set.indicator A (fun _ => (1 : ℝ≥0∞)) (PS.θ (PS.N.T m ω) ω)) + 1 := by
      intro ω
      have hsplit : ∀ m : ℤ,
          Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T m ω) *
          Set.indicator A (fun _ => (1 : ℝ≥0∞)) (PS.θ (PS.N.T m ω) ω) ≤
          Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T (m - 1) ω) *
          Set.indicator A (fun _ => (1 : ℝ≥0∞)) (PS.θ (PS.N.T m ω) ω) +
          if m = 1 then (1 : ℝ≥0∞) else 0 := by
        intro m
        by_cases hm : m = 1
        · subst hm
          have hle_one : Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T 1 ω) *
              Set.indicator A (fun _ => (1 : ℝ≥0∞)) (PS.θ (PS.N.T 1 ω) ω) ≤ 1 := by
            calc _ ≤ 1 * 1 := mul_le_mul' (indicator_one_le _ _) (indicator_one_le _ _)
              _ = 1 := one_mul 1
          simp only [↓reduceIte]
          exact le_add_of_le_right hle_one
        · simp only [hm, ↓reduceIte, add_zero]
          refine mul_le_mul_left ?_ _
          by_cases hmem : PS.N.T m ω ∈ Set.Ioc (0 : ℝ) t
          · have hm_ge : 2 ≤ m := by
              have hm_pos : 1 ≤ m := by
                by_contra h; push Not at h
                have : PS.N.T m ω ≤ PS.N.T 0 ω := (PS.N.strictMono ω).monotone (by omega)
                linarith [PS.N.zero_le ω, hmem.1]
              omega
            have hmem' : PS.N.T (m - 1) ω ∈ Set.Ioc (0 : ℝ) t := by
              refine ⟨?_, ?_⟩
              · exact lt_of_lt_of_le (PS.N.lt_one ω) ((PS.N.strictMono ω).monotone (by omega))
              · exact le_of_lt (lt_of_lt_of_le (PS.N.strictMono ω (by omega)) hmem.2)
            simp [hmem, hmem']
          · simp [hmem]
      calc _ ≤ ∑' m : ℤ, (Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T (m - 1) ω) *
              Set.indicator A (fun _ => (1 : ℝ≥0∞)) (PS.θ (PS.N.T m ω) ω) +
              if m = 1 then (1 : ℝ≥0∞) else 0) := ENNReal.tsum_le_tsum hsplit
        _ = (∑' m : ℤ, Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T (m - 1) ω) *
              Set.indicator A (fun _ => (1 : ℝ≥0∞)) (PS.θ (PS.N.T m ω) ω)) +
            ∑' m : ℤ, (if m = 1 then (1 : ℝ≥0∞) else 0) := ENNReal.tsum_add
        _ = _ := by rw [tsum_ite_eq]
    constructor
    · rw [h1, h2]
      calc _ ≤ ∫⁻ ω, ((∑' m : ℤ,
              Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T m ω) *
              Set.indicator A (fun _ => (1 : ℝ≥0∞)) (PS.θ (PS.N.T m ω) ω)) + 1) ∂PS.P :=
            lintegral_mono hle1
        _ = _ := by rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    · rw [h1, h2]
      calc _ ≤ ∫⁻ ω, ((∑' m : ℤ,
              Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T (m - 1) ω) *
              Set.indicator A (fun _ => (1 : ℝ≥0∞)) (PS.θ (PS.N.T m ω) ω)) + 1) ∂PS.P :=
            lintegral_mono hle2
        _ = _ := by rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
  -- Deduce equality by letting t → ∞
  have hle_of : ∀ a b : ℝ≥0∞, a ≠ ⊤ → b ≠ ⊤ →
      (∀ t : ℝ, 0 < t → ENNReal.ofReal (PS.lam * t) * a ≤ ENNReal.ofReal (PS.lam * t) * b + 1) →
      a ≤ b := by
    intro a b ha hb h
    rw [← ENNReal.toReal_le_toReal ha hb]
    by_contra hlt
    push Not at hlt
    let d := a.toReal - b.toReal
    have hd : 0 < d := sub_pos.mpr hlt
    let t := 2 / (PS.lam * d)
    have ht : 0 < t := div_pos two_pos (mul_pos PS.intensity.1 hd)
    have ht_bound := h t ht
    have hlt_real : (ENNReal.ofReal (PS.lam * t) * a).toReal ≤
        (ENNReal.ofReal (PS.lam * t) * b + 1).toReal :=
      ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb, ENNReal.one_ne_top⟩) ht_bound
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb) ENNReal.one_ne_top,
        ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_one,
        ENNReal.toReal_ofReal (mul_pos PS.intensity.1 ht).le] at hlt_real
    have hprod : PS.lam * t * d = 2 := by
      dsimp [t]
      field_simp [PS.intensity.1.ne', hd.ne']
    nlinarith [hprod]
  exact le_antisymm
    (hle_of _ _ (measure_ne_top _ _) (measure_ne_top _ _) fun t ht => (hbound t ht).1)
    (hle_of _ _ (measure_ne_top _ _) (measure_ne_top _ _) fun t ht => (hbound t ht).2)

lemma ergodic_palmShift (Q : Queue Ω) :
    Ergodic (palmShift Q.toPalmSetting) Q.toPalmSetting.P0 := by
  let PS := Q.toPalmSetting
  have := PS.isProb
  have := PS.palm.1
  refine ⟨measurePreserving_palmShift PS, ⟨fun B hB hBinv => ?_⟩⟩
  let A : Set Ω := {ω | PS.θ (PS.N.T 0 ω) ω ∈ B}
  have hAmeas : MeasurableSet A := measurable_flow_T PS.θ PS.N 0 hB
  -- S.symm also preserves B
  have hBinv_symm : (palmShift PS).symm ⁻¹' B = B := by
    ext ω
    have := Set.ext_iff.mp hBinv ((palmShift PS).symm ω)
    change (palmShift PS) ((palmShift PS).symm ω) ∈ B ↔ (palmShift PS).symm ω ∈ B at this
    rw [(palmShift PS).apply_symm_apply] at this
    exact this.symm
  have hBinv_iter : ∀ k : ℕ, (palmShift PS)^[k] ⁻¹' B = B := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      ext ω
      rw [Set.mem_preimage, Function.iterate_succ_apply']
      have h1 : palmShift PS ((palmShift PS)^[k] ω) ∈ B ↔ (palmShift PS)^[k] ω ∈ B :=
        Set.ext_iff.mp hBinv _
      rw [h1]
      exact Set.ext_iff.mp ih ω
  have hBinv_symm_iter : ∀ k : ℕ, ((palmShift PS).symm)^[k] ⁻¹' B = B := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      ext ω
      rw [Set.mem_preimage, Function.iterate_succ_apply']
      have h1 : (palmShift PS).symm (((palmShift PS).symm)^[k] ω) ∈ B ↔
          ((palmShift PS).symm)^[k] ω ∈ B := Set.ext_iff.mp hBinv_symm _
      rw [h1]
      exact Set.ext_iff.mp ih ω
  -- Helper: θ (T k ω) ω ∈ B ↔ ω ∈ A
  have hshift_mem : ∀ (k : ℤ) (ω : Ω), PS.θ (PS.N.T k ω) ω ∈ B ↔ ω ∈ A := by
    intro k ω
    let ω0 := PS.θ (PS.N.T 0 ω) ω
    have hω0 : PS.N.T 0 ω0 = 0 := T_zero_shift_T PS.N PS.θ PS.compatible 0 ω
    have hTk : PS.θ (PS.N.T k ω) ω = PS.θ (PS.N.T k ω0) ω0 := by
      dsimp [ω0]
      rw [T_shift_T PS.N PS.θ PS.compatible k 0 ω, add_zero, ← flow_add_apply, sub_add_cancel]
    rw [hTk]
    rcases le_or_gt 0 k with hk | hk
    · lift k to ℕ using hk
      rw [← palmShift_iterate_of_zero PS hω0 k]
      exact Set.ext_iff.mp (hBinv_iter k) ω0
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, k = -(m : ℤ) := ⟨(-k).toNat, by omega⟩
      subst hm
      rw [← palmShift_symm_iterate_of_zero PS hω0 m]
      exact Set.ext_iff.mp (hBinv_symm_iter m) ω0
  -- A is θ-invariant
  have hAinv : ∀ t : ℝ, PS.θ t ⁻¹' A = A := by
    intro t
    ext ω
    show PS.θ (PS.N.T 0 (PS.θ t ω)) (PS.θ t ω) ∈ B ↔ ω ∈ A
    rw [flow_T_zero_shift PS.N PS.θ PS.compatible t ω]
    exact hshift_mem (idx PS.N t ω) ω
  -- By ergodicity of (P, θ), P A = 0 ∨ P A = 1
  rcases Q.ergodic.2 A hAmeas hAinv with hPA0 | hPA1
  · have hPB0 : PS.P0 B = 0 := by
      have hpalm := PS.palm.2 B hB 1 one_pos
      have hzero : ∫⁻ ω, ∑' n : ℤ,
          Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ≥0∞)) (PS.N.T n ω) *
          Set.indicator B (fun _ => (1 : ℝ≥0∞)) (PS.θ (PS.N.T n ω) ω) ∂PS.P = 0 := by
        refine lintegral_eq_zero_iff ?_ |>.mpr ?_
        · refine Measurable.tsum fun n => ?_
          exact (measurable_const.indicator measurableSet_Ioc |>.comp (PS.N.measurable_T n)).mul
            ((measurable_const.indicator hB).comp (measurable_flow_T PS.θ PS.N n))
        · have hae : ∀ᵐ ω ∂PS.P, ω ∉ A := by
            rw [ae_iff]; simp only [not_not]; exact hPA0
          filter_upwards [hae] with ω hω
          refine ENNReal.tsum_eq_zero.mpr fun n => ?_
          have hnotB : PS.θ (PS.N.T n ω) ω ∉ B := mt (hshift_mem n ω).mp hω
          simp [hnotB]
      rw [hzero, mul_one] at hpalm
      have hlam_ne0 : ENNReal.ofReal PS.lam ≠ 0 := (ENNReal.ofReal_pos.mpr PS.intensity.1).ne'
      exact (mul_eq_zero.mp hpalm).resolve_left hlam_ne0
    have hae : ∀ᵐ ω ∂PS.P0, (ω ∈ B) = False := by
      rw [ae_iff]; simpa using hPB0
    exact Filter.eventuallyConst_iff_exists_eventuallyEq.mpr ⟨False, hae⟩
  · have hPBc0 : PS.P0 Bᶜ = 0 := by
      have hPAc0 : PS.P Aᶜ = 0 := by
        rw [prob_compl_eq_zero_iff hAmeas]; exact hPA1
      have hpalm := PS.palm.2 Bᶜ hB.compl 1 one_pos
      have hzero : ∫⁻ ω, ∑' n : ℤ,
          Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ≥0∞)) (PS.N.T n ω) *
          Set.indicator Bᶜ (fun _ => (1 : ℝ≥0∞)) (PS.θ (PS.N.T n ω) ω) ∂PS.P = 0 := by
        refine lintegral_eq_zero_iff ?_ |>.mpr ?_
        · refine Measurable.tsum fun n => ?_
          exact (measurable_const.indicator measurableSet_Ioc |>.comp (PS.N.measurable_T n)).mul
            ((measurable_const.indicator hB.compl).comp (measurable_flow_T PS.θ PS.N n))
        · have hae : ∀ᵐ ω ∂PS.P, ω ∈ A := by
            rw [ae_iff]; exact hPAc0
          filter_upwards [hae] with ω hω
          refine ENNReal.tsum_eq_zero.mpr fun n => ?_
          have hinB : PS.θ (PS.N.T n ω) ω ∈ B := (hshift_mem n ω).mpr hω
          simp [hinB]
      rw [hzero, mul_one] at hpalm
      have hlam_ne0 : ENNReal.ofReal PS.lam ≠ 0 := (ENNReal.ofReal_pos.mpr PS.intensity.1).ne'
      exact (mul_eq_zero.mp hpalm).resolve_left hlam_ne0
    have hae : ∀ᵐ ω ∂PS.P0, (ω ∈ B) = True := by
      rw [ae_iff]; simp only [eq_iff_iff, iff_true]; exact hPBc0
    exact Filter.eventuallyConst_iff_exists_eventuallyEq.mpr ⟨True, hae⟩

lemma lintegral_tau_zero (Q : Queue Ω) :
    ENNReal.ofReal Q.toPalmSetting.lam * ∫⁻ ω, ENNReal.ofReal (Q.tau 0 ω) ∂Q.toPalmSetting.P0 = 1 := by
  let PS := Q.toPalmSetting
  have := PS.isProb
  have := PS.palm.1
  have htau_meas : Measurable (fun ω => Q.tau 0 ω) :=
    (PS.N.measurable_T 1).sub (PS.N.measurable_T 0)
  -- Upper bound: ≤ 1 via truncation min (tau 0 ω) M
  have hupper : ENNReal.ofReal PS.lam * ∫⁻ ω, ENNReal.ofReal (Q.tau 0 ω) ∂PS.P0 ≤ 1 := by
    have hM : ∀ M : ℕ, ENNReal.ofReal PS.lam *
        ∫⁻ ω, ENNReal.ofReal (min (Q.tau 0 ω) (M : ℝ)) ∂PS.P0 ≤ 1 := by
      intro M
      have ht_bound : ∀ t : ℝ, 0 < t →
          ENNReal.ofReal (PS.lam * t) * ∫⁻ ω, ENNReal.ofReal (min (Q.tau 0 ω) (M : ℝ)) ∂PS.P0 ≤
            ENNReal.ofReal (t + M) := by
        intro t ht
        rw [palm_lintegral PS (f := fun ω => ENNReal.ofReal (min (Q.tau 0 ω) (M : ℝ)))
            (ENNReal.measurable_ofReal.comp (htau_meas.min measurable_const)) ht]
        have hpw : ∀ ω, (∑' n : ℤ,
            Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T n ω) *
            ENNReal.ofReal (min (Q.tau 0 (PS.θ (PS.N.T n ω) ω)) (M : ℝ))) ≤
            ENNReal.ofReal (t + M) := by
          intro ω
          let k := idx PS.N t ω
          have hk := idx_spec PS.N t ω
          by_cases hk0 : k ≤ 0
          · have h0 : ∀ n : ℤ, PS.N.T n ω ∉ Set.Ioc (0 : ℝ) t := by
              intro n hmem
              rcases le_or_gt n 0 with hn | hn
              · have : PS.N.T n ω ≤ PS.N.T 0 ω := (PS.N.strictMono ω).monotone hn
                linarith [PS.N.zero_le ω, hmem.1]
              · have : k + 1 ≤ n := by omega
                have : PS.N.T (k + 1) ω ≤ PS.N.T n ω := (PS.N.strictMono ω).monotone this
                linarith [hk.2, hmem.2]
            have htsum0 : (∑' n : ℤ,
                Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T n ω) *
                ENNReal.ofReal (min (Q.tau 0 (PS.θ (PS.N.T n ω) ω)) (M : ℝ))) = 0 :=
              ENNReal.tsum_eq_zero.mpr fun n => by simp [h0 n]
            rw [htsum0]; exact zero_le
          · push Not at hk0
            -- Support is contained in Finset.Icc 1 k
            have hsupp : ∀ n : ℤ, n ∉ Finset.Icc 1 k →
                Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T n ω) *
                ENNReal.ofReal (min (Q.tau 0 (PS.θ (PS.N.T n ω) ω)) (M : ℝ)) = 0 := by
              intro n hn
              rw [Finset.mem_Icc, not_and_or] at hn
              have hnot : PS.N.T n ω ∉ Set.Ioc (0 : ℝ) t := by
                rcases hn with hn | hn
                · intro hmem
                  have : PS.N.T n ω ≤ PS.N.T 0 ω := (PS.N.strictMono ω).monotone (by omega)
                  linarith [PS.N.zero_le ω, hmem.1]
                · intro hmem
                  have : PS.N.T (k + 1) ω ≤ PS.N.T n ω := (PS.N.strictMono ω).monotone (by omega)
                  linarith [hk.2, hmem.2]
              simp [hnot]
            rw [tsum_eq_sum hsupp]
            have hIcc : Finset.Icc (1 : ℤ) k = insert k (Finset.Icc 1 (k - 1)) := by
              ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
            rw [hIcc, Finset.sum_insert (by simp)]
            have hterm_k : Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T k ω) *
                ENNReal.ofReal (min (Q.tau 0 (PS.θ (PS.N.T k ω) ω)) (M : ℝ)) ≤
                ENNReal.ofReal (M : ℝ) := by
              calc _ ≤ 1 * ENNReal.ofReal (M : ℝ) :=
                    mul_le_mul' (indicator_one_le _ _)
                      (ENNReal.ofReal_le_ofReal (min_le_right _ _))
                _ = ENNReal.ofReal (M : ℝ) := one_mul _
            have hsum_prev : (∑ n ∈ Finset.Icc 1 (k - 1),
                Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T n ω) *
                ENNReal.ofReal (min (Q.tau 0 (PS.θ (PS.N.T n ω) ω)) (M : ℝ))) ≤
                ENNReal.ofReal t := by
              calc _ ≤ ∑ n ∈ Finset.Icc 1 (k - 1), ENNReal.ofReal (Q.tau n ω) := by
                    refine Finset.sum_le_sum fun n _ => ?_
                    rw [tau_shift_T, zero_add]
                    calc _ ≤ 1 * ENNReal.ofReal (Q.tau n ω) :=
                          mul_le_mul' (indicator_one_le _ _)
                            (ENNReal.ofReal_le_ofReal (min_le_left _ _))
                      _ = ENNReal.ofReal (Q.tau n ω) := one_mul _
                _ = ENNReal.ofReal (∑ n ∈ Finset.Icc 1 (k - 1), Q.tau n ω) :=
                    (ENNReal.ofReal_sum_of_nonneg fun n _ => (tau_pos Q n ω).le).symm
                _ ≤ ENNReal.ofReal t := by
                    refine ENNReal.ofReal_le_ofReal ?_
                    have htel : (∑ n ∈ Finset.Icc (1 : ℤ) (k - 1), Q.tau n ω) =
                        PS.N.T k ω - PS.N.T 1 ω := by
                      have hk1 : 0 ≤ k - 1 := by omega
                      lift k - 1 to ℕ using hk1 with m hm
                      have hk_eq : k = (m : ℤ) + 1 := by omega
                      rw [hk_eq]
                      clear hk_eq hm hk hk0 hsupp hIcc hterm_k k
                      induction m with
                      | zero => simp
                      | succ m ih =>
                        have hIcc' : Finset.Icc (1 : ℤ) ((m + 1 : ℕ) : ℤ) =
                            insert ((m + 1 : ℕ) : ℤ) (Finset.Icc 1 (m : ℤ)) := by
                          ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
                        rw [hIcc', Finset.sum_insert (by simp), ih]
                        simp only [Queue.tau, Nat.cast_add, Nat.cast_one]
                        ring
                    rw [htel]
                    linarith [hk.1, PS.N.lt_one ω]
            calc _ ≤ ENNReal.ofReal (M : ℝ) + ENNReal.ofReal t := add_le_add hterm_k hsum_prev
              _ = ENNReal.ofReal (t + M) := by
                rw [add_comm, ← ENNReal.ofReal_add ht.le (Nat.cast_nonneg M)]
        calc _ ≤ ∫⁻ _, ENNReal.ofReal (t + M) ∂PS.P := lintegral_mono hpw
          _ = ENNReal.ofReal (t + M) := by rw [lintegral_const, measure_univ, mul_one]
      -- Divide by t and let t → ∞
      have hfin : ∫⁻ ω, ENNReal.ofReal (min (Q.tau 0 ω) (M : ℝ)) ∂PS.P0 ≠ ⊤ := by
        refine ne_top_of_le_ne_top (b := ENNReal.ofReal (M : ℝ)) ENNReal.ofReal_ne_top ?_
        calc _ ≤ ∫⁻ _, ENNReal.ofReal (M : ℝ) ∂PS.P0 :=
              lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (min_le_right _ _)
          _ = ENNReal.ofReal (M : ℝ) := by rw [lintegral_const, measure_univ, mul_one]
      rw [← ENNReal.toReal_le_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) ENNReal.one_ne_top]
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal PS.intensity.1.le, ENNReal.toReal_one]
      by_contra hgt
      push Not at hgt
      set I := (∫⁻ ω, ENNReal.ofReal (min (Q.tau 0 ω) (M : ℝ)) ∂PS.P0).toReal
      let eps := PS.lam * I - 1
      have heps : 0 < eps := sub_pos.mpr hgt
      let t := ((M : ℝ) + 1) / eps
      have ht : 0 < t := div_pos (by positivity) heps
      have hb := ht_bound t ht
      have hb_real := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_pos PS.intensity.1 ht).le,
          ENNReal.toReal_ofReal (by positivity)] at hb_real
      have hprod : t * eps = (M : ℝ) + 1 := by
        dsimp [t]; field_simp [heps.ne']
      nlinarith [hprod]
    -- Let M → ∞ by monotone convergence
    have hsup : ∀ ω, ENNReal.ofReal (Q.tau 0 ω) =
        ⨆ M : ℕ, ENNReal.ofReal (min (Q.tau 0 ω) (M : ℝ)) := by
      intro ω
      refine le_antisymm ?_ (iSup_le fun M => ENNReal.ofReal_le_ofReal (min_le_left _ _))
      obtain ⟨M, hM_gt⟩ := exists_nat_gt (Q.tau 0 ω)
      refine le_iSup_of_le M ?_
      rw [min_eq_left hM_gt.le]
    simp_rw [hsup]
    rw [lintegral_iSup]
    · rw [ENNReal.mul_iSup]
      exact iSup_le hM
    · intro M; exact ENNReal.measurable_ofReal.comp (htau_meas.min measurable_const)
    · intro M1 M2 hM12 ω
      exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.mpr hM12))
  -- Lower bound: 1 ≤ ...
  have hlower : 1 ≤ ENNReal.ofReal PS.lam * ∫⁻ ω, ENNReal.ofReal (Q.tau 0 ω) ∂PS.P0 := by
    have hM : ∀ M : ℕ, PS.P {ω | PS.N.T 1 ω ≤ (M : ℝ)} ≤
        ENNReal.ofReal PS.lam * ∫⁻ ω, ENNReal.ofReal (Q.tau 0 ω) ∂PS.P0 := by
      intro M
      have ht_bound : ∀ t : ℝ, (M : ℝ) < t →
          ENNReal.ofReal (t - M) * PS.P {ω | PS.N.T 1 ω ≤ (M : ℝ)} ≤
            ENNReal.ofReal (PS.lam * t) * ∫⁻ ω, ENNReal.ofReal (Q.tau 0 ω) ∂PS.P0 := by
        intro t ht
        have ht0 : 0 < t := lt_of_le_of_lt (Nat.cast_nonneg M) ht
        rw [palm_lintegral PS (f := fun ω => ENNReal.ofReal (Q.tau 0 ω))
            (ENNReal.measurable_ofReal.comp htau_meas) ht0]
        have hSmeas : MeasurableSet {ω | PS.N.T 1 ω ≤ (M : ℝ)} :=
          measurableSet_le (PS.N.measurable_T 1) measurable_const
        have hpw : ∀ ω, Set.indicator {ω | PS.N.T 1 ω ≤ (M : ℝ)}
            (fun _ => ENNReal.ofReal (t - M)) ω ≤
            ∑' n : ℤ,
              Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T n ω) *
              ENNReal.ofReal (Q.tau 0 (PS.θ (PS.N.T n ω) ω)) := by
          intro ω
          by_cases hω : PS.N.T 1 ω ≤ (M : ℝ)
          · rw [Set.indicator_of_mem (show ω ∈ {ω | PS.N.T 1 ω ≤ (M : ℝ)} from hω)]
            let k := idx PS.N t ω
            have hk := idx_spec PS.N t ω
            have hk1 : 1 ≤ k := by
              by_contra h; push Not at h
              have : k + 1 ≤ 1 := by omega
              have : PS.N.T (k + 1) ω ≤ PS.N.T 1 ω := (PS.N.strictMono ω).monotone this
              linarith [hk.2, hω, ht]
            calc ENNReal.ofReal (t - M)
                ≤ ENNReal.ofReal (PS.N.T (k + 1) ω - PS.N.T 1 ω) :=
                  ENNReal.ofReal_le_ofReal (by linarith [hk.2, hω])
              _ = ENNReal.ofReal (∑ n ∈ Finset.Icc (1 : ℤ) k, Q.tau n ω) := by
                  congr 1
                  have hk0 : 0 ≤ k := by omega
                  lift k to ℕ using hk0 with m
                  clear hk hk1 hω
                  induction m with
                  | zero => simp
                  | succ m ih =>
                    have hIcc' : Finset.Icc (1 : ℤ) ((m + 1 : ℕ) : ℤ) =
                        insert ((m + 1 : ℕ) : ℤ) (Finset.Icc 1 (m : ℤ)) := by
                      ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
                    rw [hIcc', Finset.sum_insert (by simp), ← ih]
                    simp only [Queue.tau, Nat.cast_add, Nat.cast_one]
                    ring
              _ = ∑ n ∈ Finset.Icc (1 : ℤ) k, ENNReal.ofReal (Q.tau n ω) :=
                  ENNReal.ofReal_sum_of_nonneg fun n _ => (tau_pos Q n ω).le
              _ = ∑ n ∈ Finset.Icc (1 : ℤ) k,
                  Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ => (1 : ℝ≥0∞)) (PS.N.T n ω) *
                  ENNReal.ofReal (Q.tau 0 (PS.θ (PS.N.T n ω) ω)) := by
                  refine Finset.sum_congr rfl fun n hn => ?_
                  rw [Finset.mem_Icc] at hn
                  have hmem : PS.N.T n ω ∈ Set.Ioc (0 : ℝ) t :=
                    ⟨lt_of_lt_of_le (PS.N.lt_one ω) ((PS.N.strictMono ω).monotone hn.1),
                     le_trans ((PS.N.strictMono ω).monotone hn.2) hk.1⟩
                  rw [Set.indicator_of_mem hmem, one_mul, tau_shift_T, zero_add]
              _ ≤ _ := ENNReal.sum_le_tsum _
          · rw [Set.indicator_of_notMem (show ω ∉ {ω | PS.N.T 1 ω ≤ (M : ℝ)} from hω)]; exact zero_le
        calc _ = ∫⁻ ω, Set.indicator {ω | PS.N.T 1 ω ≤ (M : ℝ)}
                (fun _ => ENNReal.ofReal (t - M)) ω ∂PS.P := by
              rw [lintegral_indicator_const hSmeas]
          _ ≤ _ := lintegral_mono hpw
      -- Let t → ∞
      have hLHS_ne_top : ENNReal.ofReal PS.lam * ∫⁻ ω, ENNReal.ofReal (Q.tau 0 ω) ∂PS.P0 ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top hupper
      rw [← ENNReal.toReal_le_toReal (measure_ne_top _ _) hLHS_ne_top]
      by_contra hlt
      push Not at hlt
      set R := (ENNReal.ofReal PS.lam * ∫⁻ ω, ENNReal.ofReal (Q.tau 0 ω) ∂PS.P0).toReal
      set p := (PS.P {ω | PS.N.T 1 ω ≤ (M : ℝ)}).toReal
      have hp_pos : 0 < p := lt_of_le_of_lt ENNReal.toReal_nonneg hlt
      let d := p - R
      have hd : 0 < d := sub_pos.mpr hlt
      let t := max ((M : ℝ) + 1) (((M : ℝ) * p + 1) / d)
      have ht : (M : ℝ) < t := lt_of_lt_of_le (by linarith) (le_max_left _ _)
      have ht0 : 0 < t := lt_of_le_of_lt (Nat.cast_nonneg M) ht
      have hb := ht_bound t ht
      have hRHS_eq : ENNReal.ofReal (PS.lam * t) * ∫⁻ ω, ENNReal.ofReal (Q.tau 0 ω) ∂PS.P0 =
          ENNReal.ofReal t * (ENNReal.ofReal PS.lam * ∫⁻ ω, ENNReal.ofReal (Q.tau 0 ω) ∂PS.P0) := by
        rw [ENNReal.ofReal_mul PS.intensity.1.le]; ring
      rw [hRHS_eq] at hb
      have hb_real := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLHS_ne_top) hb
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal (sub_pos.mpr ht).le, ENNReal.toReal_ofReal ht0.le] at hb_real
      have ht_ge : ((M : ℝ) * p + 1) / d ≤ t := le_max_right _ _
      have htd : (M : ℝ) * p + 1 ≤ t * d := (div_le_iff₀ hd).mp ht_ge
      nlinarith [htd]
    have hUnion : (⋃ M : ℕ, {ω | PS.N.T 1 ω ≤ (M : ℝ)}) = Set.univ := by
      ext ω; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      exact exists_nat_ge (PS.N.T 1 ω)
    have hsup : (⨆ M : ℕ, PS.P {ω | PS.N.T 1 ω ≤ (M : ℝ)}) = 1 := by
      have hmono : Monotone (fun M : ℕ => {ω | PS.N.T 1 ω ≤ (M : ℝ)}) := by
        intro a b hab ω hω
        change PS.N.T 1 ω ≤ (b : ℝ)
        exact le_trans hω (Nat.cast_le.mpr hab)
      rw [← hmono.measure_iUnion, hUnion, measure_univ]
    rw [← hsup]
    exact iSup_le hM
  exact le_antisymm hupper hlower

lemma integrable_tau_zero (Q : Queue Ω) : Integrable (Q.tau 0) Q.toPalmSetting.P0 := by
  let PS := Q.toPalmSetting
  have hmeas : Measurable (Q.tau 0) := (PS.N.measurable_T 1).sub (PS.N.measurable_T 0)
  have hlint : ∫⁻ ω, ENNReal.ofReal (Q.tau 0 ω) ∂PS.P0 < ⊤ := by
    have h := lintegral_tau_zero Q
    have hlam_ne0 : ENNReal.ofReal PS.lam ≠ 0 := (ENNReal.ofReal_pos.mpr PS.intensity.1).ne'
    have hne : ∫⁻ ω, ENNReal.ofReal (Q.tau 0 ω) ∂PS.P0 ≠ ⊤ := by
      intro htop
      rw [htop, ENNReal.mul_top hlam_ne0] at h
      exact ENNReal.top_ne_one h
    exact lt_top_iff_ne_top.mpr hne
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  refine lt_of_le_of_lt ?_ hlint
  refine lintegral_mono fun ω => ?_
  rw [Real.enorm_eq_ofReal (tau_pos Q 0 ω).le]

lemma integral_tau_zero (Q : Queue Ω) :
    ∫ ω, Q.tau 0 ω ∂Q.toPalmSetting.P0 = Q.toPalmSetting.lam⁻¹ := by
  let PS := Q.toPalmSetting
  have h := lintegral_tau_zero Q
  have hint := integrable_tau_zero Q
  have hofReal : ENNReal.ofReal (∫ ω, Q.tau 0 ω ∂PS.P0) = ∫⁻ ω, ENNReal.ofReal (Q.tau 0 ω) ∂PS.P0 :=
    (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => (tau_pos Q 0 ω).le))
  rw [← hofReal, ← ENNReal.ofReal_mul PS.intensity.1.le] at h
  have hprod : PS.lam * ∫ ω, Q.tau 0 ω ∂PS.P0 = 1 := by
    have := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_ofReal (mul_nonneg PS.intensity.1.le
      (integral_nonneg fun ω => (tau_pos Q 0 ω).le)), ENNReal.toReal_one] at this
    exact this
  exact eq_inv_of_mul_eq_one_right hprod

/-- Transfer a `P0`-a.s. property to a `P`-a.s. property at all arrival shifts `θ (T k ω) ω`. -/
lemma ae_P_all_shifts_of_ae_P0 (Q : Queue Ω) {p : Ω → Prop}
    (hp : ∀ᵐ ω ∂Q.toPalmSetting.P0, p ω) :
    ∀ᵐ ω ∂Q.toPalmSetting.P, ∀ k : ℤ, p (Q.toPalmSetting.θ (Q.toPalmSetting.N.T k ω) ω) := by
  let PS := Q.toPalmSetting
  have := PS.isProb
  have := PS.palm.1
  -- Take a measurable superset N0 of {ω | ¬ p ω} with P0 N0 = 0
  obtain ⟨N0, hN0_sub, hN0_meas, hN0_zero⟩ := exists_measurable_superset_of_null hp
  -- Let B be the S-invariant union of shifts of N0
  let B : Set Ω := (⋃ k : ℕ, (palmShift PS)^[k] ⁻¹' N0) ∪ (⋃ k : ℕ, ((palmShift PS).symm)^[k] ⁻¹' N0)
  have hB_meas : MeasurableSet B := by
    refine MeasurableSet.union ?_ ?_
    · exact MeasurableSet.iUnion fun k => ((palmShift PS).measurable.iterate k) hN0_meas
    · exact MeasurableSet.iUnion fun k => ((palmShift PS).symm.measurable.iterate k) hN0_meas
  have hmp := measurePreserving_palmShift PS
  have hmp_symm : MeasurePreserving (palmShift PS).symm PS.P0 PS.P0 := hmp.symm (palmShift PS)
  have hB_zero : PS.P0 B = 0 := by
    refine measure_mono_null (Set.Subset.refl _) ?_
    rw [measure_union_null_iff]
    constructor
    · rw [measure_iUnion_null_iff]
      intro k
      rw [(hmp.iterate k).measure_preimage hN0_meas.nullMeasurableSet]
      exact hN0_zero
    · rw [measure_iUnion_null_iff]
      intro k
      rw [(hmp_symm.iterate k).measure_preimage hN0_meas.nullMeasurableSet]
      exact hN0_zero
  -- By IsPalmProbability, for P-a.e. ω, ∀ n with T n ω ∈ (0, 1], θ (T n ω) ω ∉ B
  -- Even better: for EVERY k, θ (T k ω) ω ∈ B ↔ θ (T 0 ω) ω ∈ B!
  have hB_inv : ∀ (k : ℤ) (ω : Ω), PS.θ (PS.N.T k ω) ω ∈ B ↔ PS.θ (PS.N.T 0 ω) ω ∈ B := by
    -- Actually, B is S-invariant!
    have hBS : palmShift PS ⁻¹' B = B := by
      ext ω
      simp only [B, Set.mem_preimage, Set.mem_union, Set.mem_iUnion]
      constructor
      · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
        · left; exact ⟨k + 1, by simpa [Function.iterate_succ_apply] using hk⟩
        · cases k with
          | zero => left; exact ⟨1, by simpa using hk⟩
          | succ k =>
            right; refine ⟨k, ?_⟩
            have : ((palmShift PS).symm)^[k + 1] (palmShift PS ω) = ((palmShift PS).symm)^[k] ω := by
              rw [Function.iterate_succ_apply, (palmShift PS).symm_apply_apply]
            rwa [this] at hk
      · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
        · cases k with
          | zero => right; exact ⟨1, by simpa using hk⟩
          | succ k =>
            left; exact ⟨k, by simpa [Function.iterate_succ_apply] using hk⟩
        · right; refine ⟨k + 1, ?_⟩
          rw [Function.iterate_succ_apply, (palmShift PS).symm_apply_apply]
          exact hk
    have hBS_symm : (palmShift PS).symm ⁻¹' B = B := by
      ext ω
      have := Set.ext_iff.mp hBS ((palmShift PS).symm ω)
      change (palmShift PS) ((palmShift PS).symm ω) ∈ B ↔ (palmShift PS).symm ω ∈ B at this
      rw [(palmShift PS).apply_symm_apply] at this
      exact this.symm
    intro k ω
    let ω0 := PS.θ (PS.N.T 0 ω) ω
    have hω0 : PS.N.T 0 ω0 = 0 := T_zero_shift_T PS.N PS.θ PS.compatible 0 ω
    have hTk : PS.θ (PS.N.T k ω) ω = PS.θ (PS.N.T k ω0) ω0 := by
      dsimp [ω0]
      rw [T_shift_T PS.N PS.θ PS.compatible k 0 ω, add_zero, ← flow_add_apply, sub_add_cancel]
    rw [hTk]
    rcases le_or_gt 0 k with hk | hk
    · lift k to ℕ using hk
      rw [← palmShift_iterate_of_zero PS hω0 k]
      clear hTk
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact (Set.ext_iff.mp hBS _).trans ih
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, k = -(m : ℤ) := ⟨(-k).toNat, by omega⟩
      subst hm
      rw [← palmShift_symm_iterate_of_zero PS hω0 m]
      clear hTk hk
      induction m with
      | zero => rfl
      | succ m ih =>
        rw [Function.iterate_succ_apply']
        exact (Set.ext_iff.mp hBS_symm _).trans ih
  let A : Set Ω := {ω | PS.θ (PS.N.T 0 ω) ω ∈ B}
  have hA_meas : MeasurableSet A := measurable_flow_T PS.θ PS.N 0 hB_meas
  have hA_inv : ∀ t : ℝ, PS.θ t ⁻¹' A = A := by
    intro t; ext ω
    show PS.θ (PS.N.T 0 (PS.θ t ω)) (PS.θ t ω) ∈ B ↔ PS.θ (PS.N.T 0 ω) ω ∈ B
    rw [flow_T_zero_shift PS.N PS.θ PS.compatible t ω]
    exact hB_inv (idx PS.N t ω) ω
  have hPA_zero : PS.P A = 0 := by
    rcases Q.ergodic.2 A hA_meas hA_inv with h0 | h1
    · exact h0
    · exfalso
      have hpalm := PS.palm.2 B hB_meas 1 one_pos
      rw [hB_zero, mul_zero] at hpalm
      have hAE : ∀ᵐ ω ∂PS.P, ω ∈ A := by
        rw [ae_iff]
        change PS.P Aᶜ = 0
        rw [prob_compl_eq_zero_iff hA_meas]; exact h1
      have hEq : ∫⁻ ω, ∑' n : ℤ,
          Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ≥0∞)) (PS.N.T n ω) *
          Set.indicator B (fun _ => (1 : ℝ≥0∞)) (PS.θ (PS.N.T n ω) ω) ∂PS.P =
          ENNReal.ofReal PS.lam := by
        rw [PS.intensity.2]
        refine lintegral_congr_ae ?_
        filter_upwards [hAE] with ω hω
        rw [PointProcess.count, Measure.sum_apply _ measurableSet_Ioc]
        refine tsum_congr fun n => ?_
        have hnB : PS.θ (PS.N.T n ω) ω ∈ B := (hB_inv n ω).mpr hω
        rw [Set.indicator_of_mem hnB, mul_one, Measure.dirac_apply' _ measurableSet_Ioc]
        rfl
      rw [hEq] at hpalm
      exact (ENNReal.ofReal_pos.mpr PS.intensity.1).ne hpalm
  have hAE_notA : ∀ᵐ ω ∂PS.P, ω ∉ A := by
    rw [ae_iff]; simp [hPA_zero]
  filter_upwards [hAE_notA] with ω hω k
  have hnotB : PS.θ (PS.N.T k ω) ω ∉ B := mt (hB_inv k ω).mp hω
  have hnotN0 : PS.θ (PS.N.T k ω) ω ∉ N0 := fun hmem =>
    hnotB (Or.inl (Set.mem_iUnion.mpr ⟨0, by simpa using hmem⟩))
  by_contra hp'
  exact hnotN0 (hN0_sub hp')

lemma ae_P0_of_P_invariant (PS : PalmSetting Ω) {A : Set Ω}
    (hAmeas : MeasurableSet A) (hAinv : ∀ t : ℝ, PS.θ t ⁻¹' A = A) (hPA : PS.P A = 1) :
    PS.P0 A = 1 := by
  have := PS.isProb
  have := PS.palm.1
  have hPAc : PS.P Aᶜ = 0 := by rw [prob_compl_eq_zero_iff hAmeas]; exact hPA
  have hpalm := PS.palm.2 Aᶜ hAmeas.compl 1 one_pos
  have hzero : ∫⁻ ω, ∑' n : ℤ,
      Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ≥0∞)) (PS.N.T n ω) *
      Set.indicator Aᶜ (fun _ => (1 : ℝ≥0∞)) (PS.θ (PS.N.T n ω) ω) ∂PS.P = 0 := by
    refine (lintegral_eq_zero_iff ?_).mpr ?_
    · refine Measurable.tsum fun n => ?_
      exact (measurable_const.indicator measurableSet_Ioc |>.comp (PS.N.measurable_T n)).mul
        ((measurable_const.indicator hAmeas.compl).comp (measurable_flow_T PS.θ PS.N n))
    · have hae : ∀ᵐ ω ∂PS.P, ω ∈ A := by rw [ae_iff]; exact hPAc
      filter_upwards [hae] with ω hω
      refine ENNReal.tsum_eq_zero.mpr fun n => ?_
      have hnA : PS.θ (PS.N.T n ω) ω ∈ A := (Set.ext_iff.mp (hAinv (PS.N.T n ω)) ω).mpr hω
      simp [hnA]
  rw [hzero, mul_one] at hpalm
  have hlam_ne0 : ENNReal.ofReal PS.lam ≠ 0 := (ENNReal.ofReal_pos.mpr PS.intensity.1).ne'
  have hP0Ac : PS.P0 Aᶜ = 0 := (mul_eq_zero.mp hpalm).resolve_left hlam_ne0
  exact (prob_compl_eq_zero_iff hAmeas).mp hP0Ac

lemma exists_measurable_invariant_subset_of_ae (PS : PalmSetting Ω) {S : Set Ω}
    (hSinv : ∀ t : ℝ, PS.θ t ⁻¹' S = S) (hSae : ∀ᵐ ω ∂PS.P, ω ∈ S) :
    ∃ G : Set Ω, MeasurableSet G ∧ (∀ t : ℝ, PS.θ t ⁻¹' G = G) ∧ G ⊆ S ∧ PS.P G = 1 := by
  have := PS.isProb
  obtain ⟨N0, hN0_sub, hN0_meas, hN0_zero⟩ := exists_measurable_superset_of_null hSae
  let f : Ω → ℝ≥0∞ := fun ω => ∫⁻ t : ℝ, Set.indicator N0 (fun _ => (1 : ℝ≥0∞)) (PS.θ t ω) ∂volume
  have hf_meas : Measurable f := by
    have hjoint : Measurable (fun p : ℝ × Ω => Set.indicator N0 (fun _ => (1 : ℝ≥0∞)) (PS.θ p.1 p.2)) :=
      (measurable_const.indicator hN0_meas).comp PS.θ.measurable_uncurry
    exact hjoint.lintegral_prod_left'
  let G : Set Ω := {ω | f ω = 0}
  have hG_meas : MeasurableSet G := measurableSet_eq_fun hf_meas measurable_const
  have hG_inv : ∀ t : ℝ, PS.θ t ⁻¹' G = G := by
    intro s; ext ω
    change f (PS.θ s ω) = 0 ↔ f ω = 0
    have hf_eq : f (PS.θ s ω) = f ω := by
      dsimp [f]
      simp_rw [← flow_add_apply]
      exact lintegral_add_right_eq_self (fun u => Set.indicator N0 (fun _ => (1 : ℝ≥0∞)) (PS.θ u ω)) s
    rw [hf_eq]
  have hG_sub : G ⊆ S := by
    intro ω hω
    have hae_t : ∀ᵐ t : ℝ ∂volume, Set.indicator N0 (fun _ => (1 : ℝ≥0∞)) (PS.θ t ω) = 0 := by
      refine (lintegral_eq_zero_iff ?_).mp hω
      exact (measurable_const.indicator hN0_meas).comp
        (PS.θ.measurable_uncurry.comp (measurable_id.prodMk measurable_const))
    obtain ⟨t, ht⟩ := hae_t.exists
    have hnotN0 : PS.θ t ω ∉ N0 := by
      intro hmem
      rw [Set.indicator_of_mem hmem] at ht
      exact one_ne_zero ht
    have hinS : PS.θ t ω ∈ S := by
      by_contra hnotS
      exact hnotN0 (hN0_sub hnotS)
    exact (Set.ext_iff.mp (hSinv t) ω).mp hinS
  have hPG : PS.P G = 1 := by
    have hdouble : ∫⁻ ω, f ω ∂PS.P = 0 := by
      dsimp [f]
      have hjoint : Measurable (fun p : ℝ × Ω => Set.indicator N0 (fun _ => (1 : ℝ≥0∞)) (PS.θ p.1 p.2)) :=
        (measurable_const.indicator hN0_meas).comp PS.θ.measurable_uncurry
      rw [lintegral_lintegral_swap (by exact hjoint.aemeasurable.comp_measurable measurable_swap)]
      refine (lintegral_eq_zero_iff ?_).mpr (ae_of_all _ fun t => ?_)
      · exact hjoint.lintegral_prod_right'
      · dsimp only
        have hmap : ∫⁻ ω, Set.indicator N0 (fun _ => (1 : ℝ≥0∞)) (PS.θ t ω) ∂PS.P =
            ∫⁻ ω, Set.indicator N0 (fun _ => (1 : ℝ≥0∞)) ω ∂(Measure.map (PS.θ t) PS.P) := by
          rw [lintegral_map (measurable_const.indicator hN0_meas) (PS.θ.measurable' t)]
        rw [hmap, PS.invariant t]
        have hind_eq : (∫⁻ ω, Set.indicator N0 (fun _ => (1 : ℝ≥0∞)) ω ∂PS.P) = PS.P N0 :=
          lintegral_indicator_one hN0_meas
        rw [hind_eq, hN0_zero]
        rfl
    have hae0 : ∀ᵐ ω ∂PS.P, f ω = 0 := (lintegral_eq_zero_iff hf_meas).mp hdouble
    rw [← prob_compl_eq_zero_iff hG_meas]
    rw [ae_iff] at hae0
    exact hae0
  exact ⟨G, hG_meas, hG_inv, hG_sub, hPG⟩

/-! ### Part 3: Pathwise workload inequalities and asymptotics -/

lemma workloadPath_nonneg (Q : Queue Ω) {W Wl : ℝ → Ω → ℝ} {ω : Ω}
    (hW : IsWorkloadPath Q W Wl ω) (t : ℝ) : 0 ≤ W t ω := by
  let k := idx Q.toPalmSetting.N t ω
  have hk := idx_spec Q.toPalmSetting.N t ω
  rw [hW.2.2 k t ⟨hk.1, hk.2⟩]
  exact le_max_right _ _

lemma workloadPath_Wl_nonneg (Q : Queue Ω) {W Wl : ℝ → Ω → ℝ} {ω : Ω}
    (hW : IsWorkloadPath Q W Wl ω) (s : ℝ) : 0 ≤ Wl s ω := by
  have hlim := hW.2.1 s
  have : NeBot (nhdsWithin s (Set.Iio s)) := nhdsLT_neBot s
  exact ge_of_tendsto hlim (Eventually.of_forall fun u => workloadPath_nonneg Q hW u)

lemma workloadPath_lindley_step (Q : Queue Ω) {W Wl : ℝ → Ω → ℝ} {ω : Ω}
    (hW : IsWorkloadPath Q W Wl ω) (k : ℤ) :
    Wl (Q.toPalmSetting.N.T (k + 1) ω) ω =
      max (Wl (Q.toPalmSetting.N.T k ω) ω + Q.sigma k ω - Q.tau k ω) 0 := by
  let N := Q.toPalmSetting.N
  have hlt : N.T k ω < N.T (k + 1) ω := N.strictMono ω (by omega)
  have hlim1 := hW.2.1 (N.T (k + 1) ω)
  have hlim2 : Tendsto (fun u => max (Wl (N.T k ω) ω + Q.sigma k ω - (u - N.T k ω)) 0)
      (nhdsWithin (N.T (k + 1) ω) (Set.Iio (N.T (k + 1) ω)))
      (nhds (max (Wl (N.T k ω) ω + Q.sigma k ω - Q.tau k ω) 0)) := by
    have hcont : Continuous (fun u : ℝ => max (Wl (N.T k ω) ω + Q.sigma k ω - (u - N.T k ω)) 0) :=
      (continuous_const.sub (continuous_id.sub continuous_const)).max continuous_const
    exact hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have heq : (fun u => W u ω) =ᶠ[nhdsWithin (N.T (k + 1) ω) (Set.Iio (N.T (k + 1) ω))]
      (fun u => max (Wl (N.T k ω) ω + Q.sigma k ω - (u - N.T k ω)) 0) := by
    filter_upwards [Ioo_mem_nhdsLT hlt] with u hu
    exact hW.2.2 k u ⟨hu.1.le, hu.2⟩
  have : NeBot (nhdsWithin (N.T (k + 1) ω) (Set.Iio (N.T (k + 1) ω))) := nhdsLT_neBot _
  exact tendsto_nhds_unique (hlim1.congr' heq) hlim2

lemma workloadPath_loynes_le (Q : Queue Ω) {W Wl : ℝ → Ω → ℝ} {ω : Ω}
    (hW : IsWorkloadPath Q W Wl ω) {n : ℤ} (hn : n ≤ 0) :
    Q.toPalmSetting.N.T n ω + ∑ i ∈ Finset.Icc n 0, Q.sigma i ω ≤ W 0 ω := by
  let N := Q.toPalmSetting.N
  have hstep : ∀ k : ℤ, Wl (N.T k ω) ω + Q.sigma k ω - Q.tau k ω ≤ Wl (N.T (k + 1) ω) ω := by
    intro k
    rw [workloadPath_lindley_step Q hW k]
    exact le_max_left _ _
  have hind : ∀ m : ℕ,
      Wl (N.T (-m : ℤ) ω) ω + (N.T (-m : ℤ) ω - N.T 0 ω) +
        ∑ i ∈ Finset.Icc (-m : ℤ) (-1), Q.sigma i ω ≤ Wl (N.T 0 ω) ω := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hIcc : Finset.Icc (-(m + 1 : ℕ) : ℤ) (-1) =
          insert (-(m + 1 : ℕ) : ℤ) (Finset.Icc (-m : ℤ) (-1)) := by
        ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp)]
      have hs := hstep (-(m + 1 : ℕ) : ℤ)
      have hidx : (-(m + 1 : ℕ) : ℤ) + 1 = (-m : ℤ) := by omega
      rw [hidx] at hs
      simp only [Queue.tau, hidx] at hs
      linarith [ih, hs]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨(-n).toNat, by omega⟩
  subst hm
  have h0_mem : (0 : ℝ) ∈ Set.Ico (N.T 0 ω) (N.T (0 + 1) ω) := ⟨N.zero_le ω, by simpa using N.lt_one ω⟩
  have hW0 : Wl (N.T 0 ω) ω + Q.sigma 0 ω + N.T 0 ω ≤ W 0 ω := by
    rw [hW.2.2 0 0 h0_mem]
    have := le_max_left (Wl (N.T 0 ω) ω + Q.sigma 0 ω - (0 - N.T 0 ω)) 0
    linarith
  have hIcc0 : Finset.Icc (-m : ℤ) 0 = insert (0 : ℤ) (Finset.Icc (-m : ℤ) (-1)) := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hIcc0, Finset.sum_insert (by simp)]
  have hWl_nn : 0 ≤ Wl (N.T (-m : ℤ) ω) ω := workloadPath_Wl_nonneg Q hW _
  linarith [hind m, hW0, hWl_nn]

lemma sum_range_sigma_symm (Q : Queue Ω) {ω : Ω} (h0 : Q.toPalmSetting.N.T 0 ω = 0) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), Q.sigma 0 (((palmShift Q.toPalmSetting).symm^[i]) ω)) =
      ∑ j ∈ Finset.Icc (-n : ℤ) 0, Q.sigma j ω := by
  have hterm : ∀ i : ℕ, Q.sigma 0 (((palmShift Q.toPalmSetting).symm^[i]) ω) = Q.sigma (-i : ℤ) ω := by
    intro i
    rw [palmShift_symm_iterate_of_zero Q.toPalmSetting h0 i, Q.sigma_marks.2 0 (-i : ℤ) ω, zero_add]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  refine Finset.sum_nbij (fun i : ℕ => -(i : ℤ)) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [Finset.mem_Icc]; omega
  · intro i1 _ i2 _ h
    dsimp only at h
    omega
  · intro j hj
    simp only [Finset.coe_Icc, Set.mem_Icc, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hj ⊢
    exact ⟨(-j).toNat, by omega, by omega⟩
  · intro i _; rfl

lemma sum_range_tau_symm (Q : Queue Ω) {ω : Ω} (h0 : Q.toPalmSetting.N.T 0 ω = 0) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), Q.tau 0 (((palmShift Q.toPalmSetting).symm^[i]) ω)) =
      Q.toPalmSetting.N.T 1 ω - Q.toPalmSetting.N.T (-n : ℤ) ω := by
  have hterm : ∀ i : ℕ, Q.tau 0 (((palmShift Q.toPalmSetting).symm^[i]) ω) = Q.tau (-i : ℤ) ω := by
    intro i
    rw [palmShift_symm_iterate_of_zero Q.toPalmSetting h0 i, tau_shift_T, zero_add]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  induction n with
  | zero => simp [Queue.tau]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Queue.tau]
    have hidx : (-(n + 1 : ℕ) : ℤ) + 1 = (-n : ℤ) := by omega
    rw [hidx]; ring

lemma integrable_sigma_zero_of_lt_one (Q : Queue Ω) (hρ : Q.trafficIntensity < 1) :
    Integrable (Q.sigma 0) Q.toPalmSetting.P0 ∧
      Q.toPalmSetting.lam * ∫ ω, Q.sigma 0 ω ∂Q.toPalmSetting.P0 < 1 := by
  let PS := Q.toPalmSetting
  have hlint_lt : ∫⁻ ω, ENNReal.ofReal (Q.sigma 0 ω) ∂PS.P0 < ⊤ := by
    have hlam_ne0 : ENNReal.ofReal PS.lam ≠ 0 := (ENNReal.ofReal_pos.mpr PS.intensity.1).ne'
    by_contra htop
    rw [not_lt, top_le_iff] at htop
    have : Q.trafficIntensity = ⊤ := by
      unfold Queue.trafficIntensity
      rw [htop, ENNReal.mul_top hlam_ne0]
    rw [this] at hρ
    exact not_top_lt hρ
  have hint : Integrable (Q.sigma 0) PS.P0 := by
    refine ⟨(Q.sigma_marks.1 0).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt ?_ hlint_lt
    refine lintegral_mono fun ω => ?_
    rw [Real.enorm_eq_ofReal (Q.sigma_nonneg 0 ω)]
  refine ⟨hint, ?_⟩
  have hofReal : ENNReal.ofReal (∫ ω, Q.sigma 0 ω ∂PS.P0) =
      ∫⁻ ω, ENNReal.ofReal (Q.sigma 0 ω) ∂PS.P0 :=
    ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => Q.sigma_nonneg 0 ω)
  have hprod : ENNReal.ofReal (PS.lam * ∫ ω, Q.sigma 0 ω ∂PS.P0) < ENNReal.ofReal 1 := by
    rw [ENNReal.ofReal_mul PS.intensity.1.le, hofReal, ENNReal.ofReal_one]
    exact hρ
  exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mp hprod

lemma tendsto_atBot_of_trafficIntensity_lt_one (Q : Queue Ω) (hρ : Q.trafficIntensity < 1) :
    ∀ᵐ ω ∂Q.toPalmSetting.P,
      Tendsto (fun k : ℕ => Q.toPalmSetting.N.T (-k : ℤ) ω +
        ∑ i ∈ Finset.Icc (-k : ℤ) 0, Q.sigma i ω) atTop atBot := by
  let PS := Q.toPalmSetting
  have := PS.isProb
  have := PS.palm.1
  obtain ⟨hsigInt, hrho_lt⟩ := integrable_sigma_zero_of_lt_one Q hρ
  by_cases hsig0 : ∀ᵐ ω ∂PS.P0, Q.sigma 0 ω = 0
  · have hall0 := ae_P_all_shifts_of_ae_P0 Q hsig0
    filter_upwards [hall0] with ω hω
    have hsum0 : ∀ k : ℕ, (∑ i ∈ Finset.Icc (-k : ℤ) 0, Q.sigma i ω) = 0 := by
      intro k
      refine Finset.sum_eq_zero fun i _ => ?_
      have := hω i
      rw [Q.sigma_marks.2 0 i ω, zero_add] at this
      exact this
    simp_rw [hsum0, add_zero]
    have hneg : Tendsto (fun k : ℕ => -(k : ℤ)) atTop atBot := by
      rw [tendsto_atBot]
      intro b
      filter_upwards [eventually_ge_atTop (-b).toNat] with k hk
      omega
    exact (PS.N.tendsto_atBot ω).comp hneg
  · have htauNull : ¬ (∀ᵐ ω ∂PS.P0, Q.tau 0 ω = 0) := by
      intro h
      obtain ⟨ω, hω⟩ := h.exists
      linarith [tau_pos Q 0 ω]
    have herg := queueing_ergodic_theorem PS.P0 (palmShift PS) (ergodic_palmShift Q)
      (Q.sigma 0) (Q.tau 0) (Q.sigma_marks.1 0) ((PS.N.measurable_T 1).sub (PS.N.measurable_T 0))
      (Q.sigma_nonneg 0) (fun ω => (tau_pos Q 0 ω).le) hsig0 htauNull hsigInt (integrable_tau_zero Q)
    have hP0_bot : ∀ᵐ ω ∂PS.P0,
        Tendsto (fun k : ℕ => PS.N.T (-k : ℤ) ω + ∑ i ∈ Finset.Icc (-k : ℤ) 0, Q.sigma i ω)
          atTop atBot := by
      filter_upwards [herg, ae_P0_zeroSet PS] with ω hlim h0
      have hlim_val : (∫ ω, Q.sigma 0 ω ∂PS.P0) / (∫ ω, Q.tau 0 ω ∂PS.P0) < 1 := by
        rw [integral_tau_zero Q, div_inv_eq_mul, mul_comm]
        exact hrho_lt
      let r := ((∫ ω, Q.sigma 0 ω ∂PS.P0) / (∫ ω, Q.tau 0 ω ∂PS.P0) + 1) / 2
      have hr_gt : (∫ ω, Q.sigma 0 ω ∂PS.P0) / (∫ ω, Q.tau 0 ω ∂PS.P0) < r := by dsimp [r]; linarith
      have hr_lt : r < 1 := by dsimp [r]; linarith
      have hev := hlim.eventually (eventually_lt_nhds hr_gt)
      have hneg : Tendsto (fun k : ℕ => -(k : ℤ)) atTop atBot := by
        rw [tendsto_atBot]; intro b
        filter_upwards [eventually_ge_atTop (-b).toNat] with k hk; omega
      have hTbot : Tendsto (fun k : ℕ => PS.N.T (-k : ℤ) ω) atTop atBot :=
        (PS.N.tendsto_atBot ω).comp hneg
      have hlin : Tendsto (fun k : ℕ => r * PS.N.T 1 ω + (1 - r) * PS.N.T (-k : ℤ) ω) atTop atBot := by
        have h1 : Tendsto (fun k : ℕ => (1 - r) * PS.N.T (-k : ℤ) ω) atTop atBot :=
          Tendsto.const_mul_atBot (sub_pos.mpr hr_lt) hTbot
        simpa [add_comm] using h1.atBot_add (tendsto_const_nhds (x := r * PS.N.T 1 ω))
      refine tendsto_atBot_mono' atTop ?_ hlin
      filter_upwards [hev] with k hk
      rw [sum_range_sigma_symm Q h0 k, sum_range_tau_symm Q h0 k] at hk
      have hden : 0 < PS.N.T 1 ω - PS.N.T (-k : ℤ) ω := by
        have : PS.N.T (-k : ℤ) ω ≤ PS.N.T 0 ω := (PS.N.strictMono ω).monotone (by omega)
        linarith [PS.N.lt_one ω, PS.N.zero_le ω]
      have hmul : (∑ j ∈ Finset.Icc (-k : ℤ) 0, Q.sigma j ω) < r * (PS.N.T 1 ω - PS.N.T (-k : ℤ) ω) :=
        (div_lt_iff₀ hden).mp hk
      linarith
    have hP_all := ae_P_all_shifts_of_ae_P0 Q hP0_bot
    filter_upwards [hP_all] with ω hω
    have h0 := hω 0
    have hrew : (fun k : ℕ => Q.toPalmSetting.N.T (-k : ℤ) ω + ∑ i ∈ Finset.Icc (-k : ℤ) 0, Q.sigma i ω) =
        fun k : ℕ => (PS.N.T (-k : ℤ) (PS.θ (PS.N.T 0 ω) ω) +
          ∑ i ∈ Finset.Icc (-k : ℤ) 0, Q.sigma i (PS.θ (PS.N.T 0 ω) ω)) + PS.N.T 0 ω := by
      funext k
      change PS.N.T (-k : ℤ) ω + _ = _
      rw [T_shift_T PS.N PS.θ PS.compatible (-k : ℤ) 0 ω, add_zero]
      have hsig : ∀ i, Q.sigma i (PS.θ (PS.N.T 0 ω) ω) = Q.sigma i ω := by
        intro i; rw [Q.sigma_marks.2 i 0 ω, add_zero]
      simp_rw [hsig]; ring
    rw [hrew]
    exact h0.atBot_add tendsto_const_nhds

lemma tendsto_atTop_of_one_lt_trafficIntensity (Q : Queue Ω) (hρ : 1 < Q.trafficIntensity) :
    ∀ᵐ ω ∂Q.toPalmSetting.P,
      Tendsto (fun k : ℕ => Q.toPalmSetting.N.T (-k : ℤ) ω +
        ∑ i ∈ Finset.Icc (-k : ℤ) 0, Q.sigma i ω) atTop atTop := by
  let PS := Q.toPalmSetting
  have := PS.isProb
  have := PS.palm.1
  -- Find M : ℕ such that lam * E⁰[min σ₀ M] > 1
  have hsup : ∀ ω, ENNReal.ofReal (Q.sigma 0 ω) =
      ⨆ M : ℕ, ENNReal.ofReal (min (Q.sigma 0 ω) (M : ℝ)) := by
    intro ω
    refine le_antisymm ?_ (iSup_le fun M => ENNReal.ofReal_le_ofReal (min_le_left _ _))
    obtain ⟨M, hM⟩ := exists_nat_gt (Q.sigma 0 ω)
    exact le_iSup_of_le M (by rw [min_eq_left hM.le])
  have hrho_sup : Q.trafficIntensity =
      ⨆ M : ℕ, ENNReal.ofReal PS.lam * ∫⁻ ω, ENNReal.ofReal (min (Q.sigma 0 ω) (M : ℝ)) ∂PS.P0 := by
    unfold Queue.trafficIntensity
    simp_rw [hsup]
    rw [lintegral_iSup]
    · rw [ENNReal.mul_iSup]
    · intro M; exact ENNReal.measurable_ofReal.comp ((Q.sigma_marks.1 0).min measurable_const)
    · intro M1 M2 hM12 ω
      exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.mpr hM12))
  rw [hrho_sup, lt_iSup_iff] at hρ
  obtain ⟨M, hM⟩ := hρ
  let sigM : Ω → ℝ := fun ω => min (Q.sigma 0 ω) (M : ℝ)
  have hsigM_meas : Measurable sigM := (Q.sigma_marks.1 0).min measurable_const
  have hsigM_nn : ∀ ω, 0 ≤ sigM ω := fun ω => le_min (Q.sigma_nonneg 0 ω) (Nat.cast_nonneg M)
  have hsigM_int : Integrable sigM PS.P0 := by
    refine ⟨hsigM_meas.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt (b := ENNReal.ofReal (M : ℝ)) ?_ ENNReal.ofReal_lt_top
    calc ∫⁻ ω, ‖sigM ω‖ₑ ∂PS.P0
        ≤ ∫⁻ _, ENNReal.ofReal (M : ℝ) ∂PS.P0 := by
          refine lintegral_mono fun ω => ?_
          rw [Real.enorm_eq_ofReal (hsigM_nn ω)]
          exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
      _ = ENNReal.ofReal (M : ℝ) := by rw [lintegral_const, measure_univ, mul_one]
  have hrhoM_gt : 1 < PS.lam * ∫ ω, sigM ω ∂PS.P0 := by
    have hofReal : ENNReal.ofReal (∫ ω, sigM ω ∂PS.P0) = ∫⁻ ω, ENNReal.ofReal (sigM ω) ∂PS.P0 :=
      ofReal_integral_eq_lintegral_ofReal hsigM_int (ae_of_all _ hsigM_nn)
    have hprod : ENNReal.ofReal 1 < ENNReal.ofReal (PS.lam * ∫ ω, sigM ω ∂PS.P0) := by
      rw [ENNReal.ofReal_one, ENNReal.ofReal_mul PS.intensity.1.le, hofReal]
      exact hM
    have hpos : 0 < PS.lam * ∫ ω, sigM ω ∂PS.P0 :=
      ENNReal.ofReal_pos.mp (lt_trans (by simp) hprod)
    exact (ENNReal.ofReal_lt_ofReal_iff hpos).mp hprod
  have hsigM_null : ¬ (∀ᵐ ω ∂PS.P0, sigM ω = 0) := by
    intro h0
    have hint0 : ∫ ω, sigM ω ∂PS.P0 = 0 := integral_eq_zero_of_ae h0
    rw [hint0, mul_zero] at hrhoM_gt
    linarith
  have htauNull : ¬ (∀ᵐ ω ∂PS.P0, Q.tau 0 ω = 0) := by
    intro h
    obtain ⟨ω, hω⟩ := h.exists
    linarith [tau_pos Q 0 ω]
  have herg := queueing_ergodic_theorem PS.P0 (palmShift PS) (ergodic_palmShift Q)
    sigM (Q.tau 0) hsigM_meas ((PS.N.measurable_T 1).sub (PS.N.measurable_T 0))
    hsigM_nn (fun ω => (tau_pos Q 0 ω).le) hsigM_null htauNull hsigM_int (integrable_tau_zero Q)
  have hP0_top : ∀ᵐ ω ∂PS.P0,
      Tendsto (fun k : ℕ => PS.N.T (-k : ℤ) ω + ∑ i ∈ Finset.Icc (-k : ℤ) 0, Q.sigma i ω)
        atTop atTop := by
    filter_upwards [herg, ae_P0_zeroSet PS] with ω hlim h0
    have hlim_val : 1 < (∫ ω, sigM ω ∂PS.P0) / (∫ ω, Q.tau 0 ω ∂PS.P0) := by
      rw [integral_tau_zero Q, div_inv_eq_mul, mul_comm]
      exact hrhoM_gt
    let r := (1 + (∫ ω, sigM ω ∂PS.P0) / (∫ ω, Q.tau 0 ω ∂PS.P0)) / 2
    have hr_gt : 1 < r := by dsimp [r]; linarith
    have hr_lt : r < (∫ ω, sigM ω ∂PS.P0) / (∫ ω, Q.tau 0 ω ∂PS.P0) := by dsimp [r]; linarith
    have hev := hlim.eventually (eventually_gt_nhds hr_lt)
    have hneg : Tendsto (fun k : ℕ => -(k : ℤ)) atTop atBot := by
      rw [tendsto_atBot]; intro b
      filter_upwards [eventually_ge_atTop (-b).toNat] with k hk; omega
    have hTbot : Tendsto (fun k : ℕ => PS.N.T (-k : ℤ) ω) atTop atBot :=
      (PS.N.tendsto_atBot ω).comp hneg
    have hnegTtop : Tendsto (fun k : ℕ => -PS.N.T (-k : ℤ) ω) atTop atTop :=
      tendsto_neg_atBot_atTop.comp hTbot
    have hlin : Tendsto (fun k : ℕ => r * PS.N.T 1 ω + (r - 1) * (-PS.N.T (-k : ℤ) ω)) atTop atTop := by
      have h1 : Tendsto (fun k : ℕ => (r - 1) * (-PS.N.T (-k : ℤ) ω)) atTop atTop :=
        Tendsto.const_mul_atTop (sub_pos.mpr hr_gt) hnegTtop
      simpa [add_comm] using h1.atTop_add (tendsto_const_nhds (x := r * PS.N.T 1 ω))
    refine tendsto_atTop_mono' atTop ?_ hlin
    filter_upwards [hev] with k hk
    rw [sum_range_tau_symm Q h0 k] at hk
    have hden : 0 < PS.N.T 1 ω - PS.N.T (-k : ℤ) ω := by
      have : PS.N.T (-k : ℤ) ω ≤ PS.N.T 0 ω := (PS.N.strictMono ω).monotone (by omega)
      linarith [PS.N.lt_one ω, PS.N.zero_le ω]
    have hmul : r * (PS.N.T 1 ω - PS.N.T (-k : ℤ) ω) <
        ∑ i ∈ Finset.range (k + 1), sigM (((palmShift PS).symm^[i]) ω) :=
      (lt_div_iff₀ hden).mp hk
    have hle_sig : (∑ i ∈ Finset.range (k + 1), sigM (((palmShift PS).symm^[i]) ω)) ≤
        ∑ j ∈ Finset.Icc (-k : ℤ) 0, Q.sigma j ω := by
      rw [← sum_range_sigma_symm Q h0 k]
      exact Finset.sum_le_sum fun i _ => min_le_left _ _
    linarith
  have hP_all := ae_P_all_shifts_of_ae_P0 Q hP0_top
  filter_upwards [hP_all] with ω hω
  have h0 := hω 0
  have hrew : (fun k : ℕ => Q.toPalmSetting.N.T (-k : ℤ) ω + ∑ i ∈ Finset.Icc (-k : ℤ) 0, Q.sigma i ω) =
      fun k : ℕ => (PS.N.T (-k : ℤ) (PS.θ (PS.N.T 0 ω) ω) +
        ∑ i ∈ Finset.Icc (-k : ℤ) 0, Q.sigma i (PS.θ (PS.N.T 0 ω) ω)) + PS.N.T 0 ω := by
    funext k
    change PS.N.T (-k : ℤ) ω + _ = _
    rw [T_shift_T PS.N PS.θ PS.compatible (-k : ℤ) 0 ω, add_zero]
    have hsig : ∀ i, Q.sigma i (PS.θ (PS.N.T 0 ω) ω) = Q.sigma i ω := by
      intro i; rw [Q.sigma_marks.2 i 0 ω, add_zero]
    simp_rw [hsig]; ring
  rw [hrew]
  exact h0.atTop_add tendsto_const_nhds

lemma no_workload_of_one_lt_trafficIntensity (Q : Queue Ω) (hρ : 1 < Q.trafficIntensity) :
    ¬ ∃ W Wl : ℝ → Ω → ℝ, IsCompatible Q.toPalmSetting.θ W ∧
      ∀ᵐ ω ∂Q.toPalmSetting.P, IsWorkloadPath Q W Wl ω := by
  have := Q.toPalmSetting.isProb
  rintro ⟨W, Wl, _, hWae⟩
  have htop := tendsto_atTop_of_one_lt_trafficIntensity Q hρ
  obtain ⟨ω, hW, hωtop⟩ := (hWae.and htop).exists
  obtain ⟨k, hk⟩ := (hωtop.eventually (eventually_gt_atTop (W 0 ω))).exists
  have hle := workloadPath_loynes_le Q hW (n := (-k : ℤ)) (by omega)
  linarith

/-! ### Part 4: The Loynes construction and its pathwise properties -/

noncomputable def loynesW0 (Q : Queue Ω) (ω : Ω) : ℝ :=
  sSup (loynesSet Q ω)

noncomputable def loynesW (Q : Queue Ω) (t : ℝ) (ω : Ω) : ℝ :=
  loynesW0 Q (Q.toPalmSetting.θ t ω)

noncomputable def loynesWl (Q : Queue Ω) (s : ℝ) (ω : Ω) : ℝ :=
  (liminf (fun k : ℕ => ENNReal.ofReal (loynesW Q (s - 1 / ((k : ℝ) + 1)) ω)) atTop).toReal

lemma loynesSet_eq_range (Q : Queue Ω) (ω : Ω) :
    loynesSet Q ω = Set.range (fun k : ℕ =>
      max (Q.toPalmSetting.N.T (-k : ℤ) ω + ∑ i ∈ Finset.Icc (-k : ℤ) 0, Q.sigma i ω) 0) := by
  ext x
  simp only [loynesSet, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨(-n).toNat, ?_⟩
    have h : -((-n).toNat : ℤ) = n := by omega
    rw [h]
  · rintro ⟨k, rfl⟩
    exact ⟨(-k : ℤ), by omega, rfl⟩

lemma loynesW0_eq_iSup_toReal (Q : Queue Ω) (ω : Ω) :
    loynesW0 Q ω =
      (⨆ k : ℕ, ENNReal.ofReal (max (Q.toPalmSetting.N.T (-k : ℤ) ω +
        ∑ i ∈ Finset.Icc (-k : ℤ) 0, Q.sigma i ω) 0)).toReal := by
  let f : ℕ → ℝ := fun k => max (Q.toPalmSetting.N.T (-k : ℤ) ω +
    ∑ i ∈ Finset.Icc (-k : ℤ) 0, Q.sigma i ω) 0
  have hf_nn : ∀ k, 0 ≤ f k := fun k => le_max_right _ _
  change sSup (loynesSet Q ω) = (⨆ k : ℕ, ENNReal.ofReal (f k)).toReal
  rw [loynesSet_eq_range]
  by_cases hbdd : BddAbove (Set.range f)
  · have hS_nn : 0 ≤ sSup (Set.range f) := le_csSup_of_le hbdd ⟨0, rfl⟩ (hf_nn 0)
    have hsup_eq : (⨆ k : ℕ, ENNReal.ofReal (f k)) = ENNReal.ofReal (sSup (Set.range f)) := by
      refine le_antisymm ?_ ?_
      · exact iSup_le fun k => ENNReal.ofReal_le_ofReal (le_csSup hbdd ⟨k, rfl⟩)
      · rw [ENNReal.ofReal_le_iff_le_toReal]
        · refine csSup_le ⟨f 0, 0, rfl⟩ ?_
          rintro _ ⟨k, rfl⟩
          rw [← ENNReal.toReal_ofReal (hf_nn k)]
          refine ENNReal.toReal_mono ?_ (le_iSup (fun j => ENNReal.ofReal (f j)) k)
          obtain ⟨M, hM⟩ := hbdd
          exact ne_top_of_le_ne_top (b := ENNReal.ofReal M) ENNReal.ofReal_ne_top
            (iSup_le fun j => ENNReal.ofReal_le_ofReal (hM ⟨j, rfl⟩))
        · obtain ⟨M, hM⟩ := hbdd
          exact ne_top_of_le_ne_top (b := ENNReal.ofReal M) ENNReal.ofReal_ne_top
            (iSup_le fun j => ENNReal.ofReal_le_ofReal (hM ⟨j, rfl⟩))
    rw [hsup_eq, ENNReal.toReal_ofReal hS_nn]
  · rw [Real.sSup_of_not_bddAbove hbdd]
    have htop : (⨆ k : ℕ, ENNReal.ofReal (f k)) = ⊤ := by
      rw [eq_top_iff]
      by_contra hlt
      push Not at hlt
      have hne : (⨆ k : ℕ, ENNReal.ofReal (f k)) ≠ ⊤ := ne_top_of_lt hlt
      apply hbdd
      refine ⟨(⨆ k : ℕ, ENNReal.ofReal (f k)).toReal, ?_⟩
      rintro _ ⟨k, rfl⟩
      rw [← ENNReal.toReal_ofReal (hf_nn k)]
      exact ENNReal.toReal_mono hne (le_iSup (fun j => ENNReal.ofReal (f j)) k)
    rw [htop, ENNReal.toReal_top]

lemma measurable_loynesW0 (Q : Queue Ω) : Measurable (loynesW0 Q) := by
  have hfun : loynesW0 Q = fun ω =>
      (⨆ k : ℕ, ENNReal.ofReal (max (Q.toPalmSetting.N.T (-k : ℤ) ω +
        ∑ i ∈ Finset.Icc (-k : ℤ) 0, Q.sigma i ω) 0)).toReal :=
    funext (loynesW0_eq_iSup_toReal Q)
  rw [hfun]
  refine ENNReal.measurable_toReal.comp (Measurable.iSup fun k => ENNReal.measurable_ofReal.comp ?_)
  refine Measurable.max ?_ measurable_const
  exact (Q.toPalmSetting.N.measurable_T (-k : ℤ)).add
    (Finset.measurable_sum _ fun i _ => Q.sigma_marks.1 i)

lemma measurable_loynesW (Q : Queue Ω) (t : ℝ) : Measurable (loynesW Q t) :=
  (measurable_loynesW0 Q).comp (Q.toPalmSetting.θ.measurable' t)

lemma isCompatible_loynesW (Q : Queue Ω) : IsCompatible Q.toPalmSetting.θ (loynesW Q) := by
  intro t s ω
  unfold loynesW
  rw [← flow_add_apply]

lemma measurable_loynesWl (Q : Queue Ω) (s : ℝ) : Measurable (loynesWl Q s) := by
  unfold loynesWl
  refine ENNReal.measurable_toReal.comp (Measurable.liminf fun k => ?_)
  exact ENNReal.measurable_ofReal.comp (measurable_loynesW Q (s - 1 / ((k : ℝ) + 1)))

lemma isCompatible_loynesWl (Q : Queue Ω) : IsCompatible Q.toPalmSetting.θ (loynesWl Q) := by
  intro s t ω
  unfold loynesWl
  congr 1
  refine congrArg (fun g => liminf g atTop) (funext fun k => ?_)
  rw [isCompatible_loynesW Q]
  ring_nf

lemma loynesWl_nonneg (Q : Queue Ω) (s : ℝ) (ω : Ω) : 0 ≤ loynesWl Q s ω :=
  ENNReal.toReal_nonneg

def goodSet (Q : Queue Ω) : Set Ω :=
  {ω | Tendsto (fun k : ℕ => Q.toPalmSetting.N.T (-k : ℤ) ω +
    ∑ i ∈ Finset.Icc (-k : ℤ) 0, Q.sigma i ω) atTop atBot}

lemma goodSet_invariant (Q : Queue Ω) (t : ℝ) : Q.toPalmSetting.θ t ⁻¹' goodSet Q = goodSet Q := by
  let PS := Q.toPalmSetting
  have hshift : ∀ (s : ℝ) (ω : Ω), ω ∈ goodSet Q → PS.θ s ω ∈ goodSet Q := by
    intro s ω hω
    let m := idx PS.N s ω
    -- For k large enough (k ≥ m.natAbs), rewrite the sum
    have hconst : ∃ C : ℝ, ∀ᶠ k : ℕ in atTop,
        PS.N.T (-k : ℤ) (PS.θ s ω) + ∑ i ∈ Finset.Icc (-k : ℤ) 0, Q.sigma i (PS.θ s ω) =
          (PS.N.T (-(k - m).toNat : ℤ) ω +
            ∑ j ∈ Finset.Icc (-(k - m).toNat : ℤ) 0, Q.sigma j ω) + C := by
      rcases le_or_gt 0 m with hm | hm
      · refine ⟨(∑ j ∈ Finset.Icc (1 : ℤ) m, Q.sigma j ω) - s, ?_⟩
        filter_upwards [eventually_ge_atTop m.toNat] with k hk
        have hkm : -((k - m).toNat : ℤ) = (-k : ℤ) + m := by omega
        rw [T_shift PS.N PS.θ PS.compatible s ω (-k : ℤ), hkm]
        have hsum : (∑ i ∈ Finset.Icc (-k : ℤ) 0, Q.sigma i (PS.θ s ω)) =
            ∑ j ∈ Finset.Icc ((-k : ℤ) + m) m, Q.sigma j ω := by
          rw [Finset.sum_congr rfl fun i _ => sigma_shift Q s ω i]
          refine Finset.sum_nbij (fun i => i + m) ?_ ?_ ?_ ?_
          · intro i hi; rw [Finset.mem_Icc] at hi ⊢; omega
          · intro a _ b _ h; dsimp only at h; omega
          · intro j hj
            simp only [Finset.coe_Icc, Set.mem_Icc, Set.mem_image] at hj ⊢
            exact ⟨j - m, by omega, by omega⟩
          · intro i _; rfl
        rw [hsum]
        have hsplit : Finset.Icc ((-k : ℤ) + m) m =
            Finset.Icc ((-k : ℤ) + m) 0 ∪ Finset.Icc 1 m := by
          ext j; simp only [Finset.mem_Icc, Finset.mem_union]; omega
        have hdisj : Disjoint (Finset.Icc ((-k : ℤ) + m) 0) (Finset.Icc (1 : ℤ) m) := by
          rw [Finset.disjoint_left]; intro j hj1 hj2
          rw [Finset.mem_Icc] at hj1 hj2; omega
        rw [hsplit, Finset.sum_union hdisj]; ring
      · refine ⟨-(∑ j ∈ Finset.Icc (m + 1) 0, Q.sigma j ω) - s, ?_⟩
        filter_upwards [eventually_ge_atTop 0] with k _
        have hkm : -((k - m).toNat : ℤ) = (-k : ℤ) + m := by omega
        rw [T_shift PS.N PS.θ PS.compatible s ω (-k : ℤ), hkm]
        have hsum : (∑ i ∈ Finset.Icc (-k : ℤ) 0, Q.sigma i (PS.θ s ω)) =
            ∑ j ∈ Finset.Icc ((-k : ℤ) + m) m, Q.sigma j ω := by
          rw [Finset.sum_congr rfl fun i _ => sigma_shift Q s ω i]
          refine Finset.sum_nbij (fun i => i + m) ?_ ?_ ?_ ?_
          · intro i hi; rw [Finset.mem_Icc] at hi ⊢; omega
          · intro a _ b _ h; dsimp only at h; omega
          · intro j hj
            simp only [Finset.coe_Icc, Set.mem_Icc, Set.mem_image] at hj ⊢
            exact ⟨j - m, by omega, by omega⟩
          · intro i _; rfl
        rw [hsum]
        have hsplit : Finset.Icc ((-k : ℤ) + m) 0 =
            Finset.Icc ((-k : ℤ) + m) m ∪ Finset.Icc (m + 1) 0 := by
          ext j; simp only [Finset.mem_Icc, Finset.mem_union]; omega
        have hdisj : Disjoint (Finset.Icc ((-k : ℤ) + m) m) (Finset.Icc (m + 1) 0) := by
          rw [Finset.disjoint_left]; intro j hj1 hj2
          rw [Finset.mem_Icc] at hj1 hj2; omega
        rw [hsplit, Finset.sum_union hdisj]; ring
    obtain ⟨C, hC⟩ := hconst
    have hsub : Tendsto (fun k : ℕ => ((k : ℤ) - m).toNat) atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro b
      refine ⟨(b + m.natAbs), fun k hk => ?_⟩
      omega
    have hbase : Tendsto (fun k : ℕ => (PS.N.T (-((k : ℤ) - m).toNat : ℤ) ω +
        ∑ j ∈ Finset.Icc (-((k : ℤ) - m).toNat : ℤ) 0, Q.sigma j ω) + C) atTop atBot :=
      (hω.comp hsub).atBot_add tendsto_const_nhds
    exact hbase.congr' (hC.mono fun _ h => h.symm)
  ext ω
  exact ⟨fun h => by simpa [flow_neg_cancel] using hshift (-t) (PS.θ t ω) h, hshift t ω⟩

lemma bddAbove_branch_of_goodSet (Q : Queue Ω) {ω : Ω} (hω : ω ∈ goodSet Q) (m : ℤ) :
    BddAbove {x : ℝ | ∃ n : ℤ, n ≤ m ∧ x = Q.toPalmSetting.N.T n ω + ∑ j ∈ Finset.Icc n m, Q.sigma j ω} := by
  let PS := Q.toPalmSetting
  have hω' : PS.θ (PS.N.T m ω) ω ∈ goodSet Q :=
    (Set.ext_iff.mp (goodSet_invariant Q (PS.N.T m ω)) ω).mpr hω
  -- A sequence tending to atBot is bounded above
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (hω'.eventually (eventually_le_atBot (0 : ℝ)))
  let B : ℝ := (Finset.range (N0 + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ N0)⟩
    (fun k => PS.N.T (-k : ℤ) (PS.θ (PS.N.T m ω) ω) +
      ∑ i ∈ Finset.Icc (-k : ℤ) 0, Q.sigma i (PS.θ (PS.N.T m ω) ω))
  refine ⟨max B 0 + PS.N.T m ω, ?_⟩
  rintro _ ⟨n, hn, rfl⟩
  let k : ℕ := (m - n).toNat
  have hkn : (-k : ℤ) + m = n := by omega
  have hrew : PS.N.T n ω + ∑ j ∈ Finset.Icc n m, Q.sigma j ω =
      (PS.N.T (-k : ℤ) (PS.θ (PS.N.T m ω) ω) +
        ∑ i ∈ Finset.Icc (-k : ℤ) 0, Q.sigma i (PS.θ (PS.N.T m ω) ω)) + PS.N.T m ω := by
    rw [T_shift_T PS.N PS.θ PS.compatible (-k : ℤ) m ω, hkn]
    have hsum : (∑ i ∈ Finset.Icc (-k : ℤ) 0, Q.sigma i (PS.θ (PS.N.T m ω) ω)) =
        ∑ j ∈ Finset.Icc n m, Q.sigma j ω := by
      rw [Finset.sum_congr rfl fun i _ => Q.sigma_marks.2 i m ω]
      refine Finset.sum_nbij (fun i => i + m) ?_ ?_ ?_ ?_
      · intro i hi; rw [Finset.mem_Icc] at hi ⊢; omega
      · intro a _ b _ h; dsimp only at h; omega
      · intro j hj
        simp only [Finset.coe_Icc, Set.mem_Icc, Set.mem_image] at hj ⊢
        exact ⟨j - m, by omega, by omega⟩
      · intro i _; rfl
    rw [hsum]; ring
  rw [hrew]
  rcases le_or_gt k N0 with hk | hk
  · have hle : PS.N.T (-k : ℤ) (PS.θ (PS.N.T m ω) ω) +
        ∑ i ∈ Finset.Icc (-k : ℤ) 0, Q.sigma i (PS.θ (PS.N.T m ω) ω) ≤ B :=
      Finset.le_sup' (f := fun k : ℕ => PS.N.T (-k : ℤ) (PS.θ (PS.N.T m ω) ω) +
        ∑ i ∈ Finset.Icc (-k : ℤ) 0, Q.sigma i (PS.θ (PS.N.T m ω) ω))
        (Finset.mem_range.mpr (by omega))
    linarith [le_max_left B 0]
  · have hle : PS.N.T (-k : ℤ) (PS.θ (PS.N.T m ω) ω) +
        ∑ i ∈ Finset.Icc (-k : ℤ) 0, Q.sigma i (PS.θ (PS.N.T m ω) ω) ≤ 0 :=
      hN0 k hk.le
    linarith [le_max_right B 0]

lemma sSup_max_sub_zero {S : Set ℝ} (hne : S.Nonempty) (hbdd : BddAbove S) (t : ℝ) :
    sSup {y : ℝ | ∃ x ∈ S, y = max (x - t) 0} = max (sSup S - t) 0 := by
  let T : Set ℝ := {y : ℝ | ∃ x ∈ S, y = max (x - t) 0}
  have hTne : T.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨max (x - t) 0, x, hx, rfl⟩
  have hTbdd : BddAbove T := by
    refine ⟨max (sSup S - t) 0, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact max_le_max_right 0 (sub_le_sub_right (le_csSup hbdd hx) t)
  refine le_antisymm ?_ ?_
  · refine csSup_le hTne ?_
    rintro _ ⟨x, hx, rfl⟩
    exact max_le_max_right 0 (sub_le_sub_right (le_csSup hbdd hx) t)
  · refine max_le ?_ ?_
    · rw [sub_le_iff_le_add]
      refine csSup_le hne fun x hx => ?_
      have h1 : x - t ≤ max (x - t) 0 := le_max_left _ _
      have h2 : max (x - t) 0 ≤ sSup T := le_csSup hTbdd ⟨x, hx, rfl⟩
      linarith
    · obtain ⟨x, hx⟩ := hne
      exact le_trans (le_max_right (x - t) 0) (le_csSup hTbdd ⟨x, hx, rfl⟩)

noncomputable def loynesA (Q : Queue Ω) (m : ℤ) (ω : Ω) : ℝ :=
  sSup {x : ℝ | ∃ n : ℤ, n ≤ m ∧ x = Q.toPalmSetting.N.T n ω + ∑ j ∈ Finset.Icc n m, Q.sigma j ω}

lemma bddAbove_loynesSet_of_goodSet (Q : Queue Ω) {ω : Ω} (hω : ω ∈ goodSet Q) :
    BddAbove (loynesSet Q ω) := by
  obtain ⟨M, hM⟩ := bddAbove_branch_of_goodSet Q hω 0
  refine ⟨max M 0, ?_⟩
  rintro _ ⟨n, hn, rfl⟩
  exact max_le_max_right 0 (hM ⟨n, hn, rfl⟩)

lemma loynesW_eq_max_A_sub (Q : Queue Ω) {ω : Ω} (hω : ω ∈ goodSet Q)
    (m : ℤ) {t : ℝ} (ht : t ∈ Set.Ico (Q.toPalmSetting.N.T m ω) (Q.toPalmSetting.N.T (m + 1) ω)) :
    loynesW Q t ω = max (loynesA Q m ω - t) 0 := by
  let PS := Q.toPalmSetting
  have hidx : idx PS.N t ω = m := idx_unique PS.N t ω ht.1 ht.2
  have hset : loynesSet Q (PS.θ t ω) =
      {y : ℝ | ∃ x ∈ {x : ℝ | ∃ n : ℤ, n ≤ m ∧
        x = PS.N.T n ω + ∑ j ∈ Finset.Icc n m, Q.sigma j ω}, y = max (x - t) 0} := by
    ext y
    simp only [loynesSet, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨PS.N.T (k + m) ω + ∑ j ∈ Finset.Icc (k + m) m, Q.sigma j ω, ⟨k + m, by omega, rfl⟩, ?_⟩
      rw [T_shift PS.N PS.θ PS.compatible t ω k, hidx]
      have hsum : (∑ i ∈ Finset.Icc k 0, Q.sigma i (PS.θ t ω)) =
          ∑ j ∈ Finset.Icc (k + m) m, Q.sigma j ω := by
        rw [Finset.sum_congr rfl fun i _ => by rw [sigma_shift Q t ω i, hidx]]
        refine Finset.sum_nbij (fun i => i + m) ?_ ?_ ?_ ?_
        · intro i hi; rw [Finset.mem_Icc] at hi ⊢; omega
        · intro a _ b _ h; dsimp only at h; omega
        · intro j hj
          simp only [Finset.coe_Icc, Set.mem_Icc, Set.mem_image] at hj ⊢
          exact ⟨j - m, by omega, by omega⟩
        · intro i _; rfl
      rw [hsum]; ring_nf
    · rintro ⟨_, ⟨n, hn, rfl⟩, rfl⟩
      refine ⟨n - m, by omega, ?_⟩
      rw [T_shift PS.N PS.θ PS.compatible t ω (n - m), hidx, sub_add_cancel]
      have hsum : (∑ i ∈ Finset.Icc (n - m) 0, Q.sigma i (PS.θ t ω)) =
          ∑ j ∈ Finset.Icc n m, Q.sigma j ω := by
        rw [Finset.sum_congr rfl fun i _ => by rw [sigma_shift Q t ω i, hidx]]
        refine Finset.sum_nbij (fun i => i + m) ?_ ?_ ?_ ?_
        · intro i hi; rw [Finset.mem_Icc] at hi ⊢; omega
        · intro a _ b _ h; dsimp only at h; omega
        · intro j hj
          simp only [Finset.coe_Icc, Set.mem_Icc, Set.mem_image] at hj ⊢
          exact ⟨j - m, by omega, by omega⟩
        · intro i _; rfl
      rw [hsum]; ring_nf
  unfold loynesW loynesW0 loynesA
  rw [hset]
  exact sSup_max_sub_zero
    (S := {x : ℝ | ∃ n : ℤ, n ≤ m ∧ x = PS.N.T n ω + ∑ j ∈ Finset.Icc n m, Q.sigma j ω})
    ⟨_, m, le_rfl, rfl⟩ (bddAbove_branch_of_goodSet Q hω m) t

lemma loynesA_succ (Q : Queue Ω) {ω : Ω} (hω : ω ∈ goodSet Q) (k : ℤ) :
    loynesA Q k ω = max (loynesA Q (k - 1) ω - Q.toPalmSetting.N.T k ω) 0 +
      Q.sigma k ω + Q.toPalmSetting.N.T k ω := by
  let PS := Q.toPalmSetting
  let S_k : Set ℝ := {x : ℝ | ∃ n : ℤ, n ≤ k ∧ x = PS.N.T n ω + ∑ j ∈ Finset.Icc n k, Q.sigma j ω}
  let S_prev : Set ℝ := {x : ℝ | ∃ n : ℤ, n ≤ k - 1 ∧ x = PS.N.T n ω + ∑ j ∈ Finset.Icc n (k - 1), Q.sigma j ω}
  have hne_k : S_k.Nonempty := ⟨_, k, le_rfl, rfl⟩
  have hne_prev : S_prev.Nonempty := ⟨_, k - 1, le_rfl, rfl⟩
  have hbdd_k : BddAbove S_k := bddAbove_branch_of_goodSet Q hω k
  have hbdd_prev : BddAbove S_prev := bddAbove_branch_of_goodSet Q hω (k - 1)
  change sSup S_k = max (sSup S_prev - PS.N.T k ω) 0 + Q.sigma k ω + PS.N.T k ω
  have hRHS : max (sSup S_prev - PS.N.T k ω) 0 + Q.sigma k ω + PS.N.T k ω =
      max (sSup S_prev + Q.sigma k ω) (PS.N.T k ω + Q.sigma k ω) := by
    rcases le_or_gt (sSup S_prev) (PS.N.T k ω) with h | h
    · rw [max_eq_right (by linarith), max_eq_right (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; ring
  rw [hRHS]
  refine le_antisymm ?_ ?_
  · refine csSup_le hne_k ?_
    rintro _ ⟨n, hn, rfl⟩
    rcases eq_or_lt_of_le hn with rfl | hlt
    · simp only [Finset.Icc_self, Finset.sum_singleton]
      exact le_max_right _ _
    · have hIcc : Finset.Icc n k = insert k (Finset.Icc n (k - 1)) := by
        ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp)]
      have hmem : PS.N.T n ω + ∑ j ∈ Finset.Icc n (k - 1), Q.sigma j ω ∈ S_prev :=
        ⟨n, by omega, rfl⟩
      have hle : PS.N.T n ω + ∑ j ∈ Finset.Icc n (k - 1), Q.sigma j ω ≤ sSup S_prev :=
        le_csSup hbdd_prev hmem
      exact le_trans (by linarith) (le_max_left _ _)
  · refine max_le ?_ ?_
    · rw [← le_sub_iff_add_le]
      refine csSup_le hne_prev ?_
      rintro _ ⟨n, hn, rfl⟩
      rw [le_sub_iff_add_le]
      have hIcc : Finset.Icc n k = insert k (Finset.Icc n (k - 1)) := by
        ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hmem : PS.N.T n ω + ∑ j ∈ Finset.Icc n k, Q.sigma j ω ∈ S_k :=
        ⟨n, by omega, rfl⟩
      have hle := le_csSup hbdd_k hmem
      rw [hIcc, Finset.sum_insert (by simp)] at hle
      linarith
    · refine le_csSup hbdd_k ⟨k, le_rfl, ?_⟩
      simp

lemma isWorkloadPath_loynes_of_mem_goodSet (Q : Queue Ω) {ω : Ω} (hω : ω ∈ goodSet Q) :
    IsWorkloadPath Q (loynesW Q) (loynesWl Q) ω := by
  let PS := Q.toPalmSetting
  -- Helper: for every s, find m with T m ω < s ≤ T (m + 1) ω
  have hleft_int : ∀ s : ℝ, ∃ m : ℤ, PS.N.T m ω < s ∧ s ≤ PS.N.T (m + 1) ω := by
    intro s
    let k := idx PS.N s ω
    have hk := idx_spec PS.N s ω
    rcases eq_or_lt_of_le hk.1 with heq | hlt
    · refine ⟨k - 1, ?_, ?_⟩
      · rw [← heq]; exact PS.N.strictMono ω (by omega)
      · rw [sub_add_cancel, heq]
    · exact ⟨k, hlt, hk.2.le⟩
  -- Left limit at s equals max (loynesA Q m ω - s) 0
  have hleft_lim : ∀ (s : ℝ) (m : ℤ), PS.N.T m ω < s → s ≤ PS.N.T (m + 1) ω →
      Tendsto (fun u => loynesW Q u ω) (nhdsWithin s (Set.Iio s)) (nhds (max (loynesA Q m ω - s) 0)) := by
    intro s m hm1 hm2
    have hcont : Continuous (fun u : ℝ => max (loynesA Q m ω - u) 0) :=
      (continuous_const.sub continuous_id).max continuous_const
    have hlim := hcont.continuousAt (x := s) |>.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio s))
    refine hlim.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hm1] with u hu
    exact (loynesW_eq_max_A_sub Q hω m ⟨hu.1.le, lt_of_lt_of_le hu.2 hm2⟩).symm
  -- Therefore loynesWl Q s ω = max (loynesA Q m ω - s) 0
  have hWl_eq : ∀ (s : ℝ) (m : ℤ), PS.N.T m ω < s → s ≤ PS.N.T (m + 1) ω →
      loynesWl Q s ω = max (loynesA Q m ω - s) 0 := by
    intro s m hm1 hm2
    have hlim := hleft_lim s m hm1 hm2
    have hseq : Tendsto (fun k : ℕ => s - 1 / ((k : ℝ) + 1)) atTop (nhdsWithin s (Set.Iio s)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall fun k => ?_⟩
      · have h0 : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (nhds 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa using tendsto_const_nhds.sub h0
      · show s - 1 / ((k : ℝ) + 1) < s
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    have hlim_seq : Tendsto (fun k : ℕ => loynesW Q (s - 1 / ((k : ℝ) + 1)) ω) atTop
        (nhds (max (loynesA Q m ω - s) 0)) := hlim.comp hseq
    have hlim_enn : Tendsto (fun k : ℕ => ENNReal.ofReal (loynesW Q (s - 1 / ((k : ℝ) + 1)) ω)) atTop
        (nhds (ENNReal.ofReal (max (loynesA Q m ω - s) 0))) :=
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim_seq
    unfold loynesWl
    rw [hlim_enn.liminf_eq, ENNReal.toReal_ofReal (le_max_right _ _)]
  refine ⟨?_, ?_, ?_⟩
  · -- Right continuity
    intro s
    let m := idx PS.N s ω
    have hm := idx_spec PS.N s ω
    have hcont : ContinuousWithinAt (fun u : ℝ => max (loynesA Q m ω - u) 0) (Set.Ici s) s :=
      ((continuous_const.sub continuous_id).max continuous_const).continuousWithinAt
    refine hcont.congr_of_eventuallyEq ?_ (loynesW_eq_max_A_sub Q hω m ⟨hm.1, hm.2⟩)
    filter_upwards [Ico_mem_nhdsGE hm.2] with u hu
    exact loynesW_eq_max_A_sub Q hω m ⟨le_trans hm.1 hu.1, hu.2⟩
  · -- Left limits
    intro s
    obtain ⟨m, hm1, hm2⟩ := hleft_int s
    rw [hWl_eq s m hm1 hm2]
    exact hleft_lim s m hm1 hm2
  · -- Lindley's equation
    intro k t ht
    rw [loynesW_eq_max_A_sub Q hω k ht]
    have hWl_k : loynesWl Q (PS.N.T k ω) ω = max (loynesA Q (k - 1) ω - PS.N.T k ω) 0 := by
      refine hWl_eq (PS.N.T k ω) (k - 1) (PS.N.strictMono ω (by omega)) ?_
      rw [sub_add_cancel]
    rw [loynesA_succ Q hω k, ← hWl_k]
    dsimp [PS]
    congr 1; ring

/-! ### Part 5: Empty times and uniqueness when `ρ < 1` -/

lemma P0_empty_pos (Q : Queue Ω) (hρ : Q.trafficIntensity < 1) :
    0 < Q.toPalmSetting.P0 {ω | loynesWl Q 0 ω = 0} := by
  let PS := Q.toPalmSetting
  have := PS.isProb
  have := PS.palm.1
  obtain ⟨hsigInt, hrho_lt⟩ := integrable_sigma_zero_of_lt_one Q hρ
  -- Get a measurable θ-invariant subset G ⊆ goodSet Q with P G = 1, hence P0 G = 1
  have hgood_ae := tendsto_atBot_of_trafficIntensity_lt_one Q hρ
  obtain ⟨G, hG_meas, hG_inv, hG_sub, hPG⟩ :=
    exists_measurable_invariant_subset_of_ae PS (goodSet_invariant Q) hgood_ae
  have hP0G : PS.P0 G = 1 := ae_P0_of_P_invariant PS hG_meas hG_inv hPG
  have haeG : ∀ᵐ ω ∂PS.P0, ω ∈ G := by
    rw [ae_iff]; exact (prob_compl_eq_zero_iff hG_meas).mpr hP0G
  by_contra hle
  rw [not_lt, nonpos_iff_eq_zero] at hle
  have hmp := measurePreserving_palmShift PS
  have hE_meas : MeasurableSet {ω | loynesWl Q 0 ω = 0} :=
    measurableSet_eq_fun (measurable_loynesWl Q 0) measurable_const
  have hS_zero : PS.P0 (palmShift PS ⁻¹' {ω | loynesWl Q 0 ω = 0}) = 0 := by
    rw [hmp.measure_preimage hE_meas.nullMeasurableSet]; exact hle
  have hae_pos : ∀ᵐ ω ∂PS.P0, 0 < loynesWl Q 0 (palmShift PS ω) := by
    have hae_ne : ∀ᵐ ω ∂PS.P0, loynesWl Q 0 (palmShift PS ω) ≠ 0 := by
      rw [ae_iff]; simpa using hS_zero
    filter_upwards [hae_ne] with ω hne
    exact lt_of_le_of_ne (loynesWl_nonneg Q 0 _) hne.symm
  -- On G ∩ zeroSet ∩ {Wl 0 (S ω) > 0}, Wl 0 ω - Wl 0 (S ω) = τ₀ ω - σ₀ ω
  have hdiff_ae : (fun ω => loynesWl Q 0 ω - loynesWl Q 0 (palmShift PS ω)) =ᵐ[PS.P0]
      (fun ω => Q.tau 0 ω - Q.sigma 0 ω) := by
    filter_upwards [haeG, ae_P0_zeroSet PS, hae_pos] with ω hωG h0 hpos
    have hpath := isWorkloadPath_loynes_of_mem_goodSet Q (hG_sub hωG)
    have hstep := workloadPath_lindley_step Q hpath 0
    simp only [zero_add] at hstep
    rw [h0] at hstep
    have hS : loynesWl Q 0 (palmShift PS ω) = loynesWl Q (PS.N.T 1 ω) ω := by
      rw [palmShift_apply_of_zero PS h0, isCompatible_loynesWl Q, zero_add]
    rw [hS] at hpos ⊢
    rw [hstep] at hpos ⊢
    have hinner : 0 < loynesWl Q 0 ω + Q.sigma 0 ω - Q.tau 0 ω := by
      by_contra hle'
      push Not at hle'
      rw [max_eq_right hle'] at hpos
      exact lt_irrefl 0 hpos
    rw [max_eq_left hinner.le]
    ring
  have hint_rhs : Integrable (fun ω => Q.tau 0 ω - Q.sigma 0 ω) PS.P0 :=
    (integrable_tau_zero Q).sub hsigInt
  have hint_lhs : Integrable (fun ω => loynesWl Q 0 ω - loynesWl Q 0 (palmShift PS ω)) PS.P0 :=
    hint_rhs.congr hdiff_ae.symm
  have hzero_int : ∫ ω, (loynesWl Q 0 ω - loynesWl Q 0 (palmShift PS ω)) ∂PS.P0 = 0 :=
    ergodic_lemma PS.P0 (palmShift PS) (palmShift PS).measurable hmp.map_eq
      (loynesWl Q 0) (measurable_loynesWl Q 0) (loynesWl_nonneg Q 0) hint_lhs
  rw [integral_congr_ae hdiff_ae, integral_sub (integrable_tau_zero Q) hsigInt,
      integral_tau_zero Q] at hzero_int
  have heq : ∫ ω, Q.sigma 0 ω ∂PS.P0 = PS.lam⁻¹ := by linarith
  rw [heq, mul_inv_cancel₀ PS.intensity.1.ne'] at hrho_lt
  exact lt_irrefl 1 hrho_lt

lemma infinitely_many_empty_times (Q : Queue Ω) (hρ : Q.trafficIntensity < 1) :
    ∀ᵐ ω ∂Q.toPalmSetting.P,
      {n : ℤ | n < 0 ∧ loynesWl Q (Q.toPalmSetting.N.T n ω) ω = 0}.Infinite ∧
      {n : ℤ | 0 < n ∧ loynesWl Q (Q.toPalmSetting.N.T n ω) ω = 0}.Infinite := by
  let PS := Q.toPalmSetting
  have := PS.isProb
  have := PS.palm.1
  let E : Set Ω := {ω | loynesWl Q 0 ω = 0}
  have hE_meas : MeasurableSet E := measurableSet_eq_fun (measurable_loynesWl Q 0) measurable_const
  have hE_pos : 0 < PS.P0 E := P0_empty_pos Q hρ
  -- Helper: for any ergodic measurable equiv f preserving P0, P0-a.e. ω has infinitely many k > 0 with f^[k] ω ∈ E
  have hinf_dir : ∀ (f : Ω ≃ᵐ Ω), Ergodic f PS.P0 →
      ∀ᵐ ω ∂PS.P0, {k : ℕ | 0 < k ∧ f^[k] ω ∈ E}.Infinite := by
    intro f hf
    let B : Set Ω := ⋂ N : ℕ, ⋃ k : ℕ, ⋃ (_ : N + 1 ≤ k), f^[k] ⁻¹' E
    have hB_meas : MeasurableSet B :=
      MeasurableSet.iInter fun N => MeasurableSet.iUnion fun k =>
        MeasurableSet.iUnion fun _ => (f.measurable.iterate k) hE_meas
    have hB_eq : ∀ ω, ω ∈ B ↔ {k : ℕ | 0 < k ∧ f^[k] ω ∈ E}.Infinite := by
      intro ω
      rw [Set.infinite_iff_exists_gt]
      simp only [B, Set.mem_iInter, Set.mem_iUnion, Set.mem_preimage, Set.mem_ofPred_eq]
      constructor
      · intro h N
        obtain ⟨k, hk, hmem⟩ := h N
        exact ⟨k, ⟨by omega, hmem⟩, by omega⟩
      · intro h N
        obtain ⟨k, ⟨_, hmem⟩, hk⟩ := h N
        exact ⟨k, by omega, hmem⟩
    have hB_inv : f ⁻¹' B = B := by
      ext ω
      rw [Set.mem_preimage, hB_eq, hB_eq]
      simp only [Set.infinite_iff_exists_gt, Set.mem_ofPred_eq]
      constructor
      · intro h N
        obtain ⟨k, ⟨_, hmem⟩, hk⟩ := h N
        refine ⟨k + 1, ⟨by omega, ?_⟩, by omega⟩
        rwa [Function.iterate_succ_apply]
      · intro h N
        obtain ⟨k, ⟨_, hmem⟩, hk⟩ := h (N + 1)
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        refine ⟨k', ⟨by omega, ?_⟩, by omega⟩
        rwa [← Function.iterate_succ_apply]
    -- Show P0 B > 0 using Poincaré recurrence (Conservative)
    have hcons : Conservative f PS.P0 := hf.toMeasurePreserving.conservative
    have hrec : ∀ᵐ ω ∂PS.P0, ω ∈ E → ∃ᶠ k in atTop, f^[k] ω ∈ E :=
      hcons.ae_mem_imp_frequently_image_mem hE_meas.nullMeasurableSet
    have hEB : PS.P0 E ≤ PS.P0 B := by
      have hsub : ∀ᵐ ω ∂PS.P0, ω ∈ E → ω ∈ B := by
        filter_upwards [hrec] with ω hω hmem
        rw [hB_eq, Set.infinite_iff_exists_gt]
        intro N
        have hfreq := (Filter.frequently_atTop.mp (hω hmem)) (N + 1)
        obtain ⟨k, hk, hfk⟩ := hfreq
        exact ⟨k, ⟨by omega, hfk⟩, by omega⟩
      have hdiff : PS.P0 (E \ B) = 0 := by
        have : ∀ᵐ ω ∂PS.P0, ω ∉ E \ B := by
          filter_upwards [hsub] with ω hω hmem
          exact hmem.2 (hω hmem.1)
        rw [ae_iff] at this
        have heq : {a | ¬ a ∉ E \ B} = E \ B := by ext a; simp
        rwa [heq] at this
      calc PS.P0 E ≤ PS.P0 (E \ B ∪ B) := measure_mono (fun x hx => by by_cases hxB : x ∈ B; exact Or.inr hxB; exact Or.inl ⟨hx, hxB⟩)
        _ ≤ PS.P0 (E \ B) + PS.P0 B := measure_union_le _ _
        _ = PS.P0 B := by rw [hdiff, zero_add]
    have hB_pos : 0 < PS.P0 B := lt_of_lt_of_le hE_pos hEB
    -- By ergodicity, P0 Bᶜ = 0
    have hconst := hf.ae_empty_or_univ hB_meas hB_inv
    rcases hconst with h0 | h1
    · exfalso
      have h0' : PS.P0 B = 0 := ae_eq_empty.mp h0
      rw [h0'] at hB_pos
      exact lt_irrefl 0 hB_pos
    · have hBc0 : PS.P0 Bᶜ = 0 := ae_eq_univ.mp h1
      have haeB : ∀ᵐ ω ∂PS.P0, ω ∈ B := by rw [ae_iff]; exact hBc0
      filter_upwards [haeB] with ω hω
      exact (hB_eq ω).mp hω
  have herg_fwd : Ergodic (palmShift PS) PS.P0 := ergodic_palmShift Q
  have herg_bwd : Ergodic (palmShift PS).symm PS.P0 := by
    rcases herg_fwd with ⟨hmp_fwd, ⟨hpre⟩⟩
    refine ⟨hmp_fwd.symm (palmShift PS), ⟨fun B hB hBinv => ?_⟩⟩
    have hBinv_fwd : palmShift PS ⁻¹' B = B := by
      ext ω
      have := Set.ext_iff.mp hBinv (palmShift PS ω)
      change (palmShift PS).symm (palmShift PS ω) ∈ B ↔ palmShift PS ω ∈ B at this
      rw [(palmShift PS).symm_apply_apply] at this
      exact this.symm
    exact hpre hB hBinv_fwd
  have hP0_both : ∀ᵐ ω ∂PS.P0,
      {k : ℕ | 0 < k ∧ ((palmShift PS).symm^[k]) ω ∈ E}.Infinite ∧
      {k : ℕ | 0 < k ∧ (palmShift PS)^[k] ω ∈ E}.Infinite :=
    (hinf_dir (palmShift PS).symm herg_bwd).and (hinf_dir (palmShift PS) herg_fwd)
  have hP_all := ae_P_all_shifts_of_ae_P0 Q hP0_both
  filter_upwards [hP_all] with ω hω
  obtain ⟨hneg, hpos⟩ := hω 0
  let ω0 := PS.θ (PS.N.T 0 ω) ω
  have hω0 : PS.N.T 0 ω0 = 0 := T_zero_shift_T PS.N PS.θ PS.compatible 0 ω
  have hshift_eq : ∀ n : ℤ, loynesWl Q 0 (PS.θ (PS.N.T n ω0) ω0) = loynesWl Q (PS.N.T n ω) ω := by
    intro n
    have hTn : PS.θ (PS.N.T n ω0) ω0 = PS.θ (PS.N.T n ω) ω := by
      dsimp [ω0]
      rw [T_shift_T PS.N PS.θ PS.compatible n 0 ω, add_zero, ← flow_add_apply, sub_add_cancel]
    rw [hTn, isCompatible_loynesWl Q, zero_add]
  constructor
  · refine Set.Infinite.mono (s := (fun k : ℕ => -(k : ℤ)) '' {k : ℕ | 0 < k ∧ ((palmShift PS).symm^[k]) ω0 ∈ E}) ?_ ?_
    · rintro _ ⟨k, ⟨hk, hmem⟩, rfl⟩
      dsimp only
      refine ⟨by omega, ?_⟩
      change loynesWl Q 0 (((palmShift PS).symm^[k]) ω0) = 0 at hmem
      rw [palmShift_symm_iterate_of_zero PS hω0 k, hshift_eq (-k : ℤ)] at hmem
      exact hmem
    · exact hneg.image (fun a _ b _ h => by omega)
  · refine Set.Infinite.mono (s := (fun k : ℕ => (k : ℤ)) '' {k : ℕ | 0 < k ∧ (palmShift PS)^[k] ω0 ∈ E}) ?_ ?_
    · rintro _ ⟨k, ⟨hk, hmem⟩, rfl⟩
      dsimp only
      refine ⟨by omega, ?_⟩
      change loynesWl Q 0 ((palmShift PS)^[k] ω0) = 0 at hmem
      rw [palmShift_iterate_of_zero PS hω0 k, hshift_eq (k : ℤ)] at hmem
      exact hmem
    · exact hpos.image (fun a _ b _ h => by omega)

lemma loynes_uniqueness (Q : Queue Ω) (hρ : Q.trafficIntensity < 1)
    (W' Wl' : ℝ → Ω → ℝ) (hW'meas : ∀ t : ℝ, Measurable (W' t))
    (hW'comp : IsCompatible Q.toPalmSetting.θ W')
    (hW'path : ∀ᵐ ω ∂Q.toPalmSetting.P, IsWorkloadPath Q W' Wl' ω) :
    ∀ᵐ ω ∂Q.toPalmSetting.P, ∀ t : ℝ, W' t ω = loynesW Q t ω := by
  let PS := Q.toPalmSetting
  have := PS.isProb
  have := PS.palm.1
  obtain ⟨hsigInt, hrho_lt⟩ := integrable_sigma_zero_of_lt_one Q hρ
  -- Canonical measurable θ-compatible left-limit process for W'
  let Wl'c : ℝ → Ω → ℝ := fun s ω =>
    (liminf (fun k : ℕ => ENNReal.ofReal (W' (s - 1 / ((k : ℝ) + 1)) ω)) atTop).toReal
  have hWl'c_meas : ∀ s, Measurable (Wl'c s) := fun s =>
    ENNReal.measurable_toReal.comp (Measurable.liminf fun k =>
      ENNReal.measurable_ofReal.comp (hW'meas (s - 1 / ((k : ℝ) + 1))))
  have hWl'c_comp : IsCompatible PS.θ Wl'c := by
    intro s t ω
    dsimp [Wl'c]
    congr 1
    refine congrArg (fun g => liminf g atTop) (funext fun k => ?_)
    rw [hW'comp]; ring_nf
  -- Whenever IsWorkloadPath Q W' Wl' ω holds, Wl'c agrees with Wl'
  have hWl'c_eq : ∀ {ω : Ω}, IsWorkloadPath Q W' Wl' ω → ∀ s : ℝ, Wl'c s ω = Wl' s ω := by
    intro ω hpath s
    have hseq : Tendsto (fun k : ℕ => s - 1 / ((k : ℝ) + 1)) atTop (nhdsWithin s (Set.Iio s)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall fun k => ?_⟩
      · have h0 : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (nhds 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa using tendsto_const_nhds.sub h0
      · show s - 1 / ((k : ℝ) + 1) < s
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    have hlim_seq : Tendsto (fun k : ℕ => W' (s - 1 / ((k : ℝ) + 1)) ω) atTop (nhds (Wl' s ω)) :=
      (hpath.2.1 s).comp hseq
    have hlim_enn : Tendsto (fun k : ℕ => ENNReal.ofReal (W' (s - 1 / ((k : ℝ) + 1)) ω)) atTop
        (nhds (ENNReal.ofReal (Wl' s ω))) :=
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim_seq
    dsimp [Wl'c]
    rw [hlim_enn.liminf_eq, ENNReal.toReal_ofReal (workloadPath_Wl_nonneg Q hpath s)]
  -- The set S_path := {ω | IsWorkloadPath Q W' Wl'c ω} is θ-invariant and P-a.s.
  let S_path : Set Ω := {ω | IsWorkloadPath Q W' Wl'c ω}
  have hS_path_ae : ∀ᵐ ω ∂PS.P, ω ∈ S_path := by
    filter_upwards [hW'path] with ω hpath
    have heq := hWl'c_eq hpath
    refine ⟨hpath.1, fun s => by rw [heq s]; exact hpath.2.1 s, fun n t ht => ?_⟩
    rw [heq (PS.N.T n ω)]
    exact hpath.2.2 n t ht
  have hS_path_inv : ∀ s : ℝ, PS.θ s ⁻¹' S_path = S_path := by
    have hdir : ∀ (s : ℝ) (ω : Ω), ω ∈ S_path → PS.θ s ω ∈ S_path := by
      intro s ω hpath
      refine ⟨?_, ?_, ?_⟩
      · intro t
        have h1 : ContinuousWithinAt (fun u => W' u ω) (Set.Ici (t + s)) (t + s) := hpath.1 (t + s)
        have h2 : ContinuousWithinAt (fun u => u + s) (Set.Ici t) t :=
          (continuous_id.add continuous_const).continuousWithinAt
        have hmaps : Set.MapsTo (fun u => u + s) (Set.Ici t) (Set.Ici (t + s)) :=
          fun u hu => by show t + s ≤ u + s; linarith [Set.mem_Ici.mp hu]
        have hcomp := ContinuousWithinAt.comp (g := fun u => W' u ω) (f := fun u => u + s) h1 h2 hmaps
        exact hcomp.congr (fun u _ => hW'comp u s ω) (hW'comp t s ω)
      · intro t
        have h1 := hpath.2.1 (t + s)
        have h2 : Tendsto (fun u => u + s) (nhdsWithin t (Set.Iio t)) (nhdsWithin (t + s) (Set.Iio (t + s))) := by
          rw [tendsto_nhdsWithin_iff]
          refine ⟨(continuous_id.add continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
            eventually_nhdsWithin_of_forall fun u hu => by show u + s < t + s; linarith [Set.mem_Iio.mp hu]⟩
        have hcomp := h1.comp h2
        rw [hWl'c_comp t s ω]
        exact hcomp.congr fun u => (hW'comp u s ω).symm
      · intro n t ht
        let k := idx PS.N s ω
        have ht' : t + s ∈ Set.Ico (PS.N.T (n + k) ω) (PS.N.T (n + k + 1) ω) := by
          have h1 := T_shift PS.N PS.θ PS.compatible s ω n
          have h2 := T_shift PS.N PS.θ PS.compatible s ω (n + 1)
          have h3 : n + 1 + k = n + k + 1 := by omega
          rw [h3] at h2
          exact ⟨by linarith [ht.1, h1], by linarith [ht.2, h2]⟩
        rw [hW'comp t s ω, hpath.2.2 (n + k) (t + s) ht']
        rw [T_shift PS.N PS.θ PS.compatible s ω n, hWl'c_comp, sigma_shift Q s ω n]
        have : PS.N.T (n + k) ω - s + s = PS.N.T (n + k) ω := sub_add_cancel _ _
        rw [this]
        dsimp [PS, k]; congr 1; ring
    intro s; ext ω
    exact ⟨fun h => by simpa [flow_neg_cancel] using hdir (-s) (PS.θ s ω) h, hdir s ω⟩
  -- Build a measurable θ-invariant set G ⊆ S_path ∩ goodSet Q with P G = 1 and P0 G = 1
  have hgood_ae := tendsto_atBot_of_trafficIntensity_lt_one Q hρ
  have hboth_inv : ∀ s : ℝ, PS.θ s ⁻¹' (S_path ∩ goodSet Q) = S_path ∩ goodSet Q := fun s => by
    rw [Set.preimage_inter, hS_path_inv s, goodSet_invariant Q s]
  obtain ⟨G, hG_meas, hG_inv, hG_sub, hPG⟩ :=
    exists_measurable_invariant_subset_of_ae PS hboth_inv (hS_path_ae.and hgood_ae)
  have hP0G : PS.P0 G = 1 := ae_P0_of_P_invariant PS hG_meas hG_inv hPG
  have haeG_P0 : ∀ᵐ ω ∂PS.P0, ω ∈ G := by
    rw [ae_iff]; exact (prob_compl_eq_zero_iff hG_meas).mpr hP0G
  have haeG_P : ∀ᵐ ω ∂PS.P, ω ∈ G := by
    rw [ae_iff]; exact (prob_compl_eq_zero_iff hG_meas).mpr hPG
  -- On G, Wl'c t ω ≥ loynesWl Q t ω for all t
  have hge_G : ∀ {ω : Ω}, ω ∈ G → ∀ t : ℝ, loynesW Q t ω ≤ W' t ω := by
    intro ω hω t
    have hθ : PS.θ t ω ∈ G := (Set.ext_iff.mp (hG_inv t) ω).mpr hω
    have ⟨hpath', hgood'⟩ := hG_sub hθ
    have hW't : W' t ω = W' 0 (PS.θ t ω) := by rw [hW'comp 0 t ω, zero_add]
    rw [hW't]
    have hW0_ge : loynesW0 Q (PS.θ t ω) ≤ W' 0 (PS.θ t ω) := by
      unfold loynesW0
      refine csSup_le ⟨_, 0, le_rfl, rfl⟩ ?_
      rintro _ ⟨n, hn, rfl⟩
      exact max_le (workloadPath_loynes_le Q hpath' hn) (workloadPath_nonneg Q hpath' 0)
    exact hW0_ge
  have hWl_ge_G : ∀ {ω : Ω}, ω ∈ G → ∀ s : ℝ, loynesWl Q s ω ≤ Wl'c s ω := by
    intro ω hω s
    have ⟨hpath', hgood'⟩ := hG_sub hω
    have hpath := isWorkloadPath_loynes_of_mem_goodSet Q hgood'
    have : NeBot (nhdsWithin s (Set.Iio s)) := nhdsLT_neBot s
    exact le_of_tendsto_of_tendsto (hpath.2.1 s) (hpath'.2.1 s) (Eventually.of_forall fun u => hge_G hω u)
  -- Define Z ω = max (Wl'c 0 ω - loynesWl Q 0 ω) 0
  let Z : Ω → ℝ := fun ω => max (Wl'c 0 ω - loynesWl Q 0 ω) 0
  have hZ_meas : Measurable Z := ((hWl'c_meas 0).sub (measurable_loynesWl Q 0)).max measurable_const
  have hZ_nn : ∀ ω, 0 ≤ Z ω := fun ω => le_max_right _ _
  -- P0-a.e., Z (S ω) ≤ Z ω
  have hZ_dec : ∀ᵐ ω ∂PS.P0, Z (palmShift PS ω) ≤ Z ω := by
    filter_upwards [haeG_P0, ae_P0_zeroSet PS] with ω hωG h0
    have ⟨hpath', hgood'⟩ := hG_sub hωG
    have hpath := isWorkloadPath_loynes_of_mem_goodSet Q hgood'
    have hZω : Z ω = Wl'c 0 ω - loynesWl Q 0 ω := max_eq_left (sub_nonneg.mpr (hWl_ge_G hωG 0))
    have hSωG : palmShift PS ω ∈ G := by
      rw [palmShift_apply_of_zero PS h0]
      exact (Set.ext_iff.mp (hG_inv (PS.N.T 1 ω)) ω).mpr hωG
    have hZSω : Z (palmShift PS ω) = Wl'c (PS.N.T 1 ω) ω - loynesWl Q (PS.N.T 1 ω) ω := by
      dsimp [Z]
      rw [max_eq_left (sub_nonneg.mpr (hWl_ge_G hSωG 0)), palmShift_apply_of_zero PS h0,
          hWl'c_comp, isCompatible_loynesWl Q, zero_add]
    rw [hZω, hZSω]
    have hs1 := workloadPath_lindley_step Q hpath' 0
    have hs2 := workloadPath_lindley_step Q hpath 0
    have h0' : Q.toPalmSetting.N.T 0 ω = 0 := h0
    simp only [zero_add, h0'] at hs1 hs2
    rw [hs1, hs2]
    have hle : loynesWl Q 0 ω ≤ Wl'c 0 ω := hWl_ge_G hωG 0
    rcases le_or_gt (Wl'c 0 ω + Q.sigma 0 ω - Q.tau 0 ω) 0 with h1 | h1
    · rw [max_eq_right h1, max_eq_right (by linarith)]; linarith
    · rw [max_eq_left h1.le]
      have := le_max_left (loynesWl Q 0 ω + Q.sigma 0 ω - Q.tau 0 ω) 0
      linarith
  -- Since S preserves P0 and Z (S ω) ≤ Z ω a.e., Z (S ω) = Z ω P0-a.e.
  have hmp := measurePreserving_palmShift PS
  have hZ_eq_S : ∀ᵐ ω ∂PS.P0, Z (palmShift PS ω) = Z ω := by
    have hM : ∀ M : ℕ, ∀ᵐ ω ∂PS.P0, min (Z (palmShift PS ω)) (M : ℝ) = min (Z ω) (M : ℝ) := by
      intro M
      have hintM : Integrable (fun ω => min (Z ω) (M : ℝ)) PS.P0 := by
        refine ⟨(hZ_meas.min measurable_const).aestronglyMeasurable, ?_⟩
        rw [HasFiniteIntegral]
        refine lt_of_le_of_lt (b := ENNReal.ofReal (M : ℝ)) ?_ ENNReal.ofReal_lt_top
        calc ∫⁻ ω, ‖min (Z ω) (M : ℝ)‖ₑ ∂PS.P0
            ≤ ∫⁻ _, ENNReal.ofReal (M : ℝ) ∂PS.P0 := by
              refine lintegral_mono fun ω => ?_
              rw [Real.enorm_eq_ofReal (le_min (hZ_nn ω) (Nat.cast_nonneg M))]
              exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
          _ = ENNReal.ofReal (M : ℝ) := by rw [lintegral_const, measure_univ, mul_one]
      have hintM_S : Integrable (fun ω => min (Z (palmShift PS ω)) (M : ℝ)) PS.P0 := by
        refine ⟨((hZ_meas.comp (palmShift PS).measurable).min measurable_const).aestronglyMeasurable, ?_⟩
        rw [HasFiniteIntegral]
        refine lt_of_le_of_lt (b := ENNReal.ofReal (M : ℝ)) ?_ ENNReal.ofReal_lt_top
        calc ∫⁻ ω, ‖min (Z (palmShift PS ω)) (M : ℝ)‖ₑ ∂PS.P0
            ≤ ∫⁻ _, ENNReal.ofReal (M : ℝ) ∂PS.P0 := by
              refine lintegral_mono fun ω => ?_
              rw [Real.enorm_eq_ofReal (le_min (hZ_nn _) (Nat.cast_nonneg M))]
              exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
          _ = ENNReal.ofReal (M : ℝ) := by rw [lintegral_const, measure_univ, mul_one]
      have hint_eq : ∫ ω, (min (Z ω) (M : ℝ) - min (Z (palmShift PS ω)) (M : ℝ)) ∂PS.P0 = 0 := by
        rw [integral_sub hintM hintM_S, hmp.integral_comp' (g := fun ω => min (Z ω) (M : ℝ)), sub_self]
      have hnn : 0 ≤ᵐ[PS.P0] fun ω => min (Z ω) (M : ℝ) - min (Z (palmShift PS ω)) (M : ℝ) := by
        filter_upwards [hZ_dec] with ω hω
        exact sub_nonneg.mpr (min_le_min_right (M : ℝ) hω)
      have h0 := (integral_eq_zero_iff_of_nonneg_ae hnn (hintM.sub hintM_S)).mp hint_eq
      filter_upwards [h0] with ω hω
      change min (Z ω) (M : ℝ) - min (Z (palmShift PS ω)) (M : ℝ) = 0 at hω
      linarith
    have hall : ∀ᵐ ω ∂PS.P0, ∀ M : ℕ, min (Z (palmShift PS ω)) (M : ℝ) = min (Z ω) (M : ℝ) :=
      ae_all_iff.mpr hM
    filter_upwards [hall] with ω hω
    obtain ⟨M, hM⟩ := exists_nat_gt (max (Z (palmShift PS ω)) (Z ω))
    have h1 : Z (palmShift PS ω) ≤ (M : ℝ) := le_trans (le_max_left _ _) hM.le
    have h2 : Z ω ≤ (M : ℝ) := le_trans (le_max_right _ _) hM.le
    have hEq := hω M
    rwa [min_eq_left h1, min_eq_left h2] at hEq
  -- By ergodicity of (P0, S), Z is P0-a.e. constant
  have herg := ergodic_palmShift Q
  have hZ_const : ∃ c : ℝ, ∀ᵐ ω ∂PS.P0, Z ω = c := by
    -- For every q : ℚ, P0 {Z ≤ q} ∈ {0, 1}
    have h01 : ∀ q : ℚ, PS.P0 {ω | Z ω ≤ (q : ℝ)} = 0 ∨ PS.P0 {ω | Z ω ≤ (q : ℝ)} = 1 := by
      intro q
      let B : Set Ω := {ω | Z ω ≤ (q : ℝ)}
      have hB_meas : MeasurableSet B := measurableSet_le hZ_meas measurable_const
      -- Build strictly S-invariant measurable set B' =ᵐ B: B' = {ω | ∀ᶠ k, S^[k] ω ∈ B}?
      -- Simpler: use Ergodic.ae_empty_or_univ_of_ae_le_preimage or build B_inv
      have hB_ae : (palmShift PS ⁻¹' B : Set Ω) =ᵐ[PS.P0] B := by
        filter_upwards [hZ_eq_S] with ω hω
        change (Z (palmShift PS ω) ≤ (q : ℝ)) = (Z ω ≤ (q : ℝ))
        rw [hω]
      rcases herg.ae_empty_or_univ_of_ae_le_preimage hB_meas.nullMeasurableSet hB_ae.symm.le with h0 | h1
      · left; exact ae_eq_empty.mp h0
      · right
        have hcompl : PS.P0 Bᶜ = 0 := ae_eq_univ.mp h1
        exact (prob_compl_eq_zero_iff hB_meas).mp hcompl
    let c : ℝ := sInf {x : ℝ | ∃ q : ℚ, (q : ℝ) = x ∧ PS.P0 {ω | Z ω ≤ (q : ℝ)} = 1}
    have hS_ne : {x : ℝ | ∃ q : ℚ, (q : ℝ) = x ∧ PS.P0 {ω | Z ω ≤ (q : ℝ)} = 1}.Nonempty := by
      -- Since ⋃ n : ℕ, {Z ≤ n} = univ, some n has P0 {Z ≤ n} > 0, hence = 1
      have hU : (⋃ n : ℕ, {ω | Z ω ≤ (n : ℝ)}) = Set.univ := by
        ext ω; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
        exact exists_nat_ge (Z ω)
      have hsup : (⨆ n : ℕ, PS.P0 {ω | Z ω ≤ (n : ℝ)}) = 1 := by
        have hmono : Monotone (fun n : ℕ => {ω | Z ω ≤ (n : ℝ)}) :=
          fun a b hab ω hω => show Z ω ≤ (b : ℝ) from le_trans hω (Nat.cast_le.mpr hab)
        rw [← hmono.measure_iUnion, hU, measure_univ]
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      have hall0 : ∀ n : ℕ, PS.P0 {ω | Z ω ≤ (n : ℝ)} = 0 := by
        intro n
        rcases h01 (n : ℚ) with h0 | h1
        · simpa using h0
        · exfalso
          have : ((n : ℚ) : ℝ) ∈ {x : ℝ | ∃ q : ℚ, (q : ℝ) = x ∧ PS.P0 {ω | Z ω ≤ (q : ℝ)} = 1} :=
            ⟨n, rfl, h1⟩
          rw [hempty] at this; exact this
      simp [hall0] at hsup
    have hS_bdd : BddBelow {x : ℝ | ∃ q : ℚ, (q : ℝ) = x ∧ PS.P0 {ω | Z ω ≤ (q : ℝ)} = 1} := by
      refine ⟨0, ?_⟩
      rintro x ⟨q, rfl, h1⟩
      by_contra hlt
      push Not at hlt
      have hempty : {ω | Z ω ≤ (q : ℝ)} = ∅ := by
        ext ω; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
        exact lt_of_lt_of_le hlt (hZ_nn ω)
      rw [hempty, measure_empty] at h1
      exact zero_ne_one h1
    refine ⟨c, ?_⟩
    have hle_c : ∀ᵐ ω ∂PS.P0, Z ω ≤ c := by
      have hall : ∀ n : ℕ, ∀ᵐ ω ∂PS.P0, Z ω ≤ c + 1 / ((n : ℝ) + 1) := by
        intro n
        have hlt : c < c + 1 / ((n : ℝ) + 1) := by linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity]
        obtain ⟨x, ⟨q, rfl, hq1⟩, hxq⟩ := exists_lt_of_csInf_lt hS_ne hlt
        have haeq : ∀ᵐ ω ∂PS.P0, Z ω ≤ (q : ℝ) := by
          rw [ae_iff]
          have : {ω | ¬ Z ω ≤ (q : ℝ)} = {ω | Z ω ≤ (q : ℝ)}ᶜ := rfl
          rw [this, prob_compl_eq_zero_iff (measurableSet_le hZ_meas measurable_const)]
          exact hq1
        filter_upwards [haeq] with ω hω
        linarith
      filter_upwards [ae_all_iff.mpr hall] with ω hω
      exact le_of_forall_pos_le_add fun ε hε => by
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
        exact le_trans (hω n) (by linarith)
    have hge_c : ∀ᵐ ω ∂PS.P0, c ≤ Z ω := by
      have hall : ∀ n : ℕ, ∀ᵐ ω ∂PS.P0, c - 1 / ((n : ℝ) + 1) ≤ Z ω := by
        intro n
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show c - 1 / ((n : ℝ) + 1) < c by
          linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity])
        have hq0 : PS.P0 {ω | Z ω ≤ (q : ℝ)} = 0 := by
          rcases h01 q with h0 | h1
          · exact h0
          · exfalso
            have : c ≤ (q : ℝ) := csInf_le hS_bdd ⟨q, rfl, h1⟩
            linarith
        have haeq : ∀ᵐ ω ∂PS.P0, (q : ℝ) < Z ω := by
          rw [ae_iff]; simpa only [not_lt] using hq0
        filter_upwards [haeq] with ω hω
        linarith
      filter_upwards [ae_all_iff.mpr hall] with ω hω
      by_contra hlt
      push Not at hlt
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
      linarith [hω n]
    filter_upwards [hle_c, hge_c] with ω h1 h2
    exact le_antisymm h1 h2
  obtain ⟨c, hc⟩ := hZ_const
  -- Show c = 0
  have hc0 : c = 0 := by
    have hc_nn : 0 ≤ c := by
      obtain ⟨ω, hω⟩ := hc.exists
      rw [← hω]; exact hZ_nn ω
    by_contra hne
    have hc_pos : 0 < c := lt_of_le_of_ne hc_nn (Ne.symm hne)
    have hc_S : ∀ᵐ ω ∂PS.P0, Z (palmShift PS ω) = c := by
      filter_upwards [hZ_eq_S, hc] with ω h1 h2; rw [h1, h2]
    -- On G ∩ zeroSet, max (loynesWl 0 ω + c + σ₀ - τ₀) 0 - max (loynesWl 0 ω + σ₀ - τ₀) 0 = c
    -- forces loynesWl 0 ω + σ₀ - τ₀ ≥ 0
    have hdiff_ae : (fun ω => loynesWl Q 0 ω - loynesWl Q 0 (palmShift PS ω)) =ᵐ[PS.P0]
        (fun ω => Q.tau 0 ω - Q.sigma 0 ω) := by
      filter_upwards [haeG_P0, ae_P0_zeroSet PS, hc, hc_S] with ω hωG h0 hZω hZSω
      have ⟨hpath', hgood'⟩ := hG_sub hωG
      have hpath := isWorkloadPath_loynes_of_mem_goodSet Q hgood'
      have hSωG : palmShift PS ω ∈ G := by
        rw [palmShift_apply_of_zero PS h0]
        exact (Set.ext_iff.mp (hG_inv (PS.N.T 1 ω)) ω).mpr hωG
      have h1 : Wl'c 0 ω - loynesWl Q 0 ω = c := by
        rw [← hZω]; exact (max_eq_left (sub_nonneg.mpr (hWl_ge_G hωG 0))).symm
      have h2 : Wl'c (PS.N.T 1 ω) ω - loynesWl Q (PS.N.T 1 ω) ω = c := by
        rw [← hZSω]
        dsimp [Z]
        rw [max_eq_left (sub_nonneg.mpr (hWl_ge_G hSωG 0)), palmShift_apply_of_zero PS h0,
            hWl'c_comp, isCompatible_loynesWl Q, zero_add]
      have hs1 := workloadPath_lindley_step Q hpath' 0
      have hs2 := workloadPath_lindley_step Q hpath 0
      have h0' : Q.toPalmSetting.N.T 0 ω = 0 := h0
      simp only [zero_add, h0'] at hs1 hs2
      rw [hs1, hs2] at h2
      have hWl'0 : Wl'c 0 ω = loynesWl Q 0 ω + c := by linarith
      rw [hWl'0] at h2
      have hnn_step : 0 ≤ loynesWl Q 0 ω + Q.sigma 0 ω - Q.tau 0 ω := by
        by_contra hneg
        push Not at hneg
        rw [max_eq_right hneg.le, sub_zero] at h2
        have hlt_c : max (loynesWl Q 0 ω + c + Q.sigma 0 ω - Q.tau 0 ω) 0 < c :=
          max_lt (by linarith) hc_pos
        linarith
      have hS : loynesWl Q 0 (palmShift PS ω) = loynesWl Q (PS.N.T 1 ω) ω := by
        rw [palmShift_apply_of_zero PS h0, isCompatible_loynesWl Q, zero_add]
      rw [hS, hs2, max_eq_left hnn_step]
      ring
    have hint_rhs : Integrable (fun ω => Q.tau 0 ω - Q.sigma 0 ω) PS.P0 :=
      (integrable_tau_zero Q).sub hsigInt
    have hint_lhs : Integrable (fun ω => loynesWl Q 0 ω - loynesWl Q 0 (palmShift PS ω)) PS.P0 :=
      hint_rhs.congr hdiff_ae.symm
    have hzero_int : ∫ ω, (loynesWl Q 0 ω - loynesWl Q 0 (palmShift PS ω)) ∂PS.P0 = 0 :=
      ergodic_lemma PS.P0 (palmShift PS) (palmShift PS).measurable hmp.map_eq
        (loynesWl Q 0) (measurable_loynesWl Q 0) (loynesWl_nonneg Q 0) hint_lhs
    rw [integral_congr_ae hdiff_ae, integral_sub (integrable_tau_zero Q) hsigInt,
        integral_tau_zero Q] at hzero_int
    have heq : ∫ ω, Q.sigma 0 ω ∂PS.P0 = PS.lam⁻¹ := by linarith
    rw [heq, mul_inv_cancel₀ PS.intensity.1.ne'] at hrho_lt
    exact lt_irrefl 1 hrho_lt
  -- Therefore P0-a.e. Wl'c 0 ω = loynesWl Q 0 ω
  have hP0_eq : ∀ᵐ ω ∂PS.P0, Wl'c 0 ω = loynesWl Q 0 ω := by
    filter_upwards [haeG_P0, hc] with ω hωG hZω
    rw [hc0] at hZω
    dsimp [Z] at hZω
    have hge := hWl_ge_G hωG 0
    rw [max_eq_left (sub_nonneg.mpr hge)] at hZω
    linarith
  have hP_all_eq := ae_P_all_shifts_of_ae_P0 Q hP0_eq
  filter_upwards [haeG_P, hP_all_eq] with ω hωG hall t
  have ⟨hpath', hgood'⟩ := hG_sub hωG
  have hpath := isWorkloadPath_loynes_of_mem_goodSet Q hgood'
  let k := idx PS.N t ω
  have hk := idx_spec PS.N t ω
  rw [hpath'.2.2 k t ⟨hk.1, hk.2⟩, hpath.2.2 k t ⟨hk.1, hk.2⟩]
  have hk_eq := hall k
  rw [hWl'c_comp, isCompatible_loynesWl Q, zero_add] at hk_eq
  rw [hk_eq]

end LoynesRootProof

theorem solution {Ω : Type*} [MeasurableSpace Ω] (Q : Queue Ω) :
    (Q.trafficIntensity < 1 →
      ∃ W Wl : ℝ → Ω → ℝ,
        (∀ t : ℝ, Measurable (W t)) ∧ IsCompatible Q.toPalmSetting.θ W ∧
        (∀ᵐ ω ∂Q.toPalmSetting.P, IsWorkloadPath Q W Wl ω) ∧
        (∀ W' Wl' : ℝ → Ω → ℝ, (∀ t : ℝ, Measurable (W' t)) →
          IsCompatible Q.toPalmSetting.θ W' →
          (∀ᵐ ω ∂Q.toPalmSetting.P, IsWorkloadPath Q W' Wl' ω) →
          ∀ᵐ ω ∂Q.toPalmSetting.P, ∀ t : ℝ, W' t ω = W t ω) ∧
        (∀ᵐ ω ∂Q.toPalmSetting.P, BddAbove (loynesSet Q ω) ∧ W 0 ω = sSup (loynesSet Q ω)) ∧
        (∀ᵐ ω ∂Q.toPalmSetting.P,
          {n : ℤ | n < 0 ∧ Wl (Q.toPalmSetting.N.T n ω) ω = 0}.Infinite ∧
          {n : ℤ | 0 < n ∧ Wl (Q.toPalmSetting.N.T n ω) ω = 0}.Infinite)) ∧
    (1 < Q.trafficIntensity →
      ¬ ∃ W Wl : ℝ → Ω → ℝ, IsCompatible Q.toPalmSetting.θ W ∧
        ∀ᵐ ω ∂Q.toPalmSetting.P, IsWorkloadPath Q W Wl ω) := by
  refine ⟨fun hρ => ?_, LoynesRootProof.no_workload_of_one_lt_trafficIntensity Q⟩
  refine ⟨LoynesRootProof.loynesW Q, LoynesRootProof.loynesWl Q,
    LoynesRootProof.measurable_loynesW Q,
    LoynesRootProof.isCompatible_loynesW Q, ?_, ?_, ?_, ?_⟩
  · filter_upwards [LoynesRootProof.tendsto_atBot_of_trafficIntensity_lt_one Q hρ] with ω hω
    exact LoynesRootProof.isWorkloadPath_loynes_of_mem_goodSet Q hω
  · intro W' Wl' hW'meas hW'comp hW'path
    exact LoynesRootProof.loynes_uniqueness Q hρ W' Wl' hW'meas hW'comp hW'path
  · filter_upwards [LoynesRootProof.tendsto_atBot_of_trafficIntensity_lt_one Q hρ] with ω hω
    refine ⟨LoynesRootProof.bddAbove_loynesSet_of_goodSet Q hω, ?_⟩
    unfold LoynesRootProof.loynesW LoynesRootProof.loynesW0
    rw [LoynesRootProof.flow_zero_apply]
  · exact LoynesRootProof.infinitely_many_empty_times Q hρ

