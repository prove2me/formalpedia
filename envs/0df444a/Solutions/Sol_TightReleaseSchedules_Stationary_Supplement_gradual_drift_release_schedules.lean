-- Prove2me | solution 1 for TightReleaseSchedules.Stationary.Supplement.gradual_drift_release_schedules
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T18:33:14.930783+00:00
-- url     : https://prove2.me/submissions/adfdbbda-3a4e-43c7-aba4-1e33b4e55a6d

import Definitions.Def_TightReleaseSchedules_Stationary_Supplement_drift_class
import Theorems.Thm_TightReleaseSchedules_Stationary_anchored_cross_moments
import Theorems.Thm_TightReleaseSchedules_Stationary_common_lower_error_event
import Theorems.Thm_TightReleaseSchedules_Stationary_Supplement_tracking_floor

section
/-!
# q382 gradual_drift_release_schedules -- plan with explicit constants (written BEFORE the Lean)

Truth check (done by hand, no counterexample): with y = (d/eta^2)^(1/3) >= 4 (d*eta <= 1/8), p = (d eta)^(2/3) = eta^2 y^2,
w0 = ceil y <= 2y, phi = min(p, eta^2 T^2), and a release at date n (1 <= n < T), window w = min(n, w0):
* targets of the window: ||theta_i - theta0|| <= Delta + eta*i <= Delta + eta*n =: R  (<= 3/4 <= 1), so the projection ball contains
  the window path average; Lemma 3.3 (anchored_cross_moments, clause 2): E||Pi Z - bar||^2 <= min((2d+1)/w, 4R^2) <= min(3d/w, 4R^2).
* bias ||bar - theta_{n-1}|| <= eta (w-1)/2 <= eta w/2, staleness ||theta_{n-1} - theta_i|| <= eta (i-n+1) <= eta L (L = phase length).
* squared triangle: half-error <= (3/2)(min(3d/w,4R^2) + eta^2 w^2/4 + eta^2 L^2).
* NUMERIC LEMMA: min(3d/w,4R^2) + eta^2 w^2/4 <= 8 d/x + 33 phi, x = max(n, d/Delta^2) [case w=n: min(3d/n,4(D+en)^2) <= 8min(d/n,D^2)+8e^2n^2,
  e^2 n^2 <= 4 phi => 8.25*4 = 33; case n > w0: <= 4p = 4 phi].
* phase j with release date tau_j >= 1 (< T): per-round half error <= 12 d/x_j + 49.5 phi + 1.5 eta^2 L_j^2; summed over the L_j rounds:
  12 L_j d/x_j + 49.5 L_j phi + 1.5 eta^2 L_j^3.  Phase with date 0 (theta0 served): half error <= Delta^2 + eta^2 L^2 = d/x_j + eta^2 L^2.
  Sum_j L_j = T gives risk(tau) <= 12 F(tau) + 49.5 T phi <= 12 F*_B + 50 T phi for F-minimizing tau (a),(b); (a) via a minimizer (finite set).
* LOWER BOUND (c): d >= 2. S = coordinates != 0, d_h = d-1. Path g_i = theta0 + eta i e0 + (Delta/2) e1, theta = g + H.  Lemma 4.2
  (common_lower_error_event) with L = max(firstLevel, ceil log2 T): #levels N <= log2 T, event E with Pr >= 1 - B N (9/25)^(d-1) >= 1/2.
  On E every release at tau_j < T has ||P_S head - g_S - H||^2 >= 2^-19 d_h/max(tau_j,16 d_h/Delta^2) >= 2^-24 d/x_j; theta0: >= Delta^2/8 >= 2^-24 Delta^2.
  Coordinate 0 on a phase: sum (c - eta t)^2 >= eta^2 L(L^2-1)/12.  Realized-schedule loss >= 2^-25 F(tau~) - eta^2 T/24 >= 2^-25 F* - T phi/24
  (eta^2 <= phi).  Averaging over the prior: worstRisk >= 2^-26 F* - T phi/48; tracking_floor (Delta=0 class subset of Delta class): >= 2^-13 T phi.
  Convex combination weights 2^-9, 1-2^-9: >= 2^-35 F* + 2^-14 T phi >= 2^-35 (F* + T phi).
-/

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement

noncomputable section

namespace TRS.Dev.DriftBase

instance gaussianRows_prob (T d : ℕ) : IsProbabilityMeasure (gaussianRows T d) := by
  unfold gaussianRows; infer_instance


lemma proj_spec {d : ℕ} (K : Set (Vector d)) (hne : K.Nonempty) (hc : IsClosed K)
    (hv : Convex ℝ K) (x : Vector d) :
    convexProjection K x ∈ K ∧
      ∀ w ∈ K, inner ℝ (x - convexProjection K x) (w - convexProjection K x) ≤ 0 := by
  have hh : K.Nonempty ∧ IsClosed K ∧ Convex ℝ K := ⟨hne, hc, hv⟩
  have hdef : convexProjection K x =
      Classical.choose (exists_norm_eq_iInf_of_complete_convex hh.1 hh.2.1.isComplete hh.2.2 x) := by
    unfold convexProjection
    rw [dif_pos hh]
  obtain ⟨hmem, heq⟩ :=
    Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hh.1 hh.2.1.isComplete hh.2.2 x)
  rw [hdef]
  refine ⟨hmem, ?_⟩
  exact (norm_eq_iInf_iff_real_inner_le_zero hv hmem).1 heq

lemma proj_lipschitz {d : ℕ} (K : Set (Vector d)) (hne : K.Nonempty) (hc : IsClosed K)
    (hv : Convex ℝ K) : LipschitzWith 1 (convexProjection K) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  obtain ⟨hp, hpi⟩ := proj_spec K hne hc hv x
  obtain ⟨hq, hqi⟩ := proj_spec K hne hc hv y
  set p := convexProjection K x
  set q := convexProjection K y
  have h1 := hpi q hq
  have h2 := hqi p hp
  have h3 : ‖p - q‖ ^ 2 ≤ inner ℝ (x - y) (p - q) := by
    have e1 : inner ℝ (x - p) (q - p) = -inner ℝ (x - p) (p - q) := by
      rw [← inner_neg_right, neg_sub]
    have e2 : inner ℝ (x - p - (y - q)) (p - q) =
        inner ℝ (x - p) (p - q) - inner ℝ (y - q) (p - q) := inner_sub_left _ _ _
    have e3 : inner ℝ (x - y) (p - q) = inner ℝ (x - p - (y - q)) (p - q) +
        inner ℝ (p - q) (p - q) := by
      rw [← inner_add_left]; congr 1; abel
    rw [real_inner_self_eq_norm_sq] at e3
    linarith
  have h4 : inner ℝ (x - y) (p - q) ≤ ‖x - y‖ * ‖p - q‖ := real_inner_le_norm _ _
  rw [dist_eq_norm, dist_eq_norm]
  simp only [NNReal.coe_one, one_mul]
  by_cases h0 : ‖p - q‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖p - q‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

lemma proj_ball_measurable {d : ℕ} (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    Measurable (convexProjection (Metric.closedBall (0 : Vector d) Δ)) :=
  (proj_lipschitz _ ⟨0, Metric.mem_closedBall_self hΔ⟩ Metric.isClosed_closedBall
    (convex_closedBall _ _)).continuous.measurable
lemma anchoredAverage_continuous {T d : ℕ} (θ₀ : Vector d) (I : Finset (Fin T)) :
    Continuous (fun h : Data T d => anchoredAverage θ₀ I h) := by
  unfold anchoredAverage crossMoment
  have hs : Continuous (fun h : Data T d => ∑ i ∈ I,
      ((h i).2 - inner ℝ (h i).1 θ₀) • (h i).1) := by
    apply continuous_finset_sum
    intro i _
    have h1 : Continuous (fun h : Data T d => (h i).1) := (continuous_apply i).fst
    have h2 : Continuous (fun h : Data T d => (h i).2) := (continuous_apply i).snd
    exact (h2.sub (Continuous.inner h1 continuous_const)).smul h1
  exact hs.const_smul (I.card : ℝ)⁻¹

lemma obs_continuous {T d : ℕ} (θ : Fin T → Vector d) :
    Continuous (fun z : GaussianRows T d => observations θ z) := by
  unfold observations
  apply continuous_pi
  intro i
  have h1 : Continuous (fun z : GaussianRows T d => (z i).1) := (continuous_apply i).fst
  have h2 : Continuous (fun z : GaussianRows T d => (z i).2) := (continuous_apply i).snd
  exact h1.prodMk ((Continuous.inner h1 continuous_const).add h2)


lemma foldl_spec {α β : Type*} (c : β → Prop) [DecidablePred c] (h : β → α) (w : α) (l : List β) :
    (List.foldl (fun r j => if c j then h j else r) w l = w ∧ ∀ k ∈ l, ¬ c k) ∨
    ∃ j, c j ∧ List.foldl (fun r j => if c j then h j else r) w l = h j ∧
      ∃ l₁ l₂, l = l₁ ++ j :: l₂ ∧ ∀ k ∈ l₂, ¬ c k := by
  induction l generalizing w with
  | nil => left; simp
  | cons a l ih =>
    simp only [List.foldl_cons]
    rcases ih (if c a then h a else w) with ⟨h1, h2⟩ | ⟨j, hj, hr, l₁, l₂, hl, hl₂⟩
    · by_cases ha : c a
      · right
        refine ⟨a, ha, ?_, [], l, rfl, h2⟩
        rw [h1]; simp [ha]
      · left
        refine ⟨?_, ?_⟩
        · rw [h1]; simp [ha]
        · intro k hk
          rcases List.mem_cons.1 hk with rfl | hk
          · exact ha
          · exact h2 k hk
    · right
      exact ⟨j, hj, hr, a :: l₁, l₂, by simp [hl], hl₂⟩

/-- The deployed predictor is `θ₀` or the head of the last slot with date `≤ i`. -/
lemma deployed_spec {s : RandomSeed} {T d B : ℕ} (θ₀ : Vector d) (π : ReleasePolicy s T d B)
    (ω : Transcript s T d) (i : Fin T) :
    (deployed θ₀ π ω i = θ₀ ∧ ∀ j : Fin B, i.val < π.date j ω) ∨
    ∃ j : Fin B, π.date j ω ≤ i.val ∧ deployed θ₀ π ω i = π.head j ω ∧
      ∀ k : Fin B, j < k → i.val < π.date k ω := by
  unfold deployed
  rcases foldl_spec (fun j : Fin B => π.date j ω ≤ i.val) (fun j => π.head j ω) θ₀
    (List.finRange B) with ⟨h1, h2⟩ | ⟨j, hj, hr, l₁, l₂, hl, hl₂⟩
  · left
    refine ⟨h1, fun j => ?_⟩
    have := h2 j (List.mem_finRange j)
    omega
  · right
    refine ⟨j, hj, hr, fun k hk => ?_⟩
    have hp := List.pairwise_lt_finRange B
    rw [hl] at hp
    have hkmem : k ∈ l₁ ++ j :: l₂ := hl ▸ List.mem_finRange k
    rcases List.mem_append.1 hkmem with hk1 | hk2
    · have := (List.pairwise_append.1 hp).2.2 k hk1 j (List.mem_cons_self)
      exact absurd (lt_trans this hk) (lt_irrefl _)
    · rcases List.mem_cons.1 hk2 with rfl | hk3
      · exact absurd hk (lt_irrefl _)
      · have := hl₂ k hk3
        omega


lemma sum_Ico_phases' {M : Type*} [AddCommMonoid M] (t : ℕ → ℕ) (ht : Monotone t) (f : ℕ → M)
    (n : ℕ) :
    ∑ i ∈ Finset.Ico (t 0) (t n), f i =
      ∑ j ∈ Finset.range n, ∑ i ∈ Finset.Ico (t j) (t (j + 1)), f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact (Finset.sum_Ico_consecutive f (ht (Nat.zero_le n)) (ht (Nat.le_succ n))).symm

def tt (T B : ℕ) (τ : Fin (B + 2) → ℕ) (m : ℕ) : ℕ := if hm : m < B + 2 then τ ⟨m, hm⟩ else T

lemma tt_mono (T B : ℕ) (τ : Fin (B + 2) → ℕ) (hτ : IsSchedule T B τ) : Monotone (tt T B τ) := by
  obtain ⟨h0, hlast, hmono⟩ := hτ
  intro a b hab
  simp only [tt]
  by_cases hb : b < B + 2
  · have ha : a < B + 2 := lt_of_le_of_lt hab hb
    simp only [ha, hb, dif_pos]
    exact hmono (by simpa using hab)
  · by_cases ha : a < B + 2
    · simp only [ha, hb, dif_pos, dif_neg, not_false_eq_true]
      rw [← hlast]
      exact hmono (by simp [Fin.le_def]; omega)
    · simp [ha, hb]

lemma tt_zero (T B : ℕ) (τ : Fin (B + 2) → ℕ) (hτ : IsSchedule T B τ) : tt T B τ 0 = 0 := by
  simp [tt, hτ.1]

lemma tt_last (T B : ℕ) (τ : Fin (B + 2) → ℕ) (hτ : IsSchedule T B τ) :
    tt T B τ (B + 1) = T := by
  simp only [tt]
  rw [dif_pos (by omega)]
  exact hτ.2.1

lemma tt_cast (T B : ℕ) (τ : Fin (B + 2) → ℕ) (j : Fin (B + 1)) :
    tt T B τ j.val = τ j.castSucc := by
  simp only [tt]; rw [dif_pos (by omega)]; rfl

lemma tt_succ (T B : ℕ) (τ : Fin (B + 2) → ℕ) (j : Fin (B + 1)) :
    tt T B τ (j.val + 1) = τ j.succ := by
  simp only [tt]; rw [dif_pos (by omega)]; rfl

lemma exists_phase (T B : ℕ) (τ : Fin (B + 2) → ℕ) (hτ : IsSchedule T B τ) (i : ℕ) (hi : i < T) :
    ∃ j : Fin (B + 1), τ j.castSucc ≤ i ∧ i < τ j.succ := by
  classical
  have hex : ∃ m, i < tt T B τ m := ⟨B + 1, by rw [tt_last T B τ hτ]; exact hi⟩
  set m := Nat.find hex with hm
  have hm1 : i < tt T B τ m := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, tt_zero T B τ hτ] at hm1
    omega
  have hmB : m ≤ B + 1 := Nat.find_min' hex (by rw [tt_last T B τ hτ]; exact hi)
  have hprev : ¬ i < tt T B τ (m - 1) := Nat.find_min hex (by omega)
  refine ⟨⟨m - 1, by omega⟩, ?_, ?_⟩
  · have := tt_cast T B τ ⟨m - 1, by omega⟩
    simp only at this
    rw [← this]; omega
  · have := tt_succ T B τ ⟨m - 1, by omega⟩
    simp only at this
    rw [← this]
    have e : m - 1 + 1 = m := by omega
    rw [e]; exact hm1

lemma schedule_finite (T B : ℕ) : {τ : Fin (B + 2) → ℕ | IsSchedule T B τ}.Finite := by
  refine Set.Finite.subset (Set.Finite.pi (t := fun _ : Fin (B + 2) => Set.Iic T)
    (fun _ => Set.finite_Iic T)) ?_
  intro τ hτ m _
  show τ m ≤ T
  rw [← hτ.2.1]
  exact hτ.2.2 (by simp [Fin.le_def]; omega)

lemma schedule_nonempty (T B : ℕ) : {τ : Fin (B + 2) → ℕ | IsSchedule T B τ}.Nonempty := by
  refine ⟨fun m => if m = 0 then 0 else T, ?_, ?_, ?_⟩
  · simp
  · have : Fin.last (B + 1) ≠ 0 := by simp [Fin.ext_iff]
    simp [this]
  · intro a b hab
    by_cases ha : a = 0
    · simp [ha]
    · have hb : b ≠ 0 := by
        intro hb; subst hb
        exact ha (le_antisymm hab (Fin.zero_le _))
      simp [ha, hb]

/-- The realized schedule of a policy on a transcript. -/
def sched {s : RandomSeed} {T d B : ℕ} (π : ReleasePolicy s T d B) (ω : Transcript s T d) :
    Fin (B + 2) → ℕ :=
  fun m => if m.val = 0 then 0 else if h : m.val - 1 < B then π.date ⟨m.val - 1, h⟩ ω else T

lemma sched_slot {s : RandomSeed} {T d B : ℕ} (π : ReleasePolicy s T d B)
    (ω : Transcript s T d) (j : Fin B) : sched π ω j.succ.castSucc = π.date j ω := by
  unfold sched
  have h1 : (j.succ.castSucc : Fin (B + 2)).val = j.val + 1 := by simp
  simp only [h1]
  rw [if_neg (by omega), dif_pos (by omega)]
  rfl

lemma sched_isSchedule {s : RandomSeed} {T d B : ℕ} (π : ReleasePolicy s T d B) (hπ : IsCausal π)
    (ω : Transcript s T d) : IsSchedule T B (sched π ω) := by
  obtain ⟨h1, h2, -, -⟩ := hπ
  refine ⟨?_, ?_, ?_⟩
  · simp [sched]
  · simp only [sched, Fin.val_last]
    rw [if_neg (by omega), dif_neg (by omega)]
  · intro a b hab
    have hab' : a.val ≤ b.val := hab
    unfold sched
    by_cases ha : a.val = 0
    · simp [ha]
    · have hb : b.val ≠ 0 := by omega
      simp only [ha, hb, if_false]
      by_cases hb1 : b.val - 1 < B
      · have ha1 : a.val - 1 < B := by omega
        rw [dif_pos hb1, dif_pos ha1]
        exact h2 ω (by simp [Fin.le_def]; omega)
      · rw [dif_neg hb1]
        by_cases ha1 : a.val - 1 < B
        · rw [dif_pos ha1]; exact h1 _ _
        · rw [dif_neg ha1]

lemma deployed_phase_gen {s : RandomSeed} {T d B : ℕ} (θ₀ : Vector d) (π : ReleasePolicy s T d B)
    (ω : Transcript s T d) (τ : Fin (B + 2) → ℕ) (hτ0 : τ 0 = 0) (hmono : Monotone τ)
    (hdate : ∀ k : Fin B, π.date k ω = τ k.succ.castSucc) (j : Fin (B + 1)) (i : Fin T)
    (h1 : τ j.castSucc ≤ i.val) (h2 : i.val < τ j.succ) :
    (j.val = 0 ∧ deployed θ₀ π ω i = θ₀) ∨
    (∃ k : Fin B, k.val + 1 = j.val ∧ deployed θ₀ π ω i = π.head k ω ∧
      π.date k ω = τ j.castSucc) := by
  rcases deployed_spec θ₀ π ω i with ⟨h, hall⟩ | ⟨k, hk, hdep, hlater⟩
  · left
    refine ⟨?_, h⟩
    by_contra hj
    let k : Fin B := ⟨j.val - 1, by omega⟩
    have := hall k
    rw [hdate] at this
    have e : τ k.succ.castSucc = τ j.castSucc := by
      congr 1; ext; simp [k]; omega
    rw [e] at this
    omega
  · right
    refine ⟨k, ?_, hdep, ?_⟩
    · rw [hdate] at hk
      have hlt : k.succ.castSucc < j.succ := by
        refine hmono.reflect_lt ?_
        omega
      have hkj : k.val + 1 < j.val + 1 := by simpa [Fin.lt_def] using hlt
      by_contra hne
      have hlt2 : k.val + 1 < j.val := by omega
      let k' : Fin B := ⟨k.val + 1, by omega⟩
      have hk' : k < k' := by simp [Fin.lt_def, k']
      have h3 := hlater k' hk'
      rw [hdate] at h3
      have : τ k'.succ.castSucc ≤ τ j.castSucc := by
        exact hmono (by simp [Fin.le_def, k']; omega)
      omega
    · rw [hdate]
      have hkj : k.val + 1 = j.val := by
        rw [hdate] at hk
        have hlt : k.succ.castSucc < j.succ := by
          refine hmono.reflect_lt ?_
          omega
        have hkj : k.val + 1 < j.val + 1 := by simpa [Fin.lt_def] using hlt
        by_contra hne
        have hlt2 : k.val + 1 < j.val := by omega
        let k' : Fin B := ⟨k.val + 1, by omega⟩
        have hk' : k < k' := by simp [Fin.lt_def, k']
        have h3 := hlater k' hk'
        rw [hdate] at h3
        have : τ k'.succ.castSucc ≤ τ j.castSucc := by
          exact hmono (by simp [Fin.le_def, k']; omega)
        omega
      congr 1; ext; simp; omega


end TRS.Dev.DriftBase
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement

noncomputable section

namespace TRS.Dev.DriftNum

lemma windowLength_pos (d : ℕ) (hd : 0 < d) (η : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ windowLength d η n := by
  unfold windowLength
  split_ifs with h
  · exact hn
  · refine le_min hn ?_
    apply Nat.one_le_iff_ne_zero.2
    intro h0
    have := Nat.ceil_eq_zero.1 h0
    have hpos : 0 < ((d : ℝ) / η ^ 2) ^ (1 / 3 : ℝ) := by
      apply Real.rpow_pos_of_pos
      have : 0 < η ^ 2 := by positivity
      have : (0 : ℝ) < d := by exact_mod_cast hd
      positivity
    linarith

lemma windowLength_le (d : ℕ) (η : ℝ) (n : ℕ) : windowLength d η n ≤ n := by
  unfold windowLength
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

/-- `d / max(n, d/Δ²) = min (d/n) Δ²`. -/
lemma div_clamp (d : ℝ) (hd : 0 ≤ d) (Δ : ℝ) (hΔ : 0 < Δ) (n : ℝ) (hn : 0 < n) :
    d / max n (d / Δ ^ 2) = min (d / n) (Δ ^ 2) := by
  have hΔ2 : 0 < Δ ^ 2 := by positivity
  rcases le_total n (d / Δ ^ 2) with h | h
  · rw [max_eq_right h]
    have : Δ ^ 2 ≤ d / n := by
      rw [le_div_iff₀ hn]
      rw [le_div_iff₀ hΔ2] at h
      linarith
    rw [min_eq_right this]
    rcases hd.eq_or_lt with h0 | h0
    · exfalso
      rw [← h0] at h
      simp at h
      linarith
    · field_simp
  · rw [max_eq_left h]
    have : d / n ≤ Δ ^ 2 := by
      rw [div_le_iff₀ hn]
      rw [div_le_iff₀ hΔ2] at h
      linarith
    rw [min_eq_left this]

lemma sq_add_le (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]

/-- The core numeric inequality. -/
theorem numeric (T d : ℕ) (hd : 0 < d) (Δ η : ℝ) (hΔ : 0 < Δ) (hη : 0 ≤ η)
    (hdη : (d : ℝ) * η ≤ 1 / 8) (n : ℕ) (hn1 : 1 ≤ n) (hnT : n < T) :
    min (3 * (d : ℝ) / (windowLength d η n : ℝ)) (4 * (Δ + η * n) ^ 2) +
      η ^ 2 * (windowLength d η n : ℝ) ^ 2 / 4 ≤
    8 * ((d : ℝ) / max (n : ℝ) ((d : ℝ) / Δ ^ 2)) + 33 * trackingRate T d η := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hclamp := div_clamp d hdR.le Δ hΔ n hnR
  rw [hclamp]
  have hm0 : 0 ≤ min ((d : ℝ) / n) (Δ ^ 2) := le_min (by positivity) (by positivity)
  rcases hη.eq_or_lt with h0 | hpos
  · subst h0
    have hw : windowLength d 0 n = n := by simp [windowLength]
    rw [hw]
    have hφ : trackingRate T d 0 = 0 := by
      unfold trackingRate
      simp [Real.zero_rpow (show (2 / 3 : ℝ) ≠ 0 by norm_num)]
    rw [hφ]
    have : min (3 * (d : ℝ) / n) (4 * (Δ + 0 * n) ^ 2) ≤ 4 * min ((d : ℝ) / n) (Δ ^ 2) := by
      rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 4)]
      refine le_min ?_ ?_
      · calc _ ≤ 3 * (d : ℝ) / n := min_le_left _ _
          _ = 3 * ((d : ℝ) / n) := by ring
          _ ≤ 4 * ((d : ℝ) / n) := by nlinarith [div_nonneg hdR.le hnR.le]
          _ ≤ _ := by gcongr
      · calc _ ≤ 4 * (Δ + 0 * n) ^ 2 := min_le_right _ _
          _ = 4 * Δ ^ 2 := by ring
          _ ≤ _ := by gcongr
    linarith
  · -- η > 0
    set y : ℝ := ((d : ℝ) / η ^ 2) ^ (1 / 3 : ℝ) with hy
    have hηsq : 0 < η ^ 2 := by positivity
    have hdη2 : 0 < (d : ℝ) / η ^ 2 := by positivity
    have hy0 : 0 < y := Real.rpow_pos_of_pos hdη2 _
    have hy3 : y ^ 3 = (d : ℝ) / η ^ 2 := by
      rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hdη2.le]; norm_num
    have hy4 : 4 ≤ y := by
      by_contra hlt
      push Not at hlt
      have h1 : y ^ 3 < 4 ^ 3 := by gcongr
      have h2 : (64 : ℝ) ≤ (d : ℝ) / η ^ 2 := by
        rw [le_div_iff₀ hηsq]
        have h3 : (d : ℝ) * η ≤ 1 / 8 := hdη
        have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
        have : η ≤ 1 / 8 := by nlinarith
        nlinarith [mul_pos hpos hpos]
      rw [hy3] at h1
      norm_num at h1
      linarith
    set q : ℝ := η * y with hq
    have hq0 : 0 ≤ q := by positivity
    have hq3 : q ^ 3 = (d : ℝ) * η := by
      rw [hq, mul_pow, hy3]; field_simp
    set p : ℝ := ((d : ℝ) * η) ^ (2 / 3 : ℝ) with hp
    have hpq : p = q ^ 2 := by
      rw [hp, ← hq3, ← Real.rpow_natCast, ← Real.rpow_mul hq0]; norm_num
    have hηy : η ^ 2 * y ^ 2 = p := by rw [hpq, hq]; ring
    have hdy : (d : ℝ) / y = p := by
      have hd' : (d : ℝ) = η ^ 2 * y ^ 3 := by rw [hy3]; field_simp
      rw [hd', ← hηy]; field_simp
    have hw : windowLength d η n = min n ⌈y⌉₊ := by
      unfold windowLength; rw [if_neg hpos.ne']
    have hceil1 : y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil y
    have hceil2 : (⌈y⌉₊ : ℝ) ≤ 2 * y := by
      have := Nat.ceil_lt_add_one hy0.le
      linarith
    unfold trackingRate
    rw [← hp]
    set φ := min p (η ^ 2 * (T : ℝ) ^ 2) with hφ
    have hp0 : 0 ≤ p := by rw [hp]; positivity
    have hφ0 : 0 ≤ φ := le_min hp0 (by positivity)
    have hnT' : (n : ℝ) ≤ T := by exact_mod_cast hnT.le
    rcases le_total n ⌈y⌉₊ with hcase | hcase
    · have hwn : windowLength d η n = n := by rw [hw]; exact min_eq_left hcase
      rw [hwn]
      have hnR2 : (n : ℝ) ≤ 2 * y := le_trans (by exact_mod_cast hcase) hceil2
      have h1 : η ^ 2 * (n : ℝ) ^ 2 ≤ 4 * p := by
        have : (n : ℝ) ^ 2 ≤ (2 * y) ^ 2 := by gcongr
        nlinarith [hηy]
      have h2 : η ^ 2 * (n : ℝ) ^ 2 ≤ 4 * (η ^ 2 * (T : ℝ) ^ 2) := by
        have : (n : ℝ) ^ 2 ≤ (T : ℝ) ^ 2 := by gcongr
        nlinarith [hηsq]
      have hηn : η ^ 2 * (n : ℝ) ^ 2 ≤ 4 * φ := by
        rw [hφ, mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 4)]
        exact le_min h1 h2
      have key : min (3 * (d : ℝ) / n) (4 * (Δ + η * n) ^ 2) ≤
          8 * min ((d : ℝ) / n) (Δ ^ 2) + 8 * (η ^ 2 * (n : ℝ) ^ 2) := by
        by_cases hle : (d : ℝ) / n ≤ Δ ^ 2
        · rw [min_eq_left hle]
          have : 3 * (d : ℝ) / n = 3 * ((d : ℝ) / n) := by ring
          have h3 := min_le_left (3 * (d : ℝ) / n) (4 * (Δ + η * n) ^ 2)
          have : 0 ≤ η ^ 2 * (n : ℝ) ^ 2 := by positivity
          linarith [div_nonneg hdR.le hnR.le]
        · push Not at hle
          rw [min_eq_right hle.le]
          have h3 := min_le_right (3 * (d : ℝ) / n) (4 * (Δ + η * n) ^ 2)
          have h4 := sq_add_le Δ (η * n)
          have : (η * n) ^ 2 = η ^ 2 * (n : ℝ) ^ 2 := by ring
          linarith
      linarith
    · have hwn : windowLength d η n = ⌈y⌉₊ := by rw [hw]; exact min_eq_right hcase
      rw [hwn]
      have hw0 : 0 < (⌈y⌉₊ : ℝ) := lt_of_lt_of_le hy0 hceil1
      have h1 : 3 * (d : ℝ) / (⌈y⌉₊ : ℝ) ≤ 3 * p := by
        rw [mul_div_assoc, ← hdy]
        have : (d : ℝ) / (⌈y⌉₊ : ℝ) ≤ (d : ℝ) / y :=
          div_le_div_of_nonneg_left hdR.le hy0 hceil1
        linarith
      have h2 : η ^ 2 * (⌈y⌉₊ : ℝ) ^ 2 / 4 ≤ p := by
        have : (⌈y⌉₊ : ℝ) ^ 2 ≤ (2 * y) ^ 2 := by gcongr
        nlinarith [hηy, hηsq]
      have hyT : y ≤ T := by
        have : ⌈y⌉₊ ≤ T := le_trans hcase hnT.le
        exact le_trans hceil1 (by exact_mod_cast this)
      have hφp : φ = p := by
        rw [hφ]
        apply min_eq_left
        rw [← hηy]
        have : y ^ 2 ≤ (T : ℝ) ^ 2 := by gcongr
        nlinarith [hηsq]
      have h3 := min_le_left (3 * (d : ℝ) / (⌈y⌉₊ : ℝ)) (4 * (Δ + η * n) ^ 2)
      linarith

end TRS.Dev.DriftNum
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement
open TRS.Dev.DriftBase TRS.Dev.DriftNum

noncomputable section

namespace TRS.Dev.DriftWin

/-- The head released at date `n` by Algorithm 2. -/
def windowHead (T d : ℕ) (θ₀ : Vector d) (Δ η : ℝ) (n : ℕ) (h : Data T d) : Vector d :=
  if n = 0 ∨ T ≤ n then θ₀ else
    θ₀ + convexProjection (Metric.closedBall (0 : Vector d) (Δ + η * n))
      (anchoredAverage θ₀ (recentWindow T d η n) h)

lemma head_eq (T d B : ℕ) (θ₀ : Vector d) (Δ η : ℝ) (τ : Fin (B + 2) → ℕ) (j : Fin B)
    (ω : Transcript unitSeed T d) :
    (windowedPolicy T d B θ₀ Δ η τ).head j ω = windowHead T d θ₀ Δ η (slotDate τ j) ω.2 := rfl

lemma date_eq (T d B : ℕ) (θ₀ : Vector d) (Δ η : ℝ) (τ : Fin (B + 2) → ℕ) (j : Fin B)
    (ω : Transcript unitSeed T d) :
    (windowedPolicy T d B θ₀ Δ η τ).date j ω = slotDate τ j := rfl

lemma windowHead_measurable (T d : ℕ) (θ₀ : Vector d) (Δ η : ℝ) (hΔ : 0 ≤ Δ) (hη : 0 ≤ η)
    (n : ℕ) : Measurable (windowHead T d θ₀ Δ η n) := by
  unfold windowHead
  by_cases h : n = 0 ∨ T ≤ n
  · simp only [h, if_true]; exact measurable_const
  · simp only [h, if_false]
    have hR : 0 ≤ Δ + η * n := by positivity
    exact measurable_const.add ((proj_ball_measurable _ hR).comp
      (anchoredAverage_continuous θ₀ _).measurable)

lemma isCausal_window (T d B : ℕ) (θ₀ : Vector d) (Δ η : ℝ) (hΔ : 0 ≤ Δ) (hη : 0 ≤ η)
    (τ : Fin (B + 2) → ℕ) (hτ : IsSchedule T B τ) :
    IsCausal (windowedPolicy T d B θ₀ Δ η τ) := by
  have hmono : Monotone τ := hτ.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j ω
    rw [date_eq]
    unfold slotDate
    rw [← hτ.2.1]
    exact hmono (by simp [Fin.le_def])
  · intro ω a b hab
    simp only [date_eq]
    unfold slotDate
    have hab' : a.val ≤ b.val := hab
    exact hmono (by simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega)
  · intro j n
    show @MeasurableSet _ (information unitSeed T d n)
      {ω : Transcript unitSeed T d | slotDate τ j ≤ n}
    by_cases h : slotDate τ j ≤ n
    · simp only [h, Set.setOf_true]; exact @MeasurableSet.univ _ (information unitSeed T d n)
    · simp only [h, Set.setOf_false]; exact @MeasurableSet.empty _ (information unitSeed T d n)
  · intro j n
    show @Measurable _ _ (information unitSeed T d n) _
      (fun ω : Transcript unitSeed T d => if slotDate τ j ≤ n then
        windowHead T d θ₀ Δ η (slotDate τ j) ω.2 else 0)
    by_cases h : slotDate τ j ≤ n
    · simp only [h, if_true]
      have hΨ : @Measurable _ _ (information unitSeed T d n) inferInstance
          (fun ω : Transcript unitSeed T d =>
            (ω.1, fun i : Fin T => if i.val < n then ω.2 i else ((0 : Vector d), (0 : ℝ)))) :=
        comap_measurable _
      have hg : Measurable (fun ω' : Transcript unitSeed T d =>
          windowHead T d θ₀ Δ η (slotDate τ j) ω'.2) :=
        (windowHead_measurable T d θ₀ Δ η hΔ hη _).comp measurable_snd
      have e : (fun ω : Transcript unitSeed T d => windowHead T d θ₀ Δ η (slotDate τ j) ω.2) =
          (fun ω' : Transcript unitSeed T d =>
            windowHead T d θ₀ Δ η (slotDate τ j) ω'.2) ∘
          (fun ω : Transcript unitSeed T d =>
            (ω.1, fun i : Fin T => if i.val < n then ω.2 i else ((0 : Vector d), (0 : ℝ)))) := by
        funext ω
        simp only [Function.comp]
        unfold windowHead
        split_ifs with h1
        · rfl
        · congr 2
          unfold anchoredAverage
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          have : i.val < slotDate τ j := (Finset.mem_filter.1 hi).2.2
          show crossMoment θ₀ (ω.2 i) = crossMoment θ₀ (if i.val < n then ω.2 i else (0, 0))
          rw [if_pos (lt_of_lt_of_le this h)]
      rw [e]
      exact hg.comp hΨ
    · simp only [h, if_false]
      exact measurable_const

lemma phase_deployed (T d B : ℕ) (θ₀ : Vector d) (Δ η : ℝ)
    (τ : Fin (B + 2) → ℕ) (hτ : IsSchedule T B τ) (j : Fin (B + 1))
    (i : Fin T) (h1 : τ j.castSucc ≤ i.val) (h2 : i.val < τ j.succ)
    (ω : Transcript unitSeed T d) :
    deployed θ₀ (windowedPolicy T d B θ₀ Δ η τ) ω i =
      windowHead T d θ₀ Δ η (τ j.castSucc) ω.2 := by
  have hmono : Monotone τ := hτ.2.2
  rcases deployed_spec θ₀ (windowedPolicy T d B θ₀ Δ η τ) ω i with
    ⟨h, hall⟩ | ⟨k, hk, hdep, hlater⟩
  · rw [h]
    by_cases hj : j.val = 0
    · have h0 : τ j.castSucc = 0 := by
        have : j.castSucc = 0 := Fin.ext hj
        rw [this]; exact hτ.1
      rw [h0]; simp [windowHead]
    · exfalso
      let k : Fin B := ⟨j.val - 1, by omega⟩
      have := hall k
      rw [date_eq] at this
      have e : slotDate τ k = τ j.castSucc := by
        unfold slotDate; congr 1; ext; simp [k]; omega
      rw [e] at this
      omega
  · rw [hdep, head_eq]
    rw [date_eq] at hk
    have hlt : k.succ.castSucc < j.succ := by
      refine hmono.reflect_lt ?_
      unfold slotDate at hk
      omega
    have hkj : k.val + 1 < j.val + 1 := by simpa [Fin.lt_def] using hlt
    have hkeq : k.val + 1 = j.val := by
      by_contra hne
      have hlt2 : k.val + 1 < j.val := by omega
      let k' : Fin B := ⟨k.val + 1, by omega⟩
      have hk' : k < k' := by simp [Fin.lt_def, k']
      have h3 := hlater k' hk'
      rw [date_eq] at h3
      have : slotDate τ k' ≤ τ j.castSucc := by
        unfold slotDate
        exact hmono (by simp [Fin.le_def, k']; omega)
      omega
    have : slotDate τ k = τ j.castSucc := by
      unfold slotDate; congr 1; ext; simp; omega
    rw [this]

/-! ### Drift path facts -/

lemma dist_le {T d : ℕ} (θ : Fin T → Vector d) (η : ℝ)
    (hθ : ∀ i j : Fin T, j.val = i.val + 1 → ‖θ j - θ i‖ ≤ η) :
    ∀ m : ℕ, ∀ a b : Fin T, b.val = a.val + m → ‖θ b - θ a‖ ≤ η * m := by
  intro m
  induction m with
  | zero =>
    intro a b hab
    have : b = a := Fin.ext (by omega)
    subst this
    simp
  | succ m ih =>
    intro a b hab
    let c : Fin T := ⟨a.val + m, by have := b.isLt; omega⟩
    have h1 := ih a c rfl
    have h2 := hθ c b (by simp [c]; omega)
    calc ‖θ b - θ a‖ ≤ ‖θ b - θ c‖ + ‖θ c - θ a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ η + η * m := by linarith
      _ = η * ((m + 1 : ℕ) : ℝ) := by push_cast; ring

lemma norm_from_start {T d : ℕ} (θ₀ : Vector d) (θ : Fin T → Vector d) (Δ η : ℝ)
    (hθ : θ ∈ driftClass (T := T) θ₀ Δ η) (i : Fin T) :
    ‖θ i - θ₀‖ ≤ Δ + η * i.val := by
  obtain ⟨h0, h1⟩ := hθ
  let a : Fin T := ⟨0, by have := i.isLt; omega⟩
  have := dist_le θ η h1 i.val a i (by simp [a])
  have h2 := h0 a rfl
  calc ‖θ i - θ₀‖ ≤ ‖θ i - θ a‖ + ‖θ a - θ₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ Δ + η * i.val := by linarith

lemma sum_range_real (w : ℕ) : ∑ k ∈ Finset.range w, (k : ℝ) = w * (w - 1) / 2 := by
  induction w with
  | zero => simp
  | succ w ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma window_image (T d : ℕ) (η : ℝ) (n : ℕ) (hn : n ≤ T) :
    (recentWindow T d η n).image Fin.val =
      Finset.Ico (n - windowLength d η n) n := by
  ext m
  simp only [Finset.mem_image, recentWindow, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_Ico]
  constructor
  · rintro ⟨k, ⟨h1, h2⟩, rfl⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨m, by omega⟩, ⟨h1, h2⟩, rfl⟩

lemma window_card (T d : ℕ) (η : ℝ) (n : ℕ) (hn : n ≤ T) :
    (recentWindow T d η n).card = windowLength d η n := by
  have h := window_image T d η n hn
  have hw := windowLength_le d η n
  rw [← Finset.card_image_of_injective _ Fin.val_injective, h, Nat.card_Ico]
  omega

lemma window_sum (T d : ℕ) (η : ℝ) (n : ℕ) (hn : n ≤ T) (f : ℕ → ℝ) :
    ∑ k ∈ recentWindow T d η n, f k.val =
      ∑ m ∈ Finset.Ico (n - windowLength d η n) n, f m := by
  rw [← window_image T d η n hn, Finset.sum_image (fun a _ b _ h => Fin.val_injective h)]

lemma window_triangle (T d : ℕ) (η : ℝ) (n : ℕ) (hn : n ≤ T) :
    ∑ k ∈ recentWindow T d η n, (((n : ℝ) - 1) - (k.val : ℝ)) =
      (windowLength d η n : ℝ) * ((windowLength d η n : ℝ) - 1) / 2 := by
  rw [window_sum T d η n hn (fun m => ((n : ℝ) - 1) - m), Finset.sum_Ico_eq_sum_range,
    Nat.sub_sub_self (windowLength_le d η n)]
  have : ∀ k ∈ Finset.range (windowLength d η n),
      ((n : ℝ) - 1) - ((n - windowLength d η n + k : ℕ) : ℝ) =
        ((windowLength d η n : ℝ) - 1) - (k : ℝ) := by
    intro k _
    have hw := windowLength_le d η n
    push_cast [Nat.cast_sub hw]
    ring
  rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, sum_range_real]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

end TRS.Dev.DriftWin
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement
open TRS.Dev.DriftBase TRS.Dev.DriftNum TRS.Dev.DriftWin

noncomputable section

namespace TRS.Dev.DriftRound

lemma lintegral_three {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (a : Ω → Vector d) (b c : Vector d) :
    ∫⁻ z, ENNReal.ofReal ((1 / 2 : ℝ) * ‖a z + b + c‖ ^ 2) ∂μ ≤
      ENNReal.ofReal (3 / 2) * ∫⁻ z, ENNReal.ofReal (‖a z‖ ^ 2) ∂μ +
        ENNReal.ofReal (3 / 2 * (‖b‖ ^ 2 + ‖c‖ ^ 2)) := by
  have hpt : ∀ z, ENNReal.ofReal ((1 / 2 : ℝ) * ‖a z + b + c‖ ^ 2) ≤
      ENNReal.ofReal (3 / 2) * ENNReal.ofReal (‖a z‖ ^ 2) +
        ENNReal.ofReal (3 / 2 * (‖b‖ ^ 2 + ‖c‖ ^ 2)) := by
    intro z
    rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h1 : ‖a z + b + c‖ ≤ ‖a z‖ + ‖b‖ + ‖c‖ :=
      (norm_add_le _ _).trans (by have := norm_add_le (a z) b; linarith)
    have h2 : ‖a z + b + c‖ ^ 2 ≤ (‖a z‖ + ‖b‖ + ‖c‖) ^ 2 := by gcongr
    nlinarith [sq_nonneg (‖a z‖ - ‖b‖), sq_nonneg (‖a z‖ - ‖c‖), sq_nonneg (‖b‖ - ‖c‖)]
  calc ∫⁻ z, ENNReal.ofReal ((1 / 2 : ℝ) * ‖a z + b + c‖ ^ 2) ∂μ
      ≤ ∫⁻ z, (ENNReal.ofReal (3 / 2) * ENNReal.ofReal (‖a z‖ ^ 2) +
        ENNReal.ofReal (3 / 2 * (‖b‖ ^ 2 + ‖c‖ ^ 2))) ∂μ := lintegral_mono hpt
    _ = _ := by
        rw [lintegral_add_right _ measurable_const,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        simp

lemma card_pos_of (T d : ℕ) (hd : 0 < d) (η : ℝ) (n : ℕ) (hn1 : 1 ≤ n) (hnT : n ≤ T) :
    0 < (recentWindow T d η n).card := by
  rw [window_card T d η n hnT]
  exact windowLength_pos d hd η n hn1

/-- Bias of the window average. -/
lemma bias_bound {T d : ℕ} (hd : 0 < d) (θ₀ : Vector d) (θ : Fin T → Vector d) (η : ℝ)
    (hη : 0 ≤ η) (hθ : ∀ i j : Fin T, j.val = i.val + 1 → ‖θ j - θ i‖ ≤ η)
    (n : ℕ) (hn1 : 1 ≤ n) (hnT : n < T) :
    ‖pathAverage (fun k => θ k - θ₀) (recentWindow T d η n) -
        (θ ⟨n - 1, by omega⟩ - θ₀)‖ ≤ η * (windowLength d η n : ℝ) / 2 := by
  set I := recentWindow T d η n with hI
  set w : ℕ := windowLength d η n with hw
  have hcard : I.card = w := window_card T d η n hnT.le
  have hw1 : 1 ≤ w := windowLength_pos d hd η n hn1
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw1
  set c0 := θ ⟨n - 1, by omega⟩ - θ₀ with hc0
  have hsub : ∀ k : Fin T, θ k - θ ⟨n - 1, by omega⟩ = (θ k - θ₀) - c0 := by
    intro k; simp only [hc0]; abel
  have e : pathAverage (fun k => θ k - θ₀) I - c0 =
      (w : ℝ)⁻¹ • ∑ k ∈ I, (θ k - θ ⟨n - 1, by omega⟩) := by
    simp only [hsub]
    have h1 : ∑ k ∈ I, ((θ k - θ₀) - c0) = ∑ k ∈ I, (θ k - θ₀) - (w : ℝ) • c0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, hcard, Nat.cast_smul_eq_nsmul]
    rw [h1, smul_sub, smul_smul, inv_mul_cancel₀ hwR.ne', one_smul]
    unfold pathAverage
    rw [hcard]
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hwR)]
  have hterm : ∀ k ∈ I, ‖θ k - θ ⟨n - 1, by omega⟩‖ ≤ η * (((n : ℝ) - 1) - (k.val : ℝ)) := by
    intro k hk
    have hkn : k.val < n := (Finset.mem_filter.1 hk).2.2
    have := dist_le θ η hθ (n - 1 - k.val) k ⟨n - 1, by omega⟩ (by simp; omega)
    rw [norm_sub_rev]
    have hc : ((n - 1 - k.val : ℕ) : ℝ) = ((n : ℝ) - 1) - (k.val : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub hn1]; simp
    rwa [hc] at this
  calc (w : ℝ)⁻¹ * ‖∑ k ∈ I, (θ k - θ ⟨n - 1, by omega⟩)‖
      ≤ (w : ℝ)⁻¹ * ∑ k ∈ I, ‖θ k - θ ⟨n - 1, by omega⟩‖ := by
        gcongr; exact norm_sum_le _ _
    _ ≤ (w : ℝ)⁻¹ * ∑ k ∈ I, η * (((n : ℝ) - 1) - (k.val : ℝ)) := by
        gcongr with k hk; exact hterm k hk
    _ = (w : ℝ)⁻¹ * (η * ((w : ℝ) * ((w : ℝ) - 1) / 2)) := by
        rw [← Finset.mul_sum, hI, window_triangle T d η n hnT.le]
    _ ≤ η * (w : ℝ) / 2 := by
        have : (w : ℝ)⁻¹ * (η * ((w : ℝ) * ((w : ℝ) - 1) / 2)) = η * ((w : ℝ) - 1) / 2 := by
          field_simp
        rw [this]; nlinarith

theorem round_bound (T d : ℕ) (hd : 0 < d) (θ₀ : Vector d) (Δ η : ℝ) (hΔ : 0 < Δ)
    (hΔ₂ : Δ ≤ 1 / 2) (hη : 0 ≤ η) (hηT : η * T ≤ 1 / 4)
    (θ : Fin T → Vector d) (hθ : θ ∈ driftClass (T := T) θ₀ Δ η)
    (n i : ℕ) (hn1 : 1 ≤ n) (hnT : n < T) (hni : n ≤ i) (hiT : i < T) :
    ∫⁻ z, ENNReal.ofReal ((1 / 2 : ℝ) *
        ‖windowHead T d θ₀ Δ η n (observations θ z) - θ ⟨i, hiT⟩‖ ^ 2) ∂(gaussianRows T d) ≤
      ENNReal.ofReal (3 / 2 * (min (3 * (d : ℝ) / (windowLength d η n : ℝ))
          (4 * (Δ + η * n) ^ 2) + η ^ 2 * (windowLength d η n : ℝ) ^ 2 / 4 +
        η ^ 2 * (((i : ℝ) - n + 1)) ^ 2)) := by
  have hT0 : 0 < T := by omega
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hβ : ∀ k, ‖θ k - θ₀‖ ≤ 1 := by
    intro k
    have h1 := norm_from_start θ₀ θ Δ η hθ k
    have h2 : η * (k.val : ℝ) ≤ η * T := by
      gcongr; exact_mod_cast k.isLt.le
    linarith
  have cm := (anchored_cross_moments T d hT0 hd θ₀ θ hβ).2
  set I := recentWindow T d η n with hI
  have hcard : I.card = windowLength d η n := window_card T d η n hnT.le
  have hIne : I.Nonempty := by
    rw [← Finset.card_pos]; exact card_pos_of T d hd η n hn1 hnT.le
  set R : ℝ := Δ + η * n with hR
  have hR0 : 0 ≤ R := by positivity
  set K : Set (Vector d) := Metric.closedBall (0 : Vector d) R with hK
  set ā := pathAverage (fun k => θ k - θ₀) I with hā
  have hmem : ā ∈ K := by
    rw [hK, mem_closedBall_zero_iff, hā]
    unfold pathAverage
    have hw : (0 : ℝ) < I.card := by exact_mod_cast Finset.card_pos.2 hIne
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hw)]
    calc (I.card : ℝ)⁻¹ * ‖∑ k ∈ I, (θ k - θ₀)‖ ≤ (I.card : ℝ)⁻¹ * ∑ k ∈ I, R := by
          gcongr
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k hk => ?_))
          have hk' : k.val < n := (Finset.mem_filter.1 hk).2.2
          have h1 := norm_from_start θ₀ θ Δ η hθ k
          have h2 : η * (k.val : ℝ) ≤ η * n := by
            gcongr
          rw [hR]; linarith
      _ = R := by
          rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hw.ne', one_mul]
  have hcl := cm I hIne K Metric.isClosed_closedBall (convex_closedBall _ _) hmem
  -- the projection error bound
  have hproj : ∫⁻ z, ENNReal.ofReal (‖convexProjection K
      (anchoredAverage θ₀ I (observations θ z)) - ā‖ ^ 2) ∂(gaussianRows T d) ≤
      ENNReal.ofReal (min (3 * (d : ℝ) / (windowLength d η n : ℝ)) (4 * R ^ 2)) := by
    refine hcl.trans ?_
    rw [ENNReal.ofReal_min]
    refine min_le_min ?_ ?_
    · rw [hcard]
      apply ENNReal.ofReal_le_ofReal
      have hw1 : (1 : ℝ) ≤ windowLength d η n := by exact_mod_cast windowLength_pos d hd η n hn1
      have : (2 * (d : ℝ) + 1) / (windowLength d η n : ℝ) ≤ 3 * (d : ℝ) / (windowLength d η n : ℝ) := by
        gcongr; linarith
      exact this
    · have h1 : Metric.ediam K ≤ ENNReal.ofReal (2 * R) := by
        refine Metric.ediam_le_of_forall_dist_le (fun x hx y hy => ?_)
        rw [hK, Metric.mem_closedBall, dist_zero_right] at hx hy
        calc dist x y ≤ ‖x‖ + ‖y‖ := by rw [dist_eq_norm]; exact norm_sub_le _ _
          _ ≤ 2 * R := by linarith
      calc Metric.ediam K ^ 2 ≤ ENNReal.ofReal (2 * R) ^ 2 := by gcongr
        _ = ENNReal.ofReal (4 * R ^ 2) := by
            rw [← ENNReal.ofReal_pow (by positivity)]; congr 1; ring
  -- decomposition
  let a : GaussianRows T d → Vector d := fun z =>
    convexProjection K (anchoredAverage θ₀ I (observations θ z)) - ā
  let b : Vector d := ā - (θ ⟨n - 1, by omega⟩ - θ₀)
  let c : Vector d := θ ⟨n - 1, by omega⟩ - θ ⟨i, hiT⟩
  have hdec : ∀ z, windowHead T d θ₀ Δ η n (observations θ z) - θ ⟨i, hiT⟩ = a z + b + c := by
    intro z
    unfold windowHead
    rw [if_neg (by omega)]
    simp only [a, b, c]
    abel
  have hb : ‖b‖ ≤ η * (windowLength d η n : ℝ) / 2 :=
    bias_bound hd θ₀ θ η hη hθ.2 n hn1 hnT
  have hc : ‖c‖ ≤ η * (((i : ℝ) - n + 1)) := by
    have := dist_le θ η hθ.2 (i + 1 - n) ⟨n - 1, by omega⟩ ⟨i, hiT⟩ (by simp; omega)
    rw [norm_sub_rev] at this
    have hc' : ((i + 1 - n : ℕ) : ℝ) = (i : ℝ) - n + 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rwa [hc'] at this
  simp_rw [hdec]
  refine (lintegral_three (gaussianRows T d) a b c).trans ?_
  have h3 : ENNReal.ofReal (3 / 2) * ∫⁻ z, ENNReal.ofReal (‖a z‖ ^ 2) ∂(gaussianRows T d) ≤
      ENNReal.ofReal (3 / 2) * ENNReal.ofReal (min (3 * (d : ℝ) / (windowLength d η n : ℝ))
        (4 * R ^ 2)) := by gcongr
  refine (add_le_add h3 le_rfl).trans ?_
  rw [← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity)
      (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hb2 : ‖b‖ ^ 2 ≤ η ^ 2 * (windowLength d η n : ℝ) ^ 2 / 4 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hb 2
    nlinarith
  have hc2 : ‖c‖ ^ 2 ≤ η ^ 2 * (((i : ℝ) - n + 1)) ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hc 2
    nlinarith
  linarith

end TRS.Dev.DriftRound
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement
open TRS.Dev.DriftBase TRS.Dev.DriftNum TRS.Dev.DriftWin TRS.Dev.DriftRound

noncomputable section

namespace TRS.Dev.DriftUpper

/-- Summing a per-round bound over the phases of a schedule (phase-dependent bound). -/
lemma phase_sum_bound (T B : ℕ) (τ : Fin (B + 2) → ℕ) (hτ : IsSchedule T B τ)
    (g : ℕ → ℝ≥0∞) (F : Fin (B + 1) → ℝ) (hF : ∀ j, 0 ≤ F j)
    (h : ∀ j : Fin (B + 1), ∀ i, τ j.castSucc ≤ i → i < τ j.succ →
      g i ≤ ENNReal.ofReal (F j)) :
    ∑ i ∈ Finset.range T, g i ≤
      ENNReal.ofReal (∑ j : Fin (B + 1), phaseLength τ j * F j) := by
  have hmono : Monotone τ := hτ.2.2
  have ht := tt_mono T B τ hτ
  have t0 := tt_zero T B τ hτ
  have tB := tt_last T B τ hτ
  have tj := tt_cast T B τ
  have tj1 := tt_succ T B τ
  set t := tt T B τ with htdef
  have hs := sum_Ico_phases' t ht (fun i => g i) (B + 1)
  rw [t0, tB] at hs
  rw [Finset.range_eq_Ico, hs]
  rw [Finset.sum_range]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_le_sum (fun j _ => ?_)
    calc ∑ i ∈ Finset.Ico (t j.val) (t (j.val + 1)), g i
        ≤ ∑ i ∈ Finset.Ico (t j.val) (t (j.val + 1)), ENNReal.ofReal (F j) := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          rw [Finset.mem_Ico, tj, tj1] at hi
          exact h j i hi.1 hi.2
      _ = ENNReal.ofReal (phaseLength τ j * F j) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, tj, tj1]
          have hle : τ j.castSucc ≤ τ j.succ := hmono (by simp [Fin.le_def])
          have hpl : phaseLength τ j = ((τ j.succ - τ j.castSucc : ℕ) : ℝ) := by
            unfold phaseLength; rw [Nat.cast_sub hle]
          rw [hpl, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  · intro j _
    unfold phaseLength
    have hle : τ j.castSucc ≤ τ j.succ := hmono (by simp [Fin.le_def])
    have : (τ j.castSucc : ℝ) ≤ τ j.succ := by exact_mod_cast hle
    exact mul_nonneg (by linarith) (hF _)

lemma sum_phaseLength (T B : ℕ) (τ : Fin (B + 2) → ℕ) (hτ : IsSchedule T B τ) :
    ∑ j : Fin (B + 1), phaseLength τ j = T := by
  have t0 := tt_zero T B τ hτ
  have tB := tt_last T B τ hτ
  have tj := tt_cast T B τ
  have tj1 := tt_succ T B τ
  have h1 : ∀ j : Fin (B + 1), phaseLength τ j =
      ((tt T B τ (j.val + 1) : ℕ) : ℝ) - ((tt T B τ j.val : ℕ) : ℝ) := by
    intro j; unfold phaseLength; rw [tj, tj1]
  simp_rw [h1]
  rw [Fin.sum_univ_eq_sum_range (fun j => ((tt T B τ (j + 1) : ℕ) : ℝ) - ((tt T B τ j : ℕ) : ℝ)),
    Finset.sum_range_sub (fun j => ((tt T B τ j : ℕ) : ℝ)), tB, t0]
  simp

lemma trackingRate_nonneg (T d : ℕ) (η : ℝ) (hη : 0 ≤ η) : 0 ≤ trackingRate T d η := by
  unfold trackingRate
  exact le_min (Real.rpow_nonneg (by positivity) _) (by positivity)

/-- The per-round bound used on phase `j`. -/
def Fj (T d B : ℕ) (Δ η : ℝ) (τ : Fin (B + 2) → ℕ) (j : Fin (B + 1)) : ℝ :=
  12 * ((d : ℝ) / clampedDate d Δ τ j) + 99 / 2 * trackingRate T d η +
    3 / 2 * (η ^ 2 * phaseLength τ j ^ 2)

lemma clamped_nonneg (d : ℕ) (Δ : ℝ) {B : ℕ} (τ : Fin (B + 2) → ℕ) (j : Fin (B + 1)) :
    0 ≤ clampedDate d Δ τ j := by
  unfold clampedDate
  split_ifs
  · positivity
  · exact le_max_of_le_right (by positivity)

lemma round_phase (T d B : ℕ) (hd : 0 < d) (θ₀ : Vector d) (Δ η : ℝ) (hΔ : 0 < Δ)
    (hΔ₂ : Δ ≤ 1 / 2) (hη : 0 ≤ η) (hηT : η * T ≤ 1 / 4) (hdη : (d : ℝ) * η ≤ 1 / 8)
    (τ : Fin (B + 2) → ℕ) (hτ : IsSchedule T B τ)
    (θ : Fin T → Vector d) (hθ : θ ∈ driftClass (T := T) θ₀ Δ η)
    (j : Fin (B + 1)) (i : ℕ) (hi1 : τ j.castSucc ≤ i) (hi2 : i < τ j.succ) (hiT : i < T) :
    ∫⁻ z, ENNReal.ofReal ((1 / 2 : ℝ) *
        ‖windowHead T d θ₀ Δ η (τ j.castSucc) (observations θ z) - θ ⟨i, hiT⟩‖ ^ 2)
      ∂(gaussianRows T d) ≤ ENNReal.ofReal (Fj T d B Δ η τ j) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hφ := trackingRate_nonneg T d η hη
  have hL : (i : ℝ) + 1 ≤ (τ j.succ : ℝ) := by exact_mod_cast hi2
  by_cases h0 : τ j.castSucc = 0
  · have hj : clampedDate d Δ τ j = (d : ℝ) / Δ ^ 2 := by
      unfold clampedDate
      by_cases hj0 : j.val = 0
      · simp [hj0]
      · simp only [hj0, if_false]
        unfold phaseStart
        rw [h0]
        simp only [Nat.cast_zero]
        exact max_eq_right (by positivity)
    have hdx : (d : ℝ) / clampedDate d Δ τ j = Δ ^ 2 := by
      rw [hj]; field_simp
    have hhead : windowHead T d θ₀ Δ η (τ j.castSucc) = fun _ => θ₀ := by
      funext h; rw [h0]; simp [windowHead]
    rw [hhead]
    simp only
    rw [lintegral_const, measure_univ, mul_one]
    apply ENNReal.ofReal_le_ofReal
    have h1 := norm_from_start θ₀ θ Δ η hθ ⟨i, hiT⟩
    have hLL : (i : ℝ) ≤ phaseLength τ j := by
      unfold phaseLength; rw [h0]; simp only [Nat.cast_zero, sub_zero]; linarith
    have h2 : ‖θ₀ - θ ⟨i, hiT⟩‖ ≤ Δ + η * i := by rw [norm_sub_rev]; exact h1
    have h3 : ‖θ₀ - θ ⟨i, hiT⟩‖ ^ 2 ≤ (Δ + η * i) ^ 2 := by gcongr
    have h4 : (Δ + η * i) ^ 2 ≤ 2 * Δ ^ 2 + 2 * (η * i) ^ 2 := sq_add_le _ _
    have h5 : (η * (i : ℝ)) ^ 2 ≤ η ^ 2 * phaseLength τ j ^ 2 := by
      rw [mul_pow]; gcongr
    unfold Fj
    rw [hdx]
    nlinarith [sq_nonneg Δ, sq_nonneg (η * phaseLength τ j)]
  · have hn1 : 1 ≤ τ j.castSucc := Nat.one_le_iff_ne_zero.2 h0
    have hnT : τ j.castSucc < T := lt_of_le_of_lt hi1 hiT
    have hj0 : j.val ≠ 0 := by
      intro h
      apply h0
      have : j.castSucc = 0 := Fin.ext h
      rw [this]; exact hτ.1
    have hclamp : clampedDate d Δ τ j = max ((τ j.castSucc : ℕ) : ℝ) ((d : ℝ) / Δ ^ 2) := by
      unfold clampedDate; simp only [hj0, if_false]; rfl
    refine (round_bound T d hd θ₀ Δ η hΔ hΔ₂ hη hηT θ hθ (τ j.castSucc) i hn1 hnT hi1 hiT).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have hnum := numeric T d hd Δ η hΔ hη hdη (τ j.castSucc) hn1 hnT
    have hu : (i : ℝ) - (τ j.castSucc : ℝ) + 1 ≤ phaseLength τ j := by
      unfold phaseLength; linarith
    have hu0 : 0 ≤ (i : ℝ) - (τ j.castSucc : ℝ) + 1 := by
      have : (τ j.castSucc : ℝ) ≤ i := by exact_mod_cast hi1
      linarith
    have hu2 : ((i : ℝ) - (τ j.castSucc : ℝ) + 1) ^ 2 ≤ phaseLength τ j ^ 2 := by gcongr
    have hu3 : η ^ 2 * ((i : ℝ) - (τ j.castSucc : ℝ) + 1) ^ 2 ≤ η ^ 2 * phaseLength τ j ^ 2 := by
      gcongr
    unfold Fj
    rw [hclamp]
    linarith

end TRS.Dev.DriftUpper
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement
open TRS.Dev.DriftBase TRS.Dev.DriftNum TRS.Dev.DriftWin TRS.Dev.DriftRound TRS.Dev.DriftUpper

noncomputable section

namespace TRS.Dev.DriftUpper2

lemma lintegral_snd_prob {S X : Type*} [MeasurableSpace S] [MeasurableSpace X]
    (P : Measure S) [IsProbabilityMeasure P] (ν : Measure X) [SFinite ν]
    (F : X → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ω, F ω.2 ∂(P.prod ν) = ∫⁻ x, F x ∂ν := by
  rw [lintegral_prod (fun ω : S × X => F ω.2) (hF.comp measurable_snd).aemeasurable]
  simp

lemma obs_measurable {T d : ℕ} (θ : Fin T → Vector d) :
    Measurable (fun z : GaussianRows T d => observations θ z) := (obs_continuous _).measurable

/-- Risk of the windowed policy on one path of the class. -/
theorem risk_le (T d B : ℕ) (hd : 0 < d) (θ₀ : Vector d) (Δ η : ℝ) (hΔ : 0 < Δ)
    (hΔ₂ : Δ ≤ 1 / 2) (hη : 0 ≤ η) (hηT : η * T ≤ 1 / 4) (hdη : (d : ℝ) * η ≤ 1 / 8)
    (τ : Fin (B + 2) → ℕ) (hτ : IsSchedule T B τ)
    (θ : Fin T → Vector d) (hθ : θ ∈ driftClass (T := T) θ₀ Δ η) :
    policyRisk θ₀ (windowedPolicy T d B θ₀ Δ η τ) θ ≤
      ENNReal.ofReal (∑ j : Fin (B + 1), phaseLength τ j * Fj T d B Δ η τ j) := by
  set π := windowedPolicy T d B θ₀ Δ η τ with hπ
  have hmono : Monotone τ := hτ.2.2
  have hτT : ∀ m : Fin (B + 2), τ m ≤ T := by
    intro m; rw [← hτ.2.1]; exact hmono (by simp [Fin.le_def]; omega)
  have hobs := obs_measurable θ
  set e : ℕ → GaussianRows T d → ℝ := fun i z =>
    if hi : i < T then ‖deployed θ₀ π (((), observations θ z) :
      Transcript unitSeed T d) ⟨i, hi⟩ - θ ⟨i, hi⟩‖ ^ 2 else 0 with he
  have hephase : ∀ i (hi : i < T), ∃ j : Fin (B + 1), τ j.castSucc ≤ i ∧ i < τ j.succ ∧
      ∀ z, e i z = ‖windowHead T d θ₀ Δ η (τ j.castSucc) (observations θ z) -
        θ ⟨i, hi⟩‖ ^ 2 := by
    intro i hi
    obtain ⟨j, hj1, hj2⟩ := exists_phase T B τ hτ i hi
    refine ⟨j, hj1, hj2, fun z => ?_⟩
    simp only [he, dif_pos hi]
    rw [phase_deployed T d B θ₀ Δ η τ hτ j ⟨i, hi⟩ hj1 hj2]
  have he_meas : ∀ i, Measurable (e i) := by
    intro i
    by_cases hi : i < T
    · obtain ⟨j, -, -, hj⟩ := hephase i hi
      have : e i = fun z => ‖windowHead T d θ₀ Δ η (τ j.castSucc)
        (observations θ z) - θ ⟨i, hi⟩‖ ^ 2 := funext hj
      rw [this]
      exact ((((windowHead_measurable T d θ₀ Δ η hΔ.le hη _).comp hobs).sub
        measurable_const).norm).pow_const 2
    · have : e i = fun _ => 0 := by funext z; simp [he, hi]
      rw [this]; exact measurable_const
  have h1 : policyRisk θ₀ π θ =
      ∫⁻ ω : unitSeed.space × GaussianRows T d,
        (fun z : GaussianRows T d => ∑ i ∈ Finset.range T,
          ENNReal.ofReal ((1 / 2 : ℝ) * e i z)) ω.2
        ∂(unitSeed.law.prod (gaussianRows T d)) := by
    unfold policyRisk
    apply lintegral_congr
    intro ω
    show _ = ∑ i ∈ Finset.range T, ENNReal.ofReal ((1 / 2 : ℝ) * e i ω.2)
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (by norm_num) (by
      simp only [he]; split_ifs <;> positivity)), ← Finset.mul_sum]
    congr 2
    rw [← Fin.sum_univ_eq_sum_range (fun i => e i ω.2) T]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [he, dif_pos i.isLt]
    rfl
  have hmi : ∀ i, Measurable (fun z : GaussianRows T d =>
      ENNReal.ofReal ((1 / 2 : ℝ) * e i z)) :=
    fun i => Measurable.ennreal_ofReal (measurable_const.mul (he_meas i))
  have hm : Measurable (fun z : GaussianRows T d => ∑ i ∈ Finset.range T,
      ENNReal.ofReal ((1 / 2 : ℝ) * e i z)) :=
    Finset.measurable_sum _ (fun i _ => hmi i)
  rw [h1, lintegral_snd_prob unitSeed.law (gaussianRows T d) _ hm]
  rw [lintegral_finset_sum _ (fun i _ => hmi i)]
  have hF0 : ∀ j, 0 ≤ Fj T d B Δ η τ j := by
    intro j
    unfold Fj
    have h1 : 0 ≤ (d : ℝ) / clampedDate d Δ τ j :=
      div_nonneg (by positivity) (clamped_nonneg d Δ τ j)
    have := trackingRate_nonneg T d η hη
    positivity
  refine phase_sum_bound T B τ hτ
    (fun i => ∫⁻ z, ENNReal.ofReal ((1 / 2 : ℝ) * e i z) ∂(gaussianRows T d))
    (Fj T d B Δ η τ) hF0 ?_ |>.trans (le_of_eq rfl)
  intro j i hi1 hi2
  have hiT : i < T := lt_of_lt_of_le hi2 (hτT _)
  obtain ⟨j', hj1, hj2, hj3⟩ := hephase i hiT
  have hjj : j' = j := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : j'.succ ≤ j.castSucc := by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
        have := Fin.lt_def.1 hlt; omega
      have := hmono this
      omega
    · have : j.succ ≤ j'.castSucc := by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
        have := Fin.lt_def.1 hgt; omega
      have := hmono this
      omega
  subst hjj
  simp only [hj3]
  exact round_phase T d B hd θ₀ Δ η hΔ hΔ₂ hη hηT hdη τ hτ θ hθ j' i hi1 hi2 hiT

end TRS.Dev.DriftUpper2
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement
open TRS.Dev.DriftBase TRS.Dev.DriftNum TRS.Dev.DriftWin TRS.Dev.DriftRound TRS.Dev.DriftUpper
open TRS.Dev.DriftUpper2

noncomputable section

namespace TRS.Dev.DriftUpper3

lemma sum_bound (T d B : ℕ) (hd : 0 < d) (Δ η : ℝ) (hΔ : 0 < Δ) (hη : 0 ≤ η)
    (τ : Fin (B + 2) → ℕ) (hτ : IsSchedule T B τ) :
    ∑ j : Fin (B + 1), phaseLength τ j * Fj T d B Δ η τ j ≤
      12 * driftProgram d Δ η τ + 50 * T * trackingRate T d η := by
  have hφ := trackingRate_nonneg T d η hη
  have hL : ∀ j : Fin (B + 1), 0 ≤ phaseLength τ j := by
    intro j
    unfold phaseLength
    have hle : τ j.castSucc ≤ τ j.succ := hτ.2.2 (by simp [Fin.le_def])
    have : (τ j.castSucc : ℝ) ≤ τ j.succ := by exact_mod_cast hle
    linarith
  have hsum := sum_phaseLength T B τ hτ
  have hterm : ∀ j : Fin (B + 1), phaseLength τ j * Fj T d B Δ η τ j ≤
      12 * (phaseLength τ j * (d : ℝ) / clampedDate d Δ τ j + η ^ 2 * phaseLength τ j ^ 3) +
        99 / 2 * trackingRate T d η * phaseLength τ j := by
    intro j
    unfold Fj
    have h1 : phaseLength τ j * (12 * ((d : ℝ) / clampedDate d Δ τ j)) =
        12 * (phaseLength τ j * (d : ℝ) / clampedDate d Δ τ j) := by ring
    have h2 : 0 ≤ η ^ 2 * phaseLength τ j ^ 3 := by have := hL j; positivity
    nlinarith [h1, h2]
  calc ∑ j : Fin (B + 1), phaseLength τ j * Fj T d B Δ η τ j
      ≤ ∑ j : Fin (B + 1), (12 * (phaseLength τ j * (d : ℝ) / clampedDate d Δ τ j +
          η ^ 2 * phaseLength τ j ^ 3) + 99 / 2 * trackingRate T d η * phaseLength τ j) :=
        Finset.sum_le_sum (fun j _ => hterm j)
    _ = 12 * driftProgram d Δ η τ + 99 / 2 * trackingRate T d η * T := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum]
        unfold driftProgram
        rfl
    _ ≤ _ := by nlinarith [mul_nonneg hφ (Nat.cast_nonneg T : (0 : ℝ) ≤ T)]

theorem worst_le (T d B : ℕ) (hd : 0 < d) (θ₀ : Vector d) (Δ η : ℝ) (hΔ : 0 < Δ)
    (hΔ₂ : Δ ≤ 1 / 2) (hη : 0 ≤ η) (hηT : η * T ≤ 1 / 4) (hdη : (d : ℝ) * η ≤ 1 / 8)
    (τ : Fin (B + 2) → ℕ) (hτ : IsSchedule T B τ) :
    driftWorstRisk θ₀ Δ η (windowedPolicy T d B θ₀ Δ η τ) ≤
      ENNReal.ofReal (12 * driftProgram d Δ η τ + 50 * T * trackingRate T d η) := by
  unfold driftWorstRisk
  apply iSup_le
  rintro ⟨θ, hθ⟩
  exact (risk_le T d B hd θ₀ Δ η hΔ hΔ₂ hη hηT hdη τ hτ θ hθ).trans
    (ENNReal.ofReal_le_ofReal (sum_bound T d B hd Δ η hΔ hη τ hτ))

lemma optimum_attained (T B d : ℕ) (Δ η : ℝ) :
    ∃ τ, IsSchedule T B τ ∧ driftProgram d Δ η τ = driftOptimum T d B Δ η := by
  have hfin := (schedule_finite T B).image (driftProgram d Δ η)
  have hne := (schedule_nonempty T B).image (driftProgram d Δ η)
  obtain ⟨τ, hτ, h⟩ := hne.csInf_mem hfin
  exact ⟨τ, hτ, h⟩

theorem upper_parts (T d B : ℕ) (hd : 0 < d) (θ₀ : Vector d) (Δ η : ℝ) (hΔ : 0 < Δ)
    (hΔ₂ : Δ ≤ 1 / 2) (hη : 0 ≤ η) (hηT : η * T ≤ 1 / 4) (hdη : (d : ℝ) * η ≤ 1 / 8) :
    driftMinimaxRisk T d B θ₀ Δ η ≤
      ENNReal.ofReal (12 * driftOptimum T d B Δ η + 50 * T * trackingRate T d η) ∧
    (∀ τ : Fin (B + 2) → ℕ, IsSchedule T B τ → driftProgram d Δ η τ = driftOptimum T d B Δ η →
      IsCausal (windowedPolicy T d B θ₀ Δ η τ) ∧
      HasDeterministicDates (windowedPolicy T d B θ₀ Δ η τ) ∧
      driftWorstRisk θ₀ Δ η (windowedPolicy T d B θ₀ Δ η τ) ≤
        ENNReal.ofReal (12 * driftOptimum T d B Δ η + 50 * T * trackingRate T d η)) := by
  have key : ∀ τ : Fin (B + 2) → ℕ, IsSchedule T B τ →
      driftProgram d Δ η τ = driftOptimum T d B Δ η →
      IsCausal (windowedPolicy T d B θ₀ Δ η τ) ∧
      HasDeterministicDates (windowedPolicy T d B θ₀ Δ η τ) ∧
      driftWorstRisk θ₀ Δ η (windowedPolicy T d B θ₀ Δ η τ) ≤
        ENNReal.ofReal (12 * driftOptimum T d B Δ η + 50 * T * trackingRate T d η) := by
    intro τ hτ hopt
    refine ⟨isCausal_window T d B θ₀ Δ η hΔ.le hη τ hτ, fun j => ⟨slotDate τ j, fun _ => rfl⟩, ?_⟩
    have := worst_le T d B hd θ₀ Δ η hΔ hΔ₂ hη hηT hdη τ hτ
    rwa [hopt] at this
  refine ⟨?_, key⟩
  obtain ⟨τ, hτ, hopt⟩ := optimum_attained T B d Δ η
  obtain ⟨hc, -, hw⟩ := key τ hτ hopt
  exact le_trans (sInf_le ⟨unitSeed, windowedPolicy T d B θ₀ Δ η τ, hc, rfl⟩) hw

end TRS.Dev.DriftUpper3
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement

noncomputable section

namespace TRS.Dev.DriftLower1

lemma norm_embedBlock {d : ℕ} (S : Finset (Fin d)) (v : BlockVector S) :
    ‖embedBlock S v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  set F : Fin d → ℝ := fun i => ‖(if h : i ∈ S then v ⟨i, h⟩ else 0 : ℝ)‖ ^ 2 with hF
  have h1 : ∑ i : Fin d, ‖(embedBlock S v) i‖ ^ 2 = ∑ i : Fin d, F i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [embedBlock, hF]
  have h2 : ∑ i : S, ‖v i‖ ^ 2 = ∑ i ∈ S, F i := by
    rw [← Finset.sum_coe_sort S F]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hF]
  rw [h1, h2]
  symm
  apply Finset.sum_subset (Finset.subset_univ S)
  intro i _ hi
  simp [hF, hi]


lemma blockProj_embed {d : ℕ} (S : Finset (Fin d)) (h : BlockVector S) :
    blockProjection S (embedBlock S h) = h := by
  ext i
  simp [blockProjection, embedBlock]

lemma blockProj_sub {d : ℕ} (S : Finset (Fin d)) (v w : Vector d) :
    blockProjection S (v - w) = blockProjection S v - blockProjection S w := by
  ext i; simp [blockProjection]

lemma blockProj_add {d : ℕ} (S : Finset (Fin d)) (v w : Vector d) :
    blockProjection S (v + w) = blockProjection S v + blockProjection S w := by
  ext i; simp [blockProjection]

/-- The centre of the prior. -/

lemma le_zpow_ceil (x : ℝ) (hx : 0 < x) : x ≤ (2 : ℝ) ^ ⌈Real.logb 2 x⌉ := by
  have h1 : x = (2 : ℝ) ^ (Real.logb 2 x) := (Real.rpow_logb (by norm_num) (by norm_num) hx).symm
  have h2 : (2 : ℝ) ^ (Real.logb 2 x) ≤ (2 : ℝ) ^ ((⌈Real.logb 2 x⌉ : ℤ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (Int.le_ceil _)
  rw [Real.rpow_intCast] at h2
  linarith


/-- Reshuffle `(u,(σ,z)) ↦ (σ,(u,z))`. -/
def reshuffle (α β γ : Type*) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    α × (β × γ) ≃ᵐ β × (α × γ) :=
  (MeasurableEquiv.prodAssoc.symm.trans
    ((MeasurableEquiv.prodComm (α := α) (β := β)).prodCongr (MeasurableEquiv.refl γ))).trans
    MeasurableEquiv.prodAssoc

lemma reshuffle_mp {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (ρ : Measure γ) [SFinite μ] [SFinite ν] [SFinite ρ] :
    MeasurePreserving (reshuffle α β γ) (μ.prod (ν.prod ρ)) (ν.prod (μ.prod ρ)) := by
  unfold reshuffle
  have h1 := (measurePreserving_prodAssoc μ ν ρ).symm
  have h2 : MeasurePreserving (Prod.map Prod.swap (id : γ → γ)) ((μ.prod ν).prod ρ)
      ((ν.prod μ).prod ρ) := (Measure.measurePreserving_swap (μ := μ) (ν := ν)).prod
        (MeasurePreserving.id ρ)
  have h3 := measurePreserving_prodAssoc ν μ ρ
  exact h3.comp (h2.comp h1)



instance : IsProbabilityMeasure uniformCoordinate := by
  constructor
  have hemb : MeasurableEmbedding (Subtype.val : CubeCoordinate → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  unfold uniformCoordinate
  rw [Measure.smul_apply, hemb.comap_apply]
  simp
  have : {x : ℝ | -1 ≤ x ∧ x ≤ 1} = Set.Icc (-1) 1 := rfl
  rw [this, Real.volume_Icc]
  norm_num
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ENNReal.inv_mul_cancel] <;> simp

instance instProbU {d : ℕ} (S : Finset (Fin d)) (Δ : ℝ) (L : ℤ) :
    IsProbabilityMeasure (uniformLevels S Δ L) := by
  unfold uniformLevels; infer_instance

end TRS.Dev.DriftLower1
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement
open TRS.Dev.DriftLower1

noncomputable section

namespace TRS.Dev.DriftLower2

variable {d : ℕ}

def i0 (hd : 2 ≤ d) : Fin d := ⟨0, by omega⟩
def i1 (hd : 2 ≤ d) : Fin d := ⟨1, by omega⟩
def Sset (hd : 2 ≤ d) : Finset (Fin d) := Finset.univ.erase (i0 hd)
def e0 (hd : 2 ≤ d) : Vector d := EuclideanSpace.single (i0 hd) (1 : ℝ)
def e1 (hd : 2 ≤ d) : Vector d := EuclideanSpace.single (i1 hd) (1 : ℝ)

/-- The path `g_t = θ₀ + η (t-1) e₀ + (Δ/2) e₁` (index `i` is round `i+1`). -/
def gpath (hd : 2 ≤ d) (T : ℕ) (θ₀ : Vector d) (Δ η : ℝ) : Fin T → Vector d :=
  fun i => θ₀ + (η * (i.val : ℝ)) • e0 hd + (Δ / 2) • e1 hd

def gS (hd : 2 ≤ d) (θ₀ : Vector d) (Δ : ℝ) : BlockVector (Sset hd) :=
  blockProjection (Sset hd) (θ₀ + (Δ / 2) • e1 hd)

lemma i0_ne_i1 (hd : 2 ≤ d) : i0 hd ≠ i1 hd := by
  intro h; have := congrArg Fin.val h; simp [i0, i1] at this

lemma card_Sset (hd : 2 ≤ d) : (Sset hd).card = d - 1 := by
  unfold Sset; rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp

lemma mem_Sset (hd : 2 ≤ d) (k : Fin d) : k ∈ Sset hd ↔ k ≠ i0 hd := by
  unfold Sset; simp

lemma norm_e0 (hd : 2 ≤ d) : ‖e0 hd‖ = 1 := by simp [e0]
lemma norm_e1 (hd : 2 ≤ d) : ‖e1 hd‖ = 1 := by simp [e1]

lemma e0_apply_self (hd : 2 ≤ d) : e0 hd (i0 hd) = 1 := by simp [e0]
lemma e1_apply_i0 (hd : 2 ≤ d) : e1 hd (i0 hd) = 0 := by
  simp [e1, EuclideanSpace.single_apply, (i0_ne_i1 hd)]
lemma e0_apply_of_mem (hd : 2 ≤ d) (k : Fin d) (hk : k ∈ Sset hd) : e0 hd k = 0 := by
  have := (mem_Sset hd k).1 hk
  simp [e0, EuclideanSpace.single_apply, this]

lemma embed_apply_i0 (hd : 2 ≤ d) (h : BlockVector (Sset hd)) : embedBlock (Sset hd) h (i0 hd) = 0 := by
  unfold embedBlock
  have : i0 hd ∉ Sset hd := by rw [mem_Sset]; simp
  simp [this]

lemma norm_sq_split (hd : 2 ≤ d) (v : Vector d) :
    ‖v‖ ^ 2 = (v (i0 hd)) ^ 2 + ‖blockProjection (Sset hd) v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  have h1 : ∑ i : Sset hd, ‖blockProjection (Sset hd) v i‖ ^ 2 =
      ∑ i ∈ Sset hd, ‖v i‖ ^ 2 := by
    rw [← Finset.sum_coe_sort (Sset hd) (fun i => ‖v i‖ ^ 2)]
    rfl
  rw [h1]
  have h2 : ∑ i : Fin d, ‖v i‖ ^ 2 = ‖v (i0 hd)‖ ^ 2 + ∑ i ∈ Sset hd, ‖v i‖ ^ 2 := by
    unfold Sset
    exact (Finset.add_sum_erase Finset.univ (fun i => ‖v i‖ ^ 2) (Finset.mem_univ (i0 hd))).symm
  rw [h2, Real.norm_eq_abs, sq_abs]

lemma blockProj_gpath (hd : 2 ≤ d) (T : ℕ) (θ₀ : Vector d) (Δ η : ℝ) (i : Fin T) :
    blockProjection (Sset hd) (gpath hd T θ₀ Δ η i) = gS hd θ₀ Δ := by
  ext k
  have hk : e0 hd k = 0 := e0_apply_of_mem hd k.val k.2
  simp [gpath, gS, blockProjection, hk]

lemma err_split (hd : 2 ≤ d) (T : ℕ) (θ₀ : Vector d) (Δ η : ℝ) (v : Vector d) (i : Fin T)
    (h : BlockVector (Sset hd)) :
    ‖v - (gpath hd T θ₀ Δ η i + embedBlock (Sset hd) h)‖ ^ 2 =
      (v (i0 hd) - θ₀ (i0 hd) - η * i.val) ^ 2 +
        ‖blockProjection (Sset hd) v - gS hd θ₀ Δ - h‖ ^ 2 := by
  rw [norm_sq_split hd]
  congr 2
  · simp [gpath, e0_apply_self, e1_apply_i0, embed_apply_i0]
    ring
  · rw [blockProj_sub, blockProj_add, blockProj_embed, blockProj_gpath]
    congr 1; abel

lemma norm_blockProj_e1 (hd : 2 ≤ d) : ‖blockProjection (Sset hd) (e1 hd)‖ = 1 := by
  have := norm_sq_split hd (e1 hd)
  rw [e1_apply_i0, norm_e1] at this
  nlinarith [norm_nonneg (blockProjection (Sset hd) (e1 hd))]

lemma init_err (hd : 2 ≤ d) (θ₀ : Vector d) (Δ : ℝ) (hΔ : 0 < Δ) (h : BlockVector (Sset hd))
    (hH : ‖h‖ < Δ / 32) :
    Δ ^ 2 / 8 ≤ ‖blockProjection (Sset hd) θ₀ - gS hd θ₀ Δ - h‖ ^ 2 := by
  have e : blockProjection (Sset hd) θ₀ - gS hd θ₀ Δ - h =
      -((Δ / 2) • blockProjection (Sset hd) (e1 hd) + h) := by
    unfold gS
    rw [blockProj_add]
    have : blockProjection (Sset hd) ((Δ / 2) • e1 hd) =
        (Δ / 2) • blockProjection (Sset hd) (e1 hd) := by ext k; simp [blockProjection]
    rw [this]; abel
  rw [e, norm_neg]
  have h1 := norm_sub_norm_le ((Δ / 2) • blockProjection (Sset hd) (e1 hd)) (-h)
  rw [sub_neg_eq_add, norm_neg, norm_smul, norm_blockProj_e1, Real.norm_eq_abs,
    abs_of_pos (by positivity)] at h1
  have h2 : Δ / 2 - Δ / 32 ≤ ‖(Δ / 2) • blockProjection (Sset hd) (e1 hd) + h‖ := by linarith
  nlinarith

lemma drift_mem (hd : 2 ≤ d) (T : ℕ) (θ₀ : Vector d) (Δ η : ℝ) (hΔ : 0 < Δ) (hη : 0 ≤ η)
    (h : BlockVector (Sset hd)) (hH : ‖h‖ ≤ Δ / 32) :
    (fun i : Fin T => gpath hd T θ₀ Δ η i + embedBlock (Sset hd) h) ∈
      driftClass (T := T) θ₀ Δ η := by
  refine ⟨?_, ?_⟩
  · intro i hi
    have e : gpath hd T θ₀ Δ η i + embedBlock (Sset hd) h - θ₀ =
        (Δ / 2) • e1 hd + embedBlock (Sset hd) h := by
      simp only [gpath, hi, Nat.cast_zero, mul_zero, zero_smul, add_zero]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_e1, norm_embedBlock, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  · intro i j hij
    have e : gpath hd T θ₀ Δ η j + embedBlock (Sset hd) h -
        (gpath hd T θ₀ Δ η i + embedBlock (Sset hd) h) = η • e0 hd := by
      simp only [gpath, hij]
      push_cast
      rw [← sub_eq_zero]
      have : ((η * ((i.val : ℝ) + 1)) • e0 hd) = (η * (i.val : ℝ)) • e0 hd + η • e0 hd := by
        rw [← add_smul]; congr 1; ring
      rw [this]; abel
    rw [e, norm_smul, norm_e0, Real.norm_eq_abs, abs_of_nonneg hη]; simp

/-- Coordinate-zero residual on a phase of constant predictor. -/
lemma quad_lower (c η : ℝ) (a L : ℕ) :
    η ^ 2 * (L : ℝ) * ((L : ℝ) ^ 2 - 1) / 12 ≤
      ∑ t ∈ Finset.Ico a (a + L), (c - η * (t : ℝ)) ^ 2 := by
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  have e : ∀ k ∈ Finset.range L, (c - η * ((a + k : ℕ) : ℝ)) ^ 2 =
      (c - η * a) ^ 2 - 2 * (c - η * a) * η * (k : ℝ) + η ^ 2 * (k : ℝ) ^ 2 := by
    intro k _; push_cast; ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have s2 : ∀ n : ℕ, ∑ k ∈ Finset.range n, (k : ℝ) ^ 2 = ((n : ℝ) - 1) * n * (2 * n - 1) / 6 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rw [← Finset.mul_sum, ← Finset.mul_sum, s2, DriftWin.sum_range_real]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  nlinarith [mul_nonneg hL (sq_nonneg ((c - η * a) - η * ((L : ℝ) - 1) / 2))]

end TRS.Dev.DriftLower2
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement
open TRS.Dev.DriftLower1 TRS.Dev.DriftLower2 TRS.Dev.DriftBase

noncomputable section

namespace TRS.Dev.DriftLower3

/-- Per-sample loss under the cube prior around the drifting centre. -/
def pathLoss {s : RandomSeed} {T d B : ℕ} (hd : 2 ≤ d) (θ₀ : Vector d)
    (π : ReleasePolicy s T d B) (Δ η : ℝ) (L : ℤ)
    (ω : PriorSample s T d (Sset hd) Δ L) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 / 2 : ℝ) * ∑ i : Fin T,
    ‖deployed θ₀ π (priorTranscript (gpath hd T θ₀ Δ η) ω) i -
      (gpath hd T θ₀ Δ η i + embedBlock (Sset hd) (hiddenShift (Sset hd) Δ L ω.2.1))‖ ^ 2)

theorem prior_le_worst {s : RandomSeed} {T d B : ℕ} (hd : 2 ≤ d) (θ₀ : Vector d) (Δ η : ℝ)
    (hΔ : 0 < Δ) (hη : 0 ≤ η) (π : ReleasePolicy s T d B) (L : ℤ)
    (hH : ∀ u : PriorDraws (Sset hd) Δ L, ‖hiddenShift (Sset hd) Δ L u‖ < Δ / 32) :
    ∫⁻ ω, pathLoss hd θ₀ π Δ η L ω ∂(priorLaw s T d (Sset hd) Δ L) ≤
      driftWorstRisk θ₀ Δ η π := by
  have hmp := reshuffle_mp (uniformLevels (Sset hd) Δ L) s.law (gaussianRows T d)
  have h1 : ∫⁻ ω, pathLoss hd θ₀ π Δ η L ω ∂(priorLaw s T d (Sset hd) Δ L) =
      ∫⁻ p, pathLoss hd θ₀ π Δ η L (reshuffle _ _ _ p)
        ∂((uniformLevels (Sset hd) Δ L).prod (s.law.prod (gaussianRows T d))) := by
    have := hmp.lintegral_comp_emb (reshuffle _ _ _).measurableEmbedding
      (pathLoss hd θ₀ π Δ η L)
    unfold priorLaw
    exact this.symm
  rw [h1]
  refine (lintegral_prod_le _).trans ?_
  have h2 : ∀ u : PriorDraws (Sset hd) Δ L,
      ∫⁻ y, pathLoss hd θ₀ π Δ η L (reshuffle _ _ _ (u, y)) ∂(s.law.prod (gaussianRows T d)) ≤
        driftWorstRisk θ₀ Δ η π := by
    intro u
    have hmem := drift_mem hd T θ₀ Δ η hΔ hη (hiddenShift (Sset hd) Δ L u) (hH u).le
    refine le_trans (le_of_eq ?_) (le_iSup _ ⟨_, hmem⟩)
    unfold policyRisk pathLoss
    rfl
  calc ∫⁻ x, ∫⁻ y, pathLoss hd θ₀ π Δ η L (reshuffle _ _ _ (x, y)) ∂(s.law.prod (gaussianRows T d))
        ∂(uniformLevels (Sset hd) Δ L) ≤
        ∫⁻ x, driftWorstRisk θ₀ Δ η π ∂(uniformLevels (Sset hd) Δ L) := lintegral_mono h2
    _ = driftWorstRisk θ₀ Δ η π := by simp

/-- Lower bound version of the phase sum, with aggregated phase bounds. -/
lemma phase_sum_lower (T B : ℕ) (τ : Fin (B + 2) → ℕ) (hτ : IsSchedule T B τ)
    (g : ℕ → ℝ) (G : Fin (B + 1) → ℝ)
    (h : ∀ j : Fin (B + 1), G j ≤ ∑ i ∈ Finset.Ico (τ j.castSucc) (τ j.succ), g i) :
    ∑ j : Fin (B + 1), G j ≤ ∑ i ∈ Finset.range T, g i := by
  have ht := tt_mono T B τ hτ
  have t0 := tt_zero T B τ hτ
  have tB := tt_last T B τ hτ
  have tj := tt_cast T B τ
  have tj1 := tt_succ T B τ
  have hs := sum_Ico_phases' (tt T B τ) ht g (B + 1)
  rw [t0, tB] at hs
  rw [Finset.range_eq_Ico, hs, Finset.sum_range]
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [tj, tj1]
  exact h j

end TRS.Dev.DriftLower3
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement
open TRS.Dev.DriftLower1 TRS.Dev.DriftLower2 TRS.Dev.DriftLower3 TRS.Dev.DriftBase
open TRS.Dev.DriftUpper

noncomputable section

namespace TRS.Dev.DriftLower4

lemma coeff_lower (d : ℕ) (hd : 2 ≤ d) (Δ : ℝ) (hΔ : 0 < Δ) (n : ℝ) (hn : 0 ≤ n) :
    (2 : ℝ) ^ (-24 : ℤ) * ((d : ℝ) / max n ((d : ℝ) / Δ ^ 2)) ≤
      (2 : ℝ) ^ (-19 : ℤ) * ((d - 1 : ℕ) : ℝ) / max n (16 * ((d - 1 : ℕ) : ℝ) / Δ ^ 2) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [hd1]
  have hΔ2 : 0 < Δ ^ 2 := by positivity
  set m := max n ((d : ℝ) / Δ ^ 2) with hm
  have hm0 : 0 < m := lt_max_of_lt_right (by positivity)
  set M := max n (16 * ((d : ℝ) - 1) / Δ ^ 2) with hM
  have hM0 : 0 < M := lt_max_of_lt_right (by
    have : (0 : ℝ) < (d : ℝ) - 1 := by linarith
    positivity)
  have hMm : M ≤ 16 * m := by
    refine max_le ?_ ?_
    · have : n ≤ m := le_max_left _ _
      linarith
    · have h1 : (d : ℝ) / Δ ^ 2 ≤ m := le_max_right _ _
      have : 16 * ((d : ℝ) - 1) / Δ ^ 2 ≤ 16 * ((d : ℝ) / Δ ^ 2) := by
        rw [← mul_div_assoc]; gcongr; linarith
      linarith
  have e1 : (2 : ℝ) ^ (-24 : ℤ) = (2 : ℝ) ^ (-19 : ℤ) / 32 := by norm_num
  have h19 : (0 : ℝ) < (2 : ℝ) ^ (-19 : ℤ) := by positivity
  calc (2 : ℝ) ^ (-24 : ℤ) * ((d : ℝ) / m) = ((2 : ℝ) ^ (-19 : ℤ) * d) / (32 * m) := by
        rw [e1]; field_simp
    _ ≤ ((2 : ℝ) ^ (-19 : ℤ) * ((d : ℝ) - 1)) / M := by
        rw [div_le_div_iff₀ (by positivity) hM0]
        have a := mul_le_mul_of_nonneg_left hMm (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (-19 : ℤ) * d)
        have b : 0 ≤ (2 : ℝ) ^ (-19 : ℤ) * m * ((d : ℝ) - 2) := by
          have : (0 : ℝ) ≤ (d : ℝ) - 2 := by linarith
          positivity
        nlinarith [a, b]

end TRS.Dev.DriftLower4
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement
open TRS.Dev.DriftLower1 TRS.Dev.DriftLower2 TRS.Dev.DriftLower3 TRS.Dev.DriftLower4
open TRS.Dev.DriftBase TRS.Dev.DriftUpper

noncomputable section

namespace TRS.Dev.DriftLower5

/-- Constant predictor on a phase together with its estimation error. -/
lemma phase_pred {s : RandomSeed} {T d B : ℕ} (hd : 2 ≤ d) (θ₀ : Vector d) (Δ : ℝ) (hΔ : 0 < Δ)
    (π : ReleasePolicy s T d B) (X : Transcript s T d) (τ : Fin (B + 2) → ℕ)
    (hτ : IsSchedule T B τ) (hdate : ∀ k : Fin B, π.date k X = τ k.succ.castSucc)
    (H : BlockVector (Sset hd)) (hH : ‖H‖ < Δ / 32)
    (hG : ∀ j : Fin B, π.date j X < T →
      (2 : ℝ) ^ (-19 : ℤ) * (Sset hd).card / max (π.date j X : ℝ) (16 * (Sset hd).card / Δ ^ 2) ≤
      ‖blockProjection (Sset hd) (π.head j X) - gS hd θ₀ Δ - H‖ ^ 2)
    (j : Fin (B + 1)) (hne : τ j.castSucc < τ j.succ) :
    ∃ v : Vector d, (∀ t : Fin T, τ j.castSucc ≤ t.val → t.val < τ j.succ →
        deployed θ₀ π X t = v) ∧
      (2 : ℝ) ^ (-24 : ℤ) * ((d : ℝ) / clampedDate d Δ τ j) ≤
        ‖blockProjection (Sset hd) v - gS hd θ₀ Δ - H‖ ^ 2 := by
  have hmono : Monotone τ := hτ.2.2
  have hτT : τ j.succ ≤ T := by
    rw [← hτ.2.1]; exact hmono (by simp [Fin.le_def]; omega)
  have hallt : ∀ t : Fin T, τ j.castSucc ≤ t.val → t.val < τ j.succ →
      (j.val = 0 ∧ deployed θ₀ π X t = θ₀) ∨
      (∃ k : Fin B, k.val + 1 = j.val ∧ deployed θ₀ π X t = π.head k X ∧
        π.date k X = τ j.castSucc) :=
    fun t h1 h2 => deployed_phase_gen θ₀ π X τ hτ.1 hmono hdate j t h1 h2
  by_cases hj0 : j.val = 0
  · refine ⟨θ₀, fun t h1 h2 => ?_, ?_⟩
    · rcases hallt t h1 h2 with ⟨-, h⟩ | ⟨k, hk, -, -⟩
      · exact h
      · omega
    · have hcl : clampedDate d Δ τ j = (d : ℝ) / Δ ^ 2 := by
        unfold clampedDate; simp [hj0]
      have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
      have hdx : (d : ℝ) / clampedDate d Δ τ j = Δ ^ 2 := by rw [hcl]; field_simp
      rw [hdx]
      have := init_err hd θ₀ Δ hΔ H hH
      have h2 : (2 : ℝ) ^ (-24 : ℤ) = 1 / 16777216 := by norm_num
      rw [h2]
      nlinarith [sq_nonneg Δ]
  · let k : Fin B := ⟨j.val - 1, by have := j.isLt; omega⟩
    have hdk : π.date k X = τ j.castSucc := by
      rw [hdate]; congr 1; ext; simp [k]; omega
    refine ⟨π.head k X, fun t h1 h2 => ?_, ?_⟩
    · rcases hallt t h1 h2 with ⟨h, -⟩ | ⟨k', hk', hdep, -⟩
      · exact absurd h hj0
      · have : k' = k := by ext; simp [k]; omega
        rw [hdep, this]
    · have hlt : π.date k X < T := by rw [hdk]; omega
      have h1 := hG k hlt
      rw [hdk] at h1
      have hcl : clampedDate d Δ τ j = max ((τ j.castSucc : ℕ) : ℝ) ((d : ℝ) / Δ ^ 2) := by
        unfold clampedDate; simp only [hj0, if_false]; rfl
      rw [hcl, card_Sset hd] at *
      refine le_trans (coeff_lower d hd Δ hΔ _ (Nat.cast_nonneg _)) h1

end TRS.Dev.DriftLower5
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement
open TRS.Dev.DriftLower1 TRS.Dev.DriftLower2 TRS.Dev.DriftLower3 TRS.Dev.DriftLower4
open TRS.Dev.DriftLower5 TRS.Dev.DriftBase TRS.Dev.DriftUpper

noncomputable section

namespace TRS.Dev.DriftLower6

theorem pointwise_lower {s : RandomSeed} {T d B : ℕ} (hd : 2 ≤ d) (θ₀ : Vector d) (Δ η : ℝ)
    (hΔ : 0 < Δ) (hη : 0 ≤ η) (π : ReleasePolicy s T d B) (hπ : IsCausal π) (L : ℤ)
    (ω : PriorSample s T d (Sset hd) Δ L)
    (hH : ‖hiddenShift (Sset hd) Δ L ω.2.1‖ < Δ / 32)
    (hG : ∀ j : Fin B, π.date j (priorTranscript (gpath hd T θ₀ Δ η) ω) < T →
      (2 : ℝ) ^ (-19 : ℤ) * (Sset hd).card /
        max (π.date j (priorTranscript (gpath hd T θ₀ Δ η) ω) : ℝ)
          (16 * (Sset hd).card / Δ ^ 2) ≤
      ‖blockProjection (Sset hd) (π.head j (priorTranscript (gpath hd T θ₀ Δ η) ω)) -
        gS hd θ₀ Δ - hiddenShift (Sset hd) Δ L ω.2.1‖ ^ 2) :
    (2 : ℝ) ^ (-25 : ℤ) * driftProgram d Δ η
        (sched π (priorTranscript (gpath hd T θ₀ Δ η) ω)) - η ^ 2 * T / 24 ≤
      (1 / 2 : ℝ) * ∑ t : Fin T, ‖deployed θ₀ π (priorTranscript (gpath hd T θ₀ Δ η) ω) t -
        (gpath hd T θ₀ Δ η t + embedBlock (Sset hd) (hiddenShift (Sset hd) Δ L ω.2.1))‖ ^ 2 := by
  set X := priorTranscript (gpath hd T θ₀ Δ η) ω with hX
  set H := hiddenShift (Sset hd) Δ L ω.2.1 with hHdef
  set τ := sched π X with hτdef
  have hτ : IsSchedule T B τ := sched_isSchedule π hπ X
  have hmono : Monotone τ := hτ.2.2
  have hdate : ∀ k : Fin B, π.date k X = τ k.succ.castSucc := fun k => (sched_slot π X k).symm
  let g' : ℕ → ℝ := fun t => if h : t < T then
    ‖deployed θ₀ π X ⟨t, h⟩ - (gpath hd T θ₀ Δ η ⟨t, h⟩ + embedBlock (Sset hd) H)‖ ^ 2 else 0
  let G : Fin (B + 1) → ℝ := fun j =>
    phaseLength τ j * ((2 : ℝ) ^ (-24 : ℤ) * ((d : ℝ) / clampedDate d Δ τ j)) +
      η ^ 2 * phaseLength τ j * (phaseLength τ j ^ 2 - 1) / 12
  have hτT : ∀ j : Fin (B + 1), τ j.succ ≤ T := by
    intro j; rw [← hτ.2.1]; exact hmono (by simp [Fin.le_def]; omega)
  have hphase : ∀ j : Fin (B + 1),
      G j ≤ ∑ t ∈ Finset.Ico (τ j.castSucc) (τ j.succ), g' t := by
    intro j
    by_cases hne : τ j.castSucc < τ j.succ
    · obtain ⟨v, hv, hQ⟩ := phase_pred hd θ₀ Δ hΔ π X τ hτ hdate H hH hG j hne
      obtain ⟨Lm, hLm⟩ : ∃ Lm, τ j.succ = τ j.castSucc + Lm := ⟨_, (Nat.add_sub_cancel' hne.le).symm⟩
      have hphl : phaseLength τ j = (Lm : ℝ) := by
        unfold phaseLength; rw [hLm]; push_cast; ring
      set c : ℝ := v (i0 hd) - θ₀ (i0 hd) with hc
      set Q : ℝ := ‖blockProjection (Sset hd) v - gS hd θ₀ Δ - H‖ ^ 2 with hQdef
      have hterm : ∀ t ∈ Finset.Ico (τ j.castSucc) (τ j.succ),
          g' t = (c - η * (t : ℝ)) ^ 2 + Q := by
        intro t ht
        rw [Finset.mem_Ico] at ht
        have htT : t < T := lt_of_lt_of_le ht.2 (hτT j)
        simp only [g', dif_pos htT]
        rw [hv ⟨t, htT⟩ ht.1 ht.2, err_split hd T θ₀ Δ η v ⟨t, htT⟩ H]
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, hLm]
      have hq := quad_lower c η (τ j.castSucc) Lm
      rw [nsmul_eq_mul, Nat.add_sub_cancel_left]
      have hLm0 : (0 : ℝ) ≤ Lm := Nat.cast_nonneg Lm
      have h1 := mul_le_mul_of_nonneg_left hQ hLm0
      show phaseLength τ j * _ + _ ≤ _
      rw [hphl]
      nlinarith [h1, hq]
    · have heq : τ j.succ = τ j.castSucc := le_antisymm (not_lt.1 hne) (hmono (by simp [Fin.le_def]))
      have hphl : phaseLength τ j = 0 := by unfold phaseLength; rw [heq]; ring
      simp only [G, hphl]
      rw [Finset.Ico_eq_empty (by omega)]
      simp
  have hsum := phase_sum_lower T B τ hτ g' G hphase
  have hgsum : ∑ t ∈ Finset.range T, g' t = ∑ t : Fin T,
      ‖deployed θ₀ π X t - (gpath hd T θ₀ Δ η t + embedBlock (Sset hd) H)‖ ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range g' T]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    simp [g']
  rw [hgsum] at hsum
  -- arithmetic
  have hL : ∀ j : Fin (B + 1), 0 ≤ phaseLength τ j := by
    intro j
    unfold phaseLength
    have hle : τ j.castSucc ≤ τ j.succ := hmono (by simp [Fin.le_def])
    have : (τ j.castSucc : ℝ) ≤ τ j.succ := by exact_mod_cast hle
    linarith
  have hT := sum_phaseLength T B τ hτ
  have hterm2 : ∀ j : Fin (B + 1),
      (2 : ℝ) ^ (-25 : ℤ) * (phaseLength τ j * (d : ℝ) / clampedDate d Δ τ j +
        η ^ 2 * phaseLength τ j ^ 3) - η ^ 2 * phaseLength τ j / 24 ≤ (1 / 2 : ℝ) * G j := by
    intro j
    have h0 := hL j
    have e : (2 : ℝ) ^ (-25 : ℤ) = 1 / 33554432 := by norm_num
    have e2 : (2 : ℝ) ^ (-24 : ℤ) = 1 / 16777216 := by norm_num
    simp only [G]
    rw [e, e2]
    have h3 : 0 ≤ η ^ 2 * phaseLength τ j ^ 3 := by positivity
    have h4 : phaseLength τ j * (d : ℝ) / clampedDate d Δ τ j =
        phaseLength τ j * ((d : ℝ) / clampedDate d Δ τ j) := by ring
    rw [h4]
    nlinarith [h3]
  have hF : (2 : ℝ) ^ (-25 : ℤ) * driftProgram d Δ η τ - η ^ 2 * T / 24 ≤
      (1 / 2 : ℝ) * ∑ j : Fin (B + 1), G j := by
    have : (2 : ℝ) ^ (-25 : ℤ) * driftProgram d Δ η τ - η ^ 2 * T / 24 =
        ∑ j : Fin (B + 1), ((2 : ℝ) ^ (-25 : ℤ) * (phaseLength τ j * (d : ℝ) / clampedDate d Δ τ j +
          η ^ 2 * phaseLength τ j ^ 3) - η ^ 2 * phaseLength τ j / 24) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div, ← Finset.mul_sum, hT]
      unfold driftProgram
      rfl
    rw [this, Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => hterm2 j)
  linarith

end TRS.Dev.DriftLower6
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement
open TRS.Dev.DriftLower2 TRS.Dev.DriftBase TRS.Dev.DriftUpper

noncomputable section

namespace TRS.Dev.DriftLower7

lemma log16 : Real.log 16 = 4 * Real.log 2 := by
  have : (16 : ℝ) = 2 ^ 4 := by norm_num
  rw [this, Real.log_pow]; norm_num

lemma logTwo_eq (x : ℝ) : logTwo x = Real.logb 2 x := rfl

lemma firstLevel_ge4 (c : ℕ) (Δ : ℝ) (hc : 1 ≤ c) (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1) :
    4 ≤ firstLevel c Δ := by
  unfold firstLevel
  have h16 : (16 : ℝ) ≤ 16 * c / Δ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have : Δ ^ 2 ≤ 1 := by nlinarith
    have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
    nlinarith
  have h4 : (4 : ℝ) ≤ logTwo (16 * c / Δ ^ 2) := by
    unfold logTwo
    rw [le_div_iff₀ (Real.log_pos (by norm_num))]
    have := Real.log_le_log (by norm_num) h16
    rw [log16] at this; linarith
  calc (4 : ℤ) = ⌈(4 : ℝ)⌉ := by simp
    _ ≤ _ := Int.ceil_mono h4

lemma nlev_le (T c : ℕ) (Δ : ℝ) (hT8 : 8 ≤ T) (hc : 1 ≤ c) (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1) :
    (((max (firstLevel c Δ) ⌈Real.logb 2 (T : ℝ)⌉ - firstLevel c Δ + 1 : ℤ)) : ℝ) ≤
      Real.logb 2 (T : ℝ) := by
  have h4 := firstLevel_ge4 c Δ hc hΔ hΔ₁
  have h3 : (3 : ℝ) ≤ Real.logb 2 (T : ℝ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
    norm_num
    exact_mod_cast hT8
  rcases le_total (firstLevel c Δ) ⌈Real.logb 2 (T : ℝ)⌉ with h | h
  · rw [max_eq_right h]
    push_cast
    have h1 : (⌈Real.logb 2 (T : ℝ)⌉ : ℝ) < Real.logb 2 (T : ℝ) + 1 := Int.ceil_lt_add_one _
    have h2 : (4 : ℝ) ≤ (firstLevel c Δ : ℝ) := by exact_mod_cast h4
    linarith
  · rw [max_eq_left h]
    push_cast
    linarith

lemma pow_small (c : ℕ) (M : ℝ) (hM : 1 ≤ M) (h : 1 + logTwo M ≤ c) :
    (9 / 25 : ℝ) ^ c ≤ 1 / (2 * M) := by
  have hM0 : 0 < M := by linarith
  have h1 : (9 / 25 : ℝ) ^ c ≤ (1 / 2 : ℝ) ^ c := pow_le_pow_left₀ (by norm_num) (by norm_num) c
  have h2 : (1 / 2 : ℝ) ^ c = (1 / 2 : ℝ) ^ (c : ℝ) := (Real.rpow_natCast _ _).symm
  have h3 : (1 / 2 : ℝ) ^ (c : ℝ) ≤ (1 / 2 : ℝ) ^ (1 + Real.logb 2 M) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by rw [logTwo_eq] at h; exact h)
  have h4 : (1 / 2 : ℝ) ^ (1 + Real.logb 2 M) = 1 / (2 * M) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one, one_div, Real.inv_rpow (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) hM0]
    field_simp
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := h3
    _ = _ := h4


lemma union_numeric (T B d : ℕ) (hd : 2 ≤ d) (Δ : ℝ) (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1) (hT8 : 8 ≤ T)
    (hdim : 2 + logTwo (max 1 ((B : ℝ) * logTwo T)) ≤ (d : ℝ)) :
    (B : ℝ) * (((max (firstLevel (Sset hd).card Δ) ⌈Real.logb 2 (T : ℝ)⌉ -
        firstLevel (Sset hd).card Δ + 1 : ℤ) : ℝ)) * (9 / 25 : ℝ) ^ (Sset hd).card ≤ 1 / 2 := by
  set M : ℝ := max 1 ((B : ℝ) * logTwo T) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM0 : 0 < M := by linarith
  have hKM : (B : ℝ) * logTwo T ≤ M := le_max_right _ _
  have hlT : 0 ≤ logTwo T := by
    rw [logTwo_eq]
    exact Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ T))
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hcard := card_Sset hd
  have hc1 : 1 ≤ (Sset hd).card := by omega
  have h1 := nlev_le T (Sset hd).card Δ hT8 hc1 hΔ hΔ₁
  have h2 := pow_small (Sset hd).card M hM1 (by
    rw [hcard]
    have : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [this]; linarith)
  have h0 : 0 ≤ (9 / 25 : ℝ) ^ (Sset hd).card := by positivity
  rw [logTwo_eq] at hKM
  calc _ ≤ (B : ℝ) * Real.logb 2 (T : ℝ) * (9 / 25 : ℝ) ^ (Sset hd).card := by gcongr
    _ ≤ (B : ℝ) * Real.logb 2 (T : ℝ) * (1 / (2 * M)) := by gcongr
    _ ≤ M * (1 / (2 * M)) := by gcongr
    _ = 1 / 2 := by field_simp

lemma eta_sq_le (T d : ℕ) (hT : 8 ≤ T) (hd : 0 < d) (η : ℝ) (hη : 0 ≤ η)
    (hηT : η * T ≤ 1 / 4) (hdη : (d : ℝ) * η ≤ 1 / 8) : η ^ 2 ≤ trackingRate T d η := by
  unfold trackingRate
  have hT8 : (8 : ℝ) ≤ T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ T := by linarith
  refine le_min ?_ ?_
  · have hη1 : η ≤ 1 / 32 := by nlinarith [mul_le_mul_of_nonneg_left hT8 hη]
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have h3 : η ^ 3 ≤ (d : ℝ) * η := by
      have : η ^ 2 ≤ 1 := by nlinarith
      nlinarith [pow_nonneg hη 3, mul_nonneg hη hη]
    have e : (η ^ 3) ^ (2 / 3 : ℝ) = η ^ 2 := by
      rw [← Real.rpow_natCast η 3, ← Real.rpow_mul hη,
        show ((3 : ℕ) : ℝ) * (2 / 3) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [← e]
    exact Real.rpow_le_rpow (by positivity) h3 (by norm_num)
  · have : (1 : ℝ) ≤ (T : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (sq_nonneg η)]

end TRS.Dev.DriftLower7
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement
open TRS.Dev.DriftLower1 TRS.Dev.DriftLower2 TRS.Dev.DriftLower3 TRS.Dev.DriftLower6
open TRS.Dev.DriftLower7 TRS.Dev.DriftBase TRS.Dev.DriftUpper

noncomputable section

namespace TRS.Dev.DriftLower8

lemma convex_le_max (a b : ℝ) : (1 / 512 : ℝ) * a + (511 / 512 : ℝ) * b ≤ max a b := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

lemma optimum_le (T B d : ℕ) (Δ η : ℝ) (τ : Fin (B + 2) → ℕ) (hτ : IsSchedule T B τ) :
    driftOptimum T d B Δ η ≤ driftProgram d Δ η τ := by
  unfold driftOptimum scheduleMin
  exact csInf_le ((schedule_finite T B).image (driftProgram d Δ η)).bddBelow ⟨τ, hτ, rfl⟩

theorem worst_lower_F {s : RandomSeed} {T d B : ℕ} (hT : 8 ≤ T) (hd2 : 2 ≤ d) (θ₀ : Vector d)
    (Δ η : ℝ) (hΔ : 0 < Δ) (hΔ₂ : Δ ≤ 1 / 2) (hη : 0 ≤ η)
    (π : ReleasePolicy s T d B) (hπ : IsCausal π)
    (hdim : 2 + logTwo (max 1 ((B : ℝ) * logTwo T)) ≤ (d : ℝ)) :
    ENNReal.ofReal ((1 / 2 : ℝ) * ((2 : ℝ) ^ (-25 : ℤ) * driftOptimum T d B Δ η -
      η ^ 2 * T / 24)) ≤ driftWorstRisk θ₀ Δ η π := by
  classical
  have hT0 : 0 < T := by omega
  have hd0 : 0 < d := by omega
  set S := Sset hd2 with hSdef
  have hcard : S.card = d - 1 := card_Sset hd2
  have hS : 0 < S.card := by omega
  set L : ℤ := max (firstLevel S.card Δ) ⌈Real.logb 2 (T : ℝ)⌉ with hLdef
  have hL : firstLevel S.card Δ ≤ L := le_max_left _ _
  have hLT : (T : ℝ) ≤ (2 : ℝ) ^ L :=
    le_trans (le_zpow_ceil T (by exact_mod_cast hT0))
      (zpow_le_zpow_right₀ (by norm_num) (le_max_right _ _))
  have key := common_lower_error_event T d hT0 hd0 S hS Δ hΔ (by linarith) L hL hLT
    (gpath hd2 T θ₀ Δ η) (gS hd2 θ₀ Δ) (fun i => blockProj_gpath hd2 T θ₀ Δ η i) s
  obtain ⟨hH, -, hc⟩ := key
  refine le_trans ?_ (prior_le_worst hd2 θ₀ Δ η hΔ hη π L hH)
  obtain ⟨E, hEm, hEμ, hE⟩ := hc B π hπ
  have hU := union_numeric T B d hd2 Δ hΔ (by linarith) hT hdim
  have hEμ' : ENNReal.ofReal (1 / 2) ≤ priorLaw s T d S Δ L E := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hEμ
    linarith
  set a : ℝ := (2 : ℝ) ^ (-25 : ℤ) * driftOptimum T d B Δ η - η ^ 2 * T / 24 with ha
  have hpath : ∀ ω ∈ E, ENNReal.ofReal a ≤ pathLoss hd2 θ₀ π Δ η L ω := by
    intro ω hω
    unfold pathLoss
    apply ENNReal.ofReal_le_ofReal
    have hp := DriftLower6.pointwise_lower hd2 θ₀ Δ η hΔ hη π hπ L ω (hH ω.2.1)
      (fun j hj => hE ω hω j hj)
    have hopt := optimum_le T B d Δ η _ (sched_isSchedule π hπ (priorTranscript (gpath hd2 T θ₀ Δ η) ω))
    have : (2 : ℝ) ^ (-25 : ℤ) * driftOptimum T d B Δ η ≤
        (2 : ℝ) ^ (-25 : ℤ) * driftProgram d Δ η
          (sched π (priorTranscript (gpath hd2 T θ₀ Δ η) ω)) := by gcongr
    linarith
  calc ENNReal.ofReal ((1 / 2 : ℝ) * a)
      = ENNReal.ofReal (1 / 2) * ENNReal.ofReal a := ENNReal.ofReal_mul (by norm_num)
    _ = ENNReal.ofReal a * ENNReal.ofReal (1 / 2) := mul_comm _ _
    _ ≤ ENNReal.ofReal a * priorLaw s T d S Δ L E := by gcongr
    _ = ∫⁻ ω, E.indicator (fun _ => ENNReal.ofReal a) ω ∂(priorLaw s T d S Δ L) :=
        (lintegral_indicator_const hEm _).symm
    _ ≤ _ := by
        refine lintegral_mono fun ω => ?_
        by_cases hω : ω ∈ E
        · rw [Set.indicator_of_mem hω]; exact hpath ω hω
        · rw [Set.indicator_of_notMem hω]; exact zero_le

lemma worst_mono (T d B : ℕ) (θ₀ : Vector d) (Δ η : ℝ) (hΔ : 0 ≤ Δ) {s : RandomSeed}
    (π : ReleasePolicy s T d B) :
    driftWorstRisk θ₀ 0 η π ≤ driftWorstRisk θ₀ Δ η π := by
  unfold driftWorstRisk
  apply iSup_le
  rintro ⟨θ, hθ⟩
  have hmem : θ ∈ driftClass (T := T) θ₀ Δ η :=
    ⟨fun i hi => (hθ.1 i hi).trans hΔ, hθ.2⟩
  exact le_iSup (fun θ : (driftClass (T := T) θ₀ Δ η : Set (Fin T → Vector d)) =>
    policyRisk θ₀ π θ.val) ⟨θ, hmem⟩

theorem lower_part (T d B : ℕ) (hT : 8 ≤ T) (hd : 0 < d) (Δ η : ℝ) (hΔ : 0 < Δ)
    (hΔ₂ : Δ ≤ 1 / 2) (hη : 0 ≤ η) (hηT : η * T ≤ 1 / 4) (hdη : (d : ℝ) * η ≤ 1 / 8)
    (θ₀ : Vector d)
    (hdim : 2 + logTwo (max 1 ((B : ℝ) * logTwo T)) ≤ (d : ℝ)) :
    ENNReal.ofReal ((2 : ℝ) ^ (-35 : ℤ) *
          (driftOptimum T d B Δ η + T * trackingRate T d η)) ≤
        driftMinimaxRisk T d B θ₀ Δ η := by
  have hd2 : 2 ≤ d := by
    have h0 : 0 ≤ logTwo (max 1 ((B : ℝ) * logTwo T)) := by
      rw [logTwo_eq]
      exact Real.logb_nonneg (by norm_num) (le_max_left _ _)
    have : (2 : ℝ) ≤ d := by linarith
    exact_mod_cast this
  unfold driftMinimaxRisk
  apply le_sInf
  rintro v ⟨s, π, hπ, rfl⟩
  have h1 := worst_lower_F (θ₀ := θ₀) hT hd2 Δ η hΔ hΔ₂ hη π hπ hdim
  have h2 := (tracking_floor T d hT hd η hη hηT hdη θ₀ B s π hπ).trans
    (worst_mono T d B θ₀ Δ η hΔ.le π)
  have hφ := trackingRate_nonneg T d η hη
  have hη2 := eta_sq_le T d hT hd η hη hηT hdη
  set F := driftOptimum T d B Δ η
  set φ := trackingRate T d η
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hTφ : 0 ≤ (T : ℝ) * φ := mul_nonneg hT0 hφ
  have hηT2 : η ^ 2 * T ≤ φ * T := mul_le_mul_of_nonneg_right hη2 hT0
  set a' : ℝ := (1 / 2 : ℝ) * ((2 : ℝ) ^ (-25 : ℤ) * F - η ^ 2 * T / 24) with ha'
  set b : ℝ := (2 : ℝ) ^ (-13 : ℤ) * T * φ with hb
  have e25 : (2 : ℝ) ^ (-25 : ℤ) = 1 / 33554432 := by norm_num
  have e13 : (2 : ℝ) ^ (-13 : ℤ) = 1 / 8192 := by norm_num
  have e35 : (2 : ℝ) ^ (-35 : ℤ) = 1 / 34359738368 := by norm_num
  have hcomb : (2 : ℝ) ^ (-35 : ℤ) * (F + T * φ) ≤ max a' b := by
    have : (2 : ℝ) ^ (-35 : ℤ) * (F + T * φ) ≤ (1 / 512) * a' + (511 / 512) * b := by
      rw [ha', hb, e25, e13, e35]
      nlinarith [hTφ, hηT2]
    exact this.trans (convex_le_max a' b)
  rcases le_total a' b with h | h
  · rw [max_eq_right h] at hcomb
    exact (ENNReal.ofReal_le_ofReal hcomb).trans h2
  · rw [max_eq_left h] at hcomb
    exact (ENNReal.ofReal_le_ofReal hcomb).trans h1

end TRS.Dev.DriftLower8
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary
open TightReleaseSchedules.Stationary.Supplement

/-!
# q382 gradual_drift_release_schedules -- plan with explicit constants (written BEFORE the Lean)

Truth check (done by hand, no counterexample): with y = (d/eta^2)^(1/3) >= 4 (d*eta <= 1/8), p = (d eta)^(2/3) = eta^2 y^2,
w0 = ceil y <= 2y, phi = min(p, eta^2 T^2), and a release at date n (1 <= n < T), window w = min(n, w0):
* targets of the window: ||theta_i - theta0|| <= Delta + eta*i <= Delta + eta*n =: R  (<= 3/4 <= 1), so the projection ball contains
  the window path average; Lemma 3.3 (anchored_cross_moments, clause 2): E||Pi Z - bar||^2 <= min((2d+1)/w, 4R^2) <= min(3d/w, 4R^2).
* bias ||bar - theta_{n-1}|| <= eta (w-1)/2 <= eta w/2, staleness ||theta_{n-1} - theta_i|| <= eta (i-n+1) <= eta L (L = phase length).
* squared triangle: half-error <= (3/2)(min(3d/w,4R^2) + eta^2 w^2/4 + eta^2 L^2).
* NUMERIC LEMMA: min(3d/w,4R^2) + eta^2 w^2/4 <= 8 d/x + 33 phi, x = max(n, d/Delta^2) [case w=n: min(3d/n,4(D+en)^2) <= 8min(d/n,D^2)+8e^2n^2,
  e^2 n^2 <= 4 phi => 8.25*4 = 33; case n > w0: <= 4p = 4 phi].
* phase j with release date tau_j >= 1 (< T): per-round half error <= 12 d/x_j + 49.5 phi + 1.5 eta^2 L_j^2; summed over the L_j rounds:
  12 L_j d/x_j + 49.5 L_j phi + 1.5 eta^2 L_j^3.  Phase with date 0 (theta0 served): half error <= Delta^2 + eta^2 L^2 = d/x_j + eta^2 L^2.
  Sum_j L_j = T gives risk(tau) <= 12 F(tau) + 49.5 T phi <= 12 F*_B + 50 T phi for F-minimizing tau (a),(b); (a) via a minimizer (finite set).
* LOWER BOUND (c): d >= 2. S = coordinates != 0, d_h = d-1. Path g_i = theta0 + eta i e0 + (Delta/2) e1, theta = g + H.  Lemma 4.2
  (common_lower_error_event) with L = max(firstLevel, ceil log2 T): #levels N <= log2 T, event E with Pr >= 1 - B N (9/25)^(d-1) >= 1/2.
  On E every release at tau_j < T has ||P_S head - g_S - H||^2 >= 2^-19 d_h/max(tau_j,16 d_h/Delta^2) >= 2^-24 d/x_j; theta0: >= Delta^2/8 >= 2^-24 Delta^2.
  Coordinate 0 on a phase: sum (c - eta t)^2 >= eta^2 L(L^2-1)/12.  Realized-schedule loss >= 2^-25 F(tau~) - eta^2 T/24 >= 2^-25 F* - T phi/24
  (eta^2 <= phi).  Averaging over the prior: worstRisk >= 2^-26 F* - T phi/48; tracking_floor (Delta=0 class subset of Delta class): >= 2^-13 T phi.
  Convex combination weights 2^-9, 1-2^-9: >= 2^-35 F* + 2^-14 T phi >= 2^-35 (F* + T phi).
-/


theorem TRS.chk_gradual_drift_release_schedules (T d B : ℕ) (hT : 8 ≤ T) (hd : 0 < d)
    (Δ η : ℝ) (hΔ : 0 < Δ) (hΔ₂ : Δ ≤ 1 / 2) (hη : 0 ≤ η)
    (hηT : η * T ≤ 1 / 4) (hdη : (d : ℝ) * η ≤ 1 / 8) (θ₀ : Vector d) :
    driftMinimaxRisk T d B θ₀ Δ η ≤
      ENNReal.ofReal (12 * driftOptimum T d B Δ η + 50 * T * trackingRate T d η) ∧
    (∀ τ : Fin (B + 2) → ℕ, IsSchedule T B τ → driftProgram d Δ η τ = driftOptimum T d B Δ η →
      IsCausal (windowedPolicy T d B θ₀ Δ η τ) ∧
      HasDeterministicDates (windowedPolicy T d B θ₀ Δ η τ) ∧
      driftWorstRisk θ₀ Δ η (windowedPolicy T d B θ₀ Δ η τ) ≤
        ENNReal.ofReal (12 * driftOptimum T d B Δ η + 50 * T * trackingRate T d η)) ∧
    (2 + logTwo (max 1 ((B : ℝ) * logTwo T)) ≤ (d : ℝ) →
      ENNReal.ofReal ((2 : ℝ) ^ (-35 : ℤ) *
          (driftOptimum T d B Δ η + T * trackingRate T d η)) ≤
        driftMinimaxRisk T d B θ₀ Δ η) := by
  have hΔ' : (0 : ℝ) < Δ := hΔ
  have hu := TRS.Dev.DriftUpper3.upper_parts T d B hd θ₀ Δ η hΔ hΔ₂ hη hηT hdη
  exact ⟨hu.1, hu.2, fun hdim =>
    TRS.Dev.DriftLower8.lower_part T d B hT hd Δ η hΔ hΔ₂ hη hηT hdη θ₀ hdim⟩
end

theorem solution : type_of% @TRS.chk_gradual_drift_release_schedules := @TRS.chk_gradual_drift_release_schedules
