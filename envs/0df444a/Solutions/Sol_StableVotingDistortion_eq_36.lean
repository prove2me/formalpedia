-- Prove2me | solution 1 for StableVotingDistortion.eq_36
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T12:00:18.459923+00:00
-- url     : https://prove2.me/submissions/a471bffc-771c-4d9f-b889-fe4667b006d3

import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_IsScoreFunction
import Definitions.Def_StableVotingDistortion_activation
import Definitions.Def_StableVotingDistortion_scorePrimitives
import Definitions.Def_StableVotingDistortion_slices
import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Pi

-- Source module OptimalG.Finite
section
set_option autoImplicit true
/-!
# Finite algebra and the forward metric reduction

This module proves the finite weighted-average implication in Lemma 2.2 and
(the upper-bound direction of) Lemma 2.4 of the supplied manuscript. It does not
assert existence of a stable lottery or derive the rank-integral partition
identity. The latter is an explicit premise of `stationarity`.
-/

namespace OptimalG

open scoped BigOperators

/-- Expectation with respect to a finite real weight vector. -/
def expectation {I : Type*} [Fintype I] (w f : I → ℝ) : ℝ :=
  ∑ i, w i * f i

theorem expectation_mono {I : Type*} [Fintype I]
    {w f g : I → ℝ} (hw : ∀ i, 0 ≤ w i) (hfg : ∀ i, f i ≤ g i) :
    expectation w f ≤ expectation w g := by
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hfg i) (hw i))

theorem expectation_add {I : Type*} [Fintype I] (w f g : I → ℝ) :
    expectation w (fun i => f i + g i) = expectation w f + expectation w g := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_smul {I : Type*} [Fintype I] (w f : I → ℝ) (c : ℝ) :
    expectation w (fun i => c * f i) = c * expectation w f := by
  simp [expectation, ← Finset.mul_sum, mul_left_comm]

theorem expectation_const {I : Type*} [Fintype I] {w : I → ℝ}
    (hw : ∑ i, w i = 1) (c : ℝ) : expectation w (fun _ => c) = c := by
  simp [expectation, ← Finset.sum_mul, hw]

/-- The finite weighted-average argument of Lemma 2.2. The rank-integral
partition identity is represented by `hmean`, not silently assumed as an axiom. -/
theorem stationarity {C : Type*} [Fintype C]
    (D activation : C → ℝ) (τ : ℝ)
    (hD : ∀ a, 0 ≤ D a) (hsum : ∑ a, D a = 1)
    (hstable : ∀ a, activation a ≤ τ)
    (hmean : expectation D activation = τ)
    (a : C) (ha : 0 < D a) : activation a = τ := by
  have hzero : ∑ b, D b * (τ - activation b) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    simpa [expectation, hsum] using congrArg (fun x : ℝ => τ - x) hmean
  have hnonneg : ∀ b, 0 ≤ D b * (τ - activation b) :=
    fun b => mul_nonneg (hD b) (sub_nonneg.mpr (hstable b))
  have hle : D a * (τ - activation a) ≤ 0 := by
    calc
      D a * (τ - activation a) ≤ ∑ b, D b * (τ - activation b) :=
        Finset.single_le_sum (fun b _ => hnonneg b) (Finset.mem_univ a)
      _ = 0 := hzero
  have hz : D a * (τ - activation a) = 0 := le_antisymm hle (hnonneg a)
  rcases mul_eq_zero.mp hz with h | h
  · exact False.elim (ne_of_gt ha h)
  · linarith

/-- Interchanging two finite weighted expectations needs no analytic theorem. -/
theorem expectation_commute {V C : Type*} [Fintype V] [Fintype C]
    (w : V → ℝ) (D : C → ℝ) (f : V → C → ℝ) :
    expectation D (fun a => expectation w (fun v => f v a)) =
      expectation w (fun v => expectation D (f v)) := by
  simp only [expectation, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Stationarity from the per-voter rank-partition identity. This spells out
both finite expectations appearing in Lemma 2.2. -/
theorem stationarity_of_partition_identity {V C : Type*} [Fintype V] [Fintype C]
    (w : V → ℝ) (D : C → ℝ) (activation : V → C → ℝ) (τ : ℝ)
    (hD : ∀ a, 0 ≤ D a) (hDsum : ∑ a, D a = 1)
    (hwsum : ∑ v, w v = 1)
    (hpartition : ∀ v, expectation D (activation v) = τ)
    (hstable : ∀ a, expectation w (fun v => activation v a) ≤ τ)
    (a : C) (ha : 0 < D a) :
    expectation w (fun v => activation v a) = τ := by
  apply stationarity D (fun b => expectation w (fun v => activation v b)) τ hD hDsum hstable
  · rw [expectation_commute]
    simp_rw [hpartition]
    exact expectation_const hwsum τ
  · exact ha

/-- Running minimum of candidate heights along a finite rank order. Ranks
increase from worst to best, as in Definition 2.3. The default branch equals
`ρ b`, which is itself in the lower set because `rank b ≤ rank b`. -/
noncomputable def runningMin {C : Type*} [Fintype C] [Nonempty C]
    (rank : C → ℕ) (ρ : C → ℝ) (b : C) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun c => if rank c ≤ rank b then ρ c else ρ b)

/-- Maximum drop above the running minimum, including candidates of mass zero. -/
noncomputable def maximumGap {C : Type*} [Fintype C] [Nonempty C]
    (rank : C → ℕ) (ρ : C → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun b => ρ b - runningMin rank ρ b)

/-- Consistency and the triangle inequality imply the first pointwise bound
preceding Lemma 2.4. No injectivity of candidate locations is required. -/
theorem distance_sub_le_runningMin {C X : Type*} [Fintype C] [Nonempty C]
    [PseudoMetricSpace X] (candidate : C → X) (v : X) (a : C)
    (rank : C → ℕ)
    (hconsistent : ∀ b c, rank c ≤ rank b → dist v (candidate b) ≤ dist v (candidate c))
    (b : C) :
    dist v (candidate b) - dist v (candidate a) ≤
      runningMin rank (fun c => dist (candidate a) (candidate c)) b := by
  apply Finset.le_inf'
  intro c _
  dsimp
  split_ifs with h
  · have h1 := hconsistent b c h
    have h2 := dist_triangle v (candidate a) (candidate c)
    linarith
  · have h2 := dist_triangle v (candidate a) (candidate b)
    linarith

/-- Consistency and the triangle inequality bound every drop by twice the
voter's distance from the reference candidate. -/
theorem maximumGap_le_twice_distance {C X : Type*} [Fintype C] [Nonempty C]
    [PseudoMetricSpace X] (candidate : C → X) (v : X) (a : C)
    (rank : C → ℕ)
    (hconsistent : ∀ b c, rank c ≤ rank b → dist v (candidate b) ≤ dist v (candidate c)) :
    maximumGap rank (fun c => dist (candidate a) (candidate c)) ≤
      2 * dist v (candidate a) := by
  apply Finset.sup'_le
  intro b _
  have hlow : dist (candidate a) (candidate b) - 2 * dist v (candidate a) ≤
      runningMin rank (fun c => dist (candidate a) (candidate c)) b := by
    apply Finset.le_inf'
    intro c _
    dsimp
    split_ifs with h
    · have h1 := hconsistent b c h
      have h2 := dist_triangle (candidate a) v (candidate b)
      have h3 := dist_triangle v (candidate a) (candidate c)
      rw [dist_comm (candidate a) v] at h2
      linarith
    · have hd := dist_nonneg (x := v) (y := candidate a)
      linarith
  linarith

/-- Finite weighted upper-bound direction of Lemma 2.4. The final hypothesis
is precisely the running-minimum inequality that Sections 4--5 seek to prove.
All other bounds here are derived from actual pseudometric and preference data. -/
theorem metric_distortion_upper_bound
    {V C X : Type*} [Fintype V] [Fintype C] [Nonempty C]
    [PseudoMetricSpace X]
    (voter : V → X) (candidate : C → X) (rank : V → C → ℕ)
    (w : V → ℝ) (D : C → ℝ) (a : C) (lam : ℝ)
    (hw : ∀ v, 0 ≤ w v) (hD : ∀ b, 0 ≤ D b) (hDsum : ∑ b, D b = 1)
    (hlam : 0 ≤ lam)
    (hconsistent : ∀ v b c, rank v c ≤ rank v b →
      dist (voter v) (candidate b) ≤ dist (voter v) (candidate c))
    (hcertificate :
      expectation w (fun v => expectation D
        (runningMin (rank v) (fun c => dist (candidate a) (candidate c)))) ≤
      lam * expectation w (fun v => maximumGap (rank v)
        (fun c => dist (candidate a) (candidate c)))) :
    expectation w (fun v => expectation D (fun b => dist (voter v) (candidate b))) ≤
      (1 + 2 * lam) * expectation w (fun v => dist (voter v) (candidate a)) := by
  let base : V → ℝ := fun v => dist (voter v) (candidate a)
  let N : V → ℝ := fun v => expectation D
    (runningMin (rank v) (fun c => dist (candidate a) (candidate c)))
  let Δ : V → ℝ := fun v => maximumGap (rank v)
    (fun c => dist (candidate a) (candidate c))
  have hv : ∀ v, expectation D (fun b => dist (voter v) (candidate b)) ≤ base v + N v := by
    intro v
    calc
      expectation D (fun b => dist (voter v) (candidate b)) ≤
          expectation D (fun b => base v +
            runningMin (rank v) (fun c => dist (candidate a) (candidate c)) b) := by
        apply expectation_mono hD
        intro b
        have h := distance_sub_le_runningMin candidate (voter v) a (rank v) (hconsistent v) b
        dsimp [base]
        linarith
      _ = base v + N v := by
        rw [expectation_add, expectation_const hDsum]
  have hcost := expectation_mono hw hv
  rw [expectation_add] at hcost
  have hgap : expectation w Δ ≤ 2 * expectation w base := by
    calc
      expectation w Δ ≤ expectation w (fun v => 2 * base v) := by
        apply expectation_mono hw
        intro v
        exact maximumGap_le_twice_distance candidate (voter v) a (rank v) (hconsistent v)
      _ = 2 * expectation w base := expectation_smul w base 2
  have hcert : expectation w N ≤ lam * expectation w Δ := hcertificate
  have hscaled := mul_le_mul_of_nonneg_left hgap hlam
  dsimp [base] at hcost hscaled
  nlinarith

/-- Positive-denominator form of `metric_distortion_upper_bound`. -/
theorem ratio_le_of_cost_bound {cost optimum lam : ℝ}
    (hopt : 0 < optimum) (hcost : cost ≤ (1 + 2 * lam) * optimum) :
    cost / optimum ≤ 1 + 2 * lam :=
  (div_le_iff₀ hopt).mpr hcost

end OptimalG
end

-- Source module OptimalG.RankIntegral
section
set_option autoImplicit true
/-!
# The rank-line partition and stationarity

Candidates are indexed from worst to best by `Fin n`. For elections with
arbitrary candidate labels, each voter supplies an equivalence `Fin n ≃ C`.
Zero-mass candidates are included and use exactly the integral definition of
activation from Definition 2.1, without dividing by their mass.
-/

namespace OptimalG

open Set MeasureTheory
open scoped BigOperators

/-- Total lottery mass strictly before the `k`th candidate. -/
noncomputable def rankCut {n : ℕ} (D : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i, if i.val < k then D i else 0

@[simp] theorem rankCut_zero {n : ℕ} (D : Fin n → ℝ) : rankCut D 0 = 0 := by
  simp [rankCut]

theorem rankCut_end {n : ℕ} (D : Fin n → ℝ) (hsum : ∑ i, D i = 1) :
    rankCut D n = 1 := by
  simpa [rankCut] using hsum

theorem rankCut_mem_Icc {n : ℕ} (D : Fin n → ℝ)
    (hD : ∀ i, 0 ≤ D i) (hsum : ∑ i, D i = 1) (k : ℕ) :
    rankCut D k ∈ Icc 0 1 := by
  constructor
  · apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact hD i
    · rfl
  · calc
      rankCut D k ≤ ∑ i, D i := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs
        · rfl
        · exact hD i
      _ = 1 := hsum

theorem rankCut_mono {n : ℕ} (D : Fin n → ℝ) (hD : ∀ i, 0 ≤ D i) :
    Monotone (rankCut D) := by
  intro j k hjk
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hij hik hik
  · rfl
  · omega
  · exact hD i
  · rfl

theorem rankCut_succ {n : ℕ} (D : Fin n → ℝ) (i : Fin n) :
    rankCut D (i.val + 1) = rankCut D i.val + D i := by
  have step : ∀ j : Fin n,
      (if j.val < i.val + 1 then D j else 0) =
      (if j.val < i.val then D j else 0) + (if j = i then D j else 0) := by
    intro j
    by_cases hji : j = i
    · subst j
      simp
    · have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
      by_cases hlt : j.val < i.val
      · simp [hji, hlt, show j.val < i.val + 1 by omega]
      · simp [hji, hlt, show ¬ j.val < i.val + 1 by omega]
  simp_rw [rankCut, step, Finset.sum_add_distrib]
  simp

/-- The exact copy-averaged activation in Definition 2.1. -/
noncomputable def rankActivation {n : ℕ} (g : ℝ → ℝ) (D : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  ∫ u in (0 : ℝ)..1, g (rankCut D i.val + u * D i)

/-- Affine change of variables, including the zero-width case. -/
theorem mass_mul_rankActivation {n : ℕ} (g : ℝ → ℝ) (D : Fin n → ℝ)
    (i : Fin n) :
    D i * rankActivation g D i = ∫ r in rankCut D i.val..rankCut D (i.val + 1), g r := by
  rw [rankCut_succ]
  simpa [rankActivation, smul_eq_mul, mul_comm] using
    (intervalIntegral.smul_integral_comp_add_mul (a := (0 : ℝ)) (b := 1)
      g (D i) (rankCut D i.val))

/-- A zero-mass candidate receives the activation at its rank. -/
theorem rankActivation_of_mass_zero {n : ℕ} (g : ℝ → ℝ) (D : Fin n → ℝ)
    (i : Fin n) (hi : D i = 0) : rankActivation g D i = g (rankCut D i.val) := by
  simp [rankActivation, hi]

/-- The rank intervals form an integral partition of `[0,1]`. -/
theorem rank_integral_partition {n : ℕ} (g : ℝ → ℝ) (D : Fin n → ℝ)
    (hcont : ContinuousOn g (Icc 0 1))
    (hD : ∀ i, 0 ≤ D i) (hsum : ∑ i, D i = 1) :
    expectation D (rankActivation g D) = ∫ r in (0 : ℝ)..1, g r := by
  have hint : ∀ k < n, IntervalIntegrable g volume (rankCut D k) (rankCut D (k + 1)) := by
    intro k _
    have hleft := rankCut_mem_Icc D hD hsum k
    have hright := rankCut_mem_Icc D hD hsum (k + 1)
    apply ContinuousOn.intervalIntegrable_of_Icc (rankCut_mono D hD (Nat.le_succ k))
    apply hcont.mono
    intro r hr
    exact ⟨le_trans hleft.1 hr.1, le_trans hr.2 hright.2⟩
  have hsumint := intervalIntegral.sum_integral_adjacent_intervals hint
  rw [Finset.sum_range] at hsumint
  simpa only [expectation, mass_mul_rankActivation, rankCut_zero, rankCut_end D hsum]
    using hsumint

/-- Activation with candidate labels and a voter-specific order. The equivalence
lists candidates from worst to best. -/
noncomputable def orderedActivation {C : Type*} {n : ℕ}
    (g : ℝ → ℝ) (D : C → ℝ) (order : Fin n ≃ C) (a : C) : ℝ :=
  rankActivation g (fun i => D (order i)) (order.symm a)

/-- The partition identity is invariant under the candidate labeling. -/
theorem ordered_integral_partition {C : Type*} [Fintype C] {n : ℕ}
    (g : ℝ → ℝ) (D : C → ℝ) (order : Fin n ≃ C)
    (hcont : ContinuousOn g (Icc 0 1))
    (hD : ∀ a, 0 ≤ D a) (hsum : ∑ a, D a = 1) :
    expectation D (orderedActivation g D order) = ∫ r in (0 : ℝ)..1, g r := by
  have hsum' : ∑ i, D (order i) = 1 := by
    simpa only [Equiv.sum_comp] using hsum
  have hpart := rank_integral_partition g (fun i => D (order i)) hcont
    (fun i => hD (order i)) hsum'
  simpa [expectation, orderedActivation, ← Equiv.sum_comp order]
    using hpart

/-- Supported stationarity in Lemma 2.2, now with the actual rank-integral
partition proved rather than supplied as a hypothesis. -/
theorem supported_stationarity {V C : Type*} [Fintype V] [Fintype C] {n : ℕ}
    (g : ℝ → ℝ) (D : C → ℝ) (w : V → ℝ) (order : V → Fin n ≃ C)
    (hcont : ContinuousOn g (Icc 0 1))
    (hD : ∀ a, 0 ≤ D a) (hDsum : ∑ a, D a = 1)
    (hwsum : ∑ v, w v = 1)
    (hstable : ∀ a, expectation w (fun v => orderedActivation g D (order v) a) ≤
      ∫ r in (0 : ℝ)..1, g r)
    (a : C) (ha : 0 < D a) :
    expectation w (fun v => orderedActivation g D (order v) a) =
      ∫ r in (0 : ℝ)..1, g r := by
  exact stationarity_of_partition_identity w D (fun v => orderedActivation g D (order v))
    (∫ r in (0 : ℝ)..1, g r) hD hDsum hwsum
    (fun v => ordered_integral_partition g D (order v) hcont hD hDsum) hstable a ha

end OptimalG
end

-- Source module OptimalG.Packing
section
set_option autoImplicit true
/-!
# Packing a prescribed mass against the right endpoint

This proves the one-dimensional rearrangement inequality used in (5.8).
It applies to arbitrary integrable fractional occupation functions, not just
unions of candidate intervals. Finite rank intervals will supply the occupation.
-/

namespace OptimalG

open MeasureTheory Set
open scoped Interval

theorem intervalIntegrable_on_subinterval {f : ℝ → ℝ} {a b c d : ℝ}
    (hf : IntervalIntegrable f volume a b) (hab : a ≤ b)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    IntervalIntegrable f volume c d := by
  apply hf.mono_set
  rw [uIcc_of_le hcd, uIcc_of_le hab]
  exact Icc_subset_Icc hac hdb

/-- Among occupations in `[0,1]` of mass `b-c`, an increasing score has largest
integral when that occupation fills `[c,b]`. -/
theorem pack_right (f w : ℝ → ℝ) (a c b : ℝ)
    (hac : a ≤ c) (hcb : c ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hmono : MonotoneOn f (Icc a b))
    (hw : IntervalIntegrable w volume a b)
    (hwb : ∀ x ∈ Icc a b, 0 ≤ w x ∧ w x ≤ 1)
    (hmass : (∫ x in a..b, w x) = b - c) :
    (∫ x in a..b, w x * f x) ≤ ∫ x in c..b, f x := by
  have hab : a ≤ b := le_trans hac hcb
  have hcc : c ∈ Icc a b := ⟨hac, hcb⟩
  have hfu : ContinuousOn f (uIcc a b) := by simpa [uIcc_of_le hab] using hf
  have hfw : IntervalIntegrable (fun x => w x * f x) volume a b :=
    hw.mul_continuousOn hfu
  have hfbar : IntervalIntegrable (fun x => f x - f c) volume a b :=
    (hf.sub continuousOn_const).intervalIntegrable_of_Icc hab
  have hwbar : IntervalIntegrable (fun x => w x * (f x - f c)) volume a b :=
    hw.mul_continuousOn (hfu.sub continuousOn_const)
  have hwbarLeft := intervalIntegrable_on_subinterval hwbar hab le_rfl hac hcb
  have hwbarRight := intervalIntegrable_on_subinterval hwbar hab hac hcb le_rfl
  have hfbarRight := intervalIntegrable_on_subinterval hfbar hab hac hcb le_rfl
  have hleft : (∫ x in a..c, w x * (f x - f c)) ≤ 0 := by
    have hh := intervalIntegral.integral_mono_on hac hwbarLeft
      (intervalIntegrable_const (c := (0 : ℝ))) (fun x hx => ?_)
    · simpa using hh
    · have hxab : x ∈ Icc a b := ⟨hx.1, le_trans hx.2 hcb⟩
      exact mul_nonpos_of_nonneg_of_nonpos (hwb x hxab).1
        (sub_nonpos.mpr (hmono hxab hcc hx.2))
  have hright : (∫ x in c..b, w x * (f x - f c)) ≤
      ∫ x in c..b, (f x - f c) := by
    apply intervalIntegral.integral_mono_on hcb hwbarRight hfbarRight
    intro x hx
    have hxab : x ∈ Icc a b := ⟨le_trans hac hx.1, hx.2⟩
    have hnonneg : 0 ≤ f x - f c := sub_nonneg.mpr (hmono hcc hxab hx.1)
    simpa using mul_le_mul_of_nonneg_right (hwb x hxab).2 hnonneg
  have hwhole : (∫ x in a..b, w x * (f x - f c)) ≤
      ∫ x in c..b, (f x - f c) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hwbarLeft hwbarRight]
    linarith
  have hfRight : IntervalIntegrable f volume c b :=
    intervalIntegrable_on_subinterval (hf.intervalIntegrable_of_Icc hab) hab hac hcb le_rfl
  have hrewrite : (∫ x in a..b, w x * (f x - f c)) =
      (∫ x in a..b, w x * f x) - (b - c) * f c := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub hfw (hw.mul_const (f c)),
      intervalIntegral.integral_mul_const, hmass]
  rw [hrewrite, intervalIntegral.integral_sub hfRight intervalIntegrable_const,
    intervalIntegral.integral_const] at hwhole
  simpa only [smul_eq_mul] using (sub_le_sub_iff_right ((b - c) * f c)).mp hwhole

/-- The equivalent lower bound for a decreasing curve, the sign used for φ in (5.8). -/
theorem pack_right_antitone (phi w : ℝ → ℝ) (a c b : ℝ)
    (hac : a ≤ c) (hcb : c ≤ b)
    (hphi : ContinuousOn phi (Icc a b)) (hanti : AntitoneOn phi (Icc a b))
    (hw : IntervalIntegrable w volume a b)
    (hwb : ∀ x ∈ Icc a b, 0 ≤ w x ∧ w x ≤ 1)
    (hmass : (∫ x in a..b, w x) = b - c) :
    (∫ x in c..b, phi x) ≤ ∫ x in a..b, w x * phi x := by
  have hmono : MonotoneOn (fun x => -phi x) (Icc a b) := by
    intro x hx y hy hxy
    exact neg_le_neg (hanti hx hy hxy)
  have h := pack_right (fun x => -phi x) w a c b hac hcb hphi.neg hmono hw hwb hmass
  simp only [mul_neg, intervalIntegral.integral_neg, neg_le_neg_iff] at h
  exact h

end OptimalG
end

-- Source module OptimalG.Occupation
section
set_option autoImplicit true
/-! Occupation functions of finite candidate blocks on the rank line. -/

namespace OptimalG

open MeasureTheory Set
open scoped BigOperators Interval

noncomputable def intervalOccupation (a b x : ℝ) : ℝ :=
  (Ioc a b).indicator (fun _ => 1) x

theorem intervalOccupation_nonneg (a b x : ℝ) : 0 ≤ intervalOccupation a b x := by
  simp only [intervalOccupation, indicator]
  split_ifs <;> norm_num

theorem intervalOccupation_adjacent (a b c x : ℝ) (hab : a ≤ b) (hbc : b ≤ c) :
    intervalOccupation a b x + intervalOccupation b c x = intervalOccupation a c x := by
  by_cases hax : a < x
  · by_cases hbx : b < x
    · have hxb : ¬ x ≤ b := not_le.mpr hbx
      simp [intervalOccupation, Set.indicator, Set.mem_Ioc, hax, hbx, hxb]
    · have hxb : x ≤ b := le_of_not_gt hbx
      have hxc : x ≤ c := le_trans hxb hbc
      simp [intervalOccupation, Set.indicator, Set.mem_Ioc, hax, hbx, hxb, hxc]
  · have hbx : ¬ b < x := not_lt.mpr (le_trans (le_of_not_gt hax) hab)
    simp [intervalOccupation, Set.indicator, Set.mem_Ioc, hax, hbx]

theorem sum_intervalOccupation (cuts : ℕ → ℝ) (hmono : Monotone cuts) (n : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range n, intervalOccupation (cuts k) (cuts (k + 1)) x) =
      intervalOccupation (cuts 0) (cuts n) x := by
  induction n with
  | zero => simp [intervalOccupation]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    exact intervalOccupation_adjacent _ _ _ _ (hmono (Nat.zero_le n)) (hmono (Nat.le_succ n))

theorem intervalIntegrable_indicator {f : ℝ → ℝ} {a b : ℝ} {s : Set ℝ}
    (hf : IntervalIntegrable f volume a b) (hs : MeasurableSet s) :
    IntervalIntegrable (s.indicator f) volume a b :=
  ⟨hf.1.indicator hs, hf.2.indicator hs⟩

theorem intervalOccupation_integrable (a b L R : ℝ) :
    IntervalIntegrable (intervalOccupation a b) volume L R :=
  intervalIntegrable_indicator intervalIntegrable_const measurableSet_Ioc

/-- Restricting an integral to a contained interval recovers that interval's integral. -/
theorem integral_indicator_subinterval (f : ℝ → ℝ) (L a b R : ℝ)
    (hLa : L ≤ a) (hab : a ≤ b) (hbR : b ≤ R) :
    (∫ x in L..R, (Ioc a b).indicator f x) = ∫ x in a..b, f x := by
  have hLR : L ≤ R := le_trans hLa (le_trans hab hbR)
  rw [intervalIntegral.integral_of_le hLR, MeasureTheory.integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, intervalIntegral.integral_of_le hab]
  congr 1
  congr 1
  exact inter_eq_left.mpr (Ioc_subset_Ioc hLa hbR)

theorem integral_intervalOccupation (L a b R : ℝ)
    (hLa : L ≤ a) (hab : a ≤ b) (hbR : b ≤ R) :
    (∫ x in L..R, intervalOccupation a b x) = b - a := by
  change (∫ x in L..R, (Ioc a b).indicator (fun _ : ℝ => (1 : ℝ)) x) = b - a
  rw [integral_indicator_subinterval _ L a b R hLa hab hbR]
  simp

section FiniteRankLine

variable {n : ℕ}

noncomputable def occupation (D : Fin n → ℝ) (S : Finset (Fin n)) (x : ℝ) : ℝ :=
  ∑ i ∈ S, intervalOccupation (rankCut D i.val) (rankCut D (i.val + 1)) x

theorem occupation_nonneg (D : Fin n → ℝ) (S : Finset (Fin n)) (x : ℝ) :
    0 ≤ occupation D S x :=
  Finset.sum_nonneg (fun _i _ => intervalOccupation_nonneg _ _ _)

theorem occupation_mono_set (D : Fin n → ℝ) (S T : Finset (Fin n)) (hST : S ⊆ T) (x : ℝ) :
    occupation D S x ≤ occupation D T x := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hST
  intro i _ _
  exact intervalOccupation_nonneg _ _ _

theorem occupation_univ (D : Fin n → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hDsum : ∑ i, D i = 1) (x : ℝ) :
    occupation D Finset.univ x = intervalOccupation 0 1 x := by
  have h := sum_intervalOccupation (rankCut D) (rankCut_mono D hD) n x
  rw [Finset.sum_range] at h
  simpa only [occupation, rankCut_zero, rankCut_end D hDsum] using h

theorem occupation_le_one (D : Fin n → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hDsum : ∑ i, D i = 1) (S : Finset (Fin n)) (x : ℝ) :
    occupation D S x ≤ 1 := by
  calc
    occupation D S x ≤ occupation D Finset.univ x :=
      occupation_mono_set D S Finset.univ (Finset.subset_univ _) x
    _ = intervalOccupation 0 1 x := occupation_univ D hD hDsum x
    _ ≤ 1 := by simp only [intervalOccupation, indicator]; split_ifs <;> norm_num

theorem occupation_integrable (D : Fin n → ℝ) (S : Finset (Fin n)) (L R : ℝ) :
    IntervalIntegrable (occupation D S) volume L R := by
  have hf : occupation D S =
      ∑ i ∈ S, fun x => intervalOccupation (rankCut D i.val) (rankCut D (i.val + 1)) x := by
    funext x
    simp [occupation]
  rw [hf]
  exact IntervalIntegrable.sum S (fun i _ => intervalOccupation_integrable _ _ _ _)

theorem occupation_mass (D : Fin n → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hDsum : ∑ i, D i = 1) (S : Finset (Fin n)) :
    (∫ x in (0 : ℝ)..1, occupation D S x) = ∑ i ∈ S, D i := by
  unfold occupation
  rw [intervalIntegral.integral_finsetSum (fun i _ => intervalOccupation_integrable _ _ _ _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_intervalOccupation 0 _ _ 1 (rankCut_mem_Icc D hD hDsum i.val).1
    (rankCut_mono D hD (Nat.le_succ i.val)) (rankCut_mem_Icc D hD hDsum (i.val + 1)).2]
  rw [rankCut_succ]
  ring

theorem occupation_weighted_integral (D : Fin n → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hDsum : ∑ i, D i = 1) (S : Finset (Fin n)) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc 0 1)) :
    (∫ x in (0 : ℝ)..1, occupation D S x * f x) =
      ∑ i ∈ S, ∫ x in rankCut D i.val..rankCut D (i.val + 1), f x := by
  have hfu : ContinuousOn f (uIcc 0 1) := by simpa using hf
  have heq : (fun x => occupation D S x * f x) = fun x =>
      ∑ i ∈ S, (Ioc (rankCut D i.val) (rankCut D (i.val + 1))).indicator f x := by
    funext x
    simp only [occupation, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [intervalOccupation, indicator]
    split_ifs <;> simp
  rw [heq, intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact integral_indicator_subinterval f 0 _ _ 1 (rankCut_mem_Icc D hD hDsum i.val).1
      (rankCut_mono D hD (Nat.le_succ i.val)) (rankCut_mem_Icc D hD hDsum (i.val + 1)).2
  · intro i _
    exact intervalIntegrable_indicator (hf.intervalIntegrable_of_Icc (by norm_num)) measurableSet_Ioc

end FiniteRankLine

end OptimalG
end

-- Source module OptimalG.BiasedMetric
section
set_option autoImplicit true
/-!
# Realizing the biased pseudometric

The prescribed candidate and voter distances of Definition 2.3 extend to an
actual pseudometric on `V ⊕ C`. We use an explicit finite-dimensional embedding:
a candidate is its candidate-distance profile and a voter is its prescribed
voter-to-candidate profile. The sup metric preserves all prescribed distances
because these profiles satisfy the two one-point-extension triangle inequalities.
This replaces the manuscript's shortest-path extension with an equivalent
existence proof and imposes no positivity or distinctness beyond a pseudometric.
-/

namespace OptimalG

open scoped BigOperators

section RunningMinimum

variable {C : Type*} [Fintype C] [Nonempty C]

theorem runningMin_nonneg (rank : C → ℕ) (rho : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (b : C) : 0 ≤ runningMin rank rho b := by
  apply Finset.le_inf'
  intro c _
  split_ifs
  · exact hrho c
  · exact hrho b

theorem runningMin_le_of_rank_le (rank : C → ℕ) (rho : C → ℝ)
    (b c : C) (hcb : rank c ≤ rank b) : runningMin rank rho b ≤ rho c := by
  have h := Finset.inf'_le
    (fun a => if rank a ≤ rank b then rho a else rho b) (Finset.mem_univ c)
  simpa only [runningMin, if_pos hcb] using h

theorem runningMin_le_self (rank : C → ℕ) (rho : C → ℝ) (b : C) :
    runningMin rank rho b ≤ rho b :=
  runningMin_le_of_rank_le rank rho b b le_rfl

theorem runningMin_antitone_rank (rank : C → ℕ) (rho : C → ℝ)
    (b c : C) (hcb : rank c ≤ rank b) : runningMin rank rho b ≤ runningMin rank rho c := by
  apply Finset.le_inf'
  intro a _
  split_ifs with hac
  · exact runningMin_le_of_rank_le rank rho b a (le_trans hac hcb)
  · exact runningMin_le_of_rank_le rank rho b c hcb

theorem runningMin_at_zero (rank : C → ℕ) (rho : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (a : C) (ha : rho a = 0) : runningMin rank rho a = 0 := by
  apply le_antisymm
  · simpa only [ha] using runningMin_le_self rank rho a
  · exact runningMin_nonneg rank rho hrho a

theorem le_maximumGap (rank : C → ℕ) (rho : C → ℝ) (b : C) :
    rho b - runningMin rank rho b ≤ maximumGap rank rho := by
  exact Finset.le_sup' (fun c => rho c - runningMin rank rho c) (Finset.mem_univ b)

/-- The running minimum is attained at a candidate ranked no higher than b. -/
theorem runningMin_attained (rank : C → ℕ) (rho : C → ℝ) (b : C) :
    ∃ c, rank c ≤ rank b ∧ runningMin rank rho b = rho c := by
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ)
    Finset.univ_nonempty (fun c => if rank c ≤ rank b then rho c else rho b)
  by_cases hcb : rank c ≤ rank b
  · exact ⟨c, hcb, by simpa only [runningMin, if_pos hcb] using hc⟩
  · exact ⟨b, le_rfl, by simpa only [runningMin, if_neg hcb] using hc⟩

/-- The maximum drop is attained, also when all drops are zero. -/
theorem maximumGap_attained (rank : C → ℕ) (rho : C → ℝ) :
    ∃ b, maximumGap rank rho = rho b - runningMin rank rho b := by
  obtain ⟨b, _, hb⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
    Finset.univ_nonempty (fun b => rho b - runningMin rank rho b)
  exact ⟨b, hb⟩

theorem maximumGap_nonneg (rank : C → ℕ) (rho : C → ℝ) : 0 ≤ maximumGap rank rho := by
  let b : C := Classical.arbitrary C
  exact le_trans (sub_nonneg.mpr (runningMin_le_self rank rho b)) (le_maximumGap rank rho b)

end RunningMinimum

/-- Distances between distinct candidates in the biased construction. -/
noncomputable def biasedCandidateDistance {C : Type*} (rho : C → ℝ) (a b : C) : ℝ :=
  by classical exact if a = b then 0 else max (rho a) (rho b)

@[simp] theorem biasedCandidateDistance_self {C : Type*} (rho : C → ℝ) (a : C) :
    biasedCandidateDistance rho a a = 0 := by simp [biasedCandidateDistance]

theorem biasedCandidateDistance_comm {C : Type*} (rho : C → ℝ) (a b : C) :
    biasedCandidateDistance rho a b = biasedCandidateDistance rho b a := by
  classical
  simp only [biasedCandidateDistance, eq_comm, max_comm]

theorem biasedCandidateDistance_nonneg {C : Type*} (rho : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (a b : C) : 0 ≤ biasedCandidateDistance rho a b := by
  classical
  unfold biasedCandidateDistance
  split_ifs
  · rfl
  · exact le_trans (hrho a) (le_max_left _ _)

theorem biasedCandidateDistance_triangle {C : Type*} (rho : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (a b c : C) :
    biasedCandidateDistance rho a c ≤ biasedCandidateDistance rho a b +
      biasedCandidateDistance rho b c := by
  classical
  by_cases hab : a = b
  · subst b
    simp
  by_cases hbc : b = c
  · subst c
    simp
  by_cases hac : a = c
  · subst c
    simp only [biasedCandidateDistance_self]
    exact add_nonneg (biasedCandidateDistance_nonneg rho hrho a b)
      (biasedCandidateDistance_nonneg rho hrho b a)
  simp only [biasedCandidateDistance, if_neg hab, if_neg hbc, if_neg hac]
  apply max_le
  · have h1 := le_max_left (rho a) (rho b)
    have h2 : 0 ≤ max (rho b) (rho c) := le_trans (hrho b) (le_max_left _ _)
    linarith
  · have h1 := le_max_right (rho b) (rho c)
    have h2 : 0 ≤ max (rho a) (rho b) := le_trans (hrho a) (le_max_left _ _)
    linarith

/-- The exact candidate-to-reference heights, including the reference itself. -/
theorem biasedCandidateDistance_from_zero {C : Type*} (rho : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (a : C) (ha : rho a = 0) (b : C) :
    biasedCandidateDistance rho a b = rho b := by
  classical
  by_cases hab : a = b
  · subst b
    simp [ha]
  · simp [biasedCandidateDistance, hab, ha, max_eq_right (hrho b)]

/-- A general finite sup-norm realization of a one-point metric extension. -/
theorem dist_profile_eq {C : Type*} [Fintype C]
    (d : C → C → ℝ) (f : C → ℝ)
    (hself : ∀ c, d c c = 0) (hcomm : ∀ b c, d b c = d c b)
    (hf : ∀ c, 0 ≤ f c)
    (hsub : ∀ b c, f b ≤ f c + d b c)
    (hsum : ∀ b c, d b c ≤ f b + f c) (a : C) :
    dist f (d a) = f a := by
  apply le_antisymm
  · apply (dist_pi_le_iff (hf a)).mpr
    intro b
    rw [Real.dist_eq, abs_le]
    have h1 := hsub b a
    rw [hcomm b a] at h1
    have h2 := hsum a b
    constructor <;> linarith
  · have h := dist_le_pi_dist f (d a) a
    simpa only [hself a, Real.dist_eq, sub_zero, abs_of_nonneg (hf a)] using h

section Construction

variable {V C : Type*} [Fintype C] [Nonempty C]

/-- Prescribed voter-to-candidate distance. -/
noncomputable def biasedVoterDistance (rank : V → C → ℕ) (rho : C → ℝ)
    (v : V) (b : C) : ℝ :=
  maximumGap (rank v) rho / 2 + runningMin (rank v) rho b

theorem biasedVoterDistance_nonneg (rank : V → C → ℕ) (rho : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (v : V) (b : C) : 0 ≤ biasedVoterDistance rank rho v b := by
  exact add_nonneg (div_nonneg (maximumGap_nonneg _ _) (by norm_num))
    (runningMin_nonneg _ _ hrho _)

/-- The triangle inequality with the voter as an endpoint. -/
theorem biasedVoterDistance_le_add (rank : V → C → ℕ) (rho : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (v : V) (a b : C) :
    biasedVoterDistance rank rho v a ≤ biasedVoterDistance rank rho v b +
      biasedCandidateDistance rho a b := by
  classical
  by_cases hab : a = b
  · subst b
    simp
  · have h1 := runningMin_le_self (rank v) rho a
    have h2 := runningMin_nonneg (rank v) rho hrho b
    have h3 := le_max_left (rho a) (rho b)
    simp only [biasedCandidateDistance, if_neg hab, biasedVoterDistance]
    linarith

/-- The triangle inequality with the voter between the candidates. -/
theorem biasedCandidateDistance_le_voter_sum (rank : V → C → ℕ) (rho : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (v : V) (a b : C) :
    biasedCandidateDistance rho a b ≤
      biasedVoterDistance rank rho v a + biasedVoterDistance rank rho v b := by
  classical
  by_cases hab : a = b
  · subst b
    simp only [biasedCandidateDistance_self]
    exact add_nonneg (biasedVoterDistance_nonneg rank rho hrho v a)
      (biasedVoterDistance_nonneg rank rho hrho v a)
  · have h1 := le_maximumGap (rank v) rho a
    have h2 := le_maximumGap (rank v) rho b
    have ha := runningMin_nonneg (rank v) rho hrho a
    have hb := runningMin_nonneg (rank v) rho hrho b
    simp only [biasedCandidateDistance, if_neg hab, biasedVoterDistance]
    apply max_le <;> linarith

/-- Candidate and voter distance profiles in finite-dimensional sup space. -/
noncomputable def biasedEmbedding (rank : V → C → ℕ) (rho : C → ℝ) :
    V ⊕ C → (C → ℝ)
  | Sum.inl v => biasedVoterDistance rank rho v
  | Sum.inr c => biasedCandidateDistance rho c

/-- The actual pseudometric extension. Its voter-to-voter distances are the
sup distances between the prescribed candidate-distance profiles. -/
noncomputable abbrev biasedPseudoMetricSpace (rank : V → C → ℕ) (rho : C → ℝ) :
    PseudoMetricSpace (V ⊕ C) :=
  PseudoMetricSpace.induced (biasedEmbedding rank rho) inferInstance

theorem biased_dist_voter_candidate (rank : V → C → ℕ) (rho : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (v : V) (b : C) :
    letI := biasedPseudoMetricSpace rank rho
    dist (Sum.inl v) (Sum.inr b) = biasedVoterDistance rank rho v b := by
  change dist (biasedVoterDistance rank rho v) (biasedCandidateDistance rho b) = _
  exact dist_profile_eq (biasedCandidateDistance rho) (biasedVoterDistance rank rho v)
    (biasedCandidateDistance_self rho) (biasedCandidateDistance_comm rho)
    (biasedVoterDistance_nonneg rank rho hrho v)
    (biasedVoterDistance_le_add rank rho hrho v)
    (biasedCandidateDistance_le_voter_sum rank rho hrho v) b

theorem biased_dist_candidate_candidate (rank : V → C → ℕ) (rho : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (a b : C) :
    letI := biasedPseudoMetricSpace rank rho
    dist (Sum.inr a : V ⊕ C) (Sum.inr b) = biasedCandidateDistance rho a b := by
  change dist (biasedCandidateDistance rho a) (biasedCandidateDistance rho b) = _
  apply dist_profile_eq (biasedCandidateDistance rho) (biasedCandidateDistance rho a)
    (biasedCandidateDistance_self rho) (biasedCandidateDistance_comm rho)
    (biasedCandidateDistance_nonneg rho hrho a)
  · intro c d
    simpa only [biasedCandidateDistance_comm rho c d] using
      biasedCandidateDistance_triangle rho hrho a d c
  · intro c d
    simpa only [biasedCandidateDistance_comm rho c a] using
      biasedCandidateDistance_triangle rho hrho c a d

/-- The constructed distances are consistent with the given rankings. -/
theorem biased_metric_consistent (rank : V → C → ℕ) (rho : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (v : V) (b c : C) (hcb : rank v c ≤ rank v b) :
    letI := biasedPseudoMetricSpace rank rho
    dist (Sum.inl v) (Sum.inr b) ≤ dist (Sum.inl v) (Sum.inr c) := by
  rw [biased_dist_voter_candidate rank rho hrho,
    biased_dist_voter_candidate rank rho hrho]
  have h := runningMin_antitone_rank (rank v) rho b c hcb
  dsimp [biasedVoterDistance]
  linarith

/-- Every voter has the asserted distance from the reference candidate. -/
theorem biased_distance_to_reference (rank : V → C → ℕ) (rho : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (a : C) (ha : rho a = 0) (v : V) :
    letI := biasedPseudoMetricSpace rank rho
    dist (Sum.inl v) (Sum.inr a) = maximumGap (rank v) rho / 2 := by
  rw [biased_dist_voter_candidate rank rho hrho]
  simp only [biasedVoterDistance, runningMin_at_zero (rank v) rho hrho a ha, add_zero]

/-- The reference candidate minimizes each voter's distance separately. -/
theorem biased_reference_nearest (rank : V → C → ℕ) (rho : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (a : C) (ha : rho a = 0) (v : V) (b : C) :
    letI := biasedPseudoMetricSpace rank rho
    dist (Sum.inl v) (Sum.inr a) ≤ dist (Sum.inl v) (Sum.inr b) := by
  rw [biased_distance_to_reference rank rho hrho a ha,
    biased_dist_voter_candidate rank rho hrho]
  exact le_add_of_nonneg_right (runningMin_nonneg (rank v) rho hrho b)

/-- The social cost of the reference candidate is exactly half the mean gap. -/
theorem biased_reference_cost [Fintype V]
    (rank : V → C → ℕ) (rho : C → ℝ) (w : V → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (a : C) (ha : rho a = 0) :
    letI := biasedPseudoMetricSpace rank rho
    expectation w (fun v => dist (Sum.inl v) (Sum.inr a)) =
      expectation w (fun v => maximumGap (rank v) rho) / 2 := by
  simp_rw [biased_distance_to_reference rank rho hrho a ha]
  unfold expectation
  simp_rw [← mul_div_assoc]
  rw [Finset.sum_div]

/-- Exact lottery social cost for the constructed pseudometric. -/
theorem biased_lottery_cost [Fintype V]
    (rank : V → C → ℕ) (rho : C → ℝ) (w : V → ℝ) (D : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (hDsum : ∑ c, D c = 1) :
    letI := biasedPseudoMetricSpace rank rho
    expectation w (fun v => expectation D (fun b => dist (Sum.inl v) (Sum.inr b))) =
      expectation w (fun v => maximumGap (rank v) rho) / 2 +
        expectation w (fun v => expectation D (runningMin (rank v) rho)) := by
  simp_rw [biased_dist_voter_candidate rank rho hrho, biasedVoterDistance,
    expectation_add, expectation_const hDsum]
  congr 1
  unfold expectation
  simp_rw [← mul_div_assoc]
  rw [Finset.sum_div]

/-- In particular the reference candidate minimizes social cost. -/
theorem biased_reference_cost_minimal [Fintype V]
    (rank : V → C → ℕ) (rho : C → ℝ) (w : V → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (hw : ∀ v, 0 ≤ w v) (a : C) (ha : rho a = 0) (b : C) :
    letI := biasedPseudoMetricSpace rank rho
    expectation w (fun v => dist (Sum.inl v) (Sum.inr a)) ≤
      expectation w (fun v => dist (Sum.inl v) (Sum.inr b)) := by
  exact expectation_mono hw (fun v => biased_reference_nearest rank rho hrho a ha v b)

/-- Every strict violation of (2.1) is a strict social-cost violation in the
actual constructed pseudometric. Positivity of the denominator is handled
separately by the shifted construction below. -/
theorem biased_cost_strict_violation [Fintype V]
    (rank : V → C → ℕ) (rho : C → ℝ) (w : V → ℝ) (D : C → ℝ) (lam : ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (hDsum : ∑ c, D c = 1)
    (a : C) (ha : rho a = 0)
    (hviolation : lam * expectation w (fun v => maximumGap (rank v) rho) <
      expectation w (fun v => expectation D (runningMin (rank v) rho))) :
    letI := biasedPseudoMetricSpace rank rho
    (1 + 2 * lam) * expectation w (fun v => dist (Sum.inl v) (Sum.inr a)) <
      expectation w (fun v => expectation D (fun b => dist (Sum.inl v) (Sum.inr b))) := by
  rw [biased_reference_cost rank rho w hrho a ha,
    biased_lottery_cost rank rho w D hrho hDsum]
  linarith

/-- Adding a positive constant to every distance between distinct points turns
any pseudometric into a genuine metric. -/
noncomputable abbrev separatedMetricSpace {X : Type*}
    (m : PseudoMetricSpace X) (eps : ℝ) (heps : 0 < eps) : MetricSpace X := by
  classical
  letI := m
  exact {
    dist := fun x y => if x = y then 0 else dist x y + eps
    dist_self := by intro x; simp
    dist_comm := by intro x y; simp only [eq_comm, dist_comm]
    dist_triangle := by
      intro x y z
      by_cases hxy : x = y
      · subst y
        simp
      by_cases hyz : y = z
      · subst z
        simp
      by_cases hxz : x = z
      · subst z
        simp only [ite_true, if_neg hxy, if_neg (Ne.symm hxy)]
        have h1 : 0 ≤ dist x y := dist_nonneg
        have h2 : 0 ≤ dist y x := dist_nonneg
        linarith
      · simp only [if_neg hxy, if_neg hyz, if_neg hxz]
        have h := dist_triangle x y z
        linarith
    eq_of_dist_eq_zero := by
      intro x y h
      by_contra hxy
      rw [if_neg hxy] at h
      have hn : 0 ≤ dist x y := dist_nonneg
      linarith
  }

theorem separated_dist_of_ne {X : Type*} (m : PseudoMetricSpace X)
    (eps : ℝ) (heps : 0 < eps) (x y : X) (hxy : x ≠ y) :
    letI : PseudoMetricSpace X := (separatedMetricSpace m eps heps).toPseudoMetricSpace
    dist x y = @dist X m.toDist x y + eps := by
  classical
  change (if x = y then 0 else @dist X m.toDist x y + eps) = _
  exact if_neg hxy

/-- The positive-distance version used to witness a distortion ratio. -/
noncomputable abbrev regularizedBiasedMetricSpace
    (rank : V → C → ℕ) (rho : C → ℝ) (eps : ℝ) (heps : 0 < eps) :
    MetricSpace (V ⊕ C) :=
  separatedMetricSpace (biasedPseudoMetricSpace rank rho) eps heps

theorem regularized_dist_voter_candidate
    (rank : V → C → ℕ) (rho : C → ℝ) (hrho : ∀ c, 0 ≤ rho c)
    (eps : ℝ) (heps : 0 < eps) (v : V) (b : C) :
    letI : PseudoMetricSpace (V ⊕ C) :=
      (regularizedBiasedMetricSpace rank rho eps heps).toPseudoMetricSpace
    dist (Sum.inl v) (Sum.inr b) = biasedVoterDistance rank rho v b + eps := by
  calc
    _ = @dist (V ⊕ C) (biasedPseudoMetricSpace rank rho).toDist
        (Sum.inl v) (Sum.inr b) + eps :=
      separated_dist_of_ne (biasedPseudoMetricSpace rank rho) eps heps
        (Sum.inl v) (Sum.inr b) (by simp)
    _ = _ := congrArg (fun r : ℝ => r + eps) (biased_dist_voter_candidate rank rho hrho v b)

theorem regularized_metric_consistent
    (rank : V → C → ℕ) (rho : C → ℝ) (hrho : ∀ c, 0 ≤ rho c)
    (eps : ℝ) (heps : 0 < eps) (v : V) (b c : C) (hcb : rank v c ≤ rank v b) :
    letI : PseudoMetricSpace (V ⊕ C) :=
      (regularizedBiasedMetricSpace rank rho eps heps).toPseudoMetricSpace
    dist (Sum.inl v) (Sum.inr b) ≤ dist (Sum.inl v) (Sum.inr c) := by
  rw [regularized_dist_voter_candidate rank rho hrho,
    regularized_dist_voter_candidate rank rho hrho]
  have h := runningMin_antitone_rank (rank v) rho b c hcb
  dsimp [biasedVoterDistance]
  linarith

/-- Regularization adds exactly eps to the reference social cost. -/
theorem regularized_reference_cost [Fintype V]
    (rank : V → C → ℕ) (rho : C → ℝ) (w : V → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (hwsum : ∑ v, w v = 1)
    (a : C) (ha : rho a = 0) (eps : ℝ) (heps : 0 < eps) :
    letI : PseudoMetricSpace (V ⊕ C) :=
      (regularizedBiasedMetricSpace rank rho eps heps).toPseudoMetricSpace
    expectation w (fun v => dist (Sum.inl v) (Sum.inr a)) =
      expectation w (fun v => maximumGap (rank v) rho) / 2 + eps := by
  simp_rw [regularized_dist_voter_candidate rank rho hrho, biasedVoterDistance,
    runningMin_at_zero _ rho hrho a ha, add_zero]
  rw [expectation_add, expectation_const hwsum]
  congr 1
  unfold expectation
  simp_rw [← mul_div_assoc]
  rw [Finset.sum_div]

/-- Regularization adds exactly eps to the lottery social cost as well. -/
theorem regularized_lottery_cost [Fintype V]
    (rank : V → C → ℕ) (rho : C → ℝ) (w : V → ℝ) (D : C → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (hwsum : ∑ v, w v = 1) (hDsum : ∑ c, D c = 1)
    (eps : ℝ) (heps : 0 < eps) :
    letI : PseudoMetricSpace (V ⊕ C) :=
      (regularizedBiasedMetricSpace rank rho eps heps).toPseudoMetricSpace
    expectation w (fun v => expectation D (fun b => dist (Sum.inl v) (Sum.inr b))) =
      expectation w (fun v => maximumGap (rank v) rho) / 2 +
        expectation w (fun v => expectation D (runningMin (rank v) rho)) + eps := by
  simp_rw [regularized_dist_voter_candidate rank rho hrho, biasedVoterDistance,
    expectation_add, expectation_const hDsum, expectation_const hwsum]
  congr 2
  unfold expectation
  simp_rw [← mul_div_assoc]
  rw [Finset.sum_div]

/-- The reference candidate stays optimal under regularization. -/
theorem regularized_reference_cost_minimal [Fintype V]
    (rank : V → C → ℕ) (rho : C → ℝ) (w : V → ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (hw : ∀ v, 0 ≤ w v) (a : C) (ha : rho a = 0)
    (eps : ℝ) (heps : 0 < eps) (b : C) :
    letI : PseudoMetricSpace (V ⊕ C) :=
      (regularizedBiasedMetricSpace rank rho eps heps).toPseudoMetricSpace
    expectation w (fun v => dist (Sum.inl v) (Sum.inr a)) ≤
      expectation w (fun v => dist (Sum.inl v) (Sum.inr b)) := by
  apply expectation_mono hw
  intro v
  rw [regularized_dist_voter_candidate rank rho hrho,
    regularized_dist_voter_candidate rank rho hrho]
  dsimp [biasedVoterDistance]
  rw [runningMin_at_zero _ rho hrho a ha]
  have h := runningMin_nonneg (rank v) rho hrho b
  linarith

/-- Full reverse witness for Lemma 2.4. Every strict violation of the
running-minimum inequality yields a finite genuine metric, consistent with the
rankings, with positive optimal social cost and distortion strictly above the
claimed bound. This includes mean gap zero and uses no limiting argument. -/
theorem exists_metric_of_strict_runningMin_violation [Fintype V]
    (rank : V → C → ℕ) (rho : C → ℝ) (w : V → ℝ) (D : C → ℝ) (lam : ℝ)
    (hrho : ∀ c, 0 ≤ rho c) (hw : ∀ v, 0 ≤ w v)
    (hwsum : ∑ v, w v = 1) (hDsum : ∑ c, D c = 1) (hlam : 0 ≤ lam)
    (a : C) (ha : rho a = 0)
    (hviolation : lam * expectation w (fun v => maximumGap (rank v) rho) <
      expectation w (fun v => expectation D (runningMin (rank v) rho))) :
    ∃ m : MetricSpace (V ⊕ C), letI : PseudoMetricSpace (V ⊕ C) := m.toPseudoMetricSpace
      (∀ (v : V) (b c : C), rank v c ≤ rank v b →
        dist (Sum.inl v) (Sum.inr b) ≤ dist (Sum.inl v) (Sum.inr c)) ∧
      (∀ b : C, expectation w (fun v => dist (Sum.inl v) (Sum.inr a)) ≤
        expectation w (fun v => dist (Sum.inl v) (Sum.inr b))) ∧
      0 < expectation w (fun v => dist (Sum.inl v) (Sum.inr a)) ∧
      1 + 2 * lam <
        expectation w (fun v => expectation D (fun b => dist (Sum.inl v) (Sum.inr b))) /
          expectation w (fun v => dist (Sum.inl v) (Sum.inr a)) := by
  let G := expectation w (fun v => maximumGap (rank v) rho)
  let N := expectation w (fun v => expectation D (runningMin (rank v) rho))
  let gap := N - lam * G
  have hgap : 0 < gap := sub_pos.mpr hviolation
  let eps := gap / (4 * lam + 2)
  have hden : 0 < 4 * lam + 2 := by linarith
  have heps : 0 < eps := div_pos hgap hden
  have hepsEq : eps * (4 * lam + 2) = gap := div_mul_cancel₀ _ (ne_of_gt hden)
  have hG : 0 ≤ G := by
    apply Finset.sum_nonneg
    intro v _
    exact mul_nonneg (hw v) (maximumGap_nonneg (rank v) rho)
  have hbase : 0 < G / 2 + eps := by linarith
  have hprod : 0 ≤ lam * eps := mul_nonneg hlam (le_of_lt heps)
  have hexcess : (1 + 2 * lam) * (G / 2 + eps) < G / 2 + N + eps := by
    dsimp [gap] at hepsEq
    nlinarith
  refine ⟨regularizedBiasedMetricSpace rank rho eps heps, ?_⟩
  refine ⟨fun v b c h => regularized_metric_consistent rank rho hrho eps heps v b c h,
    fun b => regularized_reference_cost_minimal rank rho w hrho hw a ha eps heps b, ?_, ?_⟩
  · rw [regularized_reference_cost rank rho w hrho hwsum a ha]
    exact hbase
  · rw [regularized_reference_cost rank rho w hrho hwsum a ha,
      regularized_lottery_cost rank rho w D hrho hwsum hDsum]
    exact (lt_div_iff₀ hbase).mpr hexcess

end Construction

end OptimalG
end

-- Source module OptimalG.Telescoping
section
set_option autoImplicit true
/-!
# The threshold telescoping step of Section 5.1

This is a theorem about integrable slice functions, including arbitrary real threshold shifts.
It covers the case where the shift exceeds the total threshold range. The hypotheses connecting
these functions to a stable lottery (packing, layer cake, and the four verifier inequalities)
are not asserted here.
-/

namespace OptimalG

open MeasureTheory Set
open scoped Interval BigOperators

private theorem subinterval_integrable {F : ℝ → ℝ} {a b c d : ℝ}
    (hF : IntervalIntegrable F volume a b) (hab : a ≤ b)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    IntervalIntegrable F volume c d := by
  apply hF.mono_set
  rw [uIcc_of_le hcd, uIcc_of_le hab]
  exact Icc_subset_Icc hac hdb

/-- The exact shifted-integral cancellation behind (5.2), with no discretization. -/
theorem integral_shift_cancellation (F : ℝ → ℝ) (X delta : ℝ)
    (hX : 0 ≤ X) (hd : 0 ≤ delta)
    (hF : IntervalIntegrable F volume (-delta) X) :
    (∫ t in (0 : ℝ)..X, (F (t - delta) - F t)) =
      (∫ t in -delta..0, F t) - (∫ t in X - delta..X, F t) := by
  have htot : -delta ≤ X := by linarith
  have h0X := subinterval_integrable hF htot (by linarith : -delta ≤ 0) hX le_rfl
  have hshift := subinterval_integrable hF htot le_rfl
    (by linarith : -delta ≤ X - delta) (by linarith : X - delta ≤ X)
  have htrans : IntervalIntegrable (fun t => F (t - delta)) volume 0 X := by
    simpa using hshift.comp_sub_right delta
  rw [intervalIntegral.integral_sub htrans h0X,
    intervalIntegral.integral_comp_sub_right]
  simp only [zero_sub]
  exact intervalIntegral.integral_interval_sub_interval_comm hshift h0X
    (subinterval_integrable hF htot le_rfl (by linarith) hX)

/-- An offset slice bounded by a backward potential difference has integral at most λΔ. -/
theorem integral_telescope_bound (L F : ℝ → ℝ) (X delta lam : ℝ)
    (hX : 0 ≤ X) (hd : 0 ≤ delta) (hlam : 0 ≤ lam)
    (hL : IntervalIntegrable L volume 0 X)
    (hF : IntervalIntegrable F volume (-delta) X)
    (hnegative : ∀ t, t < 0 → F t = lam)
    (hnonnegative : ∀ t, 0 ≤ t → 0 ≤ F t)
    (hbound : ∀ t ∈ Icc 0 X, L t ≤ F (t - delta) - F t) :
    (∫ t in (0 : ℝ)..X, L t) ≤ lam * delta := by
  have htot : -delta ≤ X := by linarith
  have h0X := subinterval_integrable hF htot (by linarith : -delta ≤ 0) hX le_rfl
  have hshift := subinterval_integrable hF htot le_rfl
    (by linarith : -delta ≤ X - delta) (by linarith : X - delta ≤ X)
  have htrans : IntervalIntegrable (fun t => F (t - delta)) volume 0 X := by
    simpa using hshift.comp_sub_right delta
  have hle := intervalIntegral.integral_mono_on hX hL (htrans.sub h0X) hbound
  rw [integral_shift_cancellation F X delta hX hd hF] at hle
  have hleft : (∫ t in -delta..0, F t) = lam * delta := by
    calc
      _ = ∫ _t in -delta..(0 : ℝ), lam := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
        intro t ht
        exact hnegative t ht.2
      _ = lam * delta := by rw [intervalIntegral.integral_const]; simp; ring
  have hall : ∀ t, 0 ≤ F t := by
    intro t
    rcases lt_or_ge t 0 with ht | ht
    · rw [hnegative t ht]; exact hlam
    · exact hnonnegative t ht
  have hright : 0 ≤ ∫ t in X - delta..X, F t :=
    intervalIntegral.integral_nonneg_of_forall (by linarith) hall
  rw [hleft] at hle
  linarith

/-- Extension by the initial potential value, as used immediately after (5.2). -/
noncomputable def extendedPotential (W q : ℝ → ℝ) (lam t : ℝ) : ℝ :=
  if t < 0 then lam else W (q t)

/-- The two slice inequalities imply the backward potential-difference bound.
The separation property `hz` is the second inequality of (5.1). -/
theorem slice_bound_to_difference
    (L W q z : ℝ → ℝ) (lam delta s t : ℝ)
    (ht : 0 ≤ t)
    (hfirst : L t ≤ lam - W (q t))
    (hsecond : ∀ r, z t ≤ r → r ≤ s → L t ≤ W r - W (q t))
    (hq : ∀ r, 0 ≤ r → q r ≤ s)
    (hz : ∀ r, 0 ≤ r → z (r + delta) ≤ q r) :
    L t ≤ extendedPotential W q lam (t - delta) - extendedPotential W q lam t := by
  simp only [extendedPotential, if_neg (not_lt.mpr ht)]
  by_cases htd : t - delta < 0
  · rw [if_pos htd]
    exact hfirst
  · rw [if_neg htd]
    have htd' : 0 ≤ t - delta := le_of_not_gt htd
    apply hsecond (q (t - delta))
    · simpa using hz (t - delta) htd'
    · exact hq (t - delta) htd'

/-- Integration commutes with finite weighted averaging. -/
theorem integral_expectation {V : Type*} [Fintype V]
    (w : V → ℝ) (f : V → ℝ → ℝ) (a b : ℝ)
    (hf : ∀ v, IntervalIntegrable (f v) volume a b) :
    (∫ t in a..b, expectation w (fun v => f v t)) =
      expectation w (fun v => ∫ t in a..b, f v t) := by
  unfold expectation
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro v _
    exact intervalIntegral.integral_const_mul (w v) (f v)
  · intro v _
    exact (hf v).const_mul (w v)

/-- Averaging the telescoping bound yields the target running-minimum inequality.
This theorem checks the integration/averaging argument; it does not supply the slice hypotheses. -/
theorem averaged_slice_bound {V : Type*} [Fintype V]
    (w delta : V → ℝ) (q L F : V → ℝ → ℝ) (X lam : ℝ)
    (hw : ∀ v, 0 ≤ w v) (hd : ∀ v, 0 ≤ delta v)
    (hX : 0 ≤ X) (hlam : 0 ≤ lam)
    (hq : ∀ v, IntervalIntegrable (q v) volume 0 X)
    (hL : ∀ v, IntervalIntegrable (L v) volume 0 X)
    (hF : ∀ v, IntervalIntegrable (F v) volume (-delta v) X)
    (hnegative : ∀ v t, t < 0 → F v t = lam)
    (hnonnegative : ∀ v t, 0 ≤ t → 0 ≤ F v t)
    (hoffset : ∀ t ∈ Icc 0 X,
      expectation w (fun v => q v t) ≤ expectation w (fun v => L v t))
    (hbound : ∀ v t, t ∈ Icc 0 X → L v t ≤ F v (t - delta v) - F v t) :
    expectation w (fun v => ∫ t in (0 : ℝ)..X, q v t) ≤
      lam * expectation w delta := by
  have hintq : IntervalIntegrable (fun t => expectation w (fun v => q v t)) volume 0 X := by
    have hf : (fun t => expectation w (fun v => q v t)) =
        (∑ v, fun t => w v * q v t) := by
      funext t
      simp [expectation]
    rw [hf]
    exact IntervalIntegrable.sum Finset.univ (fun v _ => (hq v).const_mul (w v))
  have hintL : IntervalIntegrable (fun t => expectation w (fun v => L v t)) volume 0 X := by
    have hf : (fun t => expectation w (fun v => L v t)) =
        (∑ v, fun t => w v * L v t) := by
      funext t
      simp [expectation]
    rw [hf]
    exact IntervalIntegrable.sum Finset.univ (fun v _ => (hL v).const_mul (w v))
  have hfirst := intervalIntegral.integral_mono_on hX hintq hintL hoffset
  rw [integral_expectation w q 0 X hq, integral_expectation w L 0 X hL] at hfirst
  calc
    _ ≤ expectation w (fun v => ∫ t in (0 : ℝ)..X, L v t) := hfirst
    _ ≤ expectation w (fun v => lam * delta v) := by
      apply expectation_mono hw
      intro v
      exact integral_telescope_bound (L v) (F v) X (delta v) lam hX (hd v) hlam
        (hL v) (hF v) (hnegative v) (hnonnegative v) (hbound v)
    _ = lam * expectation w delta := expectation_smul w delta lam

end OptimalG
end

-- Source module OptimalG.ThresholdGeometry
section
set_option autoImplicit true
/-!
# Threshold slices of finite rank lines

These definitions include candidates of probability zero. The first missing
candidate controls the initial slice, even when its own rank interval has zero width.
-/

namespace OptimalG

open Set MeasureTheory
open scoped BigOperators Interval

section Prefix

variable {n : ℕ} [Nonempty (Fin n)]

/-- Index of the first candidate outside `S`, or `n` if every candidate is in `S`. -/
noncomputable def prefixBoundary (S : Finset (Fin n)) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => if i ∈ S then n else i.val)

theorem before_prefixBoundary_iff (S : Finset (Fin n)) (i : Fin n) :
    i.val < prefixBoundary S ↔ ∀ j : Fin n, j.val ≤ i.val → j ∈ S := by
  classical
  simp only [prefixBoundary, Finset.lt_inf'_iff, Finset.mem_univ, forall_true_left]
  constructor
  · intro h j hji
    by_contra hj
    have hh := h j
    simp only [if_neg hj] at hh
    omega
  · intro h j
    by_cases hj : j ∈ S
    · simpa only [if_pos hj] using i.isLt
    · simp only [if_neg hj]
      by_contra hle
      exact hj (h j (by omega))

theorem prefixBoundary_le_outside (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    prefixBoundary S ≤ i.val := by
  classical
  have h := Finset.inf'_le (fun j : Fin n => if j ∈ S then n else j.val)
    (Finset.mem_univ i)
  simpa only [prefixBoundary, if_neg hi] using h

theorem prefixBoundary_le (S : Finset (Fin n)) : prefixBoundary S ≤ n := by
  classical
  let i : Fin n := Classical.arbitrary _
  have h := Finset.inf'_le (fun j : Fin n => if j ∈ S then n else j.val)
    (Finset.mem_univ i)
  change prefixBoundary S ≤ (if i ∈ S then n else i.val) at h
  split_ifs at h with hi
  · exact h
  · exact le_trans h i.isLt.le

theorem prefixCut_le_mass (D : Fin n → ℝ) (hD : ∀ i, 0 ≤ D i) (S : Finset (Fin n)) :
    rankCut D (prefixBoundary S) ≤ ∑ i ∈ S, D i := by
  classical
  unfold rankCut
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    exact (before_prefixBoundary_iff S i).mp (Finset.mem_filter.mp hi).2 i le_rfl
  · intro i _ _
    exact hD i

theorem runningMin_gt_iff (rho : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    t < runningMin (fun j : Fin n => j.val) rho i ↔
      ∀ j : Fin n, j.val ≤ i.val → t < rho j := by
  simp only [runningMin, Finset.lt_inf'_iff, Finset.mem_univ, forall_true_left]
  constructor
  · intro h j hji
    simpa only [if_pos hji] using h j
  · intro h j
    split_ifs with hji
    · exact h j hji
    · exact h i le_rfl

noncomputable def thresholdSet (rho : Fin n → ℝ) (t : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => t < rho i)

noncomputable def thresholdWidth (D rho : Fin n → ℝ) (t : ℝ) : ℝ :=
  rankCut D (prefixBoundary (thresholdSet rho t))

/-- The slice width is the lottery mass whose running minimum exceeds the threshold. -/
theorem thresholdWidth_eq_sum (D rho : Fin n → ℝ) (t : ℝ) :
    thresholdWidth D rho t = ∑ i,
      if t < runningMin (fun j : Fin n => j.val) rho i then D i else 0 := by
  classical
  unfold thresholdWidth rankCut
  apply Finset.sum_congr rfl
  intro i _
  have heq : i.val < prefixBoundary (thresholdSet rho t) ↔
      t < runningMin (fun j : Fin n => j.val) rho i := by
    rw [before_prefixBoundary_iff, runningMin_gt_iff]
    simp [thresholdSet]
  simp only [heq]

theorem thresholdWidth_nonneg (D rho : Fin n → ℝ) (hD : ∀ i, 0 ≤ D i) (t : ℝ) :
    0 ≤ thresholdWidth D rho t := by
  rw [thresholdWidth_eq_sum]
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact hD i
  · rfl

theorem thresholdWidth_le_mass (D rho : Fin n → ℝ) (hD : ∀ i, 0 ≤ D i) (t : ℝ) :
    thresholdWidth D rho t ≤ ∑ i ∈ thresholdSet rho t, D i := by
  classical
  rw [thresholdWidth_eq_sum, ← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    have hrun := (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      lt_of_lt_of_le hrun (runningMin_le_self _ rho i)⟩
  · intro i _ _
    exact hD i

theorem thresholdWidth_le_referenceRank (D rho : Fin n → ℝ)
    (hD : ∀ i, 0 ≤ D i) (a : Fin n) (ha : rho a = 0) (t : ℝ) (ht : 0 ≤ t) :
    thresholdWidth D rho t ≤ rankCut D a.val := by
  apply rankCut_mono D hD
  apply prefixBoundary_le_outside
  simp [thresholdSet, ha, not_lt.mpr ht]

/-- One past the last ordinal position in a candidate set; zero for the empty set. -/
def lastIndex (S : Finset (Fin n)) : ℕ := S.sup (fun i => i.val + 1)

omit [Nonempty (Fin n)] in
theorem lastIndex_le (S : Finset (Fin n)) : lastIndex S ≤ n := by
  apply Finset.sup_le
  intro i _
  exact i.isLt

omit [Nonempty (Fin n)] in
theorem member_lt_lastIndex (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) :
    i.val < lastIndex S := by
  exact Finset.le_sup (f := fun j : Fin n => j.val + 1) hi

omit [Nonempty (Fin n)] in
theorem mass_le_lastCut (D : Fin n → ℝ) (hD : ∀ i, 0 ≤ D i) (S : Finset (Fin n)) :
    (∑ i ∈ S, D i) ≤ rankCut D (lastIndex S) := by
  classical
  calc
    (∑ i ∈ S, D i) = ∑ i ∈ S, if i.val < lastIndex S then D i else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [member_lt_lastIndex S i hi]
    _ ≤ ∑ i : Fin n, if i.val < lastIndex S then D i else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i _ _
      split_ifs
      · exact hD i
      · rfl
    _ = rankCut D (lastIndex S) := rfl

noncomputable def thresholdRight (D rho : Fin n → ℝ) (t : ℝ) : ℝ :=
  rankCut D (lastIndex (thresholdSet rho t))

/-- Every candidate above threshold t+Δ precedes every candidate at or below t. -/
theorem threshold_candidates_separated (rho : Fin n → ℝ) (t : ℝ)
    (b c : Fin n) (hb : t + maximumGap (fun i : Fin n => i.val) rho < rho b)
    (hc : rho c ≤ t) : b.val < c.val := by
  by_contra hbc
  have hmin := runningMin_le_of_rank_le (fun i : Fin n => i.val) rho b c (by omega)
  have hgap := le_maximumGap (fun i : Fin n => i.val) rho b
  linarith

/-- The separation in (5.1), proved from the actual running maximum gap. -/
theorem threshold_separation (D rho : Fin n → ℝ) (hD : ∀ i, 0 ≤ D i) (t : ℝ) :
    thresholdRight D rho (t + maximumGap (fun i : Fin n => i.val) rho) ≤
      thresholdWidth D rho t := by
  classical
  apply rankCut_mono D hD
  apply Finset.sup_le
  intro b hb
  apply Nat.succ_le_of_lt
  rw [before_prefixBoundary_iff]
  intro c hcb
  by_contra hc
  have hb' : t + maximumGap (fun i : Fin n => i.val) rho < rho b := by
    simpa [thresholdSet] using hb
  have hc' : rho c ≤ t := by simpa [thresholdSet] using hc
  have hbc := threshold_candidates_separated rho t b c hb' hc'
  omega

theorem thresholdWidth_zero_above (D rho : Fin n → ℝ) (X t : ℝ)
    (hX : ∀ i, rho i ≤ X) (ht : X ≤ t) : thresholdWidth D rho t = 0 := by
  classical
  rw [thresholdWidth_eq_sum]
  apply Finset.sum_eq_zero
  intro i _
  have hbound := le_trans (runningMin_le_self (fun j : Fin n => j.val) rho i)
    (le_trans (hX i) ht)
  simp [not_lt.mpr hbound]

end Prefix

/-- The elementary real-valued layer-cake integral for one height. -/
theorem integral_below_height (h X : ℝ) (hh : 0 ≤ h) (hX : h ≤ X) :
    IntervalIntegrable (fun t : ℝ => if t < h then (1 : ℝ) else 0) volume 0 X ∧
      (∫ t in (0 : ℝ)..X, if t < h then (1 : ℝ) else 0) = h := by
  let f : ℝ → ℝ := fun t => if t < h then 1 else 0
  have hleft : IntervalIntegrable f volume 0 h := by
    apply (intervalIntegrable_const (c := (1 : ℝ))).congr_uIoo
    rw [uIoo_of_le hh]
    intro t ht
    simp [f, ht.2]
  have hright : IntervalIntegrable f volume h X := by
    apply (intervalIntegrable_const (c := (0 : ℝ))).congr_uIoo
    rw [uIoo_of_le hX]
    intro t ht
    simp [f, not_lt.mpr ht.1.le]
  refine ⟨hleft.trans hright, ?_⟩
  change (∫ t in (0 : ℝ)..X, f t) = h
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright]
  have hl : (∫ t in (0 : ℝ)..h, f t) = h := by
    calc
      _ = ∫ _t in (0 : ℝ)..h, (1 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hh
        intro t ht
        simp [f, ht.2]
      _ = h := by simp
  have hr : (∫ t in h..X, f t) = 0 := by
    calc
      _ = ∫ _t in h..X, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hX
        intro t ht
        simp [f, not_lt.mpr ht.1.le]
      _ = 0 := by simp
  rw [hl, hr, add_zero]

/-- Finite layer cake: the integral of the threshold slice is its running-minimum cost. -/
theorem threshold_layer_cake {n : ℕ} [Nonempty (Fin n)]
    (D rho : Fin n → ℝ) (X : ℝ) (hrho : ∀ i, 0 ≤ rho i)
    (hX : ∀ i, rho i ≤ X) :
    IntervalIntegrable (thresholdWidth D rho) volume 0 X ∧
      (∫ t in (0 : ℝ)..X, thresholdWidth D rho t) =
        expectation D (runningMin (fun j : Fin n => j.val) rho) := by
  classical
  let heights := runningMin (fun j : Fin n => j.val) rho
  let f : Fin n → ℝ → ℝ := fun i t => if t < heights i then 1 else 0
  have hf : ∀ i, IntervalIntegrable (f i) volume 0 X := by
    intro i
    exact (integral_below_height (heights i) X
      (runningMin_nonneg _ rho hrho i)
      (le_trans (runningMin_le_self _ rho i) (hX i))).1
  have heq : thresholdWidth D rho = fun t => expectation D (fun i => f i t) := by
    funext t
    rw [thresholdWidth_eq_sum]
    unfold expectation
    apply Finset.sum_congr rfl
    intro i _
    simp only [f, heights]
    split_ifs <;> simp
  rw [heq]
  constructor
  · have heqsum : (fun t => expectation D (fun i => f i t)) =
        ∑ i, fun t => D i * f i t := by
      funext t
      simp [expectation]
    rw [heqsum]
    exact IntervalIntegrable.sum _ (fun i _ => (hf i).const_mul (D i))
  · rw [integral_expectation D f 0 X hf]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact (integral_below_height (heights i) X
      (runningMin_nonneg _ rho hrho i)
      (le_trans (runningMin_le_self _ rho i) (hX i))).2

end OptimalG
end

-- Source module OptimalG.RankPacking
section
set_option autoImplicit true
/-! The packing inequalities (5.8), for actual finite candidate intervals. -/

namespace OptimalG

open Set MeasureTheory
open scoped BigOperators Interval

section

variable {n : ℕ} [Nonempty (Fin n)]

theorem occupation_prefix_one (D : Fin n → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hDsum : ∑ i, D i = 1) (S : Finset (Fin n)) (x : ℝ)
    (hx0 : 0 < x) (hxq : x ≤ rankCut D (prefixBoundary S)) :
    occupation D S x = 1 := by
  classical
  have hx1 : x ≤ 1 := le_trans hxq (rankCut_mem_Icc D hD hDsum _).2
  calc
    occupation D S x = occupation D Finset.univ x := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have hcut := rankCut_mono D hD (prefixBoundary_le_outside S i hi)
      have hxi : x ≤ rankCut D i.val := le_trans hxq hcut
      simp [intervalOccupation, Set.indicator, Set.mem_Ioc, not_lt.mpr hxi]
    _ = intervalOccupation 0 1 x := occupation_univ D hD hDsum x
    _ = 1 := by simp [intervalOccupation, hx0, hx1]

omit [Nonempty (Fin n)] in
theorem occupation_zero_above_last (D : Fin n → ℝ) (hD : ∀ i, 0 ≤ D i)
    (S : Finset (Fin n)) (x : ℝ) (hx : rankCut D (lastIndex S) < x) :
    occupation D S x = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i hi
  have hindex := member_lt_lastIndex S i hi
  have hcut := rankCut_mono D hD (show i.val + 1 ≤ lastIndex S from hindex)
  have hxi : rankCut D (i.val + 1) < x := lt_of_le_of_lt hcut hx
  simp [intervalOccupation, Set.indicator, Set.mem_Ioc, not_le.mpr hxi]

theorem occupation_middle_mass (D : Fin n → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hDsum : ∑ i, D i = 1) (S : Finset (Fin n)) (q z : ℝ)
    (hq : q = rankCut D (prefixBoundary S))
    (hz : rankCut D (lastIndex S) ≤ z) (hz1 : z ≤ 1) :
    (∫ x in q..z, occupation D S x) = (∑ i ∈ S, D i) - q := by
  have hq0 : 0 ≤ q := by rw [hq]; exact (rankCut_mem_Icc D hD hDsum _).1
  have hqp : q ≤ ∑ i ∈ S, D i := by rw [hq]; exact prefixCut_le_mass D hD S
  have hpz := le_trans (mass_le_lastCut D hD S) hz
  have hqz : q ≤ z := le_trans hqp hpz
  have hleft : (∫ x in (0 : ℝ)..q, occupation D S x) = q := by
    calc
      _ = ∫ _x in (0 : ℝ)..q, (1 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hq0
        intro x hx
        exact occupation_prefix_one D hD hDsum S x hx.1 (hq ▸ hx.2.le)
      _ = q := by simp
  have hright : (∫ x in z..1, occupation D S x) = 0 := by
    calc
      _ = ∫ _x in z..(1 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hz1
        intro x hx
        exact occupation_zero_above_last D hD S x (lt_of_le_of_lt hz hx.1)
      _ = 0 := by simp
  have htotal := occupation_mass D hD hDsum S
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
    (occupation_integrable D S 0 q) (occupation_integrable D S q z)
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
    (occupation_integrable D S 0 z) (occupation_integrable D S z 1)
  linarith

noncomputable def curvePrimitive (phi : ℝ → ℝ) (r : ℝ) : ℝ := ∫ x in (0 : ℝ)..r, phi x

noncomputable def centeredBlock (D : Fin n → ℝ) (S : Finset (Fin n)) (phi : ℝ → ℝ) : ℝ :=
  -(∑ i ∈ S, ∫ x in rankCut D i.val..rankCut D (i.val + 1), phi x)

/-- All centered activation of a candidate set is bounded by filling its remaining
mass against the right endpoint z, with its initial prefix fixed. -/
theorem centeredBlock_packing (D : Fin n → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hDsum : ∑ i, D i = 1) (S : Finset (Fin n)) (phi : ℝ → ℝ)
    (hcont : ContinuousOn phi (Icc 0 1)) (hanti : AntitoneOn phi (Icc 0 1))
    (p q z : ℝ) (hp : p = ∑ i ∈ S, D i)
    (hq : q = rankCut D (prefixBoundary S))
    (hz : rankCut D (lastIndex S) ≤ z) (hz1 : z ≤ 1) :
    centeredBlock D S phi ≤
      curvePrimitive phi (z - p + q) - curvePrimitive phi z - curvePrimitive phi q := by
  have hq0 : 0 ≤ q := by rw [hq]; exact (rankCut_mem_Icc D hD hDsum _).1
  have hqp : q ≤ p := by rw [hq, hp]; exact prefixCut_le_mass D hD S
  have hpz : p ≤ z := by rw [hp]; exact le_trans (mass_le_lastCut D hD S) hz
  have hqz : q ≤ z := le_trans hqp hpz
  have hz0 : 0 ≤ z := le_trans hq0 hqz
  have hcq : q ≤ z - p + q := by linarith
  have hcz : z - p + q ≤ z := by linarith
  have hc0 : 0 ≤ z - p + q := le_trans hq0 hcq
  have hphi : IntervalIntegrable phi volume 0 1 := hcont.intervalIntegrable_of_Icc (by norm_num)
  have hint (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :=
    intervalIntegrable_on_subinterval hphi (by norm_num) ha hab hb
  have hoccint (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
      IntervalIntegrable (fun x => occupation D S x * phi x) volume a b := by
    apply (occupation_integrable D S a b).mul_continuousOn
    rw [uIcc_of_le hab]
    exact hcont.mono (Icc_subset_Icc ha hb)
  have hpack := pack_right_antitone phi (occupation D S) q (z - p + q) z hcq hcz
    (hcont.mono (Icc_subset_Icc hq0 hz1))
    (hanti.mono (Icc_subset_Icc hq0 hz1)) (occupation_integrable D S q z)
    (fun x _ => ⟨occupation_nonneg D S x, occupation_le_one D hD hDsum S x⟩)
    (by rw [occupation_middle_mass D hD hDsum S q z hq hz hz1, ← hp]; ring)
  have hleft : (∫ x in (0 : ℝ)..q, occupation D S x * phi x) = curvePrimitive phi q := by
    apply intervalIntegral.integral_congr_Ioo_of_le hq0
    intro x hx
    change occupation D S x * phi x = phi x
    rw [occupation_prefix_one D hD hDsum S x hx.1 (hq ▸ hx.2.le), one_mul]
  have hright : (∫ x in z..1, occupation D S x * phi x) = 0 := by
    calc
      _ = ∫ _x in z..(1 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hz1
        intro x hx
        change occupation D S x * phi x = 0
        rw [occupation_zero_above_last D hD S x (lt_of_le_of_lt hz hx.1), zero_mul]
      _ = 0 := by simp
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
    (hoccint 0 q le_rfl hq0 (le_trans hqz hz1)) (hoccint q z hq0 hqz hz1)
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
    (hoccint 0 z le_rfl hz0 hz1) (hoccint z 1 hz0 hz1 le_rfl)
  have htop := intervalIntegral.integral_add_adjacent_intervals
    (hint 0 (z - p + q) le_rfl hc0 (le_trans hcz hz1))
    (hint (z - p + q) z hc0 hcz hz1)
  have hblock := occupation_weighted_integral D hD hDsum S phi hcont
  unfold centeredBlock curvePrimitive at *
  linarith

end
end OptimalG
end

-- Source module OccupationPacking
section
set_option autoImplicit true
namespace StableVotingDistortion
open OptimalG Set MeasureTheory

/-- Occupation form of (36), allowing zero-width intervals anywhere in the ordering.
The assumptions directly express that the prefix is filled and that no mass lies above z. -/
theorem packing_with_zero_blocks {n : ℕ} [Nonempty (Fin n)] (D : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ D i) (ht : ∑ i, D i=1) (S : Finset (Fin n)) (ϕ : ℝ → ℝ)
    (hc : ContinuousOn ϕ (Icc 0 1)) (ha : AntitoneOn ϕ (Icc 0 1)) (p q z : ℝ)
    (hp : p=∑ i ∈ S,D i) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hl : ∀ i, i ∉ S → q ≤ rankCut D i.val)
    (hr : ∀ i ∈ S, 0 < D i → rankCut D (i.val+1) ≤ z) :
    centeredBlock D S ϕ ≤ curvePrimitive ϕ (z-p+q)-curvePrimitive ϕ z-curvePrimitive ϕ q := by
  classical
  have left (x : ℝ) (hx : 0<x) (hxq : x ≤ q) : occupation D S x=1 := by
    have h := occupation_univ D hd ht x
    have e : occupation D S x = occupation D Finset.univ x := by
      unfold occupation
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have hx' : ¬rankCut D i.val < x := not_lt.mpr (hxq.trans (hl i hi))
      simp [intervalOccupation,Set.indicator,hx']
    rw [e,h]; simp [intervalOccupation,Set.indicator,hx,hxq.trans hq1]
  have right (x : ℝ) (hx : z<x) : occupation D S x=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hz : D i=0
    · rw [rankCut_succ, hz, add_zero]; simp [intervalOccupation]
    · have hh := hr i hi (lt_of_le_of_ne (hd i) (Ne.symm hz))
      simp [intervalOccupation,Set.indicator,not_le.mpr (hh.trans_lt hx)]
  have qz : q ≤ z := by
    by_contra! hn
    linarith [left q (hz0.trans_lt hn) le_rfl,right q hn]
  have hleft : (∫ x in (0:ℝ)..q,occupation D S x)=q := by
    calc
      _ = ∫ _x in (0:ℝ)..q,(1:ℝ) := intervalIntegral.integral_congr_Ioo_of_le hq0 (fun x hx => left x hx.1 hx.2.le)
      _ = _ := by simp
  have hright : (∫ x in z..1,occupation D S x)=0 := by
    calc
      _ = ∫ _x in z..1,(0:ℝ) := intervalIntegral.integral_congr_Ioo_of_le hz1 (fun x hx => right x hx.1)
      _ = _ := by simp
  have htot := occupation_mass D hd ht S
  have hj := intervalIntegral.integral_add_adjacent_intervals (occupation_integrable D S 0 q) (occupation_integrable D S q z)
  have hk := intervalIntegral.integral_add_adjacent_intervals (occupation_integrable D S 0 z) (occupation_integrable D S z 1)
  have hm : (∫ x in q..z,occupation D S x)=p-q := by linarith
  have hlo := intervalIntegral.integral_nonneg_of_forall (μ := volume) qz (occupation_nonneg D S)
  have hhi := intervalIntegral.integral_mono_on qz (occupation_integrable D S q z) (intervalIntegrable_const (c:=1))
    (fun x _ => occupation_le_one D hd ht S x)
  rw [hm] at hlo hhi
  simp only [intervalIntegral.integral_const,smul_eq_mul,mul_one] at hhi
  have hq' : q ≤ z-p+q := by linarith
  have hz' : z-p+q ≤ z := by linarith
  have har : 0 ≤ z-p+q := hq0.trans hq'
  have hi (a b : ℝ) (ha0 : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :=
    (hc.mono (Icc_subset_Icc ha0 hb)).intervalIntegrable_of_Icc (μ:=volume) hab
  have hI (a b : ℝ) (ha0 : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
      IntervalIntegrable (fun x => occupation D S x*ϕ x) volume a b := by
    apply (occupation_integrable D S a b).mul_continuousOn
    rw [uIcc_of_le hab]
    exact hc.mono (Icc_subset_Icc ha0 hb)
  have hpack := pack_right_antitone ϕ (occupation D S) q (z-p+q) z hq' hz'
    (hc.mono (Icc_subset_Icc hq0 hz1)) (ha.mono (Icc_subset_Icc hq0 hz1))
    (occupation_integrable D S q z) (fun x _ => ⟨occupation_nonneg D S x,occupation_le_one D hd ht S x⟩)
    (by rw [hm]; ring)
  have left' : (∫ x in (0:ℝ)..q,occupation D S x*ϕ x)=curvePrimitive ϕ q := by
    apply intervalIntegral.integral_congr_Ioo_of_le hq0
    intro x hx; change occupation D S x*ϕ x=ϕ x; rw [left x hx.1 hx.2.le,one_mul]
  have right' : (∫ x in z..1,occupation D S x*ϕ x)=0 := by
    calc
      _ = ∫ _x in z..1,(0:ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hz1
        intro x hx; change occupation D S x*ϕ x=0;rw [right x hx.1,zero_mul]
      _ = _ := by simp
  have h1 := intervalIntegral.integral_add_adjacent_intervals (hI 0 q le_rfl hq0 hq1) (hI q z hq0 qz hz1)
  have h2 := intervalIntegral.integral_add_adjacent_intervals (hI 0 z le_rfl hz0 hz1) (hI z 1 hz0 hz1 le_rfl)
  have h3 := intervalIntegral.integral_add_adjacent_intervals (hi 0 (z-p+q) le_rfl har (hz'.trans hz1)) (hi (z-p+q) z har hz' hz1)
  have hb := occupation_weighted_integral D hd ht S ϕ hc
  unfold centeredBlock curvePrimitive at *
  linarith

end StableVotingDistortion
end

-- Source module RankBridge
section
set_option autoImplicit true
/-! Identification of the strict-order ballot and the rank integrals in the two formalisms. -/
namespace StableVotingDistortion
open PctDistortion OptimalG

variable {V C : Type} [Fintype C]

/-- Enumerate a voter's ballot from worst to best. -/
theorem exists_ballot (E : PctDistortion.Election V C) (v : V) :
    ∃ order : Fin (Fintype.card C) ≃ C, ∀ i j, E.prefers v (order i) (order j) ↔ j < i := by
  classical
  let : IsStrictTotalOrder C (E.prefers v) := E.isStrictTotalOrder v
  let : LinearOrder C := linearOrderOfSTO (E.prefers v)
  let e := Fintype.orderIsoFinOfCardEq C rfl
  refine ⟨Fin.revPerm.trans e.toEquiv, fun i j => ?_⟩
  change e i.rev < e j.rev ↔ j < i
  rw [e.lt_iff_lt, Fin.rev_lt_rev]

variable (E : PctDistortion.Election V C) (D : C → ℝ) (v : V)
variable (order : Fin (Fintype.card C) ≃ C)
variable (hr : ∀ i j, E.prefers v (order i) (order j) ↔ j < i)

include hr in
theorem leftRank_eq_rankCut (a : C) :
    leftRank E D v a = rankCut (fun i => D (order i)) (order.symm a).val := by
  classical
  simp only [leftRank, Finset.sum_filter, rankCut]
  rw [← Equiv.sum_comp order]
  apply Finset.sum_congr rfl
  intro i _
  have hp : E.prefers v a (order i) ↔ i.val < (order.symm a).val := by
    simpa only [Equiv.apply_symm_apply, Fin.lt_def] using hr (order.symm a) i
  by_cases h : i.val < (order.symm a).val <;> simp [hp, h]

include hr in
theorem activation_eq_ordered (g : ℝ → ℝ) (a : C) :
    activation g E D v a = orderedActivation g D order a := by
  let w := fun i => D (order i)
  let j := order.symm a
  have hj : w j = D a := by simp [w, j]
  have hleft := leftRank_eq_rankCut E D v order hr a
  change leftRank E D v a = rankCut w j.val at hleft
  change activation g E D v a = rankActivation g w j
  unfold activation
  by_cases h : D a = 0
  · rw [if_pos h, hleft, rankActivation_of_mass_zero g w j (hj.trans h)]
  · rw [if_neg h, hleft]
    have hmul := mass_mul_rankActivation g w j
    rw [rankCut_succ, hj] at hmul
    rw [← hmul, ← mul_assoc, inv_mul_cancel₀ h, one_mul]

end StableVotingDistortion
end

-- Source module SlicePacking
section
set_option autoImplicit true
namespace StableVotingDistortion
open PctDistortion Set
theorem eq_36 {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C)
    {lam : ℝ} {ϕ : ℝ → ℝ} (hϕ : IsScoreFunction lam ϕ)
    {D ρ : C → ℝ} (hD : D ∈ stdSimplex ℝ C) (hρ : ∀ b, 0 ≤ ρ b) {aStar : C} (hstar : ρ aStar = 0)
    {t : ℝ} (ht : 0 ≤ t) (v : V) :
    kv E D ρ ϕ v t ≤ deltaP ϕ (pt D ρ t) (qv E D ρ v t) ∧
      ∀ z, zv E D ρ v t ≤ z → z ≤ 1 → kv E D ρ ϕ v t ≤ KP ϕ (pt D ρ t) (qv E D ρ v t) z := by
  classical
  obtain ⟨e,he⟩ := exists_ballot E v
  let S := (St ρ t).map e.symm.toEmbedding
  let w := fun i => D (e i)
  have w0 (i) : 0 ≤ w i := hD.1 _
  have w1 : ∑ i,w i=1 := (e.sum_comp D).trans hD.2
  have hcut (i) : leftRank E D v (e i) = OptimalG.rankCut w i.val := by
    simpa [w] using leftRank_eq_rankCut E D v e he (e i)
  have hend (i) : leftRank E D v (e i)+D (e i) = OptimalG.rankCut w (i.val+1) := by
    rw [hcut, OptimalG.rankCut_succ]
  have hmem (i) : i ∈ S ↔ e i ∈ St ρ t := Finset.mem_map_equiv
  have hmass : pt D ρ t = ∑ i ∈ S, w i := by simp [pt,S,w,Finset.sum_map]
  have hb : kv E D ρ ϕ v t = OptimalG.centeredBlock w S ϕ := by
    unfold kv blockScore OptimalG.centeredBlock
    simp only [intervalIntegral.integral_neg,Finset.sum_neg_distrib,neg_inj]
    rw [show (∑ i ∈ S, ∫ x in OptimalG.rankCut w i.val..OptimalG.rankCut w (i.val+1), ϕ x) =
      ∑ c ∈ St ρ t, ∫ x in OptimalG.rankCut w (e.symm c).val..OptimalG.rankCut w ((e.symm c).val+1), ϕ x by simp [S,Finset.sum_map]]
    apply Finset.sum_congr rfl
    intro c _
    simpa using congrArg₂ (fun a b : ℝ => ∫ x in a..b,ϕ x) (hcut (e.symm c)) (hend (e.symm c))
  let bad := Finset.univ.filter (fun c => c ∉ St ρ t)
  have hstar' : aStar ∈ bad := by simpa [bad,St,hstar] using ht
  have hq0 : 0 ≤ qv E D ρ v t := by
    unfold qv;rw [dif_pos ⟨_,hstar'⟩]
    apply Finset.le_inf';intro c _
    exact Finset.sum_nonneg fun b _ => hD.1 b
  have left (i) (h : i ∉ S) : qv E D ρ v t ≤ OptimalG.rankCut w i.val := by
    rw [← hcut]
    unfold qv;rw [dif_pos ⟨_,hstar'⟩]
    exact Finset.inf'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun hi => h ((hmem i).mpr hi)⟩)
  have hq1 : qv E D ρ v t ≤ 1 := by
    have hn : e.symm aStar ∉ S := by simpa [S] using (Finset.mem_filter.mp hstar').2
    exact (left _ hn).trans (OptimalG.rankCut_mem_Icc w w0 w1 _).2
  let good := Finset.univ.filter (fun b => b ∈ St ρ t ∧ 0<D b)
  have hr (i) (hi : i ∈ S) (hpos : 0<w i) : OptimalG.rankCut w (i.val+1) ≤ zv E D ρ v t := by
    have hh : e i ∈ good := Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hmem i).mp hi,hpos⟩
    rw [← hend]
    unfold zv;rw [dif_pos ⟨_,hh⟩]
    exact Finset.le_sup' (fun b => leftRank E D v b + D b) hh
  have hu : zv E D ρ v t ∈ Icc 0 1 := by
    unfold zv
    split_ifs with hn
    · constructor
      · obtain ⟨c,hc⟩ := hn
        apply le_trans _ (Finset.le_sup' _ hc)
        exact add_nonneg (Finset.sum_nonneg fun b _ => hD.1 b) (hD.1 c)
      · apply Finset.sup'_le;intro c _
        simpa [← hend] using (OptimalG.rankCut_mem_Icc w w0 w1 ((e.symm c).val+1)).2
    · norm_num
  have hK (z : ℝ) (hz : zv E D ρ v t ≤ z) (hz1 : z ≤ 1) :
      kv E D ρ ϕ v t ≤ KP ϕ (pt D ρ t) (qv E D ρ v t) z := by
    rw [hb]
    exact packing_with_zero_blocks w w0 w1 S ϕ hϕ.continuousOn hϕ.antitoneOn _ _ z hmass hq0 hq1
      (hu.1.trans hz) hz1 left (fun i hi hp => (hr i hi hp).trans hz)
  refine ⟨?_,hK⟩
  simpa [KP,deltaP,J,hϕ.integral_eq_zero] using hK 1 hu.2 le_rfl

end StableVotingDistortion
end

open PctDistortion
open StableVotingDistortion

theorem solution :
    ∀ {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C)
    {lam : ℝ} {ϕ : ℝ → ℝ} (hϕ : IsScoreFunction lam ϕ)
    {D ρ : C → ℝ} (hD : D ∈ stdSimplex ℝ C) (hρ : ∀ b, 0 ≤ ρ b) {aStar : C} (hstar : ρ aStar = 0)
    {t : ℝ} (ht : 0 ≤ t) (v : V),
    kv E D ρ ϕ v t ≤ deltaP ϕ (pt D ρ t) (qv E D ρ v t) ∧
      ∀ z, zv E D ρ v t ≤ z → z ≤ 1 → kv E D ρ ϕ v t ≤ KP ϕ (pt D ρ t) (qv E D ρ v t) z :=
  @StableVotingDistortion.eq_36
