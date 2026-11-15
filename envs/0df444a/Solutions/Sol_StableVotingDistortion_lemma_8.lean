-- Prove2me | solution 1 for StableVotingDistortion.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T12:02:56.975452+00:00
-- url     : https://prove2.me/submissions/8b94de7d-8e85-4c81-a43e-2afab4e6942f

import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_HasDistortionAtMost
import Definitions.Def_StableVotingDistortion_IsGStable
import Definitions.Def_StableVotingDistortion_VerifierHypotheses
import Definitions.Def_StableVotingDistortion_activation
import Definitions.Def_StableVotingDistortion_scorePrimitives
import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Theorems.Thm_StableVotingDistortion_gPhi_properties
import Theorems.Thm_StableVotingDistortion_theorem_4

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

-- Source module OptimalG.Election
section
set_option autoImplicit true
/-!
# Finite elections and the actual worst-case distortion

Elections have nonempty finite voter and candidate sets, represented by `Fin` types,
with equally weighted voters. A ranking is a permutation listed from worst to best.
Metrics are arbitrary pseudometrics on the disjoint union of voters and candidates.
This includes co-located points and zero optimal social cost.
-/

namespace OptimalG

open Set MeasureTheory
open scoped BigOperators ENNReal

structure Lottery (m : ℕ) where
  weight : Fin m → ℝ
  nonneg : ∀ a, 0 ≤ weight a
  total : ∑ a, weight a = 1

structure Election where
  voterCount : ℕ
  candidateCount : ℕ
  voters_pos : 0 < voterCount
  candidates_pos : 0 < candidateCount
  order : Fin voterCount → Equiv.Perm (Fin candidateCount)

namespace Election

abbrev Voter (E : Election) := Fin E.voterCount
abbrev Candidate (E : Election) := Fin E.candidateCount
abbrev Point (E : Election) := E.Voter ⊕ E.Candidate
abbrev Metric (E : Election) := PseudoMetricSpace E.Point

instance candidateCount_neZero (E : Election) : NeZero E.candidateCount :=
  ⟨Nat.ne_of_gt E.candidates_pos⟩

instance voterCount_neZero (E : Election) : NeZero E.voterCount :=
  ⟨Nat.ne_of_gt E.voters_pos⟩

noncomputable def voterWeight (E : Election) (_v : E.Voter) : ℝ :=
  1 / E.voterCount

theorem voterWeight_nonneg (E : Election) (v : E.Voter) : 0 ≤ E.voterWeight v := by
  exact div_nonneg (by norm_num) (Nat.cast_nonneg _)

theorem voterWeight_total (E : Election) : ∑ v, E.voterWeight v = 1 := by
  have hn : (E.voterCount : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt E.voters_pos
  simp [voterWeight, hn]

def ordinalRank (E : Election) (v : E.Voter) (a : E.Candidate) : ℕ :=
  ((E.order v).symm a).val

noncomputable def activation (E : Election) (g : ℝ → ℝ)
    (D : Lottery E.candidateCount) (v : E.Voter) (a : E.Candidate) : ℝ :=
  orderedActivation g D.weight (E.order v) a

def Stable (E : Election) (g : ℝ → ℝ) (D : Lottery E.candidateCount) : Prop :=
  ∀ a, expectation E.voterWeight (fun v => E.activation g D v a) ≤
    ∫ r in (0 : ℝ)..1, g r

theorem supported_stationarity (E : Election) (g : ℝ → ℝ)
    (D : Lottery E.candidateCount) (hg : ContinuousOn g (Icc 0 1))
    (hstable : E.Stable g D) (a : E.Candidate) (ha : 0 < D.weight a) :
    expectation E.voterWeight (fun v => E.activation g D v a) =
      ∫ r in (0 : ℝ)..1, g r := by
  exact OptimalG.supported_stationarity g D.weight E.voterWeight E.order hg
    D.nonneg D.total E.voterWeight_total hstable a ha

def Consistent (E : Election) (d : E.Metric) : Prop :=
  letI := d
  ∀ v b c, E.ordinalRank v c ≤ E.ordinalRank v b →
    dist (Sum.inl v) (Sum.inr b) ≤ dist (Sum.inl v) (Sum.inr c)

noncomputable def candidateCost (E : Election) (d : E.Metric) (a : E.Candidate) : ℝ :=
  letI := d
  expectation E.voterWeight (fun v => dist (Sum.inl v) (Sum.inr a))

noncomputable def lotteryCost (E : Election) (d : E.Metric)
    (D : Lottery E.candidateCount) : ℝ := expectation D.weight (E.candidateCost d)

theorem candidateCost_nonneg (E : Election) (d : E.Metric) (a : E.Candidate) :
    0 ≤ E.candidateCost d a := by
  letI := d
  unfold candidateCost expectation
  exact Finset.sum_nonneg (fun v _ => mul_nonneg (E.voterWeight_nonneg v)
    (dist_nonneg (x := (Sum.inl v : E.Point)) (y := Sum.inr a)))

theorem lotteryCost_nonneg (E : Election) (d : E.Metric) (D : Lottery E.candidateCount) :
    0 ≤ E.lotteryCost d D := by
  unfold lotteryCost expectation
  exact Finset.sum_nonneg (fun a _ => mul_nonneg (D.nonneg a) (E.candidateCost_nonneg d a))

theorem lotteryCost_eq_voter_average (E : Election) (d : E.Metric)
    (D : Lottery E.candidateCount) :
    E.lotteryCost d D =
      letI := d
      expectation E.voterWeight
        (fun v => expectation D.weight (fun a => dist (Sum.inl v) (Sum.inr a))) := by
  letI := d
  exact expectation_commute E.voterWeight D.weight _

end Election

/-- The paper's class of continuous activations into `[0,1]`. Values outside
that interval are immaterial because all rank arguments lie inside it. -/
def AdmissibleActivation (g : ℝ → ℝ) : Prop :=
  ContinuousOn g (Icc 0 1) ∧ MapsTo g (Icc 0 1) (Icc 0 1)

/-- Extended ratio with the usual harmless convention 0/0=1 and positive/0=∞. -/
noncomputable def costRatio (cost optimum : ℝ) : ℝ≥0∞ :=
  if optimum = 0 then (if cost = 0 then 1 else ⊤) else ENNReal.ofReal (cost / optimum)

theorem costRatio_le_iff (cost optimum K : ℝ)
    (hc : 0 ≤ cost) (ho : 0 ≤ optimum) (hK : 1 ≤ K) :
    costRatio cost optimum ≤ ENNReal.ofReal K ↔ cost ≤ K * optimum := by
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  by_cases hopt : optimum = 0
  · subst optimum
    by_cases hcost : cost = 0
    · subst cost
      have hk : (1 : ℝ≥0∞) ≤ ENNReal.ofReal K := by
        simpa using ENNReal.ofReal_le_ofReal hK
      simp [costRatio, hk]
    · have hcostpos : 0 < cost := lt_of_le_of_ne hc (Ne.symm hcost)
      simp [costRatio, hcost, not_le.mpr hcostpos]
  · have hoptpos : 0 < optimum := lt_of_le_of_ne ho (Ne.symm hopt)
    simp only [costRatio, if_neg hopt]
    rw [ENNReal.ofReal_le_ofReal_iff hK0, div_le_iff₀ hoptpos]

/-- Worst distortion over every stable lottery in every finite equally weighted election.
The extra supremum over reference candidates takes the minimum social cost in the denominator. -/
noncomputable def maximumDistortion (g : ℝ → ℝ) : ℝ≥0∞ :=
  ⨆ (E : Election) (D : Lottery E.candidateCount) (_ : E.Stable g D)
    (d : E.Metric) (_ : E.Consistent d) (a : E.Candidate),
    costRatio (E.lotteryCost d D) (E.candidateCost d a)

/-- The zero-denominator-safe form of the universal upper bound. -/
def UniversalBound (g : ℝ → ℝ) (K : ℝ) : Prop :=
  ∀ (E : Election) (D : Lottery E.candidateCount), E.Stable g D →
    ∀ d : E.Metric, E.Consistent d → ∀ a : E.Candidate,
      E.lotteryCost d D ≤ K * E.candidateCost d a

theorem maximumDistortion_le_iff (g : ℝ → ℝ) (K : ℝ) (hK : 1 ≤ K) :
    maximumDistortion g ≤ ENNReal.ofReal K ↔ UniversalBound g K := by
  simp only [maximumDistortion, iSup_le_iff, UniversalBound]
  apply forall_congr'
  intro E
  apply forall_congr'
  intro D
  apply forall_congr'
  intro _hstable
  apply forall_congr'
  intro d
  apply forall_congr'
  intro _hconsistent
  apply forall_congr'
  intro a
  exact costRatio_le_iff _ _ K (E.lotteryCost_nonneg d D) (E.candidateCost_nonneg d a) hK

/-- A concrete finite election witnessing a strict distortion lower bound. -/
def WitnessAbove (g : ℝ → ℝ) (K : ℝ) : Prop :=
  ∃ (E : Election) (D : Lottery E.candidateCount), E.Stable g D ∧
    ∃ d : E.Metric, E.Consistent d ∧ ∃ a : E.Candidate,
      0 < E.candidateCost d a ∧ K * E.candidateCost d a < E.lotteryCost d D

theorem witnessAbove_not_universalBound (g : ℝ → ℝ) (K : ℝ)
    (hw : WitnessAbove g K) : ¬ UniversalBound g K := by
  rintro hbound
  rcases hw with ⟨E, D, hstable, d, hconsistent, a, _hpos, hstrict⟩
  exact (not_lt_of_ge (hbound E D hstable d hconsistent a)) hstrict

theorem witnessAbove_mono (g : ℝ → ℝ) (K L : ℝ) (hLK : L ≤ K)
    (hw : WitnessAbove g K) : WitnessAbove g L := by
  rcases hw with ⟨E, D, hstable, d, hconsistent, a, hpos, hstrict⟩
  refine ⟨E, D, hstable, d, hconsistent, a, hpos, ?_⟩
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hLK hpos.le) hstrict

end OptimalG
end

-- Source module OptimalG.Activation
section
set_option autoImplicit true
/-!
# Normalizing a completed centered activation

The final normalization in Section 5.3 is verified here. The existence of the
completed curve is NOT assumed globally: each theorem explicitly takes the
necessary regularity, monotonicity, endpoint, or integral hypotheses. All
regularity hypotheses concern the actual interval `[0,1]`.
-/

namespace OptimalG

open Set MeasureTheory

/-- Normalization used in Section 5.3 of the manuscript. -/
noncomputable def normalizedActivation (phi : ℝ → ℝ) (r : ℝ) : ℝ :=
  (phi 0 - phi r) / (1 + phi 0)

theorem normalization_denominator_pos {phi : ℝ → ℝ}
    (hanti : StrictAntiOn phi (Icc 0 1)) (hend : phi 1 = -1) :
    0 < 1 + phi 0 := by
  have h := hanti (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show (0 : ℝ) < 1 by norm_num)
  rw [hend] at h
  linarith

theorem normalizedActivation_continuousOn {phi : ℝ → ℝ}
    (hcont : ContinuousOn phi (Icc 0 1)) :
    ContinuousOn (normalizedActivation phi) (Icc 0 1) := by
  exact (continuousOn_const.sub hcont).div_const (1 + phi 0)

theorem normalizedActivation_strictMonoOn {phi : ℝ → ℝ}
    (hanti : StrictAntiOn phi (Icc 0 1)) (hend : phi 1 = -1) :
    StrictMonoOn (normalizedActivation phi) (Icc 0 1) := by
  intro x hx y hy hxy
  have hden := normalization_denominator_pos hanti hend
  have h := hanti hx hy hxy
  dsimp [normalizedActivation]
  exact (div_lt_div_iff_of_pos_right hden).mpr (by linarith)

@[simp] theorem normalizedActivation_zero (phi : ℝ → ℝ) :
    normalizedActivation phi 0 = 0 := by
  simp [normalizedActivation]

theorem normalizedActivation_one {phi : ℝ → ℝ}
    (hanti : StrictAntiOn phi (Icc 0 1)) (hend : phi 1 = -1) :
    normalizedActivation phi 1 = 1 := by
  have hden := ne_of_gt (normalization_denominator_pos hanti hend)
  dsimp [normalizedActivation]
  rw [hend]
  convert div_self hden using 1
  ring

theorem normalizedActivation_mem_Icc {phi : ℝ → ℝ}
    (hanti : StrictAntiOn phi (Icc 0 1)) (hend : phi 1 = -1)
    {r : ℝ} (hr : r ∈ Icc 0 1) : normalizedActivation phi r ∈ Icc 0 1 := by
  have hmono := (normalizedActivation_strictMonoOn hanti hend).monotoneOn
  constructor
  · have h := hmono (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) hr hr.1
    simpa using h
  · have h := hmono hr (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) hr.2
    simpa [normalizedActivation_one hanti hend] using h

/-- Zero mean of the centered curve gives exactly the stated activation mean. -/
theorem normalizedActivation_integral {phi : ℝ → ℝ}
    (hcont : ContinuousOn phi (Icc 0 1))
    (hzero : (∫ r in (0 : ℝ)..1, phi r) = 0) :
    (∫ r in (0 : ℝ)..1, normalizedActivation phi r) = phi 0 / (1 + phi 0) := by
  have hint : IntervalIntegrable phi volume 0 1 :=
    hcont.intervalIntegrable_of_Icc (by norm_num)
  simp only [normalizedActivation, intervalIntegral.integral_div]
  rw [intervalIntegral.integral_sub intervalIntegrable_const hint]
  simp [hzero]

/-- The rescaling recovers the original centered curve pointwise. -/
theorem centered_normalizedActivation {phi : ℝ → ℝ}
    (hanti : StrictAntiOn phi (Icc 0 1)) (hend : phi 1 = -1) (r : ℝ) :
    (1 + phi 0) * (phi 0 / (1 + phi 0) - normalizedActivation phi r) = phi r := by
  have hden := ne_of_gt (normalization_denominator_pos hanti hend)
  dsimp [normalizedActivation]
  field_simp
  ring

/-- Complete verified normalization, conditional on a completed centered curve.
This packages no variational or numerical claims into its premises. -/
theorem completed_curve_yields_activation {phi : ℝ → ℝ}
    (hcont : ContinuousOn phi (Icc 0 1))
    (hanti : StrictAntiOn phi (Icc 0 1))
    (hend : phi 1 = -1)
    (hzero : (∫ r in (0 : ℝ)..1, phi r) = 0) :
    ContinuousOn (normalizedActivation phi) (Icc 0 1) ∧
    StrictMonoOn (normalizedActivation phi) (Icc 0 1) ∧
    normalizedActivation phi 0 = 0 ∧
    normalizedActivation phi 1 = 1 ∧
    (∀ r ∈ Icc (0 : ℝ) 1, normalizedActivation phi r ∈ Icc 0 1) ∧
    (∫ r in (0 : ℝ)..1, normalizedActivation phi r) = phi 0 / (1 + phi 0) := by
  exact ⟨normalizedActivation_continuousOn hcont,
    normalizedActivation_strictMonoOn hanti hend,
    normalizedActivation_zero phi,
    normalizedActivation_one hanti hend,
    fun _ hr => normalizedActivation_mem_Icc hanti hend hr,
    normalizedActivation_integral hcont hzero⟩

end OptimalG
end

-- Source module OptimalG.CenteredStability
section
set_option autoImplicit true
/-! Exact consequences of stability for the normalized centered curve. -/

namespace OptimalG

open Set MeasureTheory
open scoped BigOperators

theorem rankIntegrand_integrable {n : ℕ} (f : ℝ → ℝ) (D : Fin n → ℝ)
    (hf : ContinuousOn f (Icc 0 1)) (hD : ∀ i, 0 ≤ D i)
    (hDsum : ∑ i, D i = 1) (i : Fin n) :
    IntervalIntegrable (fun u : ℝ => f (rankCut D i.val + u * D i)) volume 0 1 := by
  have hcoord : Continuous (fun u : ℝ => rankCut D i.val + u * D i) := by fun_prop
  apply (hf.comp hcoord.continuousOn ?_).intervalIntegrable_of_Icc (by norm_num)
  intro u hu
  have hr := rankCut_mem_Icc D hD hDsum i.val
  have hrend := (rankCut_mem_Icc D hD hDsum (i.val + 1)).2
  rw [rankCut_succ] at hrend
  constructor
  · exact add_nonneg hr.1 (mul_nonneg hu.1 (hD i))
  · have hmul := mul_le_mul_of_nonneg_right hu.2 (hD i)
    linarith

theorem rankActivation_normalized {n : ℕ} (phi : ℝ → ℝ) (D : Fin n → ℝ)
    (hphi : ContinuousOn phi (Icc 0 1)) (hD : ∀ i, 0 ≤ D i)
    (hDsum : ∑ i, D i = 1) (i : Fin n) :
    rankActivation (normalizedActivation phi) D i =
      (phi 0 - rankActivation phi D i) / (1 + phi 0) := by
  unfold rankActivation normalizedActivation
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_sub intervalIntegrable_const
      (rankIntegrand_integrable phi D hphi hD hDsum i)]
  simp

theorem orderedActivation_normalized {C : Type*} [Fintype C] {n : ℕ}
    (phi : ℝ → ℝ) (D : C → ℝ) (order : Fin n ≃ C)
    (hphi : ContinuousOn phi (Icc 0 1)) (hD : ∀ a, 0 ≤ D a) (hDsum : ∑ a, D a = 1)
    (a : C) :
    orderedActivation (normalizedActivation phi) D order a =
      (phi 0 - orderedActivation phi D order a) / (1 + phi 0) := by
  have hsum : ∑ i, D (order i) = 1 := by simpa only [Equiv.sum_comp] using hDsum
  exact rankActivation_normalized phi (fun i => D (order i)) hphi
    (fun i => hD (order i)) hsum (order.symm a)

theorem expectation_sub_const_div {V : Type*} [Fintype V]
    (w f : V → ℝ) (c d : ℝ) (hw : ∑ v, w v = 1) :
    expectation w (fun v => (c - f v) / d) = (c - expectation w f) / d := by
  unfold expectation
  simp_rw [← mul_div_assoc, mul_sub]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul, hw, one_mul]

namespace Election

theorem mean_normalized_activation (E : Election) (phi : ℝ → ℝ)
    (D : Lottery E.candidateCount) (hphi : ContinuousOn phi (Icc 0 1)) (a : E.Candidate) :
    expectation E.voterWeight (fun v => E.activation (normalizedActivation phi) D v a) =
      (phi 0 - expectation E.voterWeight (fun v => E.activation phi D v a)) / (1 + phi 0) := by
  simp only [activation, orderedActivation_normalized phi D.weight _ hphi D.nonneg D.total]
  exact expectation_sub_const_div _ _ _ _ E.voterWeight_total

theorem stable_centered_nonnegative (E : Election) (phi : ℝ → ℝ)
    (D : Lottery E.candidateCount) (hphi : ContinuousOn phi (Icc 0 1))
    (hanti : AntitoneOn phi (Icc 0 1)) (hden0 : 0 < 1 + phi 0)
    (hzero : (∫ r in (0 : ℝ)..1, phi r) = 0)
    (hs : E.Stable (normalizedActivation phi) D) (a : E.Candidate) :
    0 ≤ expectation E.voterWeight (fun v => E.activation phi D v a) := by
  have h := hs a
  rw [mean_normalized_activation E phi D hphi a,
    normalizedActivation_integral hphi hzero] at h
  have hh := (div_le_div_iff_of_pos_right hden0).mp h
  linarith

theorem stable_centered_supported (E : Election) (phi : ℝ → ℝ)
    (D : Lottery E.candidateCount) (hphi : ContinuousOn phi (Icc 0 1))
    (hanti : AntitoneOn phi (Icc 0 1)) (hden0 : 0 < 1 + phi 0)
    (hzero : (∫ r in (0 : ℝ)..1, phi r) = 0)
    (hs : E.Stable (normalizedActivation phi) D) (a : E.Candidate) (ha : 0 < D.weight a) :
    expectation E.voterWeight (fun v => E.activation phi D v a) = 0 := by
  have h := E.supported_stationarity (normalizedActivation phi) D
    (normalizedActivation_continuousOn hphi) hs a ha
  rw [mean_normalized_activation E phi D hphi a,
    normalizedActivation_integral hphi hzero] at h
  have hden := ne_of_gt hden0
  have hh := (div_left_inj' hden).mp h
  linarith

noncomputable def leftRank (E : Election) (D : Lottery E.candidateCount)
    (v : E.Voter) (a : E.Candidate) : ℝ :=
  rankCut (fun i => D.weight (E.order v i)) ((E.order v).symm a).val

theorem leftRank_mem_Icc (E : Election) (D : Lottery E.candidateCount)
    (v : E.Voter) (a : E.Candidate) : E.leftRank D v a ∈ Icc 0 1 := by
  apply rankCut_mem_Icc _ (fun i => D.nonneg (E.order v i))
  simpa only [Equiv.sum_comp] using D.total

/-- The left endpoint of a decreasing curve dominates its candidate-interval average. -/
theorem centered_average_le_left (E : Election) (phi : ℝ → ℝ)
    (D : Lottery E.candidateCount) (hphi : ContinuousOn phi (Icc 0 1))
    (hanti : AntitoneOn phi (Icc 0 1)) (v : E.Voter) (a : E.Candidate) :
    E.activation phi D v a ≤ phi (E.leftRank D v a) := by
  let F : Fin E.candidateCount → ℝ := fun i => D.weight (E.order v i)
  let i := (E.order v).symm a
  have hF : ∀ j, 0 ≤ F j := fun j => D.nonneg (E.order v j)
  have hsum : ∑ j, F j = 1 := by simpa only [F, Equiv.sum_comp] using D.total
  have hleft := rankCut_mem_Icc F hF hsum i.val
  have hendcut := (rankCut_mem_Icc F hF hsum (i.val + 1)).2
  rw [rankCut_succ] at hendcut
  have h := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1) (by norm_num)
    (rankIntegrand_integrable phi F hphi hF hsum i)
    (intervalIntegrable_const (c := phi (rankCut F i.val))) (fun u hu => ?_)
  · simpa only [intervalIntegral.integral_const, sub_zero, one_smul, activation,
      orderedActivation, rankActivation, leftRank, F, i] using h
  · have hmul := mul_nonneg hu.1 (hF i)
    have hmul1 := mul_le_mul_of_nonneg_right hu.2 (hF i)
    apply hanti hleft ⟨by linarith [hleft.1], by linarith⟩
    linarith

/-- Equation (5.4), derived from actual stability rather than assumed. -/
theorem stable_left_score_nonnegative (E : Election) (phi : ℝ → ℝ)
    (D : Lottery E.candidateCount) (hphi : ContinuousOn phi (Icc 0 1))
    (hanti : AntitoneOn phi (Icc 0 1)) (hden0 : 0 < 1 + phi 0)
    (hzero : (∫ r in (0 : ℝ)..1, phi r) = 0)
    (hs : E.Stable (normalizedActivation phi) D) (a : E.Candidate) :
    0 ≤ expectation E.voterWeight (fun v => phi (E.leftRank D v a)) := by
  exact le_trans (E.stable_centered_nonnegative phi D hphi hanti hden0 hzero hs a)
    (expectation_mono E.voterWeight_nonneg
      (fun v => E.centered_average_le_left phi D hphi hanti v a))

/-- Centered activation of a candidate set, using its actual candidate averages. -/
noncomputable def blockScore (E : Election) (phi : ℝ → ℝ) (D : Lottery E.candidateCount)
    (S : Finset E.Candidate) (v : E.Voter) : ℝ :=
  -(∑ a ∈ S, D.weight a * E.activation phi D v a)

/-- Equation (5.3), including candidates of zero lottery mass. -/
theorem stable_blockScore_zero (E : Election) (phi : ℝ → ℝ)
    (D : Lottery E.candidateCount) (hphi : ContinuousOn phi (Icc 0 1))
    (hanti : AntitoneOn phi (Icc 0 1)) (hden0 : 0 < 1 + phi 0)
    (hzero : (∫ r in (0 : ℝ)..1, phi r) = 0)
    (hs : E.Stable (normalizedActivation phi) D) (S : Finset E.Candidate) :
    expectation E.voterWeight (E.blockScore phi D S) = 0 := by
  classical
  have heq : expectation E.voterWeight (E.blockScore phi D S) =
      -(∑ a ∈ S, D.weight a * expectation E.voterWeight (fun v => E.activation phi D v a)) := by
    simp only [expectation, blockScore, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [heq, neg_eq_zero]
  apply Finset.sum_eq_zero
  intro a _
  rcases eq_or_lt_of_le (D.nonneg a) with ha | ha
  · rw [← ha, zero_mul]
  · rw [E.stable_centered_supported phi D hphi hanti hden0 hzero hs a ha, mul_zero]

end Election
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

-- Source module OptimalG.ThresholdIntegrability
section
set_option autoImplicit true
/-! Any function of the finite threshold set is integrable on bounded intervals.
No measurability assumption on mass-indexed verifier coefficients is needed. -/
namespace OptimalG
open Set MeasureTheory
open scoped BigOperators

theorem intervalIntegrable_indicator_const (s : Set ℝ) (hs : MeasurableSet s)
    (c a b : ℝ) : IntervalIntegrable (s.indicator (fun _ => c)) volume a b := by
  exact intervalIntegrable_iff.mpr
    ((intervalIntegrable_iff.mp (intervalIntegrable_const (c := c))).indicator hs)

theorem thresholdSet_fiber_measurable {n : ℕ} (rho : Fin n → ℝ)
    (S : Finset (Fin n)) : MeasurableSet {t : ℝ | thresholdSet rho t = S} := by
  classical
  have heq : {t : ℝ | thresholdSet rho t = S} =
      ⋂ i : Fin n, {t : ℝ | (t < rho i ↔ i ∈ S)} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h i
      have hh := congrArg (fun T : Finset (Fin n) => i ∈ T) h
      simpa [thresholdSet] using hh
    · intro h
      ext i
      simpa [thresholdSet] using h i
  rw [heq]
  apply MeasurableSet.iInter
  intro i
  by_cases hi : i ∈ S
  · simpa only [hi, iff_true, Set.Iio_def] using (measurableSet_Iio (a := rho i))
  · simpa only [hi, iff_false, not_lt, Set.Ici_def] using (measurableSet_Ici (a := rho i))

theorem thresholdSet_function_integrable {n : ℕ} (rho : Fin n → ℝ)
    (H : Finset (Fin n) → ℝ) (a b : ℝ) :
    IntervalIntegrable (fun t => H (thresholdSet rho t)) volume a b := by
  classical
  let f : Finset (Fin n) → ℝ → ℝ := fun S =>
    {t : ℝ | thresholdSet rho t = S}.indicator (fun _ => H S)
  have heq : (fun t => H (thresholdSet rho t)) = ∑ S : Finset (Fin n), f S := by
    funext t
    simp only [Finset.sum_apply, f, Set.indicator, Set.mem_setOf_eq]
    simp
  rw [heq]
  exact IntervalIntegrable.sum Finset.univ (fun S _ =>
    intervalIntegrable_indicator_const _ (thresholdSet_fiber_measurable rho S) (H S) a b)

/-- Extension by a constant on negative thresholds preserves local integrability. -/
theorem extendedThreshold_integrable {n : ℕ} (rho : Fin n → ℝ)
    (H : Finset (Fin n) → ℝ) (lam a b : ℝ) :
    IntervalIntegrable (fun t => if t < 0 then lam else H (thresholdSet rho t)) volume a b := by
  classical
  have hleft := intervalIntegrable_indicator_const (Iio (0 : ℝ)) measurableSet_Iio lam a b
  have hright := intervalIntegrable_iff.mpr
    ((intervalIntegrable_iff.mp (thresholdSet_function_integrable rho H a b)).indicator
      (measurableSet_Ici (a := (0 : ℝ))))
  convert hleft.add hright using 1
  funext t
  by_cases ht : t < 0
  · simp [Set.indicator, Set.mem_Iio, Set.mem_Ici, ht, not_le.mpr ht]
  · simp [Set.indicator, Set.mem_Iio, Set.mem_Ici, ht, le_of_not_gt ht]

end OptimalG
end

-- Source module OptimalG.ElectionSlices
section
set_option autoImplicit true
/-! Reindexing the actual election by each voter's rank order. -/
namespace OptimalG
open Set MeasureTheory
open scoped BigOperators

theorem runningMin_reindex {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (e : A ≃ B) (rank : B → ℕ) (rho : B → ℝ) (a : A) :
    runningMin (fun i => rank (e i)) (fun i => rho (e i)) a =
      runningMin rank rho (e a) := by
  apply le_antisymm
  · obtain ⟨b, hb, heq⟩ := runningMin_attained rank rho (e a)
    rw [heq]
    simpa only [e.apply_symm_apply] using
      runningMin_le_of_rank_le (fun i => rank (e i)) (fun i => rho (e i))
        a (e.symm b) (by simpa only [e.apply_symm_apply] using hb)
  · obtain ⟨i, hi, heq⟩ := runningMin_attained (fun i => rank (e i)) (fun i => rho (e i)) a
    rw [heq]
    exact runningMin_le_of_rank_le rank rho (e a) (e i) hi

theorem maximumGap_reindex {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (e : A ≃ B) (rank : B → ℕ) (rho : B → ℝ) :
    maximumGap (fun i => rank (e i)) (fun i => rho (e i)) = maximumGap rank rho := by
  apply le_antisymm
  · obtain ⟨a, ha⟩ := maximumGap_attained (fun i => rank (e i)) (fun i => rho (e i))
    rw [ha, runningMin_reindex]
    exact le_maximumGap rank rho (e a)
  · obtain ⟨b, hb⟩ := maximumGap_attained rank rho
    rw [hb]
    have hh := le_maximumGap (fun i => rank (e i)) (fun i => rho (e i)) (e.symm b)
    simpa only [runningMin_reindex, e.apply_symm_apply] using hh

namespace Election
noncomputable abbrev rankWeights (E : Election) (D : Lottery E.candidateCount)
    (v : E.Voter) (i : Fin E.candidateCount) : ℝ := D.weight (E.order v i)
noncomputable abbrev rankHeights (E : Election) (rho : E.Candidate → ℝ)
    (v : E.Voter) (i : Fin E.candidateCount) : ℝ := rho (E.order v i)
noncomputable def rankSet (E : Election) (S : Finset E.Candidate) (v : E.Voter) :
    Finset (Fin E.candidateCount) := S.map (E.order v).symm.toEmbedding

theorem rankWeights_nonneg (E : Election) (D : Lottery E.candidateCount) (v : E.Voter)
    (i : Fin E.candidateCount) : 0 ≤ E.rankWeights D v i := D.nonneg _
theorem rankWeights_total (E : Election) (D : Lottery E.candidateCount) (v : E.Voter) :
    ∑ i, E.rankWeights D v i = 1 := by
  simpa only [rankWeights, Equiv.sum_comp] using D.total

theorem mass_rankSet (E : Election) (D : Lottery E.candidateCount)
    (S : Finset E.Candidate) (v : E.Voter) :
    (∑ i ∈ E.rankSet S v, E.rankWeights D v i) = ∑ a ∈ S, D.weight a := by
  classical
  simp [rankSet, rankWeights, Finset.sum_map]

theorem blockScore_rankSet (E : Election) (D : Lottery E.candidateCount)
    (S : Finset E.Candidate) (phi : ℝ → ℝ) (v : E.Voter) :
    E.blockScore phi D S v = centeredBlock (E.rankWeights D v) (E.rankSet S v) phi := by
  classical
  unfold blockScore centeredBlock
  congr 1
  rw [rankSet, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro a _
  have hh := mass_mul_rankActivation phi (E.rankWeights D v) ((E.order v).symm a)
  dsimp [rankWeights, activation, orderedActivation] at *
  simpa only [Equiv.apply_symm_apply] using hh

theorem runningMin_rankHeights (E : Election) (rho : E.Candidate → ℝ)
    (v : E.Voter) (i : Fin E.candidateCount) :
    runningMin (fun j : Fin E.candidateCount => j.val) (E.rankHeights rho v) i =
      runningMin (E.ordinalRank v) rho (E.order v i) := by
  simpa only [ordinalRank, Equiv.symm_apply_apply] using
    runningMin_reindex (E.order v) (E.ordinalRank v) rho i

theorem maximumGap_rankHeights (E : Election) (rho : E.Candidate → ℝ) (v : E.Voter) :
    maximumGap (fun j : Fin E.candidateCount => j.val) (E.rankHeights rho v) =
      maximumGap (E.ordinalRank v) rho := by
  simpa only [ordinalRank, Equiv.symm_apply_apply] using
    maximumGap_reindex (E.order v) (E.ordinalRank v) rho

theorem numerator_rankHeights (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (v : E.Voter) :
    expectation (E.rankWeights D v)
      (runningMin (fun j : Fin E.candidateCount => j.val) (E.rankHeights rho v)) =
      expectation D.weight (runningMin (E.ordinalRank v) rho) := by
  simp only [expectation, runningMin_rankHeights, rankWeights]
  exact Equiv.sum_comp (E.order v) (fun a => D.weight a * runningMin (E.ordinalRank v) rho a)

theorem thresholdSet_rankHeights (E : Election) (rho : E.Candidate → ℝ)
    (v : E.Voter) (t : ℝ) :
    thresholdSet (E.rankHeights rho v) t = E.rankSet (thresholdSet rho t) v := by
  classical
  ext i
  simp [thresholdSet, rankHeights, rankSet]

end Election
end OptimalG
end

-- Source module OptimalG.Potential
section
set_option autoImplicit true
/-!
# The individual potential from (5.6)

The derivative hypothesis is used here in its integrated form: the decrease of `phi`
between high ranks is at least the increase in rank. Deriving this from absolute
continuity and the almost-everywhere derivative bound is a separate obligation.
-/

namespace OptimalG

open Set

noncomputable def rankPotential (phi : ℝ → ℝ) (lam x z : ℝ) : ℝ :=
  if z ≤ lam then 0 else lam - z - ((lam - x) / phi x) * phi z

theorem potential_ratio_ge_one (phi : ℝ → ℝ) (lam x : ℝ)
    (hpos : 0 < phi x) (hcap : phi x ≤ lam - x) :
    1 ≤ (lam - x) / phi x := by
  apply (le_div_iff₀ hpos).mpr
  simpa using hcap

theorem rankPotential_low (phi : ℝ → ℝ) (lam x z : ℝ) (hz : z ≤ lam) :
    rankPotential phi lam x z = 0 := by simp [rankPotential, hz]

theorem rankPotential_high_mono (phi : ℝ → ℝ) (lam x y z : ℝ)
    (hpos : 0 < phi x) (hcap : phi x ≤ lam - x)
    (hy : lam < y) (hyz : y ≤ z) (hfall : phi z - phi y ≤ y - z) :
    rankPotential phi lam x y ≤ rankPotential phi lam x z := by
  have hratio := potential_ratio_ge_one phi lam x hpos hcap
  have hz : lam < z := lt_of_lt_of_le hy hyz
  simp only [rankPotential, if_neg (not_le.mpr hy), if_neg (not_le.mpr hz)]
  have h1 := mul_nonneg (sub_nonneg.mpr hratio) (sub_nonneg.mpr hyz)
  have h2 := mul_nonneg (by linarith : 0 ≤ (lam - x) / phi x)
    (by linarith : 0 ≤ phi y - phi z - (z - y))
  nlinarith

theorem rankPotential_nonneg (phi : ℝ → ℝ) (lam x z : ℝ)
    (hpos : 0 < phi x) (hcap : phi x ≤ lam - x)
    (hfall : lam < z → phi z ≤ lam - z) :
    0 ≤ rankPotential phi lam x z := by
  by_cases hz : z ≤ lam
  · simp [rankPotential, hz]
  · have hz' : lam < z := lt_of_not_ge hz
    have hf := hfall hz'
    have hratio := potential_ratio_ge_one phi lam x hpos hcap
    have h1 := mul_nonneg (sub_nonneg.mpr hratio) (by linarith : 0 ≤ z - lam)
    have h2 := mul_nonneg (by linarith : 0 ≤ (lam - x) / phi x)
      (by linarith : 0 ≤ lam - z - phi z)
    simp only [rankPotential, if_neg hz]
    nlinarith

/-- Integrated high-rank slope bounds imply the required monotonicity on [0,1]. -/
theorem rankPotential_monotoneOn (phi : ℝ → ℝ) (lam x : ℝ)
    (hpos : 0 < phi x) (hcap : phi x ≤ lam - x)
    (hzero : phi lam = 0)
    (hfall : ∀ y z, lam ≤ y → y ≤ z → z ≤ 1 → phi z - phi y ≤ y - z) :
    MonotoneOn (rankPotential phi lam x) (Icc 0 1) := by
  intro y hy z hz hyz
  by_cases hyl : y ≤ lam
  · rw [rankPotential_low phi lam x y hyl]
    apply rankPotential_nonneg phi lam x z hpos hcap
    intro hzl
    have hf := hfall lam z le_rfl (le_of_lt hzl) hz.2
    simpa [hzero] using hf
  · exact rankPotential_high_mono phi lam x y z hpos hcap
      (lt_of_not_ge hyl) hyz (hfall y z (le_of_not_ge hyl) hyz hz.2)

/-- The mass-one identity stated after (5.7), including z=λ. -/
theorem rankPotential_mass_one (phi : ℝ → ℝ) (lam x z : ℝ)
    (hpos : 0 < phi x) (hzero : phi lam = 0) (hz : lam ≤ z) :
    phi x * (z + rankPotential phi lam x z - lam) =
      (-phi z) * (lam - x) := by
  by_cases hzl : z ≤ lam
  · have heq : z = lam := le_antisymm hzl hz
    subst z
    simp [rankPotential, hzero]
  · simp only [rankPotential, if_neg hzl]
    field_simp
    ring

end OptimalG
end

-- Source module OptimalG.VerifierConditions
section
set_option autoImplicit true
/-! The exact functional inequalities supplied to the finite-election verifier.
These are hypotheses for the verifier lemma, not assertions of existence. -/
namespace OptimalG
open Set MeasureTheory

structure VerifierCurve (phi : ℝ → ℝ) (lam : ℝ) : Prop where
  lam_pos : 0 < lam
  lam_lt_one : lam < 1
  continuous : ContinuousOn phi (Icc 0 1)
  decreasing : AntitoneOn phi (Icc 0 1)
  positive_below : ∀ x ∈ Ico (0 : ℝ) lam, 0 < phi x
  integral_zero : (∫ r in (0 : ℝ)..1, phi r) = 0
  at_lam : phi lam = 0
  at_one : phi 1 = -1
  ceiling : ∀ r ∈ Icc (0 : ℝ) 1, phi r ≤ lam - r
  high_fall : ∀ y z, lam ≤ y → y ≤ z → z ≤ 1 → phi z - phi y ≤ y - z

namespace VerifierCurve
variable {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem lam_mem : lam ∈ Icc (0 : ℝ) 1 := ⟨h.lam_pos.le, h.lam_lt_one.le⟩
theorem positive {x : ℝ} (hx : x ∈ Ico (0 : ℝ) lam) : 0 < phi x := by
  exact h.positive_below x hx

theorem denominator_pos : 0 < 1 + phi 0 := by
  linarith [h.positive_below 0 ⟨le_rfl, h.lam_pos⟩]

theorem nonpositive {x : ℝ} (hx : x ∈ Icc lam 1) : phi x ≤ 0 := by
  rw [← h.at_lam]
  exact h.decreasing h.lam_mem ⟨h.lam_pos.le.trans hx.1, hx.2⟩ hx.1

theorem nonnegative {x : ℝ} (hx : x ∈ Icc (0 : ℝ) lam) : 0 ≤ phi x := by
  rw [← h.at_lam]
  exact h.decreasing ⟨hx.1, hx.2.trans h.lam_lt_one.le⟩ h.lam_mem hx.2

theorem potential_nonneg {x z : ℝ} (hx : x ∈ Ico (0 : ℝ) lam)
    (hz : z ∈ Icc (0 : ℝ) 1) : 0 ≤ rankPotential phi lam x z := by
  apply rankPotential_nonneg phi lam x z (h.positive hx)
    (h.ceiling x ⟨hx.1, hx.2.le.trans h.lam_lt_one.le⟩)
  intro _
  exact h.ceiling z hz

theorem potential_monotone {x : ℝ} (hx : x ∈ Ico (0 : ℝ) lam) :
    MonotoneOn (rankPotential phi lam x) (Icc 0 1) :=
  rankPotential_monotoneOn phi lam x (h.positive hx)
    (h.ceiling x ⟨hx.1, hx.2.le.trans h.lam_lt_one.le⟩) h.at_lam h.high_fall

theorem negative_part_le {q s : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (hs : s ∈ Icc lam 1) (hqs : q ≤ s) : max (-phi q) 0 ≤ -phi s := by
  apply max_le
  · exact neg_le_neg (h.decreasing hq ⟨h.lam_pos.le.trans hs.1, hs.2⟩ hqs)
  · exact neg_nonneg.mpr (h.nonpositive hs)

end VerifierCurve

noncomputable def packingDelta (phi : ℝ → ℝ) (p q : ℝ) : ℝ :=
  curvePrimitive phi (1 - p + q) - curvePrimitive phi q
noncomputable def packingK (phi : ℝ → ℝ) (p q z : ℝ) : ℝ :=
  curvePrimitive phi (z - p + q) - curvePrimitive phi z - curvePrimitive phi q

/-- Equations 5.9--5.12, on a specified mass domain. -/
structure VerifierOn (masses : Set ℝ) (phi : ℝ → ℝ) (lam : ℝ)
    (beta : ℝ → ℝ) (corr : ℝ → ℝ → ℝ) : Prop where
  beta_nonneg : ∀ p ∈ masses, 0 ≤ beta p
  corr_nonneg : ∀ p ∈ masses, ∀ x ∈ Ico (0 : ℝ) lam, 0 ≤ corr p x
  low_first : ∀ p ∈ masses, ∀ x ∈ Ico (0 : ℝ) lam, ∀ q,
    0 ≤ q → q ≤ p → q ≤ x → q + beta p * packingDelta phi p q + corr p x ≤ lam
  low_second : ∀ p ∈ masses, ∀ x ∈ Ico (0 : ℝ) lam, ∀ q,
    0 ≤ q → q ≤ p → p ≤ x → q + beta p * packingK phi p q x + corr p x ≤ 0
  high_first : ∀ p ∈ masses, ∀ x ∈ Ico (0 : ℝ) lam, ∀ q,
    0 ≤ q → q ≤ p → phi x * (q + beta p * packingDelta phi p q + rankPotential phi lam x q - lam)
      ≤ max (-phi q) 0 * corr p x
  high_second : ∀ p ∈ masses, ∀ x ∈ Ico (0 : ℝ) lam, ∀ q z,
    0 ≤ q → q ≤ p → p ≤ z → z ≤ 1 →
    phi x * (q + beta p * packingK phi p q z + rankPotential phi lam x q - rankPotential phi lam x z)
      ≤ max (-phi z) 0 * corr p x

theorem VerifierOn.transport {M N : Set ℝ} {phi : ℝ → ℝ} {lam : ℝ}
    {beta beta' : ℝ → ℝ} {corr corr' : ℝ → ℝ → ℝ}
    (hv : VerifierOn M phi lam beta corr) (hsub : N ⊆ M)
    (hb : ∀ p ∈ N, beta' p = beta p)
    (hc : ∀ p ∈ N, ∀ x ∈ Ico (0 : ℝ) lam, corr' p x = corr p x) :
    VerifierOn N phi lam beta' corr' := by
  constructor
  · intro p hp; rw [hb p hp]; exact hv.beta_nonneg p (hsub hp)
  · intro p hp x hx; rw [hc p hp x hx]; exact hv.corr_nonneg p (hsub hp) x hx
  · intro p hp x hx q hq hqp hqx; rw [hb p hp, hc p hp x hx]
    exact hv.low_first p (hsub hp) x hx q hq hqp hqx
  · intro p hp x hx q hq hqp hpx; rw [hb p hp, hc p hp x hx]
    exact hv.low_second p (hsub hp) x hx q hq hqp hpx
  · intro p hp x hx q hq hqp; rw [hb p hp, hc p hp x hx]
    exact hv.high_first p (hsub hp) x hx q hq hqp
  · intro p hp x hx q z hq hqp hpz hz; rw [hb p hp, hc p hp x hx]
    exact hv.high_second p (hsub hp) x hx q z hq hqp hpz hz

/-- At mass zero all coefficients can vanish. -/
theorem verifier_zero_mass {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam) :
    VerifierOn {0} phi lam (fun _ => 0) (fun _ _ => 0) := by
  constructor
  · simp
  · simp
  · intro p hp x hx q hq hqp hqx
    have hp0 : p = 0 := hp
    have hq0 : q = 0 := by linarith
    simp [hq0, h.lam_pos.le]
  · intro p hp x hx q hq hqp hpx
    have hp0 : p = 0 := hp
    have hq0 : q = 0 := by linarith
    simp [hq0]
  · intro p hp x hx q hq hqp
    have hp0 : p = 0 := hp
    have hq0 : q = 0 := by linarith
    simp only [hq0, zero_mul, add_zero, mul_zero]
    rw [rankPotential_low phi lam x 0 h.lam_pos.le]
    exact mul_nonpos_of_nonneg_of_nonpos (h.positive hx).le (by linarith [h.lam_pos])
  · intro p hp x hx q z hq hqp hpz hz
    have hp0 : p = 0 := hp
    have hq0 : q = 0 := by linarith
    simp only [hq0, zero_mul, add_zero, mul_zero]
    rw [rankPotential_low phi lam x 0 h.lam_pos.le]
    exact mul_nonpos_of_nonneg_of_nonpos (h.positive hx).le
      (by linarith [h.potential_nonneg hx ⟨by linarith, hz⟩])

/-- The mass-one coefficients cover zero-mass reference candidates at interior ranks. -/
theorem verifier_one_mass {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam) :
    VerifierOn {1} phi lam (fun _ => 0) (fun _ x => lam - x) := by
  have hfirst (x q : ℝ) (hx : x ∈ Ico (0 : ℝ) lam) (hq : q ∈ Icc (0 : ℝ) 1) :
      phi x * (q + rankPotential phi lam x q - lam) ≤ max (-phi q) 0 * (lam - x) := by
    by_cases hql : q ≤ lam
    · rw [rankPotential_low phi lam x q hql]
      have hpos := h.positive hx
      have hnonneg := h.nonnegative ⟨hq.1, hql⟩
      rw [max_eq_right (neg_nonpos.mpr hnonneg), zero_mul]
      exact mul_nonpos_of_nonneg_of_nonpos hpos.le (by linarith)
    · rw [rankPotential_mass_one phi lam x q (h.positive hx) h.at_lam (le_of_not_ge hql)]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sub_nonneg.mpr hx.2.le)
  constructor
  · simp
  · intro p hp x hx; exact sub_nonneg.mpr hx.2.le
  · intro p hp x hx q hq hqp hqx
    simp only [zero_mul, add_zero]
    linarith
  · intro p hp x hx q hq hqp hpx
    have hp1 : p = 1 := hp
    exfalso; linarith [hx.2, h.lam_lt_one]
  · intro p hp x hx q hq hqp
    have hp1 : p = 1 := hp
    simpa only [zero_mul, add_zero] using hfirst x q hx ⟨hq, by linarith⟩
  · intro p hp x hx q z hq hqp hpz hz
    have hp1 : p = 1 := hp
    have hz1 : z = 1 := by linarith
    subst z
    simp only [zero_mul, add_zero, h.at_one, neg_neg, max_eq_left (by norm_num : (0 : ℝ) ≤ 1), one_mul]
    have hq1 : q ≤ 1 := by linarith
    have hpot1 : lam ≤ rankPotential phi lam x 1 := by
      have hr := potential_ratio_ge_one phi lam x (h.positive hx)
        (h.ceiling x ⟨hx.1, hx.2.le.trans h.lam_lt_one.le⟩)
      simp only [rankPotential, if_neg (not_le.mpr h.lam_lt_one), h.at_one, mul_neg_one]
      linarith
    have hneg := h.negative_part_le ⟨hq, hq1⟩ ⟨h.lam_lt_one.le, le_rfl⟩ hq1
    rw [h.at_one, neg_neg] at hneg
    have hc : 0 ≤ lam - x := by linarith [hx.2]
    have hbound := hfirst x q hx ⟨hq, hq1⟩
    have hmul := mul_le_mul_of_nonneg_right hneg hc
    have hpot := mul_nonneg (h.positive hx).le (sub_nonneg.mpr hpot1)
    nlinarith

/-- Canonical endpoint extension of any verifier supplied for open masses. -/
theorem verifier_extend_endpoints {phi : ℝ → ℝ} {lam : ℝ}
    (h : VerifierCurve phi lam) (beta : ℝ → ℝ) (corr : ℝ → ℝ → ℝ)
    (hv : VerifierOn (Ioo 0 1) phi lam beta corr) :
    ∃ b c, VerifierOn (Icc 0 1) phi lam b c := by
  let b : ℝ → ℝ := fun p => if p = 0 ∨ p = 1 then 0 else beta p
  let c : ℝ → ℝ → ℝ := fun p x => if p = 0 then 0 else if p = 1 then lam - x else corr p x
  have hlocal (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
      VerifierOn {p} phi lam b c := by
    by_cases hp0 : p = 0
    · subst p
      apply (verifier_zero_mass h).transport (fun _ hr => hr)
      · intro r hr; have hr0 : r = 0 := hr; subst r; simp [b]
      · intro r hr x hx; have hr0 : r = 0 := hr; subst r; simp [c]
    · by_cases hp1 : p = 1
      · subst p
        apply (verifier_one_mass h).transport (fun _ hr => hr)
        · intro r hr; have hr1 : r = 1 := hr; subst r; simp [b]
        · intro r hr x hx; have hr1 : r = 1 := hr; subst r; simp [c]
      · have hpo : p ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hp.1 (Ne.symm hp0), lt_of_le_of_ne hp.2 hp1⟩
        apply hv.transport (fun r hr => by have hrp : r = p := hr; simpa only [hrp] using hpo)
        · intro r hr; have hrp : r = p := hr; subst r; simp [b, hp0, hp1]
        · intro r hr x hx; have hrp : r = p := hr; subst r; simp [c, hp0, hp1]
  refine ⟨b, c, ?_⟩
  constructor
  · intro p hp; exact (hlocal p hp).beta_nonneg p rfl
  · intro p hp; exact (hlocal p hp).corr_nonneg p rfl
  · intro p hp; exact (hlocal p hp).low_first p rfl
  · intro p hp; exact (hlocal p hp).low_second p rfl
  · intro p hp; exact (hlocal p hp).high_first p rfl
  · intro p hp; exact (hlocal p hp).high_second p rfl

end OptimalG
end

-- Source module OptimalG.ElectionThresholds
section
set_option autoImplicit true
/-! All geometric and integral facts about slices of actual finite elections. -/
namespace OptimalG.Election
open Set MeasureTheory
open scoped BigOperators

noncomputable def sliceMass (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (t : ℝ) : ℝ := ∑ a ∈ thresholdSet rho t, D.weight a
noncomputable def sliceWidth (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (v : E.Voter) (t : ℝ) : ℝ :=
  rankCut (E.rankWeights D v) (prefixBoundary (E.rankSet (thresholdSet rho t) v))
noncomputable def sliceRight (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (v : E.Voter) (t : ℝ) : ℝ :=
  rankCut (E.rankWeights D v) (lastIndex (E.rankSet (thresholdSet rho t) v))
noncomputable def sliceScore (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (phi : ℝ → ℝ) (v : E.Voter) (t : ℝ) : ℝ :=
  E.blockScore phi D (thresholdSet rho t) v

theorem sliceWidth_eq_threshold (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (v : E.Voter) (t : ℝ) :
    E.sliceWidth D rho v t = thresholdWidth (E.rankWeights D v) (E.rankHeights rho v) t := by
  rw [thresholdWidth, E.thresholdSet_rankHeights]; rfl

theorem sliceRight_eq_threshold (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (v : E.Voter) (t : ℝ) :
    E.sliceRight D rho v t = thresholdRight (E.rankWeights D v) (E.rankHeights rho v) t := by
  rw [thresholdRight, E.thresholdSet_rankHeights]; rfl

theorem sliceMass_mem_Icc (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (t : ℝ) : E.sliceMass D rho t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg (fun a _ => D.nonneg a)
  · calc
      _ ≤ ∑ a, D.weight a := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun a _ _ => D.nonneg a)
      _ = 1 := D.total

theorem sliceWidth_mem_Icc (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (v : E.Voter) (t : ℝ) : E.sliceWidth D rho v t ∈ Icc (0 : ℝ) 1 :=
  rankCut_mem_Icc _ (E.rankWeights_nonneg D v) (E.rankWeights_total D v) _

theorem sliceRight_mem_Icc (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (v : E.Voter) (t : ℝ) : E.sliceRight D rho v t ∈ Icc (0 : ℝ) 1 :=
  rankCut_mem_Icc _ (E.rankWeights_nonneg D v) (E.rankWeights_total D v) _

theorem sliceWidth_le_mass (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (v : E.Voter) (t : ℝ) :
    E.sliceWidth D rho v t ≤ E.sliceMass D rho t := by
  have hh := prefixCut_le_mass (E.rankWeights D v) (E.rankWeights_nonneg D v)
    (E.rankSet (thresholdSet rho t) v)
  rwa [E.mass_rankSet] at hh

theorem sliceMass_le_right (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (v : E.Voter) (t : ℝ) :
    E.sliceMass D rho t ≤ E.sliceRight D rho v t := by
  have hh := mass_le_lastCut (E.rankWeights D v) (E.rankWeights_nonneg D v)
    (E.rankSet (thresholdSet rho t) v)
  rwa [E.mass_rankSet] at hh

theorem sliceWidth_le_leftRank (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (a : E.Candidate) (ha : rho a = 0)
    (v : E.Voter) (t : ℝ) (ht : 0 ≤ t) : E.sliceWidth D rho v t ≤ E.leftRank D v a := by
  rw [E.sliceWidth_eq_threshold]
  exact thresholdWidth_le_referenceRank (E.rankWeights D v) (E.rankHeights rho v)
    (E.rankWeights_nonneg D v) ((E.order v).symm a) (by simpa only [rankHeights, Equiv.apply_symm_apply] using ha) t ht

theorem slice_separation (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (v : E.Voter) (t : ℝ) :
    E.sliceRight D rho v (t + maximumGap (E.ordinalRank v) rho) ≤ E.sliceWidth D rho v t := by
  rw [E.sliceWidth_eq_threshold, E.sliceRight_eq_threshold, ← E.maximumGap_rankHeights rho v]
  exact threshold_separation _ _ (E.rankWeights_nonneg D v) t

theorem slice_layer_cake (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (hrho : ∀ a, 0 ≤ rho a) (X : ℝ) (hX : ∀ a, rho a ≤ X)
    (v : E.Voter) : (∫ t in (0 : ℝ)..X, E.sliceWidth D rho v t) =
      expectation D.weight (runningMin (E.ordinalRank v) rho) := by
  simp_rw [E.sliceWidth_eq_threshold]
  rw [(threshold_layer_cake (E.rankWeights D v) (E.rankHeights rho v) X
    (fun i => hrho (E.order v i)) (fun i => hX (E.order v i))).2]
  exact E.numerator_rankHeights D rho v

theorem slice_packingK (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (phi : ℝ → ℝ)
    (hphi : ContinuousOn phi (Icc 0 1)) (hanti : AntitoneOn phi (Icc 0 1))
    (v : E.Voter) (t z : ℝ) (hz : E.sliceRight D rho v t ≤ z) (hz1 : z ≤ 1) :
    E.sliceScore D rho phi v t ≤ packingK phi (E.sliceMass D rho t) (E.sliceWidth D rho v t) z := by
  rw [sliceScore, E.blockScore_rankSet]
  exact centeredBlock_packing (E.rankWeights D v) (E.rankWeights_nonneg D v)
    (E.rankWeights_total D v) (E.rankSet (thresholdSet rho t) v) phi hphi hanti
    (E.sliceMass D rho t) (E.sliceWidth D rho v t) z
    (E.mass_rankSet D (thresholdSet rho t) v).symm rfl hz hz1

theorem slice_packingDelta (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (phi : ℝ → ℝ)
    (hphi : ContinuousOn phi (Icc 0 1)) (hanti : AntitoneOn phi (Icc 0 1))
    (hzero : (∫ r in (0 : ℝ)..1, phi r) = 0) (v : E.Voter) (t : ℝ) :
    E.sliceScore D rho phi v t ≤ packingDelta phi (E.sliceMass D rho t) (E.sliceWidth D rho v t) := by
  have hh := E.slice_packingK D rho phi hphi hanti v t 1 (E.sliceRight_mem_Icc D rho v t).2 le_rfl
  simpa only [packingK, packingDelta, curvePrimitive, hzero, sub_zero] using hh

theorem sliceScore_mean_zero (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
    (hstable : E.Stable (normalizedActivation phi) D) (t : ℝ) :
    expectation E.voterWeight (fun v => E.sliceScore D rho phi v t) = 0 :=
  E.stable_blockScore_zero phi D h.continuous h.decreasing h.denominator_pos h.integral_zero hstable _

theorem sliceWidth_integrable (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (v : E.Voter) (a b : ℝ) :
    IntervalIntegrable (E.sliceWidth D rho v) volume a b :=
  thresholdSet_function_integrable rho
    (fun S => rankCut (E.rankWeights D v) (prefixBoundary (E.rankSet S v))) a b

theorem slice_extendedPotential_integrable (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (v : E.Voter) (W : ℝ → ℝ) (lam a b : ℝ) :
    IntervalIntegrable (extendedPotential W (E.sliceWidth D rho v) lam) volume a b :=
  extendedThreshold_integrable rho
    (fun S => W (rankCut (E.rankWeights D v) (prefixBoundary (E.rankSet S v)))) lam a b

end OptimalG.Election
end

-- Source module OptimalG.Offsets
section
set_option autoImplicit true
/-!
# The expectation-preserving slice correction

This is the finite weighted algebra of Section 5.1, Step 2, Eq. (5.5).
The predicate `low` represents the voters with rank below the threshold.
The stability consequences are explicit hypotheses: the centered score has
nonnegative expectation and the supported-candidate correction has expectation
zero. No existence of verifier coefficients is asserted here.
-/

namespace OptimalG

open scoped BigOperators

/-- The unnormalized expectation restricted to the low-rank voters. -/
noncomputable def lowExpectation {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (f : V → ℝ) : ℝ :=
  expectation w (fun v => if low v then f v else 0)

/-- The last, piecewise-defined term of Eq. (5.5). -/
noncomputable def sliceCorrection {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low]
    (φ c : V → ℝ) (v : V) : ℝ :=
  if low v then c v
  else φ v * (lowExpectation w low c / lowExpectation w low φ)

/-- Split a finite expectation into its low and complementary contributions. -/
theorem expectation_split {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (f : V → ℝ) :
    expectation w f = lowExpectation w low f +
      expectation w (fun v => if low v then 0 else f v) := by
  unfold lowExpectation expectation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : low v <;> simp [h]

/-- Exact cancellation of the low-rank normalization in Eq. (5.5). -/
theorem expectation_sliceCorrection {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (φ c : V → ℝ)
    (hA : lowExpectation w low φ ≠ 0) :
    expectation w (sliceCorrection w low φ c) =
      (lowExpectation w low c / lowExpectation w low φ) * expectation w φ := by
  let A := lowExpectation w low φ
  let B := lowExpectation w low c
  have hpoint : sliceCorrection w low φ c = fun v =>
      (if low v then c v else 0) +
      (B / A) * (if low v then 0 else φ v) := by
    funext v
    by_cases h : low v <;> simp [sliceCorrection, A, B, h, mul_comm]
  rw [hpoint, expectation_add, expectation_smul]
  change B + (B / A) * expectation w (fun v => if low v then 0 else φ v) =
    (B / A) * expectation w φ
  rw [expectation_split w low φ]
  change B + (B / A) * expectation w (fun v => if low v then 0 else φ v) =
    (B / A) * (A + expectation w (fun v => if low v then 0 else φ v))
  have hA' : A ≠ 0 := hA
  field_simp

/-- Nonnegative low corrections yield a nonnegative normalization coefficient. -/
theorem correction_coefficient_nonneg {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (φ c : V → ℝ)
    (hw : ∀ v, 0 ≤ w v) (hc : ∀ v, low v → 0 ≤ c v)
    (hA : 0 < lowExpectation w low φ) :
    0 ≤ lowExpectation w low c / lowExpectation w low φ := by
  apply div_nonneg _ (le_of_lt hA)
  apply Finset.sum_nonneg
  intro v _
  apply mul_nonneg (hw v)
  by_cases h : low v
  · simpa [h] using hc v h
  · simp [h]

/-- Stability of the reference candidate makes the expected correction positive. -/
theorem expectation_sliceCorrection_nonneg {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (φ c : V → ℝ)
    (hw : ∀ v, 0 ≤ w v) (hc : ∀ v, low v → 0 ≤ c v)
    (hA : 0 < lowExpectation w low φ) (hφ : 0 ≤ expectation w φ) :
    0 ≤ expectation w (sliceCorrection w low φ c) := by
  rw [expectation_sliceCorrection w low φ c (ne_of_gt hA)]
  exact mul_nonneg (correction_coefficient_nonneg w low φ c hw hc hA) hφ

/-- Eq. (5.5) does not decrease the expected slice width. The coefficient β
may be arbitrary for this algebraic implication, since the k-term has mean zero. -/
theorem expected_slice_le_offset {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low]
    (φ c q k : V → ℝ) (β : ℝ)
    (hw : ∀ v, 0 ≤ w v) (hc : ∀ v, low v → 0 ≤ c v)
    (hA : 0 < lowExpectation w low φ) (hφ : 0 ≤ expectation w φ)
    (hk : expectation w k = 0) :
    expectation w q ≤ expectation w
      (fun v => q v + β * k v + sliceCorrection w low φ c v) := by
  rw [expectation_add, expectation_add, expectation_smul, hk]
  have hcmean := expectation_sliceCorrection_nonneg w low φ c hw hc hA hφ
  linarith

end OptimalG
end

-- Source module OptimalG.WeightedLow
section
set_option autoImplicit true
/-! Finite averaging with weights proportional to positive low-rank scores. -/
namespace OptimalG
open scoped BigOperators

noncomputable def weightedLow {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (score f : V → ℝ) : ℝ :=
  lowExpectation w low (fun v => score v * f v) / lowExpectation w low score

theorem lowExpectation_add {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (f g : V → ℝ) :
    lowExpectation w low (fun v => f v + g v) = lowExpectation w low f + lowExpectation w low g := by
  unfold lowExpectation expectation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : low v <;> simp [h, mul_add]

theorem lowExpectation_sub {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (f g : V → ℝ) :
    lowExpectation w low (fun v => f v - g v) = lowExpectation w low f - lowExpectation w low g := by
  unfold lowExpectation expectation
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : low v <;> simp [h, mul_sub]

theorem lowExpectation_smul {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (f : V → ℝ) (c : ℝ) :
    lowExpectation w low (fun v => c * f v) = c * lowExpectation w low f := by
  unfold lowExpectation expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : low v <;> simp [h] <;> ring

theorem weightedLow_congr {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (score f g : V → ℝ)
    (hfg : ∀ v, low v → f v = g v) : weightedLow w low score f = weightedLow w low score g := by
  unfold weightedLow lowExpectation expectation
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : low v
  · simp [h, hfg v h]
  · simp [h]

theorem weightedLow_const {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (score : V → ℝ) (c : ℝ)
    (hA : lowExpectation w low score ≠ 0) : weightedLow w low score (fun _ => c) = c := by
  simp only [weightedLow, mul_comm _ c, lowExpectation_smul]
  exact mul_div_cancel_right₀ c hA

theorem weightedLow_add {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (score f g : V → ℝ) :
    weightedLow w low score (fun v => f v + g v) = weightedLow w low score f + weightedLow w low score g := by
  simp only [weightedLow, mul_add, lowExpectation_add, add_div]

theorem weightedLow_sub {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (score f g : V → ℝ) :
    weightedLow w low score (fun v => f v - g v) = weightedLow w low score f - weightedLow w low score g := by
  simp only [weightedLow, mul_sub, lowExpectation_sub, sub_div]

theorem weightedLow_smul {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (score f : V → ℝ) (c : ℝ) :
    weightedLow w low score (fun v => c * f v) = c * weightedLow w low score f := by
  simp only [weightedLow, mul_left_comm _ c, lowExpectation_smul, mul_div_assoc]

theorem weightedLow_mono {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (score f g : V → ℝ)
    (hw : ∀ v, 0 ≤ w v) (hs : ∀ v, low v → 0 ≤ score v)
    (hA : 0 < lowExpectation w low score) (hfg : ∀ v, low v → f v ≤ g v) :
    weightedLow w low score f ≤ weightedLow w low score g := by
  apply div_le_div_of_nonneg_right _ hA.le
  apply expectation_mono hw
  intro v
  by_cases h : low v
  · simp only [if_pos h]
    exact mul_le_mul_of_nonneg_left (hfg v h) (hs v h)
  · simp [h]

theorem weightedLow_div_score {V : Type*} [Fintype V]
    (w : V → ℝ) (low : V → Prop) [DecidablePred low] (score f : V → ℝ)
    (hs : ∀ v, low v → score v ≠ 0) :
    weightedLow w low score (fun v => f v / score v) =
      lowExpectation w low f / lowExpectation w low score := by
  unfold weightedLow lowExpectation expectation
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : low v
  · simp only [if_pos h]
    rw [mul_div_cancel₀ _ (hs v h)]
  · simp [h]

end OptimalG
end

-- Source module OptimalG.AveragedVerifier
section
set_option autoImplicit true
/-! Averaging the individual potentials, and checking the actual offset of each voter. -/
namespace OptimalG
open Set

noncomputable def averagedRankPotential {V : Type*} [Fintype V]
    (w s : V → ℝ) (phi : ℝ → ℝ) (lam z : ℝ) : ℝ :=
  weightedLow w (fun v => s v < lam) (fun v => phi (s v))
    (fun v => rankPotential phi lam (s v) z)

noncomputable def averagedCorrection {V : Type*} [Fintype V]
    (w s : V → ℝ) (phi : ℝ → ℝ) (lam : ℝ) (corr : ℝ → ℝ → ℝ) (p : ℝ) : ℝ :=
  lowExpectation w (fun v => s v < lam) (fun v => corr p (s v)) /
    lowExpectation w (fun v => s v < lam) (fun v => phi (s v))

section Average
variable {V : Type*} [Fintype V] (w s : V → ℝ) {phi : ℝ → ℝ} {lam : ℝ}
    (h : VerifierCurve phi lam) (hw : ∀ v, 0 ≤ w v) (hs : ∀ v, s v ∈ Icc (0 : ℝ) 1)
    (hA : 0 < lowExpectation w (fun v => s v < lam) (fun v => phi (s v)))
include h hw hs hA

theorem averagedRankPotential_nonneg {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ averagedRankPotential w s phi lam z := by
  have hh := weightedLow_mono w (fun v => s v < lam) (fun v => phi (s v))
    (fun _ => 0) (fun v => rankPotential phi lam (s v) z) hw
    (fun v hv => (h.positive ⟨(hs v).1, hv⟩).le) hA
    (fun v hv => h.potential_nonneg ⟨(hs v).1, hv⟩ hz)
  rwa [weightedLow_const _ _ _ 0 (ne_of_gt hA)] at hh

theorem averagedRankPotential_monotone :
    MonotoneOn (averagedRankPotential w s phi lam) (Icc 0 1) := by
  intro y hy z hz hyz
  apply weightedLow_mono _ _ _ _ _ hw
    (fun v hv => (h.positive ⟨(hs v).1, hv⟩).le) hA
  intro v hv
  exact h.potential_monotone ⟨(hs v).1, hv⟩ hy hz hyz

omit h hw hs in
theorem averagedRankPotential_low {z : ℝ} (hz : z ≤ lam) :
    averagedRankPotential w s phi lam z = 0 := by
  unfold averagedRankPotential
  simp only [rankPotential_low phi lam _ z hz]
  exact weightedLow_const _ _ _ 0 (ne_of_gt hA)

theorem averagedVerifier_first (beta : ℝ → ℝ) (corr : ℝ → ℝ → ℝ)
    (hv : VerifierOn (Icc 0 1) phi lam beta corr) {p q : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hq : 0 ≤ q) (hqp : q ≤ p) :
    q + beta p * packingDelta phi p q + averagedRankPotential w s phi lam q - lam ≤
      max (-phi q) 0 * averagedCorrection w s phi lam corr p := by
  have hh := weightedLow_mono w (fun v => s v < lam) (fun v => phi (s v))
    (fun v => q + beta p * packingDelta phi p q + rankPotential phi lam (s v) q - lam)
    (fun v => max (-phi q) 0 * (corr p (s v) / phi (s v))) hw
    (fun v hv => (h.positive ⟨(hs v).1, hv⟩).le) hA (by
      intro v hl
      have hpv := h.positive ⟨(hs v).1, hl⟩
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hpv).mpr
      simpa only [mul_div_assoc, mul_comm (phi (s v))] using
        hv.high_first p hp (s v) ⟨(hs v).1, hl⟩ q hq hqp)
  simp only [weightedLow_sub, weightedLow_add,
    weightedLow_const _ _ _ _ (ne_of_gt hA), weightedLow_smul,
    weightedLow_div_score _ _ _ _ (fun v hl => ne_of_gt (h.positive ⟨(hs v).1, hl⟩))] at hh
  exact hh

theorem averagedVerifier_second (beta : ℝ → ℝ) (corr : ℝ → ℝ → ℝ)
    (hv : VerifierOn (Icc 0 1) phi lam beta corr) {p q z : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hq : 0 ≤ q) (hqp : q ≤ p) (hpz : p ≤ z) (hz : z ≤ 1) :
    q + beta p * packingK phi p q z + averagedRankPotential w s phi lam q -
      averagedRankPotential w s phi lam z ≤
      max (-phi z) 0 * averagedCorrection w s phi lam corr p := by
  have hh := weightedLow_mono w (fun v => s v < lam) (fun v => phi (s v))
    (fun v => q + beta p * packingK phi p q z + rankPotential phi lam (s v) q -
      rankPotential phi lam (s v) z)
    (fun v => max (-phi z) 0 * (corr p (s v) / phi (s v))) hw
    (fun v hl => (h.positive ⟨(hs v).1, hl⟩).le) hA (by
      intro v hl
      have hpv := h.positive ⟨(hs v).1, hl⟩
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hpv).mpr
      simpa only [mul_div_assoc, mul_comm (phi (s v))] using
        hv.high_second p hp (s v) ⟨(hs v).1, hl⟩ q z hq hqp hpz hz)
  simp only [weightedLow_sub, weightedLow_add,
    weightedLow_const _ _ _ _ (ne_of_gt hA), weightedLow_smul,
    weightedLow_div_score _ _ _ _ (fun v hl => ne_of_gt (h.positive ⟨(hs v).1, hl⟩))] at hh
  exact hh

/-- First inequality of 5.2 for an actual packed slice. -/
theorem offset_first (beta : ℝ → ℝ) (corr : ℝ → ℝ → ℝ)
    (hv : VerifierOn (Icc 0 1) phi lam beta corr)
    (v : V) (p q k : ℝ) (hp : p ∈ Icc (0 : ℝ) 1)
    (hq : 0 ≤ q) (hqp : q ≤ p) (hqs : q ≤ s v) (hk : k ≤ packingDelta phi p q) :
    q + beta p * k + sliceCorrection w (fun u => s u < lam)
      (fun u => phi (s u)) (fun u => corr p (s u)) v ≤
      lam - averagedRankPotential w s phi lam q := by
  have hbk := mul_le_mul_of_nonneg_left hk (hv.beta_nonneg p hp)
  by_cases hl : s v < lam
  · have hh := hv.low_first p hp (s v) ⟨(hs v).1, hl⟩ q hq hqp hqs
    rw [sliceCorrection, if_pos hl,
      averagedRankPotential_low w s hA (hqs.trans hl.le)]
    linarith
  · have hsHigh : s v ∈ Icc lam 1 := ⟨le_of_not_gt hl, (hs v).2⟩
    have hc := correction_coefficient_nonneg w (fun u => s u < lam)
      (fun u => phi (s u)) (fun u => corr p (s u)) hw
      (fun u hu => hv.corr_nonneg p hp (s u) ⟨(hs u).1, hu⟩) hA
    have hbound := averagedVerifier_first w s h hw hs hA beta corr hv hp hq hqp
    have hneg := mul_le_mul_of_nonneg_right
      (h.negative_part_le ⟨hq, hqp.trans hp.2⟩ hsHigh hqs) hc
    rw [sliceCorrection, if_neg hl]
    change q + beta p * k + phi (s v) * averagedCorrection w s phi lam corr p ≤ _
    change max (-phi q) 0 * averagedCorrection w s phi lam corr p ≤
      -phi (s v) * averagedCorrection w s phi lam corr p at hneg
    nlinarith

/-- Second inequality of 5.2; the low case packs directly against s_v. -/
theorem offset_second (beta : ℝ → ℝ) (corr : ℝ → ℝ → ℝ)
    (hv : VerifierOn (Icc 0 1) phi lam beta corr)
    (v : V) (p q z k : ℝ) (hp : p ∈ Icc (0 : ℝ) 1)
    (hq : 0 ≤ q) (hqp : q ≤ p) (hpz : p ≤ z) (hzs : z ≤ s v)
    (hkz : k ≤ packingK phi p q z) (hks : k ≤ packingK phi p q (s v)) :
    q + beta p * k + sliceCorrection w (fun u => s u < lam)
      (fun u => phi (s u)) (fun u => corr p (s u)) v ≤
      averagedRankPotential w s phi lam z - averagedRankPotential w s phi lam q := by
  by_cases hl : s v < lam
  · have hh := hv.low_second p hp (s v) ⟨(hs v).1, hl⟩ q hq hqp (hpz.trans hzs)
    have hbk := mul_le_mul_of_nonneg_left hks (hv.beta_nonneg p hp)
    rw [sliceCorrection, if_pos hl,
      averagedRankPotential_low w s hA (hzs.trans hl.le),
      averagedRankPotential_low w s hA (hqp.trans (hpz.trans (hzs.trans hl.le)))]
    linarith
  · have hsHigh : s v ∈ Icc lam 1 := ⟨le_of_not_gt hl, (hs v).2⟩
    have hc := correction_coefficient_nonneg w (fun u => s u < lam)
      (fun u => phi (s u)) (fun u => corr p (s u)) hw
      (fun u hu => hv.corr_nonneg p hp (s u) ⟨(hs u).1, hu⟩) hA
    have hbound := averagedVerifier_second w s h hw hs hA beta corr hv hp hq hqp hpz (hzs.trans (hs v).2)
    have hneg := mul_le_mul_of_nonneg_right
      (h.negative_part_le ⟨hp.1.trans hpz, hzs.trans (hs v).2⟩ hsHigh hzs) hc
    have hbk := mul_le_mul_of_nonneg_left hkz (hv.beta_nonneg p hp)
    rw [sliceCorrection, if_neg hl]
    change q + beta p * k + phi (s v) * averagedCorrection w s phi lam corr p ≤ _
    change max (-phi z) 0 * averagedCorrection w s phi lam corr p ≤
      -phi (s v) * averagedCorrection w s phi lam corr p at hneg
    nlinarith

end Average
end OptimalG
end

-- Source module OptimalG.ZeroLowMass
section
set_option autoImplicit true
/-! The degenerate low-score case in Appendix C.1. -/
namespace OptimalG
open Set
open scoped BigOperators

theorem lowScoreMass_nonneg {V : Type*} [Fintype V]
    (w s : V → ℝ) {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
    (hw : ∀ v, 0 ≤ w v) (hs : ∀ v, s v ∈ Icc (0 : ℝ) 1) :
    0 ≤ lowExpectation w (fun v => s v < lam) (fun v => phi (s v)) := by
  apply Finset.sum_nonneg
  intro v _
  apply mul_nonneg (hw v)
  change 0 ≤ (if s v < lam then phi (s v) else 0)
  split_ifs with hl
  · exact (h.positive ⟨(hs v).1, hl⟩).le
  · rfl

/-- With positive voter weights, zero positive-score mass forces every reference rank to λ. -/
theorem all_ranks_equal_of_zero_lowScoreMass {V : Type*} [Fintype V]
    (w s : V → ℝ) {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
    (hw : ∀ v, 0 < w v) (hs : ∀ v, s v ∈ Icc (0 : ℝ) 1)
    (hmean : 0 ≤ expectation w (fun v => phi (s v)))
    (hA : lowExpectation w (fun v => s v < lam) (fun v => phi (s v)) = 0) :
    ∀ v, s v = lam := by
  classical
  have hterm (v : V) : 0 ≤ w v * (if s v < lam then phi (s v) else 0) := by
    apply mul_nonneg (hw v).le
    split_ifs with hl
    · exact (h.positive ⟨(hs v).1, hl⟩).le
    · rfl
  have hge (v : V) : lam ≤ s v := by
    by_contra hh
    have hl : s v < lam := lt_of_not_ge hh
    have hle := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i) (Finset.mem_univ v)
    change w v * (if s v < lam then phi (s v) else 0) ≤
      lowExpectation w (fun v => s v < lam) (fun v => phi (s v)) at hle
    rw [hA, if_pos hl] at hle
    exact (not_le_of_gt (mul_pos (hw v) (h.positive ⟨(hs v).1, hl⟩))) hle
  have hnonpos (v : V) : phi (s v) ≤ 0 := h.nonpositive ⟨hge v, (hs v).2⟩
  intro v
  have hsum : expectation w (fun i => phi (s i)) ≤ w v * phi (s v) := by
    calc
      _ ≤ ∑ i, if i = v then w i * phi (s i) else 0 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i = v
        · simp [hi]
        · simp only [if_neg hi]
          exact mul_nonpos_of_nonneg_of_nonpos (hw i).le (hnonpos i)
      _ = w v * phi (s v) := by simp
  have hp : 0 ≤ phi (s v) := (nonneg_of_mul_nonneg_right (hmean.trans hsum) (hw v))
  apply le_antisymm _ (hge v)
  by_contra hh
  have hl : lam < s v := lt_of_not_ge hh
  linarith [h.ceiling (s v) (hs v)]

/-- When all reference ranks are λ, the high inequalities at x=0 suffice and W=0. -/
theorem zeroLow_offset_first {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
    (beta : ℝ → ℝ) (corr : ℝ → ℝ → ℝ)
    (hv : VerifierOn (Icc 0 1) phi lam beta corr)
    {p q k : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hq : 0 ≤ q) (hqp : q ≤ p)
    (hql : q ≤ lam) (hk : k ≤ packingDelta phi p q) : q + beta p * k ≤ lam := by
  have hx : (0 : ℝ) ∈ Ico (0 : ℝ) lam := ⟨le_rfl, h.lam_pos⟩
  have hh := hv.high_first p hp 0 hx q hq hqp
  rw [rankPotential_low phi lam 0 q hql,
    max_eq_right (neg_nonpos.mpr (h.nonnegative ⟨hq, hql⟩)), zero_mul, add_zero] at hh
  have hb : q + beta p * packingDelta phi p q - lam ≤ 0 :=
    nonpos_of_mul_nonpos_right hh (h.positive hx)
  have hbk := mul_le_mul_of_nonneg_left hk (hv.beta_nonneg p hp)
  linarith

theorem zeroLow_offset_second {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
    (beta : ℝ → ℝ) (corr : ℝ → ℝ → ℝ)
    (hv : VerifierOn (Icc 0 1) phi lam beta corr)
    {p q z k : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hq : 0 ≤ q) (hqp : q ≤ p)
    (hpz : p ≤ z) (hzl : z ≤ lam) (hk : k ≤ packingK phi p q z) : q + beta p * k ≤ 0 := by
  have hx : (0 : ℝ) ∈ Ico (0 : ℝ) lam := ⟨le_rfl, h.lam_pos⟩
  have hh := hv.high_second p hp 0 hx q z hq hqp hpz (hzl.trans h.lam_lt_one.le)
  rw [rankPotential_low phi lam 0 q (hqp.trans (hpz.trans hzl)),
    rankPotential_low phi lam 0 z hzl,
    max_eq_right (neg_nonpos.mpr (h.nonnegative ⟨hp.1.trans hpz, hzl⟩)), zero_mul,
    add_zero, sub_zero] at hh
  have hb : q + beta p * packingK phi p q z ≤ 0 := nonpos_of_mul_nonpos_right hh (h.positive hx)
  have hbk := mul_le_mul_of_nonneg_left hk (hv.beta_nonneg p hp)
  linarith

end OptimalG
end

-- Source module OptimalG.MetricReduction
section
set_option autoImplicit true
/-! Full biased-metric equivalence for the actual finite-election distortion. -/

namespace OptimalG

def RunningMinBound (g : ℝ → ℝ) (lam : ℝ) : Prop :=
  ∀ (E : Election) (D : Lottery E.candidateCount), E.Stable g D →
    ∀ (a : E.Candidate) (rho : E.Candidate → ℝ),
      (∀ b, 0 ≤ rho b) → rho a = 0 →
        expectation E.voterWeight (fun v => expectation D.weight (runningMin (E.ordinalRank v) rho)) ≤
          lam * expectation E.voterWeight (fun v => maximumGap (E.ordinalRank v) rho)

theorem runningMin_violation_witness (g : ℝ → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (E : Election) (D : Lottery E.candidateCount) (hs : E.Stable g D)
    (a : E.Candidate) (rho : E.Candidate → ℝ) (hrho : ∀ b, 0 ≤ rho b) (ha : rho a = 0)
    (hv : lam * expectation E.voterWeight (fun v => maximumGap (E.ordinalRank v) rho) <
      expectation E.voterWeight (fun v => expectation D.weight (runningMin (E.ordinalRank v) rho))) :
    WitnessAbove g (1 + 2 * lam) := by
  obtain ⟨m, hconsistent, _hoptimal, hpositive, hratio⟩ :=
    exists_metric_of_strict_runningMin_violation E.ordinalRank rho E.voterWeight D.weight lam
      hrho E.voterWeight_nonneg E.voterWeight_total D.total hlam a ha hv
  refine ⟨E, D, hs, m.toPseudoMetricSpace, hconsistent, a, hpositive, ?_⟩
  rw [E.lotteryCost_eq_voter_average]
  exact (lt_div_iff₀ hpositive).mp hratio

theorem runningMinBound_implies_universalBound (g : ℝ → ℝ) (lam : ℝ)
    (hlam : 0 ≤ lam) (hbound : RunningMinBound g lam) :
    UniversalBound g (1 + 2 * lam) := by
  intro E D hs d hc a
  letI := d
  rw [E.lotteryCost_eq_voter_average]
  apply metric_distortion_upper_bound
    (fun v : E.Voter => (Sum.inl v : E.Point))
    (fun b : E.Candidate => (Sum.inr b : E.Point))
    E.ordinalRank E.voterWeight D.weight a lam E.voterWeight_nonneg D.nonneg D.total hlam hc
  exact hbound E D hs a (fun b => dist (Sum.inr a : E.Point) (Sum.inr b))
    (fun _ => dist_nonneg) (dist_self _)

theorem universalBound_iff_runningMinBound (g : ℝ → ℝ) (lam : ℝ) (hlam : 0 ≤ lam) :
    UniversalBound g (1 + 2 * lam) ↔ RunningMinBound g lam := by
  constructor
  · intro hbound E D hs a rho hrho ha
    by_contra h
    have hw := runningMin_violation_witness g lam hlam E D hs a rho hrho ha (lt_of_not_ge h)
    exact witnessAbove_not_universalBound g (1 + 2 * lam) hw hbound
  · exact runningMinBound_implies_universalBound g lam hlam

/-- Lemma 2.4, with the supremum over all actual finite stable elections. -/
theorem maximumDistortion_iff_runningMinBound (g : ℝ → ℝ) (lam : ℝ) (hlam : 0 ≤ lam) :
    maximumDistortion g ≤ ENNReal.ofReal (1 + 2 * lam) ↔ RunningMinBound g lam := by
  rw [maximumDistortion_le_iff g (1 + 2 * lam) (by linarith)]
  exact universalBound_iff_runningMinBound g lam hlam

end OptimalG
end

-- Source module OptimalG.FiniteVerifier
section
set_option autoImplicit true
/-!
# The finite-election verifier lemma

The four functional inequalities imply the universal metric-distortion bound.
All slices are constructed from the original finite election, including candidates
of zero lottery mass. The functions of mass need no analytic regularity.
-/
namespace OptimalG
open Set MeasureTheory
open scoped BigOperators

namespace Election

theorem voterWeight_pos (E : Election) (v : E.Voter) : 0 < E.voterWeight v := by
  exact one_div_pos.mpr (Nat.cast_pos.mpr E.voters_pos)

/-- The complete threshold integration step for actual finite elections. -/
theorem runningMin_le_of_sliceBounds (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (a : E.Candidate) (hrho : ∀ b, 0 ≤ rho b) (ha : rho a = 0)
    (lam : ℝ) (hlam : 0 ≤ lam) (W : ℝ → ℝ) (L : E.Voter → ℝ → ℝ)
    (hL : ∀ v x y, IntervalIntegrable (L v) volume x y)
    (hW : ∀ z ∈ Icc (0 : ℝ) 1, 0 ≤ W z)
    (hoffset : ∀ t, 0 ≤ t → expectation E.voterWeight (fun v => E.sliceWidth D rho v t) ≤
      expectation E.voterWeight (fun v => L v t))
    (hfirst : ∀ v t, 0 ≤ t → L v t ≤ lam - W (E.sliceWidth D rho v t))
    (hsecond : ∀ v t, 0 ≤ t → ∀ z, E.sliceRight D rho v t ≤ z → z ≤ E.leftRank D v a →
      L v t ≤ W z - W (E.sliceWidth D rho v t)) :
    expectation E.voterWeight (fun v => expectation D.weight (runningMin (E.ordinalRank v) rho)) ≤
      lam * expectation E.voterWeight (fun v => maximumGap (E.ordinalRank v) rho) := by
  let X := ∑ b, rho b
  have hX : 0 ≤ X := Finset.sum_nonneg (fun b _ => hrho b)
  have hrX (b : E.Candidate) : rho b ≤ X :=
    Finset.single_le_sum (fun b _ => hrho b) (Finset.mem_univ b)
  let q := E.sliceWidth D rho
  let delta := fun v => maximumGap (E.ordinalRank v) rho
  let F := fun v => extendedPotential W (q v) lam
  have hh := averaged_slice_bound E.voterWeight delta q L F X lam E.voterWeight_nonneg
    (fun v => maximumGap_nonneg (E.ordinalRank v) rho) hX hlam
    (fun v => E.sliceWidth_integrable D rho v 0 X) (fun v => hL v 0 X)
    (fun v => E.slice_extendedPotential_integrable D rho v W lam (-delta v) X)
    (fun v t ht => by simp [F, extendedPotential, ht])
    (fun v t ht => by
      simp only [F, extendedPotential, if_neg (not_lt.mpr ht)]
      exact hW _ (E.sliceWidth_mem_Icc D rho v t))
    (fun t ht => hoffset t ht.1) (by
      intro v t ht
      apply slice_bound_to_difference (L v) W (q v) (E.sliceRight D rho v) lam (delta v)
        (E.leftRank D v a) t ht.1 (hfirst v t ht.1) (hsecond v t ht.1)
      · exact E.sliceWidth_le_leftRank D rho a ha v
      · intro r _; exact E.slice_separation D rho v r)
  simpa only [q, E.slice_layer_cake D rho hrho X hrX] using hh

noncomputable def correctedSlice (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (a : E.Candidate) (phi : ℝ → ℝ) (lam : ℝ)
    (beta : ℝ → ℝ) (corr : ℝ → ℝ → ℝ) (v : E.Voter) (t : ℝ) : ℝ :=
  E.sliceWidth D rho v t + beta (E.sliceMass D rho t) * E.sliceScore D rho phi v t +
    sliceCorrection E.voterWeight (fun u => E.leftRank D u a < lam)
      (fun u => phi (E.leftRank D u a)) (fun u => corr (E.sliceMass D rho t) (E.leftRank D u a)) v

theorem correctedSlice_integrable (E : Election) (D : Lottery E.candidateCount)
    (rho : E.Candidate → ℝ) (a : E.Candidate) (phi : ℝ → ℝ) (lam : ℝ)
    (beta : ℝ → ℝ) (corr : ℝ → ℝ → ℝ) (v : E.Voter) (x y : ℝ) :
    IntervalIntegrable (E.correctedSlice D rho a phi lam beta corr v) volume x y :=
  thresholdSet_function_integrable rho
    (fun S => rankCut (E.rankWeights D v) (prefixBoundary (E.rankSet S v)) +
      beta (∑ b ∈ S, D.weight b) * E.blockScore phi D S v +
      sliceCorrection E.voterWeight (fun u => E.leftRank D u a < lam)
        (fun u => phi (E.leftRank D u a))
        (fun u => corr (∑ b ∈ S, D.weight b) (E.leftRank D u a)) v) x y

end Election

/-- Lemma 5.1, with coefficients extended to include the endpoint masses. -/
theorem verifier_runningMinBound {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
    (beta : ℝ → ℝ) (corr : ℝ → ℝ → ℝ)
    (hv : VerifierOn (Icc 0 1) phi lam beta corr) :
    RunningMinBound (normalizedActivation phi) lam := by
  intro E D hstable a rho hrho ha
  let s := fun v => E.leftRank D v a
  have hs : ∀ v, s v ∈ Icc (0 : ℝ) 1 := fun v => E.leftRank_mem_Icc D v a
  have hmean := E.stable_left_score_nonnegative phi D h.continuous h.decreasing
    h.denominator_pos h.integral_zero hstable a
  have hA0 := lowScoreMass_nonneg E.voterWeight s h E.voterWeight_nonneg hs
  rcases eq_or_lt_of_le hA0 with hAz | hA
  · have heq := all_ranks_equal_of_zero_lowScoreMass E.voterWeight s h E.voterWeight_pos hs hmean hAz.symm
    let L := fun v t => E.sliceWidth D rho v t + beta (E.sliceMass D rho t) * E.sliceScore D rho phi v t
    apply E.runningMin_le_of_sliceBounds D rho a hrho ha lam h.lam_pos.le (fun _ => 0) L
    · intro v x y
      exact thresholdSet_function_integrable rho
        (fun S => rankCut (E.rankWeights D v) (prefixBoundary (E.rankSet S v)) +
          beta (∑ b ∈ S, D.weight b) * E.blockScore phi D S v) x y
    · intro z hz; rfl
    · intro t ht
      change _ ≤ expectation E.voterWeight (fun v => E.sliceWidth D rho v t +
        beta (E.sliceMass D rho t) * E.sliceScore D rho phi v t)
      rw [expectation_add, expectation_smul, E.sliceScore_mean_zero D rho h hstable t]
      simp
    · intro v t ht
      simp only [sub_zero]
      apply zeroLow_offset_first h beta corr hv (E.sliceMass_mem_Icc D rho t)
        (E.sliceWidth_mem_Icc D rho v t).1 (E.sliceWidth_le_mass D rho v t)
      · simpa only [← heq v] using E.sliceWidth_le_leftRank D rho a ha v t ht
      · exact E.slice_packingDelta D rho phi h.continuous h.decreasing h.integral_zero v t
    · intro v t ht z hz hzs
      simp only [sub_self]
      apply zeroLow_offset_second h beta corr hv (E.sliceMass_mem_Icc D rho t)
        (E.sliceWidth_mem_Icc D rho v t).1 (E.sliceWidth_le_mass D rho v t)
        ((E.sliceMass_le_right D rho v t).trans hz)
      · simpa only [← heq v] using hzs
      · exact E.slice_packingK D rho phi h.continuous h.decreasing v t z hz
          (hzs.trans (hs v).2)
  · apply E.runningMin_le_of_sliceBounds D rho a hrho ha lam h.lam_pos.le
      (averagedRankPotential E.voterWeight s phi lam) (E.correctedSlice D rho a phi lam beta corr)
    · exact E.correctedSlice_integrable D rho a phi lam beta corr
    · intro z hz
      exact averagedRankPotential_nonneg E.voterWeight s h E.voterWeight_nonneg hs hA hz
    · intro t ht
      exact expected_slice_le_offset E.voterWeight (fun v => s v < lam)
        (fun v => phi (s v)) (fun v => corr (E.sliceMass D rho t) (s v))
        (fun v => E.sliceWidth D rho v t) (fun v => E.sliceScore D rho phi v t)
        (beta (E.sliceMass D rho t)) E.voterWeight_nonneg
        (fun v hl => hv.corr_nonneg _ (E.sliceMass_mem_Icc D rho t) _ ⟨(hs v).1, hl⟩)
        hA hmean (E.sliceScore_mean_zero D rho h hstable t)
    · intro v t ht
      exact offset_first E.voterWeight s h E.voterWeight_nonneg hs hA beta corr hv v
        _ _ _ (E.sliceMass_mem_Icc D rho t) (E.sliceWidth_mem_Icc D rho v t).1
        (E.sliceWidth_le_mass D rho v t) (E.sliceWidth_le_leftRank D rho a ha v t ht)
        (E.slice_packingDelta D rho phi h.continuous h.decreasing h.integral_zero v t)
    · intro v t ht z hz hzs
      exact offset_second E.voterWeight s h E.voterWeight_nonneg hs hA beta corr hv v
        _ _ z _ (E.sliceMass_mem_Icc D rho t) (E.sliceWidth_mem_Icc D rho v t).1
        (E.sliceWidth_le_mass D rho v t) ((E.sliceMass_le_right D rho v t).trans hz) hzs
        (E.slice_packingK D rho phi h.continuous h.decreasing v t z hz
          (hzs.trans (hs v).2))
        (E.slice_packingK D rho phi h.continuous h.decreasing v t (s v)
          (hz.trans hzs) (hs v).2)

/-- The universal metric-distortion conclusion for the original open-mass hypotheses. -/
theorem verifier_universalBound {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
    (beta : ℝ → ℝ) (corr : ℝ → ℝ → ℝ)
    (hv : VerifierOn (Ioo 0 1) phi lam beta corr) :
    UniversalBound (normalizedActivation phi) (1 + 2 * lam) := by
  obtain ⟨b, c, hbc⟩ := verifier_extend_endpoints h beta corr hv
  exact runningMinBound_implies_universalBound _ _ h.lam_pos.le (verifier_runningMinBound h b c hbc)

theorem verifier_maximumDistortion {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
    (beta : ℝ → ℝ) (corr : ℝ → ℝ → ℝ)
    (hv : VerifierOn (Ioo 0 1) phi lam beta corr) :
    maximumDistortion (normalizedActivation phi) ≤ ENNReal.ofReal (1 + 2 * lam) :=
  (maximumDistortion_le_iff _ _ (by linarith [h.lam_pos])).mpr (verifier_universalBound h beta corr hv)

end OptimalG
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

-- Source module UniversalTransfer
section
set_option autoImplicit true
namespace StableVotingDistortion
open PctDistortion

/-- Transfer the universal finite-election cost inequality from the permutation convention
to every public election with a minimax lottery and every consistent pseudometric. -/
theorem transfer_upper {g : ℝ → ℝ} (hg : IsActivation g) {K : ℝ}
    (hu : OptimalG.UniversalBound g K)
    {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C)
    {D : C → ℝ} (hD : IsGStable g E D) : HasDistortionAtMost E D K := by
  classical
  intro d hd hc a
  let ev := (Fintype.equivFin V).symm
  let ec := (Fintype.equivFin C).symm
  choose ballot hb using exists_ballot E
  let F : OptimalG.Election := {
    voterCount := Fintype.card V, candidateCount := Fintype.card C,
    voters_pos := Fintype.card_pos, candidates_pos := Fintype.card_pos,
    order := fun i => (ballot (ev i)).trans ec.symm }
  let Q : OptimalG.Lottery F.candidateCount := {
    weight := fun i => D (ec i), nonneg := fun i => hD.1.1 _, total := (ec.sum_comp D).trans hD.1.2 }
  have hact (i : F.Voter) (b : F.Candidate) : F.activation g Q i b = activation g E D (ev i) (ec b) := by
    rw [activation_eq_ordered E D _ (ballot _) (hb _)]
    simp [OptimalG.Election.activation,OptimalG.orderedActivation,F,Q]
  have hm (u : V → ℝ) : OptimalG.expectation F.voterWeight (fun i => u (ev i)) = voterMean u := by
    simp [OptimalG.expectation,OptimalG.Election.voterWeight,voterMean,F,one_div,← Finset.mul_sum,ev.sum_comp u]
  have hs : F.Stable g Q := by
    intro b
    simp_rw [hact]
    exact (hm (fun v => activation g E D v (ec b))).trans_le (theorem_4 hg E hD _)
  letI : PseudoMetricSpace (V ⊕ C) := {dist := d, dist_self := hd.self, dist_comm := hd.symm, dist_triangle := hd.triangle}
  let label : F.Point → (V ⊕ C) := Sum.map ev ec
  let dF : F.Metric := PseudoMetricSpace.induced label inferInstance
  have hdist (i : F.Voter) (b : F.Candidate) :
      @dist _ dF.toDist (Sum.inl i) (Sum.inr b) = d (Sum.inl (ev i)) (Sum.inr (ec b)) := rfl
  have hp (v : F.Voter) (b c : F.Candidate) :
      F.ordinalRank v c < F.ordinalRank v b ↔ E.prefers (ev v) (ec b) (ec c) := by
    change ((ballot (ev v)).symm (ec c)).val < ((ballot (ev v)).symm (ec b)).val ↔ _
    simpa only [Equiv.apply_symm_apply,Fin.lt_def] using
      (hb (ev v) ((ballot (ev v)).symm (ec b)) ((ballot (ev v)).symm (ec c))).symm
  have hcon : F.Consistent dF := by
    intro v b c h
    rw [hdist,hdist]
    rcases h.lt_or_eq with lt | eq
    · exact hc _ _ _ ((hp v b c).mp lt)
    · have he : c=b := (F.order v).symm.injective (Fin.ext eq)
      rw [he]
  have hcost (b : F.Candidate) : F.candidateCost dF b = candCost d (ec b) := by
    unfold OptimalG.Election.candidateCost candCost
    simp_rw [hdist]
    exact hm (fun v => d (Sum.inl v) (Sum.inr (ec b)))
  have hlott : F.lotteryCost dF Q = lotteryCost d D := by
    unfold OptimalG.Election.lotteryCost OptimalG.expectation lotteryCost
    simp_rw [hcost]
    exact ec.sum_comp (fun c => D c * candCost d c)
  have hbound := hu F Q hs dF hcon (ec.symm a)
  simpa only [hlott,hcost,Equiv.apply_symm_apply] using hbound


end StableVotingDistortion
end

-- Source module VerifierLemma
section
set_option autoImplicit true
namespace StableVotingDistortion
open Set PctDistortion

/-- Finite-election verifier under the paper's weak antitonicity assumption. -/
theorem lemma_8 {lam : ℝ} {ϕ β : ℝ → ℝ} {c : ℝ → ℝ → ℝ}
    (h : VerifierHypotheses lam ϕ β c)
    {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C)
    {D : C → ℝ} (hD : IsGStable (gPhi ϕ) E D) : HasDistortionAtMost E D (1 + 2 * lam) := by
  have hs := gPhi_properties h.score
  have hc : OptimalG.VerifierCurve ϕ lam := by
    refine ⟨h.score.lam_mem.1,h.score.lam_mem.2,h.score.continuousOn,h.score.antitoneOn,
      h.score.pos,h.score.integral_eq_zero,hs.1,h.score.at_one,h.score.le_lam_sub,?_⟩
    intro y z hy hyz hz
    have hf := h.antitoneOn_add ⟨hy,hyz.trans hz⟩ ⟨hy.trans hyz,hz⟩ hyz
    dsimp at hf
    linarith
  have hv : OptimalG.VerifierOn (Ioo 0 1) ϕ lam β c := by
    refine ⟨h.beta_nonneg,h.c_nonneg,?_,?_,?_,?_⟩
    · intro p hp x hx q hq hqp hqx
      exact (h.eq37 p hp x hx).1 q hq (le_min hqp hqx)
    · intro p hp x hx q hq hqp hpx
      exact (h.eq37 p hp x hx).2 q hq hqp hpx
    · intro p hp x hx q hq hqp
      exact (h.eq38 p hp x hx).1 q hq hqp
    · intro p hp x hx q z hq hqp hpz hz
      exact (h.eq38 p hp x hx).2 q z hq hqp hpz hz
  exact transfer_upper hs.2.2.1 (OptimalG.verifier_universalBound hc β c hv) E hD

end StableVotingDistortion
end

open PctDistortion
open StableVotingDistortion

theorem solution :
    ∀ {lam : ℝ} {ϕ β : ℝ → ℝ} {c : ℝ → ℝ → ℝ} (h : VerifierHypotheses lam ϕ β c)
    {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C) {D : C → ℝ}
    (hD : IsGStable (gPhi ϕ) E D),
    HasDistortionAtMost E D (1 + 2 * lam) :=
  @StableVotingDistortion.lemma_8
