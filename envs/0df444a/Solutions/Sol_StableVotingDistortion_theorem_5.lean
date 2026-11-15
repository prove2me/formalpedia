-- Prove2me | solution 1 for StableVotingDistortion.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T12:00:24.15971+00:00
-- url     : https://prove2.me/submissions/9c8c5b89-e7eb-46c4-a5cf-78e3894a6436

import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_HasDistortionAtMost
import Definitions.Def_StableVotingDistortion_IsPseudometric
import Definitions.Def_StableVotingDistortion_activation
import Definitions.Def_StableVotingDistortion_rhoV
import Definitions.Def_StableVotingDistortion_voterMean
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

-- Source module MetricEquivalence
section
set_option autoImplicit true
namespace StableVotingDistortion
open PctDistortion
open scoped BigOperators

variable {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C]

private theorem rho_eq_running {rank : C → ℕ} (E : Election V C) (v : V)
    (hr : ∀ b c, rank c ≤ rank b ↔ c = b ∨ E.prefers v b c) (ρ : C → ℝ) (b : C) :
    rhoV E ρ v b = OptimalG.runningMin rank ρ b := by
  classical
  unfold rhoV OptimalG.runningMin
  apply le_antisymm
  · apply Finset.le_inf'
    intro c _
    split_ifs with h
    · exact Finset.inf'_le ρ (Finset.mem_filter.mpr ⟨Finset.mem_univ c, (hr b c).mp h⟩)
    · exact Finset.inf'_le ρ (Finset.mem_filter.mpr ⟨Finset.mem_univ b, Or.inl rfl⟩)
  · apply Finset.le_inf'
    intro c hc
    have h := (hr b c).mpr (Finset.mem_filter.mp hc).2
    calc
      _ ≤ (if rank c ≤ rank b then ρ c else ρ b) := Finset.inf'_le _ (Finset.mem_univ c)
      _ = _ := if_pos h

private theorem cost_commute (d : V ⊕ C → V ⊕ C → ℝ) (D : C → ℝ) :
    lotteryCost d D = OptimalG.expectation (fun _ : V => (Fintype.card V : ℝ)⁻¹)
      (fun v => OptimalG.expectation D (fun b => d (Sum.inl v) (Sum.inr b))) := by
  rw [← OptimalG.expectation_commute]
  simp [lotteryCost, candCost, voterMean, OptimalG.expectation, Finset.mul_sum]

/-- The public Theorem 5, with arbitrary consistent pseudometrics and a fixed reference candidate. -/
theorem theorem_5 (E : Election V C) {D : C → ℝ} (hD : D ∈ stdSimplex ℝ C)
    (aStar : C) {lam : ℝ} (hlam : 0 ≤ lam) :
    (∀ d : V ⊕ C → V ⊕ C → ℝ, IsPseudometric d → Consistent E d →
        lotteryCost d D ≤ (1 + 2 * lam) * candCost d aStar) ↔
      ∀ ρ : C → ℝ, (∀ c, 0 ≤ ρ c) → ρ aStar = 0 →
        voterMean (fun v => Lv E D ρ v) ≤ lam * voterMean (fun v => Rv E ρ v) := by
  classical
  choose ballot hb using exists_ballot E
  let rank := fun v (c : C) => ((ballot v).symm c).val
  have hp (v : V) (b c : C) : E.prefers v b c ↔ rank v c < rank v b := by
    simpa only [rank, Fin.lt_def, Equiv.apply_symm_apply] using hb v ((ballot v).symm b) ((ballot v).symm c)
  have hr (v : V) (b c : C) : rank v c ≤ rank v b ↔ c = b ∨ E.prefers v b c := by
    rw [hp, le_iff_eq_or_lt]
    have hinj : Function.Injective (rank v) := Fin.val_injective.comp (ballot v).symm.injective
    rw [hinj.eq_iff]
  have hrho (ρ : C → ℝ) (v : V) (b : C) := rho_eq_running E v (hr v) ρ b
  let w := fun _ : V => (Fintype.card V : ℝ)⁻¹
  have hw (v : V) : 0 ≤ w v := by dsimp [w]; positivity
  have hw1 : ∑ v, w v = 1 := by simp [w, Fintype.card_ne_zero]
  have hm (f : V → ℝ) : voterMean f = OptimalG.expectation w f := by
    simp [voterMean, OptimalG.expectation, w, Finset.mul_sum]
  have hL (ρ : C → ℝ) (v : V) : Lv E D ρ v = OptimalG.expectation D (OptimalG.runningMin (rank v) ρ) := by
    simp only [Lv, OptimalG.expectation, hrho]
  have hR (ρ : C → ℝ) (v : V) : Rv E ρ v = OptimalG.maximumGap (rank v) ρ := by
    simp only [Rv, OptimalG.maximumGap, hrho]
  constructor
  · intro hall ρ hρ ha
    rw [hm, hm]; simp_rw [hL, hR]
    by_contra! hn
    obtain ⟨m, hmCons, _, hpos, hcost⟩ := OptimalG.exists_metric_of_strict_runningMin_violation
      rank ρ w D lam hρ hw hw1 hD.2 hlam aStar ha hn
    letI := m
    have hd : IsPseudometric (dist : V ⊕ C → _ → ℝ) :=
      ⟨fun _ _ => dist_nonneg, dist_self, dist_comm, dist_triangle⟩
    have hc : Consistent E (dist : V ⊕ C → _ → ℝ) := fun v b c h => hmCons v b c ((hp v b c).mp h).le
    have hbound := hall dist hd hc
    rw [cost_commute, candCost, hm] at hbound
    exact (not_lt_of_ge hbound) ((lt_div_iff₀ hpos).mp hcost)
  · intro hcert d hd hcon
    letI : PseudoMetricSpace (V ⊕ C) := { dist := d, dist_self := hd.self, dist_comm := hd.symm, dist_triangle := hd.triangle }
    rw [cost_commute, candCost, hm]
    apply OptimalG.metric_distortion_upper_bound (fun v : V => Sum.inl v) (fun b : C => Sum.inr b)
      rank w D aStar lam hw hD.1 hD.2 hlam
    · intro v b c h
      rcases (hr v b c).mp h with rfl | hpref
      · exact le_rfl
      · exact hcon v b c hpref
    · let ρ : C → ℝ := fun c => dist (Sum.inr aStar : V ⊕ C) (Sum.inr c)
      have hs := hcert ρ (fun c => hd.nonneg _ _) (hd.self _)
      change OptimalG.expectation w (fun v => OptimalG.expectation D (OptimalG.runningMin (rank v) ρ)) ≤ lam * OptimalG.expectation w (fun v => OptimalG.maximumGap (rank v) ρ)
      simpa only [hm, hL, hR] using hs

end StableVotingDistortion
end

open PctDistortion
open StableVotingDistortion

theorem solution :
    ∀ {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C)
    {D : C → ℝ} (hD : D ∈ stdSimplex ℝ C) (aStar : C) {lam : ℝ} (hlam : 0 ≤ lam),
    (∀ d : V ⊕ C → V ⊕ C → ℝ, IsPseudometric d → Consistent E d →
        lotteryCost d D ≤ (1 + 2 * lam) * candCost d aStar) ↔
      ∀ ρ : C → ℝ, (∀ c, 0 ≤ ρ c) → ρ aStar = 0 →
        voterMean (fun v => Lv E D ρ v) ≤ lam * voterMean (fun v => Rv E ρ v) :=
  @StableVotingDistortion.theorem_5
