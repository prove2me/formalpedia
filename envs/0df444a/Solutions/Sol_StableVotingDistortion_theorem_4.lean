-- Prove2me | solution 1 for StableVotingDistortion.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T12:00:23.029812+00:00
-- url     : https://prove2.me/submissions/df9f1d78-4c9f-44ed-82b5-470469d7be7d

import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_IsGStable
import Definitions.Def_StableVotingDistortion_activation
import Definitions.Def_StableVotingDistortion_voterMean
import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.MetricSpace.Basic

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

-- Source module OptimalG.External.FixedPointTheorems.cubical_sperner_prep
section
set_option autoImplicit true
open Classical


/-
The Cubical Sperner's Lemma.
We mostly follow Kuhn 1960 "Some Combinatorial Lemmas in Topology"
-/

structure SpernerCube where
  n : ℕ
  p : ℕ
  RL : (Fin n → Fin (p+1)) → ℕ
  rl_proper : ∀ (I: Fin n → Fin (p+1) ), RL I ≤ n ∧
      ∀ (k : Fin n), (I k = 0 → RL I ≠ k.1) ∧ (I k = p → RL I ≤ k.1)

namespace SpernerCube

def G (SC : SpernerCube) := Fin SC.n → Fin (SC.p+1)

instance Gfin (SC : SpernerCube): Fintype SC.G := by {
  exact Pi.instFintype
}

end SpernerCube

variable (SC : SpernerCube)
variable {n1 : ℕ}
variable {hn1 : n1 + 1 = SC.n}


def simplex (m:ℕ ) (I : Fin (m+1)→ SC.G) := Function.Injective I
    ∧ ∀ i < m, ∀ j : Fin SC.n, (I (Fin.ofNat _ i) j).1 ≤ (I (Fin.ofNat _ (i+1)) j).1
    ∧ (I (Fin.last m) j).1 ≤ (I 0 j).1 + 1

def complete_simplex (m:ℕ ) (I : Fin (m+1) → SC.G ) := simplex SC m I
    ∧ Set.range (fun (i:Fin (m+1))↦ SC.RL (I i)) = {j : ℕ | j ≤ m}

def is_face I J :=
    simplex SC n1 I ∧ simplex SC SC.n J ∧ Set.range I ⊆ Set.range J

def is_boundary_face I := ∃! J, @is_face SC n1 I J

def complete_boundary_face I := is_boundary_face SC I ∧ complete_simplex SC n1 I

def case_A (I : Fin (n1 +1) → SC.G) := ∃ j, ∀ k, I k j = 0

def case_B (I : Fin (n1 +1) → SC.G) := ∃ j, ∀ k, I k j = Fin.last SC.p

def case_C (I : Fin (n1 +1) → SC.G) :=
    ∃ j, ∃ (q : Fin (SC.p + 1)), (q ≠ 0 ∧ q ≠ Fin.last SC.p ) ∧ ∀ k, I k j = q

def case_D (I : Fin (n1 +1) → SC.G) := ∀ j, ∀ q, ∃ k,I k j ≠ q


lemma one_of_ABCD (I : Fin (n1 +1) → SC.G) :
    case_A SC I ∨ case_B SC I ∨ case_C SC I ∨ case_D SC I := by {
  by_cases h1 : case_D SC I
  exact Or.inr (Or.inr (Or.inr h1))
  unfold case_D at h1
  push Not at h1
  obtain ⟨j , ⟨ q, h2 ⟩⟩ := h1
  by_cases q0 : q = 0
  {
    apply Or.inl
    use j
    rwa [← q0]
  }
  by_cases qp : q = Fin.last SC.p
  {
    apply Or.inr (Or.inl _)
    use j
    intro k
    rwa [h2 k]
  }
  suffices h3 : case_C SC I by {
    simp only [h3, true_or, or_true]
  }
  use j, q
}


section simplex_properties


lemma monotone_1_of_simplex {m:ℕ } (I : Fin (m+1)→ SC.G) (hs : simplex SC m I) (i1 i2 : Fin (m+1))
    (h1 : i1 ≤ i2) : ∀ j, I i1 j ≤ I i2 j := by {
  intro j
  let f := fun i ↦ I i j
  have h2 := @Fin.monotone_iff_le_succ m _ _ f
  suffices h3 : Monotone f by exact (h3 h1)
  rw [h2]
  clear i1 i2 h1
  intro i1
  have h3 := (hs.2 i1.1 i1.2 j).1
  simp only [Fin.val_fin_le] at h3
  convert h3 <;> ext <;> simp [Fin.ofNat_eq_cast, Nat.mod_eq_of_lt]
}

lemma monotone_2_of_simplex {m:ℕ } (I : Fin (m+1)→ SC.G) (hs : simplex SC m I) (i1 i2 : Fin (m+1)) :
    i1 ≤ i2 ↔ ∀ j, I i1 j ≤ I i2 j := by {
  apply Iff.intro
  {
    intro h1 j
    apply monotone_1_of_simplex _ I hs i1 i2 h1
  }
  {
    intro h1
    by_contra h2
    have h3 : i1 ≠ i2 := ne_of_not_le h2
    apply h3
    apply hs.1
    apply funext
    intro j
    apply le_antisymm (h1 j)
    apply monotone_1_of_simplex _ _ hs i2 i1 (le_of_not_ge h2)
  }
}

lemma last_of_simplex {m: ℕ} I (hs : simplex SC m I) j :
    (I (Fin.last m) j).1 ≤ (I 0 j).1 + 1 := by {
  cases m
  simp only [Fin.last_zero, Fin.isValue, le_add_iff_nonneg_right, zero_le]
  rename_i m
  have h3 : 0 < m + 1 := by omega
  exact (hs.2 0 h3 j).2
}

lemma le_add_one_of_simplex {m: ℕ} I (hs : simplex SC m I) (i1 i2 : Fin (m+1)) j :
    (I i1 j).1 ≤ (I i2 j).1 + 1 := by {
  have h1 := last_of_simplex SC I hs j
  apply le_trans _ (le_trans h1 _)
  apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last i1)
  apply Nat.add_le_add_right
  apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le i2)
}

end simplex_properties


lemma p_ne_zero_of_cube {hn1 : n1 + 1 = SC.n}: Fin.last SC.p ≠ 0 := by {
  simp only [ne_eq, Fin.last_eq_zero_iff]
  intro h1
  let v : Fin SC.n → Fin (SC.p + 1) := fun _ ↦ 0
  have h3 : NeZero SC.n := by {
    rw [←hn1]
    exact instNeZeroNatHAdd_1
  }
  have h4 : v 0 = 0 := by {rfl}
  have h2 := (SC.rl_proper v).2 0
  simp only [Fin.val_zero, ne_eq, h1, Fin.val_eq_zero_iff, nonpos_iff_eq_zero] at h2
  exact h2.1 h4 (h2.2 h4)
}


section simplex_child


def insert_index (j : Fin (SC.n+1)) (a: Fin (n1 +1 )) : Fin (SC.n+1) :=
{ val := if a.val < j.val then a.val else a.val+1,
  isLt := by {
    by_cases hlt : a.val < j.val
    {
      simp only [hlt, ↓reduceIte]
      exact Nat.lt_trans hlt j.2
    }
    {
      simp only [hlt, ↓reduceIte, add_lt_add_iff_right]
      rw [← hn1]
      exact a.2
    }
} }

def delete_vertex (j: Fin (SC.n+1)) (I : Fin (SC.n+1)→ SC.G) : Fin (n1 + 1) → SC.G :=
  fun a ↦ I (@insert_index SC n1 hn1 j a)

lemma insert_index_ne j a : @insert_index SC n1 hn1 j a ≠ j := by {
  apply Fin.ne_of_val_ne
  unfold insert_index
  by_cases hlt : a.val < j.val
  {
    simp only [hlt, ↓reduceIte]
    omega
  }
  {
    simp only [hlt, ↓reduceIte, ne_eq]
    omega
  }
}

lemma almost_surjective_of_insert_index (j : Fin (SC.n+1)) (a : Fin (SC.n+1)) (h : a ≠ j)
    : ∃ k : Fin (n1 + 1) , a = @insert_index SC n1 hn1 j k := by {
  unfold insert_index
  by_cases hlt : a.1 < j.1
  {
    use (Fin.ofNat _ a.1)
    have h2 : a.1 = (Fin.ofNat (n1 + 1) a.1) := by {
      rw [Fin.ofNat_eq_cast, Fin.val_cast_of_lt]
      rw [hn1]
      apply lt_of_lt_of_le hlt
      exact Fin.is_le j
    }
    simp only [← h2, hlt]
    rfl
  }
  {
    have h2 : j.1 < a.1 := by {
      have := Fin.val_ne_of_ne (id (Ne.symm h))
      omega
    }
    let a1 := a.1 - 1
    have h3 : a1 + 1 = a.1 := by {
      show a.1 - 1 + 1 = a.1
      omega
    }
    let a1f := Fin.ofNat (n1 + 1) a1
    use a1f
    ext
    have h4 : a1 < n1 +1 := by {
      have h5 := a.2
      show a.1 - 1 < n1 + 1
      omega
    }
    have h6 : a1f.1 = a1 := by {
      unfold a1f
      simp only [Fin.ofNat_eq_cast, Fin.val_natCast, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one]
      exact h4
    }
    have h5 : ¬ (a1f < j.1) := by {
      simp only [not_lt, h6]
      show j.1 ≤ a.1 - 1
      omega
    }
    simp only [h5, ↓reduceIte]
    rw [← h3, h6]
  }
}

lemma insert_index_strict_mono j : StrictMono (@insert_index SC n1 hn1 j) := by {
  intro a b h1
  have h2 : a.1 < b.1 := by {exact h1}
  have h21 : a.1 < b.1 + 1 := by omega
  unfold insert_index
  by_cases h3 : a.1 < j.1
  {
    by_cases h4 : b.1 < j.1
    repeat {
      simp only [h3, ↓reduceIte, h4, Fin.mk_lt_mk, Fin.val_fin_lt, gt_iff_lt]
      assumption
    }
  }
  {
    by_cases h4 : b.1 < j.1
    {
      simp only [h3, ↓reduceIte, h4, Fin.mk_lt_mk, gt_iff_lt]
      omega
    }
    {
      simp only [h3, ↓reduceIte, h4, Fin.mk_lt_mk, gt_iff_lt]
      omega
    }
  }
}

lemma insert_index_inj j : Function.Injective (@insert_index SC n1 hn1 j) := by {
  apply StrictMono.injective
  apply insert_index_strict_mono
}


lemma delete_vertex_inj J {hs : simplex SC SC.n J} i1 i2
    (h1 : @delete_vertex SC n1 hn1 i1 J = @delete_vertex SC n1 hn1 i2 J ) : i1 = i2 := by {
  by_contra h2
  obtain ⟨k, h3 ⟩ := @almost_surjective_of_insert_index SC n1 hn1 i2 i1 h2
  apply @insert_index_ne SC n1 hn1 i1 k
  apply hs.1
  nth_rewrite 2 [h3]
  exact (congrFun h1) k
}

lemma delete_vertex_simplex J {hs : simplex SC SC.n J} i :
    simplex SC n1 (@delete_vertex SC n1 hn1 i J) := by {
  apply And.intro
  {
    intro k1 k2 h2
    apply insert_index_inj SC i
    apply hs.1 h2
  }
  {
    intro i2 hi2 j
    unfold delete_vertex
    apply And.intro
    {
      apply monotone_1_of_simplex SC J hs
      rw [StrictMono.le_iff_le]
      {
        simp only [Fin.ofNat_eq_cast]
        apply Fin.natCast_mono hi2
        exact Nat.le_add_right i2 1
      }
      apply insert_index_strict_mono
    }
    apply le_add_one_of_simplex SC J hs
  }
}

lemma delete_vertex_is_face J {hs : simplex SC SC.n J} i :
    is_face SC (@delete_vertex SC n1 hn1 i J) J := by {
  apply And.intro
  {
    apply delete_vertex_simplex
    exact hs
  }
  {
    apply And.intro hs
    intro c hc
    obtain ⟨ i2, hi2 ⟩ := hc
    use @insert_index SC n1 hn1 i i2
    exact hi2
  }
}

lemma is_id_of_strict_mono (m: ℕ ) (f : Fin m → Fin m) (hsm : StrictMono f)
    : ∀ k, f k = k := by {
  suffices h1 : ∀ (a : ℕ), ∀ k, k.1 < a → f k = k by {
    intro k
    exact h1 m k k.2
  }
  intro a
  induction' a with a ha
  {
    intro k h1
    omega
  }
  {
    have h1 : Function.Injective f := by {exact StrictMono.injective hsm}
    have h2 : Function.Surjective f := Finite.surjective_of_injective h1
    intro k hk
    have h3 j : j < k → f j = j := by {
      intro hj
      apply ha
      omega
    }
    by_cases h4 : f k < k
    apply h1 (h3 (f k) h4)
    simp only [not_lt] at h4
    apply le_antisymm _ h4
    obtain ⟨l, h9⟩ := h2 k
    suffices h8 : k ≤ l by {rwa [← hsm.le_iff_le, h9] at h8}
    by_contra! h6
    have h7 := h3 l h6
    rw [h9] at h7
    rw [h7] at h6
    exact (lt_self_iff_false l).mp h6
  }
}

lemma is_insert_index_of_strict_mono f (hsm : StrictMono f)
    : ∃ j, f = @insert_index SC n1 hn1 j := by {
  have h31 : Function.Injective f := by {exact hsm.injective}
  have hns : ∃ j, ∀ i, f i ≠ j := by {
    by_contra! h1
    have h2 : Function.Surjective f := by {exact h1 }
    have h5 : Function.Bijective f :=  And.intro h31 h2
    have h4 := Nat.card_eq_of_bijective f h5
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.add_right_cancel_iff] at h4
    rw [h4] at hn1
    simp only [Nat.add_eq_left, one_ne_zero] at hn1
  }
  obtain ⟨ j, hj⟩ := hns
  use j
  have h1 : ∀ k1, ∃ k2, f k1 = @insert_index SC n1 hn1 j k2 := by {
    intro k1
    apply almost_surjective_of_insert_index
    exact hj k1
  }
  obtain ⟨g, hg⟩ := axiomOfChoice h1
  have h2 : StrictMono g := by {
    intro k1 k2
    contrapose!
    intro h4
    rw [←hsm.le_iff_le, hg k1, hg k2]
    have h5 := @insert_index_strict_mono SC n1 hn1 j
    rw [h5.le_iff_le]
    exact h4
  }
  have h3 := is_id_of_strict_mono _ g h2
  ext1 k
  rw [hg k, h3 k]
}

lemma child_simplex_char (I : Fin (n1 +1) → SC.G) J {hs : simplex SC SC.n J}
    : is_face SC I J ↔ ∃ i, I = @delete_vertex SC n1 hn1 i J := by {
  apply Iff.intro
  {
    intro h1
    have h2 : ∃ (f : Fin (n1+1) → Fin (SC.n+1)), ∀ k, I k = J (f k) := by {
      have h2 := h1.2.2
      have h3 : ∀ k, ∃ j, I k = J j := by {
        intro k
        have h4 : I k ∈ Set.range I := by {
          exact Set.mem_range_self k
        }
        have h3 := h2 h4
        obtain ⟨j, hj⟩ := h2 h4
        use j
        exact hj.symm
      }
      apply axiom_of_choice h3
    }
    obtain ⟨f, hf ⟩ := h2
    have h31 : Function.Injective f := by {
      intro k1 k2 h2
      apply h1.1.1
      rw [hf k1, hf k2, h2]
    }
    have h3 : StrictMono f := by {
      apply Monotone.strictMono_of_injective _ h31
      intro k1 k2 h2
      rw [monotone_2_of_simplex SC J hs]
      rw [← hf k1, ← hf k2]
      rwa [←monotone_2_of_simplex SC I h1.1]
    }
    obtain ⟨j, hj⟩ := is_insert_index_of_strict_mono SC f h3
    use j
    ext k
    unfold delete_vertex
    rw [hf k, hj]
  }
  {
    intro h1
    obtain ⟨ i, hi⟩ := h1
    rw [hi]
    apply @delete_vertex_is_face SC _ _ J hs
  }
}

end simplex_child


section cases_ABCD

lemma insert_vertex I (v : SC.G) j :
    ∃ J, I = @delete_vertex SC n1 hn1 j J ∧ J j = v := by {
  have h1 : ∀ j2, ∃ w, (j2 = j → w = v)
      ∧ ∀ i, @insert_index SC n1 hn1 j i = j2 → I i = w := by {
    intro j2
    by_cases h1 : j2 = j
    {
      use v
      simp only [implies_true, true_and]
      intro i
      have h3 : @insert_index SC n1 hn1 j i ≠ j := by {apply insert_index_ne}
      simp only [h1, h3, IsEmpty.forall_iff]
    }
    {
      have h3 : ∃ i, j2 = @insert_index SC n1 hn1 j i := by {
        apply almost_surjective_of_insert_index
        exact h1
      }
      obtain ⟨ i, hi⟩ := h3
      use (I i)
      simp only [h1, IsEmpty.forall_iff, true_and]
      intro i2 h2
      congr!
      apply insert_index_inj SC j
      rw [h2, hi]
    }
  }
  obtain ⟨J, h2⟩ := axiomOfChoice h1
  use J
  apply And.intro
  {
    ext i
    exact (h2 (@insert_index SC n1 hn1 j i)).2 i rfl
  }
  exact (h2 j).1 rfl
}

lemma surround_index (j : Fin (SC.n + 1)) (i : Fin (n1 + 1)) (hij : i.1 + 1 = j.1 )
    (hj1 : j ≠ Fin.last SC.n): ((@insert_index SC n1 hn1 j i).1 + 1 = j.1
    ∧ j.1 + 1 = @insert_index SC n1 hn1 j (i+1)) := by {
  unfold insert_index
  have h2 : i.1 < j.1 := by omega
  have h3 : (i+1).1 = i.1 + 1 := by {
    refine Fin.val_add_one_of_lt ?_
    simp only [Nat.succ_eq_add_one]
    show i.1 < n1
    have h6 := Fin.val_lt_last hj1
    omega
  }
  apply And.intro
  {
    simp only [h2, ↓reduceIte]
    exact hij
  }
  simp only [h3, hij, lt_self_iff_false, ↓reduceIte]
}

lemma parent_injective I (hs : simplex SC n1 I) J j
    (h1 : I = @delete_vertex SC n1 hn1 j J) (h2 : J j ∉ Set.range I)
    : Function.Injective J := by {
  have h5 j3 : j3 ≠ j → ∃ i3, j3 = @insert_index SC n1 hn1 j i3
    := by {apply almost_surjective_of_insert_index}
  intro j1 j2 h4
  have h7 j3 : J j3 = J j → j3 = j := by {
      intro h7
      by_contra h51
      apply h2
      obtain ⟨i3, hi3⟩ := h5 j3 h51
      use i3
      rw [←h7,h1,hi3]
      rfl
  }
  by_cases h8 : j1 = j
  {
    rw [h8, h7 j2]
    rw [←h8,h4]
  }
  by_cases h9 : j2 = j
  {
    rw [h9, h7 j1]
    rw [←h9,h4]
  }
  obtain ⟨i1, hi1⟩ := h5 j1 h8
  obtain ⟨i2, hi2⟩ := h5 j2 h9
  suffices h11 : i1 = i2 by {rw [hi1,hi2,h11] }
  apply hs.1
  rw [h1]
  unfold delete_vertex
  rw [← hi1,← hi2, h4]
}

lemma parent_simplex_case_BC I (hs : simplex SC n1 I) J
    (h1 : I = @delete_vertex SC n1 hn1 0 J) (h2 : J 0 ≠ I 0)
    (h3 : ∀ k, J 0 k ≤ I 0 k ∧ (I (Fin.last n1) k).1 ≤ (J 0 k).1 + 1) : is_face SC I J := by {
  suffices h4 : simplex SC SC.n J by {
    rw [child_simplex_char]
    use 0
    exact h4
  }
  have h4 : J 0 ∉ Set.range I := by {
    intro h5
    obtain ⟨i1, hi1⟩ := h5
    apply h2
    apply funext
    intro k
    apply le_antisymm (h3 k).1
    rw [←hi1]
    apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le i1)
  }
  apply And.intro ( parent_injective SC I hs J 0 h1 h4)
  have h5 j2 : j2 < n1 + 1 →  J (Fin.ofNat _ (j2+1)) = I (Fin.ofNat _ j2) := by {
    rw [h1]
    unfold delete_vertex insert_index
    congr! with h7
    simp only [Fin.ofNat_eq_cast, Fin.val_zero, not_lt_zero, ↓reduceIte]
    rw [Fin.val_cast_of_lt, Fin.val_cast_of_lt h7]
    omega
  }
  intro j1 hj1 k1
  apply And.intro
  {
    rw [←hn1] at hj1
    rw [h5 j1 hj1]
    cases j1
    {
      simp only [Fin.ofNat_eq_cast, Fin.val_fin_le]
      exact (h3 k1).1
    }
    rename_i j2
    rw [h5 j2]
    apply monotone_1_of_simplex SC I hs
    simp only [Fin.ofNat_eq_cast]
    apply Fin.natCast_mono
    exact Nat.le_of_lt_succ hj1
    exact Nat.le_add_right j2 1
    exact Nat.lt_of_succ_lt hj1
  }
  {
    have h6 := h5 n1 (lt_add_one n1)
    have e1 : (Fin.ofNat (SC.n + 1) (n1 + 1) : Fin (SC.n + 1)) = Fin.last SC.n := by
      rw [← hn1]; simp [Fin.ofNat_eq_cast, Fin.natCast_eq_last]
    have e2 : (Fin.ofNat (n1 + 1) n1 : Fin (n1 + 1)) = Fin.last n1 := by
      simp [Fin.ofNat_eq_cast, Fin.natCast_eq_last]
    rw [e1, e2] at h6
    rw [congrFun h6 k1]
    exact (h3 k1).2
  }
}

lemma parent_simplex_case_AC I (hs : simplex SC n1 I) J j (hj : j = Fin.last SC.n)
    (h1 : I = @delete_vertex SC n1 hn1 j J) (h2 : J j ≠ I (Fin.last n1))
    (h3 : ∀ k, I (Fin.last n1) k ≤ J j k ∧ (J j k).1 ≤ (I 0 k).1 + 1) : is_face SC I J := by {
  suffices h4 : simplex SC SC.n J by {
    rw [child_simplex_char]
    use j
    exact h4
  }
  have h4 : J j ∉ Set.range I := by {
    intro h5
    obtain ⟨i1, hi1⟩ := h5
    apply h2
    apply funext
    intro k
    apply le_antisymm _ (h3 k).1
    rw [←hi1]
    apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last i1)
  }
  have h5 j2 : j2 < SC.n → J (Fin.ofNat _ j2) = I (Fin.ofNat _ j2) := by {
    intro h6
    rw [h1,hj]
    unfold delete_vertex insert_index
    congr!
    have h7 : (Fin.ofNat (n1+1) j2).1 < (Fin.last SC.n).1 := by {
      simp only [Fin.ofNat_eq_cast, Fin.val_last]
      rw [Fin.val_cast_of_lt]
      exact h6
      rwa [←hn1] at h6
    }
    simp only [h7,↓reduceIte]
    simp only [Fin.ofNat_eq_cast]
    rw [Fin.val_cast_of_lt, Fin.val_cast_of_lt]
    rwa [←hn1] at h6
    exact Nat.lt_add_right 1 h6
  }
  apply And.intro ( parent_injective SC I hs J j h1 h4)
  intro j1 hj1 k1
  apply And.intro
  {
    rw [h5 _ hj1]
    by_cases h12 : j1 + 1 < SC.n
    {
      rw [h5 _ h12]
      apply monotone_1_of_simplex SC I hs
      simp only [Fin.ofNat_eq_cast]
      apply Fin.natCast_mono
      apply Nat.le_of_lt_add_one
      rwa [hn1]
      exact Nat.le_add_right j1 1
    }
    have h16 : j1+1 = SC.n := by omega
    have h13 : Fin.ofNat _ j1 = Fin.last n1 := by {
      suffices h15 : j1 = n1 by {
        simp only [h15, Fin.ofNat_eq_cast, Fin.natCast_eq_last]
      }
      omega
    }
    have h14 : Fin.ofNat _ (j1+1) = j := by {
      rw [hj]
      simp only [h16, Fin.ofNat_eq_cast, Fin.natCast_eq_last]
    }
    rw [h13,h14]
    exact (h3 k1).1
  }
  {
    have h7 : J 0 = I 0 := by {
      have h6 := h5 0 (Nat.zero_lt_of_lt hj1)
      simp only [Fin.ofNat_eq_cast] at h6
      exact h6
    }
    rw [h7,←hj]
    exact (h3 k1).2
  }
}

lemma parent_simplex_case_D I (hs : simplex SC n1 I) J j i
    (hij : i.1 + 1 = j.1 ) (h1 : I = @delete_vertex SC n1 hn1 j J) (h2 : J j ∉ Set.range I)
    (h3 : ∀ k, I i k ≤ J j k ∧ J j k ≤ I (i+1) k) : is_face SC I J := by {
  suffices h4 : simplex SC SC.n J by {
    rw [child_simplex_char]
    use j
    exact h4
  }
  have h5 j3 : j3 ≠ j → ∃ i3, j3 = @insert_index SC n1 hn1 j i3 := by {
    apply almost_surjective_of_insert_index
  }
  have h6 j3 : j3 ≠ j → ∃ i3, I i3 = J j3 := by {
    intro h7
    obtain ⟨i3, hi3⟩ := h5 j3 h7
    use i3
    rw [h1, hi3]
    rfl
  }
  apply And.intro (parent_injective SC I hs J j h1 h2)
  intro i2 h4 k2
  have h5 := h3 k2
  apply And.intro
  {
    simp only [Fin.ofNat_eq_cast, Fin.val_fin_le]
    rw [h1] at h5
    unfold delete_vertex at h5
    have h6 : (@insert_index SC n1 hn1 j i).1 + 1 = j := by {
      unfold insert_index
      have h7 : i.1 < j.1 := by omega
      simp only [h7, ↓reduceIte]
      exact hij
    }
    by_cases h8 : i2 = j.1
    {
      convert h5.2
      simp only [h8, Fin.cast_val_eq_self]
      have h11 : j ≠ Fin.last SC.n := by {
        suffices h12 : j.1 ≠ SC.n by exact Ne.symm (Fin.ne_of_val_ne (Ne.symm h12))
        rw [←h8]
        exact Nat.ne_of_lt h4
      }
      have h9 := @surround_index SC n1 hn1 j i hij h11
      rw [h8, h9.2]
      exact Fin.cast_val_eq_self (insert_index SC j (i + 1))
    }
    by_cases h9 : i2 + 1 = j.1
    {
      rw [←h9] at h6
      simp only [Nat.add_right_cancel_iff] at h6
      convert h5.1
      rw [←h6]
      simp only [Fin.cast_val_eq_self]
      rw [h9]
      simp only [Fin.cast_val_eq_self]
    }
    have h11 : ∃ i3, (Fin.ofNat _ i2) = @insert_index SC n1 hn1 j i3 := by {
      apply almost_surjective_of_insert_index
      intro h12
      apply h8
      rw [← h12]
      simp only [Fin.ofNat_eq_cast]
      rw [Fin.val_cast_of_lt]
      apply lt_trans h4 (lt_add_one SC.n)
    }
    have h12 : ∃ i3, (Fin.ofNat _ (i2+1)) = @insert_index SC n1 hn1 j i3 := by {
      apply almost_surjective_of_insert_index
      intro h12
      apply h9
      rw [← h12]
      simp only [Fin.ofNat_eq_cast]
      rw [Fin.val_cast_of_lt]
      omega
    }
    simp only [Fin.ofNat_eq_cast] at h11 h12
    obtain ⟨i3, hi3⟩ := h11
    obtain ⟨i4, hi4⟩ := h12
    rw [hi3, hi4]
    suffices h21 : I i3 k2 ≤ I i4 k2 by {rwa [h1] at h21}
    apply monotone_1_of_simplex SC I hs
    have h21 : StrictMono (@insert_index SC n1 hn1 j) := by {
      apply insert_index_strict_mono
    }
    rw [←h21.le_iff_le]
    rw [←hi3, ← hi4]
    refine (Fin.natCast_le_natCast ?_ h4).mpr ?_
    exact Nat.le_of_succ_le h4
    exact Nat.le_succ i2
  }
  {
    have h11 : (J (Fin.last SC.n) k2).1 ≤ (I (Fin.last n1) k2).1 := by {
      simp only [Fin.val_fin_le]
      by_cases h12 : Fin.last SC.n = j
      {
        rw [h12]
        apply le_trans h5.2
        apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last _)
      }
      obtain ⟨ i3, hi3⟩ := h6 _ h12
      rw [←hi3]
      apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last _)
    }
    have h13 := last_of_simplex SC I hs k2
    apply le_trans h11 (le_trans h13 _)
    simp only [add_le_add_iff_right, Fin.val_fin_le]
    by_cases h14 : 0 = j
    {
      rw [h14]
      apply le_trans _ h5.1
      apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le _)
    }
    {
      obtain ⟨i3, hi3⟩ := h6 _ h14
      rw [← hi3]
      apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le _)
    }
  }
}


noncomputable def coord_change_count (v1 v2 : SC.G) := Finset.card {i | v1 i ≠ v2 i}

lemma ccc_add {m} I (hs : simplex SC m I) (i1 i2 i3) (h1 : i1 ≤ i2 ∧ i2 ≤ i3) :
    coord_change_count SC (I i1) (I i3) =
    coord_change_count SC (I i1) (I i2) + coord_change_count SC (I i2) (I i3) := by {
  unfold coord_change_count
  rw [←Finset.card_union_of_disjoint]
  congr
  apply Finset.ext_iff.mpr
  intro k2
  simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  rw [←Decidable.not_and_iff_not_or_not]
  apply Iff.intro
  {
    intro h3 h4
    apply h3
    rw [h4.1, h4.2]
  }
  {
    intro h2 h3
    apply h2
    have h4 := monotone_1_of_simplex SC I hs i1 i2 h1.1 k2
    have h5 := monotone_1_of_simplex SC I hs i2 i3 h1.2 k2
    rw [h3] at h4 ⊢
    suffices h1 : I i3 k2 = I i2 k2 by exact ⟨h1, Eq.symm h1⟩
    exact Fin.le_antisymm h4 h5
  }
  {
    apply Finset.disjoint_filter.mpr
    intro k1 hk1 h2 h3
    apply h3
    have h4 : ∀ k, I i1 k ≤ I i2 k :=  monotone_1_of_simplex SC I hs i1 i2 h1.1
    have h5 : I i1 k1 < I i2 k1 := lt_of_le_of_ne (h4 k1) h2
    have h6 : (I i3 k1).1 ≤ (I i1 k1).1 + 1 := by {
      apply le_add_one_of_simplex _ _ hs
    }
    apply le_antisymm ( monotone_1_of_simplex SC I hs i2 i3 h1.2 k1)
    apply le_trans h6 h5
  }
}

lemma ccc_pos {m} I (hs : simplex SC m I) i1 i2 (h1 : i1 ≠ i2)
    : 0 < coord_change_count SC (I i1) (I i2) := by {
  unfold coord_change_count
  by_contra! h2
  apply h1
  apply hs.1
  simp only [ne_eq, nonpos_iff_eq_zero, Finset.card_eq_zero] at h2
  apply funext
  intro k
  rw [Finset.filter_eq_empty_iff] at h2
  simp only [Finset.mem_univ, Decidable.not_not, forall_const] at h2
  apply h2
}

noncomputable def ccc_fun {m} (I : Fin (m+1)→ SC.G) (i : Fin (m+1)) : Fin (SC.n + 1 )
    := ⟨ coord_change_count SC (I 0) (I i), by {
      refine Nat.lt_succ_of_le ?_
      exact card_finset_fin_le {i_1 | I 0 i_1 ≠ I i i_1}
    } ⟩

lemma ccc_fun_strict_mono {m} I (hs : simplex SC m I) :
    StrictMono (ccc_fun SC I) := by {
  intro i1 i2 h1
  unfold ccc_fun
  simp only [Fin.mk_lt_mk]
  have h3 : 0 ≤ i1 ∧ i1 ≤ i2 := ⟨ (Fin.zero_le i1), (Fin.le_of_lt h1) ⟩
  rw [ccc_add SC I hs 0 i1 i2 h3]
  simp only [lt_add_iff_pos_right, gt_iff_lt]
  apply ccc_pos SC I hs _ _ $ Fin.ne_of_lt h1
}

lemma ccc_fun_is_insert_index I (hs : simplex SC n1 I) :
    ∃ j, ccc_fun SC I = @insert_index SC n1 hn1 j := by {
  apply is_insert_index_of_strict_mono
  apply ccc_fun_strict_mono SC I hs
}



lemma ccc_fun_case_D_iff {m} I (hs : simplex SC m I) :
    case_D SC I ↔ ccc_fun SC I (Fin.last m) = Fin.last SC.n := by {
  have h1 : (ccc_fun SC I (Fin.last m) = Fin.last SC.n) ↔ ∀ k, I 0 k ≠ I (Fin.last m) k  := by {
    rw [Fin.ext_iff]
    change ({i : Fin SC.n | I 0 i ≠ I (Fin.last m) i} : Finset _).card = SC.n ↔ _
    simpa only [Fintype.card_fin, Finset.eq_univ_iff_forall, Finset.mem_filter,
      Finset.mem_univ, true_and] using
      (Finset.card_eq_iff_eq_univ (s := ({i : Fin SC.n | I 0 i ≠ I (Fin.last m) i} : Finset _)))
  }
  apply Iff.trans _ h1.symm
  unfold case_D
  apply Iff.intro
  {
    intro h2 k1
    obtain ⟨i2, hi2⟩ := h2 k1 (I 0 k1)
    intro h3
    apply hi2
    apply le_antisymm
    {
      rw [h3]
      apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last i2)
    }
    exact monotone_1_of_simplex SC I hs _ _ (Fin.zero_le i2) k1
  }
  {
    contrapose!
    intro h2
    obtain ⟨k2, ⟨q, hq⟩ ⟩ := h2
    use k2
    rw [hq, hq]
  }
}

lemma last_eq_first_add_one J (hs : simplex SC SC.n J)
    : ∀ k, (J (Fin.last SC.n) k).1 = (J 0 k).1 + 1 := by {
  have h3 : ∀ j3, ccc_fun SC J j3 = j3 := by {
    apply is_id_of_strict_mono
    apply ccc_fun_strict_mono SC J hs
  }
  have h2 := (ccc_fun_case_D_iff SC J hs).mpr (h3 _)
  unfold case_D at h2
  intro k
  apply le_antisymm  (last_of_simplex SC J hs k)
  apply Nat.add_one_le_of_lt
  obtain ⟨j1, hj1⟩ := h2 k (J 0 k)
  have h4 := monotone_1_of_simplex SC J hs _ _ (Fin.le_last j1) k
  apply lt_of_lt_of_le _ h4
  apply lt_of_le_of_ne (monotone_1_of_simplex SC J hs _ _ (Fin.zero_le j1) k) hj1.symm
}

lemma delete_vertex_ccc_fun_match J (hs : simplex SC SC.n J) j1 j2
    ( h1 : ccc_fun SC (@delete_vertex SC n1 hn1 j1 J) = @insert_index SC n1 hn1 j2)
    : (j1 = 0 → j2 = Fin.last SC.n) ∧ (j1 ≠ 0 → j1 = j2) := by {
  let I := @delete_vertex SC n1 hn1 j1 J
  have hsI : simplex SC n1 I := by {
    suffices h2 : is_face SC I J by { exact h2.1}
    rw [@child_simplex_char SC n1 hn1 I J hs]
    use j1
  }
  have scnpos : 0 < SC.n := by omega
  by_cases h4 : j1 = 0
  {
    simp only [h4, forall_const, ne_eq, not_true_eq_false, IsEmpty.forall_iff, and_true]
    have h5 : I 0 = J 1 := by {
      unfold I delete_vertex insert_index
      congr!
      rw [h4]
      simp only [Fin.val_zero, lt_self_iff_false, ↓reduceIte, zero_add]
      simp only [Fin.val_one']
      refine Eq.symm (Nat.mod_eq_of_lt ?_)
      exact Nat.lt_add_of_pos_left scnpos
    }
    symm
    by_contra h6
    obtain ⟨i1, hi1⟩ := @almost_surjective_of_insert_index SC n1 hn1 _ _ h6
    have h8 : (ccc_fun SC I i1).1 = SC.n := by {
      unfold I
      rw [h1, ← hi1]
      simp only [Fin.val_last]
    }
    unfold ccc_fun at h8
    simp only [h5] at h8
    unfold I delete_vertex at h8
    let c2 := coord_change_count SC (J 0) (J 1)
    have c2pos : 0 < c2 := by {
      apply ccc_pos _ _ hs
      simp only [ne_eq, Fin.zero_eq_one_iff, Nat.add_eq_right]
      omega
    }
    let j3 := @insert_index SC n1 hn1 j1 i1
    have h9 : (ccc_fun SC J j3).1 = c2 + SC.n:= by {
      simp only [← h8]
      apply ccc_add SC J hs
      simp only [Fin.zero_le, true_and]
      suffices h9 : j3 ≠ j1 by {
        rw [h4] at h9
        exact Fin.one_le_of_ne_zero h9
      }
      apply insert_index_ne
    }
    have h10 : c2 + SC.n ≤ SC.n := by {
      rw [←h9]
      exact Fin.is_le (ccc_fun SC J j3)
    }
    simp only [add_le_iff_nonpos_left, nonpos_iff_eq_zero] at h10
    omega
  }
  simp only [h4, IsEmpty.forall_iff, ne_eq, not_false_eq_true, forall_const, true_and]
  have h2 : I 0 = J 0 := by {
    unfold I delete_vertex
    congr!
    unfold insert_index
    simpa only [Fin.val_zero, Fin.val_pos_iff, zero_add, Fin.mk_eq_zero,
        ite_eq_left_iff, not_lt,Fin.le_zero_iff, one_ne_zero, imp_false]
  }
  have h3 : ∀ j3, ccc_fun SC J j3 = j3 := by {
    apply is_id_of_strict_mono
    apply ccc_fun_strict_mono SC J hs
  }
  symm
  by_contra h5
  obtain ⟨i1, hi1⟩ := @almost_surjective_of_insert_index SC n1 hn1 _ _ h5
  have h6 : ccc_fun SC I i1 = ccc_fun SC J j2 := by {
    unfold ccc_fun
    simp [h2]
    congr
    rw [hi1]
    rfl
  }
  rw [h1, h3 j2] at h6
  contrapose h6
  apply insert_index_ne
}

lemma case_D_iff_not_end_1 I (hs : simplex SC n1 I) j
    (h1 : ccc_fun SC I = @insert_index SC n1 hn1 j) :
    case_D SC I ↔ j ≠ 0 ∧ j ≠ Fin.last SC.n := by {
  rw [ccc_fun_case_D_iff SC I hs, h1]
  have h2 : j ≠ 0 := by {
    intro h3
    apply @insert_index_ne SC n1 hn1 j 0
    rw [←h1, h3]
    unfold ccc_fun coord_change_count
    simp only [ne_eq, not_true_eq_false, Finset.filter_false, Finset.card_empty, Fin.zero_eta]
  }
  simp only [ne_eq, h2, not_false_eq_true, true_and]
  apply Iff.intro
  {
    intro h3 h4
    apply @insert_index_ne SC n1 hn1 j (Fin.last n1)
    rw [h3,h4]
  }
  {
    intro h3
    have h32 : Fin.last SC.n ≠ j := fun a ↦ h3 (Eq.symm a)
    obtain ⟨i2, hi2⟩  := @almost_surjective_of_insert_index SC n1 hn1 j (Fin.last SC.n) h32
    apply le_antisymm
    exact Fin.le_last (insert_index SC j (Fin.last n1))
    rw [hi2]
    have h4 := @insert_index_strict_mono SC n1 hn1 j
    rw [h4.le_iff_le]
    exact Fin.le_last i2
  }
}

lemma case_D_iff_not_end_2 J (hs : simplex SC SC.n J) j :
    case_D SC (@delete_vertex SC n1 hn1 j J) ↔ j ≠ 0 ∧ j ≠ Fin.last SC.n := by {
  let I := @delete_vertex SC n1 hn1 j J
  have hsI : simplex SC n1 I := by {
    suffices h2 : is_face SC I J by exact h2.1
    rw [@child_simplex_char SC n1 hn1 I J hs]
    use j
  }
  obtain ⟨j2, hj2⟩ := @ccc_fun_is_insert_index SC n1 hn1 I hsI
  have h1 := @delete_vertex_ccc_fun_match SC n1 hn1 J hs j j2 hj2
  by_cases h2 : j = 0
  {
    rw [ccc_fun_case_D_iff SC I hsI]
    simp only [h2, ne_eq, not_true_eq_false, Fin.zero_eq_last_iff, false_and, iff_false]
    rw [←h1.1 h2, hj2]
    apply insert_index_ne
  }
  rw [@case_D_iff_not_end_1 SC n1 hn1 I hsI]
  rw [hj2, ← h1.2 h2]
}

lemma same_delete_index_eq_iff J1 J2 j
    (h1 : @delete_vertex SC n1 hn1 j J1 = @delete_vertex SC n1 hn1 j J2)
    : J1 = J2 ↔ J1 j = J2 j := by {
  apply Iff.intro (fun a ↦ congrFun a j)
  intro h2
  ext j2
  by_cases h3 : j2 = j
  rw [h3,h2]
  obtain ⟨i1, hi1⟩ := @almost_surjective_of_insert_index SC n1 hn1 j j2 h3
  rw [hi1]
  exact congrFun h1 i1
}


lemma case_D_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h1 : case_D SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 2 := by {
  obtain ⟨ j1, hj1 ⟩ := @ccc_fun_is_insert_index SC n1 hn1 I hs
  have h2 : j1 ≠ 0 ∧ j1 ≠ Fin.last SC.n := by {
    rw [←case_D_iff_not_end_1 SC I hs j1 hj1]
    exact h1
  }
  have h3 : ∃ (i1: Fin (n1 + 1)), i1.1 + 1 = j1.1 := by {
    obtain ⟨a, ha⟩ := Fin.exists_succ_eq_of_ne_zero h2.1
    rw [← ha]
    simp only [Fin.val_succ, Nat.add_right_cancel_iff]
    use ⟨ a.1, by {rw [hn1]; exact a.2}⟩
  }
  obtain ⟨ i1, hi1⟩ := h3
  have h32 : i1 ≤ i1 + 1 := by {
    refine Fin.le_of_lt ?_
    refine Fin.lt_add_one_iff.mpr ?_
    show i1.1 < n1
    have h3 := Fin.val_lt_last h2.2
    omega
  }
  have h11 := @surround_index SC n1 hn1 j1 i1 hi1 h2.2
  have h12 : @insert_index SC n1 hn1 j1 i1 ≤ j1 ∧ j1 ≤ @insert_index SC n1 hn1 j1 (i1+1) := by {
    rw [Fin.le_def, Fin.le_def, ←h11.2]
    apply And.intro
    rw [←h11.1]
    apply Nat.le_add_right
    apply Nat.le_add_right
  }
  have h3 : coord_change_count SC (I i1) (I (i1+1)) = 2 := by {
    have h3 : (@insert_index SC n1 hn1 j1 i1).1 + 2
        = (@insert_index SC n1 hn1 j1 (i1 +1)).1 := by {
      rw [← h11.2, ←h11.1]
    }
    have h4 : (ccc_fun SC I (i1+1)).1 = (ccc_fun SC I i1).1
        + coord_change_count SC (I i1) (I (i1 + 1)) := by {
      apply ccc_add SC I hs
      simp only [Fin.zero_le, true_and, h32]
    }
    rw [← hj1, h4 ] at h3
    simp only [Nat.add_left_cancel_iff] at h3
    exact h3.symm
  }
  have h4 : ∃ k1, ∃ k2, k1 ≠ k2 ∧ {k | I i1 k ≠ I (i1 +1) k} = {k1, k2} := by {
    unfold coord_change_count at h3
    rw [Finset.card_eq_two] at h3
    convert h3
    simp only [ne_eq]
    rw [←Finset.coe_eq_pair]
    simp only [Finset.coe_filter, Finset.mem_univ, true_and]
  }
  obtain ⟨k1, ⟨k2, h4⟩ ⟩ := h4
  have hk1 : I i1 k1 ≠ I (i1+1) k1 := by {
    have h5 := Set.mem_insert k1 {k2}
    rwa [←h4.2] at h5
  }
  have hk2 : I i1 k2 ≠ I (i1+1) k2 := by {
    have h5 : k2 ∈ ({k1, k2} : Set _) := Set.mem_insert_of_mem k1 rfl
    rwa [←h4.2] at h5
  }
  have h5 k3 : I i1 k3 ≠ I (i1+1) k3 → ∃ J3,
      I = @delete_vertex SC n1 hn1 j1 J3 ∧ is_face SC I J3 ∧ J3 j1 k3 ≠ I i1 k3 := by {
    intro h21
    let ins : SC.G := fun k ↦ if k = k3 then I (i1 + 1) k else I i1 k
    obtain ⟨J3, hJ3⟩ := @insert_vertex SC n1 hn1 I ins j1
    have h6 : ∀ k, I i1 k ≤ ins k ∧ ins k ≤ I (i1+1) k := by {
      intro k
      unfold ins
      have h13 : I i1 k3 ≤ I (i1+1) k3 := monotone_1_of_simplex SC I hs _ _ h32 k3
      by_cases h12 : k = k3
      simp only [h12, ↓reduceIte, le_refl, and_true, ge_iff_le]
      exact monotone_1_of_simplex SC I hs _ _ h32 k3
      simp only [h12, ↓reduceIte, le_refl, true_and, ge_iff_le]
      exact monotone_1_of_simplex SC I hs _ _ h32 k
    }
    have h22 : J3 j1 k3 ≠ I i1 k3 := by {
      rw [hJ3.2]
      unfold ins
      simp only [↓reduceIte, ne_eq]
      exact h21.symm
    }
    have h23 : ∃ k4, k3 ≠ k4 ∧ I i1 k4 ≠ I (i1+1) k4 := by {
      by_cases h24 : k3 = k1
      use k2
      rw [h24]
      apply And.intro h4.1 hk2
      use k1
    }
    have h7 : ins ∉ Set.range I := by {
      intro h9
      obtain ⟨i2,hi2⟩ := h9
      rw [forall_and, ← hi2] at h6
      rw [← monotone_2_of_simplex _ _ hs,← monotone_2_of_simplex _ _ hs] at h6
      have h13 : i2 = i1 ∨ i2 = i1 + 1 := by {
        refine (WCovBy.le_and_le_iff ?_).mp h6
        apply And.intro h32
        intro i3 h33
        simp only [not_lt]
        exact Fin.add_one_le_of_lt h33
      }
      cases' h13 with h13 h13
      apply h22
      rw [hJ3.2, ←hi2, h13]
      obtain ⟨k4, hk4⟩ := h23
      apply hk4.2
      rw [←h13, hi2]
      unfold ins
      simp only [right_eq_ite_iff]
      intro h33
      exact False.elim $ hk4.1 h33.symm
    }
    use J3
    apply And.intro hJ3.1 (And.intro _ h22)
    apply @parent_simplex_case_D SC n1 hn1 I hs J3 _ _ hi1 hJ3.1
    rwa [hJ3.2]
    rwa [hJ3.2]
  }
  obtain ⟨J1, hJ1⟩ := h5 k1 hk1
  obtain ⟨J2, hJ2⟩ := h5 k2 hk2
  have h6 J3 : I = @delete_vertex SC n1 hn1 j1 J3 → is_face SC I J3
    → ∀ k, I i1 k ≤ J3 j1 k ∧ J3 j1 k ≤ I (i1+1) k := by {
    intro h14 h13 k3
    rw [h14]
    apply And.intro
    apply monotone_1_of_simplex SC J3 h13.2.1 _ _ h12.1
    apply monotone_1_of_simplex SC J3 h13.2.1 _ _ h12.2
  }
  have h7 J3 k3 : I = @delete_vertex SC n1 hn1 j1 J3 ∧ is_face SC I J3 ∧ J3 j1 k3 ≠ I i1 k3
      → J3 j1 k3 = I (i1+1) k3 ∧ ∀ k4, k3 ≠ k4 → J3 j1 k4 = I i1 k4 := by {
    intro h9
    have h6 := h6 J3 h9.1 h9.2.1
    have h31 := h3
    rw [h9.1] at h31
    have h21 := ccc_add SC J3 h9.2.1.2.1 _ _ _ h12
    unfold delete_vertex at h31
    rw [h31] at h21
    have h22 c1 c2 : 2 = c1 + c2 → 0 < c2 → c1 ≤ 1 := by omega
    have h23 : coord_change_count SC (I i1) (J3 j1) ≤ 1 := by {
      rw [h9.1]
      apply h22 _ _ h21
      apply ccc_pos SC
      exact h9.2.1.2.1
      symm
      apply insert_index_ne
    }
    apply And.intro
    {
      apply le_antisymm (h6 k3).2
      rw [Fin.le_def]
      have h24 := le_add_one_of_simplex SC I hs (i1+1) i1 k3
      apply le_trans h24
      apply Fin.val_add_one_le_of_lt (lt_of_le_of_ne (h6 k3).1 h9.2.2.symm)
    }
    intro k4 hk4
    contrapose! h23
    refine Finset.one_lt_card_iff.mpr ?_
    use k3, k4
    simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and]
    exact And.intro h9.2.2.symm ( And.intro h23.symm hk4)
  }
  refine Finset.card_eq_two.mpr ?_
  use J1, J2
  apply And.intro
  {
    have h71 := (h7 J1 k1 hJ1).2 k2 h4.1
    intro h9
    apply hJ2.2.2
    rw [←h9, h71]
  }
  apply subset_antisymm
  {
    intro J3
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    intro hJ3
    have h14 := (@child_simplex_char SC n1 hn1 I J3 hJ3.2.1).mp hJ3
    obtain ⟨j2, hj2⟩ := h14
    rw [hj2] at hj1
    have h13 := @delete_vertex_ccc_fun_match SC n1 hn1 J3 hJ3.2.1 j2 j1 hj1
    have h15 := @case_D_iff_not_end_2 SC n1 hn1 J3 hJ3.2.1 j2
    rw [←hj2] at h15
    have h16 : j2 = j1 := h13.2 (h15.mp h1).1
    rw [h16] at hj2
    rw [same_delete_index_eq_iff SC J3 J1 j1, same_delete_index_eq_iff SC J3 J2 j1]
    have h71 := h7 J1 k1 hJ1
    have h72 := h7 J2 k2 hJ2
    have h18 : ∃ k5, J3 j1 k5 ≠ I i1 k5 := by {
      suffices h19 : J3 j1 ≠ I i1 by exact Function.ne_iff.mp h19
      intro h19
      apply @insert_index_ne SC n1 hn1 j1 i1
      apply hJ3.2.1.1
      rw [h19, hj2]
      rfl
    }
    obtain ⟨k5, hk5⟩ := h18
    have h73 := h7 J3 k5 ⟨hj2, ⟨ hJ3, hk5⟩ ⟩
    clear h15 h13
    have h19 : k5 = k1 ∨ k5 = k2 := by {
      have h21 : I i1 k5 ≠ I (i1+1) k5 := by {
        rw [←h73.1]
        exact hk5.symm
      }
      exact h4.2.subset h21
    }
    have h20 (J4 : _ → SC.G) : (J4 j1 k5 = I (i1+1) k5 ∧ ∀ k4, k5 ≠ k4 → J4 j1 k4 = I i1 k4)
        → J3 j1 = J4 j1:= by {
      intro h21
      apply funext
      intro k6
      by_cases h22 : k5 = k6
      rw [←h22,h21.1,h73.1]
      rw [h21.2 k6 h22, h73.2 k6 h22]
    }
    cases h19
    left
    rename_i h21
    apply h20
    rwa [h21]
    right
    rename_i h21
    apply h20
    rwa [h21]
    rw [←hJ2.1, ←hj2]
    any_goals exact hn1
    rw [←hJ1.1, ←hj2]
  }
  {
    refine Finset.insert_subset ?_ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hJ1.2.1
    simp only [Finset.singleton_subset_iff, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hJ2.2.1
  }
}


lemma unique_const_ABC {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) k1 q1
    (h1 : ∀ i, I i k1 = q1): ∀ k2, k1 ≠ k2 → I 0 k2 ≠ I (Fin.last n1) k2 := by {
  intro k2 h3 h2
  let s : Finset (Fin SC.n) := {i | I 0 i ≠ I (Fin.last n1) i}
  have h4 : n1 ≤ s.card := by {
    obtain ⟨j, hj⟩ := @ccc_fun_is_insert_index SC n1 hn1 I hs
    show n1 ≤ (ccc_fun SC I (Fin.last n1)).1
    rw [hj]
    unfold insert_index
    simp only [Fin.val_last]
    by_cases h11 : n1 < j.1
    simp only [h11, ↓reduceIte, le_refl]
    simp only [h11, ↓reduceIte, le_add_iff_nonneg_right, zero_le]
  }
  have h6 : 2 ≤ sᶜ.card := by {
    show 1 < sᶜ.card
    rw [Finset.one_lt_card]
    use k2
    unfold s
    simp only [ne_eq, Finset.compl_filter, Decidable.not_not, Finset.mem_filter,
        Finset.mem_univ,h2, and_self, true_and]
    use k1
    apply And.intro _ h3.symm
    rw [h1,h1]
  }
  have h7 := add_le_add h4 h6
  simp only [Finset.card_add_card_compl, Fintype.card_fin] at h7
  rw [←hn1,add_le_add_iff_left] at h7
  simp only [Nat.not_ofNat_le_one] at h7
}


lemma case_AC_ex_unique I (hs : simplex SC n1 I) k1 q
    (hABC : ∀ i, I i k1 = q) (hAC : q ≠ Fin.last SC.p)
    : ∃! J, I = @delete_vertex SC n1 hn1 (Fin.last SC.n) J ∧ is_face SC I J := by {
  have h1 k2 : I 0 k2 ≠ Fin.last SC.p := by {
    intro h11
    have h12 : k1 ≠ k2 := by {
      intro h13
      apply hAC
      rw [←hABC 0,h13,h11]
    }
    apply @unique_const_ABC SC n1 hn1 I hs k1 q hABC k2 h12
    apply le_antisymm
    apply monotone_1_of_simplex SC I hs
    exact Fin.zero_le (Fin.last n1)
    rw [h11]
    exact Fin.le_last (I (Fin.last n1) k2)
  }
  let ins2 : SC.G := fun k ↦ (I 0 k) + 1
  have h2 k : (ins2 k).1 = (I 0 k).1 + 1 := by {
    apply Fin.val_add_one_of_lt
    rw [Fin.lt_last_iff_ne_last]
    exact h1 k
  }
  obtain ⟨J1, hJ1⟩ := @insert_vertex SC n1 hn1 I ins2 (Fin.last SC.n)
  have h3 : J1 (Fin.last SC.n) ≠ I (Fin.last n1) := by {
    intro h12
    have h11 : I 0 k1 = I 0 k1 + 1 := by {
      show I 0 k1 = ins2 k1
      rw [←hJ1.2, h12,hABC,hABC]
    }
    simp only [left_eq_add, Fin.one_eq_zero_iff, Nat.add_eq_right] at h11
    apply @p_ne_zero_of_cube SC n1 hn1
    simp only [Fin.last_eq_zero_iff, h11]
  }
  have h4 : is_face SC I J1 := by {
    apply parent_simplex_case_AC SC I hs J1 (Fin.last SC.n) rfl hJ1.1 h3
    intro k2
    rw [hJ1.2]
    apply And.intro
    {
      rw [Fin.le_def, h2 k2]
      apply le_add_one_of_simplex SC I hs
    }
    rw [h2 k2]
  }
  use J1
  simp only
  apply And.intro (And.intro hJ1.1 h4)
  intro J2 hJ2
  rw [@same_delete_index_eq_iff SC n1 hn1 _ _ _ (hJ2.1.symm.trans hJ1.1)]
  rw [hJ1.2]
  apply funext
  intro k1
  ext
  have h5 := last_eq_first_add_one SC J2 hJ2.2.2.1 k1
  rw [h5, h2 k1]
  suffices h6 : I 0 = J2 0 by {rw [h6]}
  rw [hJ2.1]
  unfold delete_vertex insert_index
  congr!
  simp only [Fin.val_zero, Fin.val_last, zero_add, ite_eq_left_iff,
    not_lt, nonpos_iff_eq_zero,one_ne_zero, imp_false]
  rw [←hn1]
  omega
}

lemma case_B_not_last I (h1 : case_B SC I) J
    (h2 : I = @delete_vertex SC n1 hn1 (Fin.last SC.n) J ∧ is_face SC I J) : False := by {
  have h3 := last_eq_first_add_one SC J h2.2.2.1
  obtain ⟨k1, hk1⟩ := h1
  have h4 : I 0 = J 0 := by {
    rw [h2.1]
    unfold delete_vertex insert_index
    congr!
    simp only [Fin.val_zero, Fin.val_last, zero_add, ite_eq_left_iff,
        not_lt, nonpos_iff_eq_zero,one_ne_zero, imp_false]
    rw [←hn1]
    omega
  }
  have h5 := (J (Fin.last SC.n) k1).is_le
  rw [h3 k1,←h4,hk1 0] at h5
  contrapose! h5
  exact lt_add_one SC.p
}


lemma case_BC_ex_unique I (hs : simplex SC n1 I) k1 q
    (hABC : ∀ i, I i k1 = q) (hBC : q ≠ 0)
    : ∃! J, I = @delete_vertex SC n1 hn1 0 J ∧ is_face SC I J := by {
  have h1 k2 : I (Fin.last n1) k2 ≠ 0 := by {
    intro h11
    have h12 : k1 ≠ k2 := by {
      intro h13
      apply hBC
      rw [←hABC (Fin.last n1),h13,h11]
    }
    apply @unique_const_ABC SC n1 hn1 I hs k1 q hABC k2 h12
    apply le_antisymm
    apply monotone_1_of_simplex SC I hs
    exact Fin.zero_le (Fin.last n1)
    rw [h11]
    exact Fin.zero_le (I 0 k2)
  }
  let ins2 : SC.G := fun k ↦ (I (Fin.last n1) k) - 1
  have h22 k := Fin.val_sub_one_of_ne_zero (h1 k)
  have h21 k : (ins2 k).1 + 1 = (I (Fin.last n1) k).1  := by {
    rw [h22]
    apply Nat.sub_one_add_one ( Fin.val_ne_zero_iff.mpr (h1 k))
  }
  obtain ⟨J1, hJ1⟩ := @insert_vertex SC n1 hn1 I ins2 0
  have h3 : J1 0 ≠ I 0 := by {
    intro h12
    have h11 : (ins2 k1).1 + 1 = ins2 k1 := by {
      rw [h21 k1, hABC, ←hJ1.2,h12,hABC]
    }
    simp only [Nat.add_eq_left, one_ne_zero] at h11
  }
  have h4 : is_face SC I J1 := by {
    apply parent_simplex_case_BC SC I hs J1 hJ1.1 h3
    intro k2
    rw [hJ1.2]
    apply And.intro
    rw [Fin.le_def, ←add_le_add_iff_right 1, h21 k2]
    exact le_add_one_of_simplex SC I hs (Fin.last n1) 0 k2
    rw [h21 k2]
  }
  use J1
  simp only
  apply And.intro (And.intro hJ1.1 h4)
  intro J2 hJ2
  rw [@same_delete_index_eq_iff SC n1 hn1 _ _ _ (hJ2.1.symm.trans hJ1.1), hJ1.2]
  apply funext
  intro k1
  ext
  have h5 := last_eq_first_add_one SC J2 hJ2.2.2.1 k1
  have h6 : I (Fin.last n1) = J2 (Fin.last SC.n) := by {
    rw [hJ2.1]
    unfold delete_vertex insert_index
    simp only [Fin.val_last, Fin.val_zero, not_lt_zero, ↓reduceIte]
    congr!
  }
  rw [←h6, ←h21 k1] at h5
  omega
}

lemma zero_ne_last {hn1 : n1 + 1 = SC.n} : 0 ≠ Fin.last SC.n := by {
  simp only [ne_eq, Fin.zero_eq_last_iff]
  rw [←hn1]
  omega
}

lemma case_A_not_zero I (h1 : case_A SC I) J
    (h2 : I = @delete_vertex SC n1 hn1 0 J ∧ is_face SC I J) : False := by {
  have h3 := last_eq_first_add_one SC J h2.2.2.1
  obtain ⟨k1, hk1⟩ := h1
  have h4 : I (Fin.last n1) = J (Fin.last SC.n) := by {
    rw [h2.1]
    unfold delete_vertex insert_index
    simp only [Fin.val_last, Fin.val_zero, not_lt_zero, ↓reduceIte]
    congr!
  }
  apply Nat.zero_ne_add_one (J 0 k1).1
  rw [←h3 k1,← h4,hk1]
  rfl
}



lemma case_ABC_count_disj {hn1 : n1 + 1 = SC.n} I k1 q
    (hABC : ∀ i, I i k1 = q) : Finset.card { J | is_face SC I J}
    = Finset.card {J | I = @delete_vertex SC n1 hn1 0 J ∧ is_face SC I J}
    + Finset.card {J | I = @delete_vertex SC n1 hn1 (Fin.last SC.n) J ∧ is_face SC I J} := by {
  have hnd : ¬ case_D SC I := by {
    contrapose! hABC
    exact hABC k1 q
  }
  rw [←Finset.card_union_of_disjoint]
  congr
  ext J
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  apply Iff.intro
  {
    intro h1
    simp only [h1, and_true]
    rw [child_simplex_char] at h1
    obtain ⟨j1, hj1⟩ := h1
    have h2 := @case_D_iff_not_end_2 SC n1 hn1 J h1.2.1 j1
    rw [hj1,h2] at hnd
    have h3 := Decidable.or_iff_not_not_and_not.mpr hnd
    cases' h3 with h3 h3
    rw [hj1,h3]
    exact Or.inl rfl
    rw [hj1,h3]
    exact Or.inr rfl
    · exact hn1
    · exact h1.2.1
  }
  {
    intro h1
    rw [←or_and_right] at h1
    exact h1.2
  }
  apply Finset.disjoint_filter.mpr
  intro J h1 h2 h3
  apply @zero_ne_last SC n1 hn1
  apply @delete_vertex_inj SC n1 hn1 J h2.2.2.1
  rw [←h2.1,←h3.1]
}


lemma case_C_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h1 : case_C SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 2 := by {
  obtain ⟨k1,q, h1⟩  := h1
  have h2 := @case_AC_ex_unique SC n1 hn1 I hs k1 q h1.2 h1.1.2
  have h3 := @case_BC_ex_unique SC n1 hn1 I hs k1 q h1.2 h1.1.1
  rw [Fintype.existsUnique_iff_card_one] at h2 h3
  rw [case_ABC_count_disj SC I k1 q h1.2,h2,h3]
  exact hn1
}

lemma case_B_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h2 : case_B SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 1 := by {
  obtain ⟨k1, h1⟩  := id h2
  have h4 : Fin.last SC.p ≠ 0 := @p_ne_zero_of_cube SC n1 hn1
  have h3 := @case_BC_ex_unique SC n1 hn1 I hs k1 _ h1 h4
  rw [Fintype.existsUnique_iff_card_one] at h3
  rw [case_ABC_count_disj SC I k1 (Fin.last SC.p) h1, h3]
  simp only [Nat.add_eq_left]
  apply Finset.card_filter_eq_zero_iff.mpr
  intro J h5
  apply case_B_not_last SC I h2
  exact hn1
}

lemma case_A_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h2 : case_A SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 1 := by {
  obtain ⟨k1, h1⟩  := id h2
  have h4 : Fin.last SC.p ≠ 0 := @p_ne_zero_of_cube SC n1 hn1
  have h3 := @case_AC_ex_unique SC n1 hn1 I hs k1 _ h1 h4.symm
  rw [Fintype.existsUnique_iff_card_one] at h3
  rw [case_ABC_count_disj SC I k1 0 h1, h3]
  simp only [Nat.add_eq_right]
  apply Finset.card_filter_eq_zero_iff.mpr
  intro J h5
  apply case_A_not_zero SC I h2
  exact hn1
}

end cases_ABCD

-- used in other file
lemma boundary_is_A_or_B {hn1 : n1 + 1 = SC.n} I (hbf : @is_boundary_face SC n1 I)
    : case_A SC I ∨ case_B SC I := by {
  have hs : simplex SC n1 I := by {
    obtain ⟨J,hJ⟩ := hbf
    exact hJ.1.1
  }
  unfold is_boundary_face at hbf
  rw [Fintype.existsUnique_iff_card_one] at hbf
  have h1 := one_of_ABCD SC I
  rw [←or_assoc] at h1
  cases' h1 with h1 h1
  assumption
  cases' h1 with h1 h1
  rw [@case_C_parent_count SC n1 hn1 I hs h1] at hbf
  simp only [OfNat.ofNat_ne_one] at hbf
  rw [@case_D_parent_count SC n1 hn1 I hs h1] at hbf
  simp only [OfNat.ofNat_ne_one] at hbf
}

-- used in other file
lemma case_B_boundary {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I)
    (h1 : case_B SC I) : is_boundary_face SC I :=
  (Fintype.existsUnique_iff_card_one _).mpr (@case_B_parent_count SC n1 hn1 I hs h1)


-- used in other file
lemma parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) :
    Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} ∈ {c | c = 1 ∨ c = 2} := by {
  simp only [Set.mem_setOf_eq]
  have h1 := one_of_ABCD SC I
  rw [←or_assoc] at h1
  cases' h1 with h1 h1
  left
  cases' h1 with h2 h2
  exact @case_A_parent_count SC n1 hn1 I hs h2
  exact @case_B_parent_count SC n1 hn1 I hs h2
  right
  cases' h1 with h2 h2
  exact @case_C_parent_count SC n1 hn1 I hs h2
  exact @case_D_parent_count SC n1 hn1 I hs h2
}
end

-- Source module OptimalG.External.FixedPointTheorems.cubical_sperner
section
set_option autoImplicit true
open Classical



section completeness

lemma complete_simplex_iff {SC} m I(hs : simplex SC m I) :
    complete_simplex SC m I ↔ ∀ c, (c ≤ m) → ∃ i, SC.RL (I i) = c := by {
  apply Iff.intro
  {
    intro h1 c hc
    rwa [← Set.mem_range, h1.2, Set.mem_setOf_eq]
  }
  {
    intro c1
    apply And.intro hs
    refine Set.toFinset_inj.mp ?_
    refine (Finset.eq_iff_card_ge_of_superset ?_).mp ?_
    {
      simp only [Set.toFinset_range, Set.toFinset_subset, Finset.coe_image, Finset.coe_univ,
        Set.image_univ]
      intro c hc
      simp only [Set.mem_range, c1 c hc]
    }
    let f1 := fun (j : ℕ ) ↦ SC.RL (I (Fin.ofNat _ j))
    apply Finset.card_le_card_of_surjOn f1
    intro j h1
    simp only [Set.toFinset_range, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_range] at h1
    obtain ⟨ i, hi⟩ := h1
    use i
    simp only [Set.coe_toFinset, Set.mem_setOf_eq]
    apply And.intro (Fin.is_le i)
    unfold f1
    rw [← hi]
    simp only [Fin.ofNat_eq_cast, Fin.cast_val_eq_self]
  }
}


lemma rl_inj_of_complete {SC} m I (hcs : complete_simplex SC m I):
    ∀ i1 i2, SC.RL (I i1) = SC.RL (I i2) → i1 = i2 := by {
  let f1 : Fin (m+1) → Fin (m+1) := fun j ↦ Fin.ofNat _ (SC.RL (I j))
  suffices h1 : Function.Injective f1 by {
    intro i1 i2 h2
    apply h1
    unfold f1
    rw [h2]
  }
  have h2 := hcs.2
  apply Function.Surjective.injective_of_finite
  rfl
  rw [complete_simplex_iff _ _ hcs.1] at hcs
  intro c
  obtain ⟨a, ha⟩ := hcs c (Fin.is_le c)
  use a
  unfold f1
  rw [ha]
  exact Fin.cast_val_eq_self c
}


lemma char_complete_face {SC n1 hn1} I J (hs : simplex SC SC.n J) :
    complete_simplex SC n1 I ∧ is_face SC I J
    ↔ ∃ i, I = @delete_vertex SC n1 hn1 i J
    ∧ ∀ (c:ℕ ), c ≤ n1 → ∃ i2, i2 ≠ i ∧ SC.RL (J i2) = c := by {
  apply Iff.intro
  {
    rw [child_simplex_char]
    intro h1
    obtain ⟨i, hi1 ⟩ := h1.2
    use i
    apply And.intro hi1
    intro c hc
    have h2 := (complete_simplex_iff n1 I h1.1.1).mp h1.1 c hc
    obtain ⟨j, hj⟩ := h2
    rw [← hj, hi1]
    unfold delete_vertex
    use @insert_index SC n1 hn1 i j
    apply And.intro _ rfl
    apply insert_index_ne
    exact hn1
    exact hs
  }
  {
    intro h1
    obtain ⟨i, hi1 ⟩ := h1
    have hface : is_face SC I J := by {
      rw [child_simplex_char]
      use i
      exact hi1.1
      exact hs
    }
    apply And.intro _ hface
    rw [complete_simplex_iff n1 I hface.1]
    intro c hc
    obtain ⟨i2, hi2⟩ := hi1.2 c hc
    have h3 := @almost_surjective_of_insert_index SC n1 hn1 i i2 hi2.1
    obtain ⟨j, hj⟩ := h3
    use j
    rw [hi1.1, ← hi2.2, hj]
    rfl
  }
}


lemma complete_child_uniq {SC n1} {hn1 : n1 + 1 = SC.n} J (hcs : complete_simplex SC SC.n J) :
    ∃! (I : Fin (n1+1) → SC.G), complete_simplex SC n1 I ∧ is_face SC I J := by {
  have h4 : ∃ i, SC.RL (J i) = SC.n := by {
    rw [← Set.mem_range, hcs.2]
    simp only [Set.mem_setOf_eq, le_refl]
  }
  obtain ⟨ i, hi⟩ := h4
  let I := @delete_vertex SC n1 hn1 i J
  have hs2 : simplex SC n1 I := by {
    apply delete_vertex_simplex
    exact hcs.1
  }
  use I
  have h1 : complete_simplex SC n1 I ∧ is_face SC I J := by
  {
    rw [@char_complete_face SC n1 hn1 _ _ hcs.1]
    use i
    apply And.intro rfl
    rw [complete_simplex_iff] at hcs
    {
      intro c hc
      have h3 : c ≤ SC.n := by omega
      obtain ⟨i2, hi2 ⟩ := hcs c h3
      use i2
      apply And.intro _ hi2
      intro h4
      rw [h4, hi, ← hn1] at hi2
      rw [← hi2] at hc
      revert hc
      simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, imp_self]
    }
    {
      exact hcs.1
    }
  }
  simp only
  apply And.intro h1
  intro I2 h2
  rw [@char_complete_face SC n1 hn1 _ _ hcs.1] at h2
  obtain ⟨ i2, hi2 ⟩ := h2
  have h2 : SC.RL (J i2) = SC.n := by {
    let c2 := SC.RL (J i2)
    suffices h3 : ¬ (c2 ≤ n1) by {
      apply le_antisymm (SC.rl_proper (J i2)).1
      omega
    }
    intro h2
    obtain ⟨i3, hi3⟩ := hi2.2 c2 h2
    apply hi3.1
    apply rl_inj_of_complete SC.n J hcs
    exact hi3.2
  }
  suffices h3 : i2 = i by {
    rw [hi2.1, h3]
  }
  apply rl_inj_of_complete SC.n J hcs
  rw [h2]
  exact (Eq.symm hi)
}


lemma incomplete_childs {SC n1} {hn1 : n1 + 1 = SC.n} J (hs : simplex SC SC.n J)
    (hnc : ¬ complete_simplex SC SC.n J):
    Even (Finset.card { I : Fin (n1 + 1) → SC.G | complete_simplex SC n1 I ∧ is_face SC I J}) := by {
  let S : Finset _:= { I : Fin (n1 + 1) → SC.G | complete_simplex SC n1 I ∧ is_face SC I J}
  let c := S.card
  suffices h1 : c > 0 → c = 2 by {
    suffices h2 : Even c by {exact h2}
    by_cases h3 : c > 0
    rw [h1 h3]
    exact even_two
    use 0
    omega
  }
  intro cpos
  have h1 : Finset.Nonempty S := by {
    apply Finset.card_ne_zero.mp
    omega
  }
  obtain ⟨I1, h1 ⟩ := h1
  have hI1S := h1
  unfold S at h1
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1
  obtain ⟨i1, hi1 ⟩ := (@char_complete_face SC n1 hn1 I1 J hs).mp h1
  apply Finset.card_eq_two.mpr
  have h2 : SC.RL (J i1) ≤ n1 := by {
    by_contra h3
    apply hnc
    rw [complete_simplex_iff _ _ hs]
    intro c hc
    by_cases h4 : c ≤ n1
    {
      obtain ⟨i2, hi2 ⟩ := hi1.2 c h4
      use i2
      exact hi2.2
    }
    {
      use i1
      have h6 : c = SC.n := le_antisymm hc (le_of_eq_of_le hn1.symm (not_le.mp h4))
      rw [h6]
      apply le_antisymm (SC.rl_proper (J i1)).1
      exact le_of_eq_of_le hn1.symm (not_le.mp h3)
    }
  }
  obtain ⟨i2, hi2⟩ := hi1.2 (SC.RL (J i1)) h2
  let I2 := @delete_vertex SC n1 hn1 i2 J
  have hI2S : I2 ∈ S := by {
    unfold S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [@char_complete_face SC n1 hn1 I2 J hs]
    use i2
    apply And.intro rfl
    intro c hc
    obtain ⟨i3, hi3⟩ := hi1.2 c hc
    by_cases h4 : i3 = i2
    {
      use i1
      rw [← hi3.2,h4, hi2.2]
      exact And.intro hi2.1.symm rfl
    }
    {
      use i3
      exact And.imp_left (fun a ↦ h4) hi3
    }
  }
  use I1, I2
  apply And.intro
  {
    intro h3
    apply hi2.1
    apply @delete_vertex_inj SC n1 hn1 J hs
    rw [← hi1.1, h3]
  }
  ext I3
  simp only [Finset.mem_insert, Finset.mem_singleton]
  apply Iff.intro
  {
    intro h3
    unfold S at h3
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h3
    have h31 := h3
    rw [@char_complete_face SC n1 hn1 I3 J hs] at h3
    obtain ⟨ i3, hi3 ⟩ := h3
    by_contra h4
    simp only [not_or] at h4
    rw [hi1.1] at h4
    have h7 : ∀ i4, ¬ (I3 = @delete_vertex SC n1 hn1 i4 J) → i4 ≠ i3 := by {
      intro i4 h8 h9
      apply h8
      rw [hi3.1, h9]
    }
    have h5 := @almost_surjective_of_insert_index SC n1 hn1 i3
    obtain ⟨ k1, hk1 ⟩ := h5 i1 (h7 i1 h4.1)
    obtain ⟨ k2, hk2 ⟩ := h5 i2 (h7 i2 h4.2)
    apply hi2.1
    suffices h7 : k1 = k2 by {
      rw [hk1, hk2, h7]
    }
    apply rl_inj_of_complete n1 I3 h31.1
    rw [hi3.1]
    unfold delete_vertex
    rw [← hk1, ← hk2]
    exact hi2.2.symm
  }
  {
    intro h5
    cases h5
    rename_i h9
    rwa [h9]
    rename_i h9
    rwa [h9]
  }
}


lemma complete_boundary_face_last {SC n1} {hn1 : n1 + 1 = SC.n} (I : Fin (n1 + 1) → SC.G)
    (hcbf : complete_boundary_face SC I) :
    ∀ i, ∀ j, j.1 + 1 = SC.n →  (I i j).1 = SC.p := by {
  intro i j hj
  revert i
  have h3 := @boundary_is_A_or_B SC n1 hn1 I hcbf.1
  have h1 : j.1 = n1 := by omega
  have h4 : ∀ n2, n2 ≤ n1 → ∃ i, SC.RL (I i) = n2 := by {
    intro n2 hn2
    rw [← Set.mem_range, hcbf.2.2]
    simp only [Set.mem_setOf_eq, hn2]
  }
  have h6 (j2 : Fin SC.n) : j2.1 ≤ n1 := by omega
  cases h3
  {
    rename_i h1
    obtain ⟨ j2, hj2⟩ := h1
    exfalso
    obtain ⟨i, hi⟩ := h4 j2.1 (h6 j2)
    have h5 := ((SC.rl_proper (I i)).2 j2).1 (hj2 i)
    exact h5 hi
  }
  {
    rename_i h1
    obtain ⟨ j2, hj2⟩ := h1
    have hj3 i : (I i j2).1 = SC.p := by {
      rw [hj2 i]
      exact Fin.val_last SC.p
    }
    suffices h3 : j = j2 by {
      intro i
      rw [h3, hj3 i]
    }
    have h3 := SC.rl_proper
    obtain ⟨i, hi⟩ := h4 n1 (Nat.le_refl n1)
    have h5 := ((SC.rl_proper (I i)).2 j2).2 (hj3 i)
    rw [hi] at h5
    ext
    rw [h1]
    exact Nat.le_antisymm h5 (h6 j2)
  }
}

end completeness



section handshake

variable {A B : Type*}
variable [Fintype A] [Fintype B]

lemma handshake_3 (r : A → B → Prop) (c : A → Prop)
    (h1 : ∀ a, c a ↔ Odd (Finset.card {b | r a b}))
    : Odd (Finset.card {a | c a}) ↔ Odd (∑ a, Finset.card {b | r a b}) := by {
  rw [Finset.odd_sum_iff_odd_card_odd]
  rw [iff_eq_eq]
  congr
  ext a
  exact h1 a
}

lemma handshake_2 (r : A → B → Prop)
    (c : A → Prop) (d : B → Prop)
    (h1 : ∀ a, c a ↔ Odd (Finset.card {b | r a b}))
    (h2 : ∀ b, d b ↔ Odd (Finset.card {a | r a b})) :
    Odd (Finset.card {a | c a}) → Odd (Finset.card {b | d b}) := by {
  intro h3
  have h5 : ∑ a, Finset.card {b | r a b} = ∑ b, Finset.card {a | r a b} := by {
    apply Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
  }
  let r2 b a := r a b
  rw [handshake_3 r2 d h2, ←h5]
  rwa [←handshake_3 r c h1]
}

lemma handshake_1 (r : A → B → Prop)
    (c1 c2 c3: A → Prop) (d1 d2: B → Prop)
    (h1 : ∀ b, d1 b → ∃! a, c2 a ∧ r a b)
    (h2 : ∀ b, d2 b → ¬ d1 b → Even (Finset.card { a | c2 a ∧ r a b}))
    (h3 : ∀ a, c3 a → Finset.card { b | r a b} ∈ {c | c = 1 ∨ c = 2})
    (h5 : ∀ a, c1 a ↔ (∃! b, r a b) ∧ c2 a)
    (h6 : ∀ a, c2 a → c3 a) (h7 : ∀ b, ∀ a, r a b → d2 b)
    : Odd (Finset.card {a : A | c1 a}) → Odd (Finset.card {b : B | d1 b}) := by {
  let r2 a b := c2 a ∧ r a b
  apply handshake_2 r2
  {
    intro a
    rw [h5]
    by_cases p1 : c2 a
    unfold r2
    simp only [p1, and_true, true_and]
    rw [Fintype.existsUnique_iff_card_one]
    apply Iff.intro
    {
      intro p2
      use 0
      rwa [mul_zero, zero_add]
    }
    {
      intro p2
      have p3 := h3 a (h6 a p1)
      simp only [Set.mem_setOf_eq] at p3
      cases p3
      rename_i p4
      exact p4
      rename_i p4
      rw [p4] at p2
      exfalso
      revert p2
      simp only [imp_false, Nat.not_odd_iff_even, even_two]
    }
    {
      unfold r2
      simp only [p1, and_false, false_and, Finset.filter_false, Finset.card_empty, Nat.not_odd_zero]
    }
  }
  {
    intro b
    by_cases p1 : d1 b
    {
      simp only [p1, true_iff]
      use 0
      rw [mul_zero, zero_add]
      rw [← Fintype.existsUnique_iff_card_one]
      exact h1 b p1
    }
    {
      simp only [p1, false_iff]
      intro p2
      have p5 : Finset.Nonempty {a | r2 a b} := by {
        have p3 : Odd (Finset.card { a | r2 a b}) := by {
          convert p2
        }
        apply Finset.card_ne_zero.mp
        intro p4
        revert p3
        rw [p4]
        simp only [Nat.not_odd_zero, imp_self]
      }
      have p3 : d2 b := by {
        obtain ⟨a, p6⟩ := p5
        apply h7 b a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at p6
        exact p6.2
      }
      revert p2
      have p4 := h2 b p3 p1
      simp only [imp_false, Nat.not_odd_iff_even]
      convert p4
    }
  }
}

end handshake



lemma odd_of_boundary_faces SC {n1} {hn1 : n1 + 1 = SC.n}:
    Odd (Finset.card { I : Fin (n1 + 1) → SC.G | complete_boundary_face SC I})
    → Odd (Finset.card { I | complete_simplex SC SC.n I}) := by {
  apply handshake_1 (is_face SC)
  apply @complete_child_uniq SC n1 hn1
  apply @incomplete_childs SC n1 hn1
  apply @parent_count SC n1 hn1
  {
    intro I
    rfl
  }
  exact fun _ h1 ↦ h1.1
  exact fun _ _ h1 ↦ h1.2.1
}


section induction_step

variable (SC : SpernerCube)
variable {n1 : ℕ}


def child_map (v : Fin n1 → Fin (SC.p+1) ) : SC.G := fun i ↦
  match n1 with
  | 0 => Fin.last SC.p
  | Nat.succ _ => if i.1 + 1 = SC.n then Fin.last SC.p else v (Fin.ofNat _ i.1)

lemma child_map_last (v : Fin n1 → Fin (SC.p +1 ))
    : ∀ j, j.1 + 1 = SC.n → child_map SC v j = SC.p := by {
  intro j hj
  unfold child_map
  cases n1
  rfl
  simp only [hj, ↓reduceIte, Fin.val_last]
}

lemma child_map_applied [NeZero SC.n] {hn1 : n1 + 1 = SC.n} (v : Fin n1 → Fin (SC.p + 1))
    : ∀ (i : Fin n1), child_map SC v (Fin.ofNat _ i.1) = v i := by {
  intro i
  dsimp only [child_map]
  cases n1
  exact Fin.elim0 i
  rename_i n2
  simp only [Nat.succ_eq_add_one]
  have h5 : i.1 + 1 < SC.n := by omega
  have h2 : i.1 < SC.n := by omega
  have h3 := Fin.val_cast_of_lt h2
  rw [Fin.ofNat_eq_cast, h3]
  have h6 : i.1 + 1 ≠ SC.n := by omega
  simp only [h6, ↓reduceIte, Fin.ofNat_eq_cast, Fin.cast_val_eq_self]
}

lemma child_map_inj {hn1 : n1 + 1 = SC.n }: Function.Injective (@child_map SC n1) := by {
  intro v1 v2 h1
  ext i
  have h0 : NeZero SC.n := by {
    rw [← hn1]
    exact instNeZeroNatHAdd_1
  }
  rw [← child_map_applied SC v1]
  rw [← child_map_applied SC v2]
  rwa [h1]
  exact hn1
}

lemma child_map_surj_on {hn1 : n1 + 1 = SC.n} w
    (h1 : ∀ j, j.1 + 1 = SC.n → w j = SC.p)
    : ∃ v, @child_map SC n1 v = w := by {
  have h0 : NeZero SC.n := by {
    rw [← hn1]
    exact instNeZeroNatHAdd_1
  }
  let v2 : Fin n1 → Fin (SC.p +1) := fun i ↦ w (Fin.ofNat _ i.1)
  use v2
  apply funext
  intro i
  unfold child_map
  cases n1
  {
    simp only
    have h2 := h1 0
    simp only [Fin.val_zero, zero_add] at h2 hn1
    have h3 : i = 0 := by {
      have h4 := i.2
      simp only [← hn1] at h4
      ext
      simp only [Fin.val_zero]
      exact Nat.lt_one_iff.mp h4
    }
    rw [h3]
    exact Fin.eq_of_val_eq (id (Eq.symm (h2 hn1)))
  }
  {
    rename_i n2
    have h2 := h1 i
    by_cases h3 : i.1 +1 = SC.n
    {
      simp only [h3, ↓reduceIte]
      exact Eq.symm (Fin.eq_of_val_eq (h1 i h3))
    }
    simp only [h3, ↓reduceIte, Nat.succ_eq_add_one]
    unfold v2
    congr
    simp only [Fin.ofNat_eq_cast]
    rw [Fin.val_cast_of_lt]
    exact Fin.cast_val_eq_self i
    have h4 := i.2
    simp only [← hn1] at h3 h4
    omega
  }
}

@[reducible] def child_cube {hn1 : n1 + 1 = SC.n}: SpernerCube where
  n := n1
  p := SC.p
  RL := fun v ↦ SC.RL (child_map SC v)
  rl_proper := by {
    intro v
    have h0 : NeZero SC.n := by {
      rw [← hn1]
      exact instNeZeroNatHAdd_1
    }
    have h1 := child_map_last SC v
    have h2 := SC.rl_proper (child_map SC v)
    apply And.intro
    {
      have h3 := (h2.2 (Fin.ofNat _ n1)).2
      have h4 : n1 < SC.n := by omega
      simp only [Fin.ofNat_eq_cast] at h3
      rw [Fin.val_cast_of_lt h4] at h3
      apply h3
      apply child_map_last
      rw [Fin.val_cast_of_lt h4]
      exact hn1
    }
    intro i
    have h3 := h2.2 (Fin.ofNat _ i.1)
    rw [child_map_applied] at h3
    have h4 : (Fin.ofNat SC.n i.1).1 = i.1 := by {
      apply Fin.val_cast_of_lt
      omega
    }
    rwa [h4] at h3
    exact hn1
  }


end induction_step


lemma induction_start (SC : SpernerCube) (h0 : 0 = SC.n)
    : Odd (Finset.card { I | complete_simplex SC SC.n I}) := by {
  use 0
  simp only [mul_zero, zero_add]
  rw [←Fintype.existsUnique_iff_card_one]
  let b : SC.G := fun _ ↦ 0
  let a : Fin (SC.n + 1) → SC.G := fun _ ↦ b
  use a
  simp only
  have h1 (x : Fin (SC.n+1)) : x = 0 := by {
    ext
    simp only [Fin.val_zero]
    rw [← Nat.lt_one_iff]
    apply Fin.val_lt_of_le x
    rw [←h0]
  }
  have hf (j : Fin SC.n) : False := by {
    apply Fin.elim0
    rwa [h0]
  }
  apply And.intro
  apply And.intro
  apply And.intro
  {
    intro x1 x2 _
    rw [h1 x1, h1 x2]
  }
  {
    intro i hi j
    exact False.elim ( hf j )
  }
  {
    ext i
    simp only [← h0]
    simp only [Set.mem_range, nonpos_iff_eq_zero, Set.setOf_eq_eq_singleton, Set.mem_singleton_iff]
    have h3 : ∀ c, SC.RL (a c) = 0 := by {
      intro c
      have h2 := (SC.rl_proper (a c)).1
      simp only [← h0] at h2
      omega
    }
    apply Iff.intro
    {
      intro h2
      cases h2
      rename_i c hc
      rw [h3 c] at hc
      exact (Eq.symm hc)
    }
    {
      intro hi0
      use 0
      rw [hi0]
      exact h3 0
    }
  }
  {
    intro a2 h2
    ext i
    apply funext
    intro j
    exact False.elim ( hf j )
  }
}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem strong_cubical_sperner (k: ℕ ) : ∀ (SC : SpernerCube), k = SC.n →
    Odd (Finset.card { I | complete_simplex SC SC.n I}) := by {
  classical
  induction' k with k hind
  {
    intro SC hk
    exact induction_start SC hk
  }
  {
    intro SC1 hk1
    apply @odd_of_boundary_faces SC1 k hk1
    let SC2 := @child_cube SC1 k hk1
    have hnz : NeZero SC1.n := by {
      rw [← hk1]
      exact instNeZeroNatHAdd_1
    }
    have h2 := hind SC2 rfl
    apply Eq.mpr _ h2
    apply congrArg
    let f1 : SC2.G → SC1.G := child_map SC1
    let f2 : (Fin (k+1)→ SC2.G) → (Fin (k+1)→ SC1.G) := fun a ↦ fun b ↦ f1 (a b)
    have hf1inj : Function.Injective f1 := by {
      apply child_map_inj SC1
      rw [← hk1]
    }
    symm
    have hcomp I : complete_boundary_face SC1 (f2 I) ↔ complete_simplex SC2 SC2.n I := by {
      unfold complete_boundary_face complete_simplex
      have h_last j k: j.1 + 1 = SC1.n → f2 I k j = SC1.p := by {
        apply child_map_last
      }
      have h_bf : simplex SC1 k (f2 I) ↔ is_boundary_face SC1 (f2 I) ∧ simplex SC1 k (f2 I):= by {
        simp only [iff_and_self]
        intro hs
        apply @case_B_boundary SC1 k hk1
        exact hs
        use (Fin.ofNat _ k)
        intro i
        ext
        apply h_last
        simp [← hk1]
      }
      rw [← and_assoc, ←h_bf]
      have h3 : SC2.n = k := rfl
      apply and_congr
      apply and_congr
      {
        apply Iff.intro
        {
          intro h4 i1 i2 h5
          exact h4 (congrArg f1 h5)
        }
        {
          intro h4 i1 i2 h5
          apply h4
          apply hf1inj h5
        }
      }
      {
        simp only [h3]
        apply forall₂_congr
        intro i hi1
        apply Iff.intro
        {
          intro h4 j
          have h6 k : (f2 I k (Fin.ofNat _ j.1)) = (I k j) := by {
            unfold f2
            apply child_map_applied
            rw [← hk1]
          }
          simpa only [h6] using h4 (Fin.ofNat _ j.1)
        }
        {
          intro h4 j
          by_cases h5 : j.1 + 1 = SC1.n
          {
            rw [h_last, h_last, h_last, h_last]
            simp only [le_refl, le_add_iff_nonneg_right, zero_le,
              and_self]
            repeat' exact h5
          }
          {
            have h7 : j.1 < SC2.n := by {
              rw [h3]
              have h6 := j.2
              simp only [← hk1] at h5 h6
              omega
            }
            have hn02 : NeZero SC2.n := by {
              exact NeZero.of_gt hi1
            }
            let j2 : Fin SC2.n := (Fin.ofNat _ j.1)
            have h8 : j = (Fin.ofNat _ j2.1) := by {
              unfold j2
              simp only [Fin.ofNat_eq_cast,]
              rw [Fin.val_cast_of_lt]
              exact Eq.symm (Fin.cast_val_eq_self j)
              exact h7
            }
            have h6 k : (f2 I k j) = (I k j2) := by {
              unfold f2
              rw [h8]
              apply child_map_applied
              exact hk1
            }
            rw [h6, h6, h6, h6]
            exact h4 j2
          }
        }
      }
      exact Eq.congr_right rfl
    }
    apply Finset.card_nbij f2
    {
      intro I hI
      have hI' : complete_simplex SC2 SC2.n I :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp hI)).2
      exact Finset.mem_coe.mpr
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hcomp I).mpr hI'⟩)
    }
    {
      intro I1 h41 I2 h42 h5
      ext i
      apply hf1inj
      exact congrFun h5 i
    }
    {
      simp only [Finset.coe_filter, Finset.mem_univ, true_and]
      intro J
      simp only [Set.mem_setOf_eq, Set.mem_image]
      intro h3
      have h4 : ∃ I, f2 I = J := by {
        suffices h6 : ∀ i, ∃ ii, f1 ii = J i by {
          obtain ⟨I, h5⟩  := axiomOfChoice h6
          use I
          ext i
          exact h5 i
        }
        intro i
        have h5 := @child_map_surj_on SC1 k hk1
        apply h5
        exact @complete_boundary_face_last SC1 k hk1 J h3 i
      }
      obtain ⟨I, h4⟩ := h4
      use I
      simp only [h4, and_true]
      exact (hcomp I).mp (h4 ▸ h3)
    }
  }

}

theorem weaker_cubical_sperner SC : ∃ I, complete_simplex SC SC.n I := by {
  have h1 := strong_cubical_sperner SC.n SC rfl
  obtain ⟨k1, hk1⟩ := h1
  have h2 : 0 < 2 * k1 + 1 := by omega
  rw [←hk1, Finset.card_pos] at h2
  obtain ⟨I, hI1⟩ := h2
  use I
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hI1
  exact hI1
}
end

-- Source module OptimalG.External.FixedPointTheorems.apply_cubical_sperner
section
set_option autoImplicit true
open Classical

/-
shows the fixed-point theorem for the unit cube
by applying the cubical sperner's lemma
-/


variable {n : ℕ}

def unit_cube := { v : Fin n → ℝ | 0 ≤ v ∧ v ≤ 1 }

noncomputable def rl_point {f : @unit_cube n → @unit_cube n} (x : @unit_cube n) : ℕ :=
  match (Finset.min { i | (f x).1 i < x.1 i ∨ x.1 i = 1}) with
    | some k => k.1
    | none => n

lemma reduced_label_props_1 (f : @unit_cube n → @unit_cube n) (x : @unit_cube n)
    : @rl_point n f x ≤ n ∧ ∀ k,
    (@rl_point n f x = k.1 → (f x).1 k < x.1 k ∨ x.1 k = 1)
    ∧ ((f x).1 k < x.1 k ∨ x.1 k = 1 → @rl_point n f x ≤ k.1) := by {
  let s : Finset (Fin n) := {i | (f x).1 i < x.1 i ∨ x.1 i = 1}
  let minval := Finset.min s
  let rlp := match minval with
    | some k => k.1
    | none => n
  by_cases he : s = ∅
  {
    have h1 : @rl_point n f x = n := by {
      show rlp = n
      unfold rlp minval
      rw [he]
      simp only [Finset.min_empty]
    }
    rw [h1]
    simp only [le_refl, true_and]
    intro k
    have h2 : n ≠ k.1 := by omega
    simp only [h2, IsEmpty.forall_iff, true_and]
    intro h3
    have h4 : k ∈ s := by {
      unfold s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h3
    }
    rw [he] at h4
    simp only [Finset.notMem_empty] at h4
  }
  have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
  obtain ⟨m, hm⟩ := Finset.min_of_nonempty hne
  have h1 : @rl_point n f x = m.1 := by {
    show rlp = m.1
    unfold rlp minval
    rw [hm]
  }
  rw [h1]
  simp only [Fin.is_le', Fin.val_fin_le, true_and]
  intro k1
  apply And.intro
  {
    intro h2
    suffices h3 : k1 ∈ s by {
      unfold s at h3
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h3
      exact h3
    }
    apply Finset.mem_of_min
    rw [hm]
    simp only [WithTop.coe_eq_coe]
    ext
    exact h2
  }
  {
    intro h2
    have h3 : k1 ∈ s := by {
      unfold s
      simp only [Finset.mem_filter, Finset.mem_univ, h2, and_self]
    }
    exact Finset.min_le_of_eq h3 hm
  }
}

lemma reduced_label_props_2 (f : @unit_cube n → @unit_cube n) (x : @unit_cube n)
    : @rl_point n f x ≤ n ∧
    ∀ k, (x.1 k = 0 → @rl_point n f x ≠ k.1) ∧ (x.1 k = 1 → @rl_point n f x ≤ k.1):= by {
  have h1 := reduced_label_props_1 f x
  apply And.intro h1.1
  intro k
  apply And.intro
  {
    intro h2 h3
    have h4 := (h1.2 k).1 h3
    rw [h2] at h4
    simp only [zero_ne_one, or_false] at h4
    contrapose! h4
    exact (f x).2.1 k
  }
  {
    intro h2
    apply (h1.2 k).2
    exact Or.inr h2
  }
}

lemma reduced_label_props_3 (f : @unit_cube n → @unit_cube n) (x : @unit_cube n) (k : Fin n)
    : (@rl_point n f x = k → (f x).1 k ≤ x.1 k) ∧ (@rl_point n f x > k → (f x).1 k ≥ x.1 k) := by {
  have h1 := (reduced_label_props_1 f x).2 k
  apply And.intro
  {
    intro h2
    cases h1.1 h2
    (expose_names; exact le_of_lt h)
    rename_i h3
    rw [h3]
    exact (f x).2.2 k
  }
  {
    contrapose!
    intro h2
    apply h1.2
    exact Or.inl h2
  }
}

noncomputable def discrete_map (p : ℕ ) (v : Fin n → Fin (p+1)) : @unit_cube n :=
  ⟨ fun i ↦ ((v i).1 : ℝ ) / p , by {
    unfold unit_cube
    simp only [Set.mem_setOf_eq]
    rw [Pi.le_def, Pi.le_def, ←forall_and]
    intro i
    simp only [Pi.zero_apply, Pi.one_apply]
    apply And.intro
    exact div_nonneg (Nat.cast_nonneg' ↑(v i)) (Nat.cast_nonneg' p)
    apply div_le_one_of_le₀ ?_ (Nat.cast_nonneg' p)
    simp only [Nat.cast_le]
    exact Fin.is_le (v i)
  }⟩

noncomputable def sperner_cube_of_function (f : @unit_cube n → @unit_cube n)
  (p : ℕ ) {ppos : 0 < p} : SpernerCube where
  n := n
  p := p
  RL := fun v ↦ @rl_point _ f (discrete_map p v)
  rl_proper := by {
    intro v
    let x := discrete_map p v
    have h1 := reduced_label_props_2 f x
    apply And.intro h1.1
    intro k
    apply And.intro
    {
      intro h2
      apply (h1.2 k).1
      unfold x discrete_map
      simp only [div_eq_zero_iff, Nat.cast_eq_zero, Fin.val_eq_zero_iff]
      exact Or.inl h2
    }
    {
      intro h2
      apply (h1.2 k).2
      unfold x discrete_map
      simp only [h2]
      refine (div_eq_one_iff_eq ?_).mpr rfl
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    }
  }

lemma dist_discrete_map p (ppos: 0 < p) (v1 v2 : Fin n → Fin (p+1))
    (h1 : ∀ k, (v1 k).1 ≤ (v2 k).1 + 1 ∧ (v2 k).1 ≤ (v1 k).1 + 1) :
    dist (discrete_map p v1) (discrete_map p v2) ≤ 1 / p := by {
  let x1 := (discrete_map p v1).1
  let x2 := (discrete_map p v2).1
  show dist x1 x2 ≤ 1 / p
  refine (dist_pi_le_iff ?_).mpr ?_
  simp only [one_div, inv_nonneg, Nat.cast_nonneg]
  intro k
  have hx1 : x1 k = (v1 k).1 / p := by {rfl}
  have hx2 : x2 k = (v2 k).1 / p := by {rfl}
  rw [hx1, hx2]
  rw [Real.dist_eq, abs_sub_le_iff]
  have h1k := (h1 k).1
  have h2k := (h1 k).2
  apply And.intro
  repeat {
    rw [sub_le_iff_le_add', ← add_div]
    have ppos2 : 0 < (p : ℝ) := Nat.cast_pos'.mpr ppos
    rwa [div_le_div_iff_of_pos_right ppos2, ←Nat.cast_add_one, Nat.cast_le]
  }
}

lemma nearby_points (f : @unit_cube n → @unit_cube n) (p0:ℕ):
    ∃ x0 : @unit_cube n, ∀ k, (f x0).1 k ≥ x0.1 k ∧
    ∃ xk : @unit_cube n, dist x0 xk ≤ 1 / ↑(p0 +1) ∧ (f xk).1 k ≤ xk.1 k := by {
  let p := p0 + 1
  have ppos : 0 < p := by omega
  let SC := @sperner_cube_of_function n f p ppos
  obtain ⟨I, h3⟩ := weaker_cubical_sperner SC
  have h4 j : j ≤ n → ∃ i, SC.RL (I i) = j := by {
    intro h4
    exact h3.2.symm.subset h4
  }
  obtain ⟨i0, hi0⟩ := h4 n (Nat.le_refl n)
  let x0 := discrete_map SC.p (I i0)
  use x0
  intro k
  apply And.intro
  {
    apply (reduced_label_props_3 f x0 k).2
    have h6 : @rl_point _ f x0 = n := by exact hi0
    rw [h6]
    simp only [gt_iff_lt, Fin.is_lt]
  }
  obtain ⟨ik, hik⟩ := h4 k.1 k.is_le'
  let xk := discrete_map SC.p (I ik)
  use xk
  apply And.intro _ $ (reduced_label_props_3 f xk k).1 hik
  unfold x0 xk
  apply dist_discrete_map p ppos
  have h5 := le_add_one_of_simplex SC I h3.1
  intro k
  exact ⟨h5 i0 ik k, h5 ik i0 k⟩
}


theorem fixed_point_unit_cube (f : C(@unit_cube n, @unit_cube n)) : ∃ x, f x = x := by {
  obtain ⟨x0s, hx0⟩ := axiomOfChoice (nearby_points f)
  have hc1 : ∃ xx : @unit_cube n, ∃ (φ:ℕ → ℕ ), StrictMono φ ∧
      Filter.Tendsto (x0s ∘ φ ) Filter.atTop (nhds xx) := by {
    have hc1 : IsCompact (@unit_cube n) := isCompact_Icc
    let x0 : ℕ → Fin n → ℝ := fun i ↦ (x0s i).1
    have h2 : ∀ i, x0 i ∈ unit_cube := fun i ↦ (x0s i).2
    obtain ⟨a, ⟨ha, ⟨φ,h3⟩ ⟩ ⟩ := hc1.isSeqCompact h2
    use ⟨a, ha⟩
    use φ
    exact And.intro h3.1 $ tendsto_subtype_rng.mpr h3.2
  }
  obtain ⟨xxx, ⟨φ, h2⟩ ⟩ := hc1
  let y0 := x0s ∘ φ
  let g : Fin n → @unit_cube n → ℝ := fun k x ↦ x.1 k
  have hc2 k : Continuous (g k) := by {
    exact (continuous_apply k).comp continuous_subtype_val
  }
  have h3 k : xxx.1 k ≤ (f xxx).1 k := by {
    show g k xxx ≤ g k (f xxx)
    have h6 :=  (hc2 k).seqContinuous h2.2
    have h7 := (hc2 k).seqContinuous $ f.2.seqContinuous h2.2
    apply le_of_tendsto_of_tendsto' h6 h7
    exact fun i ↦ (hx0 (φ i) k).1
  }
  have h4 k : (f xxx).1 k ≤ xxx.1 k := by {
    show g k (f xxx) ≤ g k xxx
    have h5 n:= (hx0 (φ n) k).2
    obtain ⟨yk, h6⟩ := axiomOfChoice h5
    have h4 : Filter.Tendsto yk Filter.atTop (nhds xxx) := by {
      apply tendsto_of_tendsto_of_dist h2.2
      have h7 := @tendsto_one_div_add_atTop_nhds_zero_nat ℝ _ _ _ _
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h7 _
      {
        intro i
        apply le_trans (h6 i).1
        simp only [Nat.cast_add, Nat.cast_one, one_div]
        apply inv_anti₀ (Nat.cast_add_one_pos i)
        simp only [add_le_add_iff_right, Nat.cast_le, h2.1.le_apply]
      }
      exact fun _ ↦ dist_nonneg
    }
    have h7 := (hc2 k).seqContinuous h4
    have h8 := (hc2 k).seqContinuous $ f.2.seqContinuous h4
    apply le_of_tendsto_of_tendsto' h8 h7
    exact fun i ↦ (h6 i).2
  }
  use xxx
  ext k
  apply le_antisymm (h4 k) (h3 k)
}

/-- The cubical fixed-point theorem stated with mathlib's `Function.IsFixedPt` vocabulary. -/
theorem fixed_point_unit_cube_isFixedPt (f : C(@unit_cube n, @unit_cube n)) :
    ∃ x, Function.IsFixedPt f x := by
  simpa [Function.IsFixedPt] using fixed_point_unit_cube f
end

-- Source module OptimalG.External.FixedPointTheorems.convex_homeos
section
set_option autoImplicit true
/-
some helper lemmas involving homeomorphisms.
-/


lemma homeo_unit_ball {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s: Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s)
    (hni : (interior s).Nonempty):
    Nonempty (s ≃ₜ Metric.closedBall (0: V) 1) := by {
  have h1 := exists_homeomorph_image_interior_closure_frontier_eq_unitBall hcvx hni
  have h2 : Bornology.IsBounded s := IsCompact.isBounded hcmpct
  cases (h1 h2)
  rename_i e he
  have h4 := closure_eq_iff_isClosed.mpr (IsCompact.isClosed hcmpct)
  have e2 := Homeomorph.image e s
  rw [h4] at he
  rw [he.2.1] at e2
  exact Nonempty.intro e2
}


theorem homeo_of_finrank_eq {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (hreq : Module.finrank ℝ V = Module.finrank ℝ W) :
    Nonempty (Metric.closedBall (0: V) 1 ≃ₜ Metric.closedBall (0: W) 1) := by {
  have L := ContinuousLinearEquiv.ofFinrankEq hreq
  let pL := L ⁻¹' (Metric.closedBall (0:W) 1)
  have hpL : pL = L.toHomeomorph ⁻¹' (Metric.closedBall (0:W) 1) := rfl
  have h4 : Convex ℝ pL := Convex.linear_preimage (convex_closedBall 0 1) L.toLinearMap
  have h5 : IsCompact pL := by {
    rw [hpL,Homeomorph.isCompact_preimage]
    exact isCompact_closedBall 0 1
  }
  have h6 : (interior pL).Nonempty := by {
    rw [hpL, ← Homeomorph.preimage_interior]
    refine (Function.Surjective.nonempty_preimage ?_).mpr ?_
    exact Homeomorph.surjective L.toHomeomorph
    use 0
    rw [interior_closedBall]
    {simp only [Metric.mem_ball, dist_self, zero_lt_one]}
    {exact Ne.symm (zero_ne_one' ℝ)}
  }
  have e1 : pL ≃ₜ Metric.closedBall (0:W) 1 := by {
    rw [hpL]
    exact L.toHomeomorph.sets hpL
  }
  have h7 := homeo_unit_ball _ h4 h5 h6
  cases h7
  rename_i e2
  apply Nonempty.intro
  exact e2.symm.trans e1
}


lemma unit_cube_homeo_unit_ball {n}
    : Nonempty (Set.Icc (0 : Fin n → ℝ) 1 ≃ₜ Metric.closedBall (0 : Fin n → ℝ) 1 ) := by
  apply homeo_unit_ball _ (convex_Icc 0 1) isCompact_Icc
  have h1 : Set.Icc (0 : Fin n → ℝ) 1 = Set.univ.pi (fun _ => Set.Icc (0 : ℝ) 1) := by
    ext x; simp [Set.mem_Icc, Pi.le_def]
  rw [h1, interior_pi_set Set.finite_univ]
  exact Set.univ_pi_nonempty_iff.mpr fun _ => by
    rw [interior_Icc]; exact ⟨1/2, by norm_num, by norm_num⟩

lemma homeo_unit_cube_of_convex_compact {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s: Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s) (hne : s.Nonempty)
    : ∃ k, Nonempty (s ≃ₜ Set.Icc (0 : Fin k → ℝ) 1) := by {
  haveI := hne.coe_sort
  let W := affineSpan ℝ s
  obtain ⟨ps, hps⟩ := hne
  let pss : W := ⟨ps, mem_affineSpan ℝ hps⟩
  let g2 := AffineIsometryEquiv.constVSub ℝ pss
  let g1 : W → V := fun x ↦ x.1
  let s2 := g1 ⁻¹' s
  let s3 := g2.symm ⁻¹' s2
  have h32 : Convex ℝ s3 := by {
    exact hcvx.affine_preimage
      ((affineSpan ℝ s).subtype.comp
      (AffineIsometryEquiv.constVSub ℝ pss).symm.toAffineMap)
  }
  have h34 : (interior s3).Nonempty := by {
    refine (Convex.interior_nonempty_iff_affineSpan_eq_top h32).mpr ?_
    unfold s3
    rw [←AffineIsometryEquiv.coe_toAffineEquiv]
    rw [← AffineSubspace.comap_span]
    rw [affineSpan_coe_preimage_eq_top]
    rfl
  }
  let g3 := g1.comp g2.symm
  have h4 : Topology.IsEmbedding g3 := by {
    apply Topology.IsEmbedding.subtypeVal.comp g2.symm.toHomeomorph.isEmbedding
  }
  have h5 : Set.MapsTo g3 s3 s := by {
    intro w h1
    unfold s3 s2 at h1
    rwa [Set.mem_preimage, Set.mem_preimage] at h1
  }
  have h6 : Function.Surjective (Set.MapsTo.restrict g3 s3 s h5) := by {
    refine (Set.MapsTo.restrict_surjective_iff h5).mpr ?_
    refine Set.SurjOn.comp_right ?_ ?_
    exact AffineIsometryEquiv.surjective g2.symm
    intro v h1
    refine (Set.mem_image g1 (g1 ⁻¹' s) v).mpr ?_
    have h11 : v ∈ affineSpan ℝ s := mem_affineSpan ℝ h1
    use ⟨v, h11⟩
    simp only [Set.mem_preimage]
    apply And.intro h1 rfl
  }
  let e1 := (h4.restrict h5).toHomeomorphOfSurjective h6
  have h31 : IsCompact s3 := by {
    have h51 : _ → IsCompact Set.univ := (Homeomorph.isCompact_image e1).mp
    simp only [Set.image_univ, EquivLike.range_eq_univ] at h51
    apply isCompact_iff_isCompact_univ.mpr
    apply h51 $ isCompact_iff_isCompact_univ.mp hcmpct
  }
  obtain ⟨e2⟩ := homeo_unit_ball s3 h32 h31 h34
  let k := Module.finrank ℝ W.direction
  obtain ⟨e3⟩ := @unit_cube_homeo_unit_ball k
  have h2 : k = Module.finrank ℝ (Fin k → ℝ) := (Module.finrank_fin_fun ℝ).symm
  obtain ⟨e4⟩ := homeo_of_finrank_eq h2
  let e5 := (e1.symm.trans e2).trans (e4.trans e3.symm)
  use k
  exact Nonempty.intro e5
}
end

-- Source module OptimalG.External.FixedPointTheorems.brouwer
section
set_option autoImplicit true
/- Brouwer fixed-point theorem:
Every continuous function mapping a nonempty compact convex set to itself has a fixed point
(the set should be a subset of a finite dimensional vector space).

https://en.wikipedia.org/wiki/Brouwer_fixed-point_theorem
-/


theorem brouwer_fixed_point {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    : ∀ (s : Set V), Convex ℝ s → IsCompact s → Set.Nonempty s →
    ∀ (f : C(s, s)), ∃ x, f x = x := by {
  intro s hcvx hcmpct hne f
  obtain ⟨k, ⟨e⟩ ⟩ := homeo_unit_cube_of_convex_compact s hcvx hcmpct hne
  let g := (toContinuousMap e).comp (f.comp (toContinuousMap e.symm))
  obtain ⟨y, hy⟩ := @fixed_point_unit_cube k g
  use (toContinuousMap e.symm) y
  have h1 : e.symm (e (f (e.symm y))) = e.symm y := congrArg e.symm hy
  rwa [e.symm_apply_apply] at h1
}

/-- Brouwer's fixed-point theorem stated with mathlib's `Function.IsFixedPt` vocabulary. -/
theorem brouwer_fixed_point_isFixedPt {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s) (hne : Set.Nonempty s)
    (f : C(s, s)) :
    ∃ x, Function.IsFixedPt f x := by
  simpa [Function.IsFixedPt] using brouwer_fixed_point s hcvx hcmpct hne f

/-- The fixed-point set of a continuous self-map on a Brouwer domain is nonempty. -/
theorem brouwer_fixedPoints_nonempty {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s) (hne : Set.Nonempty s)
    (f : C(s, s)) :
    (Function.fixedPoints f).Nonempty := by
  exact brouwer_fixed_point_isFixedPt s hcvx hcmpct hne f
end

-- Source module OptimalG.StableFixedPoint
section
set_option autoImplicit true
/-! # A continuous score partition has a stable lottery

The fixed-point theorem is supplied by the pinned, fully proved cubical Sperner
development in `External/FixedPointTheorems`; no fixed-point axiom is used.
-/

namespace OptimalG
open Set
open scoped BigOperators

/-- A continuous finite score map whose lottery-weighted mean is fixed admits
a lottery at which every candidate score is at most that mean. -/
theorem exists_simplex_score_bound {m : ℕ} [NeZero m]
    (score : (Fin m → ℝ) → Fin m → ℝ) (mean : ℝ)
    (hcont : ∀ a, ContinuousOn (fun D => score D a) (stdSimplex ℝ (Fin m)))
    (hpartition : ∀ D ∈ stdSimplex ℝ (Fin m), expectation D (score D) = mean) :
    ∃ D ∈ stdSimplex ℝ (Fin m), ∀ a, score D a ≤ mean := by
  classical
  let K := stdSimplex ℝ (Fin m)
  let delta := fun (D : K) a => max 0 (score D.val a - mean)
  let total := fun D : K => ∑ a, delta D a
  have hdelta : ∀ D a, 0 ≤ delta D a := fun D a => le_max_left _ _
  have htotal : ∀ D, 0 ≤ total D := fun D => Finset.sum_nonneg (fun a _ => hdelta D a)
  have hden : ∀ D, 0 < 1 + total D := fun D => by linarith [htotal D]
  have hcDelta : ∀ a, Continuous (fun D : K => delta D a) := by
    intro a
    exact continuous_const.max ((hcont a).restrict.sub continuous_const)
  have hcTotal : Continuous total := continuous_finsetSum _ (fun a _ => hcDelta a)
  let next := fun (D : K) a => (D.val a + delta D a) / (1 + total D)
  have hnext : ∀ D, next D ∈ K := by
    intro D
    constructor
    · intro a
      exact div_nonneg (add_nonneg (D.property.1 a) (hdelta D a)) (hden D).le
    · dsimp [next]
      rw [← Finset.sum_div, Finset.sum_add_distrib, D.property.2]
      exact div_self (ne_of_gt (hden D))
  have hcNext : Continuous next := by
    apply continuous_pi
    intro a
    exact (((continuous_apply a).comp continuous_subtype_val).add (hcDelta a)).div
      (continuous_const.add hcTotal) (fun D => ne_of_gt (hden D))
  let F : C(K, K) := ⟨fun D => ⟨next D, hnext D⟩, hcNext.subtype_mk hnext⟩
  have hne : K.Nonempty := ⟨Pi.single (0 : Fin m) 1, single_mem_stdSimplex ℝ 0⟩
  obtain ⟨D, hfixed⟩ := brouwer_fixed_point K (convex_stdSimplex ℝ (Fin m))
    (isCompact_stdSimplex ℝ (Fin m)) hne F
  have hfix (a : Fin m) : delta D a = D.val a * total D := by
    have he := congrArg (fun Q : K => Q.val a) hfixed
    change (D.val a + delta D a) / (1 + total D) = D.val a at he
    have hm := (div_eq_iff (ne_of_gt (hden D))).mp he
    nlinarith only [hm]
  refine ⟨D.val, D.property, ?_⟩
  intro a
  by_contra! ha
  have hda : 0 < delta D a := lt_of_lt_of_le (sub_pos.mpr ha) (le_max_right _ _)
  have hSa : delta D a ≤ total D := Finset.single_le_sum (fun i _ => hdelta D i) (Finset.mem_univ a)
  have hS : 0 < total D := hda.trans_le hSa
  have hpositive (i : Fin m) (hi : 0 < D.val i) : 0 < score D.val i - mean := by
    have hd : 0 < delta D i := by rw [hfix]; exact mul_pos hi hS
    exact (lt_max_iff.mp hd).resolve_left (lt_irrefl (0 : ℝ))
  have hterms : ∀ i : Fin m, 0 ≤ D.val i * (score D.val i - mean) := by
    intro i
    by_cases hi : D.val i = 0
    · simp [hi]
    · exact (mul_pos (lt_of_le_of_ne (D.property.1 i) (Ne.symm hi))
        (hpositive i (lt_of_le_of_ne (D.property.1 i) (Ne.symm hi)))).le
  have hDa : 0 < D.val a := by
    by_contra! hn
    have hzero : D.val a = 0 := le_antisymm hn (D.property.1 a)
    rw [hfix, hzero, zero_mul] at hda
    exact (lt_irrefl 0) hda
  have hsumPos : 0 < ∑ i, D.val i * (score D.val i - mean) :=
    Finset.sum_pos' (fun i _ => hterms i) ⟨a, Finset.mem_univ a, mul_pos hDa (sub_pos.mpr ha)⟩
  have hzero : (∑ i, D.val i * (score D.val i - mean)) = 0 := by
    rw [show (∑ i, D.val i * (score D.val i - mean)) =
        expectation D.val (score D.val) - (∑ i, D.val i) * mean by
      simp only [expectation, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]]
    rw [hpartition D.val D.property, D.property.2]
    ring
  rw [hzero] at hsumPos
  exact (lt_irrefl 0) hsumPos

end OptimalG
end

-- Source module OptimalG.ScoreDerivative
section
set_option autoImplicit true
/-!
# The actual derivative of candidate activation

For positive candidate mass, the rank-interval average is the quotient of two
primitive values by the candidate mass. Its strict Fréchet derivative is proved
from the fundamental theorem of calculus. This supplies the analytic map used
in the equal-voter realization argument.
-/

namespace OptimalG
open Set MeasureTheory
open scoped BigOperators Topology

/-- The linear map giving the lottery mass below a candidate in a fixed order. -/
noncomputable def rankPrefixLinear {m : ℕ} (order : Equiv.Perm (Fin m)) (a : Fin m) :
    (Fin m → ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin m, if i.val < (order.symm a).val then ContinuousLinearMap.proj (order i) else 0

theorem rankPrefixLinear_apply {m : ℕ} (order : Equiv.Perm (Fin m))
    (a : Fin m) (D : Fin m → ℝ) :
    rankPrefixLinear order a D = rankCut (fun i => D (order i)) (order.symm a).val := by
  simp only [rankPrefixLinear, sum_apply, rankCut]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> rfl

noncomputable def activationPrimitive (g : ℝ → ℝ) (r : ℝ) : ℝ := ∫ x in (0 : ℝ)..r, g x

/-- A globally defined smooth extension of the positive-mass interval average. -/
noncomputable def scoreExtension {m : ℕ} (g : ℝ → ℝ) (order : Equiv.Perm (Fin m))
    (a : Fin m) (D : Fin m → ℝ) : ℝ :=
  (activationPrimitive g (rankPrefixLinear order a D + D a) -
    activationPrimitive g (rankPrefixLinear order a D)) / D a

/-- At positive masses the extension equals the actual activation definition. -/
theorem scoreExtension_eq_orderedActivation {m : ℕ} (g : ℝ → ℝ)
    (hg : Continuous g) (order : Equiv.Perm (Fin m)) (a : Fin m)
    (D : Fin m → ℝ) (hDa : D a ≠ 0) :
    scoreExtension g order a D = orderedActivation g D order a := by
  have hint := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hg.intervalIntegrable 0 (rankPrefixLinear order a D))
    (hg.intervalIntegrable (rankPrefixLinear order a D) (rankPrefixLinear order a D + D a))
  have hmass := mass_mul_rankActivation g (fun i => D (order i)) (order.symm a)
  rw [rankCut_succ] at hmass
  simp only [Equiv.apply_symm_apply] at hmass
  rw [← rankPrefixLinear_apply] at hmass
  unfold scoreExtension activationPrimitive orderedActivation
  apply (div_eq_iff hDa).mpr
  linarith

/-- Explicit derivative, written in the product-rule form. -/
noncomputable def scoreDerivative {m : ℕ} (g : ℝ → ℝ) (order : Equiv.Perm (Fin m))
    (a : Fin m) (D : Fin m → ℝ) : (Fin m → ℝ) →L[ℝ] ℝ :=
  let L := rankPrefixLinear order a
  let P : (Fin m → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj a
  (activationPrimitive g (L D + D a) - activationPrimitive g (L D)) •
      (-(D a ^ 2)⁻¹ • P) +
    (D a)⁻¹ • (g (L D + D a) • (L + P) - g (L D) • L)

theorem scoreExtension_hasStrictFDerivAt {m : ℕ} (g : ℝ → ℝ)
    (hg : Continuous g) (order : Equiv.Perm (Fin m)) (a : Fin m)
    (D : Fin m → ℝ) (hDa : D a ≠ 0) :
    HasStrictFDerivAt (scoreExtension g order a) (scoreDerivative g order a D) D := by
  let L := rankPrefixLinear order a
  let P : (Fin m → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj a
  have hL := L.hasStrictFDerivAt (x := D)
  have hP := P.hasStrictFDerivAt (x := D)
  have hright := (hg.integral_hasStrictDerivAt 0 (L D + D a)).comp_hasStrictFDerivAt D (hL.add hP)
  have hleft := (hg.integral_hasStrictDerivAt 0 (L D)).comp_hasStrictFDerivAt D hL
  have hinv := (hasStrictDerivAt_inv hDa).comp_hasStrictFDerivAt D hP
  convert! (hright.sub hleft).mul hinv using 1

/-- The pointwise differential formula used to calculate the auxiliary profile. -/
theorem scoreDerivative_apply {m : ℕ} (g : ℝ → ℝ) (order : Equiv.Perm (Fin m))
    (a : Fin m) (D h : Fin m → ℝ) (hDa : D a ≠ 0) :
    scoreDerivative g order a D h =
      (g (rankPrefixLinear order a D + D a) * (rankPrefixLinear order a h + h a) -
       g (rankPrefixLinear order a D) * rankPrefixLinear order a h -
       scoreExtension g order a D * h a) / D a := by
  simp only [scoreDerivative, scoreExtension, add_apply,
    sub_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  field_simp
  ring

/-- Extend an activation continuously by its endpoint values. -/
noncomputable def clippedActivation (g : ℝ → ℝ) (r : ℝ) : ℝ := g (max 0 (min 1 r))

theorem clippedActivation_eq (g : ℝ → ℝ) (r : ℝ) (hr : r ∈ Icc 0 1) :
    clippedActivation g r = g r := by
  simp [clippedActivation, min_eq_right hr.2, max_eq_right hr.1]

theorem clippedActivation_continuous (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 1)) :
    Continuous (clippedActivation g) := by
  apply continuousOn_univ.mp
  exact hg.comp ((continuous_const.max (continuous_const.min continuous_id)).continuousOn)
    (fun r _ => ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩)

/-- Clipping leaves every lottery rank-interval activation unchanged. -/
theorem rankActivation_clipped {m : ℕ} (g : ℝ → ℝ) (D : Fin m → ℝ)
    (hD : ∀ a, 0 ≤ D a) (hsum : ∑ a, D a = 1) (a : Fin m) :
    rankActivation (clippedActivation g) D a = rankActivation g D a := by
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hu
  apply clippedActivation_eq
  have hleft := rankCut_mem_Icc D hD hsum a.val
  have hright := rankCut_mem_Icc D hD hsum (a.val + 1)
  rw [rankCut_succ] at hright
  constructor
  · exact add_nonneg hleft.1 (mul_nonneg hu.1 (hD a))
  · have hmul := mul_le_of_le_one_left (hD a) hu.2
    linarith [hright.2]

theorem orderedActivation_clipped {m : ℕ} (g : ℝ → ℝ) (D : Fin m → ℝ)
    (hD : ∀ a, 0 ≤ D a) (hsum : ∑ a, D a = 1)
    (order : Equiv.Perm (Fin m)) (a : Fin m) :
    orderedActivation (clippedActivation g) D order a = orderedActivation g D order a := by
  apply rankActivation_clipped g (fun i => D (order i)) (fun i => hD (order i))
  simpa only [Equiv.sum_comp] using hsum

/-- Positive-mass actual scores are represented by the globally differentiable
extension, even when g was only assumed continuous on the rank interval. -/
theorem clipped_scoreExtension_eq_orderedActivation {m : ℕ} (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc 0 1)) (order : Equiv.Perm (Fin m)) (a : Fin m)
    (D : Fin m → ℝ) (hD : ∀ a, 0 ≤ D a) (hsum : ∑ a, D a = 1) (hDa : D a ≠ 0) :
    scoreExtension (clippedActivation g) order a D = orderedActivation g D order a := by
  rw [scoreExtension_eq_orderedActivation _ (clippedActivation_continuous g hg) order a D hDa,
    orderedActivation_clipped g D hD hsum]

/-- The actual finite weighted profile score, extended to a neighborhood in
voter probabilities and positive candidate masses. -/
noncomputable def weightedScoreExtension {V : Type*} [Fintype V] {m : ℕ}
    (g : ℝ → ℝ) (orders : V → Equiv.Perm (Fin m)) (a : Fin m)
    (p : (V → ℝ) × (Fin m → ℝ)) : ℝ :=
  expectation p.1 (fun v => scoreExtension g (orders v) a p.2)

noncomputable def weightedScoreDerivative {V : Type*} [Fintype V] {m : ℕ}
    (g : ℝ → ℝ) (orders : V → Equiv.Perm (Fin m)) (a : Fin m)
    (p : (V → ℝ) × (Fin m → ℝ)) : ((V → ℝ) × (Fin m → ℝ)) →L[ℝ] ℝ :=
  ∑ v, (p.1 v • ((scoreDerivative g (orders v) a p.2).comp (ContinuousLinearMap.snd ℝ _ _)) +
    scoreExtension g (orders v) a p.2 •
      ((ContinuousLinearMap.proj v).comp (ContinuousLinearMap.fst ℝ _ _)))

/-- Strict differentiability in voter weights and candidate masses jointly. -/
theorem weightedScoreExtension_hasStrictFDerivAt {V : Type*} [Fintype V] {m : ℕ}
    (g : ℝ → ℝ) (hg : Continuous g) (orders : V → Equiv.Perm (Fin m)) (a : Fin m)
    (p : (V → ℝ) × (Fin m → ℝ)) (hDa : p.2 a ≠ 0) :
    HasStrictFDerivAt (weightedScoreExtension g orders a) (weightedScoreDerivative g orders a p) p := by
  have hterm (v : V) : HasStrictFDerivAt
      (fun q : (V → ℝ) × (Fin m → ℝ) => q.1 v * scoreExtension g (orders v) a q.2)
      (p.1 v • ((scoreDerivative g (orders v) a p.2).comp (ContinuousLinearMap.snd ℝ _ _)) +
       scoreExtension g (orders v) a p.2 •
         ((ContinuousLinearMap.proj v).comp (ContinuousLinearMap.fst ℝ _ _))) p := by
    have hproj := ((ContinuousLinearMap.proj v).comp (ContinuousLinearMap.fst ℝ (V → ℝ) (Fin m → ℝ))).hasStrictFDerivAt (x := p)
    have hs := (scoreExtension_hasStrictFDerivAt g hg (orders v) a p.2 hDa).comp p
      ((ContinuousLinearMap.snd ℝ (V → ℝ) (Fin m → ℝ)).hasStrictFDerivAt (x := p))
    convert! hproj.mul hs using 1
  exact HasStrictFDerivAt.fun_sum (u := Finset.univ) (fun v _ => hterm v)

theorem weightedScoreExtension_eq {V : Type*} [Fintype V] {m : ℕ}
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 1))
    (orders : V → Equiv.Perm (Fin m)) (a : Fin m) (w : V → ℝ)
    (D : Fin m → ℝ) (hD : ∀ a, 0 ≤ D a) (hsum : ∑ a, D a = 1) (hDa : D a ≠ 0) :
    weightedScoreExtension (clippedActivation g) orders a (w, D) =
      expectation w (fun v => orderedActivation g D (orders v) a) := by
  unfold weightedScoreExtension expectation
  apply Finset.sum_congr rfl
  intro v _
  change w v * scoreExtension (clippedActivation g) (orders v) a D = _
  rw [clipped_scoreExtension_eq_orderedActivation g hg (orders v) a D hD hsum hDa]

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

-- Source module OptimalG.ClippedElection
section
set_option autoImplicit true
/-! # Continuous clipping preserves the actual election problem exactly -/

namespace OptimalG
open Set MeasureTheory

theorem clippedActivation_mean (g : ℝ → ℝ) :
    (∫ r in (0 : ℝ)..1, clippedActivation g r) = ∫ r in (0 : ℝ)..1, g r := by
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hr
  exact clippedActivation_eq g r hr

theorem Election.activation_clipped (E : Election) (g : ℝ → ℝ)
    (D : Lottery E.candidateCount) (v : E.Voter) (a : E.Candidate) :
    E.activation (clippedActivation g) D v a = E.activation g D v a :=
  orderedActivation_clipped g D.weight D.nonneg D.total (E.order v) a

theorem Election.stable_clipped_iff (E : Election) (g : ℝ → ℝ)
    (D : Lottery E.candidateCount) : E.Stable (clippedActivation g) D ↔ E.Stable g D := by
  simp only [Election.Stable, Election.activation_clipped, clippedActivation_mean]

theorem witnessAbove_clipped_iff (g : ℝ → ℝ) (K : ℝ) :
    WitnessAbove (clippedActivation g) K ↔ WitnessAbove g K := by
  simp only [WitnessAbove, Election.stable_clipped_iff]

theorem universalBound_clipped_iff (g : ℝ → ℝ) (K : ℝ) :
    UniversalBound (clippedActivation g) K ↔ UniversalBound g K := by
  simp only [UniversalBound, Election.stable_clipped_iff]

end OptimalG
end

-- Source module OptimalG.StableExistence
section
set_option autoImplicit true
/-! # Every finite election admits a stable lottery

Continuity at zero candidate mass follows directly from the averaged rank
integral. Thus the fixed-point construction applies on the entire closed
simplex, including its boundary.
-/

namespace OptimalG
open Set MeasureTheory
open scoped BigOperators

/-- Actual activation, including at zero mass, is continuous in all masses. -/
theorem orderedActivation_continuous {m : ℕ} (g : ℝ → ℝ) (hg : Continuous g)
    (order : Equiv.Perm (Fin m)) (a : Fin m) :
    Continuous (fun D : Fin m → ℝ => orderedActivation g D order a) := by
  have harg : Continuous (fun q : (Fin m → ℝ) × ℝ =>
      rankPrefixLinear order a q.1 + q.2 * q.1 a) :=
    ((rankPrefixLinear order a).continuous.comp continuous_fst).add
      (continuous_snd.mul ((continuous_apply a).comp continuous_fst))
  have hint := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (f := fun (D : Fin m → ℝ) u => g (rankPrefixLinear order a D + u * D a))
    (hg.comp harg) 0 1
  simpa only [orderedActivation, rankActivation, rankPrefixLinear_apply,
    Equiv.apply_symm_apply] using hint

/-- Existence requires only continuity on the rank interval; no differentiability,
strict monotonicity, or positive-mass hypothesis is imposed. -/
theorem Election.exists_stable (E : Election) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc 0 1)) :
    ∃ D : Lottery E.candidateCount, E.Stable g D := by
  let gc := clippedActivation g
  have hgc : Continuous gc := clippedActivation_continuous g hg
  let score := fun (D : E.Candidate → ℝ) a =>
    expectation E.voterWeight (fun v => orderedActivation gc D (E.order v) a)
  have hcont (a : E.Candidate) : Continuous (fun D => score D a) := by
    change Continuous (fun D => ∑ v, E.voterWeight v * orderedActivation gc D (E.order v) a)
    exact continuous_finsetSum _ (fun v _ => continuous_const.mul
      (orderedActivation_continuous gc hgc (E.order v) a))
  have hpartition (D : E.Candidate → ℝ) (hD : D ∈ stdSimplex ℝ E.Candidate) :
      expectation D (score D) = ∫ r in (0 : ℝ)..1, gc r := by
    dsimp only [score]
    rw [expectation_commute]
    simp_rw [ordered_integral_partition gc D _ hgc.continuousOn hD.1 hD.2]
    exact expectation_const E.voterWeight_total _
  obtain ⟨D, hD, hscore⟩ := exists_simplex_score_bound score (∫ r in (0 : ℝ)..1, gc r)
    (fun a => (hcont a).continuousOn) hpartition
  let lottery : Lottery E.candidateCount := ⟨D, hD.1, hD.2⟩
  refine ⟨lottery, (E.stable_clipped_iff g lottery).mp ?_⟩
  exact hscore

end OptimalG
end

-- Source module Stability
section
set_option autoImplicit true
/-! The minimax definition in the submission and the pointwise bound used in the supplement. -/
namespace StableVotingDistortion
open PctDistortion
open scoped BigOperators

variable {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C]

private theorem stableWitness (g : ℝ → ℝ) (hg : IsActivation g) (E : Election V C) :
    ∃ Q ∈ stdSimplex ℝ C, ∀ a, voterMean (fun v => activation g E Q v a) ≤
      ∫ r in (0 : ℝ)..1, g r := by
  classical
  let vlabel := (Fintype.equivFin V).symm
  let clabel := Fintype.equivFin C
  choose ballot hballot using exists_ballot E
  let election : OptimalG.Election := {
    voterCount := Fintype.card V, candidateCount := Fintype.card C,
    voters_pos := Fintype.card_pos, candidates_pos := Fintype.card_pos,
    order := fun i => (ballot (vlabel i)).trans clabel }
  obtain ⟨L, hL⟩ := election.exists_stable g hg.continuousOn
  let Q := fun a => L.weight (clabel a)
  have hQ : Q ∈ stdSimplex ℝ C := ⟨fun a => L.nonneg _, (clabel.sum_comp L.weight).trans L.total⟩
  refine ⟨Q, hQ, fun a => ?_⟩
  specialize hL (clabel a)
  have hid (i : Fin (Fintype.card V)) : activation g E Q (vlabel i) a =
      election.activation g L i (clabel a) := by
    rw [activation_eq_ordered E Q _ (ballot _) (hballot _) g a]
    simp [OptimalG.Election.activation, OptimalG.orderedActivation, election, Q]
  calc
    voterMean (fun v => activation g E Q v a) = (Fintype.card V : ℝ)⁻¹ *
        ∑ i, activation g E Q (vlabel i) a := by
      unfold voterMean
      rw [vlabel.sum_comp (fun v => activation g E Q v a)]
    _ = OptimalG.expectation election.voterWeight (fun i => election.activation g L i (clabel a)) := by
      simp only [OptimalG.expectation, OptimalG.Election.voterWeight, one_div,
        hid, Finset.mul_sum, election]
    _ ≤ _ := hL

/-- Theorem 4 in its public mission formulation. -/
theorem theorem_4 {g : ℝ → ℝ} (hg : IsActivation g) (E : Election V C)
    {D : C → ℝ} (hD : IsGStable g E D) (a : C) :
    voterMean (fun v => activation g E D v a) ≤ ∫ t in (0 : ℝ)..1, g t := by
  classical
  obtain ⟨Q, hQ, hbound⟩ := stableWitness g hg E
  exact (Finset.le_sup' (fun a => voterMean (fun v => activation g E D v a))
    (Finset.mem_univ a)).trans ((hD.2 Q hQ).trans (Finset.sup'_le _ _ (fun a _ => hbound a)))


end StableVotingDistortion
end

open PctDistortion
open StableVotingDistortion

theorem solution :
    ∀ {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] {g : ℝ → ℝ}
    (hg : IsActivation g) (E : Election V C) {D : C → ℝ} (hD : IsGStable g E D) (a : C),
    voterMean (fun v => activation g E D v a) ≤ ∫ t in (0 : ℝ)..1, g t :=
  @StableVotingDistortion.theorem_4
