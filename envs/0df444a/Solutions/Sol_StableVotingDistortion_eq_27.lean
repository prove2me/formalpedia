-- Prove2me | solution 1 for StableVotingDistortion.eq_27
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T12:00:17.260889+00:00
-- url     : https://prove2.me/submissions/d6d7e5b6-fde5-41e6-8ea2-04131cdf53c8

import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_activation
import Definitions.Def_StableVotingDistortion_rhoV
import Definitions.Def_StableVotingDistortion_slices
import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
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

-- Source module SliceGeometry
section
set_option autoImplicit true
namespace StableVotingDistortion
open PctDistortion Set MeasureTheory

variable {V C : Type} [Fintype C] [Nonempty C]

private theorem rankEnd_le {E : Election V C} {D : C → ℝ} (hD : ∀ b, 0 ≤ D b)
    {v : V} {b c : C} (h : E.prefers v c b) : leftRank E D v b + D b ≤ leftRank E D v c := by
  obtain ⟨e,he⟩ := exists_ballot E v
  let w := fun i => D (e i)
  have hpos : (e.symm b).val < (e.symm c).val := by
    exact (he (e.symm c) (e.symm b)).mp (by simpa using h)
  rw [leftRank_eq_rankCut E D v e he, leftRank_eq_rankCut E D v e he]
  have hh := OptimalG.rankCut_mono w (fun i => hD _) (Nat.succ_le_of_lt hpos)
  rw [OptimalG.rankCut_succ] at hh
  simpa [w] using hh

private theorem rank_mono {E : Election V C} {D : C → ℝ} (hD : ∀ b, 0≤D b)
    {v : V} {b c : C} (h : E.prefers v c b) : leftRank E D v b ≤ leftRank E D v c :=
  (le_add_of_nonneg_right (hD b)).trans (rankEnd_le hD h)

private theorem slice_width_sum (E : Election V C) {D ρ : C → ℝ} (hD : ∀ b,0≤D b)
    (v : V) {a : C} (ha : ρ a=0) {t : ℝ} (ht : 0≤t) :
    qv E D ρ v t = ∑ b, if t < rhoV E ρ v b then D b else 0 := by
  classical
  let bad := Finset.univ.filter (fun c => c ∉ St ρ t)
  have hmem (c : C) : c∈bad ↔ ρ c≤t := by simp [bad,St]
  have hne : bad.Nonempty := ⟨a,(hmem a).2 (ha.trans_le ht)⟩
  obtain ⟨e,he⟩ := exists_ballot E v
  let idx := fun c => (e.symm c).val
  obtain ⟨c,hcb,hmin⟩ := Finset.exists_min_image bad idx hne
  have hρc := (hmem c).1 hcb
  have hrel (b d : C) : idx d < idx b ↔ E.prefers v b d := by
    simpa only [idx,Equiv.apply_symm_apply,Fin.lt_def] using (he (e.symm b) (e.symm d)).symm
  have hk (b : C) : t < rhoV E ρ v b ↔ E.prefers v c b := by
    constructor
    · intro hlt
      have hh (d : C) (hd : d=b ∨ E.prefers v b d) : t < ρ d := by
        apply hlt.trans_le
        exact Finset.inf'_le ρ (Finset.mem_filter.mpr ⟨Finset.mem_univ d,hd⟩)
      by_contra h
      have hi : idx c ≤ idx b := not_lt.mp (fun u => h ((hrel c b).mp u))
      rcases hi.lt_or_eq with lo | eq
      · exact (not_lt_of_ge hρc) (hh c (Or.inr ((hrel b c).mp lo)))
      · have inj : Function.Injective idx := Fin.val_injective.comp e.symm.injective
        exact (not_lt_of_ge hρc) (hh c (Or.inl (inj eq)))
    · intro hp
      unfold rhoV
      apply (Finset.lt_inf'_iff _).mpr
      intro d hd
      have hd := (Finset.mem_filter.mp hd).2
      have hdc : idx d < idx c := by
        rcases hd with rfl | h
        · exact (hrel _ _).mpr hp
        · exact ((hrel _ _).mpr h).trans ((hrel _ _).mpr hp)
      exact lt_of_not_ge fun hn => (not_lt_of_ge (hmin d ((hmem d).2 hn))) hdc
  have hRank : qv E D ρ v t = leftRank E D v c := by
    unfold qv
    rw [dif_pos hne]
    apply le_antisymm (Finset.inf'_le _ hcb)
    apply Finset.le_inf'
    intro d hd
    rcases (hmin d hd).lt_or_eq with lo | eq
    · exact rank_mono hD ((hrel d c).mp lo)
    · have inj : Function.Injective idx := Fin.val_injective.comp e.symm.injective
      rw [inj eq]
  rw [hRank]
  simp only [leftRank, Finset.sum_filter,hk]

theorem eq_27 {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C)
    {D ρ : C → ℝ} (hD : D ∈ stdSimplex ℝ C) (hρ : ∀ c, 0 ≤ ρ c) {aStar : C} (hstar : ρ aStar = 0)
    (v : V) :
    MeasureTheory.IntegrableOn (qv E D ρ v) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi (0 : ℝ), qv E D ρ v t = Lv E D ρ v ∧
      (∀ t, 0 ≤ t → zv E D ρ v (t + Rv E ρ v) ≤ qv E D ρ v t) ∧
      ∀ t, 0 ≤ t → qv E D ρ v t ≤ sv E D aStar v := by
  classical
  let f := fun (b : C) => (Ioo (0:ℝ) (rhoV E ρ v b)).indicator (fun _ => D b)
  have hi (b : C) : Integrable (f b) := (integrable_indicator_iff measurableSet_Ioo).2
    (integrableOn_const (by simp [Real.volume_Ioo]))
  have ha : qv E D ρ v =ᵐ[volume.restrict (Ioi 0)] (fun t => ∑ b, f b t) := by
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi (0:ℝ)) measurableSet_Ioi] with t ht
    rw [slice_width_sum E hD.1 v hstar ht.le]
    simp [f,Set.indicator,Set.mem_Ioo,(show 0<t from ht)]
  have he (b : C) : (∫ t in Ioi (0:ℝ), f b t) = D b * rhoV E ρ v b := by
    have hr : 0 ≤ rhoV E ρ v b := Finset.le_inf' _ _ (fun c _ => hρ c)
    unfold f
    rw [setIntegral_indicator measurableSet_Ioo,inter_eq_right.mpr Ioo_subset_Ioi_self, integral_const]
    simp [measureReal_def, Real.volume_Ioo, hr,smul_eq_mul,mul_comm]
  refine ⟨(integrable_finsetSum _ (fun b _ => (hi b).integrableOn)).congr ha.symm, ?_,?_,?_⟩
  · rw [integral_congr_ae ha,integral_finsetSum _ (fun b _ => (hi b).integrableOn)]
    exact Finset.sum_congr rfl (fun b _ => he b)
  · intro t ht
    have hout (x : ℝ) : aStar∉St ρ x ↔ 0≤x := by simp [St,hstar]
    have hne : (Finset.univ.filter (fun c => c ∉ St ρ t)).Nonempty := ⟨aStar,by simp [(hout t).2 ht]⟩
    unfold zv qv
    rw [dif_pos hne]
    split_ifs with hn
    · apply Finset.sup'_le
      intro b hb
      apply Finset.le_inf'
      intro c hc
      have hb' : t+Rv E ρ v < ρ b := by simpa [St] using (Finset.mem_filter.mp hb).2.1
      have hc' : ρ c ≤ t := by simpa [St] using (Finset.mem_filter.mp hc).2
      apply rankEnd_le hD.1
      by_contra hf
      have hcb : c=b ∨ E.prefers v b c := by
        by_cases hh : E.prefers v b c
        · exact Or.inr hh
        · exact Or.inl ((E.isStrictTotalOrder v).trichotomous b c hh hf).symm
      have hl : rhoV E ρ v b ≤ ρ c := Finset.inf'_le ρ (Finset.mem_filter.mpr ⟨Finset.mem_univ c,hcb⟩)
      have hg := Finset.le_sup' (fun b => ρ b - rhoV E ρ v b) (Finset.mem_univ b)
      change rhoV E ρ v b ≤ ρ c at hl
      change ρ b - rhoV E ρ v b ≤ Rv E ρ v at hg
      linarith
    · apply Finset.le_inf'; intro c _
      exact Finset.sum_nonneg fun b _ => hD.1 b
  · intro t ht
    have ha : aStar ∈ Finset.univ.filter (fun c => c∉ St ρ t) := by simpa [St,hstar] using ht
    unfold qv sv
    rw [dif_pos ⟨aStar,ha⟩]
    exact Finset.inf'_le _ ha

end StableVotingDistortion
end

open PctDistortion
open StableVotingDistortion

theorem solution :
    ∀ {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C)
    {D ρ : C → ℝ} (hD : D ∈ stdSimplex ℝ C) (hρ : ∀ c, 0 ≤ ρ c) {aStar : C} (hstar : ρ aStar = 0)
    (v : V),
    MeasureTheory.IntegrableOn (qv E D ρ v) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi (0 : ℝ), qv E D ρ v t = Lv E D ρ v ∧
      (∀ t, 0 ≤ t → zv E D ρ v (t + Rv E ρ v) ≤ qv E D ρ v t) ∧
      ∀ t, 0 ≤ t → qv E D ρ v t ≤ sv E D aStar v :=
  @StableVotingDistortion.eq_27
