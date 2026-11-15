-- Prove2me | solution 1 for StableVotingDistortion.eq_33
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T12:06:08.99259+00:00
-- url     : https://prove2.me/submissions/a38c3774-ea6b-47e5-8ff5-1e20190ede16

import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_IsGStable
import Definitions.Def_StableVotingDistortion_IsScoreFunction
import Definitions.Def_StableVotingDistortion_offset
import Definitions.Def_StableVotingDistortion_scorePrimitives
import Definitions.Def_StableVotingDistortion_slices
import Definitions.Def_StableVotingDistortion_voterMean
import Mathlib
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Basic
import Theorems.Thm_StableVotingDistortion_eq_30_31

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

-- Source module SliceOffset
section
set_option autoImplicit true
namespace StableVotingDistortion
open PctDistortion

theorem eq_33 {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C)
    {lam : ℝ} {ϕ β : ℝ → ℝ} {c : ℝ → ℝ → ℝ} (hϕ : IsScoreFunction lam ϕ)
    {D ρ : C → ℝ} (hD : IsGStable (gPhi ϕ) E D) (hρ : ∀ b, 0 ≤ ρ b) {aStar : C} (hstar : ρ aStar = 0)
    {t : ℝ} (ht : 0 ≤ t) (hA : 0 < Aval lam ϕ E D aStar)
    (hpt : pt D ρ t ∈ Set.Ioo (0 : ℝ) 1)
    (hβ : ∀ p ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ β p)
    (hc : ∀ p ∈ Set.Ioo (0 : ℝ) 1, ∀ x ∈ Set.Ico 0 lam, 0 ≤ c p x) :
    voterMean (fun v => qv E D ρ v t) ≤ voterMean (fun v => qTilde lam ϕ β c E D ρ aStar v t) := by
  classical
  let w := fun _ : V => (Fintype.card V : ℝ)⁻¹
  let s := sv E D aStar
  let p := pt D ρ t
  let low := fun v => s v < lam
  let τ := fun v => ϕ (s v)
  let κ := fun v => c p (s v)
  have hm (f : V → ℝ) : OptimalG.expectation w f = voterMean f := by
    simp [w,OptimalG.expectation,voterMean,Finset.mul_sum]
  have hs := eq_30_31 E hϕ hD
  have hκ (v : V) (hv : low v) : 0 ≤ κ v := by
    exact hc _ hpt _ ⟨Finset.sum_nonneg (fun b _ => hD.1.1 b),hv⟩
  have hAval : OptimalG.lowExpectation w low τ = Aval lam ϕ E D aStar := by
    unfold OptimalG.lowExpectation Aval; exact hm _
  have hB : OptimalG.lowExpectation w low κ / OptimalG.lowExpectation w low τ =
      cbar lam ϕ c E D aStar p := by
    unfold cbar; rw [hAval]; rw [OptimalG.lowExpectation,hm]
  have h := OptimalG.expected_slice_le_offset w low τ κ (fun v => qv E D ρ v t)
    (fun v => kv E D ρ ϕ v t) (β p) (fun v => by dsimp [w]; positivity) hκ
    (hAval.trans_gt hA) (by rw [hm]; exact hs.2 aStar) (by rw [hm]; exact hs.1 (St ρ t))
  simp only [hm,OptimalG.sliceCorrection,hB] at h
  exact h

end StableVotingDistortion
end

open PctDistortion
open StableVotingDistortion

theorem solution :
    ∀ {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C)
    {lam : ℝ} {ϕ β : ℝ → ℝ} {c : ℝ → ℝ → ℝ} (hϕ : IsScoreFunction lam ϕ)
    {D ρ : C → ℝ} (hD : IsGStable (gPhi ϕ) E D) (hρ : ∀ b, 0 ≤ ρ b) {aStar : C} (hstar : ρ aStar = 0)
    {t : ℝ} (ht : 0 ≤ t) (hA : 0 < Aval lam ϕ E D aStar)
    (hpt : pt D ρ t ∈ Set.Ioo (0 : ℝ) 1)
    (hβ : ∀ p ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ β p)
    (hc : ∀ p ∈ Set.Ioo (0 : ℝ) 1, ∀ x ∈ Set.Ico 0 lam, 0 ≤ c p x),
    voterMean (fun v => qv E D ρ v t) ≤ voterMean (fun v => qTilde lam ϕ β c E D ρ aStar v t) :=
  @StableVotingDistortion.eq_33
