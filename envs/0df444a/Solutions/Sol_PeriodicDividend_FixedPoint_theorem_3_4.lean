-- Prove2me | solution 1 for PeriodicDividend.FixedPoint.theorem_3_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T13:46:46.207986+00:00
-- url     : https://prove2.me/submissions/3120422a-15c3-417a-80a8-f844060aa91a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PeriodicDividend_FixedPoint_Model
import Theorems.Thm_PeriodicDividend_FixedPoint_theorem_3_3_LT
import Theorems.Thm_PeriodicDividend_FixedPoint_theorem_3_4_verification

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace PDSol34
open PeriodicDividend.FixedPoint

lemma Iop_bdd (p : Params) (hS : p.Standing) (ψ : ℝ≥0 → ℝ) (A : ℝ)
    (hb : ∀ y, ψ y ≤ (y : ℝ) + A) (x : ℝ≥0) :
    BddAbove {y : ℝ | ∃ z : ℝ≥0, 0 < z ∧ y = ψ (x + z) - issueCost p z} := by
  obtain ⟨_, _, _, hF, hP, _⟩ := hS
  refine ⟨(x : ℝ) + A, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  have h1 := hb (x + z)
  have hz' : (0 : ℝ) < z := hz
  simp only [issueCost, hz', if_true]
  push_cast at h1
  nlinarith

lemma Iop_nonempty (p : Params) (ψ : ℝ≥0 → ℝ) (x : ℝ≥0) :
    ({y : ℝ | ∃ z : ℝ≥0, 0 < z ∧ y = ψ (x + z) - issueCost p z}).Nonempty :=
  ⟨_, 1, one_pos, rfl⟩

lemma le_Iop (p : Params) (hS : p.Standing) (ψ : ℝ≥0 → ℝ) (A : ℝ)
    (hb : ∀ y, ψ y ≤ (y : ℝ) + A) (x z : ℝ≥0) (hz : 0 < z) :
    ψ (x + z) - issueCost p z ≤ Iop p ψ x :=
  le_csSup (Iop_bdd p hS ψ A hb x) ⟨z, hz, rfl⟩

lemma Astar_nonneg (p : Params) (hS : p.Standing) : 0 ≤ Astar p := by
  obtain ⟨hρ, hμ, _, _, _, hT⟩ := hS
  unfold Astar
  apply div_nonneg (mul_pos hμ hT).le
  have : 1 < Real.exp (p.rho * p.T) := Real.one_lt_exp_iff.mpr (mul_pos hρ hT)
  linarith

/-- The identity function lies in `C_A` for every `A ≥ 0`. -/
lemma CA_id (p : Params) (hS : p.Standing) (A : ℝ) (hA : 0 ≤ A) :
    CA p A (fun x => (x : ℝ)) := by
  obtain ⟨_, _, _, hF, hP, _⟩ := hS
  have hI : ∀ x : ℝ≥0, Iop p (fun x => (x : ℝ)) x ≤ x := by
    intro x
    apply csSup_le (Iop_nonempty p _ x)
    rintro w ⟨z, hz, rfl⟩
    have hz' : (0 : ℝ) < z := hz
    simp only [issueCost, hz', if_true]
    push_cast
    nlinarith
  refine ⟨⟨NNReal.continuous_coe, fun a b h => h, fun x => ⟨x.2, max_le (hI x) x.2, by linarith⟩,
    ?_⟩, ?_, fun x => by simpa using hA⟩
  · apply le_antisymm
    · simp
    · exact max_le (by simpa using hI 0) (by simp)
  · intro a b _; simp

/-- `C_A` is closed under uniform limits. -/
lemma CA_of_uniform (p : Params) (hS : p.Standing) (A : ℝ) (f : ℕ → ℝ≥0 → ℝ)
    (hf : ∀ n, CA p A (f n)) (Φ : ℝ≥0 → ℝ) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hu : ∀ n x, |Φ x - f n x| ≤ ε n) : CA p A Φ := by
  have hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (Φ x)) := by
    intro x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hε
    rw [Real.norm_eq_abs, abs_sub_comm]; exact hu n x
  have hb : ∀ n y, f n y ≤ (y : ℝ) + A := fun n y => ((hf n).1.2.2.1 y).2.2
  have hΦb : ∀ y, Φ y ≤ (y : ℝ) + A := fun y =>
    le_of_tendsto' (hlim y) (fun n => hb n y)
  -- continuity via uniform convergence
  have hcont : Continuous Φ := by
    have hU : TendstoUniformly f Φ atTop := by
      rw [Metric.tendstoUniformly_iff]
      intro δ hδ
      filter_upwards [(tendsto_order.1 hε).2 δ hδ] with n hn x
      rw [Real.dist_eq]
      exact lt_of_le_of_lt (hu n x) hn
    exact hU.continuous (Eventually.of_forall fun n => (hf n).1.1).frequently
  have hmono : Monotone Φ := fun a b h =>
    le_of_tendsto_of_tendsto' (hlim a) (hlim b) (fun n => (hf n).1.2.1 h)
  have hmonoM : Monotone (fun x => Φ x - (x : ℝ)) := fun a b h =>
    le_of_tendsto_of_tendsto' ((hlim a).sub_const _) ((hlim b).sub_const _)
      (fun n => (hf n).2.1 h)
  have hnn : ∀ x, 0 ≤ Φ x := fun x => ge_of_tendsto' (hlim x) (fun n => ((hf n).1.2.2.1 x).1)
  have habs : ∀ x, |Φ x - (x : ℝ)| ≤ A := fun x => by
    have := ((hlim x).sub_const (x : ℝ)).abs
    exact le_of_tendsto' this (fun n => (hf n).2.2 x)
  have hI : ∀ x, Iop p Φ x ≤ Φ x := by
    intro x
    apply csSup_le (Iop_nonempty p Φ x)
    rintro w ⟨z, hz, rfl⟩
    apply le_of_tendsto_of_tendsto' ((hlim (x + z)).sub_const _) (hlim x)
    intro n
    have h1 := le_Iop p hS (f n) A (hb n) x z hz
    have h2 := le_trans (le_max_left _ _) ((hf n).1.2.2.1 x).2.1
    linarith
  refine ⟨⟨hcont, hmono, fun x => ⟨hnn x, max_le (hI x) (hnn x), hΦb x⟩, ?_⟩, hmonoM, habs⟩
  apply le_antisymm _ (max_le (hI 0) (hnn 0))
  -- Φ 0 ≤ max (Iop Φ 0) 0
  have hstep : ∀ n, f n 0 ≤ max (Iop p Φ 0) 0 + ε n := by
    intro n
    have hεn : 0 ≤ ε n := le_trans (abs_nonneg _) (hu n 0)
    rw [(hf n).1.2.2.2]
    apply max_le
    · have : Iop p (f n) 0 ≤ Iop p Φ 0 + ε n := by
        apply csSup_le (Iop_nonempty p (f n) 0)
        rintro w ⟨z, hz, rfl⟩
        have h1 := le_Iop p hS Φ A hΦb 0 z hz
        have h2 := hu n (0 + z)
        rw [abs_le] at h2
        linarith
      linarith [le_max_left (Iop p Φ 0) 0]
    · linarith [le_max_right (Iop p Φ 0) 0]
  have := le_of_tendsto_of_tendsto' (hlim 0) (tendsto_const_nhds.add hε) hstep
  simpa using this

end PDSol34

open PDSol34 in
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ mΩ) (C : ℝ → Ω → ℝ) (p : PeriodicDividend.FixedPoint.Params)
    (hS : p.Standing)
    (hU : PeriodicDividend.FixedPoint.UsualConditions P 𝔽)
    (hC : AtaBarjesteh23.Workload.IsDriftBM 𝔽 P C p.mu p.sigma) :
    ∃ Φ : ℝ≥0 → ℝ,
      (∀ x : ℝ≥0, PeriodicDividend.FixedPoint.valueFn P 𝔽 C p x = ((Φ x : ℝ) : EReal)) ∧
      PeriodicDividend.FixedPoint.CA p (PeriodicDividend.FixedPoint.Astar p) Φ ∧
      PeriodicDividend.FixedPoint.Top P 𝔽 C p Φ = Φ ∧
      ∀ ψ : ℝ≥0 → ℝ, PeriodicDividend.FixedPoint.CA p (PeriodicDividend.FixedPoint.Astar p) ψ →
        PeriodicDividend.FixedPoint.Top P 𝔽 C p ψ = ψ → ψ = Φ := by
  open PeriodicDividend.FixedPoint in
  set A := Astar p with hAdef
  have hA0 : 0 ≤ A := Astar_nonneg p hS
  obtain ⟨hself, hcontr⟩ := theorem_3_3_LT P 𝔽 C p hS hU hC A le_rfl
  set T := Top P 𝔽 C p with hTdef
  set q := Real.exp (-p.rho * p.T) with hqdef
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    obtain ⟨hρ, _, _, _, _, hT⟩ := hS
    have : -p.rho * p.T < 0 := by nlinarith [mul_pos hρ hT]
    simpa [hqdef] using Real.exp_lt_exp.mpr this
  -- iteration
  let f : ℕ → ℝ≥0 → ℝ := fun n => T^[n] (fun x => (x : ℝ))
  have hfs : ∀ n, f (n + 1) = T (f n) := fun n => Function.iterate_succ_apply' _ _ _
  have hf : ∀ n, CA p A (f n) := by
    intro n
    induction n with
    | zero => exact CA_id p hS A hA0
    | succ n ih => rw [hfs]; exact (hself _ ih).2
  have hstep : ∀ n x, |f (n + 1) x - f n x| ≤ 2 * A * q ^ n := by
    intro n
    induction n with
    | zero =>
      intro x
      have h1 := (hf 1).2.2 x
      have h0 := (hf 0).2.2 x
      simp only [pow_zero, mul_one]
      calc |f (0 + 1) x - f 0 x| = |(f 1 x - x) - (f 0 x - x)| := by ring_nf
        _ ≤ |f 1 x - x| + |f 0 x - x| := abs_sub _ _
        _ ≤ 2 * A := by linarith
    | succ n ih =>
      intro x
      have := hcontr (f (n + 1)) (f n) (2 * A * q ^ n) (hf _) (hf _) ih x
      have e1 := congrFun (hfs (n + 1)) x
      have e2 := congrFun (hfs n) x
      rw [e1, e2]
      calc |T (f (n + 1)) x - T (f n) x| ≤ q * (2 * A * q ^ n) := this
        _ = 2 * A * q ^ (n + 1) := by ring
  have hcauchy : ∀ x, CauchySeq (fun n => f n x) := fun x =>
    cauchySeq_of_le_geometric q (2 * A) hq1 (fun n => by
      rw [Real.dist_eq, abs_sub_comm]; exact hstep n x)
  choose Φ hΦ using fun x => cauchySeq_tendsto_of_complete (hcauchy x)
  have hdist : ∀ n x, |Φ x - f n x| ≤ 2 * A * q ^ n / (1 - q) := by
    intro n x
    have := dist_le_of_le_geometric_of_tendsto q (2 * A) hq1 (fun n => by
      rw [Real.dist_eq, abs_sub_comm]; exact hstep n x) (hΦ x) n
    rw [Real.dist_eq, abs_sub_comm] at this
    exact this
  have hεlim : Tendsto (fun n : ℕ => 2 * A * q ^ n / (1 - q)) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (2 * A)
    have := this.div_const (1 - q)
    simpa using this
  have hΦCA : CA p A Φ := CA_of_uniform p hS A f hf Φ _ hεlim hdist
  -- Φ is a fixed point
  have hfixΦ : T Φ = Φ := by
    funext x
    have h1 : Tendsto (fun n => f (n + 1) x) atTop (𝓝 (Φ x)) :=
      (hΦ x).comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n => f (n + 1) x) atTop (𝓝 (T Φ x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hb : ∀ n, ‖f (n + 1) x - T Φ x‖ ≤ q * (2 * A * q ^ n / (1 - q)) := by
        intro n
        rw [hfs n, Real.norm_eq_abs, abs_sub_comm]
        exact hcontr Φ (f n) _ hΦCA (hf n) (hdist n) x
      refine squeeze_zero (fun n => norm_nonneg _) hb ?_
      simpa using hεlim.const_mul q
    exact tendsto_nhds_unique h2 h1
  have hV := theorem_3_4_verification P 𝔽 C p hS hU hC Φ hΦCA hfixΦ
  refine ⟨Φ, hV, hΦCA, hfixΦ, fun ψ hψ hψfix => ?_⟩
  have hVψ := theorem_3_4_verification P 𝔽 C p hS hU hC ψ hψ hψfix
  funext x
  have := (hVψ x).symm.trans (hV x)
  exact_mod_cast this
