-- Prove2me | solution 1 for TwoSidedMatching.MechBound.lemma_S2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T21:31:09.41561+00:00
-- url     : https://prove2.me/submissions/092368de-ed30-4afe-a197-ead6f1aedf2e

import Mathlib
import Definitions.Def_TwoSidedMatching_MechBound_Mechanism
import Theorems.Thm_TwoSidedMatching_MechBound_lemma_S1

open MeasureTheory MechanismDesign.BilateralTrade

namespace TwoSidedMatching.Guarantee.MBCopy

lemma prim_facts (lo hi : ℝ) (f : ℝ → ℝ) (hlt : lo < hi)
    (hpos : ∀ x ∈ Set.Icc lo hi, 0 < f x)
    (hint : IntervalIntegrable f volume lo hi) :
    ContinuousOn (fun y => ∫ z in lo..y, f z) (Set.Icc lo hi) ∧
    StrictMonoOn (fun y => ∫ z in lo..y, f z) (Set.Icc lo hi) := by
  constructor
  · have := intervalIntegral.continuousOn_primitive_interval' hint (a := lo)
      (Set.left_mem_uIcc)
    rwa [Set.uIcc_of_le hlt.le] at this
  · intro x hx y hy hxy
    have hxi : IntervalIntegrable f volume lo x :=
      hint.mono_set (by
        rw [Set.uIcc_of_le hx.1, Set.uIcc_of_le hlt.le]
        exact Set.Icc_subset_Icc le_rfl hx.2)
    have hyi : IntervalIntegrable f volume lo y :=
      hint.mono_set (by
        rw [Set.uIcc_of_le hy.1, Set.uIcc_of_le hlt.le]
        exact Set.Icc_subset_Icc le_rfl hy.2)
    have hxyi : IntervalIntegrable f volume x y :=
      hint.mono_set (by
        rw [Set.uIcc_of_le hxy.le, Set.uIcc_of_le hlt.le]
        exact Set.Icc_subset_Icc hx.1 hy.2)
    have h1 := intervalIntegral.integral_interval_sub_left hyi hxi
    have h2 : 0 < ∫ z in x..y, f z :=
      intervalIntegral.intervalIntegral_pos_of_pos_on hxyi
        (fun z hz => hpos z ⟨hx.1.trans hz.1.le, hz.2.le.trans hy.2⟩) hxy
    show (∫ z in lo..x, f z) < ∫ z in lo..y, f z
    linarith

open MechanismDesign.BilateralTrade in
lemma cdfB_props (E : Environment) :
    ContinuousOn E.cdfB (Set.Icc E.loB E.hiB) ∧ StrictMonoOn E.cdfB (Set.Icc E.loB E.hiB) ∧
    E.cdfB E.loB = 0 ∧ E.cdfB E.hiB = 1 := by
  obtain ⟨h1, h2⟩ := prim_facts E.loB E.hiB E.fB E.loB_lt_hiB E.fB_pos E.fB_intervalIntegrable
  refine ⟨h1, h2, ?_, E.fB_integral⟩
  show ∫ z in E.loB..E.loB, E.fB z = 0
  simp

open MechanismDesign.BilateralTrade in
lemma cdfS_props (E : Environment) :
    ContinuousOn E.cdfS (Set.Icc E.loS E.hiS) ∧ StrictMonoOn E.cdfS (Set.Icc E.loS E.hiS) ∧
    E.cdfS E.loS = 0 ∧ E.cdfS E.hiS = 1 := by
  obtain ⟨h1, h2⟩ := prim_facts E.loS E.hiS E.fS E.loS_lt_hiS E.fS_pos E.fS_intervalIntegrable
  refine ⟨h1, h2, ?_, E.fS_integral⟩
  show ∫ z in E.loS..E.loS, E.fS z = 0
  simp

open MechanismDesign.BilateralTrade in
lemma psiB_cont (E : Environment) (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB)) :
    ContinuousOn E.psiB (Set.Icc E.loB E.hiB) := by
  obtain ⟨hc, -⟩ := cdfB_props E
  unfold Environment.psiB
  exact continuousOn_id.sub
    ((continuousOn_const.sub hc).div hcontB (fun x hx => (E.fB_pos x hx).ne'))

open MechanismDesign.BilateralTrade in
lemma psiS_cont (E : Environment) (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS)) :
    ContinuousOn E.psiS (Set.Icc E.loS E.hiS) := by
  obtain ⟨hc, -⟩ := cdfS_props E
  unfold Environment.psiS
  exact continuousOn_id.add
    (hc.div hcontS (fun x hx => (E.fS_pos x hx).ne'))




lemma worth_le_sum {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ) (u : M → ℝ) (v : N → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ j, 0 ≤ v j) (huv : ∀ i j, a i j ≤ u i + v j) :
    AssignmentGame.CoreLP.worth a Finset.univ Finset.univ ≤ ∑ i, u i + ∑ j, v j := by
  classical
  unfold AssignmentGame.CoreLP.worth
  apply Finset.sup'_le
  intro P hP
  unfold AssignmentGame.CoreLP.matchings at hP
  rw [Finset.mem_filter] at hP
  obtain ⟨-, -, h1, h2⟩ := hP
  have e1 : ∑ p ∈ P, u p.1 = ∑ i ∈ P.image Prod.fst, u i := by
    rw [Finset.sum_image]
    intro p hp q hq hpq
    exact h1 p hp q hq hpq
  have e2 : ∑ p ∈ P, v p.2 = ∑ j ∈ P.image Prod.snd, v j := by
    rw [Finset.sum_image]
    intro p hp q hq hpq
    exact h2 p hp q hq hpq
  calc ∑ p ∈ P, a p.1 p.2 ≤ ∑ p ∈ P, (u p.1 + v p.2) :=
        Finset.sum_le_sum (fun p _ => huv p.1 p.2)
    _ = ∑ p ∈ P, u p.1 + ∑ p ∈ P, v p.2 := Finset.sum_add_distrib
    _ ≤ ∑ i, u i + ∑ j, v j := by
        rw [e1, e2]
        exact add_le_add
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hu i))
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hv i))

lemma worth_nonneg {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ) :
    0 ≤ AssignmentGame.CoreLP.worth a Finset.univ Finset.univ := by
  classical
  unfold AssignmentGame.CoreLP.worth
  have := Finset.le_sup' (fun P => ∑ p ∈ P, a p.1 p.2)
    (AssignmentGame.CoreLP.empty_mem_matchings (M := M) (N := N) Finset.univ Finset.univ)
  simpa using this

lemma Jbar_le (E : Environment) (b h η : ℝ) (hb : 0 ≤ b) (hh : 0 ≤ h) (ω : Ω) :
    Jbar E b h ω ≤ (∑ i : Fin ω.1.1, max (E.psiB (buyerValue ω i) - η) 0) +
      (∑ j : Fin ω.2.1, max (η - E.psiS (sellerCost ω j)) 0) := by
  unfold Jbar
  have := worth_le_sum (assignmentWeight E b h ω)
    (fun j => max (η - E.psiS (sellerCost ω j)) 0) (fun i => max (E.psiB (buyerValue ω i) - η) 0)
    (fun j => le_max_right _ _) (fun i => le_max_right _ _) (by
      intro j i
      unfold assignmentWeight
      have h1 : 0 ≤ b * max (sellerTime ω j - buyerTime ω i) 0 :=
        mul_nonneg hb (le_max_right _ _)
      have h2 : 0 ≤ h * max (buyerTime ω i - sellerTime ω j) 0 :=
        mul_nonneg hh (le_max_right _ _)
      have h3 := le_max_left (E.psiB (buyerValue ω i) - η) 0
      have h4 := le_max_left (η - E.psiS (sellerCost ω j)) 0
      linarith)
  linarith

lemma Jbar_nonneg (E : Environment) (b h : ℝ) (ω : Ω) : 0 ≤ Jbar E b h ω :=
  worth_nonneg _


section PoissonPart
open ProbabilityTheory
open scoped NNReal Nat


lemma poisson_hasSum_mean (r : ℝ≥0) :
    HasSum (fun n : ℕ => (Real.exp (-r) * (r:ℝ) ^ n / (n)!) * (n:ℝ)) (r:ℝ) := by
  have h1 : HasSum (fun n : ℕ => (r:ℝ) ^ n / (n)!) (Real.exp r) := by
    simpa [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (r : ℝ)
  have h2 := h1.mul_left (Real.exp (-r) * (r:ℝ))
  have hv : Real.exp (-r) * (r:ℝ) * Real.exp r = r := by
    rw [mul_right_comm, ← Real.exp_add]; simp
  rw [hv] at h2
  have e : (fun n : ℕ => (Real.exp (-r) * (r:ℝ) ^ (n+1) / ((n+1)!:ℕ)) * ((n+1:ℕ):ℝ)) =
      fun i : ℕ => Real.exp (-r) * (r:ℝ) * ((r:ℝ) ^ i / (i)!) := by
    funext n
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  have key : HasSum (fun n : ℕ => (Real.exp (-r) * (r:ℝ) ^ (n+1) / ((n+1)!:ℕ)) * ((n+1:ℕ):ℝ)) (r:ℝ) := by
    rw [e]; exact h2
  refine (hasSum_nat_add_iff' 1).1 ?_
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, sub_zero]
  exact key

lemma poisson_hasSum_fact2 (r : ℝ≥0) :
    HasSum (fun n : ℕ => (Real.exp (-r) * (r:ℝ) ^ n / (n)!) * ((n:ℝ) * ((n:ℝ) - 1))) ((r:ℝ)^2) := by
  have h1 : HasSum (fun n : ℕ => (r:ℝ) ^ n / (n)!) (Real.exp r) := by
    simpa [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (r : ℝ)
  have h2 := h1.mul_left (Real.exp (-r) * (r:ℝ)^2)
  have hv : Real.exp (-r) * (r:ℝ)^2 * Real.exp r = (r:ℝ)^2 := by
    rw [mul_right_comm, ← Real.exp_add]; simp
  rw [hv] at h2
  have e : (fun n : ℕ => (Real.exp (-r) * (r:ℝ) ^ (n+2) / ((n+2)!:ℕ)) *
        (((n+2:ℕ):ℝ) * (((n+2:ℕ):ℝ) - 1))) =
      fun i : ℕ => Real.exp (-r) * (r:ℝ)^2 * ((r:ℝ) ^ i / (i)!) := by
    funext n
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  have key : HasSum (fun n : ℕ => (Real.exp (-r) * (r:ℝ) ^ (n+2) / ((n+2)!:ℕ)) *
        (((n+2:ℕ):ℝ) * (((n+2:ℕ):ℝ) - 1))) ((r:ℝ)^2) := by
    rw [e]; exact h2
  refine (hasSum_nat_add_iff' 2).1 ?_
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.cast_zero,
    Nat.cast_one, sub_self, zero_mul, mul_zero, sub_zero, zero_add, zero_sub, mul_neg, mul_one, neg_zero, add_zero]
  exact key

lemma poisson_integrable_id (ρ : ℝ≥0) : Integrable (fun n : ℕ => (n:ℝ)) Po(ρ) := by
  rw [integrable_poissonMeasure_iff]
  refine (poisson_hasSum_mean ρ).summable.congr (fun n => ?_)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg n)]

lemma poisson_integral_id (ρ : ℝ≥0) : ∫ n : ℕ, (n:ℝ) ∂Po(ρ) = ρ := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  exact (poisson_hasSum_mean ρ).tsum_eq

lemma sideLaw_eq (r T : ℝ) (Q : Measure (ℝ × ℝ)) :
    sideLaw r T Q = (Po(⟨max (r * T) 0, le_max_right _ _⟩)).prod
      (Measure.infinitePi (fun _ : ℕ => Q)) := rfl

lemma wald (r T : ℝ) (Q : Measure (ℝ × ℝ)) [IsProbabilityMeasure Q]
    (g : ℝ × ℝ → ℝ) (hg : Measurable g) (hint : Integrable g Q) :
    Integrable (fun x : ℕ × (ℕ → ℝ × ℝ) => ∑ i ∈ Finset.range x.1, g (x.2 i)) (sideLaw r T Q) ∧
    ∫ x : ℕ × (ℕ → ℝ × ℝ), ∑ i ∈ Finset.range x.1, g (x.2 i) ∂(sideLaw r T Q) =
      max (r * T) 0 * ∫ z, g z ∂Q := by
  set ρ : ℝ≥0 := ⟨max (r * T) 0, le_max_right _ _⟩ with hρ
  rw [sideLaw_eq]
  have hev : ∀ i : ℕ, MeasureTheory.MeasurePreserving (fun x : ℕ → ℝ × ℝ => x i)
      (Measure.infinitePi (fun _ : ℕ => Q)) Q := fun i => measurePreserving_eval_infinitePi _ i
  have hxint : ∀ i : ℕ, Integrable (fun x : ℕ → ℝ × ℝ => g (x i))
      (Measure.infinitePi (fun _ : ℕ => Q)) := fun i =>
    (hev i).integrable_comp_of_integrable hint
  have hxint' : ∀ i : ℕ, ∫ x : ℕ → ℝ × ℝ, g (x i) ∂(Measure.infinitePi (fun _ : ℕ => Q)) =
      ∫ z, g z ∂Q := by
    intro i
    have := integral_map (μ := Measure.infinitePi (fun _ : ℕ => Q))
      (hev i).measurable.aemeasurable (f := g) hg.aestronglyMeasurable
    rw [(hev i).map_eq] at this
    exact this.symm
  have hxint'abs : ∀ i : ℕ, ∫ x : ℕ → ℝ × ℝ, ‖g (x i)‖ ∂(Measure.infinitePi (fun _ : ℕ => Q)) =
      ∫ z, ‖g z‖ ∂Q := by
    intro i
    have := integral_map (μ := Measure.infinitePi (fun _ : ℕ => Q))
      (hev i).measurable.aemeasurable (f := fun z => ‖g z‖) hg.norm.aestronglyMeasurable
    rw [(hev i).map_eq] at this
    exact this.symm
  have hmeas : Measurable (fun x : ℕ × (ℕ → ℝ × ℝ) => ∑ i ∈ Finset.range x.1, g (x.2 i)) := by
    apply measurable_from_prod_countable_right
    intro n
    show Measurable fun y : ℕ → ℝ × ℝ => ∑ i ∈ Finset.range n, g (y i)
    exact Finset.measurable_sum (Finset.range n) (fun i _ => hg.comp (measurable_pi_apply i))
  -- fiber facts
  have hfib : ∀ n : ℕ, Integrable (fun x : ℕ → ℝ × ℝ => ∑ i ∈ Finset.range n, g (x i))
      (Measure.infinitePi (fun _ : ℕ => Q)) := fun n => integrable_finsetSum _ (fun i _ => hxint i)
  have hfibv : ∀ n : ℕ, ∫ x : ℕ → ℝ × ℝ, ∑ i ∈ Finset.range n, g (x i)
      ∂(Measure.infinitePi (fun _ : ℕ => Q)) = n * ∫ z, g z ∂Q := by
    intro n
    rw [integral_finsetSum _ (fun i _ => hxint i)]
    simp [hxint']
  have hbound : ∀ n : ℕ, ∫ x : ℕ → ℝ × ℝ, ‖∑ i ∈ Finset.range n, g (x i)‖
      ∂(Measure.infinitePi (fun _ : ℕ => Q)) ≤ n * ∫ z, ‖g z‖ ∂Q := by
    intro n
    calc ∫ x : ℕ → ℝ × ℝ, ‖∑ i ∈ Finset.range n, g (x i)‖ ∂(Measure.infinitePi (fun _ : ℕ => Q))
        ≤ ∫ x : ℕ → ℝ × ℝ, ∑ i ∈ Finset.range n, ‖g (x i)‖ ∂(Measure.infinitePi (fun _ : ℕ => Q)) :=
          integral_mono (hfib n).norm (integrable_finsetSum _ (fun i _ => (hxint i).norm))
            (fun x => norm_sum_le _ _)
      _ = n * ∫ z, ‖g z‖ ∂Q := by
          rw [integral_finsetSum _ (fun i _ => (hxint i).norm)]
          simp only [hxint'abs, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hI : Integrable (fun x : ℕ × (ℕ → ℝ × ℝ) => ∑ i ∈ Finset.range x.1, g (x.2 i))
      (Po(ρ).prod (Measure.infinitePi (fun _ : ℕ => Q))) := by
    refine (integrable_prod_iff hmeas.aestronglyMeasurable).2 ⟨Filter.Eventually.of_forall (fun n => hfib n), ?_⟩
    refine Integrable.mono' ((poisson_integrable_id ρ).mul_const (∫ z, ‖g z‖ ∂Q)) ?_ ?_
    · exact (hmeas.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun n => by
        rw [Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg _))]
        exact hbound n)
  refine ⟨hI, ?_⟩
  rw [integral_prod _ hI]
  simp_rw [hfibv]
  rw [integral_mul_const, poisson_integral_id]
  rfl


end PoissonPart


lemma measurable_primitive (lo : ℝ) (f : ℝ → ℝ) (hf : Measurable f) :
    Measurable (fun y => ∫ z in lo..y, f z) := by
  have key1 : Measurable (fun y : ℝ => ∫ z in Set.Ioc lo y, f z) := by
    have hF : Measurable (fun p : ℝ × ℝ => Set.indicator {q : ℝ × ℝ | lo < q.2 ∧ q.2 ≤ q.1}
        (fun q => f q.2) p) := by
      apply Measurable.indicator
      · exact hf.comp measurable_snd
      · exact (measurableSet_lt measurable_const measurable_snd).inter
          (measurableSet_le measurable_snd measurable_fst)
    have hm : Measurable (fun y : ℝ => ∫ z, Set.indicator {q : ℝ × ℝ | lo < q.2 ∧ q.2 ≤ q.1}
        (fun q => f q.2) (y, z) ∂volume) :=
      (hF.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
    convert hm using 1
    funext y
    symm
    have : (fun z : ℝ => Set.indicator {q : ℝ × ℝ | lo < q.2 ∧ q.2 ≤ q.1}
        (fun q => f q.2) (y, z)) = Set.indicator (Set.Ioc lo y) f := by
      funext z
      by_cases h : lo < z ∧ z ≤ y
      · simp [Set.indicator, h]
      · simp [Set.indicator, h]
    show (∫ z, Set.indicator {q : ℝ × ℝ | lo < q.2 ∧ q.2 ≤ q.1} (fun q => f q.2) (y, z)) = _
    rw [this, integral_indicator measurableSet_Ioc]
  have key2 : Measurable (fun y : ℝ => ∫ z in Set.Ioc y lo, f z) := by
    have hF : Measurable (fun p : ℝ × ℝ => Set.indicator {q : ℝ × ℝ | q.1 < q.2 ∧ q.2 ≤ lo}
        (fun q => f q.2) p) := by
      apply Measurable.indicator
      · exact hf.comp measurable_snd
      · exact (measurableSet_lt measurable_fst measurable_snd).inter
          (measurableSet_le measurable_snd measurable_const)
    have hm : Measurable (fun y : ℝ => ∫ z, Set.indicator {q : ℝ × ℝ | q.1 < q.2 ∧ q.2 ≤ lo}
        (fun q => f q.2) (y, z) ∂volume) :=
      (hF.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
    convert hm using 1
    funext y
    symm
    have : (fun z : ℝ => Set.indicator {q : ℝ × ℝ | q.1 < q.2 ∧ q.2 ≤ lo}
        (fun q => f q.2) (y, z)) = Set.indicator (Set.Ioc y lo) f := by
      funext z
      by_cases h : y < z ∧ z ≤ lo
      · simp [Set.indicator, h]
      · simp [Set.indicator, h]
    show (∫ z, Set.indicator {q : ℝ × ℝ | q.1 < q.2 ∧ q.2 ≤ lo} (fun q => f q.2) (y, z)) = _
    rw [this, integral_indicator measurableSet_Ioc]
  exact key1.sub key2

open MechanismDesign.BilateralTrade in
lemma measurable_psiB (E : Environment) : Measurable E.psiB := by
  have h1 : Measurable E.cdfB := measurable_primitive E.loB E.fB E.fB_measurable
  exact measurable_id.sub ((measurable_const.sub h1).div E.fB_measurable)

open MechanismDesign.BilateralTrade in
lemma measurable_psiS (E : Environment) : Measurable E.psiS := by
  have h1 : Measurable E.cdfS := measurable_primitive E.loS E.fS E.fS_measurable
  exact measurable_id.add (h1.div E.fS_measurable)

lemma measurable_worth {δ : Type*} [MeasurableSpace δ] {M N : Type*} [Fintype M] [Fintype N]
    (a : M → N → δ → ℝ) (ha : ∀ i j, Measurable (a i j)) :
    Measurable (fun x => AssignmentGame.CoreLP.worth (fun i j => a i j x) Finset.univ Finset.univ) := by
  classical
  unfold AssignmentGame.CoreLP.worth
  have hne : (AssignmentGame.CoreLP.matchings (M := M) (N := N) Finset.univ Finset.univ).Nonempty :=
    ⟨∅, AssignmentGame.CoreLP.empty_mem_matchings _ _⟩
  have key : (fun x => (AssignmentGame.CoreLP.matchings (M := M) (N := N) Finset.univ Finset.univ).sup'
      ⟨∅, AssignmentGame.CoreLP.empty_mem_matchings _ _⟩
      (fun P => ∑ p ∈ P, a p.1 p.2 x)) =
      (AssignmentGame.CoreLP.matchings (M := M) (N := N) Finset.univ Finset.univ).sup' hne
        (fun P x => ∑ p ∈ P, a p.1 p.2 x) := by
    funext x
    rw [Finset.sup'_apply]
  rw [key]
  apply Finset.measurable_sup'
  intro P _
  exact Finset.measurable_sum _ (fun p _ => ha p.1 p.2)

lemma weight_meas (E : Environment) (b h : ℝ) (n m : ℕ) (j : Fin m) (i : Fin n) :
    Measurable (fun xy : (ℕ → ℝ × ℝ) × (ℕ → ℝ × ℝ) =>
      E.psiB (xy.1 i).2 - E.psiS (xy.2 j).2 -
        b * max ((xy.2 j).1 - (xy.1 i).1) 0 - h * max ((xy.1 i).1 - (xy.2 j).1) 0) := by
  have hψB := measurable_psiB E
  have hψS := measurable_psiS E
  fun_prop

noncomputable def Gfun (E : Environment) (b h : ℝ) (n m : ℕ)
    (xy : (ℕ → ℝ × ℝ) × (ℕ → ℝ × ℝ)) : ℝ :=
  AssignmentGame.CoreLP.worth (M := Fin m) (N := Fin n)
      (fun j i => E.psiB (xy.1 i).2 - E.psiS (xy.2 j).2 -
        b * max ((xy.2 j).1 - (xy.1 i).1) 0 - h * max ((xy.1 i).1 - (xy.2 j).1) 0)
      Finset.univ Finset.univ

lemma G_meas (E : Environment) (b h : ℝ) (n m : ℕ) : Measurable (Gfun E b h n m) :=
  measurable_worth (fun (j : Fin m) (i : Fin n) (xy : (ℕ → ℝ × ℝ) × (ℕ → ℝ × ℝ)) =>
      E.psiB (xy.1 i).2 - E.psiS (xy.2 j).2 -
        b * max ((xy.2 j).1 - (xy.1 i).1) 0 - h * max ((xy.1 i).1 - (xy.2 j).1) 0)
      (fun j i => weight_meas E b h n m j i)

lemma Jbar_eq (E : Environment) (b h : ℝ) (ω : Ω) :
    Jbar E b h ω = Gfun E b h ω.1.1 ω.2.1 (ω.1.2, ω.2.2) := rfl

lemma hG_meas (E : Environment) (b h : ℝ) :
    Measurable (fun p : (ℕ × ℕ) × ((ℕ → ℝ × ℝ) × (ℕ → ℝ × ℝ)) => Gfun E b h p.1.1 p.1.2 p.2) :=
  measurable_from_prod_countable_right (fun nm => G_meas E b h nm.1 nm.2)

lemma Jbar_measurable (E : Environment) (b h : ℝ) : Measurable (Jbar E b h) := by
  have hpre : Measurable (fun ω : Ω => ((ω.1.1, ω.2.1), (ω.1.2, ω.2.2))) := by
    fun_prop
  have e : Jbar E b h = (fun p : (ℕ × ℕ) × ((ℕ → ℝ × ℝ) × (ℕ → ℝ × ℝ)) =>
      Gfun E b h p.1.1 p.1.2 p.2) ∘ (fun ω : Ω => ((ω.1.1, ω.2.1), (ω.1.2, ω.2.2))) := by
    funext ω
    exact Jbar_eq E b h ω
  rw [e]
  exact (hG_meas E b h).comp hpre


lemma timeLaw_prob (T : ℝ) (hT : 0 < T) : IsProbabilityMeasure (timeLaw T) := by
  refine ⟨?_⟩
  unfold timeLaw
  rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Icc, smul_eq_mul, ← ENNReal.ofReal_mul (by positivity)]
  have : 1 / T * (T - 0) = 1 := by rw [sub_zero]; field_simp
  rw [this]; simp

open MechanismDesign.BilateralTrade in
lemma valLaw_prob (E : Environment) : IsProbabilityMeasure (valLaw E) := by
  refine ⟨?_⟩
  unfold valLaw
  have hI : IntegrableOn E.fB (Set.Icc E.loB E.hiB) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le E.loB_lt_hiB.le).1 E.fB_intervalIntegrable
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc E.loB E.hiB)] E.fB :=
    (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall (fun x hx => (E.fB_pos x hx).le))
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hI hnn]
  have : ∫ x in Set.Icc E.loB E.hiB, E.fB x = 1 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le E.loB_lt_hiB.le]
    exact E.fB_integral
  rw [this]; simp

open MechanismDesign.BilateralTrade in
lemma costLaw_prob (E : Environment) : IsProbabilityMeasure (costLaw E) := by
  refine ⟨?_⟩
  unfold costLaw
  have hI : IntegrableOn E.fS (Set.Icc E.loS E.hiS) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le E.loS_lt_hiS.le).1 E.fS_intervalIntegrable
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc E.loS E.hiS)] E.fS :=
    (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall (fun x hx => (E.fS_pos x hx).le))
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hI hnn]
  have : ∫ x in Set.Icc E.loS E.hiS, E.fS x = 1 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le E.loS_lt_hiS.le]
    exact E.fS_integral
  rw [this]; simp

open MechanismDesign.BilateralTrade in
lemma valLaw_integral (E : Environment) (g : ℝ → ℝ) :
    ∫ x, g x ∂valLaw E = ∫ x in Set.Icc E.loB E.hiB, E.fB x * g x := by
  unfold valLaw
  rw [integral_withDensity_eq_integral_toReal_smul
    (E.fB_measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)) g]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  simp [ENNReal.toReal_ofReal (E.fB_pos x hx).le]

open MechanismDesign.BilateralTrade in
lemma costLaw_integral (E : Environment) (g : ℝ → ℝ) :
    ∫ x, g x ∂costLaw E = ∫ x in Set.Icc E.loS E.hiS, E.fS x * g x := by
  unfold costLaw
  rw [integral_withDensity_eq_integral_toReal_smul
    (E.fS_measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)) g]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  simp [ENNReal.toReal_ofReal (E.fS_pos x hx).le]

open MechanismDesign.BilateralTrade in
lemma valLaw_integrable (E : Environment) (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (g : ℝ → ℝ) (hg : ContinuousOn g (Set.Icc E.loB E.hiB)) : Integrable g (valLaw E) := by
  unfold valLaw
  rw [integrable_withDensity_iff_integrable_smul' (E.fB_measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  have : IntegrableOn (fun x => E.fB x * g x) (Set.Icc E.loB E.hiB) :=
    (hcontB.mul hg).integrableOn_Icc
  refine this.congr_fun (fun x hx => ?_) measurableSet_Icc
  simp [ENNReal.toReal_ofReal (E.fB_pos x hx).le]

open MechanismDesign.BilateralTrade in
lemma costLaw_integrable (E : Environment) (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (g : ℝ → ℝ) (hg : ContinuousOn g (Set.Icc E.loS E.hiS)) : Integrable g (costLaw E) := by
  unfold costLaw
  rw [integrable_withDensity_iff_integrable_smul' (E.fS_measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  have : IntegrableOn (fun x => E.fS x * g x) (Set.Icc E.loS E.hiS) :=
    (hcontS.mul hg).integrableOn_Icc
  refine this.congr_fun (fun x hx => ?_) measurableSet_Icc
  simp [ENNReal.toReal_ofReal (E.fS_pos x hx).le]

lemma snd_marks (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (g : ℝ → ℝ) (hg : Measurable g) (hint : Integrable g ν) :
    Integrable (fun z : ℝ × ℝ => g z.2) (μ.prod ν) ∧
    ∫ z : ℝ × ℝ, g z.2 ∂(μ.prod ν) = ∫ x, g x ∂ν := by
  have mp : MeasurePreserving Prod.snd (μ.prod ν) ν := measurePreserving_snd
  refine ⟨mp.integrable_comp_of_integrable hint, ?_⟩
  have := integral_map (μ := μ.prod ν) mp.measurable.aemeasurable (f := g) hg.aestronglyMeasurable
  rw [mp.map_eq] at this
  exact this.symm

lemma sideLaw_prob (r T : ℝ) (Q : Measure (ℝ × ℝ)) [IsProbabilityMeasure Q] :
    IsProbabilityMeasure (sideLaw r T Q) := by
  unfold sideLaw
  have h1 : IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => Q)) := inferInstance
  have h2' : ∀ ρ : NNReal, IsProbabilityMeasure (ProbabilityTheory.poissonMeasure ρ) :=
    fun ρ => inferInstance
  have h2 := h2' ⟨max (r * T) 0, le_max_right _ _⟩
  infer_instance

open MechanismDesign.BilateralTrade in
lemma Seta_facts (E : Environment) (lamD lamS T η : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hd : 0 < lamD) (hs : 0 < lamS) (hT : 0 < T) :
    Integrable (fun ω : Ω => (∑ i : Fin ω.1.1, max (E.psiB (buyerValue ω i) - η) 0) +
        (∑ j : Fin ω.2.1, max (η - E.psiS (sellerCost ω j)) 0)) (P E lamD lamS T) ∧
    ∫ ω : Ω, ((∑ i : Fin ω.1.1, max (E.psiB (buyerValue ω i) - η) 0) +
        (∑ j : Fin ω.2.1, max (η - E.psiS (sellerCost ω j)) 0)) ∂(P E lamD lamS T) =
      lamD * T * (∫ x in Set.Icc E.loB E.hiB, E.fB x * max (E.psiB x - η) 0) +
      lamS * T * (∫ x in Set.Icc E.loS E.hiS, E.fS x * max (η - E.psiS x) 0) := by
  have := timeLaw_prob T hT
  have := valLaw_prob E
  have := costLaw_prob E
  have hbm : IsProbabilityMeasure (buyerMark E T) := by unfold buyerMark; infer_instance
  have hsm : IsProbabilityMeasure (sellerMark E T) := by unfold sellerMark; infer_instance
  have hA : IsProbabilityMeasure (sideLaw lamD T (buyerMark E T)) := sideLaw_prob _ _ _
  have hB : IsProbabilityMeasure (sideLaw lamS T (sellerMark E T)) := sideLaw_prob _ _ _
  have gBm : Measurable (fun x => max (E.psiB x - η) 0) :=
    ((measurable_psiB E).sub measurable_const).max measurable_const
  have gSm : Measurable (fun x => max (η - E.psiS x) 0) :=
    (measurable_const.sub (measurable_psiS E)).max measurable_const
  have gBc : ContinuousOn (fun x => max (E.psiB x - η) 0) (Set.Icc E.loB E.hiB) :=
    (continuous_id.max continuous_const).comp_continuousOn
      ((psiB_cont E hcontB).sub continuousOn_const)
  have gSc : ContinuousOn (fun x => max (η - E.psiS x) 0) (Set.Icc E.loS E.hiS) :=
    (continuous_id.max continuous_const).comp_continuousOn
      (continuousOn_const.sub (psiS_cont E hcontS))
  obtain ⟨hBi, hBv⟩ := snd_marks (timeLaw T) (valLaw E) _ gBm (valLaw_integrable E hcontB _ gBc)
  obtain ⟨hSi, hSv⟩ := snd_marks (timeLaw T) (costLaw E) _ gSm (costLaw_integrable E hcontS _ gSc)
  obtain ⟨hWB1, hWB2⟩ := wald lamD T (buyerMark E T) (fun z => max (E.psiB z.2 - η) 0)
    (gBm.comp measurable_snd) hBi
  obtain ⟨hWS1, hWS2⟩ := wald lamS T (sellerMark E T) (fun z => max (η - E.psiS z.2) 0)
    (gSm.comp measurable_snd) hSi
  have eB : ∀ ω : Ω, ∑ i : Fin ω.1.1, max (E.psiB (buyerValue ω i) - η) 0 =
      ∑ i ∈ Finset.range ω.1.1, max (E.psiB (ω.1.2 i).2 - η) 0 := fun ω =>
    Fin.sum_univ_eq_sum_range (fun i => max (E.psiB (ω.1.2 i).2 - η) 0) ω.1.1
  have eS : ∀ ω : Ω, ∑ j : Fin ω.2.1, max (η - E.psiS (sellerCost ω j)) 0 =
      ∑ j ∈ Finset.range ω.2.1, max (η - E.psiS (ω.2.2 j).2) 0 := fun ω =>
    Fin.sum_univ_eq_sum_range (fun j => max (η - E.psiS (ω.2.2 j).2) 0) ω.2.1
  simp_rw [eB, eS]
  have mpf : MeasurePreserving Prod.fst ((sideLaw lamD T (buyerMark E T)).prod
      (sideLaw lamS T (sellerMark E T))) (sideLaw lamD T (buyerMark E T)) := measurePreserving_fst
  have mps : MeasurePreserving Prod.snd ((sideLaw lamD T (buyerMark E T)).prod
      (sideLaw lamS T (sellerMark E T))) (sideLaw lamS T (sellerMark E T)) := measurePreserving_snd
  have i1 := mpf.integrable_comp_of_integrable hWB1
  have i2 := mps.integrable_comp_of_integrable hWS1
  have hPeq : P E lamD lamS T = (sideLaw lamD T (buyerMark E T)).prod
      (sideLaw lamS T (sellerMark E T)) := rfl
  rw [hPeq]
  refine ⟨i1.add i2, ?_⟩
  have j1 := integral_map (μ := (sideLaw lamD T (buyerMark E T)).prod (sideLaw lamS T (sellerMark E T)))
    mpf.measurable.aemeasurable
    (f := fun x : ℕ × (ℕ → ℝ × ℝ) => ∑ i ∈ Finset.range x.1, max (E.psiB (x.2 i).2 - η) 0)
    (by
      apply Measurable.aestronglyMeasurable
      apply measurable_from_prod_countable_right
      intro n
      show Measurable fun y : ℕ → ℝ × ℝ => ∑ i ∈ Finset.range n, max (E.psiB (y i).2 - η) 0
      exact Finset.measurable_sum (Finset.range n) (fun i _ =>
        gBm.comp (measurable_snd.comp (measurable_pi_apply i))))
  have j2 := integral_map (μ := (sideLaw lamD T (buyerMark E T)).prod (sideLaw lamS T (sellerMark E T)))
    mps.measurable.aemeasurable
    (f := fun x : ℕ × (ℕ → ℝ × ℝ) => ∑ i ∈ Finset.range x.1, max (η - E.psiS (x.2 i).2) 0)
    (by
      apply Measurable.aestronglyMeasurable
      apply measurable_from_prod_countable_right
      intro n
      show Measurable fun y : ℕ → ℝ × ℝ => ∑ i ∈ Finset.range n, max (η - E.psiS (y i).2) 0
      exact Finset.measurable_sum (Finset.range n) (fun i _ =>
        gSm.comp (measurable_snd.comp (measurable_pi_apply i))))
  rw [mpf.map_eq] at j1
  rw [mps.map_eq] at j2
  refine Eq.trans (integral_add i1 i2) ?_
  have k1 : ∫ ω : (ℕ × (ℕ → ℝ × ℝ)) × (ℕ × (ℕ → ℝ × ℝ)),
      ∑ i ∈ Finset.range ω.1.1, max (E.psiB (ω.1.2 i).2 - η) 0
        ∂((sideLaw lamD T (buyerMark E T)).prod (sideLaw lamS T (sellerMark E T))) =
      ∫ x : ℕ × (ℕ → ℝ × ℝ), ∑ i ∈ Finset.range x.1, max (E.psiB (x.2 i).2 - η) 0
        ∂(sideLaw lamD T (buyerMark E T)) := j1.symm
  have k2 : ∫ ω : (ℕ × (ℕ → ℝ × ℝ)) × (ℕ × (ℕ → ℝ × ℝ)),
      ∑ i ∈ Finset.range ω.2.1, max (η - E.psiS (ω.2.2 i).2) 0
        ∂((sideLaw lamD T (buyerMark E T)).prod (sideLaw lamS T (sellerMark E T))) =
      ∫ x : ℕ × (ℕ → ℝ × ℝ), ∑ i ∈ Finset.range x.1, max (η - E.psiS (x.2 i).2) 0
        ∂(sideLaw lamS T (sellerMark E T)) := j2.symm
  show (∫ ω : (ℕ × (ℕ → ℝ × ℝ)) × (ℕ × (ℕ → ℝ × ℝ)),
      ∑ i ∈ Finset.range ω.1.1, max (E.psiB (ω.1.2 i).2 - η) 0
        ∂((sideLaw lamD T (buyerMark E T)).prod (sideLaw lamS T (sellerMark E T)))) +
      (∫ ω : (ℕ × (ℕ → ℝ × ℝ)) × (ℕ × (ℕ → ℝ × ℝ)),
      ∑ i ∈ Finset.range ω.2.1, max (η - E.psiS (ω.2.2 i).2) 0
        ∂((sideLaw lamD T (buyerMark E T)).prod (sideLaw lamS T (sellerMark E T)))) = _
  have hbmdef : buyerMark E T = (timeLaw T).prod (valLaw E) := rfl
  have hsmdef : sellerMark E T = (timeLaw T).prod (costLaw E) := rfl
  rw [k1, k2, hWB2, hWS2, hbmdef, hsmdef, hBv, hSv, valLaw_integral, costLaw_integral,
    max_eq_left (by positivity : (0:ℝ) ≤ lamD * T), max_eq_left (by positivity : (0:ℝ) ≤ lamS * T)]


end TwoSidedMatching.Guarantee.MBCopy

namespace TwoSidedMatching.MechBound.S1Aux

open TwoSidedMatching.MechBound

lemma ae_mark (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] (A B : Set ℝ)
    (hA : ∀ᵐ x ∂μ, x ∈ A) (hB : ∀ᵐ x ∂ν, x ∈ B) :
    ∀ᵐ z ∂(μ.prod ν), z ∈ A ×ˢ B := by
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hA
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hB
  filter_upwards [h1, h2] with z hz1 hz2
  exact ⟨hz1, hz2⟩

lemma ae_time (T : ℝ) : ∀ᵐ x ∂(TwoSidedMatching.Guarantee.timeLaw T), x ∈ Set.Icc 0 T := by
  unfold TwoSidedMatching.Guarantee.timeLaw
  exact (Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _)

lemma ae_dens (lo hi : ℝ) (f : ℝ → ℝ) :
    ∀ᵐ x ∂((volume.restrict (Set.Icc lo hi)).withDensity (fun v => ENNReal.ofReal (f v))),
      x ∈ Set.Icc lo hi :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Icc)

lemma ae_side (r T : ℝ) (Q : Measure (ℝ × ℝ)) [IsProbabilityMeasure Q] (A : Set (ℝ × ℝ))
    (hA : ∀ᵐ z ∂Q, z ∈ A) :
    ∀ᵐ x ∂(TwoSidedMatching.Guarantee.sideLaw r T Q), ∀ i, x.2 i ∈ A := by
  unfold TwoSidedMatching.Guarantee.sideLaw
  have hinf : ∀ᵐ w ∂(Measure.infinitePi (fun _ : ℕ => Q)), ∀ i, w i ∈ A := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => Q) i).quasiMeasurePreserving.ae hA
  exact (Measure.quasiMeasurePreserving_snd
    (μ := ProbabilityTheory.poissonMeasure ⟨max (r * T) 0, le_max_right _ _⟩)
    (ν := Measure.infinitePi (fun _ : ℕ => Q))).ae hinf

lemma ae_types (E : Environment) (lamD lamS T : ℝ) (hT : 0 < T) :
    ∀ᵐ ω ∂(P E lamD lamS T), (∀ φ ∈ Hd ω, φ ∈ buyerTypes E T) ∧ (∀ ψ ∈ Hs ω, ψ ∈ sellerTypes E T) := by
  have := TwoSidedMatching.Guarantee.MBCopy.timeLaw_prob T hT
  have hv : IsProbabilityMeasure (valLaw E) := TwoSidedMatching.Guarantee.MBCopy.valLaw_prob E
  have hc : IsProbabilityMeasure (costLaw E) := TwoSidedMatching.Guarantee.MBCopy.costLaw_prob E
  have hbm : IsProbabilityMeasure (buyerMark E T) := by
    unfold buyerMark; infer_instance
  have hsm : IsProbabilityMeasure (sellerMark E T) := by
    unfold sellerMark; infer_instance
  have hA : IsProbabilityMeasure (TwoSidedMatching.Guarantee.sideLaw lamD T (buyerMark E T)) :=
    TwoSidedMatching.Guarantee.MBCopy.sideLaw_prob _ _ _
  have hB : IsProbabilityMeasure (TwoSidedMatching.Guarantee.sideLaw lamS T (sellerMark E T)) :=
    TwoSidedMatching.Guarantee.MBCopy.sideLaw_prob _ _ _
  have hbt : ∀ᵐ z ∂(buyerMark E T), z ∈ buyerTypes E T :=
    ae_mark _ _ _ _ (ae_time T) (ae_dens _ _ _)
  have hst : ∀ᵐ z ∂(sellerMark E T), z ∈ sellerTypes E T :=
    ae_mark _ _ _ _ (ae_time T) (ae_dens _ _ _)
  have h1 := ae_side lamD T (buyerMark E T) _ hbt
  have h2 := ae_side lamS T (sellerMark E T) _ hst
  have g1 := (Measure.quasiMeasurePreserving_fst
    (μ := TwoSidedMatching.Guarantee.sideLaw lamD T (buyerMark E T))
    (ν := TwoSidedMatching.Guarantee.sideLaw lamS T (sellerMark E T))).ae h1
  have g2 := (Measure.quasiMeasurePreserving_snd
    (μ := TwoSidedMatching.Guarantee.sideLaw lamD T (buyerMark E T))
    (ν := TwoSidedMatching.Guarantee.sideLaw lamS T (sellerMark E T))).ae h2
  unfold P
  filter_upwards [g1, g2] with ω hω1 hω2
  refine ⟨fun φ hφ => ?_, fun ψ hψ => ?_⟩
  · simp only [Hd, Multiset.mem_map] at hφ
    obtain ⟨i, -, rfl⟩ := hφ
    exact hω1 i
  · simp only [Hs, Multiset.mem_map] at hψ
    obtain ⟨i, -, rfl⟩ := hψ
    exact hω2 i

lemma P_prob (E : Environment) (lamD lamS T : ℝ) (hT : 0 < T) :
    IsProbabilityMeasure (P E lamD lamS T) := by
  have := TwoSidedMatching.Guarantee.MBCopy.timeLaw_prob T hT
  have hv : IsProbabilityMeasure (valLaw E) := TwoSidedMatching.Guarantee.MBCopy.valLaw_prob E
  have hc : IsProbabilityMeasure (costLaw E) := TwoSidedMatching.Guarantee.MBCopy.costLaw_prob E
  have hbm : IsProbabilityMeasure (buyerMark E T) := by
    unfold buyerMark; infer_instance
  have hsm : IsProbabilityMeasure (sellerMark E T) := by
    unfold sellerMark; infer_instance
  have hA : IsProbabilityMeasure (TwoSidedMatching.Guarantee.sideLaw lamD T (buyerMark E T)) :=
    TwoSidedMatching.Guarantee.MBCopy.sideLaw_prob _ _ _
  have hB : IsProbabilityMeasure (TwoSidedMatching.Guarantee.sideLaw lamS T (sellerMark E T)) :=
    TwoSidedMatching.Guarantee.MBCopy.sideLaw_prob _ _ _
  unfold P
  infer_instance

lemma ins_eq (z1 : ℕ → ℝ × ℝ) (n : ℕ) (φhat : ℝ × ℝ) :
    (Multiset.range (n + 1)).map (Function.update z1 n φhat) =
      φhat ::ₘ (Multiset.range n).map z1 := by
  rw [Multiset.range_succ, Multiset.map_cons, Function.update_self]
  congr 1
  apply Multiset.map_congr rfl
  intro i hi
  rw [Function.update_of_ne (Nat.ne_of_lt (Multiset.mem_range.1 hi))]

lemma inserted_measurable (E : Environment) (lamD lamS T : ℝ) (y : Mechanism)
    (hwd : WellDefined E lamD lamS T y) (φhat : ℝ × ℝ) :
    Measurable (fun ω : TwoSidedMatching.Guarantee.Ω =>
      ((y (φhat ::ₘ Hd ω) (Hs ω)).1 φhat).toTriple) := by
  classical
  have hG : Measurable (fun p : (ℕ × ℕ) × ((ℕ → ℝ × ℝ) × (ℕ → ℝ × ℝ)) =>
      ((y (φhat ::ₘ (Multiset.range p.1.1).map p.2.1)
        ((Multiset.range p.1.2).map p.2.2)).1 φhat).toTriple) := by
    apply measurable_from_prod_countable_right
    intro nk
    obtain ⟨n, k⟩ := nk
    have h1 := hwd.buyer_measurable (n + 1) k n (Nat.lt_succ_self n)
    have h2 : Measurable (fun z : (ℕ → ℝ × ℝ) × (ℕ → ℝ × ℝ) =>
        (Function.update z.1 n φhat, z.2)) :=
      (measurable_update_left.comp measurable_fst).prodMk measurable_snd
    have h3 := h1.comp h2
    convert h3 using 1
    funext z
    simp only [Function.comp_apply, ins_eq, Function.update_self]
  have hpre : Measurable (fun ω : TwoSidedMatching.Guarantee.Ω =>
      ((ω.1.1, ω.2.1), (ω.1.2, ω.2.2))) := by fun_prop
  exact hG.comp hpre

lemma outcome_ae (E : Environment) (lamD lamS T : ℝ) (hT : 0 < T) (y : Mechanism)
    (hfeas : Feasible E T y) (φhat : ℝ × ℝ) (hφ : φhat ∈ buyerTypes E T) :
    ∀ᵐ ω ∂(P E lamD lamS T), AgentFeasible T φhat ((y (φhat ::ₘ Hd ω) (Hs ω)).1 φhat) := by
  filter_upwards [ae_types E lamD lamS T hT] with ω hω
  refine (hfeas (φhat ::ₘ Hd ω) (Hs ω) ?_ hω.2).1 φhat (Multiset.mem_cons_self _ _)
  intro x hx
  rw [Multiset.mem_cons] at hx
  rcases hx with rfl | hx
  · exact hφ
  · exact hω.1 x hx

lemma comp_integrable (E : Environment) (lamD lamS T : ℝ) (hT : 0 < T) (y : Mechanism)
    (hfeas : Feasible E T y) (hwd : WellDefined E lamD lamS T y)
    (φhat : ℝ × ℝ) (hφ : φhat ∈ buyerTypes E T) :
    Integrable (fun ω => ((y (φhat ::ₘ Hd ω) (Hs ω)).1 φhat).m) (P E lamD lamS T) ∧
    Integrable (fun ω => ((y (φhat ::ₘ Hd ω) (Hs ω)).1 φhat).s) (P E lamD lamS T) ∧
    Integrable (fun ω => ((y (φhat ::ₘ Hd ω) (Hs ω)).1 φhat).p) (P E lamD lamS T) := by
  have := P_prob E lamD lamS T hT
  have hm := inserted_measurable E lamD lamS T y hwd φhat
  have hae := outcome_ae E lamD lamS T hT y hfeas φhat hφ
  refine ⟨?_, ?_, hwd.buyer_interim_integrable φhat hφ⟩
  · refine Integrable.of_bound hm.snd.fst.aestronglyMeasurable 1 ?_
    filter_upwards [hae] with ω hω
    rcases hω.2.2 with h0 | h1
    · show ‖((y (φhat ::ₘ Hd ω) (Hs ω)).1 φhat).m‖ ≤ 1
      rw [h0]; simp
    · show ‖((y (φhat ::ₘ Hd ω) (Hs ω)).1 φhat).m‖ ≤ 1
      rw [h1]; simp
  · refine Integrable.of_bound hm.fst.aestronglyMeasurable (|φhat.1| + |T|) ?_
    filter_upwards [hae] with ω hω
    show ‖((y (φhat ::ₘ Hd ω) (Hs ω)).1 φhat).s‖ ≤ |φhat.1| + |T|
    rw [Real.norm_eq_abs, abs_le]
    obtain ⟨h1, h2, -⟩ := hω
    constructor
    · have := neg_abs_le φhat.1; have := abs_nonneg T; linarith
    · have := le_abs_self T; have := abs_nonneg φhat.1; linarith

lemma Eminus_Ud (E : Environment) (lamD lamS T b : ℝ) (hT : 0 < T) (y : Mechanism)
    (hfeas : Feasible E T y) (hwd : WellDefined E lamD lamS T y)
    (φhat : ℝ × ℝ) (hφ : φhat ∈ buyerTypes E T) (φ : ℝ × ℝ) :
    Eminus E lamD lamS T y φhat (Ud b φ) =
      φ.2 * Eminus E lamD lamS T y φhat (fun o => o.m) - Eminus E lamD lamS T y φhat (fun o => o.p)
        - b * Eminus E lamD lamS T y φhat (fun o => o.s - φ.1) := by
  obtain ⟨im, is, ip⟩ := comp_integrable E lamD lamS T hT y hfeas hwd φhat hφ
  have := P_prob E lamD lamS T hT
  unfold Eminus Ud
  have i1 := im.const_mul φ.2
  have i2 : Integrable (fun ω => b * (((y (φhat ::ₘ Hd ω) (Hs ω)).1 φhat).s - φ.1))
      (P E lamD lamS T) := (is.sub (integrable_const φ.1)).const_mul b
  have i12 : Integrable (fun ω => φ.2 * ((y (φhat ::ₘ Hd ω) (Hs ω)).1 φhat).m -
      ((y (φhat ::ₘ Hd ω) (Hs ω)).1 φhat).p) (P E lamD lamS T) := i1.sub ip
  rw [integral_sub i12 i2, integral_sub i1 ip, integral_const_mul, integral_const_mul]

end TwoSidedMatching.MechBound.S1Aux

open ProbabilityTheory
open scoped ENNReal NNReal

namespace TwoSidedMatching.MechBound.MeckeAux

variable {X : Type*} [MeasurableSpace X]

/-- Law of `update z n (z' n)` under two independent copies. -/
lemma law_update (Q : Measure X) [IsProbabilityMeasure Q] (n : ℕ) :
    ((Measure.infinitePi (fun _ : ℕ => Q)).prod (Measure.infinitePi (fun _ : ℕ => Q))).map
      (fun p : (ℕ → X) × (ℕ → X) => Function.update p.1 n (p.2 n)) =
      Measure.infinitePi (fun _ : ℕ => Q) := by
  classical
  apply Measure.eq_infinitePi
  intro s t ht
  have hmeas : Measurable (fun p : (ℕ → X) × (ℕ → X) => Function.update p.1 n (p.2 n)) := by
    fun_prop
  rw [Measure.map_apply hmeas (MeasurableSet.pi (Finset.countable_toSet s) (fun i _ => ht i))]
  have hpre : (fun p : (ℕ → X) × (ℕ → X) => Function.update p.1 n (p.2 n)) ⁻¹'
      (Set.pi (↑s) t) =
      (Set.pi (↑(s.erase n)) t) ×ˢ
        (if n ∈ s then (fun z : ℕ → X => z n) ⁻¹' t n else Set.univ) := by
    ext ⟨z, z'⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.mem_erase]
    constructor
    · intro h
      refine ⟨fun i ⟨hin, his⟩ => ?_, ?_⟩
      · have := h i his
        rwa [Function.update_of_ne hin] at this
      · split_ifs with hn
        · have := h n hn
          rwa [Function.update_self] at this
        · trivial
    · rintro ⟨h1, h2⟩ i his
      by_cases hin : i = n
      · subst hin
        rw [if_pos his] at h2
        rw [Function.update_self]; exact h2
      · rw [Function.update_of_ne hin]; exact h1 i ⟨hin, his⟩
  rw [hpre, Measure.prod_prod, Measure.infinitePi_pi _ (fun i _ => ht i)]
  split_ifs with hn
  · have := (measurePreserving_eval_infinitePi (fun _ : ℕ => Q) n).measure_preimage
      (ht n).nullMeasurableSet
    erw [this]
    rw [mul_comm, Finset.mul_prod_erase s (fun i => Q (t i)) hn]
  · rw [Finset.erase_eq_of_notMem hn, measure_univ, mul_one]

lemma law_swap (Q : Measure X) [IsProbabilityMeasure Q] (σ : Equiv.Perm ℕ) :
    (Measure.infinitePi (fun _ : ℕ => Q)).map (fun z : ℕ → X => fun j => z (σ j)) =
      Measure.infinitePi (fun _ : ℕ => Q) := by
  classical
  apply Measure.eq_infinitePi
  intro s t ht
  have hmeas : Measurable (fun z : ℕ → X => fun j => z (σ j)) := by fun_prop
  rw [Measure.map_apply hmeas (MeasurableSet.pi (Finset.countable_toSet s) (fun i _ => ht i))]
  have hpre : (fun z : ℕ → X => fun j => z (σ j)) ⁻¹' (Set.pi (↑s) t) =
      Set.pi (↑(s.map σ.toEmbedding)) (fun j => t (σ.symm j)) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Finset.mem_map_equiv]
    constructor
    · intro h j hj
      have := h (σ.symm j) hj
      simpa using this
    · intro h i hi
      have := h (σ i) (by simpa using hi)
      rwa [Equiv.symm_apply_apply] at this
  rw [hpre, Measure.infinitePi_pi _ (fun i _ => ht _), Finset.prod_map]
  exact Finset.prod_congr rfl (fun x _ => by simp only [Equiv.coe_toEmbedding, Equiv.symm_apply_apply])

lemma key_eq (F : Multiset X → X → ℝ≥0∞) (n : ℕ) (z' z : ℕ → X) (i : ℕ)
    (hmap : (Multiset.range (n + 1)).map z' = (Multiset.range (n + 1)).map z) (hval : z' n = z i) :
    F (z' n ::ₘ (Multiset.range n).map z') (z' n) = F ((Multiset.range (n + 1)).map z) (z i) := by
  rw [← hval, ← hmap, Multiset.range_succ, Multiset.map_cons]

/-- Exchangeability + independence: the inserted-point identity for `n + 1` points. -/
lemma mecke_n (Q : Measure X) [IsProbabilityMeasure Q] (F : Multiset X → X → ℝ≥0∞) (n : ℕ)
    (hF : Measurable (fun p : X × (ℕ → X) => F (p.1 ::ₘ (Multiset.range n).map p.2) p.1)) :
    ∫⁻ z, (((Multiset.range (n + 1)).map z).map (F ((Multiset.range (n + 1)).map z))).sum
        ∂(Measure.infinitePi (fun _ : ℕ => Q)) =
      (n + 1 : ℝ≥0∞) * ∫⁻ φ, ∫⁻ z, F (φ ::ₘ (Multiset.range n).map z) φ
        ∂(Measure.infinitePi (fun _ : ℕ => Q)) ∂Q := by
  classical
  set μ := Measure.infinitePi (fun _ : ℕ => Q) with hμ
  set H : X → (ℕ → X) → ℝ≥0∞ := fun φ z => F (φ ::ₘ (Multiset.range n).map z) φ with hH
  have hHm : Measurable (fun p : X × (ℕ → X) => H p.1 p.2) := hF
  have hDsucc : ∀ z : ℕ → X, (Multiset.range (n + 1)).map z = z n ::ₘ (Multiset.range n).map z := by
    intro z; rw [Multiset.range_succ, Multiset.map_cons]
  -- the integrand as a finite sum over indices
  have hsum : ∀ z : ℕ → X, (((Multiset.range (n + 1)).map z).map
      (F ((Multiset.range (n + 1)).map z))).sum =
      ∑ i ∈ Finset.range (n + 1), F ((Multiset.range (n + 1)).map z) (z i) := by
    intro z; rw [Multiset.map_map]; rfl
  -- invariance of the multiset under a swap of indices in range (n+1)
  have hperm : ∀ (i : ℕ), i < n + 1 → ∀ z : ℕ → X,
      (Multiset.range (n + 1)).map (fun j => z (Equiv.swap i n j)) =
        (Multiset.range (n + 1)).map z := by
    intro i hi z
    rw [show (fun j => z (Equiv.swap i n j)) = z ∘ (Equiv.swap i n) from rfl,
      ← Multiset.map_map z (Equiv.swap i n)]
    congr 1
    have : (Finset.range (n + 1)).map (Equiv.swap i n).toEmbedding = Finset.range (n + 1) := by
      apply Finset.eq_of_subset_of_card_le
      · intro j hj
        rw [Finset.mem_map_equiv] at hj
        rw [Finset.mem_range] at hj ⊢
        rcases eq_or_ne j i with rfl | h1
        · simp [Equiv.swap_apply_left]; omega
        rcases eq_or_ne j n with rfl | h2
        · simp [Equiv.swap_apply_right]
        · rw [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne h1 h2] at hj; exact hj
      · simp
    have := congrArg Finset.val this
    simpa using this
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ∫⁻ z, F ((Multiset.range (n + 1)).map z) (z i) ∂μ = ∫⁻ φ, ∫⁻ z, H φ z ∂μ ∂Q := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    -- step 1: swap i and n
    have hK : Measurable (fun z : ℕ → X => H (z n) z) :=
      hHm.comp (f := fun z : ℕ → X => (z n, z)) ((measurable_pi_apply n).prodMk measurable_id)
    have hswm : Measurable (fun z : ℕ → X => fun j => z (Equiv.swap i n j)) := by fun_prop
    have e1 : ∫⁻ z, F ((Multiset.range (n + 1)).map z) (z i) ∂μ = ∫⁻ z, H (z n) z ∂μ := by
      have := lintegral_map hK hswm (μ := μ)
      rw [law_swap Q (Equiv.swap i n)] at this
      rw [this]
      congr 1
      funext z
      exact (key_eq F n _ z i (hperm i hi' z) (by simp)).symm
    -- step 2: independence of coordinate n
    have hU : Measurable (fun p : (ℕ → X) × (ℕ → X) => Function.update p.1 n (p.2 n)) := by
      fun_prop
    have e2 : ∫⁻ z, H (z n) z ∂μ = ∫⁻ p, H (p.2 n) p.1 ∂(μ.prod μ) := by
      have := lintegral_map hK hU (μ := μ.prod μ)
      rw [law_update Q n] at this
      rw [this]
      congr 1
      funext p
      simp only [hH, Function.update_self]
      congr 2
      apply Multiset.map_congr rfl
      intro j hj
      rw [Function.update_of_ne (Nat.ne_of_lt (Multiset.mem_range.1 hj))]
    have hm2 : Measurable (fun p : (ℕ → X) × (ℕ → X) => H (p.2 n) p.1) :=
      hHm.comp (f := fun p : (ℕ → X) × (ℕ → X) => (p.2 n, p.1))
        (((measurable_pi_apply n).comp measurable_snd).prodMk measurable_fst)
    have e3 : ∫⁻ p, H (p.2 n) p.1 ∂(μ.prod μ) = ∫⁻ z', ∫⁻ z, H (z' n) z ∂μ ∂μ :=
      lintegral_prod_symm' _ hm2
    have hm3 : Measurable (fun φ : X => ∫⁻ z, H φ z ∂μ) :=
      hHm.lintegral_prod_right'
    have e4 : ∫⁻ z', ∫⁻ z, H (z' n) z ∂μ ∂μ = ∫⁻ φ, ∫⁻ z, H φ z ∂μ ∂Q := by
      have := lintegral_map hm3 (measurable_pi_apply n) (μ := μ)
      rw [(measurePreserving_eval_infinitePi (fun _ : ℕ => Q) n).map_eq] at this
      exact this.symm
    rw [e1, e2, e3, e4]
  simp_rw [hsum]
  rw [lintegral_finsetSum]
  · rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast; rfl
  · intro i hi
    have hi' := Finset.mem_range.1 hi
    have hswm : Measurable (fun z : ℕ → X => fun j => z (Equiv.swap i n j)) := by fun_prop
    have hK : Measurable (fun z : ℕ → X => H (z n) z) :=
      hHm.comp (f := fun z : ℕ → X => (z n, z)) ((measurable_pi_apply n).prodMk measurable_id)
    have e : (fun z : ℕ → X => F ((Multiset.range (n + 1)).map z) (z i)) =
        (fun z : ℕ → X => H (z n) z) ∘ (fun z : ℕ → X => fun j => z (Equiv.swap i n j)) := by
      funext z
      exact (key_eq F n _ z i (hperm i hi' z) (by simp)).symm
    rw [e]
    exact hK.comp hswm


lemma poisson_succ (ρ : ℝ≥0) (n : ℕ) :
    poissonMeasure ρ {n + 1} * ((n : ℝ≥0∞) + 1) = (ρ : ℝ≥0∞) * poissonMeasure ρ {n} := by
  rw [poissonMeasure_singleton, poissonMeasure_singleton]
  have h1 : ((n : ℝ≥0∞) + 1) = ENNReal.ofReal ((n : ℝ) + 1) := by
    rw [ENNReal.ofReal_add (by positivity) zero_le_one]; simp
  have h2 : (ρ : ℝ≥0∞) = ENNReal.ofReal (ρ : ℝ) := by simp
  rw [h1, h2, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- Mecke (Slivnyak) formula for the mixed-binomial representation of a Poisson process, with an
independent parameter `y`. -/
lemma mecke (ρ : ℝ≥0) (Q : Measure X) [IsProbabilityMeasure Q]
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν]
    (F : Y → Multiset X → X → ℝ≥0∞)
    (hF : ∀ n : ℕ, Measurable (fun q : Y × X × (ℕ → X) =>
      F q.1 (q.2.1 ::ₘ (Multiset.range n).map q.2.2) q.2.1))
    (hL : Measurable (fun q : (ℕ × (ℕ → X)) × Y =>
      (((Multiset.range q.1.1).map q.1.2).map (F q.2 ((Multiset.range q.1.1).map q.1.2))).sum)) :
    ∫⁻ q, (((Multiset.range q.1.1).map q.1.2).map (F q.2 ((Multiset.range q.1.1).map q.1.2))).sum
        ∂(((poissonMeasure ρ).prod (Measure.infinitePi (fun _ : ℕ => Q))).prod ν) =
      (ρ : ℝ≥0∞) * ∫⁻ φ, ∫⁻ q, F q.2 (φ ::ₘ (Multiset.range q.1.1).map q.1.2) φ
        ∂(((poissonMeasure ρ).prod (Measure.infinitePi (fun _ : ℕ => Q))).prod ν) ∂Q := by
  classical
  set μ := Measure.infinitePi (fun _ : ℕ => Q) with hμ
  set A := (poissonMeasure ρ).prod μ with hA
  -- joint measurability of the right-hand integrand
  have hGm : Measurable (fun p : X × ((ℕ × (ℕ → X)) × Y) =>
      F p.2.2 (p.1 ::ₘ (Multiset.range p.2.1.1).map p.2.1.2) p.1) := by
    have h1 : Measurable (fun r : ℕ × (Y × X × (ℕ → X)) =>
        F r.2.1 (r.2.2.1 ::ₘ (Multiset.range r.1).map r.2.2.2) r.2.2.1) :=
      measurable_from_prod_countable_right (fun n => hF n)
    have h2 : Measurable (fun p : X × ((ℕ × (ℕ → X)) × Y) => (p.2.1.1, (p.2.2, p.1, p.2.1.2))) := by
      fun_prop
    exact h1.comp h2
  -- right-hand side rearranged
  have hR : ∫⁻ φ, ∫⁻ q, F q.2 (φ ::ₘ (Multiset.range q.1.1).map q.1.2) φ ∂(A.prod ν) ∂Q =
      ∫⁻ y, ∑' n, poissonMeasure ρ {n} *
        ∫⁻ φ, ∫⁻ z, F y (φ ::ₘ (Multiset.range n).map z) φ ∂μ ∂Q ∂ν := by
    rw [lintegral_lintegral_swap hGm.aemeasurable]
    have hm1 : Measurable (fun q : (ℕ × (ℕ → X)) × Y =>
        ∫⁻ φ, F q.2 (φ ::ₘ (Multiset.range q.1.1).map q.1.2) φ ∂Q) :=
      hGm.lintegral_prod_left'
    rw [lintegral_prod_symm' _ hm1]
    congr 1
    funext y
    have hm2 : Measurable (fun x : ℕ × (ℕ → X) =>
        ∫⁻ φ, F y (φ ::ₘ (Multiset.range x.1).map x.2) φ ∂Q) :=
      hm1.comp (measurable_id.prodMk measurable_const)
    rw [hA, lintegral_prod _ hm2.aemeasurable, lintegral_countable']
    congr 1
    funext n
    rw [mul_comm]
    congr 1
    have hm3 : Measurable (fun p : X × (ℕ → X) => F y (p.1 ::ₘ (Multiset.range n).map p.2) p.1) :=
      (hF n).comp (measurable_const.prodMk measurable_id)
    exact lintegral_lintegral_swap (hm3.comp measurable_swap).aemeasurable
  rw [hR, lintegral_prod_symm' _ hL, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  congr 1
  funext y
  have hLy : Measurable (fun x : ℕ × (ℕ → X) =>
      (((Multiset.range x.1).map x.2).map (F y ((Multiset.range x.1).map x.2))).sum) :=
    hL.comp (measurable_id.prodMk measurable_const)
  rw [hA, lintegral_prod _ hLy.aemeasurable, lintegral_countable']
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Multiset.range_zero, Multiset.map_zero, Multiset.sum_zero, lintegral_zero,
    zero_mul, zero_add]
  rw [← ENNReal.tsum_mul_left]
  congr 1
  funext n
  have hFn : Measurable (fun p : X × (ℕ → X) => F y (p.1 ::ₘ (Multiset.range n).map p.2) p.1) :=
    (hF n).comp (measurable_const.prodMk measurable_id)
  rw [mecke_n Q (F y) n hFn]
  rw [mul_comm, ← mul_assoc, poisson_succ]
  ring


end TwoSidedMatching.MechBound.MeckeAux


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace TwoSidedMatching.MechBound.MeckeAux

variable {X : Type*} [MeasurableSpace X]

lemma ofReal_msum {α : Type*} (M : Multiset α) (h : α → ℝ) (hh : ∀ a, 0 ≤ h a) :
    ENNReal.ofReal (M.map h).sum = (M.map (fun a => ENNReal.ofReal (h a))).sum := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons,
      ENNReal.ofReal_add (hh a) (Multiset.sum_nonneg (fun x hx => by
        obtain ⟨b, -, rfl⟩ := Multiset.mem_map.1 hx; exact hh b)), ih]

lemma sum_meas {Y : Type*} [MeasurableSpace Y] {β : Type*} [AddCommMonoid β] [MeasurableSpace β]
    [MeasurableAdd₂ β] (G : Y → Multiset X → X → β)
    (hG : ∀ n i, i < n →
      Measurable (fun q : Y × (ℕ → X) => G q.1 ((Multiset.range n).map q.2) (q.2 i))) :
    Measurable (fun q : (ℕ × (ℕ → X)) × Y =>
      (((Multiset.range q.1.1).map q.1.2).map (G q.2 ((Multiset.range q.1.1).map q.1.2))).sum) := by
  have h1 : Measurable (fun r : ℕ × (Y × (ℕ → X)) =>
      ∑ i ∈ Finset.range r.1, G r.2.1 ((Multiset.range r.1).map r.2.2) (r.2.2 i)) :=
    measurable_from_prod_countable_right (fun n => by
      show Measurable (fun y : Y × (ℕ → X) =>
        ∑ i ∈ Finset.range n, G y.1 ((Multiset.range n).map y.2) (y.2 i))
      exact Finset.measurable_sum _ (fun i hi => hG n i (Finset.mem_range.1 hi)))
  have h2 : Measurable (fun q : (ℕ × (ℕ → X)) × Y => (q.1.1, (q.2, q.1.2))) := by fun_prop
  convert h1.comp h2 using 1
  funext q
  simp only [Function.comp_apply, Multiset.map_map]
  rfl

/-- The Mecke formula for real integrands. -/
lemma mecke_real (ρ : ℝ≥0) (hρ : 0 < ρ) (Q : Measure X) [IsProbabilityMeasure Q]
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν]
    (g : Y → Multiset X → X → ℝ)
    (hG : ∀ n i, i < n →
      Measurable (fun q : Y × (ℕ → X) => g q.1 ((Multiset.range n).map q.2) (q.2 i)))
    (hF : ∀ n : ℕ, Measurable (fun q : Y × X × (ℕ → X) =>
      g q.1 (q.2.1 ::ₘ (Multiset.range n).map q.2.2) q.2.1))
    (hint : Integrable (fun q : (ℕ × (ℕ → X)) × Y =>
      (((Multiset.range q.1.1).map q.1.2).map
        (fun φ => |g q.2 ((Multiset.range q.1.1).map q.1.2) φ|)).sum)
      (((poissonMeasure ρ).prod (Measure.infinitePi (fun _ : ℕ => Q))).prod ν)) :
    Integrable (fun p : X × ((ℕ × (ℕ → X)) × Y) =>
        g p.2.2 (p.1 ::ₘ (Multiset.range p.2.1.1).map p.2.1.2) p.1)
      (Q.prod (((poissonMeasure ρ).prod (Measure.infinitePi (fun _ : ℕ => Q))).prod ν)) ∧
    ∫ q, (((Multiset.range q.1.1).map q.1.2).map (g q.2 ((Multiset.range q.1.1).map q.1.2))).sum
        ∂(((poissonMeasure ρ).prod (Measure.infinitePi (fun _ : ℕ => Q))).prod ν) =
      (ρ : ℝ) * ∫ φ, ∫ q, g q.2 (φ ::ₘ (Multiset.range q.1.1).map q.1.2) φ
        ∂(((poissonMeasure ρ).prod (Measure.infinitePi (fun _ : ℕ => Q))).prod ν) ∂Q := by
  classical
  set M := ((poissonMeasure ρ).prod (Measure.infinitePi (fun _ : ℕ => Q))).prod ν with hM
  set K : X × ((ℕ × (ℕ → X)) × Y) → ℝ :=
    fun p => g p.2.2 (p.1 ::ₘ (Multiset.range p.2.1.1).map p.2.1.2) p.1 with hK
  have hKm : Measurable K := by
    have h1 : Measurable (fun r : ℕ × (Y × X × (ℕ → X)) =>
        g r.2.1 (r.2.2.1 ::ₘ (Multiset.range r.1).map r.2.2.2) r.2.2.1) :=
      measurable_from_prod_countable_right (fun n => hF n)
    have h2 : Measurable (fun p : X × ((ℕ × (ℕ → X)) × Y) => (p.2.1.1, (p.2.2, p.1, p.2.1.2))) := by
      fun_prop
    exact h1.comp h2
  -- generic lintegral Mecke for `u ∘ g`
  have mk : ∀ u : ℝ → ℝ, Measurable u → (∀ x, 0 ≤ u x) →
      ∫⁻ q, ENNReal.ofReal ((((Multiset.range q.1.1).map q.1.2).map
          (fun φ => u (g q.2 ((Multiset.range q.1.1).map q.1.2) φ))).sum) ∂M =
        (ρ : ℝ≥0∞) * ∫⁻ p, ENNReal.ofReal (u (K p)) ∂(Q.prod M) := by
    intro u hu hu0
    have e1 : ∀ q : (ℕ × (ℕ → X)) × Y, ENNReal.ofReal ((((Multiset.range q.1.1).map q.1.2).map
          (fun φ => u (g q.2 ((Multiset.range q.1.1).map q.1.2) φ))).sum) =
        (((Multiset.range q.1.1).map q.1.2).map
          (fun φ => ENNReal.ofReal (u (g q.2 ((Multiset.range q.1.1).map q.1.2) φ)))).sum := by
      intro q
      exact ofReal_msum _ _ (fun a => hu0 _)
    simp_rw [e1]
    rw [mecke ρ Q ν (fun y D φ => ENNReal.ofReal (u (g y D φ)))
      (fun n => ENNReal.measurable_ofReal.comp (hu.comp (hF n)))
      (sum_meas (fun y D φ => ENNReal.ofReal (u (g y D φ)))
        (fun n i hi => ENNReal.measurable_ofReal.comp (hu.comp (hG n i hi))))]
    congr 1
    exact (lintegral_prod (fun p => ENNReal.ofReal (u (K p)))
      (ENNReal.measurable_ofReal.comp (hu.comp hKm)).aemeasurable).symm
  -- integrability of K
  have habs := mk (fun x => |x|) continuous_abs.measurable (fun x => abs_nonneg x)
  have hfin : ∫⁻ q, ENNReal.ofReal ((((Multiset.range q.1.1).map q.1.2).map
      (fun φ => |g q.2 ((Multiset.range q.1.1).map q.1.2) φ|)).sum) ∂M < ∞ :=
    hint.lintegral_lt_top
  rw [habs] at hfin
  have hKfin : ∫⁻ p, ENNReal.ofReal (|K p|) ∂(Q.prod M) < ∞ := by
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon, ENNReal.mul_top (by exact_mod_cast hρ.ne')] at hfin
    exact lt_irrefl _ hfin
  have hKint : Integrable K (Q.prod M) := by
    refine ⟨hKm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simpa [← ofReal_norm_eq_enorm, Real.norm_eq_abs] using hKfin
  refine ⟨hKint, ?_⟩
  -- positive and negative parts
  have part : ∀ u : ℝ → ℝ, Measurable u → (∀ x, 0 ≤ u x) → (∀ x, u x ≤ |x|) →
      Integrable (fun q : (ℕ × (ℕ → X)) × Y => (((Multiset.range q.1.1).map q.1.2).map
          (fun φ => u (g q.2 ((Multiset.range q.1.1).map q.1.2) φ))).sum) M ∧
      ∫ q, (((Multiset.range q.1.1).map q.1.2).map
          (fun φ => u (g q.2 ((Multiset.range q.1.1).map q.1.2) φ))).sum ∂M =
        (ρ : ℝ) * ∫ p, u (K p) ∂(Q.prod M) := by
    intro u hu hu0 hule
    have hmeas : Measurable (fun q : (ℕ × (ℕ → X)) × Y => (((Multiset.range q.1.1).map q.1.2).map
          (fun φ => u (g q.2 ((Multiset.range q.1.1).map q.1.2) φ))).sum) :=
      sum_meas (fun y D φ => u (g y D φ)) (fun n i hi => hu.comp (hG n i hi))
    have hI : Integrable (fun q : (ℕ × (ℕ → X)) × Y => (((Multiset.range q.1.1).map q.1.2).map
          (fun φ => u (g q.2 ((Multiset.range q.1.1).map q.1.2) φ))).sum) M := by
      refine Integrable.mono' hint hmeas.aestronglyMeasurable (Filter.Eventually.of_forall
        (fun q => ?_))
      rw [Real.norm_of_nonneg (Multiset.sum_nonneg (fun x hx => by
        obtain ⟨b, -, rfl⟩ := Multiset.mem_map.1 hx; exact hu0 _))]
      exact Multiset.sum_map_le_sum_map _ _ (fun φ _ => hule _)
    have hKu : Integrable (fun p => u (K p)) (Q.prod M) :=
      Integrable.mono' hKint.norm (hu.comp hKm).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun p => by
          rw [Real.norm_of_nonneg (hu0 _), Real.norm_eq_abs]; exact hule _))
    refine ⟨hI, ?_⟩
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun q =>
        Multiset.sum_nonneg (fun x hx => by
          obtain ⟨b, -, rfl⟩ := Multiset.mem_map.1 hx; exact hu0 _))) hmeas.aestronglyMeasurable,
      mk u hu hu0,
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun p => hu0 _))
        (hu.comp hKm).aestronglyMeasurable,
      ENNReal.toReal_mul]
    simp
  have hpos := part (fun x => max x 0) (continuous_id.max continuous_const).measurable
    (fun x => le_max_right _ _) (fun x => max_le (le_abs_self x) (abs_nonneg x))
  have hneg := part (fun x => max (-x) 0) (continuous_neg.max continuous_const).measurable
    (fun x => le_max_right _ _) (fun x => max_le (neg_le_abs x) (abs_nonneg x))
  have hsplit : ∀ q : (ℕ × (ℕ → X)) × Y,
      (((Multiset.range q.1.1).map q.1.2).map (g q.2 ((Multiset.range q.1.1).map q.1.2))).sum =
      (((Multiset.range q.1.1).map q.1.2).map
          (fun φ => max (g q.2 ((Multiset.range q.1.1).map q.1.2) φ) 0)).sum -
      (((Multiset.range q.1.1).map q.1.2).map
          (fun φ => max (-g q.2 ((Multiset.range q.1.1).map q.1.2) φ) 0)).sum := by
    intro q
    rw [← Multiset.sum_map_sub]
    congr 1
    apply Multiset.map_congr rfl
    intro φ _
    rcases le_total 0 (g q.2 ((Multiset.range q.1.1).map q.1.2) φ) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  simp_rw [hsplit]
  rw [integral_sub hpos.1 hneg.1, hpos.2, hneg.2, ← mul_sub,
    ← integral_sub (hKint.pos_part) (hKint.neg_part)]
  · rw [← integral_prod _ hKint]
    congr 2
    funext p
    rcases le_total 0 (K p) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring

end TwoSidedMatching.MechBound.MeckeAux


open MeasureTheory Set

namespace TwoSidedMatching.MechBound.IBPAux

/-- `∫_{[lo,hi]} f(v) ∫_{lo}^{v} q = ∫_{[lo,hi]} q(v') ∫_{v'}^{hi} f`. -/
lemma ibp_core (lo hi : ℝ) (hlh : lo ≤ hi) (f q : ℝ → ℝ) (hf : Measurable f) (hq : Measurable q)
    (hfi : IntegrableOn f (Icc lo hi)) (hqb : ∀ v ∈ Icc lo hi, |q v| ≤ 1) :
    ∫ v in Icc lo hi, f v * (∫ v' in lo..v, q v') =
      ∫ v' in Icc lo hi, q v' * (∫ v in v'..hi, f v) := by
  set μL := volume.restrict (Icc lo hi) with hμL
  have hfin : IsFiniteMeasure μL := by
    rw [hμL]; exact isFiniteMeasure_restrict.2 (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  set H : ℝ → ℝ → ℝ := fun v v' => f v * (if v' ≤ v then q v' else 0) with hH
  have hHm : Measurable (Function.uncurry H) := by
    apply Measurable.mul (hf.comp measurable_fst)
    exact Measurable.ite (measurableSet_le measurable_snd measurable_fst)
      (hq.comp measurable_snd) measurable_const
  have hHi : Integrable (Function.uncurry H) (μL.prod μL) := by
    refine Integrable.mono' ((hfi.norm).comp_fst μL) hHm.aestronglyMeasurable ?_
    have hae : ∀ᵐ p ∂(μL.prod μL), p.2 ∈ Icc lo hi :=
      (Measure.quasiMeasurePreserving_snd (μ := μL) (ν := μL)).ae (ae_restrict_mem measurableSet_Icc)
    filter_upwards [hae] with p hp
    simp only [Function.uncurry, hH, norm_mul, Real.norm_eq_abs]
    have : |if p.2 ≤ p.1 then q p.2 else 0| ≤ 1 := by
      split_ifs
      · exact hqb _ hp
      · simp
    calc |f p.1| * |if p.2 ≤ p.1 then q p.2 else 0| ≤ |f p.1| * 1 :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = ‖f p.1‖ := by rw [mul_one, Real.norm_eq_abs]
  -- left side as an iterated integral
  have hL : ∀ v ∈ Icc lo hi, (∫ v' in lo..v, q v') = ∫ v', (if v' ≤ v then q v' else 0) ∂μL := by
    intro v hv
    have e1 : (fun v' => if v' ≤ v then q v' else 0) = (Iic v).indicator q := by
      funext v'; simp [Set.indicator, Set.mem_Iic]
    have e2 : Iic v ∩ Icc lo hi = Icc lo v := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hv.2⟩
    rw [e1, integral_indicator measurableSet_Iic, hμL, Measure.restrict_restrict measurableSet_Iic,
      e2, intervalIntegral.integral_of_le hv.1, ← integral_Icc_eq_integral_Ioc]
  have hR : ∀ v' ∈ Icc lo hi, ∫ v, H v v' ∂μL = q v' * ∫ v in v'..hi, f v := by
    intro v' hv'
    have e1 : (fun v => H v v') = fun v => q v' * (Ici v').indicator f v := by
      funext v
      simp only [hH, Set.indicator, Set.mem_Ici]
      split_ifs <;> ring
    have e2 : Ici v' ∩ Icc lo hi = Icc v' hi := by
      ext x; simp only [mem_inter_iff, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, hv'.1.trans h1, h2⟩
    rw [e1, integral_const_mul, integral_indicator measurableSet_Ici, hμL,
      Measure.restrict_restrict measurableSet_Ici, e2,
      intervalIntegral.integral_of_le hv'.2, ← integral_Icc_eq_integral_Ioc]
  calc ∫ v in Icc lo hi, f v * (∫ v' in lo..v, q v')
      = ∫ v, ∫ v', H v v' ∂μL ∂μL := by
        refine setIntegral_congr_fun measurableSet_Icc (fun v hv => ?_)
        simp only [hH]
        rw [hL v hv, ← integral_const_mul]
    _ = ∫ v', ∫ v, H v v' ∂μL ∂μL := integral_integral_swap hHi
    _ = ∫ v' in Icc lo hi, q v' * (∫ v in v'..hi, f v) :=
        setIntegral_congr_fun measurableSet_Icc (fun v' hv' => hR v' hv')

end TwoSidedMatching.MechBound.IBPAux


open MeasureTheory ProbabilityTheory MechanismDesign.BilateralTrade
open scoped ENNReal NNReal

namespace TwoSidedMatching.MechBound.S2Aux

open TwoSidedMatching.MechBound TwoSidedMatching.MechBound.MeckeAux

abbrev X2 := ℝ × ℝ

/-- seller multiset of a seller-side sample -/
def Sof (w : ℕ × (ℕ → ℝ × ℝ)) : Multiset (ℝ × ℝ) := (Multiset.range w.1).map w.2

lemma meas_hG (E : Environment) (lamD lamS T : ℝ) (y : Mechanism)
    (hwd : WellDefined E lamD lamS T y)
    (Gt : (ℝ × ℝ × ℝ) × (ℝ × ℝ) → ℝ) (hGt : Measurable Gt) :
    ∀ n i, i < n → Measurable (fun q : (ℕ × (ℕ → ℝ × ℝ)) × (ℕ → ℝ × ℝ) =>
      Gt (((y ((Multiset.range n).map q.2) (Sof q.1)).1 (q.2 i)).toTriple, q.2 i)) := by
  intro n i hi
  have h1 : Measurable (fun r : ℕ × ((ℕ → ℝ × ℝ) × (ℕ → ℝ × ℝ)) =>
      Gt (((y ((Multiset.range n).map r.2.1) ((Multiset.range r.1).map r.2.2)).1
        (r.2.1 i)).toTriple, r.2.1 i)) := by
    apply measurable_from_prod_countable_right
    intro k
    exact hGt.comp ((hwd.buyer_measurable n k i hi).prodMk
      ((measurable_pi_apply i).comp measurable_fst))
  have h2 : Measurable (fun q : (ℕ × (ℕ → ℝ × ℝ)) × (ℕ → ℝ × ℝ) => (q.1.1, (q.2, q.1.2))) := by
    fun_prop
  exact h1.comp h2

lemma meas_hF (E : Environment) (lamD lamS T : ℝ) (y : Mechanism)
    (hwd : WellDefined E lamD lamS T y)
    (Gt : (ℝ × ℝ × ℝ) × (ℝ × ℝ) → ℝ) (hGt : Measurable Gt) :
    ∀ n : ℕ, Measurable (fun q : (ℕ × (ℕ → ℝ × ℝ)) × (ℝ × ℝ) × (ℕ → ℝ × ℝ) =>
      Gt (((y (q.2.1 ::ₘ (Multiset.range n).map q.2.2) (Sof q.1)).1 q.2.1).toTriple, q.2.1)) := by
  classical
  intro n
  have h1 : Measurable (fun r : ℕ × ((ℝ × ℝ) × (ℕ → ℝ × ℝ) × (ℕ → ℝ × ℝ)) =>
      Gt (((y (r.2.1 ::ₘ (Multiset.range n).map r.2.2.1) ((Multiset.range r.1).map r.2.2.2)).1
        r.2.1).toTriple, r.2.1)) := by
    apply measurable_from_prod_countable_right
    intro k
    have hb := hwd.buyer_measurable (n + 1) k n (Nat.lt_succ_self n)
    have hu : Measurable (fun r : (ℝ × ℝ) × (ℕ → ℝ × ℝ) × (ℕ → ℝ × ℝ) =>
        (Function.update r.2.1 n r.1, r.2.2)) := by fun_prop
    have := hGt.comp ((hb.comp hu).prodMk measurable_fst)
    convert this using 1
    funext r
    simp only [Function.comp_apply, S1Aux.ins_eq, Function.update_self]
  have h2 : Measurable (fun q : (ℕ × (ℕ → ℝ × ℝ)) × (ℝ × ℝ) × (ℕ → ℝ × ℝ) =>
      (q.1.1, (q.2.1, q.2.2, q.1.2))) := by fun_prop
  exact h1.comp h2

lemma P_eq_prod (E : Environment) (lamD lamS T : ℝ) :
    P E lamD lamS T = ((poissonMeasure ⟨max (lamD * T) 0, le_max_right _ _⟩).prod
      (Measure.infinitePi (fun _ : ℕ => buyerMark E T))).prod
      (TwoSidedMatching.Guarantee.sideLaw lamS T (sellerMark E T)) := rfl

/-- Mecke for buyer-side sums of a function of the buyer's own outcome and type. -/
lemma mecke_buyer (E : Environment) (lamD lamS T : ℝ) (hlamD : 0 < lamD) (hT : 0 < T)
    (y : Mechanism) (hwd : WellDefined E lamD lamS T y)
    (Gt : (ℝ × ℝ × ℝ) × (ℝ × ℝ) → ℝ) (hGt : Measurable Gt)
    (hint : Integrable (fun ω => ((Hd ω).map (fun φ =>
      |Gt (((y (Hd ω) (Hs ω)).1 φ).toTriple, φ)|)).sum) (P E lamD lamS T)) :
    Integrable (fun p : (ℝ × ℝ) × TwoSidedMatching.Guarantee.Ω =>
        Gt (((y (p.1 ::ₘ Hd p.2) (Hs p.2)).1 p.1).toTriple, p.1))
      ((buyerMark E T).prod (P E lamD lamS T)) ∧
    ∫ ω, ((Hd ω).map (fun φ => Gt (((y (Hd ω) (Hs ω)).1 φ).toTriple, φ))).sum ∂P E lamD lamS T =
      (lamD * T) * ∫ φ, Eminus E lamD lamS T y φ (fun o => Gt (o.toTriple, φ)) ∂buyerMark E T := by
  have := S1Aux.P_prob E lamD lamS T hT
  have := TwoSidedMatching.Guarantee.MBCopy.timeLaw_prob T hT
  have hv : IsProbabilityMeasure (valLaw E) := TwoSidedMatching.Guarantee.MBCopy.valLaw_prob E
  have hc : IsProbabilityMeasure (costLaw E) := TwoSidedMatching.Guarantee.MBCopy.costLaw_prob E
  have hbm : IsProbabilityMeasure (buyerMark E T) := by unfold buyerMark; infer_instance
  have hsm : IsProbabilityMeasure (sellerMark E T) := by unfold sellerMark; infer_instance
  have hB : IsProbabilityMeasure (TwoSidedMatching.Guarantee.sideLaw lamS T (sellerMark E T)) :=
    TwoSidedMatching.Guarantee.MBCopy.sideLaw_prob _ _ _
  have hρ : (0 : ℝ≥0) < ⟨max (lamD * T) 0, le_max_right _ _⟩ := by
    show (0:ℝ) < max (lamD * T) 0
    exact lt_max_of_lt_left (mul_pos hlamD hT)
  have key := mecke_real ⟨max (lamD * T) 0, le_max_right _ _⟩ hρ (buyerMark E T)
    (TwoSidedMatching.Guarantee.sideLaw lamS T (sellerMark E T))
    (fun w D φ => Gt (((y D (Sof w)).1 φ).toTriple, φ))
    (meas_hG E lamD lamS T y hwd Gt hGt) (meas_hF E lamD lamS T y hwd Gt hGt)
    (by rw [← P_eq_prod]; exact hint)
  rw [← P_eq_prod] at key
  refine ⟨key.1, Eq.trans key.2 ?_⟩
  congr 1
  show max (lamD * T) 0 = lamD * T
  exact max_eq_left (mul_pos hlamD hT).le


lemma joint_meas (E : Environment) (lamD lamS T : ℝ) (y : Mechanism)
    (hwd : WellDefined E lamD lamS T y)
    (Gt : (ℝ × ℝ × ℝ) × (ℝ × ℝ) → ℝ) (hGt : Measurable Gt) :
    Measurable (fun p : (ℝ × ℝ) × TwoSidedMatching.Guarantee.Ω =>
      Gt (((y (p.1 ::ₘ Hd p.2) (Hs p.2)).1 p.1).toTriple, p.1)) := by
  have h1 : Measurable (fun r : ℕ × ((ℕ × (ℕ → ℝ × ℝ)) × (ℝ × ℝ) × (ℕ → ℝ × ℝ)) =>
      Gt (((y (r.2.2.1 ::ₘ (Multiset.range r.1).map r.2.2.2) (Sof r.2.1)).1 r.2.2.1).toTriple,
        r.2.2.1)) :=
    measurable_from_prod_countable_right (fun n => meas_hF E lamD lamS T y hwd Gt hGt n)
  have h2 : Measurable (fun p : (ℝ × ℝ) × TwoSidedMatching.Guarantee.Ω =>
      (p.2.1.1, (p.2.2, p.1, p.2.1.2))) := by fun_prop
  exact h1.comp h2

lemma Eminus_meas (E : Environment) (lamD lamS T : ℝ) (hT : 0 < T) (y : Mechanism)
    (hwd : WellDefined E lamD lamS T y)
    (Gt : (ℝ × ℝ × ℝ) × (ℝ × ℝ) → ℝ) (hGt : Measurable Gt) :
    Measurable (fun φ => Eminus E lamD lamS T y φ (fun o => Gt (o.toTriple, φ))) :=
  have := S1Aux.P_prob E lamD lamS T hT
  ((joint_meas E lamD lamS T y hwd Gt hGt).stronglyMeasurable.integral_prod_right'
    (ν := P E lamD lamS T)).measurable

lemma ae_buyerMark (E : Environment) (T : ℝ) (hT : 0 < T) :
    ∀ᵐ φ ∂(buyerMark E T), φ ∈ buyerTypes E T :=
  have := TwoSidedMatching.Guarantee.MBCopy.timeLaw_prob T hT
  have hv : IsProbabilityMeasure (valLaw E) := TwoSidedMatching.Guarantee.MBCopy.valLaw_prob E
  S1Aux.ae_mark _ _ _ _ (S1Aux.ae_time T) (S1Aux.ae_dens _ _ _)

lemma Qm_bound (E : Environment) (lamD lamS T : ℝ) (hT : 0 < T) (y : Mechanism)
    (hfeas : Feasible E T y) (φ : ℝ × ℝ) (hφ : φ ∈ buyerTypes E T) :
    |Eminus E lamD lamS T y φ (fun o => o.m)| ≤ 1 ∧
      |Eminus E lamD lamS T y φ (fun o => o.s - φ.1)| ≤ T := by
  have := S1Aux.P_prob E lamD lamS T hT
  have hae := S1Aux.outcome_ae E lamD lamS T hT y hfeas φ hφ
  constructor
  · have := norm_integral_le_of_norm_le_const (μ := P E lamD lamS T) (C := 1)
      (f := fun ω => ((y (φ ::ₘ Hd ω) (Hs ω)).1 φ).m) (by
        filter_upwards [hae] with ω hω
        rcases hω.2.2 with h0 | h1
        · rw [h0]; simp
        · rw [h1]; simp)
    show |∫ ω, ((y (φ ::ₘ Hd ω) (Hs ω)).1 φ).m ∂P E lamD lamS T| ≤ 1
    simpa [Real.norm_eq_abs] using this
  · have := norm_integral_le_of_norm_le_const (μ := P E lamD lamS T) (C := T)
      (f := fun ω => ((y (φ ::ₘ Hd ω) (Hs ω)).1 φ).s - φ.1) (by
        filter_upwards [hae] with ω hω
        obtain ⟨h1, h2, -⟩ := hω
        have h0 := hφ.1.1
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith)
    show |∫ ω, (((y (φ ::ₘ Hd ω) (Hs ω)).1 φ).s - φ.1) ∂P E lamD lamS T| ≤ T
    simpa [Real.norm_eq_abs] using this

/-- The integration-by-parts identity for one arrival time. -/
lemma ibp_valLaw (E : Environment) (q w : ℝ → ℝ) (hq : Measurable q) (hw : Measurable w)
    (hqb : ∀ v ∈ Set.Icc E.loB E.hiB, |q v| ≤ 1) (C : ℝ) (hwb : ∀ v ∈ Set.Icc E.loB E.hiB, |w v| ≤ C)
    (Cψ : ℝ) (hψ : ∀ v ∈ Set.Icc E.loB E.hiB, |E.psiB v| ≤ Cψ) (b : ℝ) :
    ∫ v, (v * q v - (∫ v' in E.loB..v, q v') - b * w v) ∂valLaw E =
      ∫ v, (E.psiB v * q v - b * w v) ∂valLaw E := by
  have hint := TwoSidedMatching.Guarantee.MBCopy.valLaw_integral E
  rw [show valLaw E = TwoSidedMatching.Guarantee.valLaw E from rfl, hint, hint]
  set L := Set.Icc E.loB E.hiB with hL
  have hfi : IntegrableOn E.fB L :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le E.loB_lt_hiB.le).1 E.fB_intervalIntegrable
  have hlo : ∀ᵐ v ∂(volume.restrict L), v ∈ L := ae_restrict_mem measurableSet_Icc
  have hIm : Measurable (fun v => ∫ v' in E.loB..v, q v') :=
    TwoSidedMatching.Guarantee.MBCopy.measurable_primitive E.loB q hq
  have hIb : ∀ v ∈ L, |∫ v' in E.loB..v, q v'| ≤ E.hiB - E.loB := by
    intro v hv
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := E.loB) (b := v) (C := 1)
      (f := q) (fun x hx => by
        rw [Set.uIoc_of_le hv.1] at hx
        rw [Real.norm_eq_abs]; exact hqb x ⟨hx.1.le, hx.2.trans hv.2⟩)
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hv.1] : (0:ℝ) ≤ v - E.loB)] at this
    linarith [hv.2]
  have bdd : ∀ (g : ℝ → ℝ), Measurable g → ∀ K, (∀ v ∈ L, |g v| ≤ K) →
      Integrable (fun v => E.fB v * g v) (volume.restrict L) := by
    intro g hg K hK
    have := Integrable.bdd_mul (c := K) hfi hg.aestronglyMeasurable (by
      filter_upwards [hlo] with v hv; rw [Real.norm_eq_abs]; exact hK v hv)
    refine this.congr (Filter.Eventually.of_forall (fun v => ?_))
    simp only; ring
  have i1 := bdd (fun v => v * q v) (measurable_id.mul hq) (|E.loB| + |E.hiB|) (by
    intro v hv; rw [abs_mul]
    have h1 : |v| ≤ |E.loB| + |E.hiB| := by
      rw [abs_le]; constructor
      · have := neg_abs_le E.loB; have := abs_nonneg E.hiB; linarith [hv.1]
      · have := le_abs_self E.hiB; have := abs_nonneg E.loB; linarith [hv.2]
    calc |v| * |q v| ≤ (|E.loB| + |E.hiB|) * 1 :=
          mul_le_mul h1 (hqb v hv) (abs_nonneg _) (by positivity)
      _ = _ := mul_one _)
  have i2 := bdd (fun v => ∫ v' in E.loB..v, q v') hIm _ hIb
  have i3 := bdd (fun v => b * w v) (measurable_const.mul hw) (|b| * C) (by
    intro v hv; rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hwb v hv) (abs_nonneg b))
  have i4 := bdd (fun v => E.psiB v * q v)
    ((TwoSidedMatching.Guarantee.MBCopy.measurable_psiB E).mul hq) (Cψ * 1) (by
      intro v hv; rw [abs_mul]
      exact mul_le_mul (hψ v hv) (hqb v hv) (abs_nonneg _) ((abs_nonneg _).trans (hψ v hv)))
  obtain ⟨-, hFmono, hF0, hF1⟩ := TwoSidedMatching.Guarantee.MBCopy.cdfB_props E
  have hFm : Measurable E.cdfB :=
    TwoSidedMatching.Guarantee.MBCopy.measurable_primitive E.loB E.fB E.fB_measurable
  have hFb : ∀ v ∈ L, 0 ≤ E.cdfB v ∧ E.cdfB v ≤ 1 := by
    intro v hv
    have hloL : E.loB ∈ L := ⟨le_rfl, E.loB_lt_hiB.le⟩
    have hhiL : E.hiB ∈ L := ⟨E.loB_lt_hiB.le, le_rfl⟩
    constructor
    · rw [← hF0]; exact hFmono.monotoneOn hloL hv hv.1
    · rw [← hF1]; exact hFmono.monotoneOn hv hhiL hv.2
  have hfin : IsFiniteMeasure (volume.restrict L) :=
    isFiniteMeasure_restrict.2 (by rw [hL, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have i6 : Integrable (fun v' => q v' * (1 - E.cdfB v')) (volume.restrict L) := by
    refine Integrable.of_bound (hq.mul (measurable_const.sub hFm)).aestronglyMeasurable 1 ?_
    filter_upwards [hlo] with v hv
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |1 - E.cdfB v| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [(hFb v hv).1, (hFb v hv).2]
    calc |q v| * |1 - E.cdfB v| ≤ 1 * 1 :=
          mul_le_mul (hqb v hv) h1 (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hJ : ∀ v' ∈ L, (∫ v in v'..E.hiB, E.fB v) = 1 - E.cdfB v' := by
    intro v' hv'
    have hac : IntervalIntegrable E.fB volume E.loB v' :=
      E.fB_intervalIntegrable.mono_set (by
        rw [Set.uIcc_of_le hv'.1, Set.uIcc_of_le E.loB_lt_hiB.le]
        exact Set.Icc_subset_Icc le_rfl hv'.2)
    have := intervalIntegral.integral_interval_sub_left E.fB_intervalIntegrable hac
    rw [E.fB_integral] at this
    show _ = 1 - ∫ z in E.loB..v', E.fB z
    linarith
  have hcore := TwoSidedMatching.MechBound.IBPAux.ibp_core E.loB E.hiB E.loB_lt_hiB.le E.fB q
    E.fB_measurable hq hfi hqb
  have hcore' : ∫ v in L, E.fB v * (∫ v' in E.loB..v, q v') =
      ∫ v' in L, q v' * (1 - E.cdfB v') :=
    hcore.trans (setIntegral_congr_fun measurableSet_Icc (fun v' hv' => by
      rw [hJ v' hv']))
  have hpsi : ∀ v ∈ L, E.fB v * (v * q v) - q v * (1 - E.cdfB v) = E.fB v * (E.psiB v * q v) := by
    intro v hv
    have hf0 := (E.fB_pos v hv).ne'
    unfold Environment.psiB
    field_simp
    try ring
  have i12 : Integrable (fun v => E.fB v * (v * q v) - E.fB v * (∫ v' in E.loB..v, q v'))
      (volume.restrict L) := i1.sub i2
  have i16 : Integrable (fun v => E.fB v * (v * q v) - q v * (1 - E.cdfB v))
      (volume.restrict L) := i1.sub i6
  calc ∫ v in L, E.fB v * (v * q v - (∫ v' in E.loB..v, q v') - b * w v)
      = ∫ v in L, (E.fB v * (v * q v) - E.fB v * (∫ v' in E.loB..v, q v') -
          E.fB v * (b * w v)) := by
        congr 1; funext v; ring
    _ = (∫ v in L, E.fB v * (v * q v)) - (∫ v in L, E.fB v * (∫ v' in E.loB..v, q v')) -
          ∫ v in L, E.fB v * (b * w v) := by
        rw [integral_sub i12 i3, integral_sub i1 i2]
    _ = (∫ v in L, E.fB v * (v * q v)) - (∫ v' in L, q v' * (1 - E.cdfB v')) -
          ∫ v in L, E.fB v * (b * w v) := by rw [hcore']
    _ = (∫ v in L, (E.fB v * (v * q v) - q v * (1 - E.cdfB v))) -
          ∫ v in L, E.fB v * (b * w v) := by rw [integral_sub i1 i6]
    _ = (∫ v in L, E.fB v * (E.psiB v * q v)) - ∫ v in L, E.fB v * (b * w v) := by
        rw [setIntegral_congr_fun measurableSet_Icc hpsi]
    _ = ∫ v in L, E.fB v * (E.psiB v * q v - b * w v) := by
        rw [← integral_sub i4 i3]; congr 1; funext v; ring

end TwoSidedMatching.MechBound.S2Aux

open TwoSidedMatching.MechBound TwoSidedMatching.MechBound.S2Aux TwoSidedMatching.MechBound.MeckeAux

theorem solution
    (E : Environment)
    (hfB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hfS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hcv : E.loS ≤ E.hiB)
    (lamD lamS T b h : ℝ) (hlamD : 0 < lamD) (hlamS : 0 < lamS) (hT : 0 < T)
    (hb : 0 ≤ b) (hh : 0 ≤ h)
    (y : Mechanism) (hfeas : Feasible E T y) (hwd : WellDefined E lamD lamS T y)
    (hIC : ICd' E lamD lamS T b y) (hIR : IRd E lamD lamS T b y) :
    Integrable (fun ω => ((Hd ω).map (fun φ =>
        E.psiB φ.2 * ((y (Hd ω) (Hs ω)).1 φ).m - b * (((y (Hd ω) (Hs ω)).1 φ).s - φ.1))).sum)
      (P E lamD lamS T) ∧
    ∫ ω, ((Hd ω).map (fun φ => ((y (Hd ω) (Hs ω)).1 φ).p)).sum ∂P E lamD lamS T ≤
      ∫ ω, ((Hd ω).map (fun φ =>
        E.psiB φ.2 * ((y (Hd ω) (Hs ω)).1 φ).m - b * (((y (Hd ω) (Hs ω)).1 φ).s - φ.1))).sum
        ∂P E lamD lamS T := by
  classical
  have hPprob := S1Aux.P_prob E lamD lamS T hT
  have htl := TwoSidedMatching.Guarantee.MBCopy.timeLaw_prob T hT
  have hvl : IsProbabilityMeasure (valLaw E) := TwoSidedMatching.Guarantee.MBCopy.valLaw_prob E
  have hcl : IsProbabilityMeasure (costLaw E) := TwoSidedMatching.Guarantee.MBCopy.costLaw_prob E
  have hbm : IsProbabilityMeasure (buyerMark E T) := by unfold buyerMark; infer_instance
  have hsm : IsProbabilityMeasure (sellerMark E T) := by unfold sellerMark; infer_instance
  have hB : IsProbabilityMeasure (TwoSidedMatching.Guarantee.sideLaw lamS T (sellerMark E T)) :=
    TwoSidedMatching.Guarantee.MBCopy.sideLaw_prob _ _ _
  have hψm := TwoSidedMatching.Guarantee.MBCopy.measurable_psiB E
  obtain ⟨Cψ, hCψ⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (TwoSidedMatching.Guarantee.MBCopy.psiB_cont E hfB)
  have hCψ' : ∀ v ∈ Set.Icc E.loB E.hiB, |E.psiB v| ≤ Cψ := fun v hv => by
    have := hCψ v hv; rwa [Real.norm_eq_abs] at this
  have hCψ0 : 0 ≤ Cψ := (abs_nonneg _).trans (hCψ' E.loB ⟨le_rfl, E.loB_lt_hiB.le⟩)
  -- the two integrands
  set GtP : (ℝ × ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun x => x.1.2.2 with hGtP
  set GtV : (ℝ × ℝ × ℝ) × (ℝ × ℝ) → ℝ :=
    fun x => E.psiB x.2.2 * x.1.2.1 - b * (x.1.1 - x.2.1) with hGtV
  have mGtP : Measurable GtP := by rw [hGtP]; fun_prop
  have mGtV : Measurable GtV := by rw [hGtV]; fun_prop
  have mGtVa : Measurable (fun x => |GtV x|) := continuous_abs.measurable.comp mGtV
  -- integrability of the number of buyers
  have hN : Integrable (fun ω : TwoSidedMatching.Guarantee.Ω => (ω.1.1 : ℝ)) (P E lamD lamS T) := by
    have m1 : MeasurePreserving Prod.fst
        ((poissonMeasure ⟨max (lamD * T) 0, le_max_right _ _⟩).prod
          (Measure.infinitePi (fun _ : ℕ => buyerMark E T)))
        (poissonMeasure ⟨max (lamD * T) 0, le_max_right _ _⟩) := measurePreserving_fst
    have i1 := m1.integrable_comp_of_integrable
      (TwoSidedMatching.Guarantee.MBCopy.poisson_integrable_id ⟨max (lamD * T) 0, le_max_right _ _⟩)
    have m2 : MeasurePreserving Prod.fst (P E lamD lamS T)
        (TwoSidedMatching.Guarantee.sideLaw lamD T (buyerMark E T)) := measurePreserving_fst
    exact m2.integrable_comp_of_integrable i1
  have hVint : Integrable (fun ω => ((Hd ω).map (fun φ =>
      |GtV (((y (Hd ω) (Hs ω)).1 φ).toTriple, φ)|)).sum) (P E lamD lamS T) := by
    have hm : Measurable (fun ω : TwoSidedMatching.Guarantee.Ω => ((Hd ω).map (fun φ =>
        |GtV (((y (Hd ω) (Hs ω)).1 φ).toTriple, φ)|)).sum) :=
      sum_meas (fun w D φ => |GtV (((y D (Sof w)).1 φ).toTriple, φ)|)
        (meas_hG E lamD lamS T y hwd (fun x => |GtV x|) mGtVa)
    refine Integrable.mono' (hN.mul_const (Cψ + b * T)) hm.aestronglyMeasurable ?_
    filter_upwards [S1Aux.ae_types E lamD lamS T hT] with ω hω
    obtain ⟨f1, -, -⟩ := hfeas (Hd ω) (Hs ω) hω.1 hω.2
    rw [Real.norm_of_nonneg (Multiset.sum_nonneg (fun x hx => by
      obtain ⟨c, -, rfl⟩ := Multiset.mem_map.1 hx; exact abs_nonneg _))]
    have hbound : ∀ φ ∈ Hd ω, |GtV (((y (Hd ω) (Hs ω)).1 φ).toTriple, φ)| ≤ Cψ + b * T := by
      intro φ hφ
      obtain ⟨h1, h2, hm⟩ := f1 φ hφ
      have ht0 := (hω.1 φ hφ).1.1
      simp only [hGtV, Outcome.toTriple]
      have e1 : |E.psiB φ.2 * ((y (Hd ω) (Hs ω)).1 φ).m| ≤ Cψ := by
        rw [abs_mul]
        rcases hm with h0 | h1'
        · rw [h0]; simp [hCψ0]
        · rw [h1', abs_one, mul_one]; exact hCψ' _ (hω.1 φ hφ).2
      have e2 : |b * (((y (Hd ω) (Hs ω)).1 φ).s - φ.1)| ≤ b * T := by
        rw [abs_mul, abs_of_nonneg hb]
        exact mul_le_mul_of_nonneg_left (by rw [abs_le]; constructor <;> linarith) hb
      calc _ ≤ |E.psiB φ.2 * ((y (Hd ω) (Hs ω)).1 φ).m| +
            |b * (((y (Hd ω) (Hs ω)).1 φ).s - φ.1)| := abs_sub _ _
        _ ≤ Cψ + b * T := add_le_add e1 e2
    calc ((Hd ω).map (fun φ => |GtV (((y (Hd ω) (Hs ω)).1 φ).toTriple, φ)|)).sum
        ≤ ((Hd ω).map (fun _ => Cψ + b * T)).sum := Multiset.sum_map_le_sum_map _ _ hbound
      _ = (ω.1.1 : ℝ) * (Cψ + b * T) := by
        rw [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul]
        simp [Hd]
  obtain ⟨hKP, eqP⟩ := mecke_buyer E lamD lamS T hlamD hT y hwd GtP mGtP
    hwd.buyer_payments_integrable
  obtain ⟨hKV, eqV⟩ := mecke_buyer E lamD lamS T hlamD hT y hwd GtV mGtV hVint
  refine ⟨?_, ?_⟩
  · -- integrability of the right-hand side
    have hm : Measurable (fun ω : TwoSidedMatching.Guarantee.Ω => ((Hd ω).map (fun φ =>
        GtV (((y (Hd ω) (Hs ω)).1 φ).toTriple, φ))).sum) :=
      sum_meas (fun w D φ => GtV (((y D (Sof w)).1 φ).toTriple, φ))
        (meas_hG E lamD lamS T y hwd GtV mGtV)
    refine Integrable.mono' hVint hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs]
    exact Multiset.abs_sum_le_sum_abs.trans (le_of_eq (by rw [Multiset.map_map]; rfl))
  · show ∫ ω, ((Hd ω).map (fun φ => GtP (((y (Hd ω) (Hs ω)).1 φ).toTriple, φ))).sum
        ∂P E lamD lamS T ≤
      ∫ ω, ((Hd ω).map (fun φ => GtV (((y (Hd ω) (Hs ω)).1 φ).toTriple, φ))).sum ∂P E lamD lamS T
    rw [eqP, eqV]
    apply mul_le_mul_of_nonneg_left _ (mul_pos hlamD hT).le
    -- notation
    set Qm : ℝ × ℝ → ℝ := fun φ => Eminus E lamD lamS T y φ (fun o => o.m) with hQm
    set W : ℝ × ℝ → ℝ := fun φ => Eminus E lamD lamS T y φ (fun o => o.s - φ.1) with hW
    have mQm : Measurable Qm := Eminus_meas E lamD lamS T hT y hwd (fun x => x.1.2.1) (by fun_prop)
    have mW : Measurable W := Eminus_meas E lamD lamS T hT y hwd (fun x => x.1.1 - x.2.1)
      (by fun_prop)
    have hPpi : Integrable (fun φ => Eminus E lamD lamS T y φ (fun o => GtP (o.toTriple, φ)))
        (buyerMark E T) := hKP.integral_prod_left
    have hEVi : Integrable (fun φ => Eminus E lamD lamS T y φ (fun o => GtV (o.toTriple, φ)))
        (buyerMark E T) := hKV.integral_prod_left
    -- the virtual-value integrand, simplified
    have hlin : ∀ φ ∈ buyerTypes E T,
        Eminus E lamD lamS T y φ (fun o => GtV (o.toTriple, φ)) =
          E.psiB φ.2 * Qm φ - b * W φ := by
      intro φ hφ
      obtain ⟨im, is, -⟩ := S1Aux.comp_integrable E lamD lamS T hT y hfeas hwd φ hφ
      simp only [hQm, hW, hGtV, Eminus, Outcome.toTriple]
      have i1 := im.const_mul (E.psiB φ.2)
      have i2 : Integrable (fun ω => b * (((y (φ ::ₘ Hd ω) (Hs ω)).1 φ).s - φ.1))
          (P E lamD lamS T) := (is.sub (integrable_const φ.1)).const_mul b
      rw [integral_sub i1 i2, integral_const_mul, integral_const_mul]
    have hEVae : (fun φ => Eminus E lamD lamS T y φ (fun o => GtV (o.toTriple, φ))) =ᵐ[buyerMark E T]
        (fun φ => E.psiB φ.2 * Qm φ - b * W φ) := by
      filter_upwards [ae_buyerMark E T hT] with φ hφ
      exact hlin φ hφ
    have hG2i : Integrable (fun φ => E.psiB φ.2 * Qm φ - b * W φ) (buyerMark E T) :=
      hEVi.congr hEVae
    rw [integral_congr_ae hEVae]
    have hbmdef : buyerMark E T = (TwoSidedMatching.Guarantee.timeLaw T).prod (valLaw E) := rfl
    rw [hbmdef] at hPpi hG2i ⊢
    rw [integral_prod _ hPpi, integral_prod _ hG2i]
    apply integral_mono_ae hPpi.integral_prod_left hG2i.integral_prod_left
    filter_upwards [S1Aux.ae_time T, hPpi.prod_right_ae] with t ht hPt
    -- fixed arrival time `t`
    have hq : Measurable (fun v => Qm (t, v)) := mQm.comp (measurable_const.prodMk measurable_id)
    have hw : Measurable (fun v => W (t, v)) := mW.comp (measurable_const.prodMk measurable_id)
    have hqb : ∀ v ∈ Set.Icc E.loB E.hiB, |Qm (t, v)| ≤ 1 := fun v hv =>
      (Qm_bound E lamD lamS T hT y hfeas (t, v) ⟨ht, hv⟩).1
    have hwb : ∀ v ∈ Set.Icc E.loB E.hiB, |W (t, v)| ≤ T := fun v hv =>
      (Qm_bound E lamD lamS T hT y hfeas (t, v) ⟨ht, hv⟩).2
    have hval : ∀ᵐ v ∂(valLaw E), v ∈ Set.Icc E.loB E.hiB := S1Aux.ae_dens _ _ _
    have hIm : Measurable (fun v => ∫ v' in E.loB..v, Qm (t, v')) :=
      TwoSidedMatching.Guarantee.MBCopy.measurable_primitive E.loB _ hq
    have hmid : Integrable (fun v => v * Qm (t, v) - (∫ v' in E.loB..v, Qm (t, v')) - b * W (t, v))
        (valLaw E) := by
      refine Integrable.of_bound (((measurable_id.mul hq).sub hIm).sub
        (measurable_const.mul hw)).aestronglyMeasurable
        ((|E.loB| + |E.hiB|) + (E.hiB - E.loB) + b * T) ?_
      filter_upwards [hval] with v hv
      rw [Real.norm_eq_abs]
      have a1 : |v * Qm (t, v)| ≤ |E.loB| + |E.hiB| := by
        rw [abs_mul]
        have h1 : |v| ≤ |E.loB| + |E.hiB| := by
          rw [abs_le]; constructor
          · have := neg_abs_le E.loB; have := abs_nonneg E.hiB; linarith [hv.1]
          · have := le_abs_self E.hiB; have := abs_nonneg E.loB; linarith [hv.2]
        calc |v| * |Qm (t, v)| ≤ (|E.loB| + |E.hiB|) * 1 :=
              mul_le_mul h1 (hqb v hv) (abs_nonneg _) (by positivity)
          _ = _ := mul_one _
      have a2 : |∫ v' in E.loB..v, Qm (t, v')| ≤ E.hiB - E.loB := by
        have := intervalIntegral.norm_integral_le_of_norm_le_const (a := E.loB) (b := v) (C := 1)
          (f := fun v' => Qm (t, v')) (fun x hx => by
            rw [Set.uIoc_of_le hv.1] at hx
            rw [Real.norm_eq_abs]; exact hqb x ⟨hx.1.le, hx.2.trans hv.2⟩)
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hv.1] : (0:ℝ) ≤ v - E.loB)] at this
        linarith [hv.2]
      have a3 : |b * W (t, v)| ≤ b * T := by
        rw [abs_mul, abs_of_nonneg hb]; exact mul_le_mul_of_nonneg_left (hwb v hv) hb
      calc |v * Qm (t, v) - (∫ v' in E.loB..v, Qm (t, v')) - b * W (t, v)|
          ≤ |v * Qm (t, v)| + |∫ v' in E.loB..v, Qm (t, v')| + |b * W (t, v)| := by
            have := abs_sub (v * Qm (t, v) - ∫ v' in E.loB..v, Qm (t, v')) (b * W (t, v))
            have := abs_sub (v * Qm (t, v)) (∫ v' in E.loB..v, Qm (t, v'))
            linarith
        _ ≤ _ := by linarith
    have hS1 := TwoSidedMatching.MechBound.lemma_S1 E hfB hfS hreg hcv lamD lamS T b h hlamD hlamS
      hT hb hh y hfeas hwd hIC hIR
    calc ∫ v, Eminus E lamD lamS T y (t, v) (fun o => GtP (o.toTriple, (t, v))) ∂valLaw E
        ≤ ∫ v, (v * Qm (t, v) - (∫ v' in E.loB..v, Qm (t, v')) - b * W (t, v)) ∂valLaw E := by
          refine integral_mono_ae ?_ hmid ?_
          · exact hPt
          · filter_upwards [hval] with v hv
            exact (hS1 (t, v) ⟨ht, hv⟩).2
      _ = ∫ v, (E.psiB v * Qm (t, v) - b * W (t, v)) ∂valLaw E :=
          ibp_valLaw E _ _ hq hw hqb T hwb Cψ hCψ' b
