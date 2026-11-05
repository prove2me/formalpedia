-- Prove2me | solution 1 for TwoSidedMatching.MechBound.lemma_1_mechanism_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T21:09:31.018601+00:00
-- url     : https://prove2.me/submissions/d8803ce2-3121-44aa-85df-8d7953088646

import Mathlib
import Definitions.Def_TwoSidedMatching_MechBound_Mechanism
import Theorems.Thm_TwoSidedMatching_MechBound_lemma_S2
import Theorems.Thm_TwoSidedMatching_MechBound_lemma_S4
import Theorems.Thm_TwoSidedMatching_MechBound_pathwise_bound

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

namespace TwoSidedMatching.MechBound.RedAux

open TwoSidedMatching.MechBound

/-! ### Reindexing the assignment value -/

lemma worth_le_of_equiv {M N M' N' : Type*} [Fintype M] [Fintype N] [Fintype M'] [Fintype N']
    (a : M → N → ℝ) (a' : M' → N' → ℝ) (eM : M ≃ M') (eN : N ≃ N')
    (h : ∀ i j, a' (eM i) (eN j) = a i j) :
    AssignmentGame.CoreLP.worth a Finset.univ Finset.univ ≤
      AssignmentGame.CoreLP.worth a' Finset.univ Finset.univ := by
  classical
  unfold AssignmentGame.CoreLP.worth
  apply Finset.sup'_le
  intro P hP
  unfold AssignmentGame.CoreLP.matchings at hP
  rw [Finset.mem_filter] at hP
  obtain ⟨-, -, h1, h2⟩ := hP
  let emb : M × N ↪ M' × N' := (eM.prodCongr eN).toEmbedding
  have hP' : P.map emb ∈ AssignmentGame.CoreLP.matchings
      (Finset.univ : Finset M') (Finset.univ : Finset N') := by
    unfold AssignmentGame.CoreLP.matchings
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_powerset.2 (by intro p _; simp), by intro p _; simp, ?_, ?_⟩
    · intro p hp q hq hpq
      rw [Finset.mem_map] at hp hq
      obtain ⟨p0, hp0, rfl⟩ := hp
      obtain ⟨q0, hq0, rfl⟩ := hq
      have : p0.1 = q0.1 := eM.injective hpq
      rw [h1 p0 hp0 q0 hq0 this]
    · intro p hp q hq hpq
      rw [Finset.mem_map] at hp hq
      obtain ⟨p0, hp0, rfl⟩ := hp
      obtain ⟨q0, hq0, rfl⟩ := hq
      have : p0.2 = q0.2 := eN.injective hpq
      rw [h2 p0 hp0 q0 hq0 this]
  refine le_trans (le_of_eq ?_) (Finset.le_sup' (fun P => ∑ p ∈ P, a' p.1 p.2) hP')
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  exact (h p.1 p.2).symm

lemma worth_eq_of_equiv {M N M' N' : Type*} [Fintype M] [Fintype N] [Fintype M'] [Fintype N']
    (a : M → N → ℝ) (a' : M' → N' → ℝ) (eM : M ≃ M') (eN : N ≃ N')
    (h : ∀ i j, a' (eM i) (eN j) = a i j) :
    AssignmentGame.CoreLP.worth a Finset.univ Finset.univ =
      AssignmentGame.CoreLP.worth a' Finset.univ Finset.univ :=
  le_antisymm (worth_le_of_equiv a a' eM eN h)
    (worth_le_of_equiv a' a eM.symm eN.symm (fun i j => by
      rw [← h]; simp))

lemma sum_fin_get' {X : Type*} (L : List X) (g : X → ℝ) :
    ∑ i : Fin L.length, g (L.get i) = (L.map g).sum := by
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_getElem <;> simp

lemma map_ite_sum' {X : Type*} (L : List X) (p : X → Prop) [DecidablePred p] :
    ((L.map (fun x => if p x then (1:ℝ) else 0)).sum) = ((L.filter p).length : ℝ) := by
  induction L with
  | nil => simp
  | cons a l ih =>
    by_cases ha : p a
    · simp [ha, List.filter_cons, ih]; ring
    · simp [ha, List.filter_cons, ih]

lemma card_idx' {X : Type*} (L : List X) (p : X → Prop) [DecidablePred p] :
    Fintype.card {i : Fin L.length // p (L.get i)} = (L.filter p).length := by
  rw [Fintype.card_subtype, Finset.card_filter]
  have h1 : (∑ i : Fin L.length, (if p (L.get i) then (1:ℝ) else 0)) =
      (L.map (fun x => if p x then (1:ℝ) else 0)).sum :=
    sum_fin_get' L (fun x => if p x then (1:ℝ) else 0)
  have h2 := map_ite_sum' L p
  have h3 : ((∑ i : Fin L.length, (if p (L.get i) then 1 else 0) : ℕ) : ℝ) =
      ∑ i : Fin L.length, (if p (L.get i) then (1:ℝ) else 0) := by
    push_cast; rfl
  exact_mod_cast h3.trans (h1.trans h2)

lemma idx_equiv {X : Type*} (L : List X) (n : ℕ) (z : ℕ → X)
    (hL : (L : Multiset X) = (Multiset.range n).map z) :
    ∃ e : Fin L.length ≃ Fin n, ∀ i, z (e i) = L.get i := by
  classical
  set L' : List X := (List.range n).map z with hL'
  have hperm : L.Perm L' := by
    rw [← Multiset.coe_eq_coe, hL, hL']
    rfl
  have hlen : L'.length = n := by simp [hL']
  have hget : ∀ i : Fin L'.length, L'.get i = z i := by
    intro i; simp [hL']
  have hcard : ∀ x : X, Fintype.card {i : Fin L.length // L.get i = x} =
      Fintype.card {i : Fin n // (fun i : Fin n => z i) i = x} := by
    intro x
    have c1 := card_idx' L (fun y => y = x)
    have c2 := card_idx' L' (fun y => y = x)
    have c3 : Fintype.card {i : Fin n // z i = x} =
        Fintype.card {i : Fin L'.length // L'.get i = x} := by
      apply Fintype.card_congr
      refine (Equiv.subtypeEquiv (finCongr hlen.symm) ?_)
      intro i
      rw [hget]
      rfl
    have c4 : (L.filter (fun y => decide (y = x))).length =
        (L'.filter (fun y => decide (y = x))).length :=
      (hperm.filter _).length_eq
    show _ = Fintype.card {i : Fin n // z i = x}
    rw [c3]
    exact c1.trans (c4.trans c2.symm)
  refine ⟨(Equiv.ofFiberEquiv (fun x => Fintype.equivOfCardEq (hcard x))), fun i => ?_⟩
  exact Equiv.ofFiberEquiv_map (f := L.get) (g := fun i : Fin n => z i) _ i

lemma Jbar_eq_guarantee (E : Environment) (b h : ℝ) (ω : TwoSidedMatching.Guarantee.Ω) :
    Jbar E b h ω = TwoSidedMatching.Guarantee.Jbar E b h ω := by
  obtain ⟨eD, heD⟩ := idx_equiv (Hd ω).toList ω.1.1 ω.1.2 (by rw [Multiset.coe_toList]; rfl)
  obtain ⟨eS, heS⟩ := idx_equiv (Hs ω).toList ω.2.1 ω.2.2 (by rw [Multiset.coe_toList]; rfl)
  unfold Jbar JbarProfile TwoSidedMatching.Guarantee.Jbar
  refine worth_eq_of_equiv _ _ eS eD (fun j i => ?_)
  unfold TwoSidedMatching.Guarantee.assignmentWeight weight
  unfold TwoSidedMatching.Guarantee.buyerValue TwoSidedMatching.Guarantee.sellerCost
    TwoSidedMatching.Guarantee.buyerTime TwoSidedMatching.Guarantee.sellerTime
  rw [heD i, heS j]

lemma P_eq (E : Environment) (lamD lamS T : ℝ) :
    P E lamD lamS T = TwoSidedMatching.Guarantee.P E lamD lamS T := rfl

lemma Jbar_integrable (E : Environment) (lamD lamS T b h : ℝ)
    (hfB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hfS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hd : 0 < lamD) (hs : 0 < lamS) (hT : 0 < T) (hb : 0 ≤ b) (hh : 0 ≤ h) :
    Integrable (Jbar E b h) (P E lamD lamS T) := by
  have e : Jbar E b h = TwoSidedMatching.Guarantee.Jbar E b h := funext (Jbar_eq_guarantee E b h)
  rw [e, P_eq]
  obtain ⟨hSint, -⟩ := TwoSidedMatching.Guarantee.MBCopy.Seta_facts E lamD lamS T 0 hfB hfS hd hs hT
  exact Integrable.mono' hSint
    (TwoSidedMatching.Guarantee.MBCopy.Jbar_measurable E b h).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_of_nonneg (TwoSidedMatching.Guarantee.MBCopy.Jbar_nonneg E b h ω)]
      exact TwoSidedMatching.Guarantee.MBCopy.Jbar_le E b h 0 hb hh ω))

/-! ### Measurability of per-side sums -/

lemma side_sum_measurable (F : ℕ → ℕ → ((ℕ → ℝ × ℝ) × (ℕ → ℝ × ℝ)) → ℕ → ℝ)
    (sel : ℕ × ℕ → ℕ)
    (hF : ∀ n k i, i < sel (n, k) → Measurable (fun z => F n k z i)) :
    Measurable (fun ω : TwoSidedMatching.Guarantee.Ω =>
      ∑ i ∈ Finset.range (sel (ω.1.1, ω.2.1)), F ω.1.1 ω.2.1 (ω.1.2, ω.2.2) i) := by
  have hG : Measurable (fun p : (ℕ × ℕ) × ((ℕ → ℝ × ℝ) × (ℕ → ℝ × ℝ)) =>
      ∑ i ∈ Finset.range (sel p.1), F p.1.1 p.1.2 p.2 i) := by
    apply measurable_from_prod_countable_right
    intro nk
    exact Finset.measurable_sum _ (fun i hi => hF nk.1 nk.2 i (Finset.mem_range.1 hi))
  have hpre : Measurable (fun ω : TwoSidedMatching.Guarantee.Ω =>
      ((ω.1.1, ω.2.1), (ω.1.2, ω.2.2))) := by fun_prop
  exact hG.comp hpre

lemma buyer_pay_measurable (E : Environment) (lamD lamS T : ℝ) (y : Mechanism)
    (hwd : WellDefined E lamD lamS T y) :
    Measurable (fun ω => ((Hd ω).map (fun φ => ((y (Hd ω) (Hs ω)).1 φ).p)).sum) := by
  have := side_sum_measurable
    (fun n k z i => ((y ((Multiset.range n).map z.1) ((Multiset.range k).map z.2)).1 (z.1 i)).p)
    (fun nk => nk.1)
    (fun n k i hi => (hwd.buyer_measurable n k i hi).snd.snd)
  convert this using 2 with ω
  simp only [Hd, Hs, Multiset.map_map]
  rfl

lemma seller_pay_measurable (E : Environment) (lamD lamS T : ℝ) (y : Mechanism)
    (hwd : WellDefined E lamD lamS T y) :
    Measurable (fun ω => ((Hs ω).map (fun ψ => ((y (Hd ω) (Hs ω)).2 ψ).p)).sum) := by
  have := side_sum_measurable
    (fun n k z i => ((y ((Multiset.range n).map z.1) ((Multiset.range k).map z.2)).2 (z.2 i)).p)
    (fun nk => nk.2)
    (fun n k i hi => (hwd.seller_measurable n k i hi).snd.snd)
  convert this using 2 with ω
  simp only [Hd, Hs, Multiset.map_map]
  rfl

/-! ### Almost every realized type lies in the type space -/

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

end TwoSidedMatching.MechBound.RedAux

open TwoSidedMatching.MechBound TwoSidedMatching.MechBound.RedAux

theorem solution
    (E : Environment)
    (hfB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hfS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hcv : E.loS ≤ E.hiB)
    (lamD lamS T b h : ℝ) (hlamD : 0 < lamD) (hlamS : 0 < lamS) (hT : 0 < T)
    (hb : 0 ≤ b) (hh : 0 ≤ h)
    (y : Mechanism) (hfeas : Feasible E T y) (hwd : WellDefined E lamD lamS T y)
    (hICd : ICd E lamD lamS T b y) (hIRd : IRd E lamD lamS T b y)
    (hICs : ICs E lamD lamS T h y) (hIRs : IRs E lamD lamS T h y) :
    Integrable (Jbar E b h) (P E lamD lamS T) ∧
      ∫ ω, profit y ω ∂P E lamD lamS T ≤ ∫ ω, Jbar E b h ω ∂P E lamD lamS T := by
  have hJ := Jbar_integrable E lamD lamS T b h hfB hfS hlamD hlamS hT hb hh
  refine ⟨hJ, ?_⟩
  -- (ICd′), (ICs′) are special cases of (ICd), (ICs)
  have hICd' : ICd' E lamD lamS T b y := fun φ hφ v' hv' =>
    hICd φ hφ (φ.1, v') ⟨hφ.1, hv'⟩ le_rfl
  have hICs' : ICs' E lamD lamS T h y := fun ψ hψ c' hc' =>
    hICs ψ hψ (ψ.1, c') ⟨hψ.1, hc'⟩ le_rfl
  obtain ⟨hRAi, hS2⟩ := lemma_S2 E hfB hfS hreg hcv lamD lamS T b h hlamD hlamS hT hb hh y
    hfeas hwd hICd' hIRd
  obtain ⟨hRBi, hS4⟩ := lemma_S4 E hfB hfS hreg hcv lamD lamS T b h hlamD hlamS hT hb hh y
    hfeas hwd hICs' hIRs
  -- integrability of the two payment sums
  have hAi : Integrable (fun ω => ((Hd ω).map (fun φ => ((y (Hd ω) (Hs ω)).1 φ).p)).sum)
      (P E lamD lamS T) :=
    Integrable.mono' hwd.buyer_payments_integrable
      (buyer_pay_measurable E lamD lamS T y hwd).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs]
        exact Multiset.abs_sum_le_sum_abs.trans (le_of_eq (by rw [Multiset.map_map]; rfl))))
  have hBi : Integrable (fun ω => ((Hs ω).map (fun ψ => ((y (Hd ω) (Hs ω)).2 ψ).p)).sum)
      (P E lamD lamS T) :=
    Integrable.mono' hwd.seller_payments_integrable
      (seller_pay_measurable E lamD lamS T y hwd).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs]
        exact Multiset.abs_sum_le_sum_abs.trans (le_of_eq (by rw [Multiset.map_map]; rfl))))
  have hprofit : ∫ ω, profit y ω ∂P E lamD lamS T =
      (∫ ω, ((Hd ω).map (fun φ => ((y (Hd ω) (Hs ω)).1 φ).p)).sum ∂P E lamD lamS T) -
      ∫ ω, ((Hs ω).map (fun ψ => ((y (Hd ω) (Hs ω)).2 ψ).p)).sum ∂P E lamD lamS T :=
    integral_sub hAi hBi
  -- pathwise bound, almost surely
  have hpath : ∀ᵐ ω ∂(P E lamD lamS T),
      ((Hd ω).map (fun φ => E.psiB φ.2 * ((y (Hd ω) (Hs ω)).1 φ).m -
          b * (((y (Hd ω) (Hs ω)).1 φ).s - φ.1))).sum -
        ((Hs ω).map (fun ψ => E.psiS ψ.2 * ((y (Hd ω) (Hs ω)).2 ψ).m +
          h * (((y (Hd ω) (Hs ω)).2 ψ).s - ψ.1))).sum ≤ Jbar E b h ω := by
    filter_upwards [ae_types E lamD lamS T hT] with ω hω
    obtain ⟨f1, f2, f3⟩ := hfeas (Hd ω) (Hs ω) hω.1 hω.2
    exact pathwise_bound E hfB hfS hreg hcv lamD lamS T b h hlamD hlamS hT hb hh (Hd ω) (Hs ω)
      (y (Hd ω) (Hs ω)).1 (y (Hd ω) (Hs ω)).2 hω.1 hω.2 f1 f2 f3
  have hmono := integral_mono_ae (hRAi.sub hRBi) hJ hpath
  have hsplit := integral_sub hRAi hRBi
  simp only [Pi.sub_apply] at hmono
  rw [hsplit] at hmono
  rw [hprofit]
  linarith
