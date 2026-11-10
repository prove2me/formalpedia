-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.expected_totalSteps_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:38:42.834203+00:00
-- url     : https://prove2.me/submissions/3163d3c3-91bd-4d6f-96c1-3b509b3f4b2a

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Expectation
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_StrictSlackMoments
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_mem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_notMem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_eventProbability_nonneg
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_historyWitness_root_count
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurableSet_compatible
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_prefixCount
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_nil_mem_witnessPaths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceHistory_count
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceHistory_length
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceTree_compatible
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceTree_injective
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceTree_paths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_prefixCount_monotone
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_tree_compatibility_probability_le
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_le_budget
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_zero
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessWeight_eq_prod_paths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessWeight_nonneg
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_mem
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_notMem
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.mem_closedNeighbors
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.nil_mem_witnessPaths
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.occurrenceHistory_length
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.witnessPartition_zero
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert


section
namespace QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
private theorem moment_constants (D : ℕ) :
    0 < momentWeight D ∧ momentWeight D ≤ 1/2 ∧ momentWeight D < 1 ∧
      0 < momentRatio D ∧ momentRatio D < 1 ∧
      1 / (1 - momentRatio D) = (D : ℝ) + 2 := by
  have hd : (0 : ℝ) ≤ D := by positivity
  have ha : (0 : ℝ) < (D : ℝ) + 1 := by positivity
  have hb : (0 : ℝ) < (D : ℝ) + 2 := by positivity
  have hx : 0 < momentWeight D := by unfold momentWeight; positivity
  have hhalf : momentWeight D ≤ 1/2 := by
    unfold momentWeight
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2*((D : ℝ)+1)) (by norm_num)).mpr
    nlinarith
  have hc : 0 < momentRatio D := div_pos ha hb
  have hc1 : momentRatio D < 1 := (div_lt_one hb).mpr (by linarith)
  refine ⟨hx,hhalf,by linarith,hc,hc1,?_⟩
  have he : 1-momentRatio D = 1/((D : ℝ)+2) := by
    unfold momentRatio
    field_simp [hb.ne']
    <;> ring
  rw [he]
  simp
private theorem rank_geometric_bound {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (n : ℕ) :
    (n : ℝ) * c^n ≤ 1 / (1-c) := by
  have hsum : (n : ℝ)*c^n ≤ ∑ k ∈ Finset.range n, (c^k) := by
    calc
      _ = ∑ _k ∈ Finset.range n, (c^n) := by simp
      _ ≤ _ := Finset.sum_le_sum fun k hk =>
        pow_le_pow_of_le_one hc0 hc1.le (Finset.mem_range.mp hk).le
  have hgeom := geom_sum_mul_neg c n
  have hmul : (∑ k ∈ Finset.range n, (c^k))*(1-c) ≤ 1 := by
    nlinarith [pow_nonneg hc0 n]
  exact (le_div_iff₀ (sub_pos.mpr hc1)).mpr
    ((mul_le_mul_of_nonneg_right hsum (sub_pos.mpr hc1).le).trans hmul)
section Trees
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]
private theorem amplified_criterion (D : ℕ)
    (hdegree : ∀ i, (G.neighborFinset i).card ≤ D) (q : I → ℝ)
    (hq : ∀ i, q i ≤ 1 / (4*((D : ℝ)+1))) (i : I) :
    q i / momentRatio D ≤ momentWeight D *
      ∏ _j ∈ G.neighborFinset i, (1-momentWeight D) := by
  have hx := moment_constants D
  have hd : ((G.neighborFinset i).card : ℝ) ≤ D := by exact_mod_cast hdegree i
  have hbern := one_add_mul_le_pow (a := -momentWeight D)
    (by linarith : -2 ≤ -momentWeight D) (G.neighborFinset i).card
  have hpow : 1-((G.neighborFinset i).card : ℝ)*momentWeight D ≤
      (1-momentWeight D)^(G.neighborFinset i).card := by
    simpa only [sub_eq_add_neg,mul_neg] using hbern
  have hprod : 1-(D : ℝ)*momentWeight D ≤
      ∏ _j ∈ G.neighborFinset i, (1-momentWeight D) := by
    rw [Finset.prod_const]
    exact (sub_le_sub_left (mul_le_mul_of_nonneg_right hd hx.1.le) 1).trans hpow
  have he : 1/(4*((D : ℝ)+1)) =
      (momentWeight D*(1-(D : ℝ)*momentWeight D))*momentRatio D := by
    unfold momentWeight momentRatio
    have ha : (D : ℝ)+1 ≠ 0 := by positivity
    have hb : (D : ℝ)+2 ≠ 0 := by positivity
    field_simp [ha,hb]
    <;> ring
  apply (div_le_iff₀ hx.2.2.2.1).mpr
  calc
    q i ≤ 1/(4*((D : ℝ)+1)) := hq i
    _ = _ := he
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hprod hx.1.le) hx.2.2.2.1.le
private theorem weight_amplification (q : I → ℝ) (D h : ℕ) (i : I)
    (t : WitnessTree G h i) :
    witnessWeight G q h i t = (momentRatio D)^(pathCount G h i t) *
      witnessWeight G (fun j => q j / momentRatio D) h i t := by
  rw [witnessWeight_eq_prod_paths,witnessWeight_eq_prod_paths]
  have hc : momentRatio D ≠ 0 := (moment_constants D).2.2.2.1.ne'
  have he : (∏ p ∈ witnessPaths G h i t, q (pathLabel i p)) =
      ∏ p ∈ witnessPaths G h i t, momentRatio D*(q (pathLabel i p)/momentRatio D) := by
    apply Finset.prod_congr rfl
    intro p hp
    field_simp [hc]
  rw [he,Finset.prod_mul_distrib,Finset.prod_const]
  rfl
private theorem weighted_partition_le (D : ℕ)
    (hdegree : ∀ i, (G.neighborFinset i).card ≤ D) (q : I → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq : ∀ i, q i ≤ 1/(4*((D : ℝ)+1))) (h : ℕ) (i : I) :
    (∑ t : WitnessTree G h i, ((pathCount G h i t : ℝ)*witnessWeight G q h i t)) ≤
      (D : ℝ)+2 := by
  have hx := moment_constants D
  let q' : I → ℝ := fun j => q j / momentRatio D
  have hq' : ∀ j, 0 ≤ q' j := fun j => div_nonneg (hq0 j) hx.2.2.2.1.le
  have hcrit : ∀ j, q' j ≤ momentWeight D *
      ∏ _k ∈ G.neighborFinset j, (1-momentWeight D) :=
    amplified_criterion G D hdegree q hq
  have hpart := witnessPartition_le_budget G q' (fun _ => momentWeight D) hq'
    (fun _ => hx.1.le) (fun _ => hx.2.2.1) hcrit h i
  have hbudget : resamplingBudget (fun _ : I => momentWeight D) i ≤ 1 := by
    unfold resamplingBudget
    exact (div_le_one (sub_pos.mpr hx.2.2.1)).mpr (by linarith [hx.2.1])
  calc
    _ ≤ ∑ t : WitnessTree G h i, (((D : ℝ)+2)*witnessWeight G q' h i t) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [weight_amplification G q D h i t]
      have hn := rank_geometric_bound hx.2.2.2.1.le hx.2.2.2.2.1 (pathCount G h i t)
      rw [hx.2.2.2.2.2] at hn
      simpa only [q',mul_assoc] using
        mul_le_mul_of_nonneg_right hn (witnessWeight_nonneg G q' hq' h i t)
    _ = ((D : ℝ)+2)*witnessPartition G q' h i := by
      unfold witnessPartition
      rw [Finset.mul_sum]
    _ ≤ ((D : ℝ)+2)*resamplingBudget (fun _ : I => momentWeight D) i :=
      mul_le_mul_of_nonneg_left hpart (by positivity)
    _ ≤ (D : ℝ)+2 := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hbudget
        (by positivity : 0 ≤ (D : ℝ)+2)
end Trees
section Execution
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
private theorem count_succ (R : Table (X := X)) (T : ℕ) (i : I) :
    prefixCount vars bad R (T+1) i = prefixCount vars bad R T i+
      if selected vars bad R T=some i then 1 else 0 := by
  classical
  by_cases h : selected vars bad R T=some i <;>
    simp [prefixCount,occurrences,Finset.range_add_one,Finset.filter_insert,h]
private theorem rank_sum (R : Table (X := X)) (T : ℕ) (i : I) :
    2*(∑ n ∈ occurrences vars bad R T i, (prefixCount vars bad R n i+1)) =
      prefixCount vars bad R T i*(prefixCount vars bad R T i+1) := by
  classical
  induction T with
  | zero => simp [prefixCount,occurrences]
  | succ T ih =>
    have hnot : T ∉ occurrences vars bad R T i := by simp [occurrences]
    have hset : occurrences vars bad R (T+1) i =
        if selected vars bad R T=some i then insert T (occurrences vars bad R T i)
        else occurrences vars bad R T i := by
      by_cases hs : selected vars bad R T=some i <;>
        simp [occurrences,Finset.range_add_one,Finset.filter_insert,hs]
    rw [hset,count_succ]
    by_cases hs : selected vars bad R T=some i
    · simp only [if_pos hs,Finset.sum_insert hnot]
      nlinarith
    · simpa only [if_neg hs,Nat.add_zero] using ih
private theorem occurrence_rank_le_paths (R : Table (X := X)) (T : ℕ) (i : I)
    (n : occurrences vars bad R T i) :
    prefixCount vars bad R n.val i+1 ≤
      pathCount (supportGraph vars) (T+1) i (occurrenceTree vars bad R T i n) := by
  calc
    _ = labelCount i i (witnessPaths (supportGraph vars) (T+1) i
        (occurrenceTree vars bad R T i n)) := by
      rw [occurrenceTree_paths,historyWitness_root_count,occurrenceHistory_count]
    _ ≤ _ := Finset.card_filter_le _ _
open scoped Classical in
private theorem square_count_le_witnesses (R : Table (X := X)) (T : ℕ) (i : I) :
    (prefixCount vars bad R T i)^2 ≤
      2*(∑ t ∈ (Finset.univ : Finset (WitnessTree (supportGraph vars) (T+1) i)).filter
        (fun t => R ∈ compatible vars bad i (witnessPaths (supportGraph vars) (T+1) i t)),
        (pathCount (supportGraph vars) (T+1) i t)) := by
  classical
  let f := occurrenceTree vars bad R T i
  let nodes := pathCount (supportGraph vars) (T+1) i
  have hinj : Function.Injective f := occurrenceTree_injective vars bad R T i
  have hsum : (∑ n ∈ occurrences vars bad R T i, (prefixCount vars bad R n i+1)) ≤
      ∑ t ∈ (Finset.univ : Finset (WitnessTree (supportGraph vars) (T+1) i)).filter
        (fun t => R ∈ compatible vars bad i (witnessPaths (supportGraph vars) (T+1) i t)), (nodes t) := by
    calc
      _ = ∑ n : occurrences vars bad R T i, (prefixCount vars bad R n.val i+1) :=
        (Finset.sum_coe_sort _ _).symm
      _ ≤ ∑ n : occurrences vars bad R T i, (nodes (f n)) :=
        Finset.sum_le_sum fun n _ => occurrence_rank_le_paths vars bad R T i n
      _ = ∑ t ∈ Finset.univ.image f, (nodes t) := by
        rw [Finset.sum_image (fun a _ b _ hab => hinj hab)]
      _ ≤ _ := Finset.sum_le_sum_of_subset (by
        intro t ht
        obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp ht
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,occurrenceTree_compatible vars bad R T i n⟩)
  have hr := rank_sum vars bad R T i
  nlinarith
variable [MeasurableSpace I] [MeasurableSingletonClass I]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
variable (hbad : ∀ i, MeasurableSet (bad i))
include hbad in
private theorem prefix_count_second_moment (D : ℕ)
    (hdegree : ∀ i, ((supportGraph vars).neighborFinset i).card ≤ D)
    (hprob : ∀ i, eventProbability vars ν bad i ≤ 1/(4*((D : ℝ)+1)))
    (T : ℕ) (i : I) :
    (∫⁻ R, (prefixCount vars bad R T i : ℝ≥0∞)^2 ∂tableLaw ν) ≤
      (2*(D+2) : ℕ) := by
  classical
  let nodes := pathCount (supportGraph vars) (T+1) i
  let S : WitnessTree (supportGraph vars) (T+1) i → Set (Table (X := X)) :=
    fun t => compatible vars bad i (witnessPaths (supportGraph vars) (T+1) i t)
  have hS : ∀ t, MeasurableSet (S t) := fun t => measurableSet_compatible vars bad hbad i _
  have hm : Measurable (fun R : Table (X := X) =>
      ∑ t : WitnessTree (supportGraph vars) (T+1) i, ((S t).indicator (fun _ => (nodes t : ℝ≥0∞)) R)) :=
    Finset.measurable_sum _ fun t _ => measurable_const.indicator (hS t)
  calc
    _ ≤ ∫⁻ R, (2 : ℝ≥0∞)*∑ t : WitnessTree (supportGraph vars) (T+1) i,
        ((S t).indicator (fun _ => (nodes t : ℝ≥0∞)) R) ∂tableLaw ν := by
      apply lintegral_mono
      intro R
      have hn := square_count_le_witnesses vars bad R T i
      have hc := (Nat.cast_le (α := ℝ≥0∞)).mpr hn
      simp only [Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sum] at hc
      simpa only [S,nodes,Finset.sum_filter,Set.indicator_apply] using hc
    _ = 2*∑ t : WitnessTree (supportGraph vars) (T+1) i,
        ((nodes t : ℝ≥0∞)*tableLaw ν (S t)) := by
      rw [lintegral_const_mul _ hm,lintegral_finsetSum _
        (fun t _ => measurable_const.indicator (hS t))]
      congr 1
      apply Finset.sum_congr rfl
      intro t ht
      exact lintegral_indicator_const (hS t) _
    _ ≤ 2*∑ t : WitnessTree (supportGraph vars) (T+1) i,
        ((nodes t : ℝ≥0∞)*ENNReal.ofReal (witnessWeight (supportGraph vars)
          (eventProbability vars ν bad) (T+1) i t)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_left
        (tree_compatibility_probability_le vars ν bad hbad (T+1) i t) (by positivity)
    _ = ENNReal.ofReal (2*∑ t : WitnessTree (supportGraph vars) (T+1) i,
        ((nodes t : ℝ)*witnessWeight (supportGraph vars) (eventProbability vars ν bad) (T+1) i t)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_sum_of_nonneg (fun t _ => mul_nonneg (Nat.cast_nonneg _)
          (witnessWeight_nonneg _ _ (eventProbability_nonneg vars ν bad) _ _ t))]
      norm_num only [ENNReal.ofReal_ofNat]
      congr 1
      apply Finset.sum_congr rfl
      intro t ht
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (2*((D : ℝ)+2)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (weighted_partition_le (supportGraph vars) D hdegree (eventProbability vars ν bad)
          (eventProbability_nonneg vars ν bad) hprob (T+1) i) (by norm_num))
    _ = _ := by
      have he : 2*((D : ℝ)+2) = ((2*(D+2) : ℕ) : ℝ) := by push_cast; ring
      rw [he,ENNReal.ofReal_natCast]
private theorem sum_square_le_card_mul_sum_square (a : I → ℝ) :
    (∑ i, (a i))^2 ≤ (Fintype.card I : ℝ)*(∑ i, ((a i)^2)) := by
  have hpair (i j : I) : 2*a i*a j ≤ (a i)^2+(a j)^2 := by
    nlinarith [sq_nonneg (a i-a j)]
  have hs : (∑ i : I, (∑ j : I, (2*a i*a j))) ≤
      ∑ i : I, (∑ j : I, ((a i)^2+(a j)^2)) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
  have hleft : (∑ i : I, (∑ j : I, (2*a i*a j))) = 2*(∑ i, (a i))^2 := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hright : (∑ i : I, (∑ j : I, ((a i)^2+(a j)^2))) =
      2*(Fintype.card I : ℝ)*(∑ i, ((a i)^2)) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ, ← Finset.mul_sum]
    ring
  rw [hleft,hright] at hs
  nlinarith
include hbad in
private theorem prefix_steps_second_moment (D : ℕ)
    (hdegree : ∀ i, ((supportGraph vars).neighborFinset i).card ≤ D)
    (hprob : ∀ i, eventProbability vars ν bad i ≤ 1/(4*((D : ℝ)+1))) (T : ℕ) :
    (∫⁻ R, (∑ i, (prefixCount vars bad R T i : ℝ≥0∞))^2 ∂tableLaw ν) ≤
      (2*(Fintype.card I)^2*(D+2)^2 : ℕ) := by
  have hm (i : I) : Measurable (fun R : Table (X := X) =>
      (prefixCount vars bad R T i : ℝ≥0∞)^2) :=
    (measurable_prefixCount vars bad hbad T i).pow_const 2
  calc
    _ ≤ ∫⁻ R, (Fintype.card I : ℝ≥0∞)*
        ∑ i, ((prefixCount vars bad R T i : ℝ≥0∞)^2) ∂tableLaw ν := by
      apply lintegral_mono
      intro R
      have h := sum_square_le_card_mul_sum_square
        (fun i : I => (prefixCount vars bad R T i : ℝ))
      have hn : (∑ i, (prefixCount vars bad R T i))^2 ≤
          Fintype.card I*(∑ i, ((prefixCount vars bad R T i)^2)) := by exact_mod_cast h
      change (∑ i, (prefixCount vars bad R T i : ℝ≥0∞))^2 ≤
        (Fintype.card I : ℝ≥0∞)*(∑ i, ((prefixCount vars bad R T i : ℝ≥0∞)^2))
      simpa only [Nat.cast_pow,Nat.cast_sum,Nat.cast_mul] using
        (Nat.cast_le (α := ℝ≥0∞)).mpr hn
    _ = (Fintype.card I : ℝ≥0∞)*
        ∑ i, (∫⁻ R, (prefixCount vars bad R T i : ℝ≥0∞)^2 ∂tableLaw ν) := by
      rw [lintegral_const_mul _ (Finset.measurable_sum _ (fun i _ => hm i)),
        lintegral_finsetSum _ (fun i _ => hm i)]
    _ ≤ (Fintype.card I : ℝ≥0∞)*∑ _i : I, ((2*(D+2) : ℕ) : ℝ≥0∞) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun i _ => prefix_count_second_moment vars bad ν hbad D hdegree hprob T i
    _ = (2*(Fintype.card I)^2*(D+2) : ℕ) := by simp; push_cast; ring
    _ ≤ _ := by
      exact_mod_cast Nat.mul_le_mul_left (2*(Fintype.card I)^2)
        (show D+2 ≤ (D+2)^2 by nlinarith)
private theorem square_iSup (f : ℕ → ℝ≥0∞) (hf : Monotone f) :
    (⨆ n, f n)^2 = ⨆ n, (f n)^2 := by
  apply le_antisymm
  · simp only [pow_two,ENNReal.iSup_mul,ENNReal.mul_iSup]
    apply iSup_le
    intro a
    apply iSup_le
    intro b
    have hmul : f a*f b ≤ f (max a b)*f (max a b) :=
      mul_le_mul' (hf (le_max_left a b)) (hf (le_max_right a b))
    exact le_iSup_of_le (max a b) (by simpa only [mul_comm] using hmul)
  · apply iSup_le
    intro n
    exact pow_le_pow_left₀ (by positivity) (le_iSup f n) 2
end Execution
end QEC.Coding.ProbabilisticConstruction.Resampling
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
variable [MeasurableSpace I] [MeasurableSingletonClass I]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
variable (hbad : ∀ i, MeasurableSet (bad i))
include hbad
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (D : ℕ)
    (hdegree : ∀ i, ((supportGraph vars).neighborFinset i).card ≤ D)
    (hprob : ∀ i, eventProbability vars ν bad i ≤ 1/(4*((D : ℝ)+1))) :
    (∫⁻ R, (totalSteps vars bad R)^2 ∂tableLaw ν) ≤
      (2*(Fintype.card I)^2*(D+2)^2 : ℕ) := by
  have he (R : Table (X := X)) : (totalSteps vars bad R)^2 =
      ⨆ T : ℕ, (∑ i, (prefixCount vars bad R T i : ℝ≥0∞))^2 := by
    unfold totalSteps totalCount
    rw [ENNReal.finsetSum_iSup_of_monotone (fun i a b hab =>
      (Nat.cast_le (α := ℝ≥0∞)).mpr (prefixCount_monotone vars bad R i hab))]
    exact square_iSup _ (fun a b hab => Finset.sum_le_sum fun i _ =>
      (Nat.cast_le (α := ℝ≥0∞)).mpr (prefixCount_monotone vars bad R i hab))
  simp_rw [he]
  rw [lintegral_iSup (fun T =>
    (Finset.measurable_sum _ (fun i _ => measurable_prefixCount vars bad hbad T i)).pow_const 2)]
  · exact iSup_le fun T => prefix_steps_second_moment vars bad ν hbad D hdegree hprob T
  · intro a b hab R
    exact pow_le_pow_left₀ (by positivity) (Finset.sum_le_sum fun i _ =>
      (Nat.cast_le (α := ℝ≥0∞)).mpr (prefixCount_monotone vars bad R i hab)) 2
end QEC.Coding.ProbabilisticConstruction.Resampling
