-- Prove2me | solution 1 for StableMSR.Recovery.Supplement.partition_scale_success
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-19T00:03:27.443686+00:00
-- url     : https://prove2.me/submissions/90033330-41f7-4974-ae4d-6a746b98ecf1

import Definitions.Def_StableMSR_Recovery_Supplement_Partitions
import Theorems.Thm_StableMSR_Recovery_Supplement_split_probability
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
set_option autoImplicit false
open scoped Classical ENNReal
open StableMSR.Recovery
namespace GrowthAux

lemma metric_nonneg {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) (x y : Point n) : 0 ≤ d x y := by
  obtain ⟨m, hm⟩ := hd
  letI := m
  rw [← hm]
  exact dist_nonneg

lemma metric_symm {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) (x y : Point n) : d x y = d y x := by
  obtain ⟨m, hm⟩ := hd
  letI := m
  rw [← hm, ← hm]
  exact dist_comm x y

lemma metric_triangle {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) (x y z : Point n) : d x z ≤ d x y + d y z := by
  obtain ⟨m, hm⟩ := hd
  letI := m
  rw [← hm, ← hm, ← hm]
  exact dist_triangle x y z

lemma exists_center {n : ℕ} (d : Point n → Point n → ℝ)
    {C : Cluster n} (hC : C.Nonempty) : ∃ c, OptimalCenter d C c := by
  classical
  obtain ⟨c, hc, he⟩ := Finset.exists_mem_eq_inf' hC (eccentricity d C)
  refine ⟨c, hc, ?_⟩
  simp only [radius, dif_pos hC]
  exact he.symm

lemma distance_le_radius {n : ℕ} {d : Point n → Point n → ℝ}
    {C : Cluster n} {c x : Point n} (hc : OptimalCenter d C c) (hx : x ∈ C) :
    d c x ≤ radius d C := by
  have hC : C.Nonempty := ⟨c, hc.1⟩
  rw [← hc.2]
  simp only [eccentricity, dif_pos hC]
  exact Finset.le_sup' (d c) hx

lemma radius_nonneg {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) {C : Cluster n} (hC : C.Nonempty) : 0 ≤ radius d C := by
  obtain ⟨c, hc⟩ := exists_center d hC
  exact (metric_nonneg hd c c).trans (distance_le_radius hc hc.1)

lemma radius_pos {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) {C : Cluster n} (hC : 2 ≤ C.card) : 0 < radius d C := by
  classical
  have hne : C.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨c, hc⟩ := exists_center d hne
  obtain ⟨y, hy, hyc⟩ := Finset.exists_mem_ne (by omega : 1 < C.card) c
  obtain ⟨m, hm⟩ := hd
  letI := m
  have hcy : 0 < d c y := by rw [← hm]; exact dist_pos.mpr hyc.symm
  exact hcy.trans_le (distance_le_radius hc hy)

lemma radius_le_largest {n : ℕ} {d : Point n → Point n → ℝ}
    {O : Partition n} {C : Cluster n} (hC : C ∈ O) : radius d C ≤ largestRadius d O := by
  classical
  rw [largestRadius, dif_pos ⟨C, hC⟩]
  exact Finset.le_sup' _ hC

lemma largest_pos {n k : ℕ} {d : Point n → Point n → ℝ} (hd : IsMetricArray d)
    {O : Partition n} (hO : Feasible Finset.univ k O) (hkn : k < n) :
    0 < largestRadius d O := by
  classical
  have hex : ∃ C ∈ O, 2 ≤ C.card := by
    by_contra hn
    have hc : ∀ C ∈ O, C.card ≤ 1 := by
      intro C hC
      by_contra hnC
      exact hn ⟨C, hC, by omega⟩
    have hsum : (∑ C ∈ O, C.card) ≤ O.card := by
      calc
        (∑ C ∈ O, C.card) ≤ ∑ C ∈ O, 1 := Finset.sum_le_sum hc
        _ = _ := by simp
    have hncard : (∑ C ∈ O, C.card) = n := by
      rw [← Finset.card_biUnion hO.2.2.1]
      change (O.biUnion id).card = n
      rw [hO.2.2.2]
      simp
    rw [hncard, hO.1] at hsum
    omega
  obtain ⟨C, hC, hC2⟩ := hex
  exact (radius_pos hd hC2).trans_le (radius_le_largest hC)

end GrowthAux
namespace StableMSR.Recovery
theorem few_bound_of_densityScale_lt (ε R M : ℝ) (t : ℕ)
    (hε : 0 < ε) (hR : 0 < R)
    (ht : (t : ℝ) * (ε * R / 4) ≤ M)
    (hscale : ε * M / 4 < sigma * R) : t ≤ fewBound ε := by
  have he2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hm := mul_le_mul_of_nonneg_left ht hε.le
  have htR : R * ((t : ℝ) * ε ^ 2) < R * (16 * sigma) := by
    nlinarith
  have htε : (t : ℝ) * ε ^ 2 < 16 * sigma :=
    (mul_lt_mul_iff_right₀ hR).mp (by simpa [mul_comm] using htR)
  have hreal : (t : ℝ) < 16 * sigma / ε ^ 2 := (lt_div_iff₀ he2).2 htε
  have hceil : (t : ℝ) ≤ (⌈16 * sigma / ε ^ 2⌉₊ : ℝ) :=
    hreal.le.trans (Nat.le_ceil _)
  exact_mod_cast hceil

/-- The deterministic dyadic-scale alternative in Lemma A.4. The upper index
is exactly the finite scale list used by Algorithm 1. -/
theorem dyadic_scale_selection (ε R M : ℝ) (n : ℕ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : 0 < R)
    (hM : M ≤ (n : ℝ) * R)
    (hscale : sigma * R ≤ ε * M / 4) :
    ∃ j : ℕ, 9 ≤ j ∧ j ≤ ⌈Real.logb 2 (n : ℝ)⌉₊ ∧
      sigma * R ≤ (2 : ℝ) ^ j * R ∧
      (2 : ℝ) ^ j * R ≤ ε * M / 4 ∧
      ε * M / 4 < 2 * ((2 : ℝ) ^ j * R) ∧
      M / ((2 : ℝ) ^ j * R) < 8 / ε := by
  have hsig : sigma = 512 := rfl
  have hρ : 0 < ε * M / 4 := by rw [hsig] at hscale; nlinarith
  have hMpos : 0 < M := by
    by_contra h
    have hm0 : ε * M ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hε.le (le_of_not_gt h)
    linarith
  have hratio : 1 ≤ (ε * M / 4) / R := by
    apply (le_div_iff₀ hR).2
    rw [hsig] at hscale
    nlinarith
  obtain ⟨j, hjlo, hjhi⟩ := exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  have hj9 : 9 ≤ j := by
    by_contra h
    have hjpow : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ 9 :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h512 : (512 : ℝ) ≤ (ε * M / 4) / R := by
      apply (le_div_iff₀ hR).2
      simpa [sigma] using hscale
    norm_num at hjpow
    linarith
  have hL : 0 < (2 : ℝ) ^ j * R := by positivity
  have hjLlo : (2 : ℝ) ^ j * R ≤ ε * M / 4 := (le_div_iff₀ hR).mp hjlo
  have hjLhi : ε * M / 4 < 2 * ((2 : ℝ) ^ j * R) := by
    have hh := (div_lt_iff₀ hR).mp hjhi
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hh
  have hρn : ε * M / 4 < (n : ℝ) * R := by
    have hp := mul_pos hMpos (sub_pos.mpr hε1)
    nlinarith
  have hjn : (2 : ℝ) ^ j < (n : ℝ) := by
    apply (mul_lt_mul_iff_right₀ hR).mp
    simpa [mul_comm] using hjLlo.trans_lt hρn
  have hjlog : (j : ℝ) ≤ Real.logb 2 (n : ℝ) := by
    have hh := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num)
      (show 0 < (2 : ℝ) ^ j by positivity) hjn.le
    simpa [Real.logb_pow] using hh
  have hjceil : j ≤ ⌈Real.logb 2 (n : ℝ)⌉₊ := by
    exact_mod_cast hjlog.trans (Nat.le_ceil _)
  refine ⟨j, hj9, hjceil, ?_, hjLlo, hjLhi, ?_⟩
  · have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj9
    norm_num at hpow
    simpa [sigma] using mul_le_mul_of_nonneg_right hpow hR.le
  · apply (div_lt_div_iff₀ hL hε).2
    nlinarith

/-- Lemma A.4's deterministic case distinction, independent of the random
partition routine and therefore requiring no probability hypothesis. -/
theorem scale_selection_alternatives (ε R M : ℝ) (n t : ℕ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : 0 < R)
    (ht : (t : ℝ) * (ε * R / 4) ≤ M)
    (hM : M ≤ (n : ℝ) * R) :
    (ε * M / 4 < sigma * R ∧ t ≤ fewBound ε) ∨
    (∃ j : ℕ, 9 ≤ j ∧ j ≤ ⌈Real.logb 2 (n : ℝ)⌉₊ ∧
      sigma * R ≤ (2 : ℝ) ^ j * R ∧
      (2 : ℝ) ^ j * R ≤ ε * M / 4 ∧
      ε * M / 4 < 2 * ((2 : ℝ) ^ j * R) ∧
      M / ((2 : ℝ) ^ j * R) < 8 / ε) := by
  rcases lt_or_ge (ε * M / 4) (sigma * R) with h | h
  · exact Or.inl ⟨h, few_bound_of_densityScale_lt ε R M t hε hR ht h⟩
  · exact Or.inr (dyadic_scale_selection ε R M n hε hε1 hR hM h)


/-- The mass bounds used by Lemma A.4 follow from feasibility alone. -/
theorem large_mass_bounds {n k : ℕ} (d : Point n → Point n → ℝ)
    (hd : IsMetricArray d) (O : Partition n) (hO : Feasible Finset.univ k O)
    (hkn : k < n) (ε : ℝ) :
    ((largeClusters d O ε).card : ℝ) * (ε * largestRadius d O / 4) ≤
      largeMass d O ε ∧
    largeMass d O ε ≤ (n : ℝ) * largestRadius d O := by
  classical
  let T := largeClusters d O ε
  have hTO : T ⊆ O := Finset.filter_subset _ _
  have hcard : T.card ≤ n := by
    have hh := Finset.card_le_card hTO
    rw [hO.1] at hh
    omega
  have hR : 0 < largestRadius d O := GrowthAux.largest_pos hd hO hkn
  constructor
  · change (T.card : ℝ) * (ε * largestRadius d O / 4) ≤ ∑ C ∈ T, radius d C
    calc
      (T.card : ℝ) * (ε * largestRadius d O / 4) =
          ∑ _C ∈ T, ε * largestRadius d O / 4 := by simp
      _ ≤ ∑ C ∈ T, radius d C := by
        apply Finset.sum_le_sum
        intro C hC
        exact (Finset.mem_filter.mp hC).2
  · change (∑ C ∈ T, radius d C) ≤ (n : ℝ) * largestRadius d O
    calc
      (∑ C ∈ T, radius d C) ≤ ∑ _C ∈ T, largestRadius d O := by
        exact Finset.sum_le_sum (fun C hC => GrowthAux.radius_le_largest (hTO hC))
      _ = (T.card : ℝ) * largestRadius d O := by simp
      _ ≤ (n : ℝ) * largestRadius d O := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hR.le

/-- Lemma A.4, deterministic alternatives, instantiated with the canonical
clustering scales. No stability hypothesis is needed for this numerical step. -/
theorem clustering_scale_selection {n k : ℕ} (d : Point n → Point n → ℝ)
    (hd : IsMetricArray d) (O : Partition n) (hO : Feasible Finset.univ k O)
    (hkn : k < n) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (densityScale d O ε < sigma * largestRadius d O ∧
      (largeClusters d O ε).card ≤ fewBound ε) ∨
    (∃ j : ℕ, 9 ≤ j ∧ j ≤ ⌈Real.logb 2 (n : ℝ)⌉₊ ∧
      sigma * largestRadius d O ≤ (2 : ℝ) ^ j * largestRadius d O ∧
      (2 : ℝ) ^ j * largestRadius d O ≤ densityScale d O ε ∧
      densityScale d O ε < 2 * ((2 : ℝ) ^ j * largestRadius d O) ∧
      largeMass d O ε / ((2 : ℝ) ^ j * largestRadius d O) < 8 / ε) := by
  obtain ⟨ht, hM⟩ := large_mass_bounds d hd O hO hkn ε
  exact scale_selection_alternatives ε (largestRadius d O) (largeMass d O ε)
    n (largeClusters d O ε).card hε hε1 (GrowthAux.largest_pos hd hO hkn) ht hM

end StableMSR.Recovery
set_option autoImplicit false
open scoped Classical
namespace StableMSR.Recovery.Supplement

/-- Consecutive entries bracket every value between the least entry and the
strict upper endpoint. The lower endpoint may equal the value. -/
lemma consecutive_gap (l : List ℝ) (u : ℝ) (sorted : l.Pairwise (· ≤ ·))
    (low : ∃ a ∈ l, a ≤ u) (high : ∃ b ∈ l, u < b) :
    ∃ a b, (a,b) ∈ l.zip l.tail ∧ a ≤ u ∧ u < b ∧ ∀ v ∈ l, v ≤ a ∨ b ≤ v := by
  induction l with
  | nil => simp at low
  | cons a l ih =>
    obtain ⟨before,rest⟩ := List.pairwise_cons.mp sorted
    have au : a ≤ u := by
      obtain ⟨c,hc,cu⟩ := low
      rcases List.mem_cons.mp hc with rfl|hc
      · exact cu
      · exact (before _ hc).trans cu
    obtain ⟨c,hc,uc⟩ := high
    have cl : c ∈ l := (List.mem_cons.mp hc).resolve_left (by rintro rfl; linarith)
    cases l with
    | nil => simp at cl
    | cons b bs =>
      by_cases ub : u < b
      · refine ⟨a,b,by simp,au,ub,?_⟩
        intro v hv
        rcases List.mem_cons.mp hv with rfl|hv
        · exact Or.inl le_rfl
        · rcases List.mem_cons.mp hv with rfl|hv
          · exact Or.inr le_rfl
          · exact Or.inr ((List.pairwise_cons.mp rest).1 _ hv)
      · obtain ⟨i,j,hp,iu,uj,hgap⟩ := ih rest ⟨b,List.mem_cons_self,le_of_not_gt ub⟩ ⟨c,cl,uc⟩
        refine ⟨i,j,by simpa only [List.tail_cons,List.zip_cons_cons,List.mem_cons] using Or.inr hp,iu,uj,?_⟩
        intro v hv
        rcases List.mem_cons.mp hv with rfl|hv
        · have hi : i ∈ b::bs := List.of_mem_zip hp |>.1
          exact Or.inl (before _ hi)
        · exact hgap _ hv

lemma component_is_wide {n : ℕ} (d : Point n → Point n → ℝ) (R L : ℝ) (x : Point n)
    (wide : L < diameter d (component d R Finset.univ x)) :
    component d R Finset.univ x ∈ wideComponents d R L := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩,wide⟩

/-- All radius dependence of the final partition is through center-to-point
comparisons, including when the small-component relabelling changes a point. -/
lemma partition_congr_tests {n : ℕ} (d : Point n → Point n → ℝ) (ε R L a b : ℝ)
    (π : List (Point n)) (same : ∀ z ∈ netVertices d R L, ∀ x, (d z x ≤ a ↔ d z x ≤ b)) :
    partitionAt d ε R L a π = partitionAt d ε R L b π := by
  classical
  have labels (x : Point n) : initialLabel d R L a π x = initialLabel d R L b π x := by
    dsimp only [initialLabel]
    split
    next wide =>
      congr 2
      apply List.filter_congr
      intro z _
      simp only [decide_eq_decide]
      apply and_congr_right
      intro hz
      exact same z (Finset.mem_biUnion.mpr ⟨_,component_is_wide d R L x wide,hz⟩) x
    next => rfl
  simp only [partitionAt,labels]

/-- Every radius in the half-open sampling interval has an enumerated midpoint
with the same predicates for every net center and every input point. -/
theorem midpoint_tests {n : ℕ} (d : Point n → Point n → ℝ) (R L β : ℝ)
    (lo : L/16 ≤ β) (hi : β < L/8) :
    ∃ m ∈ midpointRadii d R L, ∀ z ∈ netVertices d R L, ∀ x : Point n, (d z x ≤ β ↔ d z x ≤ m) := by
  classical
  let B := breakpoints d R L
  have sorted : B.Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have left : L/16 ∈ B := by simp [B,breakpoints]
  have right : L/8 ∈ B := by simp [B,breakpoints]
  obtain ⟨a,b,hp,hlo,hhi,gap⟩ := consecutive_gap B β sorted ⟨_,left,lo⟩ ⟨_,right,hi⟩
  have la := (gap _ left).resolve_right (by linarith)
  have bh := (gap _ right).resolve_left (by linarith)
  refine ⟨(a+b)/2,List.mem_map.mpr ⟨(a,b),hp,rfl⟩,?_⟩
  intro z hz x
  by_cases hl : d z x ≤ L/16
  · constructor <;> intro <;> linarith
  by_cases hr : L/8 ≤ d z x
  · constructor <;> intro <;> linarith
  have mem : d z x ∈ B := by
    simp only [B,breakpoints,Finset.mem_sort,Finset.mem_union]
    right
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_biUnion.mpr ⟨z,hz,Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩⟩,
      lt_of_not_ge hl,lt_of_not_ge hr⟩
  rcases gap _ mem with h|h <;> constructor <;> intro <;> linarith

theorem partition_mem_enumeration {n : ℕ} (d : Point n → Point n → ℝ) (ε R L β : ℝ)
    (π : List (Point n)) (live : netVertices d R L ≠ ∅) (lo : L/16 ≤ β) (hi : β < L/8) :
    partitionAt d ε R L β π ∈ randomPartitions d ε R L π := by
  obtain ⟨m,hm,eq⟩ := midpoint_tests d R L β lo hi
  simp only [randomPartitions,if_neg live]
  exact List.mem_map.mpr ⟨m,hm,(partition_congr_tests d ε R L β m π eq).symm⟩
end StableMSR.Recovery.Supplement
set_option autoImplicit false
open scoped Classical ENNReal
open MeasureTheory Set
namespace StableMSR.Recovery.Supplement

lemma order_probability {n : ℕ} (V : Cluster n) : IsProbabilityMeasure (orderLaw V) := by
  classical
  have total (l : List (List (Point n))) :
      ((l.map Measure.dirac).sum : Measure (List (Point n))) univ = (l.length : ℝ≥0∞) := by
    induction l with
    | nil => simp
    | cons a l ih => simp [Measure.add_apply,ih,add_comm]
  constructor
  simp only [orderLaw,Measure.smul_apply,smul_eq_mul,total]
  exact ENNReal.inv_mul_cancel (by simp [allOrders,List.length_permutations,Nat.factorial_ne_zero]) (by simp)

lemma radius_probability {L : ℝ} (pos : 0 < L) : IsProbabilityMeasure (radiusLaw L) := by
  constructor
  simp only [radiusLaw,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ,Real.volume_Icc]
  rw [show L/8-L/16 = L/16 by ring]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top

lemma radius_half_open {L : ℝ} (pos : 0 < L) : radiusLaw L (Ico (L/16) (L/8)) = 1 := by
  rw [radiusLaw,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply measurableSet_Ico,
    inter_eq_left.mpr Ico_subset_Icc_self,Real.volume_Ico,show L/8-L/16 = L/16 by ring]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top

end StableMSR.Recovery.Supplement
set_option autoImplicit false
open scoped Classical ENNReal
open MeasureTheory Set
namespace StableMSR.Recovery.Supplement

/-- A clustering event depends on the order and finitely many measurable
center-distance comparisons. This applies to arbitrary predicates on partitions. -/
lemma partition_event {n : ℕ} (d : Point n → Point n → ℝ) (ε R L : ℝ) (P : Partition n → Prop) :
    MeasurableSet {p : List (Point n) × ℝ | P (partitionAt d ε R L p.2 p.1)} := by
  classical
  letI : DiscreteMeasurableSpace (List (Point n)) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  let mask := fun (r : ℝ) (i : Point n × Point n) => decide (d i.1 i.2 ≤ r)
  let f := fun p : List (Point n) × ℝ => (p.1,mask p.2)
  have hm : Measurable mask := by
    apply measurable_pi_lambda
    intro i
    apply measurable_to_countable'
    intro b
    cases b
    · rw [show (fun r => mask r i) ⁻¹' {false} = Iio (d i.1 i.2) by
            ext r; simp [mask]]
      exact measurableSet_Iio
    · rw [show (fun r => mask r i) ⁻¹' {true} = Ici (d i.1 i.2) by
            ext r; simp [mask]]
      exact measurableSet_Ici
  have hf : Measurable f := measurable_fst.prodMk (hm.comp measurable_snd)
  let E := {p : List (Point n) × ℝ | P (partitionAt d ε R L p.2 p.1)}
  have eq : E = f ⁻¹' (f '' E) := by
    ext p
    constructor
    · exact fun hp => ⟨p,hp,rfl⟩
    · rintro ⟨q,hq,h⟩
      change (q.1,mask q.2) = (p.1,mask p.2) at h
      have peq := Prod.mk.inj h |>.1
      have masks : mask q.2 = mask p.2 := congrArg Prod.snd h
      have part := partition_congr_tests d ε R L q.2 p.2 p.1 (by
        intro z _ x
        simpa [mask] using congrFun masks (z,x))
      change P (partitionAt d ε R L q.2 q.1) at hq
      rwa [peq,part] at hq
  change MeasurableSet E
  rw [eq]
  exact hf ((f '' E).to_countable.measurableSet)

/-- The analytic split expectation is exactly the finite sum of indicator
integrals for the split count evaluated at the sampled order and radius. -/
lemma split_integral {n : ℕ} (d : Point n → Point n → ℝ) (O : Partition n) (ε R L : ℝ) (hL : 0 < L) :
    let μ := analysisLaw d R L
    let count := fun p : List (Point n) × ℝ => (splitCount d O ε (partitionAt d ε R L p.2 p.1) : ℝ≥0∞)
    Measurable count ∧ (∫⁻ p, count p ∂μ).toReal = splitExpectation d O ε R L ∧ (∫⁻ p, count p ∂μ) ≠ ∞ := by
  classical
  letI := order_probability (netVertices d R L)
  letI := radius_probability hL
  let μ := analysisLaw d R L
  letI : IsProbabilityMeasure μ := inferInstanceAs (IsProbabilityMeasure ((orderLaw _).prod (radiusLaw L)))
  let T := largeClusters d O ε
  let S := fun C : Cluster n => {p : List (Point n) × ℝ | Split C (partitionAt d ε R L p.2 p.1)}
  let one := fun C : Cluster n => (S C).indicator (fun _ => (1:ℝ≥0∞))
  have meas (C : Cluster n) : MeasurableSet (S C) := partition_event d ε R L (Split C)
  have hm (C : Cluster n) : Measurable (one C) := measurable_const.indicator (meas C)
  have eq (p : List (Point n) × ℝ) :
      (splitCount d O ε (partitionAt d ε R L p.2 p.1) : ℝ≥0∞) = ∑ C ∈ T, one C p := by
    simp only [splitCount,T,Finset.card_filter,Nat.cast_sum,one,S,Set.indicator_apply,Set.mem_setOf_eq]
    apply Finset.sum_congr rfl
    intro C _
    split <;> simp
  have charge : (∫⁻ p, ∑ C ∈ T, one C p ∂μ) = ∑ C ∈ T, μ (S C) := by
    rw [lintegral_finsetSum T (fun C _ => hm C)]
    exact Finset.sum_congr rfl (fun C _ => lintegral_indicator_one (meas C))
  dsimp only
  simp_rw [eq]
  refine ⟨Finset.measurable_sum _ (fun C _ => hm C),?_,?_⟩
  · rw [charge,ENNReal.toReal_sum (fun C _ => measure_ne_top μ _)]
    rfl
  · rw [charge]; exact ENNReal.sum_ne_top.mpr (fun C _ => measure_ne_top μ _)

end StableMSR.Recovery.Supplement
set_option autoImplicit false
open scoped Classical ENNReal
open MeasureTheory Set
namespace StableMSR.Recovery.Supplement

/-- Markov's inequality on the product law transfers to the algorithm's order
law because every radius in [L/16,L/8) is represented by an enumerated partition. -/
theorem enumerated_success {n : ℕ} (d : Point n → Point n → ℝ) (O : Partition n) (ε R L : ℝ)
    (hL : 0 < L) (live : netVertices d R L ≠ ∅) (F : ℕ)
    (small : splitExpectation d O ε R L ≤ (2/3:ℝ)*F) :
    (1/3 : ℝ≥0∞) ≤ (orderLaw (netVertices d R L))
      {π | ∃ Q ∈ randomPartitions d ε R L π, splitCount d O ε Q ≤ F} := by
  classical
  let ν := orderLaw (netVertices d R L)
  let μ := analysisLaw d R L
  letI : IsProbabilityMeasure ν := order_probability _
  letI := radius_probability hL
  letI : IsProbabilityMeasure μ := inferInstanceAs (IsProbabilityMeasure (ν.prod (radiusLaw L)))
  let good : Set (List (Point n)) := {π | ∃ Q ∈ randomPartitions d ε R L π, splitCount d O ε Q ≤ F}
  let count := fun p : List (Point n) × ℝ => (splitCount d O ε (partitionAt d ε R L p.2 p.1) : ℝ≥0∞)
  obtain ⟨hm,he,finite⟩ := split_integral d O ε R L hL
  have incl : goodᶜ ×ˢ (Ico (L/16) (L/8)) ⊆ {p | ((F+1:ℕ):ℝ≥0∞) ≤ count p} := by
    intro p hp
    obtain ⟨fail,lo,hi⟩ := hp
    have it := partition_mem_enumeration d ε R L p.2 p.1 live lo hi
    have high : F < splitCount d O ε (partitionAt d ε R L p.2 p.1) := by
      by_contra! small'
      exact fail ⟨_,it,small'⟩
    change ((F+1:ℕ):ℝ≥0∞) ≤ (splitCount d O ε (partitionAt d ε R L p.2 p.1):ℝ≥0∞)
    exact_mod_cast Nat.succ_le_of_lt high
  have mass : μ (goodᶜ ×ˢ (Ico (L/16) (L/8))) = ν goodᶜ := by
    change ν.prod (radiusLaw L) _ = _
    rw [Measure.prod_prod,radius_half_open hL,mul_one]
  have mkv := mul_meas_ge_le_lintegral (μ:=μ) hm ((F+1:ℕ):ℝ≥0∞)
  have le : ((F+1:ℕ):ℝ≥0∞)*ν goodᶜ ≤ ∫⁻ p, count p ∂μ := by
    rw [←mass]
    apply le_trans _ mkv
    gcongr <;> exact measure_mono incl
  have bound := ENNReal.toReal_mono finite le
  rw [ENNReal.toReal_mul,ENNReal.toReal_natCast,Nat.cast_add,Nat.cast_one,he] at bound
  have hreal : ((F:ℝ)+1)*(ν goodᶜ).toReal ≤ (2/3:ℝ)*F := by
    exact bound.trans small
  have sum := measure_add_measure_compl (μ:=ν) (show MeasurableSet good from MeasurableSpace.measurableSet_top)
  have one := congrArg ENNReal.toReal sum
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),measure_univ,ENNReal.toReal_one] at one
  change (1/3 : ℝ≥0∞) ≤ ν good
  apply (ENNReal.toReal_le_toReal (by norm_num) (measure_ne_top _ _)).mp
  have failSmall : (ν goodᶜ).toReal ≤ 2/3 := by
    by_contra! big
    nlinarith [mul_nonneg (show 0 ≤ (F:ℝ) by positivity) (sub_nonneg.mpr big.le)]
  norm_num
  linarith

lemma expectation_budget {ε M L : ℝ} (e0 : 0 < ε) (l0 : 0 < L) (mass : M/L < 8/ε) :
    chi*M/L*Real.log (1+12*sigma/ε^2) ≤ (2/3:ℝ)*(splitBound ε : ℝ) := by
  let x := 1+12*sigma/ε^2
  have hx : 1 ≤ x := le_add_of_nonneg_right (by dsimp [sigma]; positivity)
  have lg : 0 ≤ Real.log x := Real.log_nonneg hx
  have log2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have le1 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have lgb : Real.log x ≤ Real.logb 2 x := by
    rw [Real.logb,le_div_iff₀ log2]
    nlinarith [mul_le_mul_of_nonneg_left le1 lg]
  have ceil : Real.log x ≤ (lambda ε : ℝ) := lgb.trans (Nat.le_ceil _)
  have cpos : 0 ≤ chi := by norm_num [chi]
  have e : chi*(M/L)*Real.log x ≤ chi*(8/ε)*(lambda ε:ℝ) :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left mass.le cpos) lg).trans
      (mul_le_mul_of_nonneg_left ceil (mul_nonneg cpos (by positivity)))
  have cap := Nat.le_ceil (12*chi*(lambda ε:ℝ)/ε)
  change _ ≤ (splitBound ε:ℝ) at cap
  have ident : chi*(8/ε)*(lambda ε:ℝ) = (2/3:ℝ)*(12*chi*(lambda ε:ℝ)/ε) := by ring
  rw [ident] at e
  change chi*M/L*Real.log x ≤ _
  rw [mul_div_assoc]; linarith

end StableMSR.Recovery.Supplement
set_option autoImplicit false
open scoped Classical
namespace StableMSR.Recovery.Supplement

/-- A star through an optimal center puts its entire cluster in a single
component at threshold R. This handles the empty-net branch of the algorithm. -/
lemma component_unsplit {n k : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (O : Partition n) (hO : Feasible Finset.univ k O) {C : Cluster n} (hC : C ∈ O) :
    ¬ Split C (components d (largestRadius d O) Finset.univ) := by
  classical
  let R := largestRadius d O
  let G := thresholdGraph d R (Finset.univ : Cluster n)
  obtain ⟨c,hc⟩ := GrowthAux.exists_center d (hO.2.1 C hC)
  have star (x : Point n) (hx : x ∈ C) : G.Reachable c x := by
    by_cases eq : c = x
    · subst x; exact .refl _
    · have near := (GrowthAux.distance_le_radius hc hx).trans (GrowthAux.radius_le_largest hC)
      exact (show G.Adj c x from ⟨eq,Finset.mem_univ _,Finset.mem_univ _,near,
        (GrowthAux.metric_symm hd x c) ▸ near⟩).reachable
  have sub : meeting (components d R Finset.univ) C ⊆ {component d R Finset.univ c} := by
    intro D hD
    obtain ⟨hparts,x,hx⟩ := Finset.mem_filter.mp hD
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hparts
    obtain ⟨hxy,hxC⟩ := Finset.mem_inter.mp hx
    have cy := (star x hxC).trans ((Finset.mem_filter.mp hxy).2.symm)
    apply Finset.mem_singleton.mpr
    ext v
    simp only [component,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨cy.trans,cy.symm.trans⟩
  exact not_lt_of_ge ((Finset.card_le_card sub).trans (by simp))

theorem empty_net_partition {n k : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (O : Partition n) (hO : Feasible Finset.univ k O) (ε L : ℝ)
    (empty : netVertices d (largestRadius d O) L = ∅) (π : List (Point n)) :
    ∃ Q ∈ randomPartitions d ε (largestRadius d O) L π, splitCount d O ε Q = 0 := by
  classical
  refine ⟨components d (largestRadius d O) Finset.univ,by simp [randomPartitions,empty],?_⟩
  simp only [splitCount,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
  intro C hC
  exact component_unsplit d hd O hO (Finset.mem_filter.mp hC).1

end StableMSR.Recovery.Supplement
set_option autoImplicit false
open scoped Classical ENNReal
open MeasureTheory
namespace StableMSR.Recovery.Supplement
theorem partition_scale_of_expectation {n k : ℕ} (d : Point n → Point n → ℝ) (γ : ℝ) (O : Partition n)
    (hk : 1 ≤ k) (hkn : k < n) (hd : IsMetricArray d) (hγ : 1 < γ ∧ γ < 2)
    (hO : Stable d k γ O)
    (expected : ∀ L : ℝ, netVertices d (largestRadius d O) L ≠ ∅ →
      sigma*largestRadius d O ≤ L ∧ L ≤ densityScale d O (γ-1) →
      splitExpectation d O (γ-1) (largestRadius d O) L ≤
        chi*largeMass d O (γ-1)/L * Real.log (1+12*sigma/(γ-1)^2)) :
    (densityScale d O (γ - 1) < sigma * largestRadius d O →
      (largeClusters d O (γ - 1)).card ≤ fewBound (γ - 1)) ∧
    (sigma * largestRadius d O ≤ densityScale d O (γ - 1) →
      ∃ j : ℕ, 9 ≤ j ∧ j ≤ ⌈Real.logb 2 n⌉₊ ∧
        let L := (2 : ℝ) ^ j * largestRadius d O
        sigma * largestRadius d O ≤ L ∧ L ≤ densityScale d O (γ - 1) ∧
        densityScale d O (γ - 1) < 2 * L ∧ largeMass d O (γ - 1) / L < 8 / (γ - 1) ∧
        (orderLaw (netVertices d (largestRadius d O) L))
          {π | ∃ Q ∈ randomPartitions d (γ - 1) (largestRadius d O) L π,
            splitCount d O (γ - 1) Q ≤ splitBound (γ - 1)} ≥ (1 / 3 : ENNReal)) := by
  let ε := γ-1
  let R := largestRadius d O
  let M := largeMass d O ε
  let ρ := densityScale d O ε
  have e0 : 0 < ε := sub_pos.mpr hγ.1
  have e1 : ε < 1 := by dsimp [ε]; linarith [hγ.2]
  have r0 : 0 < R := GrowthAux.largest_pos hd hO.1 hkn
  have alt := clustering_scale_selection d hd O hO.1 hkn ε e0 e1
  constructor
  · intro small
    rcases alt with h|⟨j,_,_,lo,hi,_⟩
    · exact h.2
    · exact ((lo.trans hi).not_gt small).elim
  · intro big
    rcases alt with h|⟨j,jlo,jhi,lo,hi,near,mass⟩
    · exact (h.1.not_ge big).elim
    let L := (2:ℝ)^j*R
    have pos : 0 < L := by dsimp [L]; positivity
    refine ⟨j,jlo,jhi,lo,hi,near,mass,?_⟩
    by_cases empty : netVertices d R L = ∅
    · have allGood (π : List (Point n)) : ∃ Q ∈ randomPartitions d ε R L π, splitCount d O ε Q ≤ splitBound ε := by
        obtain ⟨Q,hQ,q⟩ := empty_net_partition d hd O hO.1 ε L empty π
        exact ⟨Q,hQ,by rw [q]; exact Nat.zero_le _⟩
      have setEq : {π | ∃ Q ∈ randomPartitions d ε R L π, splitCount d O ε Q ≤ splitBound ε} = Set.univ :=
        Set.eq_univ_of_forall allGood
      letI := order_probability (netVertices d R L)
      change (1/3:ℝ≥0∞) ≤ (orderLaw (netVertices d R L)) _
      rw [setEq,measure_univ]; norm_num
    · exact enumerated_success d O ε R L pos empty (splitBound ε)
        ((expected L empty ⟨lo,hi⟩).trans (expectation_budget e0 pos mass))
end StableMSR.Recovery.Supplement
open StableMSR.Recovery.Supplement
theorem solution {n k : ℕ} (d : Point n → Point n → ℝ) (γ : ℝ) (O : Partition n)
    (hk : 1 ≤ k) (hkn : k < n) (hd : IsMetricArray d) (hγ : 1 < γ ∧ γ < 2)
    (hO : Stable d k γ O) :
    (densityScale d O (γ - 1) < sigma * largestRadius d O →
      (largeClusters d O (γ - 1)).card ≤ fewBound (γ - 1)) ∧
    (sigma * largestRadius d O ≤ densityScale d O (γ - 1) →
      ∃ j : ℕ, 9 ≤ j ∧ j ≤ ⌈Real.logb 2 n⌉₊ ∧
        let L := (2 : ℝ) ^ j * largestRadius d O
        sigma * largestRadius d O ≤ L ∧ L ≤ densityScale d O (γ - 1) ∧
        densityScale d O (γ - 1) < 2 * L ∧ largeMass d O (γ - 1) / L < 8 / (γ - 1) ∧
        (orderLaw (netVertices d (largestRadius d O) L))
          {π | ∃ Q ∈ randomPartitions d (γ - 1) (largestRadius d O) L π,
            splitCount d O (γ - 1) Q ≤ splitBound (γ - 1)} ≥ (1 / 3 : ENNReal)) := by
  apply partition_scale_of_expectation d γ O hk hkn hd hγ hO
  intro L live range
  exact (split_probability d γ L O hk hkn hd hγ hO live range).2
