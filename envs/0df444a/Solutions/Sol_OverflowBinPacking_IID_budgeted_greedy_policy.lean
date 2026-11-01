-- Prove2me | solution 1 for OverflowBinPacking.IID.budgeted_greedy_policy
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T02:27:17.459886+00:00
-- url     : https://prove2.me/submissions/aed3630a-8ad4-435e-a388-426c74c25716

import Mathlib
import Definitions.Def_OverflowBinPacking_IID_BudgetedGreedy

open MeasureTheory OverflowBinPacking.IID

namespace OBPX

variable {n : ℕ} (μ : Fin n → Measure ℝ) (C γ : ℝ) (x : Fin n → ℝ)

lemma bgPrefix_succ_lt (t : ℕ) (h : t < n) :
    bgPrefix μ C γ x (t + 1) = bgPrefix μ C γ x t ++ [bgChoice μ C γ x (bgPrefix μ C γ x t) ⟨t, h⟩] := by
  rw [bgPrefix]; simp [h]

lemma bgPrefix_succ_ge (t : ℕ) (h : n ≤ t) :
    bgPrefix μ C γ x (t + 1) = bgPrefix μ C γ x t := by
  rw [bgPrefix]; simp [Nat.not_lt.mpr h]

lemma bgPrefix_length (t : ℕ) : (bgPrefix μ C γ x t).length = min t n := by
  induction t with
  | zero => simp [bgPrefix]
  | succ t ih =>
    by_cases h : t < n
    · rw [bgPrefix_succ_lt μ C γ x t h]; simp [ih]; omega
    · rw [bgPrefix_succ_ge μ C γ x t (by omega), ih]; omega

lemma bgPrefix_prefix (t s : ℕ) (h : t ≤ s) : bgPrefix μ C γ x t <+: bgPrefix μ C γ x s := by
  induction s, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ s hs ih =>
    by_cases h : s < n
    · rw [bgPrefix_succ_lt μ C γ x s h]; exact ih.trans (List.prefix_append _ _)
    · rw [bgPrefix_succ_ge μ C γ x s (by omega)]; exact ih

lemma bgRule_eq_choice (i : Fin n) :
    bgRule μ C γ i x = bgChoice μ C γ x (bgPrefix μ C γ x i.val) i := by
  unfold bgRule
  rw [bgPrefix_succ_lt μ C γ x i.val i.isLt]
  have hl : (bgPrefix μ C γ x i.val).length = i.val := by
    rw [bgPrefix_length]; omega
  simp [List.getElem?_append_right, hl]

lemma bgPrefix_getElem? (t : ℕ) (ht : t ≤ n) (k : Fin n) :
    (bgPrefix μ C γ x t)[k.val]? = if k.val < t then some (bgRule μ C γ k x) else none := by
  split_ifs with hk
  · have hpre := bgPrefix_prefix μ C γ x (k.val + 1) t (by omega)
    have hl : (bgPrefix μ C γ x (k.val + 1)).length = k.val + 1 := by
      rw [bgPrefix_length]; omega
    obtain ⟨l, hl2⟩ := hpre
    rw [← hl2, List.getElem?_append_left (by omega)]
    rw [bgRule_eq_choice, bgPrefix_succ_lt μ C γ x k.val k.isLt]
    have hl' : (bgPrefix μ C γ x k.val).length = k.val := by
      rw [bgPrefix_length]; omega
    simp [List.getElem?_append_right, hl']
  · rw [List.getElem?_eq_none]; rw [bgPrefix_length]; omega

/-- loads computed from the rule agree with prefix loads. -/
lemma usage_bg (j : Fin n) (t : ℕ) (ht : t ≤ n) :
    usage (bgRule μ C γ) x j t = prefixUsage x (bgPrefix μ C γ x t) j := by
  unfold usage prefixUsage
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, bgPrefix_getElem? μ C γ x t ht k]
  split_ifs with hk <;> simp [hk]

lemma take_bgPrefix (t k : ℕ) (hk : k ≤ t) :
    (bgPrefix μ C γ x t).take k = bgPrefix μ C γ x k := by
  have hpre := bgPrefix_prefix μ C γ x k t hk
  have hl : (bgPrefix μ C γ x k).length = min k n := bgPrefix_length μ C γ x k
  obtain ⟨l, hl'⟩ := hpre
  by_cases hkn : k ≤ n
  · rw [← hl', List.take_left' (by rw [hl]; omega)]
  · -- k > n: both equal bgPrefix n
    have h1 : bgPrefix μ C γ x t = bgPrefix μ C γ x k := by
      have := bgPrefix_length μ C γ x t
      have hlen : (bgPrefix μ C γ x t).length = (bgPrefix μ C γ x k).length := by
        rw [this, hl]; omega
      rw [← hl'] at hlen ⊢
      simp at hlen
      rw [hlen]; simp
    rw [h1]; apply List.take_of_length_le; rw [hl]; omega

lemma riskUpTo_bg (j : Fin n) (t : ℕ) (ht : t ≤ n) :
    riskUpTo μ (bgRule μ C γ) x j t = prefixRisk μ x (bgPrefix μ C γ x t) j := by
  unfold riskUpTo prefixRisk
  have hset : (Finset.univ.filter (fun k : Fin n => (k : ℕ) < t ∧ bgRule μ C γ k x = j)) =
      Finset.univ.filter (fun k : Fin n => (bgPrefix μ C γ x t)[k.val]? = some j) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, bgPrefix_getElem? μ C γ x t ht k]
    split_ifs with hk <;> simp [hk]
  rw [hset]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, bgPrefix_getElem? μ C γ x t ht k] at hk
  have hkt : k.val < t := by split_ifs at hk with h; exact h
  rw [usage_bg μ C γ x j k.val (by omega), take_bgPrefix μ C γ x t k.val hkt.le]

end OBPX

namespace OBPX

variable {n : ℕ} (μ : Fin n → Measure ℝ) (C γ : ℝ)

lemma prefixUsage_congr (x y : Fin n → ℝ) (p : List (Fin n))
    (hxy : ∀ k : Fin n, k.val < p.length → x k = y k) (j : Fin n) :
    prefixUsage x p j = prefixUsage y p j := by
  unfold prefixUsage
  refine Finset.sum_congr rfl (fun k hk => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
  apply hxy
  by_contra h
  rw [List.getElem?_eq_none (by omega)] at hk
  simp at hk

lemma prefixRisk_congr (x y : Fin n → ℝ) (p : List (Fin n))
    (hxy : ∀ k : Fin n, k.val < p.length → x k = y k) (j : Fin n) :
    prefixRisk μ x p j = prefixRisk μ y p j := by
  unfold prefixRisk
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [prefixUsage_congr x y (p.take k.val) (fun k' hk' => hxy k' (by simp at hk'; omega)) j]

lemma bgChoice_congr (x y : Fin n → ℝ) (p : List (Fin n))
    (hxy : ∀ k : Fin n, k.val < p.length → x k = y k) (i : Fin n) :
    bgChoice μ C γ x p i = bgChoice μ C γ y p i := by
  have hU := prefixUsage_congr x y p hxy
  have hR := prefixRisk_congr μ x y p hxy
  unfold bgChoice
  simp only [hU, hR]

lemma bgPrefix_congr (x y : Fin n → ℝ) (t : ℕ) (hxy : ∀ k : Fin n, k.val < t → x k = y k) :
    bgPrefix μ C γ x (t + 1) = bgPrefix μ C γ y (t + 1) := by
  induction t with
  | zero =>
    by_cases h : 0 < n
    · rw [bgPrefix_succ_lt μ C γ x 0 h, bgPrefix_succ_lt μ C γ y 0 h]
      simp only [bgPrefix, List.nil_append]
      rw [bgChoice_congr μ C γ x y [] (fun k hk => by simp at hk)]
    · rw [bgPrefix_succ_ge μ C γ x 0 (by omega), bgPrefix_succ_ge μ C γ y 0 (by omega)]
      rfl
  | succ t ih =>
    have ih' := ih (fun k hk => hxy k (by omega))
    by_cases h : t + 1 < n
    · rw [bgPrefix_succ_lt μ C γ x (t+1) h, bgPrefix_succ_lt μ C γ y (t+1) h, ih']
      rw [bgChoice_congr μ C γ x y _ (fun k hk => hxy k (by
        rw [bgPrefix_length] at hk; omega))]
    · rw [bgPrefix_succ_ge μ C γ x (t+1) (by omega), bgPrefix_succ_ge μ C γ y (t+1) (by omega), ih']

lemma bg_nonanticipative : Nonanticipative (bgRule μ C γ) := by
  intro i x y hxy
  unfold bgRule
  rw [bgPrefix_congr μ C γ x y i.val (fun k hk => hxy k hk)]

lemma prefixUsage_unused (x : Fin n → ℝ) (p : List (Fin n)) (j : Fin n)
    (hj : j ∉ prefixOpened p) : prefixUsage x p j = 0 := by
  unfold prefixUsage
  apply Finset.sum_eq_zero
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
  exfalso; apply hj
  simp only [prefixOpened, List.mem_toFinset]
  exact List.mem_of_getElem? hk

lemma bgChoice_usage_le (x : Fin n → ℝ) (p : List (Fin n)) (hp : p.length < n) (i : Fin n) :
    prefixUsage x p (bgChoice μ C γ x p i) ≤ 1 := by
  classical
  unfold bgChoice
  simp only
  split_ifs with he hu
  · have := Finset.min'_mem _ he
    simp only [Finset.mem_filter] at this
    convert this.2.1
  · rw [prefixUsage_unused x p _ (Finset.mem_filter.mp (Finset.min'_mem _ hu)).2]
    norm_num
  · exfalso; apply hu
    have hcard : p.toFinset.card < (Finset.univ : Finset (Fin n)).card := by
      calc p.toFinset.card ≤ p.length := List.toFinset_card_le p
        _ < n := hp
        _ = _ := by simp
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩

lemma bg_feasible : Feasible (bgRule μ C γ) := by
  intro x i
  rw [usage_bg μ C γ x _ i.val i.isLt.le, bgRule_eq_choice]
  apply bgChoice_usage_le
  rw [bgPrefix_length]; omega

end OBPX

namespace OBPX

variable {n : ℕ} (μ : Fin n → Measure ℝ) (C γ : ℝ)

lemma measurable_prefixUsage (p : List (Fin n)) (j : Fin n) :
    Measurable (fun x : Fin n → ℝ => prefixUsage x p j) := by
  unfold prefixUsage
  exact Finset.measurable_sum _ (fun k _ => measurable_pi_apply k)

lemma measurable_overflowProb (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Measurable (fun S : ℝ => overflowProb ν S) := by
  apply Monotone.measurable
  intro a b hab
  unfold overflowProb
  apply measureReal_mono
  · intro z hz; simp only [Set.mem_Ioi] at hz ⊢; linarith
  · exact measure_ne_top _ _

lemma measurable_prefixRisk (hμ : ∀ i, IsProbabilityMeasure (μ i)) (p : List (Fin n)) (j : Fin n) :
    Measurable (fun x : Fin n → ℝ => prefixRisk μ x p j) := by
  unfold prefixRisk
  exact Finset.measurable_sum _ (fun k _ =>
    (measurable_overflowProb (μ k)).comp (measurable_prefixUsage _ j))

/-- Budgeted Greedy's choice as a function of the eligibility vector. -/
noncomputable def choiceOf (p : List (Fin n)) (i : Fin n) (b : Fin n → Bool) : Fin n := by
  classical
  let eligible : Finset (Fin n) := (prefixOpened p).filter fun j => b j = true
  if he : eligible.Nonempty then
    exact eligible.min' he
  else
    let unused : Finset (Fin n) := Finset.univ.filter fun j => j ∉ prefixOpened p
    if hu : unused.Nonempty then
      exact unused.min' hu
    else
      exact i

lemma bgChoice_eq_choiceOf (x : Fin n → ℝ) (p : List (Fin n)) (i : Fin n) :
    bgChoice μ C γ x p i = choiceOf p i (fun j => decide (prefixUsage x p j ≤ 1 ∧
      prefixRisk μ x p j + overflowProb (μ i) (prefixUsage x p j) ≤ γ / C)) := by
  unfold bgChoice choiceOf
  simp only [decide_eq_true_eq]

lemma measurable_bgChoice (hμ : ∀ i, IsProbabilityMeasure (μ i)) (p : List (Fin n)) (i : Fin n) :
    Measurable (fun x => bgChoice μ C γ x p i) := by
  have hb : Measurable (fun x : Fin n → ℝ => (fun j => decide (prefixUsage x p j ≤ 1 ∧
      prefixRisk μ x p j + overflowProb (μ i) (prefixUsage x p j) ≤ γ / C))) := by
    refine measurable_pi_iff.mpr (fun j => ?_)
    refine measurable_to_countable' (fun b => ?_)
    have hs : MeasurableSet {x : Fin n → ℝ | prefixUsage x p j ≤ 1 ∧
        prefixRisk μ x p j + overflowProb (μ i) (prefixUsage x p j) ≤ γ / C} :=
      (measurableSet_le (measurable_prefixUsage p j) measurable_const).inter
        (measurableSet_le ((measurable_prefixRisk μ hμ p j).add
          ((measurable_overflowProb (μ i)).comp (measurable_prefixUsage p j))) measurable_const)
    cases b
    · have : (fun x : Fin n → ℝ => decide (prefixUsage x p j ≤ 1 ∧
          prefixRisk μ x p j + overflowProb (μ i) (prefixUsage x p j) ≤ γ / C)) ⁻¹' {false} =
          {x | prefixUsage x p j ≤ 1 ∧
          prefixRisk μ x p j + overflowProb (μ i) (prefixUsage x p j) ≤ γ / C}ᶜ := by
        ext x; simp
      rw [this]; exact hs.compl
    · have : (fun x : Fin n → ℝ => decide (prefixUsage x p j ≤ 1 ∧
          prefixRisk μ x p j + overflowProb (μ i) (prefixUsage x p j) ≤ γ / C)) ⁻¹' {true} =
          {x | prefixUsage x p j ≤ 1 ∧
          prefixRisk μ x p j + overflowProb (μ i) (prefixUsage x p j) ≤ γ / C} := by
        ext x; simp
      rw [this]; exact hs
  have hc : Measurable (choiceOf p i) := measurable_of_countable _
  have := hc.comp hb
  convert this using 1
  funext x
  exact bgChoice_eq_choiceOf μ C γ x p i

lemma measurableSet_bgPrefix_eq (hμ : ∀ i, IsProbabilityMeasure (μ i)) (t : ℕ)
    (q : List (Fin n)) : MeasurableSet {x | bgPrefix μ C γ x t = q} := by
  induction t generalizing q with
  | zero =>
    by_cases h : ([] : List (Fin n)) = q
    · simp [bgPrefix, h]
    · simp [bgPrefix, h]
  | succ t ih =>
    by_cases h : t < n
    · have : {x | bgPrefix μ C γ x (t+1) = q} = ⋃ p : List (Fin n),
          ({x | bgPrefix μ C γ x t = p} ∩
            (fun x => bgChoice μ C γ x p ⟨t, h⟩) ⁻¹' {j | p ++ [j] = q}) := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
          bgPrefix_succ_lt μ C γ x t h]
        constructor
        · intro hx; exact ⟨_, rfl, hx⟩
        · rintro ⟨p, hp, hq⟩; rw [hp]; exact hq
      rw [this]
      exact MeasurableSet.iUnion (fun p => (ih p).inter
        (measurable_bgChoice μ C γ hμ p _ (MeasurableSet.of_discrete)))
    · have : {x | bgPrefix μ C γ x (t+1) = q} = {x | bgPrefix μ C γ x t = q} := by
        ext x; simp [bgPrefix_succ_ge μ C γ x t (by omega)]
      rw [this]; exact ih q

lemma bg_measurable (hμ : ∀ i, IsProbabilityMeasure (μ i)) : MeasurableRule (bgRule μ C γ) := by
  intro i j
  have : {x | bgRule μ C γ i x = j} = ⋃ p : List (Fin n),
      ({x | bgPrefix μ C γ x i.val = p} ∩ (fun x => bgChoice μ C γ x p i) ⁻¹' {j}) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, bgRule_eq_choice]
    constructor
    · intro hx; exact ⟨_, rfl, hx⟩
    · rintro ⟨p, hp, hq⟩; rw [hp]; exact hq
  rw [this]
  exact MeasurableSet.iUnion (fun p => (measurableSet_bgPrefix_eq μ C γ hμ _ p).inter
    (measurable_bgChoice μ C γ hμ p i (MeasurableSet.of_discrete)))

lemma bg_isPolicy (hμ : ∀ i, IsProbabilityMeasure (μ i)) : IsPolicy (bgRule μ C γ) :=
  ⟨bg_nonanticipative μ C γ, bg_measurable μ C γ hμ, bg_feasible μ C γ⟩

end OBPX

open OverflowBinPacking.IID in
theorem solution {n : ℕ} (μ : Fin n → Measure ℝ)
    (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hμ0 : ∀ i, μ i (Set.Iio 0) = 0)
    (C γ : ℝ) (hC : 1 ≤ C) (hγ : 1 ≤ γ) :
    IsPolicy (bgRule μ C γ) :=
  OBPX.bg_isPolicy μ C γ hμ
