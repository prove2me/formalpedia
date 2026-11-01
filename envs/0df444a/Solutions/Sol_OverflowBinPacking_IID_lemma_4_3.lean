-- Prove2me | solution 1 for OverflowBinPacking.IID.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T03:04:05.372474+00:00
-- url     : https://prove2.me/submissions/ec02ec37-6b40-4a73-a7ed-c5e0db7cdb0a

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


open MeasureTheory OverflowBinPacking.IID

namespace OBPX

variable {n : ℕ}

lemma usage_succ (a : Rule n) (x : Fin n → ℝ) (j : Fin n) (i : Fin n) :
    usage a x j (i.val + 1) = usage a x j i.val + (if a i x = j then x i else 0) := by
  classical
  unfold usage
  simp_rw [Finset.sum_filter]
  have : ∀ k : Fin n, (if (k : ℕ) < i.val + 1 ∧ a k x = j then x k else 0) =
      (if (k : ℕ) < i.val ∧ a k x = j then x k else 0) +
        (if i = k then (if a k x = j then x k else 0) else 0) := by
    intro k
    by_cases hik : i = k
    · subst hik; simp
    · have : (k : ℕ) ≠ i.val := fun h => hik (Fin.ext h.symm)
      by_cases hk : (k : ℕ) < i.val
      · simp [hk, hik, show (k : ℕ) < i.val + 1 by omega]
      · simp [hk, hik, show ¬ (k : ℕ) < i.val + 1 by omega]
  rw [Finset.sum_congr rfl (fun k _ => this k), Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp

lemma usage_zero (a : Rule n) (x : Fin n → ℝ) (j : Fin n) : usage a x j 0 = 0 := by
  unfold usage; simp

lemma usage_mono (a : Rule n) (x : Fin n → ℝ) (hx : ∀ k, 0 ≤ x k) (j : Fin n) {s t : ℕ}
    (hst : s ≤ t) : usage a x j s ≤ usage a x j t := by
  unfold usage
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  · intro k _ _; exact hx k

lemma usage_nonneg (a : Rule n) (x : Fin n → ℝ) (hx : ∀ k, 0 ≤ x k) (j : Fin n) (t : ℕ) :
    0 ≤ usage a x j t := by
  unfold usage; exact Finset.sum_nonneg (fun k _ => hx k)

/-- Deterministic identity: a bin breaks iff exactly one item overflows it. -/
lemma card_overflow_items (a : Rule n) (ha : Feasible a) (x : Fin n → ℝ) (hx : ∀ k, 0 ≤ x k)
    (j : Fin n) :
    (Finset.univ.filter (fun i : Fin n => a i x = j ∧ 1 < usage a x j i + x i)).card =
      if 1 < usage a x j n then 1 else 0 := by
  classical
  set F := Finset.univ.filter (fun i : Fin n => a i x = j ∧ 1 < usage a x j i + x i) with hF
  have hmemF : ∀ i, i ∈ F ↔ a i x = j ∧ 1 < usage a x j i + x i := by
    intro i; simp [hF]
  have hsucc : ∀ i : Fin n, a i x = j → usage a x j (i.val + 1) = usage a x j i + x i := by
    intro i hi; rw [usage_succ]; simp [hi]
  have hle1 : F.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi i' hi'
    rw [hmemF] at hi hi'
    by_contra hne
    have key : ∀ i i' : Fin n, a i x = j ∧ 1 < usage a x j i + x i →
        a i' x = j → i < i' → False := by
      intro i i' hi hi' hlt
      have h1 := hsucc i hi.1
      have h2 := usage_mono a x hx j (show i.val + 1 ≤ i'.val by omega)
      have h3 := ha x i'
      rw [hi'] at h3
      linarith [hi.2]
    rcases lt_or_gt_of_ne hne with h | h
    · exact key i i' hi hi'.1 h
    · exact key i' i hi' hi.1 h
  split_ifs with hb
  · apply le_antisymm hle1
    rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty]
    -- find the first time the load exceeds one
    have hex : ∃ t, 1 < usage a x j t := ⟨n, hb⟩
    let t := Nat.find hex
    have ht : 1 < usage a x j t := Nat.find_spec hex
    have htn : t ≤ n := Nat.find_min' hex hb
    have ht0 : t ≠ 0 := by
      intro h0; rw [show t = 0 from h0, usage_zero] at ht; linarith
    obtain ⟨s, hs⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have hsn : s < n := by omega
    have hsle : ¬ 1 < usage a x j s := Nat.find_min hex (by omega)
    have := usage_succ a x j ⟨s, hsn⟩
    simp only at this
    rw [← hs] at this
    by_cases has : a ⟨s, hsn⟩ x = j
    · refine ⟨⟨s, hsn⟩, (hmemF _).mpr ⟨has, ?_⟩⟩
      simp only [has, if_true] at this
      simp only
      linarith
    · simp only [has, if_false, add_zero] at this
      exact absurd (this ▸ ht) hsle
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro i hi
    rw [hmemF] at hi
    have h1 := hsucc i hi.1
    have h2 := usage_mono a x hx j (show i.val + 1 ≤ n by omega)
    exact hb (by linarith [hi.2])

lemma measurable_usage (a : Rule n) (ha : MeasurableRule a) (j : Fin n) (t : ℕ) :
    Measurable (fun x => usage a x j t) := by
  classical
  unfold usage
  simp_rw [Finset.sum_filter]
  refine Finset.measurable_sum _ (fun k _ => ?_)
  refine Measurable.ite ?_ (measurable_pi_apply k) measurable_const
  by_cases hk : (k : ℕ) < t
  · simpa [hk] using ha k j
  · simp [hk]

lemma measurable_overflowProb' (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Measurable (fun S : ℝ => overflowProb ν S) := by
  apply Monotone.measurable
  intro a b hab
  unfold overflowProb
  apply measureReal_mono
  · intro z hz; simp only [Set.mem_Ioi] at hz ⊢; linarith
  · exact measure_ne_top _ _

/-- Freezing coordinate `i`: integrating the overflow indicator of item `i` against
quantities not depending on `x i` yields the overflow probability. -/
lemma freeze (μ : Fin n → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i)) (i : Fin n)
    (P : (Fin n → ℝ) → Prop) [DecidablePred P] (hP : MeasurableSet {x | P x})
    (hPinv : ∀ x t, P (Function.update x i t) ↔ P x)
    (h : (Fin n → ℝ) → ℝ) (hh : Measurable h) (hhinv : ∀ x t, h (Function.update x i t) = h x) :
    ∫⁻ x, (if P x ∧ 1 < h x + x i then (1 : ENNReal) else 0) ∂(Measure.pi μ) =
      ∫⁻ x, (if P x then ENNReal.ofReal (overflowProb (μ i) (h x)) else 0) ∂(Measure.pi μ) := by
  classical
  apply lintegral_eq_of_lmarginal_eq {i}
  · refine Measurable.ite (hP.inter (measurableSet_lt measurable_const
      (hh.add (measurable_pi_apply i)))) measurable_const measurable_const
  · refine Measurable.ite hP (ENNReal.measurable_ofReal.comp
      ((measurable_overflowProb' (μ i)).comp hh)) measurable_const
  · funext x
    rw [lmarginal_singleton, lmarginal_singleton]
    simp only [hPinv, hhinv, Function.update_self]
    by_cases hPx : P x
    · simp only [hPx, true_and, if_true, lintegral_const, measure_univ, mul_one]
      have : (fun t : ℝ => if 1 < h x + t then (1 : ENNReal) else 0) =
          (Set.Ioi (1 - h x)).indicator 1 := by
        funext t
        simp only [Set.indicator, Set.mem_Ioi, Pi.one_apply]
        congr 1; apply propext; constructor <;> intro <;> linarith
      rw [this, lintegral_indicator_one measurableSet_Ioi, overflowProb,
        ofReal_measureReal (measure_ne_top _ _)]
    · simp [hPx]

end OBPX

namespace OBPX

variable {n : ℕ}

lemma ae_nonneg (μ : Fin n → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hμ0 : ∀ i, μ i (Set.Iio 0) = 0) :
    ∀ᵐ x ∂(Measure.pi μ), ∀ k, 0 ≤ x k := by
  rw [ae_all_iff]
  intro k
  have : Measure.pi μ (Function.eval k ⁻¹' Set.Iio 0) = 0 :=
    Measure.pi_eval_preimage_null μ (hμ0 k)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp this] with x hx
  simpa using hx

lemma usage_update_self (a : Rule n) (ha : Nonanticipative a) (x : Fin n → ℝ) (j i : Fin n)
    (t : ℝ) : usage a (Function.update x i t) j i = usage a x j i := by
  classical
  unfold usage
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases hk : (k : ℕ) < i.val
  · have hne : k ≠ i := fun e => by rw [e] at hk; exact lt_irrefl _ hk
    have h1 : a k (Function.update x i t) = a k x := by
      refine ha k _ _ (fun k' hk' => ?_)
      have : k' ≠ i := fun e => by
        rw [e] at hk'; exact absurd (lt_trans hk' (Fin.lt_def.mpr hk)) (lt_irrefl _)
      exact Function.update_of_ne this _ _
    simp [hk, h1, Function.update_of_ne hne]
  · simp [hk]

lemma rule_update_self (a : Rule n) (ha : Nonanticipative a) (x : Fin n → ℝ) (i : Fin n)
    (t : ℝ) : a i (Function.update x i t) = a i x := by
  refine ha i _ _ (fun k' hk' => ?_)
  exact Function.update_of_ne (ne_of_lt hk') _ _

lemma measurable_risk (μ : Fin n → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (a : Rule n) (ha : MeasurableRule a) (j : Fin n) :
    Measurable (fun x => risk μ a x j) := by
  classical
  unfold risk riskUpTo
  simp_rw [Finset.sum_filter]
  refine Finset.measurable_sum _ (fun k _ => ?_)
  refine Measurable.ite ?_ ((measurable_overflowProb' (μ k)).comp
    (measurable_usage a ha j k)) measurable_const
  simpa using ha k j

lemma risk_eq_sum (μ : Fin n → Measure ℝ) (a : Rule n) (x : Fin n → ℝ) (j : Fin n) :
    risk μ a x j = ∑ k : Fin n, if a k x = j then overflowProb (μ k) (usage a x j k) else 0 := by
  classical
  unfold risk riskUpTo
  rw [Finset.sum_filter]
  simp

lemma overflowProb_nonneg (ν : Measure ℝ) (S : ℝ) : 0 ≤ overflowProb ν S := measureReal_nonneg

lemma overflowProb_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν] (S : ℝ) :
    overflowProb ν S ≤ 1 := measureReal_le_one

lemma risk_nonneg (μ : Fin n → Measure ℝ) (a : Rule n) (x : Fin n → ℝ) (j : Fin n) :
    0 ≤ risk μ a x j := by
  rw [risk_eq_sum]
  exact Finset.sum_nonneg (fun k _ => by split_ifs <;> simp [overflowProb_nonneg])

lemma per_bin (μ : Fin n → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hμ0 : ∀ i, μ i (Set.Iio 0) = 0) (a : Rule n) (ha : IsPolicy a) (j : Fin n) :
    Measure.pi μ {x | 1 < usage a x j n} =
      ∫⁻ x, ENNReal.ofReal (risk μ a x j) ∂(Measure.pi μ) := by
  classical
  have hmS : MeasurableSet {x : Fin n → ℝ | 1 < usage a x j n} :=
    measurableSet_lt measurable_const (measurable_usage a ha.2.1 j n)
  have hmeasP : ∀ i : Fin n, MeasurableSet {x : Fin n → ℝ | a i x = j} := fun i => ha.2.1 i j
  calc Measure.pi μ {x | 1 < usage a x j n}
      = ∫⁻ x, (if 1 < usage a x j n then (1 : ENNReal) else 0) ∂(Measure.pi μ) := by
        rw [← lintegral_indicator_one hmS]
        congr 1
    _ = ∫⁻ x, ∑ i : Fin n, (if a i x = j ∧ 1 < usage a x j i + x i then (1 : ENNReal) else 0)
          ∂(Measure.pi μ) := by
        apply lintegral_congr_ae
        filter_upwards [ae_nonneg μ hμ hμ0] with x hx
        have hc := card_overflow_items a ha.2.2 x hx j
        rw [Finset.card_filter] at hc
        have := congrArg (fun m : ℕ => (m : ENNReal)) hc
        simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at this
        exact this.symm
    _ = ∑ i : Fin n, ∫⁻ x, (if a i x = j ∧ 1 < usage a x j i + x i then (1 : ENNReal) else 0)
          ∂(Measure.pi μ) := by
        refine lintegral_finsetSum _ (fun i _ => ?_)
        exact Measurable.ite ((hmeasP i).inter (measurableSet_lt measurable_const
          ((measurable_usage a ha.2.1 j i).add (measurable_pi_apply i)))) measurable_const
          measurable_const
    _ = ∑ i : Fin n, ∫⁻ x, (if a i x = j then ENNReal.ofReal (overflowProb (μ i)
          (usage a x j i)) else 0) ∂(Measure.pi μ) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact freeze μ hμ i (fun x => a i x = j) (hmeasP i)
          (fun x t => by simp only [rule_update_self a ha.1 x i t])
          (fun x => usage a x j i) (measurable_usage a ha.2.1 j i)
          (fun x t => usage_update_self a ha.1 x j i t)
    _ = ∫⁻ x, ∑ i : Fin n, (if a i x = j then ENNReal.ofReal (overflowProb (μ i)
          (usage a x j i)) else 0) ∂(Measure.pi μ) := by
        refine (lintegral_finsetSum _ (fun i _ => ?_)).symm
        exact Measurable.ite (hmeasP i) (ENNReal.measurable_ofReal.comp
          ((measurable_overflowProb' (μ i)).comp (measurable_usage a ha.2.1 j i)))
          measurable_const
    _ = ∫⁻ x, ENNReal.ofReal (risk μ a x j) ∂(Measure.pi μ) := by
        congr 1; funext x
        rw [risk_eq_sum, ENNReal.ofReal_sum_of_nonneg
          (fun k _ => by split_ifs <;> simp [overflowProb_nonneg])]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        split_ifs <;> simp

lemma prop31 (μ : Fin n → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hμ0 : ∀ i, μ i (Set.Iio 0) = 0) (a : Rule n) (ha : IsPolicy a) :
    (∀ j : Fin n,
      (Measure.pi μ).real {x | 1 < usage a x j n} =
        ∫ x, risk μ a x j ∂(Measure.pi μ)) ∧
    (∫ x, (numBroken a x : ℝ) ∂(Measure.pi μ)) =
      ∫ x, (∑ j : Fin n, risk μ a x j) ∂(Measure.pi μ) := by
  classical
  have h1 : ∀ j : Fin n, (Measure.pi μ).real {x | 1 < usage a x j n} =
      ∫ x, risk μ a x j ∂(Measure.pi μ) := by
    intro j
    rw [measureReal_def, per_bin μ hμ hμ0 a ha j, integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun x => risk_nonneg μ a x j))
      (measurable_risk μ hμ a ha.2.1 j).aestronglyMeasurable]
  refine ⟨h1, ?_⟩
  have hint : ∀ j : Fin n, Integrable (fun x => risk μ a x j) (Measure.pi μ) := by
    intro j
    refine Integrable.of_bound (measurable_risk μ hμ a ha.2.1 j).aestronglyMeasurable (n : ℝ)
      (Filter.Eventually.of_forall (fun x => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (risk_nonneg μ a x j), risk_eq_sum]
    calc _ ≤ ∑ k : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun k _ => by
            split_ifs
            · exact overflowProb_le_one _ _
            · norm_num)
      _ = n := by simp
  have hB : (fun x => (numBroken a x : ℝ)) =
      fun x => ∑ j : Fin n, ({x | 1 < usage a x j n}).indicator (1 : (Fin n → ℝ) → ℝ) x := by
    funext x
    rw [numBroken, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [Set.indicator]
  rw [hB, integral_finsetSum _ (fun j _ => ?_), integral_finsetSum _ (fun j _ => hint j)]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_indicator_one (measurableSet_lt measurable_const
      (measurable_usage a ha.2.1 j n)), h1 j]
  · exact (integrable_const (1 : ℝ)).indicator (measurableSet_lt measurable_const
      (measurable_usage a ha.2.1 j n))

end OBPX


open MeasureTheory OverflowBinPacking.IID

namespace OBPX

variable {n : ℕ}

lemma prefixRisk_not_opened (μ : Fin n → Measure ℝ) (x : Fin n → ℝ) (p : List (Fin n))
    (j : Fin n) (hj : j ∉ prefixOpened p) : prefixRisk μ x p j = 0 := by
  unfold prefixRisk
  apply Finset.sum_eq_zero
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
  exfalso; apply hj
  simp only [prefixOpened, List.mem_toFinset]
  exact List.mem_of_getElem? hk

lemma prefixRisk_append (μ : Fin n → Measure ℝ) (x : Fin n → ℝ) (p : List (Fin n))
    (t : Fin n) (hp : p.length = t.val) (c j : Fin n) :
    prefixRisk μ x (p ++ [c]) j = prefixRisk μ x p j +
      (if c = j then overflowProb (μ t) (prefixUsage x p j) else 0) := by
  classical
  unfold prefixRisk
  rw [Finset.sum_filter, Finset.sum_filter]
  have : (if c = j then overflowProb (μ t) (prefixUsage x p j) else 0) =
      ∑ k : Fin n, if t = k then (if c = j then overflowProb (μ k)
        (prefixUsage x (p.take k.val) j) else 0) else 0 := by
    rw [Finset.sum_ite_eq]; simp [List.take_of_length_le, hp]
  rw [this, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rcases lt_trichotomy k.val t.val with h | h | h
  · have htk : t ≠ k := fun e => by rw [e] at h; exact lt_irrefl _ h
    rw [List.getElem?_append_left (by omega), List.take_append_of_le_length (by omega)]
    simp [htk]
  · have htk : t = k := Fin.ext h.symm
    subst htk
    rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (l := p) (by omega)]
    simp [hp, List.take_append_of_le_length]
    rw [show List.take (↑t) p = p from List.take_of_length_le (by omega)]
  · have htk : t ≠ k := fun e => by rw [e] at h; exact lt_irrefl _ h
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (l := p) (by omega)]
    simp [htk]

variable (μ : Fin n → Measure ℝ) (C γ : ℝ)

lemma bgChoice_risk_le (x : Fin n → ℝ) (p : List (Fin n)) (hp : p.length < n) (i : Fin n)
    (hLi : (μ i).real (Set.Ioi 1) ≤ γ / C) :
    prefixRisk μ x p (bgChoice μ C γ x p i) +
      overflowProb (μ i) (prefixUsage x p (bgChoice μ C γ x p i)) ≤ γ / C := by
  classical
  unfold bgChoice
  simp only
  split_ifs with he hu
  · have := Finset.min'_mem _ he
    simp only [Finset.mem_filter] at this
    convert this.2.2
  · have hm := (Finset.mem_filter.mp (Finset.min'_mem _ hu)).2
    rw [prefixUsage_unused x p _ hm, prefixRisk_not_opened μ x p _ hm, zero_add]
    unfold overflowProb; simpa using hLi
  · exfalso; apply hu
    have hcard : p.toFinset.card < (Finset.univ : Finset (Fin n)).card := by
      calc p.toFinset.card ≤ p.length := List.toFinset_card_le p
        _ < n := hp
        _ = _ := by simp
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩

lemma bgPrefix_risk_le (hb : 0 ≤ γ / C) (hLight : ∀ i, (μ i).real (Set.Ioi 1) ≤ γ / C)
    (x : Fin n → ℝ) (t : ℕ) (ht : t ≤ n) (j : Fin n) :
    prefixRisk μ x (bgPrefix μ C γ x t) j ≤ γ / C := by
  induction t with
  | zero => simp [bgPrefix, prefixRisk, hb]
  | succ t ih =>
    have htn : t < n := by omega
    rw [bgPrefix_succ_lt μ C γ x t htn,
      prefixRisk_append μ x _ ⟨t, htn⟩ (by rw [bgPrefix_length]; simp; omega)]
    split_ifs with hc
    · subst hc
      exact bgChoice_risk_le μ C γ x _ (by rw [bgPrefix_length]; omega) _ (hLight _)
    · rw [add_zero]; exact ih (by omega)

lemma bg_risk_le (hb : 0 ≤ γ / C) (hLight : ∀ i, (μ i).real (Set.Ioi 1) ≤ γ / C)
    (x : Fin n → ℝ) (j : Fin n) :
    risk μ (bgRule μ C γ) x j ≤
      (Set.indicator {x | ∃ i : Fin n, bgRule μ C γ i x = j} (fun _ => γ / C)) x := by
  by_cases hj : ∃ i : Fin n, bgRule μ C γ i x = j
  · rw [Set.indicator_of_mem (show x ∈ {x | ∃ i : Fin n, bgRule μ C γ i x = j} from hj)]
    unfold risk
    rw [riskUpTo_bg μ C γ x j n le_rfl]
    exact bgPrefix_risk_le μ C γ hb hLight x n le_rfl j
  · rw [Set.indicator_of_notMem (show x ∉ {x | ∃ i : Fin n, bgRule μ C γ i x = j} from hj)]
    rw [risk_eq_sum]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro k _
    rw [if_neg (fun h => hj ⟨k, h⟩)]

end OBPX

namespace OBPX

variable {n : ℕ}

lemma integrable_risk (μ : Fin n → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (a : Rule n) (ha : MeasurableRule a) (j : Fin n) :
    Integrable (fun x => risk μ a x j) (Measure.pi μ) := by
  refine Integrable.of_bound (measurable_risk μ hμ a ha j).aestronglyMeasurable (n : ℝ)
    (Filter.Eventually.of_forall (fun x => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (risk_nonneg μ a x j), risk_eq_sum]
  calc _ ≤ ∑ k : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun k _ => by
          split_ifs
          · exact overflowProb_le_one _ _
          · norm_num)
    _ = n := by simp

lemma measurableSet_opened (a : Rule n) (ha : MeasurableRule a) (j : Fin n) :
    MeasurableSet {x | ∃ i : Fin n, a i x = j} := by
  have : {x | ∃ i : Fin n, a i x = j} = ⋃ i : Fin n, {x | a i x = j} := by
    ext x; simp
  rw [this]; exact MeasurableSet.iUnion (fun i => ha i j)

lemma numOpened_eq_sum (a : Rule n) (x : Fin n → ℝ) :
    (numOpened a x : ℝ) = ∑ j : Fin n, Set.indicator {x | ∃ i : Fin n, a i x = j} 1 x := by
  classical
  have : Finset.univ.image (fun i : Fin n => a i x) =
      Finset.univ.filter (fun j => ∃ i : Fin n, a i x = j) := by
    ext j; simp
  rw [numOpened, this, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [Set.indicator]

lemma integral_numOpened (μ : Fin n → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (a : Rule n) (ha : MeasurableRule a) :
    ∫ x, (numOpened a x : ℝ) ∂(Measure.pi μ) =
      ∑ j : Fin n, (Measure.pi μ).real {x | ∃ i : Fin n, a i x = j} := by
  simp_rw [numOpened_eq_sum]
  rw [integral_finsetSum _ (fun j _ => ?_)]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    exact integral_indicator_one (measurableSet_opened a ha j)
  · exact (integrable_const (1 : ℝ)).indicator (measurableSet_opened a ha j)

lemma measurable_numOpened (a : Rule n) (ha : MeasurableRule a) :
    Measurable (fun x => (numOpened a x : ℝ)) := by
  simp_rw [numOpened_eq_sum]
  exact Finset.measurable_sum _ (fun j _ =>
    measurable_const.indicator (measurableSet_opened a ha j))

lemma measurable_numBroken (a : Rule n) (ha : MeasurableRule a) :
    Measurable (fun x => (numBroken a x : ℝ)) := by
  classical
  have : (fun x => (numBroken a x : ℝ)) =
      fun x => ∑ j : Fin n, (if 1 < usage a x j n then (1 : ℝ) else 0) := by
    funext x
    rw [numBroken, Finset.card_filter]
    push_cast
    rfl
  rw [this]
  refine Finset.measurable_sum _ (fun j _ => ?_)
  exact Measurable.ite (measurableSet_lt measurable_const
    (measurable_usage a ha j n)) measurable_const measurable_const

lemma integrable_numOpened (μ : Fin n → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (a : Rule n) (ha : MeasurableRule a) :
    Integrable (fun x => (numOpened a x : ℝ)) (Measure.pi μ) := by
  refine Integrable.of_bound (measurable_numOpened a ha).aestronglyMeasurable (n : ℝ)
    (Filter.Eventually.of_forall (fun x => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have : numOpened a x ≤ n := by
    unfold numOpened
    calc _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
      _ = n := by simp
  exact_mod_cast this

lemma integrable_numBroken (μ : Fin n → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (a : Rule n) (ha : MeasurableRule a) :
    Integrable (fun x => (numBroken a x : ℝ)) (Measure.pi μ) := by
  refine Integrable.of_bound (measurable_numBroken a ha).aestronglyMeasurable (n : ℝ)
    (Filter.Eventually.of_forall (fun x => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have : numBroken a x ≤ n := by
    unfold numBroken
    calc _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
      _ = n := by simp
  exact_mod_cast this

lemma cost_eq (μ : Fin n → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i)) (C : ℝ)
    (a : Rule n) (ha : MeasurableRule a) :
    cost μ C a = ∫ x, (numOpened a x : ℝ) ∂(Measure.pi μ) +
      C * ∫ x, (numBroken a x : ℝ) ∂(Measure.pi μ) := by
  unfold cost
  rw [integral_add (integrable_numOpened μ hμ a ha)
    ((integrable_numBroken μ hμ a ha).const_mul C), integral_const_mul]

theorem lemma34 (μ : Fin n → Measure ℝ)
    (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hμ0 : ∀ i, μ i (Set.Iio 0) = 0)
    (C γ : ℝ) (hC : 1 ≤ C) (hγ : 1 ≤ γ)
    (hLight : ∀ i, (μ i).real (Set.Ioi 1) ≤ γ / C) :
    ∀ j : Fin n,
      (Measure.pi μ).real {x | 1 < usage (bgRule μ C γ) x j n} ≤
        γ / C * (Measure.pi μ).real {x | ∃ i : Fin n, bgRule μ C γ i x = j} := by
  intro j
  have hb : 0 ≤ γ / C := div_nonneg (by linarith) (by linarith)
  have hpol := bg_isPolicy μ C γ hμ
  rw [(prop31 μ hμ hμ0 _ hpol).1 j]
  calc ∫ x, risk μ (bgRule μ C γ) x j ∂(Measure.pi μ)
      ≤ ∫ x, (Set.indicator {x | ∃ i : Fin n, bgRule μ C γ i x = j} (fun _ => γ / C)) x
          ∂(Measure.pi μ) :=
        integral_mono (integrable_risk μ hμ _ hpol.2.1 j)
          ((integrable_const _).indicator (measurableSet_opened _ hpol.2.1 j))
          (fun x => bg_risk_le μ C γ hb hLight x j)
    _ = _ := by
        rw [integral_indicator_const _ (measurableSet_opened _ hpol.2.1 j), smul_eq_mul, mul_comm]

theorem cor35 (μ : Fin n → Measure ℝ)
    (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hμ0 : ∀ i, μ i (Set.Iio 0) = 0)
    (C γ : ℝ) (hC : 1 ≤ C) (hγ : 1 ≤ γ)
    (hLight : ∀ i, (μ i).real (Set.Ioi 1) ≤ γ / C) :
    cost μ C (bgRule μ C γ) ≤
      (1 + γ) * ∫ x, (numOpened (bgRule μ C γ) x : ℝ) ∂(Measure.pi μ) := by
  have hpol := bg_isPolicy μ C γ hμ
  have hO : ∫ x, (numBroken (bgRule μ C γ) x : ℝ) ∂(Measure.pi μ) ≤
      γ / C * ∫ x, (numOpened (bgRule μ C γ) x : ℝ) ∂(Measure.pi μ) := by
    rw [(prop31 μ hμ hμ0 _ hpol).2, integral_finsetSum _
      (fun j _ => integrable_risk μ hμ _ hpol.2.1 j), integral_numOpened μ hμ _ hpol.2.1,
      Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [← (prop31 μ hμ hμ0 _ hpol).1 j]
    exact lemma34 μ hμ hμ0 C γ hC hγ hLight j
  rw [cost_eq μ hμ C _ hpol.2.1]
  have hCpos : 0 < C := by linarith
  have := mul_le_mul_of_nonneg_left hO hCpos.le
  rw [← mul_assoc, mul_div_cancel₀ _ hCpos.ne'] at this
  linarith

end OBPX


open MeasureTheory OverflowBinPacking.IID

namespace OBPX

variable {n : ℕ}

lemma overflowProb_mono (ν : Measure ℝ) [IsFiniteMeasure ν] {S S' : ℝ} (h : S ≤ S') :
    overflowProb ν S ≤ overflowProb ν S' := by
  unfold overflowProb
  apply measureReal_mono
  · intro z hz; simp only [Set.mem_Ioi] at hz ⊢; linarith
  · exact measure_ne_top _ _

lemma overflowProb_zero (ν : Measure ℝ) : overflowProb ν 0 = ν.real (Set.Ioi 1) := by
  simp [overflowProb]

lemma sum_risk (μ : Fin n → Measure ℝ) (a : Rule n) (x : Fin n → ℝ) :
    ∑ j : Fin n, risk μ a x j = ∑ k : Fin n, overflowProb (μ k) (usage a x (a k x) k) := by
  classical
  simp_rw [risk_eq_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_ite_eq]
  simp

lemma prefixRisk_nonneg (μ : Fin n → Measure ℝ) (x : Fin n → ℝ) (p : List (Fin n)) (j : Fin n) :
    0 ≤ prefixRisk μ x p j := by
  unfold prefixRisk
  exact Finset.sum_nonneg (fun k _ => overflowProb_nonneg _ _)

lemma prefixUsage_nonneg (x : Fin n → ℝ) (hx : ∀ k, 0 ≤ x k) (p : List (Fin n)) (j : Fin n) :
    0 ≤ prefixUsage x p j := by
  unfold prefixUsage
  exact Finset.sum_nonneg (fun k _ => hx k)

/-- In the heavy case, Budgeted Greedy puts item `i` in bin `i`. -/
lemma bg_heavy_diag (ν : Measure ℝ) [IsProbabilityMeasure ν] (C γ : ℝ)
    (hH : γ / C < ν.real (Set.Ioi 1)) (x : Fin n → ℝ) (hx : ∀ k, 0 ≤ x k) :
    ∀ i : Fin n, bgRule (fun _ : Fin n => ν) C γ i x = i := by
  classical
  suffices H : ∀ m : ℕ, ∀ i : Fin n, i.val = m → bgRule (fun _ : Fin n => ν) C γ i x = i by
    intro i; exact H i.val i rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro i hi
  subst hi
  have ih' : ∀ k : Fin n, k.val < i.val → bgRule (fun _ : Fin n => ν) C γ k x = k :=
    fun k hk => ih k.val hk k rfl
  set p := bgPrefix (fun _ : Fin n => ν) C γ x i.val with hpdef
  have hp : ∀ k : Fin n, p[k.val]? = if k.val < i.val then some k else none := by
    intro k
    rw [hpdef, bgPrefix_getElem? _ C γ x i.val i.isLt.le k]
    split_ifs with h
    · rw [ih' k h]
    · rfl
  have hlen : p.length = i.val := by rw [hpdef, bgPrefix_length]; omega
  have hmem : ∀ j : Fin n, j ∈ prefixOpened p ↔ j.val < i.val := by
    intro j
    simp only [prefixOpened, List.mem_toFinset, List.mem_iff_getElem?]
    constructor
    · rintro ⟨m, hm⟩
      have hml : m < p.length := by
        by_contra h; rw [List.getElem?_eq_none (by omega)] at hm; simp at hm
      have := hp ⟨m, by omega⟩
      simp only at this
      rw [hm, if_pos (by omega)] at this
      have e := Option.some.inj this
      rw [e]; simp only; omega
    · intro h; exact ⟨j.val, by rw [hp j, if_pos h]⟩
  rw [bgRule_eq_choice, ← hpdef]
  unfold bgChoice
  simp only
  split_ifs with he hu
  · exfalso
    obtain ⟨j, hj⟩ := he
    simp only [Finset.mem_filter] at hj
    have h1 := prefixRisk_nonneg (fun _ : Fin n => ν) x p j
    have h2 := overflowProb_mono ν (prefixUsage_nonneg x hx p j)
    rw [overflowProb_zero] at h2
    linarith [hj.2.2]
  · apply le_antisymm
    · apply Finset.min'_le
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmem]
      omega
    · apply Finset.le_min'
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmem] at hy
      exact Fin.le_def.mpr (by omega)
  · exfalso; apply hu
    exact ⟨i, by simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmem]; omega⟩

lemma integral_sum_risk_ge (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν0 : ν (Set.Iio 0) = 0)
    (a : Rule n) (ha : IsPolicy a) :
    (n : ℝ) * ν.real (Set.Ioi 1) ≤
      ∫ x, (numBroken a x : ℝ) ∂(Measure.pi (fun _ : Fin n => ν)) := by
  have hμ : ∀ _ : Fin n, IsProbabilityMeasure ν := fun _ => inferInstance
  rw [(prop31 (fun _ : Fin n => ν) hμ (fun _ => hν0) a ha).2]
  have hint : Integrable (fun x => ∑ j : Fin n, risk (fun _ : Fin n => ν) a x j)
      (Measure.pi (fun _ : Fin n => ν)) :=
    integrable_finsetSum _ (fun j _ => integrable_risk _ hμ a ha.2.1 j)
  calc (n : ℝ) * ν.real (Set.Ioi 1)
      = ∫ _x, (n : ℝ) * ν.real (Set.Ioi 1) ∂(Measure.pi (fun _ : Fin n => ν)) := by
        simp
    _ ≤ _ := by
        refine integral_mono_ae (integrable_const _) hint ?_
        filter_upwards [ae_nonneg (fun _ : Fin n => ν) hμ (fun _ => hν0)] with x hx
        rw [sum_risk]
        calc (n : ℝ) * ν.real (Set.Ioi 1) = ∑ _k : Fin n, ν.real (Set.Ioi 1) := by simp
          _ ≤ _ := Finset.sum_le_sum (fun k _ => by
              rw [← overflowProb_zero]
              exact overflowProb_mono ν (usage_nonneg a x hx _ _))

theorem heavy (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν0 : ν (Set.Iio 0) = 0) (C : ℝ) (hC : 1 ≤ C)
    (hHeavy : Real.sqrt 2 / C < ν.real (Set.Ioi 1)) :
    cost (fun _ : Fin n => ν) C
      (bgRule (fun _ : Fin n => ν) C (Real.sqrt 2)) =
      (n : ℝ) * (1 + C * ν.real (Set.Ioi 1)) ∧
    ∀ a : Rule n, IsPolicy a →
      (n : ℝ) * C * ν.real (Set.Ioi 1) ≤
        cost (fun _ : Fin n => ν) C a := by
  classical
  have hμ : ∀ _ : Fin n, IsProbabilityMeasure ν := fun _ => inferInstance
  have hCpos : 0 < C := by linarith
  refine ⟨?_, ?_⟩
  · have hpol := bg_isPolicy (fun _ : Fin n => ν) C (Real.sqrt 2) hμ
    have hdiag := bg_heavy_diag (n := n) ν C (Real.sqrt 2) hHeavy
    rw [cost_eq _ hμ C _ hpol.2.1, (prop31 (fun _ : Fin n => ν) hμ (fun _ => hν0) _ hpol).2]
    have hN : ∫ x, (numOpened (bgRule (fun _ : Fin n => ν) C (Real.sqrt 2)) x : ℝ)
        ∂(Measure.pi (fun _ : Fin n => ν)) = n := by
      rw [integral_congr_ae (g := fun _ => (n : ℝ))]
      · simp
      · filter_upwards [ae_nonneg (fun _ : Fin n => ν) hμ (fun _ => hν0)] with x hx
        have : Finset.univ.image (fun i : Fin n => bgRule (fun _ : Fin n => ν) C (Real.sqrt 2) i x)
            = Finset.univ := by
          ext j; simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
          exact ⟨j, hdiag x hx j⟩
        simp [numOpened, this]
    have hO : ∫ x, (∑ j : Fin n, risk (fun _ : Fin n => ν)
        (bgRule (fun _ : Fin n => ν) C (Real.sqrt 2)) x j) ∂(Measure.pi (fun _ : Fin n => ν)) =
        n * ν.real (Set.Ioi 1) := by
      rw [integral_congr_ae (g := fun _ => (n : ℝ) * ν.real (Set.Ioi 1))]
      · simp
      · filter_upwards [ae_nonneg (fun _ : Fin n => ν) hμ (fun _ => hν0)] with x hx
        rw [sum_risk]
        have : ∀ k : Fin n, usage (bgRule (fun _ : Fin n => ν) C (Real.sqrt 2)) x
            (bgRule (fun _ : Fin n => ν) C (Real.sqrt 2) k x) k = 0 := by
          intro k
          rw [hdiag x hx k]
          unfold usage
          apply Finset.sum_eq_zero
          intro k' hk'
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hdiag x hx k'] at hk'
          exfalso; rw [hk'.2] at hk'; exact lt_irrefl _ hk'.1
        simp only [this, overflowProb_zero]
        simp
    rw [hN, hO]; ring
  · intro a ha
    rw [cost_eq _ hμ C _ ha.2.1]
    have h1 : 0 ≤ ∫ x, (numOpened a x : ℝ) ∂(Measure.pi (fun _ : Fin n => ν)) :=
      integral_nonneg (fun x => by positivity)
    have h2 := mul_le_mul_of_nonneg_left (integral_sum_risk_ge ν hν0 a ha) hCpos.le
    nlinarith

end OBPX


open MeasureTheory OverflowBinPacking.IID

namespace OBPX

/-! Generic online rules built from a choice function on prefixes. -/

variable {n : ℕ} (ch : (Fin n → ℝ) → List (Fin n) → Fin n → Fin n) (x : Fin n → ℝ)

noncomputable def gPrefix (x : Fin n → ℝ) : ℕ → List (Fin n)
  | 0 => []
  | t + 1 => if h : t < n then gPrefix x t ++ [ch x (gPrefix x t) ⟨t, h⟩] else gPrefix x t

noncomputable def gRule : Rule n := fun i x => ((gPrefix ch x (i.val + 1))[i.val]?).getD i

lemma gPrefix_succ_lt (t : ℕ) (h : t < n) :
    gPrefix ch x (t + 1) = gPrefix ch x t ++ [ch x (gPrefix ch x t) ⟨t, h⟩] := by
  rw [gPrefix]; simp [h]

lemma gPrefix_succ_ge (t : ℕ) (h : n ≤ t) : gPrefix ch x (t + 1) = gPrefix ch x t := by
  rw [gPrefix]; simp [Nat.not_lt.mpr h]

lemma gPrefix_length (t : ℕ) : (gPrefix ch x t).length = min t n := by
  induction t with
  | zero => simp [gPrefix]
  | succ t ih =>
    by_cases h : t < n
    · rw [gPrefix_succ_lt ch x t h]; simp [ih]; omega
    · rw [gPrefix_succ_ge ch x t (by omega), ih]; omega

lemma gPrefix_prefix (t s : ℕ) (h : t ≤ s) : gPrefix ch x t <+: gPrefix ch x s := by
  induction s, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ s hs ih =>
    by_cases h : s < n
    · rw [gPrefix_succ_lt ch x s h]; exact ih.trans (List.prefix_append _ _)
    · rw [gPrefix_succ_ge ch x s (by omega)]; exact ih

lemma gRule_eq_choice (i : Fin n) : gRule ch i x = ch x (gPrefix ch x i.val) i := by
  unfold gRule
  rw [gPrefix_succ_lt ch x i.val i.isLt]
  have hl : (gPrefix ch x i.val).length = i.val := by rw [gPrefix_length]; omega
  simp [hl]

lemma gPrefix_getElem? (t : ℕ) (ht : t ≤ n) (k : Fin n) :
    (gPrefix ch x t)[k.val]? = if k.val < t then some (gRule ch k x) else none := by
  split_ifs with hk
  · have hpre := gPrefix_prefix ch x (k.val + 1) t (by omega)
    have hl : (gPrefix ch x (k.val + 1)).length = k.val + 1 := by
      rw [gPrefix_length]; omega
    obtain ⟨l, hl2⟩ := hpre
    rw [← hl2, List.getElem?_append_left (by omega)]
    rw [gRule_eq_choice, gPrefix_succ_lt ch x k.val k.isLt]
    have hl' : (gPrefix ch x k.val).length = k.val := by rw [gPrefix_length]; omega
    simp [hl']
  · rw [List.getElem?_eq_none]; rw [gPrefix_length]; omega

lemma usage_g (j : Fin n) (t : ℕ) (ht : t ≤ n) :
    usage (gRule ch) x j t = prefixUsage x (gPrefix ch x t) j := by
  unfold usage prefixUsage
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, gPrefix_getElem? ch x t ht k]
  split_ifs with hk <;> simp [hk]

lemma take_gPrefix (t k : ℕ) (hk : k ≤ t) :
    (gPrefix ch x t).take k = gPrefix ch x k := by
  have hpre := gPrefix_prefix ch x k t hk
  have hl : (gPrefix ch x k).length = min k n := gPrefix_length ch x k
  obtain ⟨l, hl'⟩ := hpre
  by_cases hkn : k ≤ n
  · rw [← hl', List.take_left' (by rw [hl]; omega)]
  · have h1 : gPrefix ch x t = gPrefix ch x k := by
      have := gPrefix_length ch x t
      have hlen : (gPrefix ch x t).length = (gPrefix ch x k).length := by
        rw [this, hl]; omega
      rw [← hl'] at hlen ⊢
      simp at hlen
      rw [hlen]; simp
    rw [h1]; apply List.take_of_length_le; rw [hl]; omega

lemma riskUpTo_g (μ : Fin n → Measure ℝ) (j : Fin n) (t : ℕ) (ht : t ≤ n) :
    riskUpTo μ (gRule ch) x j t = prefixRisk μ x (gPrefix ch x t) j := by
  unfold riskUpTo prefixRisk
  have hset : (Finset.univ.filter (fun k : Fin n => (k : ℕ) < t ∧ gRule ch k x = j)) =
      Finset.univ.filter (fun k : Fin n => (gPrefix ch x t)[k.val]? = some j) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, gPrefix_getElem? ch x t ht k]
    split_ifs with hk <;> simp [hk]
  rw [hset]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, gPrefix_getElem? ch x t ht k] at hk
  have hkt : k.val < t := by split_ifs at hk with h; exact h
  rw [usage_g ch x j k.val (by omega), take_gPrefix ch x t k.val hkt.le]

lemma prefixOpened_gPrefix (t : ℕ) (ht : t ≤ n) (c : Fin n) :
    c ∈ prefixOpened (gPrefix ch x t) ↔ ∃ k : Fin n, k.val < t ∧ gRule ch k x = c := by
  simp only [prefixOpened, List.mem_toFinset, List.mem_iff_getElem?]
  constructor
  · rintro ⟨m, hm⟩
    have hml : m < (gPrefix ch x t).length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hm; simp at hm
    rw [gPrefix_length] at hml
    have := gPrefix_getElem? ch x t ht ⟨m, by omega⟩
    simp only at this
    rw [hm, if_pos (lt_of_lt_of_le hml (min_le_left _ _))] at this
    exact ⟨⟨m, by omega⟩, lt_of_lt_of_le hml (min_le_left _ _), (Option.some.inj this).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.val, by rw [gPrefix_getElem? ch x t ht k, if_pos hk]⟩

lemma gPrefix_congr (hch : ∀ (x y : Fin n → ℝ) (p : List (Fin n)) (i : Fin n),
      p.length = i.val → (∀ k : Fin n, k.val < i.val → x k = y k) → ch x p i = ch y p i)
    (x y : Fin n → ℝ) (t : ℕ) (hxy : ∀ k : Fin n, k.val < t → x k = y k) :
    gPrefix ch x (t + 1) = gPrefix ch y (t + 1) := by
  induction t with
  | zero =>
    by_cases h : 0 < n
    · rw [gPrefix_succ_lt ch x 0 h, gPrefix_succ_lt ch y 0 h]
      simp only [gPrefix, List.nil_append]
      rw [hch x y [] ⟨0, h⟩ rfl (fun k hk => by simp at hk)]
    · rw [gPrefix_succ_ge ch x 0 (by omega), gPrefix_succ_ge ch y 0 (by omega)]
      rfl
  | succ t ih =>
    have ih' := ih (fun k hk => hxy k (by omega))
    by_cases h : t + 1 < n
    · rw [gPrefix_succ_lt ch x (t+1) h, gPrefix_succ_lt ch y (t+1) h, ih']
      rw [hch x y _ ⟨t + 1, h⟩ (by rw [gPrefix_length]; simp; omega) (fun k hk => hxy k hk)]
    · rw [gPrefix_succ_ge ch x (t+1) (by omega), gPrefix_succ_ge ch y (t+1) (by omega), ih']

lemma g_nonanticipative (hch : ∀ (x y : Fin n → ℝ) (p : List (Fin n)) (i : Fin n),
      p.length = i.val → (∀ k : Fin n, k.val < i.val → x k = y k) → ch x p i = ch y p i) :
    Nonanticipative (gRule ch) := by
  intro i x y hxy
  unfold gRule
  rw [gPrefix_congr ch hch x y i.val (fun k hk => hxy k hk)]

lemma measurableSet_gPrefix_eq (hm : ∀ p i, Measurable (fun x => ch x p i)) (t : ℕ)
    (q : List (Fin n)) : MeasurableSet {x | gPrefix ch x t = q} := by
  induction t generalizing q with
  | zero =>
    by_cases h : ([] : List (Fin n)) = q
    · simp [gPrefix, h]
    · simp [gPrefix, h]
  | succ t ih =>
    by_cases h : t < n
    · have : {x | gPrefix ch x (t+1) = q} = ⋃ p : List (Fin n),
          ({x | gPrefix ch x t = p} ∩ (fun x => ch x p ⟨t, h⟩) ⁻¹' {j | p ++ [j] = q}) := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
          gPrefix_succ_lt ch x t h]
        constructor
        · intro hx; exact ⟨_, rfl, hx⟩
        · rintro ⟨p, hp, hq⟩; rw [hp]; exact hq
      rw [this]
      exact MeasurableSet.iUnion (fun p => (ih p).inter (hm p _ (MeasurableSet.of_discrete)))
    · have : {x | gPrefix ch x (t+1) = q} = {x | gPrefix ch x t = q} := by
        ext x; simp [gPrefix_succ_ge ch x t (by omega)]
      rw [this]; exact ih q

lemma g_measurable (hm : ∀ p i, Measurable (fun x => ch x p i)) : MeasurableRule (gRule ch) := by
  intro i j
  have : {x | gRule ch i x = j} = ⋃ p : List (Fin n),
      ({x | gPrefix ch x i.val = p} ∩ (fun x => ch x p i) ⁻¹' {j}) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, gRule_eq_choice]
    constructor
    · intro hx; exact ⟨_, rfl, hx⟩
    · rintro ⟨p, hp, hq⟩; rw [hp]; exact hq
  rw [this]
  exact MeasurableSet.iUnion (fun p => (measurableSet_gPrefix_eq ch hm _ p).inter
    (hm p i (MeasurableSet.of_discrete)))

lemma g_feasible (hf : ∀ (x : Fin n → ℝ) (p : List (Fin n)) (i : Fin n), p.length = i.val →
      prefixUsage x p (ch x p i) ≤ 1) : Feasible (gRule ch) := by
  intro x i
  rw [usage_g ch x _ i.val i.isLt.le, gRule_eq_choice]
  apply hf
  rw [gPrefix_length]; omega

end OBPX


open MeasureTheory OverflowBinPacking.IID

namespace OBPX

variable {n : ℕ} (μ : Fin n → Measure ℝ) (C γ : ℝ)

/-- heavy items: overflow probability on an empty bin exceeds the budget -/
def IsHeavy (i : Fin n) : Prop := γ / C < (μ i).real (Set.Ioi 1)

noncomputable def freshLabel (p : List (Fin n)) (i : Fin n) : Fin n := by
  classical
  exact if hu : (Finset.univ.filter fun j => j ∉ prefixOpened p).Nonempty then
    (Finset.univ.filter fun j => j ∉ prefixOpened p).min' hu else i

/-- The last light item before round `t` that the original assignment `A` put in bin `j`. -/
noncomputable def lastLightAux (A : Fin n → Fin n) (t : ℕ) (j : Fin n) : Option (Fin n) := by
  classical
  exact if h : (Finset.univ.filter fun k : Fin n => k.val < t ∧ A k = j ∧ ¬ IsHeavy μ C γ k).Nonempty
    then some ((Finset.univ.filter fun k : Fin n => k.val < t ∧ A k = j ∧ ¬ IsHeavy μ C γ k).max' h)
    else none

noncomputable def cvAux (p : List (Fin n)) (i : Fin n) (A : Fin n → Fin n) (B : Fin n → Bool) :
    Fin n := by
  classical
  exact if IsHeavy μ C γ i then freshLabel p i else
    (lastLightAux μ C γ A i.val (A i)).elim (freshLabel p i)
      (fun k => if B ((p[k.val]?).getD i) = true then (p[k.val]?).getD i else freshLabel p i)

def Fits (x : Fin n → ℝ) (p : List (Fin n)) (i c : Fin n) : Prop :=
  prefixUsage x p c ≤ 1 ∧ prefixRisk μ x p c + overflowProb (μ i) (prefixUsage x p c) ≤ γ / C

noncomputable def cvChoice (a : Rule n) : (Fin n → ℝ) → List (Fin n) → Fin n → Fin n := by
  classical
  exact fun x p i => cvAux μ C γ p i (fun k => a k x) (fun c => decide (Fits μ C γ x p i c))

/-- The converted (risk-budgeted, heavy-isolating) rule. -/
noncomputable def cvRule (a : Rule n) : Rule n := gRule (cvChoice μ C γ a)

/-! ### basic facts -/

lemma freshLabel_notMem (p : List (Fin n)) (i : Fin n) (hp : p.length < n) :
    freshLabel p i ∉ prefixOpened p := by
  classical
  unfold freshLabel
  split_ifs with hu
  · exact (Finset.mem_filter.mp (Finset.min'_mem _ hu)).2
  · exfalso; apply hu
    have hcard : p.toFinset.card < (Finset.univ : Finset (Fin n)).card := by
      calc p.toFinset.card ≤ p.length := List.toFinset_card_le p
        _ < n := hp
        _ = _ := by simp
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩

lemma lastLightAux_congr (A A' : Fin n → Fin n) (t : ℕ) (j : Fin n)
    (h : ∀ k : Fin n, k.val < t → A k = A' k) :
    lastLightAux μ C γ A t j = lastLightAux μ C γ A' t j := by
  classical
  unfold lastLightAux
  have : (Finset.univ.filter fun k : Fin n => k.val < t ∧ A k = j ∧ ¬ IsHeavy μ C γ k) =
      (Finset.univ.filter fun k : Fin n => k.val < t ∧ A' k = j ∧ ¬ IsHeavy μ C γ k) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, (h k h1) ▸ h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, (h k h1).symm ▸ h2, h3⟩
  simp only [this]

lemma lastLightAux_spec (A : Fin n → Fin n) (t : ℕ) (j k : Fin n) :
    lastLightAux μ C γ A t j = some k ↔
      (k.val < t ∧ A k = j ∧ ¬ IsHeavy μ C γ k) ∧
      ∀ k' : Fin n, k'.val < t → A k' = j → ¬ IsHeavy μ C γ k' → k' ≤ k := by
  classical
  unfold lastLightAux
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · rintro rfl
      have hm := Finset.max'_mem _ h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      refine ⟨hm, fun k' h1 h2 h3 => Finset.le_max' _ _ ?_⟩
      simp [h1, h2, h3]
    · rintro ⟨hk, hmax⟩
      apply le_antisymm
      · apply Finset.max'_le
        intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        exact hmax y hy.1 hy.2.1 hy.2.2
      · apply Finset.le_max'; simp [hk]
  · simp only [reduceCtorEq, false_iff]
    rintro ⟨hk, -⟩
    exact h ⟨k, by simp [hk]⟩

lemma lastLightAux_none (A : Fin n → Fin n) (t : ℕ) (j : Fin n) :
    lastLightAux μ C γ A t j = none ↔
      ∀ k : Fin n, k.val < t → A k = j → IsHeavy μ C γ k := by
  classical
  unfold lastLightAux
  split_ifs with h
  · simp only [reduceCtorEq, false_iff]
    intro hall
    obtain ⟨k, hk⟩ := h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact hk.2.2 (hall k hk.1 hk.2.1)
  · simp only [true_iff]
    intro k h1 h2
    by_contra h3
    exact h ⟨k, by simp [h1, h2, h3]⟩

open Classical in
lemma lastLightAux_succ (A : Fin n → Fin n) (i : Fin n) (j : Fin n) :
    lastLightAux μ C γ A (i.val + 1) j =
      if A i = j ∧ ¬ IsHeavy μ C γ i then some i else lastLightAux μ C γ A i.val j := by
  split_ifs with h
  · rw [lastLightAux_spec]
    refine ⟨⟨by omega, h.1, h.2⟩, fun k' hk' _ _ => Fin.le_def.mpr (by omega)⟩
  · cases hL : lastLightAux μ C γ A i.val j with
    | none =>
      rw [lastLightAux_none] at hL ⊢
      intro k hk hA
      by_cases hki : k.val < i.val
      · exact hL k hki hA
      · have : k = i := Fin.ext (by omega)
        subst this
        by_contra hh; exact h ⟨hA, hh⟩
    | some k =>
      rw [lastLightAux_spec] at hL ⊢
      refine ⟨⟨by omega, hL.1.2.1, hL.1.2.2⟩, fun k' hk' hA hH => ?_⟩
      by_cases hki : k'.val < i.val
      · exact hL.2 k' hki hA hH
      · have : k' = i := Fin.ext (by omega)
        subst this
        exact absurd ⟨hA, hH⟩ h

end OBPX

namespace OBPX

variable {n : ℕ} (μ : Fin n → Measure ℝ) (C γ : ℝ)

lemma cvAux_congr (p : List (Fin n)) (i : Fin n) (A A' : Fin n → Fin n) (B B' : Fin n → Bool)
    (hAi : A i = A' i) (hLL : ∀ k : Fin n, k.val < i.val → A k = A' k) (hB : B = B') :
    cvAux μ C γ p i A B = cvAux μ C γ p i A' B' := by
  unfold cvAux
  rw [hAi, lastLightAux_congr μ C γ A A' i.val (A' i) hLL, hB]

lemma cv_nonanticipative (a : Rule n) (ha : Nonanticipative a) :
    Nonanticipative (cvRule μ C γ a) := by
  classical
  apply g_nonanticipative
  intro x y p i hp hxy
  unfold cvChoice
  apply cvAux_congr
  · exact ha i x y (fun k hk => hxy k hk)
  · intro k hk
    exact ha k x y (fun k' hk' => hxy k' (lt_trans (Fin.lt_def.mp hk') hk))
  · funext c
    have hU := prefixUsage_congr x y p (fun k hk => hxy k (by omega)) c
    have hR := prefixRisk_congr μ x y p (fun k hk => hxy k (by omega)) c
    have hiff : Fits μ C γ x p i c ↔ Fits μ C γ y p i c := by simp only [Fits, hU, hR]
    exact decide_eq_decide.mpr hiff

lemma cv_measurable (hμ : ∀ i, IsProbabilityMeasure (μ i)) (a : Rule n) (ha : MeasurableRule a) :
    MeasurableRule (cvRule μ C γ a) := by
  classical
  apply g_measurable
  intro p i
  have hA : Measurable (fun x : Fin n → ℝ => (fun k => a k x)) := by
    refine measurable_pi_iff.mpr (fun k => ?_)
    exact measurable_to_countable' (fun j => ha k j)
  have hB : Measurable (fun x : Fin n → ℝ => (fun c => decide (Fits μ C γ x p i c))) := by
    refine measurable_pi_iff.mpr (fun c => ?_)
    refine measurable_to_countable' (fun b => ?_)
    have hs : MeasurableSet {x : Fin n → ℝ | Fits μ C γ x p i c} := by
      show MeasurableSet ({x : Fin n → ℝ | prefixUsage x p c ≤ 1} ∩
        {x | prefixRisk μ x p c + overflowProb (μ i) (prefixUsage x p c) ≤ γ / C})
      exact (measurableSet_le (measurable_prefixUsage p c) measurable_const).inter
        (measurableSet_le ((measurable_prefixRisk μ hμ p c).add
          ((measurable_overflowProb (μ i)).comp (measurable_prefixUsage p c))) measurable_const)
    cases b
    · have : (fun x : Fin n → ℝ => decide (Fits μ C γ x p i c)) ⁻¹' {false} =
          {x | Fits μ C γ x p i c}ᶜ := by ext x; simp
      rw [this]; exact hs.compl
    · have : (fun x : Fin n → ℝ => decide (Fits μ C γ x p i c)) ⁻¹' {true} =
          {x | Fits μ C γ x p i c} := by ext x; simp
      rw [this]; exact hs
  have hc : Measurable (fun z : (Fin n → Fin n) × (Fin n → Bool) => cvAux μ C γ p i z.1 z.2) :=
    measurable_of_countable _
  have := hc.comp (hA.prodMk hB)
  exact this

lemma cvChoice_cases (a : Rule n) (x : Fin n → ℝ) (p : List (Fin n)) (i : Fin n) :
    (cvChoice μ C γ a x p i = freshLabel p i) ∨
    (¬ IsHeavy μ C γ i ∧ ∃ k, lastLightAux μ C γ (fun k => a k x) i.val (a i x) = some k ∧
      Fits μ C γ x p i ((p[k.val]?).getD i) ∧
      cvChoice μ C γ a x p i = (p[k.val]?).getD i) := by
  classical
  unfold cvChoice cvAux
  split_ifs with hH
  · left; rfl
  · cases hL : lastLightAux μ C γ (fun k => a k x) i.val (a i x) with
    | none => left; rfl
    | some k =>
      simp only [Option.elim]
      split_ifs with hB
      · right
        refine ⟨hH, k, rfl, ?_, rfl⟩
        simpa using hB
      · left; rfl

lemma cvChoice_fresh_of (a : Rule n) (x : Fin n → ℝ) (p : List (Fin n)) (i : Fin n)
    (h : IsHeavy μ C γ i ∨ lastLightAux μ C γ (fun k => a k x) i.val (a i x) = none ∨
      ∃ k, lastLightAux μ C γ (fun k => a k x) i.val (a i x) = some k ∧
        ¬ Fits μ C γ x p i ((p[k.val]?).getD i)) :
    cvChoice μ C γ a x p i = freshLabel p i := by
  classical
  rcases cvChoice_cases μ C γ a x p i with h1 | ⟨hH, k, hk, hF, _⟩
  · exact h1
  · exfalso
    rcases h with h | h | ⟨k', hk', hF'⟩
    · exact hH h
    · rw [hk] at h; exact absurd h (by simp)
    · rw [hk] at hk'; cases hk'; exact hF' hF

lemma cv_feasible (a : Rule n) : Feasible (cvRule μ C γ a) := by
  apply g_feasible
  intro x p i hp
  rcases cvChoice_cases μ C γ a x p i with h1 | ⟨_, k, _, hF, h2⟩
  · rw [h1, prefixUsage_unused x p _ (freshLabel_notMem p i (by omega))]; norm_num
  · rw [h2]; exact hF.1

end OBPX

namespace OBPX

variable {n : ℕ} (μ : Fin n → Measure ℝ) (C γ : ℝ)

lemma cvChoice_of_fits (a : Rule n) (x : Fin n → ℝ) (p : List (Fin n)) (i k : Fin n)
    (hH : ¬ IsHeavy μ C γ i) (hL : lastLightAux μ C γ (fun k => a k x) i.val (a i x) = some k)
    (hF : Fits μ C γ x p i ((p[k.val]?).getD i)) :
    cvChoice μ C γ a x p i = (p[k.val]?).getD i := by
  classical
  unfold cvChoice cvAux
  simp only [hH, if_false]
  rw [hL]
  simp only [Option.elim]
  simp [hF]

end OBPX


open MeasureTheory OverflowBinPacking.IID

namespace OBPX

variable {n : ℕ}

lemma riskUpTo_succ (μ : Fin n → Measure ℝ) (a : Rule n) (x : Fin n → ℝ) (j : Fin n) (i : Fin n) :
    riskUpTo μ a x j (i.val + 1) = riskUpTo μ a x j i.val +
      (if a i x = j then overflowProb (μ i) (usage a x j i) else 0) := by
  classical
  unfold riskUpTo
  simp_rw [Finset.sum_filter]
  have : ∀ k : Fin n, (if (k : ℕ) < i.val + 1 ∧ a k x = j then
        overflowProb (μ k) (usage a x j k) else 0) =
      (if (k : ℕ) < i.val ∧ a k x = j then overflowProb (μ k) (usage a x j k) else 0) +
        (if i = k then (if a k x = j then overflowProb (μ k) (usage a x j k) else 0) else 0) := by
    intro k
    by_cases hik : i = k
    · subst hik; simp
    · have : (k : ℕ) ≠ i.val := fun h => hik (Fin.ext h.symm)
      by_cases hk : (k : ℕ) < i.val
      · simp [hk, hik, show (k : ℕ) < i.val + 1 by omega]
      · simp [hk, hik, show ¬ (k : ℕ) < i.val + 1 by omega]
  rw [Finset.sum_congr rfl (fun k _ => this k), Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp

lemma riskUpTo_zero (μ : Fin n → Measure ℝ) (a : Rule n) (x : Fin n → ℝ) (j : Fin n) :
    riskUpTo μ a x j 0 = 0 := by
  unfold riskUpTo; simp

/-- usage of a label not yet used is zero -/
lemma usage_of_fresh (a : Rule n) (x : Fin n → ℝ) (c : Fin n) (t : ℕ)
    (h : ∀ k : Fin n, k.val < t → a k x ≠ c) : usage a x c t = 0 := by
  unfold usage
  apply Finset.sum_eq_zero
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
  exact absurd hk.2 (h k hk.1)

lemma riskUpTo_of_fresh (μ : Fin n → Measure ℝ) (a : Rule n) (x : Fin n → ℝ) (c : Fin n) (t : ℕ)
    (h : ∀ k : Fin n, k.val < t → a k x ≠ c) : riskUpTo μ a x c t = 0 := by
  unfold riskUpTo
  apply Finset.sum_eq_zero
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
  exact absurd hk.2 (h k hk.1)

variable (μ : Fin n → Measure ℝ) (C γ : ℝ) (a : Rule n) (x : Fin n → ℝ)

/-- The fit test, in terms of the converted rule itself. -/
def FitsR (i c : Fin n) : Prop :=
  usage (cvRule μ C γ a) x c i ≤ 1 ∧
    riskUpTo μ (cvRule μ C γ a) x c i + overflowProb (μ i) (usage (cvRule μ C γ a) x c i) ≤ γ / C

/-- shorthand for the last light item of `a`'s bin of item `i` -/
noncomputable def LL (i : Fin n) : Option (Fin n) :=
  lastLightAux μ C γ (fun k => a k x) i.val (a i x)

lemma fits_iff (i c : Fin n) :
    Fits μ C γ x (gPrefix (cvChoice μ C γ a) x i.val) i c ↔ FitsR μ C γ a x i c := by
  unfold Fits FitsR cvRule
  rw [usage_g _ x c i.val i.isLt.le, riskUpTo_g _ x μ c i.val i.isLt.le]

lemma getD_gPrefix (i k : Fin n) (hk : k.val < i.val) :
    ((gPrefix (cvChoice μ C γ a) x i.val)[k.val]?).getD i = cvRule μ C γ a k x := by
  rw [gPrefix_getElem? _ x i.val i.isLt.le k, if_pos hk]
  rfl

lemma cv_eq_of_fits (i k : Fin n) (hH : ¬ IsHeavy μ C γ i) (hL : LL μ C γ a x i = some k)
    (hF : FitsR μ C γ a x i (cvRule μ C γ a k x)) :
    cvRule μ C γ a i x = cvRule μ C γ a k x := by
  classical
  have hk : k.val < i.val := ((lastLightAux_spec μ C γ _ _ _ _).mp hL).1.1
  have hF' : Fits μ C γ x (gPrefix (cvChoice μ C γ a) x i.val) i
      (((gPrefix (cvChoice μ C γ a) x i.val)[k.val]?).getD i) := by
    rw [getD_gPrefix μ C γ a x i k hk, fits_iff]; exact hF
  rw [show cvRule μ C γ a i x = cvChoice μ C γ a x (gPrefix (cvChoice μ C γ a) x i.val) i from
    gRule_eq_choice _ x i]
  rw [← getD_gPrefix μ C γ a x i k hk]
  exact cvChoice_of_fits μ C γ a x _ i k hH hL hF'

lemma cv_fresh (i : Fin n)
    (h : IsHeavy μ C γ i ∨ LL μ C γ a x i = none ∨
      ∃ k, LL μ C γ a x i = some k ∧ ¬ FitsR μ C γ a x i (cvRule μ C γ a k x)) :
    ∀ k' : Fin n, k'.val < i.val → cvRule μ C γ a k' x ≠ cvRule μ C γ a i x := by
  intro k' hk' heq
  have hfr : cvRule μ C γ a i x = freshLabel (gPrefix (cvChoice μ C γ a) x i.val) i := by
    rw [show cvRule μ C γ a i x = cvChoice μ C γ a x (gPrefix (cvChoice μ C γ a) x i.val) i from
      gRule_eq_choice _ x i]
    apply cvChoice_fresh_of
    rcases h with h | h | ⟨k, hk, hF⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr ⟨k, hk, ?_⟩)
      have hkl : k.val < i.val := ((lastLightAux_spec μ C γ _ _ _ _).mp hk).1.1
      rw [getD_gPrefix μ C γ a x i k hkl, fits_iff]; exact hF
  have hnot := freshLabel_notMem (gPrefix (cvChoice μ C γ a) x i.val) i
    (by rw [gPrefix_length]; omega)
  rw [← hfr, prefixOpened_gPrefix _ x i.val i.isLt.le] at hnot
  exact hnot ⟨k', hk', heq⟩

/-- dichotomy for the converted rule -/
lemma cv_dichotomy (i : Fin n) :
    (∃ k, ¬ IsHeavy μ C γ i ∧ LL μ C γ a x i = some k ∧
      FitsR μ C γ a x i (cvRule μ C γ a k x) ∧ cvRule μ C γ a i x = cvRule μ C γ a k x) ∨
    ((∀ k' : Fin n, k'.val < i.val → cvRule μ C γ a k' x ≠ cvRule μ C γ a i x) ∧
      (IsHeavy μ C γ i ∨ LL μ C γ a x i = none ∨
        ∃ k, LL μ C γ a x i = some k ∧ ¬ FitsR μ C γ a x i (cvRule μ C γ a k x))) := by
  by_cases hH : IsHeavy μ C γ i
  · exact Or.inr ⟨cv_fresh μ C γ a x i (Or.inl hH), Or.inl hH⟩
  · obtain hL | ⟨k, hL⟩ : LL μ C γ a x i = none ∨ ∃ k, LL μ C γ a x i = some k := by
      cases LL μ C γ a x i <;> simp
    · exact Or.inr ⟨cv_fresh μ C γ a x i (Or.inr (Or.inl hL)), Or.inr (Or.inl hL)⟩
    · by_cases hF : FitsR μ C γ a x i (cvRule μ C γ a k x)
      · exact Or.inl ⟨k, hH, hL, hF, cv_eq_of_fits μ C γ a x i k hH hL hF⟩
      · have h3 : IsHeavy μ C γ i ∨ LL μ C γ a x i = none ∨
            ∃ k', LL μ C γ a x i = some k' ∧ ¬ FitsR μ C γ a x i (cvRule μ C γ a k' x) :=
          Or.inr (Or.inr ⟨k, hL, hF⟩)
        exact Or.inr ⟨cv_fresh μ C γ a x i h3, h3⟩

lemma LL_spec_some (i k : Fin n) (h : LL μ C γ a x i = some k) :
    k.val < i.val ∧ a k x = a i x ∧ ¬ IsHeavy μ C γ k :=
  ((lastLightAux_spec μ C γ _ _ _ _).mp h).1

/-- The converted rule refines the original one. -/
lemma cv_refines : ∀ i k : Fin n, k.val < i.val →
    cvRule μ C γ a k x = cvRule μ C γ a i x → a k x = a i x := by
  suffices H : ∀ m : ℕ, ∀ i : Fin n, i.val = m → ∀ k : Fin n, k.val < i.val →
      cvRule μ C γ a k x = cvRule μ C γ a i x → a k x = a i x by
    intro i; exact H i.val i rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro i hi k hk heq
  subst hi
  rcases cv_dichotomy μ C γ a x i with ⟨ks, _, hL, _, heqs⟩ | ⟨hfr, _⟩
  · obtain ⟨hks, hAks, _⟩ := LL_spec_some μ C γ a x i ks hL
    rw [heqs] at heq
    rw [← hAks]
    rcases lt_trichotomy k.val ks.val with h | h | h
    · exact ih ks.val hks ks rfl k h heq
    · rw [Fin.ext h]
    · exact (ih k.val hk k rfl ks h heq.symm).symm
  · exact absurd heq (hfr k hk)

lemma cv_heavy_alone (i : Fin n) (hH : IsHeavy μ C γ i) :
    ∀ k : Fin n, k ≠ i → cvRule μ C γ a k x ≠ cvRule μ C γ a i x := by
  have hbefore := cv_fresh μ C γ a x i (Or.inl hH)
  suffices H : ∀ m : ℕ, ∀ k : Fin n, k.val = m → i.val < k.val →
      cvRule μ C γ a k x ≠ cvRule μ C γ a i x by
    intro k hki
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hki) with h | h
    · exact hbefore k h
    · exact H k.val k rfl h
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro k hk hik
  subst hk
  rcases cv_dichotomy μ C γ a x k with ⟨ks, _, hL, _, heqs⟩ | ⟨hfr, _⟩
  · obtain ⟨hks, _, hlight⟩ := LL_spec_some μ C γ a x k ks hL
    rw [heqs]
    rcases lt_trichotomy ks.val i.val with h | h | h
    · exact hbefore ks h
    · exact absurd (Fin.ext h ▸ hH) hlight
    · exact ih ks.val hks ks rfl h
  · exact fun heq => hfr i hik heq.symm

lemma cv_light_budget (hγC : 0 ≤ γ / C) (c : Fin n)
    (hlight : ∀ i : Fin n, cvRule μ C γ a i x = c → ¬ IsHeavy μ C γ i) :
    ∀ t : ℕ, t ≤ n → riskUpTo μ (cvRule μ C γ a) x c t ≤ γ / C := by
  intro t
  induction t with
  | zero => intro _; rw [riskUpTo_zero]; exact hγC
  | succ t ih =>
    intro ht
    have htn : t < n := by omega
    have := riskUpTo_succ μ (cvRule μ C γ a) x c ⟨t, htn⟩
    simp only at this
    rw [this]
    split_ifs with hc
    · have hl := hlight _ hc
      rcases cv_dichotomy μ C γ a x ⟨t, htn⟩ with ⟨ks, _, _, hF, heqs⟩ | ⟨hfr, _⟩
      · rw [heqs] at hc; rw [← hc]; exact hF.2
      · have h0 : ∀ k : Fin n, k.val < t → cvRule μ C γ a k x ≠ c := by
          intro k hk; rw [← hc]; exact hfr k hk
        rw [riskUpTo_of_fresh μ _ x c t h0, usage_of_fresh _ x c t h0, zero_add,
          overflowProb_zero]
        unfold IsHeavy at hl; push Not at hl; exact hl
    · rw [add_zero]; exact ih (by omega)

end OBPX


open MeasureTheory OverflowBinPacking.IID

namespace OBPX

variable {n : ℕ} (μ : Fin n → Measure ℝ) (C γ : ℝ) (a : Rule n) (x : Fin n → ℝ)

noncomputable def NPc (t : ℕ) : ℕ :=
  ((Finset.univ.filter (fun k : Fin n => k.val < t)).image (fun k => cvRule μ C γ a k x)).card

noncomputable def NPL (t : ℕ) : ℕ := by
  classical
  exact ((Finset.univ.filter (fun k : Fin n => k.val < t ∧ ¬ IsHeavy μ C γ k)).image
    (fun k => a k x)).card

noncomputable def Rho (t : ℕ) : ℝ := ∑ j : Fin n, riskUpTo μ a x j t

noncomputable def slj (t : ℕ) (j : Fin n) : ℝ :=
  (lastLightAux μ C γ (fun k => a k x) t j).elim 0
    (fun k => riskUpTo μ (cvRule μ C γ a) x (cvRule μ C γ a k x) t)

noncomputable def Sl (t : ℕ) : ℝ := ∑ j : Fin n, slj μ C γ a x t j

lemma filter_lt_succ (i : Fin n) :
    (Finset.univ.filter (fun k : Fin n => k.val < i.val + 1)) =
      insert i (Finset.univ.filter (fun k : Fin n => k.val < i.val)) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro h; by_cases hk : k = i
    · exact Or.inl hk
    · exact Or.inr (by have := Fin.val_ne_of_ne hk; omega)
  · rintro (rfl | h) <;> omega

lemma NPc_succ_le (i : Fin n) : NPc μ C γ a x (i.val + 1) ≤ NPc μ C γ a x i.val + 1 := by
  unfold NPc
  rw [filter_lt_succ, Finset.image_insert]
  exact Finset.card_insert_le _ _

lemma NPc_succ_eq (i : Fin n) (h : ∃ k : Fin n, k.val < i.val ∧ cvRule μ C γ a k x = cvRule μ C γ a i x) :
    NPc μ C γ a x (i.val + 1) = NPc μ C γ a x i.val := by
  unfold NPc
  rw [filter_lt_succ, Finset.image_insert, Finset.insert_eq_of_mem]
  obtain ⟨k, hk, he⟩ := h
  exact Finset.mem_image.mpr ⟨k, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hk, he⟩

lemma NPL_mono (i : Fin n) : NPL μ C γ a x i.val ≤ NPL μ C γ a x (i.val + 1) := by
  classical
  unfold NPL
  apply Finset.card_le_card
  apply Finset.image_subset_image
  intro k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

lemma NPL_succ_new (i : Fin n) (hH : ¬ IsHeavy μ C γ i)
    (hnone : ∀ k : Fin n, k.val < i.val → a k x = a i x → IsHeavy μ C γ k) :
    NPL μ C γ a x (i.val + 1) = NPL μ C γ a x i.val + 1 := by
  classical
  unfold NPL
  have : (Finset.univ.filter (fun k : Fin n => k.val < i.val + 1 ∧ ¬ IsHeavy μ C γ k)) =
      insert i (Finset.univ.filter (fun k : Fin n => k.val < i.val ∧ ¬ IsHeavy μ C γ k)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩; by_cases hk : k = i
      · exact Or.inl hk
      · exact Or.inr ⟨by have := Fin.val_ne_of_ne hk; omega, h2⟩
    · rintro (rfl | h)
      · exact ⟨by omega, hH⟩
      · exact ⟨by omega, h.2⟩
  rw [this, Finset.image_insert, Finset.card_insert_of_notMem]
  intro hmem
  obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hmem
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
  exact hk.2 (hnone k hk.1 he)

lemma Rho_succ (i : Fin n) : Rho μ a x (i.val + 1) =
    Rho μ a x i.val + overflowProb (μ i) (usage a x (a i x) i) := by
  classical
  unfold Rho
  simp_rw [riskUpTo_succ]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp

lemma cv_refines_sym (k k' : Fin n) (h : cvRule μ C γ a k x = cvRule μ C γ a k' x) :
    a k x = a k' x := by
  rcases lt_trichotomy k.val k'.val with hl | hl | hl
  · exact cv_refines μ C γ a x k' k hl h
  · rw [Fin.ext hl]
  · exact (cv_refines μ C γ a x k k' hl h.symm).symm

lemma usage_cv_le (hx : ∀ k, 0 ≤ x k) (k : Fin n) (t : ℕ) :
    usage (cvRule μ C γ a) x (cvRule μ C γ a k x) t ≤ usage a x (a k x) t := by
  unfold usage
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨h1, h2⟩
    exact ⟨h1, cv_refines_sym μ C γ a x k' k h2⟩
  · intro k' _ _; exact hx k'

lemma slj_other (i : Fin n) (j : Fin n) (hj : a i x ≠ j) :
    slj μ C γ a x (i.val + 1) j = slj μ C γ a x i.val j := by
  classical
  unfold slj
  rw [lastLightAux_succ]
  rw [if_neg (fun h => hj h.1)]
  obtain hL | ⟨k, hL⟩ : lastLightAux μ C γ (fun k => a k x) i.val j = none ∨
      ∃ k, lastLightAux μ C γ (fun k => a k x) i.val j = some k := by
    cases lastLightAux μ C γ (fun k => a k x) i.val j <;> simp
  · rw [hL]; rfl
  · rw [hL]
    simp only [Option.elim]
    rw [riskUpTo_succ, if_neg, add_zero]
    have hk := ((lastLightAux_spec μ C γ _ _ _ _).mp hL).1
    intro he
    have := cv_refines μ C γ a x i k hk.1 he.symm
    exact hj (this ▸ hk.2.1)

lemma Sl_succ (i : Fin n) :
    Sl μ C γ a x (i.val + 1) = Sl μ C γ a x i.val - slj μ C γ a x i.val (a i x) +
      slj μ C γ a x (i.val + 1) (a i x) := by
  unfold Sl
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (a i x)),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ (a i x))]
  have : ∑ j ∈ Finset.univ.erase (a i x), slj μ C γ a x (i.val + 1) j =
      ∑ j ∈ Finset.univ.erase (a i x), slj μ C γ a x i.val j := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    exact slj_other μ C γ a x i j (Finset.ne_of_mem_erase hj).symm
  rw [this]; ring

lemma slj_nonneg (t : ℕ) (j : Fin n) : 0 ≤ slj μ C γ a x t j := by
  unfold slj
  cases lastLightAux μ C γ (fun k => a k x) t j with
  | none => simp
  | some k =>
    simp only [Option.elim]
    rw [riskUpTo]
    exact Finset.sum_nonneg (fun _ _ => overflowProb_nonneg _ _)

lemma slj_same (i : Fin n) (j : Fin n) (h1 : ¬ (a i x = j ∧ ¬ IsHeavy μ C γ i))
    (h2 : ∀ k, lastLightAux μ C γ (fun k => a k x) i.val j = some k →
      cvRule μ C γ a i x ≠ cvRule μ C γ a k x) :
    slj μ C γ a x (i.val + 1) j = slj μ C γ a x i.val j := by
  classical
  unfold slj
  rw [lastLightAux_succ]
  rw [if_neg (by simpa using h1)]
  obtain hL | ⟨k, hL⟩ : lastLightAux μ C γ (fun k => a k x) i.val j = none ∨
      ∃ k, lastLightAux μ C γ (fun k => a k x) i.val j = some k := by
    cases lastLightAux μ C γ (fun k => a k x) i.val j <;> simp
  · rw [hL]; rfl
  · rw [hL]
    simp only [Option.elim]
    rw [riskUpTo_succ, if_neg (h2 k hL), add_zero]

lemma slj_light (i : Fin n) (hH : ¬ IsHeavy μ C γ i) :
    slj μ C γ a x (i.val + 1) (a i x) =
      riskUpTo μ (cvRule μ C γ a) x (cvRule μ C γ a i x) i.val +
        overflowProb (μ i) (usage (cvRule μ C γ a) x (cvRule μ C γ a i x) i) := by
  classical
  unfold slj
  rw [lastLightAux_succ, if_pos ⟨rfl, hH⟩]
  simp only [Option.elim]
  rw [riskUpTo_succ, if_pos rfl]

lemma slj_of_LL (i k : Fin n) (hL : LL μ C γ a x i = some k) :
    slj μ C γ a x i.val (a i x) = riskUpTo μ (cvRule μ C γ a) x (cvRule μ C γ a k x) i.val := by
  unfold slj
  unfold LL at hL
  rw [hL]; rfl

lemma slj_of_LL_none (i : Fin n) (hL : LL μ C γ a x i = none) :
    slj μ C γ a x i.val (a i x) = 0 := by
  unfold slj
  unfold LL at hL
  rw [hL]; rfl

lemma pot_step (hμ : ∀ i, IsProbabilityMeasure (μ i)) (ha : IsPolicy a) (hx : ∀ k, 0 ≤ x k) (hC : 0 < C) (hγ : 0 < γ) (i : Fin n)
    (hI : (NPc μ C γ a x i.val : ℝ) + (C / γ) * Sl μ C γ a x i.val ≤
      NPL μ C γ a x i.val + 2 * (C / γ) * Rho μ a x i.val) :
    (NPc μ C γ a x (i.val + 1) : ℝ) + (C / γ) * Sl μ C γ a x (i.val + 1) ≤
      NPL μ C γ a x (i.val + 1) + 2 * (C / γ) * Rho μ a x (i.val + 1) := by
  haveI := hμ i
  set κ := C / γ with hκ
  have hκpos : 0 < κ := div_pos hC hγ
  have hκb : κ * (γ / C) = 1 := by rw [hκ]; field_simp
  set δ := overflowProb (μ i) (usage a x (a i x) i) with hδ
  have hRho := Rho_succ μ a x i
  rw [← hδ] at hRho
  rw [hRho]
  have hq0 : overflowProb (μ i) 0 ≤ δ := overflowProb_mono _ (usage_nonneg a x hx _ _)
  have hq0nn : 0 ≤ overflowProb (μ i) 0 := overflowProb_nonneg _ _
  have hNPL : (NPL μ C γ a x i.val : ℝ) ≤ NPL μ C γ a x (i.val + 1) := by
    exact_mod_cast NPL_mono μ C γ a x i
  have hNPc : (NPc μ C γ a x (i.val + 1) : ℝ) ≤ NPc μ C γ a x i.val + 1 := by
    exact_mod_cast NPc_succ_le μ C γ a x i
  have hSl := Sl_succ μ C γ a x i
  rcases cv_dichotomy μ C γ a x i with ⟨k, hH, hL, hF, heq⟩ | ⟨hfr, hcase⟩
  · -- fits in the current sub-bin
    have hk := LL_spec_some μ C γ a x i k hL
    have hNPc' : NPc μ C γ a x (i.val + 1) = NPc μ C γ a x i.val :=
      NPc_succ_eq μ C γ a x i ⟨k, hk.1, heq.symm⟩
    rw [hNPc']
    rw [slj_light μ C γ a x i hH, slj_of_LL μ C γ a x i k hL, ← heq] at hSl
    have hd' : overflowProb (μ i) (usage (cvRule μ C γ a) x (cvRule μ C γ a i x) i) ≤ δ :=
      overflowProb_mono _ (usage_cv_le μ C γ a x hx i i)
    rw [hSl]
    have hδnn : 0 ≤ δ := overflowProb_nonneg _ _
    have e1 : κ * (Sl μ C γ a x i.val -
        riskUpTo μ (cvRule μ C γ a) x (cvRule μ C γ a i x) i.val +
        (riskUpTo μ (cvRule μ C γ a) x (cvRule μ C γ a i x) i.val +
          overflowProb (μ i) (usage (cvRule μ C γ a) x (cvRule μ C γ a i x) i))) =
        κ * Sl μ C γ a x i.val +
          κ * overflowProb (μ i) (usage (cvRule μ C γ a) x (cvRule μ C γ a i x) i) := by ring
    rw [e1]
    have := mul_le_mul_of_nonneg_left hd' hκpos.le
    have := mul_nonneg hκpos.le hδnn
    nlinarith
  · have hfr0 : ∀ k : Fin n, k.val < i.val → cvRule μ C γ a k x ≠ cvRule μ C γ a i x := hfr
    have hU0 : usage (cvRule μ C γ a) x (cvRule μ C γ a i x) i = 0 :=
      usage_of_fresh _ x _ _ hfr0
    have hR0 : riskUpTo μ (cvRule μ C γ a) x (cvRule μ C γ a i x) i.val = 0 :=
      riskUpTo_of_fresh μ _ x _ _ hfr0
    by_cases hH : IsHeavy μ C γ i
    · -- heavy item: own bin, potential pays
      have hsame : slj μ C γ a x (i.val + 1) (a i x) = slj μ C γ a x i.val (a i x) := by
        refine slj_same μ C γ a x i (a i x) (fun h => h.2 hH) (fun k hk => ?_)
        have hkl := ((lastLightAux_spec μ C γ _ _ _ _).mp hk).1.1
        exact fun h => hfr0 k hkl h.symm
      rw [hsame] at hSl
      have hSl' : Sl μ C γ a x (i.val + 1) = Sl μ C γ a x i.val := by rw [hSl]; ring
      rw [hSl']
      have hδbig : γ / C < δ := by
        unfold IsHeavy at hH
        rw [overflowProb_zero] at hq0
        linarith
      have : 1 < κ * δ := by
        have := mul_lt_mul_of_pos_left hδbig hκpos
        linarith
      nlinarith
    · rcases hcase with hH' | hLn | ⟨k, hL, hnF⟩
      · exact absurd hH' hH
      · -- first light item of this original bin
        have hnone : ∀ k : Fin n, k.val < i.val → a k x = a i x → IsHeavy μ C γ k :=
          (lastLightAux_none μ C γ _ _ _).mp hLn
        have hNPL' := NPL_succ_new μ C γ a x i hH hnone
        rw [slj_light μ C γ a x i hH, slj_of_LL_none μ C γ a x i hLn, hU0, hR0] at hSl
        rw [hSl]
        have hcast : (NPL μ C γ a x (i.val + 1) : ℝ) = NPL μ C γ a x i.val + 1 := by
          exact_mod_cast hNPL'
        rw [hcast]
        have := mul_le_mul_of_nonneg_left hq0 hκpos.le
        have := mul_nonneg hκpos.le hq0nn
        nlinarith
      · -- split: open a new sub-bin
        have hk := LL_spec_some μ C γ a x i k hL
        rw [slj_light μ C γ a x i hH, slj_of_LL μ C γ a x i k hL, hU0, hR0] at hSl
        rw [hSl]
        set r' := riskUpTo μ (cvRule μ C γ a) x (cvRule μ C γ a k x) i.val with hr'
        have hu' : usage (cvRule μ C γ a) x (cvRule μ C γ a k x) i ≤ usage a x (a i x) i := by
          have := usage_cv_le μ C γ a x hx k i
          rw [hk.2.1] at this; exact this
        have hfeas : usage a x (a i x) i ≤ 1 := ha.2.2 x i
        have hq' : overflowProb (μ i) (usage (cvRule μ C γ a) x (cvRule μ C γ a k x) i) ≤ δ :=
          overflowProb_mono _ hu'
        have hbig : γ / C < r' + δ := by
          unfold FitsR at hnF
          push Not at hnF
          have := hnF (le_trans hu' hfeas)
          linarith
        have h1 : 1 < κ * r' + κ * δ := by
          have := mul_lt_mul_of_pos_left hbig hκpos
          rw [mul_add] at this; linarith
        have := mul_le_mul_of_nonneg_left hq0 hκpos.le
        nlinarith

end OBPX


open MeasureTheory OverflowBinPacking.IID
open scoped ENNReal

namespace OBPX

/-! ## A dynamic-programming value function on bin configurations (i.i.d. case) -/

section V

variable (ν : Measure ℝ) [IsProbabilityMeasure ν] (b : ℝ)

/-- a bin in state `(load, risk)` can receive one more item -/
def adm (s : ℝ × ℝ) : Prop := s.1 ≤ 1 ∧ s.2 + overflowProb ν s.1 ≤ b

noncomputable instance (s : ℝ × ℝ) : Decidable (adm ν b s) := Classical.dec _

/-- state transition when an item of size `y` is added -/
noncomputable def Tr (s : ℝ × ℝ) (y : ℝ) : ℝ × ℝ := (s.1 + y, s.2 + overflowProb ν s.1)

/-- Expected number of new bins Budgeted Greedy needs for `m` more items, starting from
`k` open bins whose states are `L 0, …, L (k-1)`. -/
noncomputable def V : ℕ → ℕ → (ℕ → ℝ × ℝ) → ℝ≥0∞
  | 0, _, _ => 0
  | m + 1, k, L =>
    if h : ∃ l, l < k ∧ adm ν b (L l) then
      ∫⁻ y, V m k (Function.update L (Nat.find h) (Tr ν (L (Nat.find h)) y)) ∂ν
    else 1 + ∫⁻ y, V m (k + 1) (Function.update L k (Tr ν (0, 0) y)) ∂ν

lemma V_zero (k : ℕ) (L : ℕ → ℝ × ℝ) : V ν b 0 k L = 0 := rfl

lemma V_succ_of_adm (m k : ℕ) (L : ℕ → ℝ × ℝ) (h : ∃ l, l < k ∧ adm ν b (L l)) :
    V ν b (m + 1) k L = ∫⁻ y, V ν b m k (Function.update L (Nat.find h)
      (Tr ν (L (Nat.find h)) y)) ∂ν := by
  classical
  rw [V]; simp only [dif_pos h]

lemma V_succ_of_not (m k : ℕ) (L : ℕ → ℝ × ℝ) (h : ¬ ∃ l, l < k ∧ adm ν b (L l)) :
    V ν b (m + 1) k L = 1 + ∫⁻ y, V ν b m (k + 1) (Function.update L k (Tr ν (0, 0) y)) ∂ν := by
  classical
  rw [V]; simp only [dif_neg h]

lemma measurable_overflowProb'' : Measurable (fun S : ℝ => overflowProb ν S) := by
  apply Monotone.measurable
  intro a b hab
  unfold overflowProb
  apply measureReal_mono
  · intro z hz; simp only [Set.mem_Ioi] at hz ⊢; linarith
  · exact measure_ne_top _ _

lemma measurableSet_adm : MeasurableSet {s : ℝ × ℝ | adm ν b s} :=
  (measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_le (measurable_snd.add ((measurable_overflowProb'' ν).comp measurable_fst))
      measurable_const)


/-- measurability of `(L, y) ↦ update L l (Tr (L l) y)` -/
lemma measurable_upd (l : ℕ) :
    Measurable (fun p : (ℕ → ℝ × ℝ) × ℝ => Function.update p.1 l (Tr ν (p.1 l) p.2)) := by
  refine measurable_pi_iff.mpr (fun l' => ?_)
  by_cases h : l' = l
  · subst h
    simp only [Function.update_self]
    unfold Tr
    exact ((measurable_fst.comp ((measurable_pi_apply l').comp measurable_fst)).add measurable_snd).prodMk
      ((measurable_snd.comp ((measurable_pi_apply l').comp measurable_fst)).add
        ((measurable_overflowProb'' ν).comp
          (measurable_fst.comp ((measurable_pi_apply l').comp measurable_fst))))
  · simp only [Function.update_of_ne h]
    exact (measurable_pi_apply l').comp measurable_fst

lemma measurable_upd_const (l : ℕ) (s : ℝ × ℝ) :
    Measurable (fun p : (ℕ → ℝ × ℝ) × ℝ => Function.update p.1 l (Tr ν s p.2)) := by
  refine measurable_pi_iff.mpr (fun l' => ?_)
  by_cases h : l' = l
  · subst h
    simp only [Function.update_self]
    unfold Tr
    exact (measurable_const.add measurable_snd).prodMk measurable_const
  · simp only [Function.update_of_ne h]
    exact (measurable_pi_apply l').comp measurable_fst

lemma measurable_of_countable_index {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    [Countable β] (c : α → β) (hc : ∀ i, MeasurableSet (c ⁻¹' {i}))
    (W : β → α → γ) (hW : ∀ i, Measurable (W i)) : Measurable (fun a => W (c a) a) := by
  intro s hs
  have : (fun a => W (c a) a) ⁻¹' s = ⋃ i, (c ⁻¹' {i} ∩ (W i) ⁻¹' s) := by
    ext a; simp
  rw [this]
  exact MeasurableSet.iUnion (fun i => (hc i).inter (hW i hs))

lemma measurable_V (m : ℕ) : ∀ k, Measurable (V ν b m k) := by
  classical
  induction m with
  | zero => intro k; exact measurable_const
  | succ m ih =>
    intro k
    -- the index chosen: least admissible position, or `k` if none
    let c : (ℕ → ℝ × ℝ) → ℕ := fun L =>
      if h : ∃ l, l < k ∧ adm ν b (L l) then Nat.find h else k
    let W : ℕ → (ℕ → ℝ × ℝ) → ℝ≥0∞ := fun l L =>
      if l < k then ∫⁻ y, V ν b m k (Function.update L l (Tr ν (L l) y)) ∂ν
      else 1 + ∫⁻ y, V ν b m (k + 1) (Function.update L k (Tr ν (0, 0) y)) ∂ν
    have hVW : V ν b (m + 1) k = fun L => W (c L) L := by
      funext L
      by_cases h : ∃ l, l < k ∧ adm ν b (L l)
      · rw [V_succ_of_adm ν b m k L h]
        have hc : c L = Nat.find h := by simp only [c, dif_pos h]
        simp only [W, hc, if_pos (Nat.find_spec h).1]
      · rw [V_succ_of_not ν b m k L h]
        have hc : c L = k := by simp only [c, dif_neg h]
        simp only [W, hc, lt_irrefl, if_false]
    rw [hVW]
    apply measurable_of_countable_index
    · intro l
      have hA : ∀ l', MeasurableSet {L : ℕ → ℝ × ℝ | adm ν b (L l')} :=
        fun l' => (measurableSet_adm ν b).preimage (measurable_pi_apply l')
      by_cases hl : l < k
      · have : c ⁻¹' {l} = {L | adm ν b (L l)} ∩ ⋂ l' ∈ Finset.range l, {L | ¬ adm ν b (L l')} := by
          ext L
          simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
            Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range, c]
          constructor
          · intro hcL
            by_cases h : ∃ l, l < k ∧ adm ν b (L l)
            · rw [dif_pos h] at hcL
              subst hcL
              exact ⟨(Nat.find_spec h).2, fun l' hl' hadm =>
                Nat.find_min h hl' ⟨by have := (Nat.find_spec h).1; omega, hadm⟩⟩
            · rw [dif_neg h] at hcL; omega
          · rintro ⟨h1, h2⟩
            have h : ∃ l, l < k ∧ adm ν b (L l) := ⟨l, hl, h1⟩
            rw [dif_pos h]
            apply le_antisymm
            · exact Nat.find_min' h ⟨hl, h1⟩
            · by_contra hlt; push Not at hlt
              exact h2 _ hlt (Nat.find_spec h).2
        rw [this]
        exact (hA l).inter (MeasurableSet.biInter (Set.to_countable _)
          (fun l' _ => (hA l').compl))
      · by_cases hlk : l = k
        · subst hlk
          have : c ⁻¹' {l} = ⋂ l' ∈ Finset.range l, {L | ¬ adm ν b (L l')} := by
            ext L
            simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter,
              Finset.mem_range, Set.mem_ofPred_eq, c]
            constructor
            · intro hcL l' hl' hadm
              have h : ∃ l'', l'' < l ∧ adm ν b (L l'') := ⟨l', hl', hadm⟩
              rw [dif_pos h] at hcL
              have := (Nat.find_spec h).1; omega
            · intro hall
              have h : ¬ ∃ l'', l'' < l ∧ adm ν b (L l'') := fun ⟨l'', h1, h2⟩ => hall l'' h1 h2
              rw [dif_neg h]
          rw [this]
          exact MeasurableSet.biInter (Set.to_countable _) (fun l' _ => (hA l').compl)
        · have : c ⁻¹' {l} = ∅ := by
            ext L
            simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
              iff_false, c]
            split_ifs with h
            · have := (Nat.find_spec h).1; omega
            · omega
          rw [this]; exact MeasurableSet.empty
    · intro l
      by_cases hl : l < k
      · have : W l = fun L => ∫⁻ y, V ν b m k (Function.update L l (Tr ν (L l) y)) ∂ν := by
          funext L; simp only [W, if_pos hl]
        rw [this]
        exact ((ih k).comp (measurable_upd ν l)).lintegral_prod_right'
      · have : W l = fun L => 1 + ∫⁻ y, V ν b m (k + 1) (Function.update L k (Tr ν (0, 0) y)) ∂ν := by
          funext L; simp only [W, if_neg hl]
        rw [this]
        exact measurable_const.add (((ih (k + 1)).comp (measurable_upd_const ν k _)).lintegral_prod_right')

lemma measurable_upd2 (L : ℕ → ℝ × ℝ) (l l' : ℕ) (s s' : ℝ × ℝ) :
    Measurable (fun p : ℝ × ℝ => Function.update (Function.update L l (Tr ν s p.1)) l'
      (Tr ν s' p.2)) := by
  refine measurable_pi_iff.mpr (fun r => ?_)
  by_cases h' : r = l'
  · subst h'
    simp only [Function.update_self]
    unfold Tr
    exact (measurable_const.add measurable_snd).prodMk measurable_const
  · simp only [Function.update_of_ne h']
    by_cases h : r = l
    · subst h
      simp only [Function.update_self]
      unfold Tr
      exact (measurable_const.add measurable_fst).prodMk measurable_const
    · simp only [Function.update_of_ne h]
      exact measurable_const

lemma lintegral_swap_upd (m k : ℕ) (L : ℕ → ℝ × ℝ) (l l' : ℕ) (hll : l ≠ l') (s s' : ℝ × ℝ) :
    ∫⁻ y, ∫⁻ z, V ν b m k (Function.update (Function.update L l (Tr ν s y)) l' (Tr ν s' z)) ∂ν ∂ν =
    ∫⁻ y, ∫⁻ z, V ν b m k (Function.update (Function.update L l' (Tr ν s' y)) l (Tr ν s z)) ∂ν ∂ν := by
  rw [lintegral_lintegral_swap]
  · congr 1; funext y; congr 1; funext z
    rw [Function.update_comm hll]
  · exact ((measurable_V ν b m k).comp (measurable_upd2 ν L l l' s s')).aemeasurable

lemma V_key (m : ℕ) : ∀ (k : ℕ) (L : ℕ → ℝ × ℝ) (l : ℕ), l < k → adm ν b (L l) →
    ∫⁻ y, V ν b m k (Function.update L l (Tr ν (L l) y)) ∂ν = V ν b (m + 1) k L := by
  induction m with
  | zero =>
    intro k L l hl hadm
    rw [V_succ_of_adm ν b 0 k L ⟨l, hl, hadm⟩]
    simp [V_zero]
  | succ m ih =>
    intro k L l hl hadm
    have h : ∃ l, l < k ∧ adm ν b (L l) := ⟨l, hl, hadm⟩
    rw [V_succ_of_adm ν b (m + 1) k L h]
    set ls := Nat.find h with hls
    by_cases hll : l = ls
    · rw [hll]
    · have hls' : ls < k ∧ adm ν b (L ls) := Nat.find_spec h
      have e1 : ∀ y, V ν b (m + 1) k (Function.update L l (Tr ν (L l) y)) =
          ∫⁻ z, V ν b m k (Function.update (Function.update L l (Tr ν (L l) y)) ls
            (Tr ν (L ls) z)) ∂ν := by
        intro y
        have := ih k (Function.update L l (Tr ν (L l) y)) ls hls'.1
          (by rw [Function.update_of_ne (Ne.symm hll)]; exact hls'.2)
        rw [Function.update_of_ne (Ne.symm hll)] at this
        exact this.symm
      have e2 : ∀ y, V ν b (m + 1) k (Function.update L ls (Tr ν (L ls) y)) =
          ∫⁻ z, V ν b m k (Function.update (Function.update L ls (Tr ν (L ls) y)) l
            (Tr ν (L l) z)) ∂ν := by
        intro y
        have := ih k (Function.update L ls (Tr ν (L ls) y)) l hl
          (by rw [Function.update_of_ne hll]; exact hadm)
        rw [Function.update_of_ne hll] at this
        exact this.symm
      simp_rw [e1, e2]
      exact lintegral_swap_upd ν b m k L l ls hll (L l) (L ls)

lemma V_key2 (m : ℕ) : ∀ (k : ℕ) (L : ℕ → ℝ × ℝ),
    V ν b (m + 1) k L ≤ 1 + ∫⁻ y, V ν b m (k + 1) (Function.update L k (Tr ν (0, 0) y)) ∂ν := by
  induction m with
  | zero =>
    intro k L
    by_cases h : ∃ l, l < k ∧ adm ν b (L l)
    · rw [V_succ_of_adm ν b 0 k L h]; simp [V_zero]
    · rw [V_succ_of_not ν b 0 k L h]
  | succ m ih =>
    intro k L
    by_cases h : ∃ l, l < k ∧ adm ν b (L l)
    · rw [V_succ_of_adm ν b (m + 1) k L h]
      set ls := Nat.find h with hls
      have hls' : ls < k ∧ adm ν b (L ls) := Nat.find_spec h
      have hne : ls ≠ k := by omega
      calc ∫⁻ y, V ν b (m + 1) k (Function.update L ls (Tr ν (L ls) y)) ∂ν
          ≤ ∫⁻ y, (1 + ∫⁻ z, V ν b m (k + 1) (Function.update
              (Function.update L ls (Tr ν (L ls) y)) k (Tr ν (0, 0) z)) ∂ν) ∂ν :=
            lintegral_mono (fun y => ih k _)
        _ = 1 + ∫⁻ y, ∫⁻ z, V ν b m (k + 1) (Function.update
              (Function.update L ls (Tr ν (L ls) y)) k (Tr ν (0, 0) z)) ∂ν ∂ν := by
            rw [lintegral_add_left measurable_const]
            simp
        _ = 1 + ∫⁻ y, ∫⁻ z, V ν b m (k + 1) (Function.update
              (Function.update L k (Tr ν (0, 0) y)) ls (Tr ν (L ls) z)) ∂ν ∂ν := by
            rw [lintegral_swap_upd ν b m (k + 1) L ls k hne (L ls) (0, 0)]
        _ = 1 + ∫⁻ y, V ν b (m + 1) (k + 1) (Function.update L k (Tr ν (0, 0) y)) ∂ν := by
            congr 1
            refine lintegral_congr (fun y => ?_)
            have := V_key ν b m (k + 1) (Function.update L k (Tr ν (0, 0) y)) ls (by omega)
              (by rw [Function.update_of_ne hne]; exact hls'.2)
            rw [Function.update_of_ne hne] at this
            exact this
    · rw [V_succ_of_not ν b (m + 1) k L h]

lemma V_le (m : ℕ) : ∀ k L, V ν b m k L ≤ m := by
  induction m with
  | zero => intro k L; simp [V_zero]
  | succ m ih =>
    intro k L
    by_cases h : ∃ l, l < k ∧ adm ν b (L l)
    · rw [V_succ_of_adm ν b m k L h]
      calc _ ≤ ∫⁻ _y, (m : ℝ≥0∞) ∂ν := lintegral_mono (fun y => ih _ _)
        _ = m := by simp
        _ ≤ _ := by exact_mod_cast Nat.le_succ m
    · rw [V_succ_of_not ν b m k L h]
      calc _ ≤ 1 + ∫⁻ _y, (m : ℝ≥0∞) ∂ν := by gcongr with y; exact ih _ _
        _ = (m + 1 : ℕ) := by simp [add_comm]

end V

end OBPX


open MeasureTheory OverflowBinPacking.IID
open scoped ENNReal

namespace OBPX

variable {n : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν] (b : ℝ)

/-- Simulation of the bin configuration (in order of opening) along an assignment pattern. -/
noncomputable def sim (A : Fin n → Fin n) (x : Fin n → ℝ) : ℕ → ℕ × (ℕ → ℝ × ℝ) × (Fin n → ℕ)
  | 0 => (0, fun _ => (0, 0), fun _ => 0)
  | t + 1 =>
    if h : t < n then
      if ∃ k : Fin n, k.val < t ∧ A k = A ⟨t, h⟩ then
        ((sim A x t).1,
          Function.update (sim A x t).2.1 ((sim A x t).2.2 (A ⟨t, h⟩))
            (Tr ν ((sim A x t).2.1 ((sim A x t).2.2 (A ⟨t, h⟩))) (x ⟨t, h⟩)),
          (sim A x t).2.2)
      else
        ((sim A x t).1 + 1,
          Function.update (sim A x t).2.1 (sim A x t).1 (Tr ν (0, 0) (x ⟨t, h⟩)),
          Function.update (sim A x t).2.2 (A ⟨t, h⟩) (sim A x t).1)
    else sim A x t

lemma sim_succ_used (A : Fin n → Fin n) (x : Fin n → ℝ) (i : Fin n)
    (h : ∃ k : Fin n, k.val < i.val ∧ A k = A i) :
    sim ν A x (i.val + 1) = ((sim ν A x i).1,
      Function.update (sim ν A x i).2.1 ((sim ν A x i).2.2 (A i))
        (Tr ν ((sim ν A x i).2.1 ((sim ν A x i).2.2 (A i))) (x i)),
      (sim ν A x i).2.2) := by
  rw [sim, dif_pos i.isLt, if_pos h]

lemma sim_succ_new (A : Fin n → Fin n) (x : Fin n → ℝ) (i : Fin n)
    (h : ¬ ∃ k : Fin n, k.val < i.val ∧ A k = A i) :
    sim ν A x (i.val + 1) = ((sim ν A x i).1 + 1,
      Function.update (sim ν A x i).2.1 (sim ν A x i).1 (Tr ν (0, 0) (x i)),
      Function.update (sim ν A x i).2.2 (A i) (sim ν A x i).1) := by
  rw [sim, dif_pos i.isLt, if_neg h]

/-- `sim` at time `t` only depends on the first `t` coordinates. -/
lemma sim_congr (A A' : Fin n → Fin n) (x x' : Fin n → ℝ) (t : ℕ)
    (h : ∀ k : Fin n, k.val < t → A k = A' k ∧ x k = x' k) :
    sim ν A x t = sim ν A' x' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ih' := ih (fun k hk => h k (by omega))
    by_cases htn : t < n
    · have hA := (h ⟨t, htn⟩ (by simp)).1
      have hx := (h ⟨t, htn⟩ (by simp)).2
      have hiff : (∃ k : Fin n, k.val < t ∧ A k = A ⟨t, htn⟩) ↔
          (∃ k : Fin n, k.val < t ∧ A' k = A' ⟨t, htn⟩) := by
        constructor
        · rintro ⟨k, hk, he⟩; exact ⟨k, hk, by rw [← (h k (by omega)).1, ← hA]; exact he⟩
        · rintro ⟨k, hk, he⟩; exact ⟨k, hk, by rw [(h k (by omega)).1, hA]; exact he⟩
      by_cases hu : ∃ k : Fin n, k.val < t ∧ A k = A ⟨t, htn⟩
      · rw [sim_succ_used ν A x ⟨t, htn⟩ hu, sim_succ_used ν A' x' ⟨t, htn⟩ (hiff.mp hu), ih', hA, hx]
      · rw [sim_succ_new ν A x ⟨t, htn⟩ hu,
          sim_succ_new ν A' x' ⟨t, htn⟩ (fun hh => hu (hiff.mpr hh)), ih', hA, hx]
    · rw [sim, dif_neg htn, sim, dif_neg htn, ih']

/-- The discrete part of `sim` does not depend on the sizes. -/
lemma sim_discrete (A : Fin n → Fin n) (x x' : Fin n → ℝ) (t : ℕ) :
    (sim ν A x t).1 = (sim ν A x' t).1 ∧ (sim ν A x t).2.2 = (sim ν A x' t).2.2 := by
  induction t with
  | zero => exact ⟨rfl, rfl⟩
  | succ t ih =>
    by_cases htn : t < n
    · by_cases hu : ∃ k : Fin n, k.val < t ∧ A k = A ⟨t, htn⟩
      · rw [sim_succ_used ν A x ⟨t, htn⟩ hu, sim_succ_used ν A x' ⟨t, htn⟩ hu]
        exact ⟨ih.1, ih.2⟩
      · rw [sim_succ_new ν A x ⟨t, htn⟩ hu, sim_succ_new ν A x' ⟨t, htn⟩ hu]
        simp only [ih.1, ih.2, and_self]
    · rw [sim, dif_neg htn, sim, dif_neg htn]; exact ih

lemma measurable_sim_L (A : Fin n → Fin n) (t : ℕ) :
    Measurable (fun x : Fin n → ℝ => (sim ν A x t).2.1) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    by_cases htn : t < n
    · by_cases hu : ∃ k : Fin n, k.val < t ∧ A k = A ⟨t, htn⟩
      · have e : (fun x : Fin n → ℝ => (sim ν A x (t + 1)).2.1) = fun x =>
            Function.update (sim ν A x t).2.1 ((sim ν A 0 t).2.2 (A ⟨t, htn⟩))
              (Tr ν ((sim ν A x t).2.1 ((sim ν A 0 t).2.2 (A ⟨t, htn⟩))) (x ⟨t, htn⟩)) := by
          funext x
          rw [sim_succ_used ν A x ⟨t, htn⟩ hu, (sim_discrete ν A x 0 t).2]
        rw [e]
        exact (measurable_upd ν _).comp (ih.prodMk (measurable_pi_apply _))
      · have e : (fun x : Fin n → ℝ => (sim ν A x (t + 1)).2.1) = fun x =>
            Function.update (sim ν A x t).2.1 (sim ν A 0 t).1 (Tr ν (0, 0) (x ⟨t, htn⟩)) := by
          funext x
          rw [sim_succ_new ν A x ⟨t, htn⟩ hu, (sim_discrete ν A x 0 t).1]
        rw [e]
        exact (measurable_upd_const ν _ _).comp (ih.prodMk (measurable_pi_apply _))
    · have e : (fun x : Fin n → ℝ => (sim ν A x (t + 1)).2.1) = fun x => (sim ν A x t).2.1 := by
        funext x; rw [sim, dif_neg htn]
      rw [e]; exact ih

/-- invariants of the simulated configuration for a rule `a` -/
def SimInv (a : Rule n) (x : Fin n → ℝ) (t : ℕ) : Prop :=
  let c := sim ν (fun k => a k x) x t
  c.1 = ((Finset.univ.filter (fun k : Fin n => k.val < t)).image (fun k => a k x)).card ∧
  (∀ j, (∃ k : Fin n, k.val < t ∧ a k x = j) → c.2.2 j < c.1) ∧
  (∀ j j', (∃ k : Fin n, k.val < t ∧ a k x = j) → (∃ k : Fin n, k.val < t ∧ a k x = j') →
    c.2.2 j = c.2.2 j' → j = j') ∧
  (∀ p, p < c.1 → ∃ j, (∃ k : Fin n, k.val < t ∧ a k x = j) ∧ c.2.2 j = p) ∧
  (∀ j, (∃ k : Fin n, k.val < t ∧ a k x = j) →
    c.2.1 (c.2.2 j) = (usage a x j t, riskUpTo (fun _ : Fin n => ν) a x j t))

lemma sim_inv (a : Rule n) (x : Fin n → ℝ) : ∀ t, t ≤ n → SimInv ν a x t := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨by simp [sim], fun j ⟨k, hk, _⟩ => absurd hk (Nat.not_lt_zero _),
      fun j j' ⟨k, hk, _⟩ => absurd hk (Nat.not_lt_zero _),
      fun p hp => absurd hp (by simp [sim]), fun j ⟨k, hk, _⟩ => absurd hk (Nat.not_lt_zero _)⟩
  | succ t ih =>
    intro ht
    have htn : t < n := by omega
    obtain ⟨I1, I2, I3, I4, I5⟩ := ih (by omega)
    set i : Fin n := ⟨t, htn⟩ with hi
    have hti : t = i.val := rfl
    set c := sim ν (fun k => a k x) x t with hc
    have hused_succ : ∀ j, (∃ k : Fin n, k.val < t + 1 ∧ a k x = j) ↔
        ((∃ k : Fin n, k.val < t ∧ a k x = j) ∨ a i x = j) := by
      intro j
      constructor
      · rintro ⟨k, hk, he⟩
        by_cases hkt : k.val < t
        · exact Or.inl ⟨k, hkt, he⟩
        · right; have : k = i := Fin.ext (by simp [hi]; omega)
          rw [← this]; exact he
      · rintro (⟨k, hk, he⟩ | he)
        · exact ⟨k, by omega, he⟩
        · exact ⟨i, by simp [hi], he⟩
    have himg : (Finset.univ.filter (fun k : Fin n => k.val < t + 1)).image (fun k => a k x) =
        insert (a i x) ((Finset.univ.filter (fun k : Fin n => k.val < t)).image (fun k => a k x)) := by
      rw [show t + 1 = i.val + 1 from rfl, filter_lt_succ, Finset.image_insert]
    have hst_other : ∀ j, a i x ≠ j → usage a x j (t + 1) = usage a x j t ∧
        riskUpTo (fun _ : Fin n => ν) a x j (t + 1) = riskUpTo (fun _ : Fin n => ν) a x j t := by
      intro j hj
      rw [hti, usage_succ, riskUpTo_succ, if_neg hj, if_neg hj]; simp
    by_cases hu : ∃ k : Fin n, k.val < t ∧ a k x = a i x
    · have hs := sim_succ_used ν (fun k => a k x) x i hu
      rw [← hti] at hs
      unfold SimInv
      simp only
      rw [hs]
      simp only
      rw [← hc]
      have huse : ∀ j, (∃ k : Fin n, k.val < t + 1 ∧ a k x = j) ↔
          (∃ k : Fin n, k.val < t ∧ a k x = j) := by
        intro j; rw [hused_succ]
        constructor
        · rintro (h | h)
          · exact h
          · rw [← h]; exact hu
        · exact Or.inl
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [I1, himg, Finset.insert_eq_of_mem]
        obtain ⟨k, hk, he⟩ := hu
        exact Finset.mem_image.mpr ⟨k, by simp [hk], he⟩
      · intro j hj; exact I2 j ((huse j).mp hj)
      · intro j j' hj hj'; exact I3 j j' ((huse j).mp hj) ((huse j').mp hj')
      · intro p hp
        obtain ⟨j, hj, hpj⟩ := I4 p hp
        exact ⟨j, (huse j).mpr hj, hpj⟩
      · intro j hj
        have hj' := (huse j).mp hj
        by_cases hji : j = a i x
        · subst hji
          rw [Function.update_self, I5 _ hj', hti, usage_succ, riskUpTo_succ]
          simp [Tr]
        · have hne : c.2.2 j ≠ c.2.2 (a i x) := fun h => hji (I3 j (a i x) hj' hu h)
          rw [Function.update_of_ne hne, I5 j hj', (hst_other j (Ne.symm hji)).1,
            (hst_other j (Ne.symm hji)).2]
    · have hs := sim_succ_new ν (fun k => a k x) x i hu
      rw [← hti] at hs
      unfold SimInv
      simp only
      rw [hs]
      simp only
      rw [← hc]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [I1, himg, Finset.card_insert_of_notMem]
        intro hmem
        obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hmem
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        exact hu ⟨k, hk, he⟩
      · intro j hj
        rcases (hused_succ j).mp hj with hj' | hj'
        · have hne : j ≠ a i x := fun h => hu (h ▸ hj')
          rw [Function.update_of_ne hne]; have := I2 j hj'; omega
        · rw [← hj', Function.update_self]; omega
      · intro j j' hj hj' hpp
        rcases (hused_succ j).mp hj with h1 | h1 <;> rcases (hused_succ j').mp hj' with h2 | h2
        · have hne : j ≠ a i x := fun h => hu (h ▸ h1)
          have hne' : j' ≠ a i x := fun h => hu (h ▸ h2)
          rw [Function.update_of_ne hne, Function.update_of_ne hne'] at hpp
          exact I3 j j' h1 h2 hpp
        · have hne : j ≠ a i x := fun h => hu (h ▸ h1)
          rw [Function.update_of_ne hne, ← h2, Function.update_self] at hpp
          have := I2 j h1; omega
        · have hne' : j' ≠ a i x := fun h => hu (h ▸ h2)
          rw [Function.update_of_ne hne', ← h1, Function.update_self] at hpp
          have := I2 j' h2; omega
        · rw [← h1, ← h2]
      · intro p hp
        by_cases hpk : p < c.1
        · obtain ⟨j, hj, hpj⟩ := I4 p hpk
          have hne : j ≠ a i x := fun h => hu (h ▸ hj)
          exact ⟨j, (hused_succ j).mpr (Or.inl hj), by rw [Function.update_of_ne hne]; exact hpj⟩
        · refine ⟨a i x, (hused_succ _).mpr (Or.inr rfl), ?_⟩
          rw [Function.update_self]; omega
      · intro j hj
        rcases (hused_succ j).mp hj with hj' | hj'
        · have hne : j ≠ a i x := fun h => hu (h ▸ hj')
          rw [Function.update_of_ne hne]
          have hlt := I2 j hj'
          rw [Function.update_of_ne (by omega), I5 j hj', (hst_other j (Ne.symm hne)).1,
            (hst_other j (Ne.symm hne)).2]
        · subst hj'
          rw [Function.update_self, Function.update_self]
          have h0 : ∀ k : Fin n, k.val < i.val → a k x ≠ a i x := fun k hk he => hu ⟨k, hk, he⟩
          rw [hti, usage_succ, riskUpTo_succ, if_pos rfl, if_pos rfl,
            usage_of_fresh a x _ _ h0, riskUpTo_of_fresh _ a x _ _ h0]
          simp [Tr]

/-- the potential: value-to-go plus bins opened so far -/
noncomputable def Psi (a : Rule n) (t : ℕ) (x : Fin n → ℝ) : ℝ≥0∞ :=
  V ν b (n - t) (sim ν (fun k => a k x) x t).1 (sim ν (fun k => a k x) x t).2.1 +
    ((sim ν (fun k => a k x) x t).1 : ℝ≥0∞)

lemma measurable_Psi (a : Rule n) (ha : MeasurableRule a) (t : ℕ) :
    Measurable (Psi ν b a t) := by
  unfold Psi
  refine measurable_of_countable_index (fun x => fun k => a k x) ?_
    (fun A x => V ν b (n - t) (sim ν A x t).1 (sim ν A x t).2.1 + ((sim ν A x t).1 : ℝ≥0∞)) ?_
  · intro A
    have : (fun x : Fin n → ℝ => fun k => a k x) ⁻¹' {A} = ⋂ k, {x | a k x = A k} := by
      ext x; simp [funext_iff]
    rw [this]; exact MeasurableSet.iInter (fun k => ha k (A k))
  · intro A
    have e : (fun x => V ν b (n - t) (sim ν A x t).1 (sim ν A x t).2.1 + ((sim ν A x t).1 : ℝ≥0∞))
        = fun x => V ν b (n - t) (sim ν A 0 t).1 (sim ν A x t).2.1 + ((sim ν A 0 t).1 : ℝ≥0∞) := by
      funext x; rw [(sim_discrete ν A x 0 t).1]
    rw [e]
    exact ((measurable_V ν b _ _).comp (measurable_sim_L ν A t)).add measurable_const

lemma lintegral_freeze (i : Fin n) (F : (Fin n → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x ∂(Measure.pi fun _ : Fin n => ν) =
      ∫⁻ x, (∫⁻ y, F (Function.update x i y) ∂ν) ∂(Measure.pi fun _ : Fin n => ν) := by
  classical
  have hG : Measurable (∫⋯∫⁻_{i}, F ∂(fun _ : Fin n => ν)) := hF.lmarginal _
  have e : (fun x => ∫⁻ y, F (Function.update x i y) ∂ν) = ∫⋯∫⁻_{i}, F ∂(fun _ : Fin n => ν) := by
    rw [lmarginal_singleton]
  rw [e]
  apply lintegral_eq_of_lmarginal_eq {i} hF hG
  funext x
  rw [lmarginal_singleton (∫⋯∫⁻_{i}, F ∂(fun _ : Fin n => ν))]
  simp_rw [lmarginal_update_of_mem (fun _ : Fin n => ν) (Finset.mem_singleton_self i)]
  simp

lemma riskUpTo_mono' (μ : Fin n → Measure ℝ) (a : Rule n) (x : Fin n → ℝ) (j : Fin n) {s t : ℕ}
    (hst : s ≤ t) : riskUpTo μ a x j s ≤ riskUpTo μ a x j t := by
  unfold riskUpTo
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  · intro k _ _; exact overflowProb_nonneg _ _

/-- one telescoping step -/
lemma Psi_step (a : Rule n) (ha : Nonanticipative a) (x : Fin n → ℝ) (i : Fin n)
    (Hlow : (∃ k : Fin n, k.val < i.val ∧ a k x = a i x) →
      adm ν b (usage a x (a i x) i, riskUpTo (fun _ : Fin n => ν) a x (a i x) i)) :
    Psi ν b a i.val x ≤ ∫⁻ y, Psi ν b a (i.val + 1) (Function.update x i y) ∂ν ∧
    ((¬ (∃ k : Fin n, k.val < i.val ∧ a k x = a i x) →
      ∀ j, (∃ k : Fin n, k.val < i.val ∧ a k x = j) →
        ¬ adm ν b (usage a x j i, riskUpTo (fun _ : Fin n => ν) a x j i)) →
      Psi ν b a i.val x = ∫⁻ y, Psi ν b a (i.val + 1) (Function.update x i y) ∂ν) := by
  obtain ⟨I1, I2, I3, I4, I5⟩ := sim_inv ν a x i.val i.isLt.le
  set c := sim ν (fun k => a k x) x i.val with hc
  have hA : ∀ y : ℝ, ∀ k : Fin n, k.val ≤ i.val → a k (Function.update x i y) = a k x := by
    intro y k hk
    refine ha k _ _ (fun k' hk' => ?_)
    have : k' ≠ i := fun e => by
      rw [e] at hk'; exact absurd (Fin.lt_def.mp hk') (by omega)
    exact Function.update_of_ne this _ _
  have hsim : ∀ y : ℝ, sim ν (fun k => a k (Function.update x i y)) (Function.update x i y) i.val
      = c := by
    intro y
    rw [hc]
    apply sim_congr
    intro k hk
    refine ⟨hA y k hk.le, ?_⟩
    exact Function.update_of_ne (fun e => by rw [e] at hk; exact lt_irrefl _ hk) _ _
  have hflag : ∀ y : ℝ, (∃ k : Fin n, k.val < i.val ∧
      a k (Function.update x i y) = a i (Function.update x i y)) ↔
      (∃ k : Fin n, k.val < i.val ∧ a k x = a i x) := by
    intro y
    rw [hA y i le_rfl]
    constructor
    · rintro ⟨k, hk, he⟩; exact ⟨k, hk, by rw [← hA y k hk.le]; exact he⟩
    · rintro ⟨k, hk, he⟩; exact ⟨k, hk, by rw [hA y k hk.le]; exact he⟩
  have hnt : n - i.val = (n - (i.val + 1)) + 1 := by have := i.isLt; omega
  have hPsi0 : Psi ν b a i.val x = V ν b (n - i.val) c.1 c.2.1 + (c.1 : ℝ≥0∞) := rfl
  by_cases hu : ∃ k : Fin n, k.val < i.val ∧ a k x = a i x
  · -- existing bin
    have hPsi1 : ∀ y, Psi ν b a (i.val + 1) (Function.update x i y) =
        V ν b (n - (i.val + 1)) c.1 (Function.update c.2.1 (c.2.2 (a i x))
          (Tr ν (c.2.1 (c.2.2 (a i x))) y)) + (c.1 : ℝ≥0∞) := by
      intro y
      unfold Psi
      rw [sim_succ_used ν _ _ i ((hflag y).mpr hu), hsim y, hA y i le_rfl, Function.update_self]
    simp_rw [hPsi1]
    have hpos := I2 (a i x) hu
    have hadm : adm ν b (c.2.1 (c.2.2 (a i x))) := by rw [I5 _ hu]; exact Hlow hu
    have hkey := V_key ν b (n - (i.val + 1)) c.1 c.2.1 (c.2.2 (a i x)) hpos hadm
    rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one, hkey,
      ← hnt, hPsi0]
    exact ⟨le_rfl, fun _ => rfl⟩
  · -- new bin
    have hPsi1 : ∀ y, Psi ν b a (i.val + 1) (Function.update x i y) =
        V ν b (n - (i.val + 1)) (c.1 + 1) (Function.update c.2.1 c.1 (Tr ν (0, 0) y)) +
          ((c.1 + 1 : ℕ) : ℝ≥0∞) := by
      intro y
      unfold Psi
      rw [sim_succ_new ν _ _ i (fun h => hu ((hflag y).mp h)), hsim y, Function.update_self]
    simp_rw [hPsi1]
    rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one, hPsi0]
    have hk2 := V_key2 ν b (n - (i.val + 1)) c.1 c.2.1
    rw [← hnt] at hk2
    push_cast
    refine ⟨?_, fun Hbg => ?_⟩
    · calc V ν b (n - i.val) c.1 c.2.1 + (c.1 : ℝ≥0∞)
          ≤ (1 + ∫⁻ y, V ν b (n - (i.val + 1)) (c.1 + 1)
              (Function.update c.2.1 c.1 (Tr ν (0, 0) y)) ∂ν) + c.1 := by gcongr
        _ = _ := by ring
    · have hnone : ¬ ∃ l, l < c.1 ∧ adm ν b (c.2.1 l) := by
        rintro ⟨l, hl, hadm⟩
        obtain ⟨j, hj, hpj⟩ := I4 l hl
        rw [← hpj, I5 j hj] at hadm
        exact Hbg hu j hj hadm
      rw [hnt, V_succ_of_not ν b _ c.1 c.2.1 hnone]
      ring

lemma Psi_zero (a : Rule n) (x : Fin n → ℝ) :
    Psi ν b a 0 x = V ν b n 0 (fun _ => (0, 0)) := by
  unfold Psi; simp [sim]

lemma Psi_n (a : Rule n) (x : Fin n → ℝ) : Psi ν b a n x = (numOpened a x : ℝ≥0∞) := by
  obtain ⟨I1, -⟩ := sim_inv ν a x n le_rfl
  unfold Psi
  rw [Nat.sub_self, V_zero, zero_add, I1]
  have hfilt : (Finset.univ.filter (fun k : Fin n => k.val < n)) = Finset.univ := by
    ext k; simp
  rw [hfilt]; rfl

lemma Psi_tele (a : Rule n) (ha : IsPolicy a)
    (Hlow : ∀ x (i : Fin n), (∃ k : Fin n, k.val < i.val ∧ a k x = a i x) →
      adm ν b (usage a x (a i x) i, riskUpTo (fun _ : Fin n => ν) a x (a i x) i)) :
    ∀ t, t ≤ n → ∫⁻ x, Psi ν b a 0 x ∂(Measure.pi fun _ : Fin n => ν) ≤
      ∫⁻ x, Psi ν b a t x ∂(Measure.pi fun _ : Fin n => ν) := by
  intro t
  induction t with
  | zero => intro _; exact le_rfl
  | succ t ih =>
    intro ht
    have htn : t < n := by omega
    refine (ih (by omega)).trans ?_
    rw [lintegral_freeze ν ⟨t, htn⟩ _ (measurable_Psi ν b a ha.2.1 (t + 1))]
    exact lintegral_mono (fun x => (Psi_step ν b a ha.1 x ⟨t, htn⟩ (Hlow x ⟨t, htn⟩)).1)

lemma Psi_tele_eq (a : Rule n) (ha : IsPolicy a)
    (Hlow : ∀ x (i : Fin n), (∃ k : Fin n, k.val < i.val ∧ a k x = a i x) →
      adm ν b (usage a x (a i x) i, riskUpTo (fun _ : Fin n => ν) a x (a i x) i))
    (Hbg : ∀ x (i : Fin n), ¬ (∃ k : Fin n, k.val < i.val ∧ a k x = a i x) →
      ∀ j, (∃ k : Fin n, k.val < i.val ∧ a k x = j) →
        ¬ adm ν b (usage a x j i, riskUpTo (fun _ : Fin n => ν) a x j i)) :
    ∀ t, t ≤ n → ∫⁻ x, Psi ν b a 0 x ∂(Measure.pi fun _ : Fin n => ν) =
      ∫⁻ x, Psi ν b a t x ∂(Measure.pi fun _ : Fin n => ν) := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    have htn : t < n := by omega
    rw [ih (by omega)]
    rw [lintegral_freeze ν ⟨t, htn⟩ _ (measurable_Psi ν b a ha.2.1 (t + 1))]
    exact lintegral_congr (fun x =>
      (Psi_step ν b a ha.1 x ⟨t, htn⟩ (Hlow x ⟨t, htn⟩)).2 (Hbg x ⟨t, htn⟩))

lemma lower_bound (a : Rule n) (ha : IsPolicy a)
    (Hlow : ∀ x (i : Fin n), (∃ k : Fin n, k.val < i.val ∧ a k x = a i x) →
      adm ν b (usage a x (a i x) i, riskUpTo (fun _ : Fin n => ν) a x (a i x) i)) :
    V ν b n 0 (fun _ => (0, 0)) ≤
      ∫⁻ x, (numOpened a x : ℝ≥0∞) ∂(Measure.pi fun _ : Fin n => ν) := by
  have h := Psi_tele ν b a ha Hlow n le_rfl
  simp_rw [Psi_zero, Psi_n] at h
  simpa using h

lemma exact_value (a : Rule n) (ha : IsPolicy a)
    (Hlow : ∀ x (i : Fin n), (∃ k : Fin n, k.val < i.val ∧ a k x = a i x) →
      adm ν b (usage a x (a i x) i, riskUpTo (fun _ : Fin n => ν) a x (a i x) i))
    (Hbg : ∀ x (i : Fin n), ¬ (∃ k : Fin n, k.val < i.val ∧ a k x = a i x) →
      ∀ j, (∃ k : Fin n, k.val < i.val ∧ a k x = j) →
        ¬ adm ν b (usage a x j i, riskUpTo (fun _ : Fin n => ν) a x j i)) :
    V ν b n 0 (fun _ => (0, 0)) =
      ∫⁻ x, (numOpened a x : ℝ≥0∞) ∂(Measure.pi fun _ : Fin n => ν) := by
  have h := Psi_tele_eq ν b a ha Hlow Hbg n le_rfl
  simp_rw [Psi_zero, Psi_n] at h
  simpa using h

/-- budgeted policies only put items in admissible bins -/
lemma Hlow_of_budgeted (a : Rule n) (ha : IsPolicy a)
    (hB : IsBudgeted (fun _ : Fin n => ν) a b) :
    ∀ x (i : Fin n), (∃ k : Fin n, k.val < i.val ∧ a k x = a i x) →
      adm ν b (usage a x (a i x) i, riskUpTo (fun _ : Fin n => ν) a x (a i x) i) := by
  intro x i _
  refine ⟨ha.2.2 x i, ?_⟩
  have h1 := riskUpTo_succ (fun _ : Fin n => ν) a x (a i x) i
  rw [if_pos rfl] at h1
  have h2 := riskUpTo_mono' (fun _ : Fin n => ν) a x (a i x) (show i.val + 1 ≤ n by omega)
  have h3 := hB x (a i x)
  unfold risk at h3
  simp only
  linarith

end OBPX


open MeasureTheory OverflowBinPacking.IID
open scoped ENNReal

namespace OBPX

variable {n : ℕ}

lemma bgPrefix_mem_opened (μ : Fin n → Measure ℝ) (C γ : ℝ) (x : Fin n → ℝ) (t : ℕ) (ht : t ≤ n)
    (c : Fin n) :
    c ∈ prefixOpened (bgPrefix μ C γ x t) ↔ ∃ k : Fin n, k.val < t ∧ bgRule μ C γ k x = c := by
  simp only [prefixOpened, List.mem_toFinset, List.mem_iff_getElem?]
  constructor
  · rintro ⟨m, hm⟩
    have hml : m < (bgPrefix μ C γ x t).length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hm; simp at hm
    rw [bgPrefix_length] at hml
    have := bgPrefix_getElem? μ C γ x t ht ⟨m, by omega⟩
    simp only at this
    rw [hm, if_pos (lt_of_lt_of_le hml (min_le_left _ _))] at this
    exact ⟨⟨m, by omega⟩, lt_of_lt_of_le hml (min_le_left _ _), (Option.some.inj this).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.val, by rw [bgPrefix_getElem? μ C γ x t ht k, if_pos hk]⟩

lemma bg_Hbg (ν : Measure ℝ) [IsProbabilityMeasure ν] (C γ : ℝ) :
    ∀ x (i : Fin n), ¬ (∃ k : Fin n, k.val < i.val ∧
        bgRule (fun _ : Fin n => ν) C γ k x = bgRule (fun _ : Fin n => ν) C γ i x) →
      ∀ j, (∃ k : Fin n, k.val < i.val ∧ bgRule (fun _ : Fin n => ν) C γ k x = j) →
        ¬ adm ν (γ / C) (usage (bgRule (fun _ : Fin n => ν) C γ) x j i,
          riskUpTo (fun _ : Fin n => ν) (bgRule (fun _ : Fin n => ν) C γ) x j i) := by
  classical
  intro x i hnew j hj hadm
  set μ : Fin n → Measure ℝ := fun _ => ν
  set p := bgPrefix μ C γ x i.val with hp
  have hjmem : j ∈ prefixOpened p := (bgPrefix_mem_opened μ C γ x i.val i.isLt.le j).mpr hj
  have hcond : prefixUsage x p j ≤ 1 ∧
      prefixRisk μ x p j + overflowProb (μ i) (prefixUsage x p j) ≤ γ / C := by
    rw [hp, ← usage_bg μ C γ x j i.val i.isLt.le, ← riskUpTo_bg μ C γ x j i.val i.isLt.le]
    exact hadm
  have key : bgRule μ C γ i x ∈ prefixOpened p := by
    rw [bgRule_eq_choice]
    unfold bgChoice
    simp only
    split_ifs with he hu
    · exact (Finset.mem_filter.mp (Finset.min'_mem _ he)).1
    · exfalso; apply he; exact ⟨j, Finset.mem_filter.mpr ⟨hjmem, hcond⟩⟩
    · exfalso; apply he; exact ⟨j, Finset.mem_filter.mpr ⟨hjmem, hcond⟩⟩
  rw [bgPrefix_mem_opened μ C γ x i.val i.isLt.le] at key
  exact hnew key

theorem lemma43 (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν0 : ν (Set.Iio 0) = 0)
    (C γ : ℝ) (hC : 1 ≤ C) (hγ : 1 ≤ γ)
    (hLight : ν.real (Set.Ioi 1) ≤ γ / C) :
    IsBudgeted (fun _ : Fin n => ν) (bgRule (fun _ : Fin n => ν) C γ) (γ / C) ∧
    ∀ a : Rule n, IsPolicy a → IsBudgeted (fun _ : Fin n => ν) a (γ / C) →
      (∫ x, (numOpened (bgRule (fun _ : Fin n => ν) C γ) x : ℝ)
        ∂(Measure.pi (fun _ : Fin n => ν))) ≤
      (∫ x, (numOpened a x : ℝ) ∂(Measure.pi (fun _ : Fin n => ν))) := by
  have hμ : ∀ _ : Fin n, IsProbabilityMeasure ν := fun _ => inferInstance
  have hb : 0 ≤ γ / C := div_nonneg (by linarith) (by linarith)
  have hBG : IsBudgeted (fun _ : Fin n => ν) (bgRule (fun _ : Fin n => ν) C γ) (γ / C) := by
    intro x j
    refine (bg_risk_le (fun _ : Fin n => ν) C γ hb (fun _ => hLight) x j).trans ?_
    by_cases hx : x ∈ {x | ∃ i : Fin n, bgRule (fun _ : Fin n => ν) C γ i x = j}
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]; exact hb
  refine ⟨hBG, fun a ha haB => ?_⟩
  have hpolBG := bg_isPolicy (fun _ : Fin n => ν) C γ hμ
  have hEq := exact_value ν (γ / C) _ hpolBG
    (Hlow_of_budgeted ν (γ / C) _ hpolBG hBG) (bg_Hbg ν C γ)
  have hLe := lower_bound ν (γ / C) a ha (Hlow_of_budgeted ν (γ / C) a ha haB)
  have hconv : ∀ b : Rule n, MeasurableRule b →
      ∫ x, (numOpened b x : ℝ) ∂(Measure.pi (fun _ : Fin n => ν)) =
        (∫⁻ x, (numOpened b x : ℝ≥0∞) ∂(Measure.pi (fun _ : Fin n => ν))).toReal := by
    intro b hb'
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => by positivity))
      (measurable_numOpened b hb').aestronglyMeasurable]
    congr 1
    refine lintegral_congr (fun x => ?_)
    simp
  rw [hconv _ hpolBG.2.1, hconv a ha.2.1, ← hEq]
  refine ENNReal.toReal_mono ?_ hLe
  refine ne_top_of_le_ne_top (b := (n : ℝ≥0∞)) (by simp) ?_
  calc _ ≤ ∫⁻ _x, (n : ℝ≥0∞) ∂(Measure.pi (fun _ : Fin n => ν)) := by
        refine lintegral_mono (fun x => ?_)
        have : numOpened a x ≤ n := by
          unfold numOpened
          calc _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
            _ = n := by simp
        exact Nat.cast_le.mpr this
    _ = n := by simp

end OBPX


open OverflowBinPacking.IID in
theorem solution {n : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν0 : ν (Set.Iio 0) = 0)
    (C γ : ℝ) (hC : 1 ≤ C) (hγ : 1 ≤ γ)
    (hLight : ν.real (Set.Ioi 1) ≤ γ / C) :
    IsBudgeted (fun _ : Fin n => ν) (bgRule (fun _ : Fin n => ν) C γ) (γ / C) ∧
    ∀ a : Rule n, IsPolicy a → IsBudgeted (fun _ : Fin n => ν) a (γ / C) →
      (∫ x, (numOpened (bgRule (fun _ : Fin n => ν) C γ) x : ℝ)
        ∂(Measure.pi (fun _ : Fin n => ν))) ≤
      (∫ x, (numOpened a x : ℝ) ∂(Measure.pi (fun _ : Fin n => ν))) :=
  OBPX.lemma43 ν hν0 C γ hC hγ hLight
