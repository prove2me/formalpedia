-- Prove2me | solution 1 for OverflowBinPacking.IID.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T02:34:13.863331+00:00
-- url     : https://prove2.me/submissions/3fc4ec25-5b34-4f8b-a831-0c0da068f5e0

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


open OverflowBinPacking.IID in
theorem solution {n : ℕ} (μ : Fin n → Measure ℝ)
    (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hμ0 : ∀ i, μ i (Set.Iio 0) = 0)
    (C γ : ℝ) (hC : 1 ≤ C) (hγ : 1 ≤ γ)
    (hLight : ∀ i, (μ i).real (Set.Ioi 1) ≤ γ / C) :
    ∀ j : Fin n,
      (Measure.pi μ).real {x | 1 < usage (bgRule μ C γ) x j n} ≤
        γ / C * (Measure.pi μ).real {x | ∃ i : Fin n, bgRule μ C γ i x = j} :=
  OBPX.lemma34 μ hμ hμ0 C γ hC hγ hLight
