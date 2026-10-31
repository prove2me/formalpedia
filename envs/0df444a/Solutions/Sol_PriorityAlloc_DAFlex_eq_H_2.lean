-- Prove2me | solution 1 for PriorityAlloc.DAFlex.eq_H_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T14:20:14.398388+00:00
-- url     : https://prove2.me/submissions/43e15459-7c23-446a-ab80-17044a8a4ea6

import Mathlib
import Definitions.Def_PriorityAlloc_DAFlex_Model

namespace PriorityAlloc.DAFlex

open MeasureTheory Classical

variable {m n : ℕ}

lemma mem_budget_none (z π : Fin n → ℝ) : none ∈ budget z π := by
  simp [budget]

lemma mem_budget_some (z π : Fin n → ℝ) (i : Fin n) : some i ∈ budget z π ↔ z i ≤ π i := by
  simp [budget]

lemma budget_eq_iff (z π : Fin n → ℝ) (T : Finset (Option (Fin n))) :
    budget z π = T ↔ none ∈ T ∧ ∀ i, (z i ≤ π i ↔ some i ∈ T) := by
  constructor
  · rintro rfl
    exact ⟨mem_budget_none z π, fun i => (mem_budget_some z π i).symm⟩
  · rintro ⟨h0, h⟩
    ext o
    cases o with
    | none => simp [mem_budget_none, h0]
    | some i => rw [mem_budget_some, h i]

lemma measurableSet_budget_eq (z : Fin n → ℝ) (T : Finset (Option (Fin n))) :
    MeasurableSet {π : Fin n → ℝ | budget z π = T} := by
  have : {π : Fin n → ℝ | budget z π = T} =
      {_π | none ∈ T} ∩ ⋂ i, {π : Fin n → ℝ | (z i ≤ π i ↔ some i ∈ T)} := by
    ext π; simp [budget_eq_iff]
  rw [this]
  refine (MeasurableSet.const _).inter (MeasurableSet.iInter fun i => ?_)
  by_cases hi : some i ∈ T
  · simp only [hi, iff_true]
    exact measurableSet_le measurable_const (measurable_pi_apply i)
  · simp only [hi, iff_false]
    exact (measurableSet_le measurable_const (measurable_pi_apply i)).compl

lemma measurableSet_choice (j : Option (Fin n)) (T : Finset (Option (Fin n))) :
    MeasurableSet {u : Option (Fin n) → ℝ | j ∈ T ∧ ∀ j' ∈ T, u j' ≤ u j} := by
  have : {u : Option (Fin n) → ℝ | j ∈ T ∧ ∀ j' ∈ T, u j' ≤ u j} =
      {_u | j ∈ T} ∩ ⋂ j' ∈ T, {u : Option (Fin n) → ℝ | u j' ≤ u j} := by
    ext u; simp
  rw [this]
  exact (MeasurableSet.const _).inter (Finset.measurableSet_biInter _ fun j' _ =>
    measurableSet_le (measurable_pi_apply j') (measurable_pi_apply j))

/-- Fibers of the budget map partition any measurable set. -/
lemma sum_fiber_real {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (g : X → Finset (Option (Fin n))) (hg : ∀ T, MeasurableSet {x | g x = T})
    (s : Set X) (hs : MeasurableSet s) :
    ∑ T, (μ (s ∩ {x | g x = T})).toReal = (μ s).toReal := by
  have hU : s = ⋃ T ∈ (Finset.univ : Finset (Finset (Option (Fin n)))), s ∩ {x | g x = T} := by
    ext x; simp
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Finset (Option (Fin n)))))
      (fun T => s ∩ {x | g x = T}) := by
    intro T _ T' _ hTT'
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨_, hx⟩ ⟨_, hx'⟩
    exact hTT' (hx.symm.trans hx')
  conv_rhs => rw [hU, measure_biUnion_finset hdisj (fun T _ => hs.inter (hg T))]
  rw [ENNReal.toReal_sum (fun T _ => measure_ne_top _ _)]

lemma sum_bsProb (G : Fin m → Measure (Fin n → ℝ)) (hG : ∀ t, IsProbabilityMeasure (G t))
    (z : Fin n → ℝ) (t : Fin m) : ∑ T, bsProb G z t T = 1 := by
  have := sum_fiber_real (G t) (budget z) (measurableSet_budget_eq z) Set.univ MeasurableSet.univ
  simpa [bsProb] using this

lemma bsProb_nonneg (G : Fin m → Measure (Fin n → ℝ)) (z : Fin n → ℝ) (t : Fin m)
    (T : Finset (Option (Fin n))) : 0 ≤ bsProb G z t T := ENNReal.toReal_nonneg

lemma bsProb_eq_zero_of_none (G : Fin m → Measure (Fin n → ℝ)) (z : Fin n → ℝ) (t : Fin m)
    (T : Finset (Option (Fin n))) (hT : none ∉ T) : bsProb G z t T = 0 := by
  have : {π : Fin n → ℝ | budget z π = T} = ∅ := by
    ext π; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro rfl; exact hT (mem_budget_none z π)
  simp [bsProb, this]

lemma choiceProb_nonneg (M : Market m n) (t : Fin m) (j : Option (Fin n))
    (S : Finset (Option (Fin n))) : 0 ≤ choiceProb M t j S := ENNReal.toReal_nonneg

/-- Demand decomposition: `D_j(z) = Σ_t λ_t Σ_T P_t(j,T) · P(B_π = T)`. -/
lemma demand_eq_sum (M : Market m n) (hM : M.Standing) (G : Fin m → Measure (Fin n → ℝ))
    (hG : ∀ t, IsProbabilityMeasure (G t)) (z : Fin n → ℝ) (j : Fin n) :
    demand M G z j = ∑ t, M.lam t * ∑ T, choiceProb M t (some j) T * bsProb G z t T := by
  unfold demand
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  have := hM.2.2.1 t
  have := hG t
  set A : Finset (Option (Fin n)) → Set (Option (Fin n) → ℝ) :=
    fun T => {u | some j ∈ T ∧ ∀ j' ∈ T, u j' ≤ u (some j)}
  have hE : {p : (Option (Fin n) → ℝ) × (Fin n → ℝ) |
      some j ∈ budget z p.2 ∧ ∀ j' ∈ budget z p.2, p.1 j' ≤ p.1 (some j)} =
      ⋃ T ∈ (Finset.univ : Finset (Finset (Option (Fin n)))),
        A T ×ˢ {π : Fin n → ℝ | budget z π = T} := by
    ext p; simp [A]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Finset (Option (Fin n)))))
      (fun T => A T ×ˢ {π : Fin n → ℝ | budget z π = T}) := by
    intro T _ T' _ hTT'
    rw [Function.onFun, Set.disjoint_left]
    rintro p ⟨_, hx⟩ ⟨_, hx'⟩
    exact hTT' ((hx : budget z p.2 = T).symm.trans hx')
  rw [hE, measure_biUnion_finset hdisj (fun T _ =>
    (measurableSet_choice (some j) T).prod (measurableSet_budget_eq z T))]
  rw [ENNReal.toReal_sum (fun T _ => measure_ne_top _ _)]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Measure.prod_prod, ENNReal.toReal_mul]
  rfl

lemma measurableSet_injective :
    MeasurableSet {u : Option (Fin n) → ℝ | Function.Injective u} := by
  have : {u : Option (Fin n) → ℝ | Function.Injective u} =
      ⋂ a, ⋂ b, {u : Option (Fin n) → ℝ | u a = u b → a = b} := by
    ext u; simp [Function.Injective]
  rw [this]
  refine MeasurableSet.iInter fun a => MeasurableSet.iInter fun b => ?_
  by_cases hab : a = b
  · simp [hab]
  · have : {u : Option (Fin n) → ℝ | u a = u b → a = b} = {u | u a = u b}ᶜ := by
      ext u; simp [hab]
    rw [this]
    exact (measurableSet_eq_fun (measurable_pi_apply a) (measurable_pi_apply b)).compl

/-- With strict preferences, the choice probabilities from a budget set containing `0` sum
to one. -/
lemma sum_choiceProb (M : Market m n) (hM : M.Standing) (t : Fin m)
    (T : Finset (Option (Fin n))) (hT : none ∈ T) :
    ∑ o, choiceProb M t o T = 1 := by
  have := hM.2.2.1 t
  set F := M.F t
  set I := {u : Option (Fin n) → ℝ | Function.Injective u}
  have hI : F Iᶜ = 0 := by
    have h := hM.2.2.2 t
    rw [ae_iff] at h
    exact h
  set C : Option (Fin n) → Set (Option (Fin n) → ℝ) :=
    fun o => {u | o ∈ T ∧ ∀ j' ∈ T, u j' ≤ u o}
  have hC : ∀ o, choiceProb M t o T = (F (C o ∩ I)).toReal := by
    intro o; rw [measure_inter_conull hI]; rfl
  have hU : I = ⋃ o ∈ (Finset.univ : Finset (Option (Fin n))), C o ∩ I := by
    ext u
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left, Set.mem_inter_iff]
    constructor
    · intro hu
      obtain ⟨o, ho, hmax⟩ := T.exists_max_image u ⟨none, hT⟩
      exact ⟨o, ⟨ho, hmax⟩, hu⟩
    · rintro ⟨_, _, hu⟩; exact hu
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Option (Fin n))))
      (fun o => C o ∩ I) := by
    intro o _ o' _ hoo'
    rw [Function.onFun, Set.disjoint_left]
    rintro u ⟨⟨ho, hmo⟩, hu⟩ ⟨⟨ho', hmo'⟩, _⟩
    exact hoo' (hu (le_antisymm (hmo' o ho) (hmo o' ho')))
  simp_rw [hC]
  rw [← ENNReal.toReal_sum (fun o _ => measure_ne_top _ _),
    ← measure_biUnion_finset hdisj (fun o _ => (measurableSet_choice o T).inter
      measurableSet_injective), ← hU]
  have : F I = 1 := by
    have h1 := measure_inter_conull (s := Set.univ) hI
    rw [Set.univ_inter, measure_univ] at h1; exact h1
  rw [this]; rfl

lemma sum_choiceProb_some (M : Market m n) (hM : M.Standing) (t : Fin m)
    (T : Finset (Option (Fin n))) (hT : none ∈ T) :
    ∑ j : Fin n, choiceProb M t (some j) T = 1 - choiceProb M t none T := by
  have := sum_choiceProb M hM t T hT
  rw [Fintype.sum_option] at this
  linarith

/-- Total demand for real items in terms of the outside-option probabilities. -/
lemma sum_demand (M : Market m n) (hM : M.Standing) (G : Fin m → Measure (Fin n → ℝ))
    (hG : ∀ t, IsProbabilityMeasure (G t)) (z : Fin n → ℝ) :
    ∑ j, demand M G z j =
      ∑ t, M.lam t * ∑ T, bsProb G z t T * (1 - choiceProb M t none T) := by
  simp_rw [demand_eq_sum M hM G hG z]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases hT : none ∈ T
  · rw [← sum_choiceProb_some M hM t T hT, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  · simp [bsProb_eq_zero_of_none G z t T hT]

lemma choiceProb_none_anti (M : Market m n) (hM : M.Standing) (t : Fin m)
    (S S' : Finset (Option (Fin n)))
    (hS : none ∈ S) (h : S ⊆ S') : choiceProb M t none S' ≤ choiceProb M t none S := by
  have := hM.2.2.1 t
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
  rintro u ⟨_, hu⟩
  exact ⟨hS, fun j' hj' => hu j' (h hj')⟩

lemma budget_anti {z Z : Fin n → ℝ} (h : z ≤ Z) (π : Fin n → ℝ) : budget Z π ⊆ budget z π := by
  intro o ho
  cases o with
  | none => exact mem_budget_none z π
  | some i =>
    rw [mem_budget_some] at ho ⊢
    exact (h i).trans ho

/-- The joint law of the budget sets under two cutoff vectors. -/
noncomputable def kap (G : Fin m → Measure (Fin n → ℝ)) (Z z : Fin n → ℝ) (t : Fin m)
    (T T' : Finset (Option (Fin n))) : ℝ :=
  (G t {π | budget Z π = T ∧ budget z π = T'}).toReal

lemma kap_nonneg (G : Fin m → Measure (Fin n → ℝ)) (Z z : Fin n → ℝ) (t : Fin m)
    (T T' : Finset (Option (Fin n))) : 0 ≤ kap G Z z t T T' := ENNReal.toReal_nonneg

lemma kap_sum_right (G : Fin m → Measure (Fin n → ℝ)) (hG : ∀ t, IsProbabilityMeasure (G t))
    (Z z : Fin n → ℝ) (t : Fin m) (T : Finset (Option (Fin n))) :
    ∑ T', kap G Z z t T T' = bsProb G Z t T :=
  sum_fiber_real (G t) (budget z) (measurableSet_budget_eq z) _ (measurableSet_budget_eq Z T)

lemma kap_sum_left (G : Fin m → Measure (Fin n → ℝ)) (hG : ∀ t, IsProbabilityMeasure (G t))
    (Z z : Fin n → ℝ) (t : Fin m) (T' : Finset (Option (Fin n))) :
    ∑ T, kap G Z z t T T' = bsProb G z t T' := by
  have := sum_fiber_real (G t) (budget Z) (measurableSet_budget_eq Z) _
    (measurableSet_budget_eq z T')
  unfold bsProb
  rw [← this]
  refine Finset.sum_congr rfl fun T _ => ?_
  unfold kap
  congr 2
  ext π; simp [and_comm]

lemma kap_pos (G : Fin m → Measure (Fin n → ℝ)) (Z z : Fin n → ℝ) (t : Fin m)
    (T T' : Finset (Option (Fin n))) (h : 0 < kap G Z z t T T') :
    ∃ π, budget Z π = T ∧ budget z π = T' := by
  by_contra hne
  push_neg at hne
  have : {π | budget Z π = T ∧ budget z π = T'} = (∅ : Set (Fin n → ℝ)) := by
    ext π; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    exact hne π
  simp [kap, this] at h

lemma core_identity (M : Market m n) (hM : M.Standing) (G : Fin m → Measure (Fin n → ℝ))
    (hG : ∀ t, IsProbabilityMeasure (G t)) (z Z : Fin n → ℝ) :
    ∑ j, demand M G z j - ∑ j, demand M G Z j =
      ∑ t, M.lam t * ∑ T, ∑ T', kap G Z z t T T' *
        (choiceProb M t none T - choiceProb M t none T') := by
  rw [sum_demand M hM G hG z, sum_demand M hM G hG Z, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← mul_sub]
  congr 1
  have h1 : ∑ T, bsProb G z t T * (1 - choiceProb M t none T) =
      ∑ T, ∑ T', kap G Z z t T T' * (1 - choiceProb M t none T') := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun T' _ => ?_
    rw [← kap_sum_left G hG Z z t T', Finset.sum_mul]
  have h2 : ∑ T, bsProb G Z t T * (1 - choiceProb M t none T) =
      ∑ T, ∑ T', kap G Z z t T T' * (1 - choiceProb M t none T) := by
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [← kap_sum_right G hG Z z t T, Finset.sum_mul]
  rw [h1, h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun T' _ => by ring

lemma core_term_nonneg (M : Market m n) (hM : M.Standing) (G : Fin m → Measure (Fin n → ℝ))
    (z Z : Fin n → ℝ) (hzZ : z ≤ Z) (t : Fin m) (T T' : Finset (Option (Fin n))) :
    0 ≤ kap G Z z t T T' * (choiceProb M t none T - choiceProb M t none T') := by
  rcases (kap_nonneg G Z z t T T').eq_or_lt with h | h
  · rw [← h, zero_mul]
  · obtain ⟨π, rfl, rfl⟩ := kap_pos G Z z t T T' h
    refine mul_nonneg h.le (sub_nonneg.mpr ?_)
    exact choiceProb_none_anti M hM t _ _ (mem_budget_none Z π) (budget_anti hzZ π)

lemma core_le (M : Market m n) (hM : M.Standing) (G : Fin m → Measure (Fin n → ℝ))
    (hG : ∀ t, IsProbabilityMeasure (G t)) (z Z : Fin n → ℝ) (hzZ : z ≤ Z) :
    ∑ j, demand M G Z j ≤ ∑ j, demand M G z j := by
  have := core_identity M hM G hG z Z
  have h0 : 0 ≤ ∑ t, M.lam t * ∑ T, ∑ T', kap G Z z t T T' *
        (choiceProb M t none T - choiceProb M t none T') :=
    Finset.sum_nonneg fun t _ => mul_nonneg (hM.1 t).le (Finset.sum_nonneg fun T _ =>
      Finset.sum_nonneg fun T' _ => core_term_nonneg M hM G z Z hzZ t T T')
  linarith

lemma core_eq (M : Market m n) (hM : M.Standing) (hreg : Regular M)
    (G : Fin m → Measure (Fin n → ℝ))
    (hG : ∀ t, IsProbabilityMeasure (G t)) (z Z : Fin n → ℝ) (hzZ : z ≤ Z)
    (hle : ∑ j, demand M G z j ≤ ∑ j, demand M G Z j) :
    ∀ t T, bsProb G z t T = bsProb G Z t T := by
  have hid := core_identity M hM G hG z Z
  have hterm := core_term_nonneg M hM G z Z hzZ
  have hX : ∀ t, 0 ≤ ∑ T, ∑ T', kap G Z z t T T' *
        (choiceProb M t none T - choiceProb M t none T') := fun t =>
    Finset.sum_nonneg fun T _ => Finset.sum_nonneg fun T' _ => hterm t T T'
  have hsum0 : ∑ t, M.lam t * ∑ T, ∑ T', kap G Z z t T T' *
        (choiceProb M t none T - choiceProb M t none T') = 0 :=
    le_antisymm (by linarith) (Finset.sum_nonneg fun t _ => mul_nonneg (hM.1 t).le (hX t))
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun t _ => mul_nonneg (hM.1 t).le (hX t))] at hsum0
  have hoff : ∀ t T T', T ≠ T' → kap G Z z t T T' = 0 := by
    intro t T T' hTT'
    have ht := hsum0 t (Finset.mem_univ _)
    rw [mul_eq_zero] at ht
    rcases ht with ht | ht
    · exact absurd ht (hM.1 t).ne'
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun T _ => Finset.sum_nonneg fun T' _ =>
      hterm t T T')] at ht
    have ht2 := ht T (Finset.mem_univ _)
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun T' _ => hterm t T T')] at ht2
    have ht3 := ht2 T' (Finset.mem_univ _)
    by_contra hk
    have hkpos : 0 < kap G Z z t T T' := lt_of_le_of_ne (kap_nonneg _ _ _ _ _ _) (Ne.symm hk)
    obtain ⟨π, hT, hT'⟩ := kap_pos G Z z t T T' hkpos
    have hsub : T ⊂ T' := by
      rw [← hT, ← hT']
      refine Finset.ssubset_iff_subset_ne.mpr ⟨budget_anti hzZ π, ?_⟩
      rw [hT, hT']; exact hTT'
    have hlt := hreg t T T' (hT ▸ mem_budget_none Z π) hsub
    have : 0 < kap G Z z t T T' * (choiceProb M t none T - choiceProb M t none T') :=
      mul_pos hkpos (by linarith)
    linarith
  intro t T
  rw [← kap_sum_left G hG Z z t T, ← kap_sum_right G hG Z z t T,
    Finset.sum_eq_single T (fun T'' _ h => hoff t T'' T h) (by simp),
    Finset.sum_eq_single T (fun T'' _ h => hoff t T T'' (Ne.symm h)) (by simp)]

lemma demand_mono_gen (M : Market m n) (hM : M.Standing) (G : Fin m → Measure (Fin n → ℝ))
    (hG : ∀ t, IsProbabilityMeasure (G t)) (z z' : Fin n → ℝ) (j : Fin n)
    (h1 : ∀ π, some j ∈ budget z π → some j ∈ budget z' π)
    (h2 : ∀ π, some j ∈ budget z π → budget z' π ⊆ budget z π) :
    demand M G z j ≤ demand M G z' j := by
  unfold demand
  refine Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left ?_ (hM.1 t).le
  have := hM.2.2.1 t
  have := hG t
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
  rintro p ⟨hj, hmax⟩
  exact ⟨h1 _ hj, fun j' hj' => hmax j' (h2 _ hj hj')⟩

lemma budget_update_eq (z π : Fin n → ℝ) (j : Fin n) (s : ℝ) (hs : z j ≤ s)
    (hN : ¬ (z j ≤ π j ∧ π j < s)) : budget (Function.update z j s) π = budget z π := by
  ext o
  cases o with
  | none => simp [mem_budget_none]
  | some i =>
    rw [mem_budget_some, mem_budget_some]
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self]
      constructor
      · intro h; linarith
      · intro h; by_contra h'; exact hN ⟨h, lt_of_not_ge h'⟩
    · rw [Function.update_of_ne hij]

lemma demand_bound (M : Market m n) (hM : M.Standing) (G : Fin m → Measure (Fin n → ℝ))
    (hG : ∀ t, IsProbabilityMeasure (G t)) (z : Fin n → ℝ) (j : Fin n) (s : ℝ)
    (hs : z j ≤ s) :
    demand M G z j ≤ demand M G (Function.update z j s) j +
      ∑ t, M.lam t * (G t {π | z j ≤ π j ∧ π j < s}).toReal := by
  unfold demand
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun t _ => ?_
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (hM.1 t).le
  have := hM.2.2.1 t
  have := hG t
  set N := {π : Fin n → ℝ | z j ≤ π j ∧ π j < s}
  have hsub : {p : (Option (Fin n) → ℝ) × (Fin n → ℝ) |
      some j ∈ budget z p.2 ∧ ∀ j' ∈ budget z p.2, p.1 j' ≤ p.1 (some j)} ⊆
      {p : (Option (Fin n) → ℝ) × (Fin n → ℝ) |
      some j ∈ budget (Function.update z j s) p.2 ∧
        ∀ j' ∈ budget (Function.update z j s) p.2, p.1 j' ≤ p.1 (some j)} ∪
      (Set.univ ×ˢ N) := by
    rintro p hp
    by_cases hN : p.2 ∈ N
    · exact Or.inr ⟨Set.mem_univ _, hN⟩
    · left
      rw [Set.mem_ofPred_eq, budget_update_eq z p.2 j s hs hN]
      exact hp
  have h := (measure_mono (μ := (M.F t).prod (G t)) hsub).trans (measure_union_le _ _)
  rw [Measure.prod_prod, measure_univ, one_mul] at h
  rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) h

/-- At a fixed point of the DA operator, an item whose cutoff is below the top of the box has
demand at most its quota, provided the priority marginals have no atoms (Lipschitz bound). -/
lemma fixed_respects (M : Market m n) (hM : M.Standing) (G : Fin m → Measure (Fin n → ℝ))
    (hG : ∀ t, IsProbabilityMeasure (G t))
    (hLip : ∀ t j (a w : ℝ), a ≤ w → (G t {π | a ≤ π j ∧ π j < w}).toReal ≤ w - a)
    (q : Fin n → ℝ) (B : ℝ) (z : Fin n → ℝ) (hfix : DAop M G q B z = z) (j : Fin n)
    (hzB : z j < B) : demand M G z j ≤ q j := by
  by_contra hcon
  push_neg at hcon
  set C := ∑ t, M.lam t with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun t _ => (hM.1 t).le
  set ε := min ((demand M G z j - q j) / (C + 1)) (B - z j) with hε
  have hεpos : 0 < ε := lt_min (div_pos (by linarith) (by linarith)) (by linarith)
  have hε1 : (C + 1) * ε ≤ demand M G z j - q j := by
    have := min_le_left ((demand M G z j - q j) / (C + 1)) (B - z j)
    rw [le_div_iff₀ (by linarith)] at this
    linarith
  have hε2 : ε ≤ B - z j := min_le_right _ _
  have hinf := congrFun hfix j
  unfold DAop at hinf
  set Sset := {w | z j ≤ w ∧ w ≤ B ∧ demand M G (Function.update z j w) j ≤ q j} ∪ {B}
  have hlt : sInf Sset < z j + ε := by rw [hinf]; linarith
  obtain ⟨s, hsS, hslt⟩ := exists_lt_of_csInf_lt ⟨B, Or.inr rfl⟩ hlt
  rcases hsS with ⟨hs1, _, hs3⟩ | hsB
  · have hb := demand_bound M hM G hG z j s hs1
    have hsum : ∑ t, M.lam t * (G t {π | z j ≤ π j ∧ π j < s}).toReal ≤ C * (s - z j) := by
      rw [hC, Finset.sum_mul]
      exact Finset.sum_le_sum fun t _ =>
        mul_le_mul_of_nonneg_left (hLip t j _ _ hs1) (hM.1 t).le
    have : C * (s - z j) ≤ C * ε := mul_le_mul_of_nonneg_left (by linarith) hC0
    nlinarith
  · rw [Set.mem_singleton_iff] at hsB
    linarith

lemma daop_le (M : Market m n) (G : Fin m → Measure (Fin n → ℝ)) (q : Fin n → ℝ) (B : ℝ)
    (z : Fin n → ℝ) (j : Fin n) : DAop M G q B z j ≤ B := by
  refine csInf_le ⟨min (z j) B, ?_⟩ (Or.inr rfl)
  rintro x (⟨hx, _⟩ | hx)
  · exact (min_le_left _ _).trans hx
  · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact min_le_right _ _

lemma daop_ge (M : Market m n) (G : Fin m → Measure (Fin n → ℝ)) (q : Fin n → ℝ) (B : ℝ)
    (z : Fin n → ℝ) (j : Fin n) (hzB : z j ≤ B) : z j ≤ DAop M G q B z j := by
  refine le_csInf ⟨B, Or.inr rfl⟩ ?_
  rintro x (⟨hx, _⟩ | hx)
  · exact hx
  · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hzB

lemma daop_mono (M : Market m n) (hM : M.Standing) (G : Fin m → Measure (Fin n → ℝ))
    (hG : ∀ t, IsProbabilityMeasure (G t)) (q : Fin n → ℝ) (B : ℝ)
    (z z' : Fin n → ℝ) (hzz : z ≤ z') : DAop M G q B z ≤ DAop M G q B z' := by
  intro j
  refine csInf_le_csInf ⟨min (z j) B, ?_⟩ ⟨B, Or.inr rfl⟩ ?_
  · rintro x (⟨hx, _⟩ | hx)
    · exact (min_le_left _ _).trans hx
    · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact min_le_right _ _
  · rintro w (⟨hw1, hw2, hw3⟩ | hw)
    · refine Or.inl ⟨(hzz j).trans hw1, hw2, le_trans ?_ hw3⟩
      refine demand_mono_gen M hM G hG _ _ j ?_ ?_
      · intro π h; rw [mem_budget_some] at h ⊢; simpa using h
      · intro π _
        refine budget_anti ?_ π
        intro i
        by_cases hij : i = j
        · subst hij; simp
        · rw [Function.update_of_ne hij, Function.update_of_ne hij]; exact hzz i
    · exact Or.inr hw

lemma daop_fixed (M : Market m n) (G : Fin m → Measure (Fin n → ℝ)) (q : Fin n → ℝ) (B : ℝ)
    (Z : Fin n → ℝ) (hZB : ∀ j, Z j ≤ B) (hD : ∀ j, demand M G Z j ≤ q j) :
    DAop M G q B Z = Z := by
  funext j
  refine le_antisymm ?_ (daop_ge M G q B Z j (hZB j))
  refine csInf_le ⟨min (Z j) B, ?_⟩ (Or.inl ⟨le_rfl, hZB j, by simpa using hD j⟩)
  rintro x (⟨hx, _⟩ | hx)
  · exact (min_le_left _ _).trans hx
  · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact min_le_right _ _

lemma box_eq_Icc (B : ℝ) : (box B : Set (Fin n → ℝ)) = Set.Icc 0 (fun _ => B) := by
  ext π; simp [box, Set.mem_pi, Pi.le_def, forall_and]

lemma daop_mem_box (M : Market m n) (G : Fin m → Measure (Fin n → ℝ)) (q : Fin n → ℝ) (B : ℝ)
    (hB : 0 < B) (z : Fin n → ℝ) (hz : z ∈ box B) : DAop M G q B z ∈ box B := by
  rw [box_eq_Icc] at hz ⊢
  refine ⟨fun j => ?_, fun j => daop_le M G q B z j⟩
  exact (hz.1 j).trans (daop_ge M G q B z j (hz.2 j))

lemma cutoff_exists (M : Market m n) (hM : M.Standing) (G : Fin m → Measure (Fin n → ℝ))
    (hG : ∀ t, IsProbabilityMeasure (G t)) (q : Fin n → ℝ) (B : ℝ) (hB : 0 < B) :
    ∃ z, IsDACutoff M G q B z := by
  have hfact : Fact ((0 : Fin n → ℝ) ≤ fun _ => B) := ⟨fun _ => hB.le⟩
  let f : Set.Icc (0 : Fin n → ℝ) (fun _ => B) →o Set.Icc (0 : Fin n → ℝ) (fun _ => B) :=
    { toFun := fun x => ⟨DAop M G q B x.1, by
        have h := daop_mem_box M G q B hB x.1 (by rw [box_eq_Icc]; exact x.2)
        rw [box_eq_Icc] at h; exact h⟩
      monotone' := fun x y hxy => daop_mono M hM G hG q B x.1 y.1 hxy }
  refine ⟨(OrderHom.lfp f).1, ⟨?_, ?_⟩, ?_⟩
  · rw [box_eq_Icc]; exact (OrderHom.lfp f).2
  · exact congrArg Subtype.val (OrderHom.map_lfp f)
  · rintro z' ⟨hz'box, hz'fix⟩
    rw [box_eq_Icc] at hz'box
    have := OrderHom.lfp_le_fixed f (a := ⟨z', hz'box⟩) (Subtype.ext hz'fix)
    exact this

/-- The law of `π = c + δ·𝟏` with `δ ∼ Uniform(0,1)`. -/
noncomputable def shiftLaw (c : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).map (fun δ => fun j => c j + δ)

lemma measurable_shift (c : Fin n → ℝ) : Measurable (fun δ : ℝ => fun j => c j + δ) :=
  measurable_pi_lambda _ fun _ => measurable_const.add measurable_id

lemma shift_apply (c : Fin n → ℝ) (A : Set (Fin n → ℝ)) (hA : MeasurableSet A) :
    shiftLaw c A = volume ((fun δ : ℝ => fun j => c j + δ) ⁻¹' A ∩ Set.Icc 0 1) := by
  unfold shiftLaw
  rw [Measure.map_apply (measurable_shift c) hA,
    Measure.restrict_apply (hA.preimage (measurable_shift c))]

lemma shift_prob (c : Fin n → ℝ) : IsProbabilityMeasure (shiftLaw c) :=
  ⟨by rw [shift_apply c _ MeasurableSet.univ]; simp [Real.volume_Icc]⟩

lemma shift_lip (c : Fin n → ℝ) (j : Fin n) (a w : ℝ) :
    shiftLaw c {π | a ≤ π j ∧ π j < w} ≤ ENNReal.ofReal (w - a) := by
  have hA : MeasurableSet {π : Fin n → ℝ | a ≤ π j ∧ π j < w} := by
    rw [Set.setOf_and]
    exact (measurableSet_le measurable_const (measurable_pi_apply j)).inter
      (measurableSet_lt (measurable_pi_apply j) measurable_const)
  rw [shift_apply c _ hA]
  refine (measure_mono Set.inter_subset_left).trans ?_
  have : (fun δ : ℝ => fun j => c j + δ) ⁻¹' {π | a ≤ π j ∧ π j < w} =
      Set.Ico (a - c j) (w - c j) := by
    ext δ; simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Ico]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [this, Real.volume_Ico]
  apply le_of_eq; congr 1; ring

lemma shift_box (c : Fin n → ℝ) (B : ℝ) (hc : ∀ j, 0 ≤ c j ∧ c j + 1 ≤ B) :
    shiftLaw c (box B)ᶜ = 0 := by
  have hbox : MeasurableSet (box B : Set (Fin n → ℝ)) :=
    MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Icc
  rw [shift_apply c _ hbox.compl]
  convert measure_empty (μ := (volume : Measure ℝ))
  ext δ
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_Icc,
    Set.mem_empty_iff_false, iff_false, not_and, and_imp]
  intro h0 h1 hn
  apply h0
  simp only [box, Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const]
  intro j
  constructor <;> linarith [(hc j).1, (hc j).2]

lemma budget_mono_pi (z : Fin n → ℝ) {π π' : Fin n → ℝ} (h : ∀ i, π i ≤ π' i) :
    budget z π ⊆ budget z π' := by
  intro o ho
  cases o with
  | none => exact mem_budget_none z π'
  | some i => rw [mem_budget_some] at ho ⊢; exact ho.trans (h i)

lemma eq_of_le_sum {ι : Type*} [Fintype ι] (b y : ι → ℝ) (hb : ∑ i, b i = 1)
    (hy : ∑ i, y i = 1) (h : ∀ i, y i ≤ b i) : ∀ i, b i = y i := by
  have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun i _ => h i)).mp (by rw [hb, hy])
  exact fun i => (this i (Finset.mem_univ _)).symm

/-! ### The law (H.1) -/

lemma h1Law_eq (y : Fin m → Finset (Option (Fin n)) → ℝ) (t : Fin m) :
    h1Law y t = ∑ S, ENNReal.ofReal (y t S) •
      shiftLaw (fun j => if some j ∈ S then (1 : ℝ) else 0) := rfl

lemma h1Law_apply (y : Fin m → Finset (Option (Fin n)) → ℝ) (t : Fin m)
    (A : Set (Fin n → ℝ)) : h1Law y t A = ∑ S, ENNReal.ofReal (y t S) *
      shiftLaw (fun j => if some j ∈ S then (1 : ℝ) else 0) A := by
  rw [h1Law_eq, Measure.coe_finset_sum, Finset.sum_apply]
  rfl

lemma ofReal_sum_y (M : Market m n) (y : Fin m → Finset (Option (Fin n)) → ℝ) (hy : Ymem M y)
    (t : Fin m) : ∑ S, ENNReal.ofReal (y t S) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun S _ => hy.1 t S), hy.2.2.1 t, ENNReal.ofReal_one]

lemma h1_prob (M : Market m n) (y : Fin m → Finset (Option (Fin n)) → ℝ) (hy : Ymem M y)
    (t : Fin m) : IsProbabilityMeasure (h1Law y t) := by
  constructor
  rw [h1Law_apply]
  have : ∀ S : Finset (Option (Fin n)),
      shiftLaw (fun j => if some j ∈ S then (1 : ℝ) else 0) Set.univ = 1 := fun S =>
    (shift_prob _).measure_univ
  simp_rw [this, mul_one]
  exact ofReal_sum_y M y hy t

lemma h1_lip (M : Market m n) (y : Fin m → Finset (Option (Fin n)) → ℝ) (hy : Ymem M y)
    (t : Fin m) (j : Fin n) (a w : ℝ) (haw : a ≤ w) :
    (h1Law y t {π | a ≤ π j ∧ π j < w}).toReal ≤ w - a := by
  refine ENNReal.toReal_le_of_le_ofReal (by linarith) ?_
  rw [h1Law_apply]
  calc ∑ S, ENNReal.ofReal (y t S) *
        shiftLaw (fun j => if some j ∈ S then (1 : ℝ) else 0) {π | a ≤ π j ∧ π j < w}
      ≤ ∑ S, ENNReal.ofReal (y t S) * ENNReal.ofReal (w - a) :=
        Finset.sum_le_sum fun S _ => mul_le_mul_right (shift_lip _ j a w) _
    _ = ENNReal.ofReal (w - a) := by rw [← Finset.sum_mul, ofReal_sum_y M y hy t, one_mul]

lemma h1_box (M : Market m n) (y : Fin m → Finset (Option (Fin n)) → ℝ) (t : Fin m) :
    ∀ᵐ π ∂(h1Law y t), π ∈ box 2 := by
  rw [ae_iff]
  change h1Law y t (box 2)ᶜ = 0
  rw [h1Law_apply]
  refine Finset.sum_eq_zero fun S _ => ?_
  rw [shift_box _ 2 (fun j => by split_ifs <;> norm_num), mul_zero]

lemma budget_one_ind (T : Finset (Option (Fin n))) (hT : none ∈ T) (δ : ℝ) (h0 : 0 ≤ δ)
    (h1 : δ < 1) : budget 1 (fun j => (if some j ∈ T then (1 : ℝ) else 0) + δ) = T := by
  rw [budget_eq_iff]
  refine ⟨hT, fun i => ?_⟩
  simp only [Pi.one_apply]
  by_cases hi : some i ∈ T
  · simp only [hi, if_true, iff_true]; linarith
  · simp only [hi, if_false, iff_false, not_le]; linarith

lemma h1_bs_one (M : Market m n) (y : Fin m → Finset (Option (Fin n)) → ℝ) (hy : Ymem M y) :
    ∀ t T, bsProb (h1Law y) 1 t T = y t T := by
  intro t
  have hG : ∀ t, IsProbabilityMeasure (h1Law y t) := h1_prob M y hy
  refine eq_of_le_sum _ _ (sum_bsProb _ hG 1 t) (hy.2.2.1 t) fun T => ?_
  by_cases hT : none ∈ T
  · unfold bsProb
    refine (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp ?_
    rw [h1Law_apply]
    refine le_trans ?_ (Finset.single_le_sum (fun S _ => zero_le) (Finset.mem_univ T))
    have : shiftLaw (fun j => if some j ∈ T then (1 : ℝ) else 0) {π | budget 1 π = T} = 1 := by
      have := shift_prob (fun j => if some j ∈ T then (1 : ℝ) else 0)
      refine le_antisymm prob_le_one ?_
      rw [shift_apply _ _ (measurableSet_budget_eq 1 T)]
      calc (1 : ENNReal) = volume (Set.Ico (0 : ℝ) 1) := by simp [Real.volume_Ico]
        _ ≤ _ := by
          refine measure_mono ?_
          intro δ hδ
          exact ⟨budget_one_ind T hT δ hδ.1 hδ.2, hδ.1, hδ.2.le⟩
    rw [this, mul_one]
  · rw [hy.2.2.2 t T hT]; exact bsProb_nonneg _ _ _ _

/-! ### The DA-STB law -/

lemma stbLaw_eq (b : Fin m → Fin n → ℝ) (t : Fin m) : stbLaw b t = shiftLaw (b t) := rfl

lemma stb_prob (b : Fin m → Fin n → ℝ) (t : Fin m) : IsProbabilityMeasure (stbLaw b t) :=
  shift_prob (b t)

lemma stb_lip (b : Fin m → Fin n → ℝ) (t : Fin m) (j : Fin n) (a w : ℝ) (haw : a ≤ w) :
    (stbLaw b t {π | a ≤ π j ∧ π j < w}).toReal ≤ w - a :=
  ENNReal.toReal_le_of_le_ofReal (by linarith) (shift_lip (b t) j a w)

lemma stb_pos (b : Fin m → Fin n → ℝ) (z : Fin n → ℝ) (t : Fin m)
    (S : Finset (Option (Fin n))) (h : 0 < bsProb (stbLaw b) z t S) :
    ∃ δ : ℝ, budget z (fun j => b t j + δ) = S := by
  by_contra hne
  push_neg at hne
  unfold bsProb at h
  rw [stbLaw_eq, shift_apply _ _ (measurableSet_budget_eq z S)] at h
  have : (fun δ : ℝ => fun j => b t j + δ) ⁻¹' {π | budget z π = S} ∩ Set.Icc 0 1 = ∅ := by
    ext δ; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro h'; exact absurd h' (hne δ)
  rw [this] at h; simp at h

lemma stb_nested (b : Fin m → Fin n → ℝ) (z : Fin n → ℝ) :
    NestedWithinSegment (bsProb (stbLaw b) z) := by
  intro t S S' hS hS'
  obtain ⟨δ, rfl⟩ := stb_pos b z t S hS
  obtain ⟨δ', rfl⟩ := stb_pos b z t S' hS'
  rcases le_total δ δ' with h | h
  · exact Or.inl (budget_mono_pi z fun i => by linarith)
  · exact Or.inr (budget_mono_pi z fun i => by linarith)

lemma stbBoost_eq (y : Fin m → Finset (Option (Fin n)) → ℝ) (t : Fin m) (j : Fin n) :
    stbBoost y t j = ∑ S, if some j ∈ S then y t S else 0 := by
  unfold stbBoost; rw [Finset.sum_filter]

lemma stbBoost_bounds (M : Market m n) (y : Fin m → Finset (Option (Fin n)) → ℝ)
    (hy : Ymem M y) (t : Fin m) (j : Fin n) : 0 ≤ stbBoost y t j ∧ stbBoost y t j + 1 ≤ 2 := by
  rw [stbBoost_eq]
  constructor
  · exact Finset.sum_nonneg fun S _ => by split_ifs; exacts [hy.1 t S, le_rfl]
  · have : ∑ S, (if some j ∈ S then y t S else 0) ≤ ∑ S, y t S :=
      Finset.sum_le_sum fun S _ => by split_ifs; exacts [le_rfl, hy.1 t S]
    rw [hy.2.2.1 t] at this; linarith

lemma stb_bs_one (M : Market m n) (y : Fin m → Finset (Option (Fin n)) → ℝ) (hy : Ymem M y)
    (hnest : NestedWithinSegment y) :
    ∀ t T, bsProb (stbLaw (stbBoost y)) 1 t T = y t T := by
  intro t
  have hG : ∀ t, IsProbabilityMeasure (stbLaw (stbBoost y) t) := stb_prob _
  refine eq_of_le_sum _ _ (sum_bsProb _ hG 1 t) (hy.2.2.1 t) fun T => ?_
  rcases (hy.1 t T).eq_or_lt with h0 | hpos
  · rw [← h0]; exact bsProb_nonneg _ _ _ _
  have hT : none ∈ T := by
    by_contra hT; rw [hy.2.2.2 t T hT] at hpos; exact lt_irrefl _ hpos
  set a := ∑ S, if S ⊂ T then y t S else 0 with ha
  have hyT : y t T = ∑ S, if S = T then y t S else 0 := by
    rw [Finset.sum_ite_eq' Finset.univ T]; simp
  have ha0 : 0 ≤ a := Finset.sum_nonneg fun S _ => by split_ifs; exacts [hy.1 t S, le_rfl]
  have ha1 : a + y t T ≤ 1 := by
    rw [ha, hyT, ← Finset.sum_add_distrib, ← hy.2.2.1 t]
    refine Finset.sum_le_sum fun S _ => ?_
    by_cases h1 : S ⊂ T
    · have : S ≠ T := h1.ne
      simp [h1, this]
    · split_ifs <;> simp [hy.1 t S]
  -- items of `T` are in the budget, others are not, for `δ ∈ [a, a + y_T)`
  have hin : ∀ i, some i ∈ T → 1 ≤ stbBoost y t i + a := by
    intro i hi
    rw [stbBoost_eq, ha, ← Finset.sum_add_distrib, ← hy.2.2.1 t]
    refine Finset.sum_le_sum fun S _ => ?_
    by_cases hiS : some i ∈ S
    · simp only [hiS, if_true]; split_ifs <;> linarith [hy.1 t S]
    · simp only [hiS, if_false, zero_add]
      by_cases hST : S ⊂ T
      · simp [hST]
      · simp only [hST, if_false]
        refine le_of_not_gt fun hSpos => ?_
        rcases hnest t S T hSpos hpos with h | h
        · have : S = T := by
            by_contra hne; exact hST (Finset.ssubset_iff_subset_ne.mpr ⟨h, hne⟩)
          rw [this] at hiS; exact hiS hi
        · exact hiS (h hi)
  have hout : ∀ i, some i ∉ T → stbBoost y t i + a + y t T ≤ 1 := by
    intro i hi
    rw [stbBoost_eq, ha, hyT, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← hy.2.2.1 t]
    refine Finset.sum_le_sum fun S _ => ?_
    by_cases hiS : some i ∈ S
    · have h1 : ¬ S ⊂ T := fun h => hi (h.subset hiS)
      have h2 : S ≠ T := fun h => hi (h ▸ hiS)
      simp [hiS, h1, h2]
    · by_cases h1 : S ⊂ T
      · have : S ≠ T := h1.ne
        simp [hiS, h1, this]
      · split_ifs <;> simp [hy.1 t S]
  unfold bsProb
  refine (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp ?_
  rw [stbLaw_eq, shift_apply _ _ (measurableSet_budget_eq 1 T)]
  calc ENNReal.ofReal (y t T) = volume (Set.Ico a (a + y t T)) := by
        rw [Real.volume_Ico]; congr 1; ring
    _ ≤ _ := by
      refine measure_mono fun δ hδ => ⟨?_, by linarith [hδ.1], by linarith [hδ.2]⟩
      simp only [Set.mem_preimage, Set.mem_ofPred_eq]
      rw [budget_eq_iff]
      refine ⟨hT, fun i => ?_⟩
      simp only [Pi.one_apply]
      by_cases hi : some i ∈ T
      · simp only [hi, iff_true]; linarith [hin i hi, hδ.1]
      · simp only [hi, iff_false, not_le]; linarith [hout i hi, hδ.2]

/-! ### Generic implementation argument (proof of Propositions H.1 / H.3) -/

lemma demand_one_eq (M : Market m n) (hM : M.Standing) (G : Fin m → Measure (Fin n → ℝ))
    (hG : ∀ t, IsProbabilityMeasure (G t)) (y : Fin m → Finset (Option (Fin n)) → ℝ)
    (hbs : ∀ t T, bsProb G 1 t T = y t T) : ∀ j, demand M G 1 j = lhs11 M y j := by
  intro j
  rw [demand_eq_sum M hM G hG, lhs11]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [hbs]; ring

lemma one_mem_box2 : (1 : Fin n → ℝ) ∈ box 2 := by
  simp only [box, Set.mem_pi, Set.mem_univ, Set.mem_Icc, Pi.one_apply, forall_const]
  norm_num

lemma one_fixed (M : Market m n) (hM : M.Standing) (G : Fin m → Measure (Fin n → ℝ))
    (hG : ∀ t, IsProbabilityMeasure (G t)) (y : Fin m → Finset (Option (Fin n)) → ℝ)
    (hbs : ∀ t T, bsProb G 1 t T = y t T) : DAop M G (lhs11 M y) 2 1 = 1 :=
  daop_fixed M G _ 2 1 (fun _ => by norm_num)
    (fun j => (demand_one_eq M hM G hG y hbs j).le)

lemma cutoff_le_one (M : Market m n) (hM : M.Standing) (G : Fin m → Measure (Fin n → ℝ))
    (hG : ∀ t, IsProbabilityMeasure (G t)) (y : Fin m → Finset (Option (Fin n)) → ℝ)
    (hbs : ∀ t T, bsProb G 1 t T = y t T) (z : Fin n → ℝ)
    (hz : IsDACutoff M G (lhs11 M y) 2 z) : z ≤ 1 :=
  hz.2 ⟨one_mem_box2, one_fixed M hM G hG y hbs⟩

lemma cutoff_respects (M : Market m n) (hM : M.Standing) (G : Fin m → Measure (Fin n → ℝ))
    (hG : ∀ t, IsProbabilityMeasure (G t))
    (hLip : ∀ t j (a w : ℝ), a ≤ w → (G t {π | a ≤ π j ∧ π j < w}).toReal ≤ w - a)
    (y : Fin m → Finset (Option (Fin n)) → ℝ)
    (hbs : ∀ t T, bsProb G 1 t T = y t T) (z : Fin n → ℝ)
    (hz : IsDACutoff M G (lhs11 M y) 2 z) : ∀ j, demand M G z j ≤ lhs11 M y j := by
  intro j
  have h1 := cutoff_le_one M hM G hG y hbs z hz j
  exact fixed_respects M hM G hG hLip _ 2 z hz.1.2 j (by simp at h1; linarith)

lemma implement (M : Market m n) (hM : M.Standing) (hreg : Regular M)
    (G : Fin m → Measure (Fin n → ℝ)) (hG : ∀ t, IsProbabilityMeasure (G t))
    (hLip : ∀ t j (a w : ℝ), a ≤ w → (G t {π | a ≤ π j ∧ π j < w}).toReal ≤ w - a)
    (y : Fin m → Finset (Option (Fin n)) → ℝ)
    (hbs : ∀ t T, bsProb G 1 t T = y t T) :
    ∃ z, IsDACutoff M G (lhs11 M y) 2 z ∧ ∀ t S, bsProb G z t S = y t S := by
  obtain ⟨z, hz⟩ := cutoff_exists M hM G hG (lhs11 M y) 2 (by norm_num)
  refine ⟨z, hz, fun t S => ?_⟩
  have hle : ∑ j, demand M G z j ≤ ∑ j, demand M G 1 j := by
    rw [Finset.sum_congr rfl fun j _ => demand_one_eq M hM G hG y hbs j]
    exact Finset.sum_le_sum fun j _ => cutoff_respects M hM G hG hLip y hbs z hz j
  rw [core_eq M hM hreg G hG z 1 (cutoff_le_one M hM G hG y hbs z hz) hle t S, hbs]

lemma lhs11_nonneg (M : Market m n) (hM : M.Standing) (y : Fin m → Finset (Option (Fin n)) → ℝ)
    (hy : Ymem M y) (j : Fin n) : 0 ≤ lhs11 M y j :=
  Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun S _ =>
    mul_nonneg (mul_nonneg (hM.1 t).le (choiceProb_nonneg _ _ _ _)) (hy.1 t S)

/-! ### Milestones -/

theorem ms_demand_monotone (M : Market m n) (hM : M.Standing) (G : Fin m → Measure (Fin n → ℝ))
    (hG : ∀ t, IsProbabilityMeasure (G t)) :
    (∀ (z : Fin n → ℝ) (j : Fin n) (w w' : ℝ), w ≤ w' →
        demand M G (Function.update z j w') j ≤ demand M G (Function.update z j w) j) ∧
      (∀ (z : Fin n → ℝ) (j k : Fin n) (w w' : ℝ), k ≠ j → w ≤ w' →
        demand M G (Function.update z k w) j ≤ demand M G (Function.update z k w') j) := by
  constructor
  · intro z j w w' hww
    refine demand_mono_gen M hM G hG _ _ j ?_ ?_
    · intro π h; rw [mem_budget_some] at h ⊢; simp at h ⊢; linarith
    · intro π hj o ho
      cases o with
      | none => exact mem_budget_none _ π
      | some i =>
        by_cases hij : i = j
        · subst hij; exact hj
        · rw [mem_budget_some] at ho ⊢
          rwa [Function.update_of_ne hij] at ho ⊢
  · intro z j k w w' hkj hww
    refine demand_mono_gen M hM G hG _ _ j ?_ ?_
    · intro π h; rw [mem_budget_some] at h ⊢
      rwa [Function.update_of_ne hkj.symm] at h ⊢
    · intro π _
      refine budget_anti ?_ π
      intro i
      by_cases hik : i = k
      · subst hik; simpa using hww
      · rw [Function.update_of_ne hik, Function.update_of_ne hik]

theorem ms_daop_monotone_cutoff_exists (M : Market m n) (hM : M.Standing)
    (G : Fin m → Measure (Fin n → ℝ)) (hG : ∀ t, IsProbabilityMeasure (G t))
    (q : Fin n → ℝ) (B : ℝ) (hB : 0 < B) :
    (∀ z ∈ box B, DAop M G q B z ∈ box B) ∧
      (∀ z ∈ box B, ∀ z' ∈ box B, z ≤ z' → DAop M G q B z ≤ DAop M G q B z') ∧
      ∃ z, IsDACutoff M G q B z :=
  ⟨fun z hz => daop_mem_box M G q B hB z hz,
    fun z _ z' _ h => daop_mono M hM G hG q B z z' h, cutoff_exists M hM G hG q B hB⟩

theorem ms_eq_H_2 (M : Market m n) (hM : M.Standing) (y : Fin m → Finset (Option (Fin n)) → ℝ)
    (hy : Ymem M y) :
    (∀ j, demand M (h1Law y) 1 j = lhs11 M y j) ∧
      DAop M (h1Law y) (lhs11 M y) 2 1 = 1 :=
  ⟨demand_one_eq M hM _ (h1_prob M y hy) y (h1_bs_one M y hy),
    one_fixed M hM _ (h1_prob M y hy) y (h1_bs_one M y hy)⟩

theorem ms_h1_budget_at_one (M : Market m n) (y : Fin m → Finset (Option (Fin n)) → ℝ)
    (hy : Ymem M y) :
    (∀ t, IsProbabilityMeasure (h1Law y t)) ∧ (∀ t, ∀ᵐ π ∂(h1Law y t), π ∈ box 2) ∧
      ∀ t S, bsProb (h1Law y) 1 t S = y t S :=
  ⟨h1_prob M y hy, h1_box M y, h1_bs_one M y hy⟩

theorem ms_h1_cutoff_respects_quota (M : Market m n) (hM : M.Standing)
    (y : Fin m → Finset (Option (Fin n)) → ℝ) (hy : Ymem M y) (z : Fin n → ℝ)
    (hz : IsDACutoff M (h1Law y) (lhs11 M y) 2 z) :
    ∀ j, demand M (h1Law y) z j ≤ lhs11 M y j :=
  cutoff_respects M hM _ (h1_prob M y hy) (h1_lip M y hy) y (h1_bs_one M y hy) z hz

theorem ms_eq_H_4 (M : Market m n) (hM : M.Standing) (hreg : Regular M)
    (y : Fin m → Finset (Option (Fin n)) → ℝ) (hy : Ymem M y) (z : Fin n → ℝ)
    (hzbox : z ∈ box 2) (hz1 : z ≤ 1)
    (hne : ∃ t S, bsProb (h1Law y) z t S ≠ y t S) :
    (∑ t, M.lam t) - ∑ j, demand M (h1Law y) z j < (∑ t, M.lam t) - ∑ j, lhs11 M y j := by
  have hG := h1_prob M y hy
  have hbs := h1_bs_one M y hy
  have hD1 := demand_one_eq M hM _ hG y hbs
  rw [← Finset.sum_congr rfl fun j _ => hD1 j]
  by_contra hcon
  have hle : ∑ j, demand M (h1Law y) z j ≤ ∑ j, demand M (h1Law y) 1 j := by linarith
  obtain ⟨t, S, hS⟩ := hne
  exact hS ((core_eq M hM hreg _ hG z 1 hz1 hle t S).trans (hbs t S))

theorem ms_proposition_H_1 (M : Market m n) (hM : M.Standing) (hreg : Regular M)
    (y : Fin m → Finset (Option (Fin n)) → ℝ) (hy : Ymem M y) :
    ∃ z, IsDACutoff M (h1Law y) (lhs11 M y) 2 z ∧ ∀ t S, bsProb (h1Law y) z t S = y t S :=
  implement M hM hreg _ (h1_prob M y hy) (h1_lip M y hy) y (h1_bs_one M y hy)

theorem ms_proposition_H_2_a (b : Fin m → Fin n → ℝ) (z : Fin n → ℝ) :
    NestedWithinSegment (bsProb (stbLaw b) z) := stb_nested b z

theorem ms_proposition_H_3 (M : Market m n) (hM : M.Standing) (hreg : Regular M)
    (y : Fin m → Finset (Option (Fin n)) → ℝ) (hy : Ymem M y) (hnest : NestedWithinSegment y) :
    ∃ z, IsDACutoff M (stbLaw (stbBoost y)) (lhs11 M y) 2 z ∧
      ∀ t S, bsProb (stbLaw (stbBoost y)) z t S = y t S :=
  implement M hM hreg _ (stb_prob _) (stb_lip _) y (stb_bs_one M y hy hnest)

theorem ms_theorem_1_a (M : Market m n) (hM : M.Standing) (hreg : Regular M) :
    (∀ y, Ymem M y → DAImplementable M y) ∧
      (∀ y, Ymem M y → (DASTBImplementable M y ↔ NestedWithinSegment y)) := by
  constructor
  · intro y hy
    obtain ⟨z, hz, hbs⟩ := ms_proposition_H_1 M hM hreg y hy
    exact ⟨2, h1Law y, lhs11 M y, z, by norm_num, h1_prob M y hy, h1_box M y,
      fun j => ⟨lhs11_nonneg M hM y hy j, hy.2.1 j⟩, hz, hbs⟩
  · intro y hy
    constructor
    · rintro ⟨B, b, q, z, _, _, _, _, hbs⟩
      intro t S S' h1 h2
      exact stb_nested b z t S S' (by rw [hbs]; exact h1) (by rw [hbs]; exact h2)
    · intro hnest
      obtain ⟨z, hz, hbs⟩ := ms_proposition_H_3 M hM hreg y hy hnest
      exact ⟨2, stbBoost y, lhs11 M y, z, by norm_num, stbBoost_bounds M y hy,
        fun j => ⟨lhs11_nonneg M hM y hy j, hy.2.1 j⟩, hz, hbs⟩

end PriorityAlloc.DAFlex

open PriorityAlloc.DAFlex MeasureTheory Classical

theorem solution {m n : ℕ} (M : Market m n) (hM : M.Standing) (y : Fin m → Finset (Option (Fin n)) → ℝ)
    (hy : Ymem M y) :
    (∀ j, demand M (h1Law y) 1 j = lhs11 M y j) ∧
      DAop M (h1Law y) (lhs11 M y) 2 1 = 1 := by
  apply PriorityAlloc.DAFlex.ms_eq_H_2 <;> assumption
