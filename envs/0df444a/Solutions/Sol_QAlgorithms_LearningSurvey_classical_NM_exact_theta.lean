-- Prove2me | solution 1 for QAlgorithms.LearningSurvey.classical_NM_exact_theta
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T10:46:08.91357+00:00
-- url     : https://prove2.me/submissions/4938676a-5b8b-4464-b54e-ef85f402584b

import Definitions.Def_QAlgorithms_Defs_LearningHardInstances

noncomputable section

namespace NMAux

open QAlgorithms QAlgorithms.Learning
open Classical

variable {ι : Type*}

/-- Query the listed indices that still split the current class. -/
def build : List ι → Finset (ι → Bool) → DecisionTree ι Bool (ι → Bool)
  | [], S => .leaf (if h : S.Nonempty then h.choose else fun _ => false)
  | i :: L, S =>
    if ∃ c ∈ S, ∃ c' ∈ S, c i ≠ c' i then
      .node i (fun b => build L (S.filter (fun c => c i = b)))
    else build L S

lemma build_queries (L : List ι) : ∀ (S : Finset (ι → Bool)) (x : ι → Bool),
    (build L S).queries x ≤ L.length ∧ (build L S).queries x ≤ S.card - 1 := by
  induction L with
  | nil => intro S x; simp [build, DecisionTree.queries]
  | cons i L ih =>
    intro S x
    by_cases h : ∃ c ∈ S, ∃ c' ∈ S, c i ≠ c' i
    · rw [build, if_pos h, DecisionTree.queries]
      obtain ⟨c, hc, c', hc', hne⟩ := h
      obtain ⟨h1, h2⟩ := ih (S.filter (fun d => d i = x i)) x
      have hsub : (S.filter (fun d => d i = x i)).card < S.card := by
        apply Finset.card_lt_card
        refine ⟨Finset.filter_subset _ _, fun hS => ?_⟩
        have := hS hc; have := hS hc'
        simp only [Finset.mem_filter] at *
        exact hne (by simp_all)
      have hpos : 0 < (S.filter (fun d => d i = x i)).card := by
        apply Finset.card_pos.2
        by_cases hx : c i = x i
        · exact ⟨c, Finset.mem_filter.2 ⟨hc, hx⟩⟩
        · refine ⟨c', Finset.mem_filter.2 ⟨hc', ?_⟩⟩
          cases h1' : c i <;> cases h2' : c' i <;> cases h3 : x i <;> simp_all
      simp only [List.length_cons]
      omega
    · rw [build, if_neg h]
      obtain ⟨h1, h2⟩ := ih S x
      simp only [List.length_cons]
      omega

lemma build_eval (L : List ι) : ∀ (S : Finset (ι → Bool)) (c : ι → Bool), c ∈ S →
    (∀ j, j ∉ L → ∀ d ∈ S, d j = c j) → (build L S).eval c = c := by
  induction L with
  | nil =>
    intro S c hc hagree
    have hS : S.Nonempty := ⟨c, hc⟩
    simp only [build, dif_pos hS, DecisionTree.eval]
    funext j
    exact hagree j (by simp) _ hS.choose_spec
  | cons i L ih =>
    intro S c hc hagree
    by_cases h : ∃ c ∈ S, ∃ c' ∈ S, c i ≠ c' i
    · rw [build, if_pos h, DecisionTree.eval]
      refine ih (S.filter (fun d => d i = c i)) c (Finset.mem_filter.2 ⟨hc, rfl⟩) ?_
      intro j hj d hd
      rw [Finset.mem_filter] at hd
      by_cases hji : j = i
      · subst hji; exact hd.2
      · exact hagree j (by simp [hji, hj]) d hd.1
    · rw [build, if_neg h]
      apply ih S c hc
      intro j hj d hd
      by_cases hji : j = i
      · subst hji
        by_contra hne
        exact h ⟨d, hd, c, hc, hne⟩
      · exact hagree j (by simp [hji, hj]) d hd

variable [Fintype ι] [DecidableEq ι]

lemma upper (C : Finset (ι → Bool)) :
    ((Finset.univ : Finset ι).toList.length) ∈ {T : ℕ | ∃ R : RandDecisionTree ι Bool (ι → Bool),
      RandMakesAtMost R T ∧ ∀ c ∈ C, successProb R c c ≥ 2 / 3} ∧
    (C.card - 1) ∈ {T : ℕ | ∃ R : RandDecisionTree ι Bool (ι → Bool),
      RandMakesAtMost R T ∧ ∀ c ∈ C, successProb R c c ≥ 2 / 3} := by
  have hsucc : ∀ c ∈ C, successProb (PMF.pure (build Finset.univ.toList C)) c c ≥ 2 / 3 := by
    intro c hc
    rw [successProb, PMF.pure_map, build_eval _ C c hc (fun j hj => absurd (by simp) hj)]
    simp; norm_num
  refine ⟨⟨PMF.pure (build Finset.univ.toList C), ?_, hsucc⟩,
    ⟨PMF.pure (build Finset.univ.toList C), ?_, hsucc⟩⟩
  · intro t ht x
    rw [PMF.support_pure, Set.mem_singleton_iff] at ht
    subst ht; exact (build_queries _ C x).1
  · intro t ht x
    rw [PMF.support_pure, Set.mem_singleton_iff] at ht
    subst ht; exact (build_queries _ C x).2

lemma classicalExact_le (C : Finset (ι → Bool)) :
    classicalExactComplexity C ≤ min (C.card - 1) (Fintype.card ι) := by
  obtain ⟨h1, h2⟩ := upper C
  rw [Finset.length_toList, Finset.card_univ] at h1
  exact le_min (Nat.sInf_le h2) (Nat.sInf_le h1)

lemma classicalExact_mem (C : Finset (ι → Bool)) :
    classicalExactComplexity C ∈ {T : ℕ | ∃ R : RandDecisionTree ι Bool (ι → Bool),
      RandMakesAtMost R T ∧ ∀ c ∈ C, successProb R c c ≥ 2 / 3} :=
  Nat.sInf_mem ⟨_, (upper C).2⟩


/-- The set of indices queried along the path of `x`. -/
def qset {α : Type*} : DecisionTree ι Bool α → (ι → Bool) → Finset ι
  | .leaf _, _ => ∅
  | .node i next, x => insert i (qset (next (x i)) x)

lemma qset_card {α : Type*} (t : DecisionTree ι Bool α) (x : ι → Bool) :
    (qset t x).card ≤ t.queries x := by
  induction t with
  | leaf a => simp [qset, DecisionTree.queries]
  | node i next ih =>
    simp only [qset, DecisionTree.queries]
    exact (Finset.card_insert_le _ _).trans (by have := ih (x i); omega)

lemma eval_agree {α : Type*} (t : DecisionTree ι Bool α) (x y : ι → Bool)
    (h : ∀ j ∈ qset t x, x j = y j) : t.eval x = t.eval y := by
  induction t with
  | leaf a => rfl
  | node i next ih =>
    simp only [qset, Finset.mem_insert] at h
    simp only [DecisionTree.eval]
    rw [← h i (Or.inl rfl)]
    exact ih (x i) (fun j hj => h j (Or.inr hj))

/-- The point concept `e_i`. -/
def pt (i : ι) : ι → Bool := fun j => decide (j = i)

lemma pt_ne_zero (i : ι) : pt i ≠ fun _ => false := by
  intro h; have := congrFun h i; simp [pt] at this

lemma pt_inj : Function.Injective (pt : ι → ι → Bool) := by
  intro i j h; have := congrFun h i; simp [pt] at this; exact this

lemma pointwise (I : Finset ι) (t : DecisionTree ι Bool (ι → Bool)) (T : ℕ)
    (ht : t.MakesAtMost T) :
    (∑ i ∈ I, (if t.eval (pt i) = pt i then 1 else 0 : ℕ)) +
      (if t.eval (fun _ => false) = (fun _ => false) then 1 else 0) ≤ T + 1 := by
  set v := t.eval (fun _ => false)
  have h1 : ∀ i ∈ I, (if t.eval (pt i) = pt i then 1 else 0 : ℕ) ≤
      (if i ∈ qset t (fun _ => false) then 1 else 0) + (if v = pt i then 1 else 0) := by
    intro i _
    by_cases hq : i ∈ qset t (fun _ => false)
    · simp only [hq, if_true]; split_ifs <;> omega
    · have : t.eval (pt i) = v := by
        symm; apply eval_agree; intro j hj
        have : j ≠ i := fun e => hq (e ▸ hj)
        simp [pt, this]
      rw [this]; simp only [hq, if_false]; omega
  have h2 : (∑ i ∈ I, (if i ∈ qset t (fun _ => false) then 1 else 0 : ℕ)) ≤ T := by
    rw [Finset.sum_boole]
    simp only [Nat.cast_id]
    refine (Finset.card_le_card (fun j hj => (Finset.mem_filter.1 hj).2)).trans ?_
    exact (qset_card t _).trans (ht _)
  have h3 : (∑ i ∈ I, (if v = pt i then 1 else 0 : ℕ)) +
      (if v = (fun _ => false) then 1 else 0) ≤ 1 := by
    rw [Finset.sum_boole]
    simp only [Nat.cast_id]
    by_cases hv : v = fun _ => false
    · have : I.filter (fun i => v = pt i) = ∅ := by
        apply Finset.filter_false_of_mem; intro i _ h
        exact pt_ne_zero i (h ▸ hv)
      rw [hv] at this ⊢; rw [this]; simp
    · simp only [hv, if_false, add_zero]
      apply Finset.card_le_one.2
      intro a ha b hb
      exact pt_inj ((Finset.mem_filter.1 ha).2.symm.trans (Finset.mem_filter.1 hb).2)
  calc _ ≤ (∑ i ∈ I, ((if i ∈ qset t (fun _ => false) then 1 else 0 : ℕ) +
        (if v = pt i then 1 else 0))) + (if v = (fun _ => false) then 1 else 0) :=
          Nat.add_le_add_right (Finset.sum_le_sum h1) _
    _ ≤ T + 1 := by rw [Finset.sum_add_distrib]; omega

lemma map_eq (R : RandDecisionTree ι Bool (ι → Bool)) (x a : ι → Bool) :
    (R.map fun t => t.eval x) a = ∑' t, R t * (if t.eval x = a then 1 else 0) := by
  rw [PMF.map_apply]; congr 1; funext t
  by_cases h : t.eval x = a
  · simp [h]
  · simp [h, Ne.symm h]

lemma expect (I : Finset ι) (R : RandDecisionTree ι Bool (ι → Bool)) (T : ℕ)
    (hR : RandMakesAtMost R T) :
    (∑ i ∈ I, successProb R (pt i) (pt i)) + successProb R (fun _ => false) (fun _ => false)
      ≤ T + 1 := by
  have hE : (∑ i ∈ I, (R.map fun t => t.eval (pt i)) (pt i)) +
      (R.map fun t => t.eval (fun _ => false)) (fun _ => false) ≤ (T + 1 : ENNReal) := by
    simp only [map_eq]
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), ← ENNReal.tsum_add]
    calc _ ≤ ∑' t, R t * ((T + 1 : ℕ) : ENNReal) := by
          apply ENNReal.tsum_le_tsum; intro t
          rw [← Finset.mul_sum, ← mul_add]
          by_cases h0 : R t = 0
          · simp [h0]
          · gcongr
            have := pointwise I t T (hR t ((PMF.mem_support_iff R t).2 h0))
            exact_mod_cast this
      _ = (T + 1 : ENNReal) := by rw [ENNReal.tsum_mul_right, R.tsum_coe, one_mul]; push_cast; rfl
  have hfin : ∀ x a, (R.map fun t => t.eval x) a ≠ ⊤ := fun x a => PMF.apply_ne_top _ _
  have := ENNReal.toReal_mono (by simp) hE
  have hT : ((T : ENNReal) + 1).toReal = T + 1 := by
    rw [ENNReal.toReal_add (by simp) (by simp)]; simp
  rw [ENNReal.toReal_add (ENNReal.sum_ne_top.2 (fun i _ => hfin _ _)) (hfin _ _),
    ENNReal.toReal_sum (fun i _ => hfin _ _), hT] at this
  exact this

lemma lower (I : Finset ι) (C : Finset (ι → Bool)) (hC0 : (fun _ => false) ∈ C)
    (hCI : ∀ i ∈ I, pt i ∈ C) (T : ℕ)
    (hT : T ∈ {T : ℕ | ∃ R : RandDecisionTree ι Bool (ι → Bool),
      RandMakesAtMost R T ∧ ∀ c ∈ C, successProb R c c ≥ 2 / 3}) :
    ((I.card : ℝ) + 1) * (2 / 3) ≤ T + 1 := by
  obtain ⟨R, hR, hs⟩ := hT
  have := expect I R T hR
  have h1 : ∑ i ∈ I, (2 / 3 : ℝ) ≤ ∑ i ∈ I, successProb R (pt i) (pt i) :=
    Finset.sum_le_sum fun i hi => hs _ (hCI i hi)
  have h2 := hs _ hC0
  simp only [Finset.sum_const, nsmul_eq_mul] at h1
  linarith

end NMAux

open QAlgorithms QAlgorithms.Learning in
theorem solution :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (n M : ℕ), 2 ≤ M → M ≤ 2 ^ (2 ^ n) →
      c₁ * (min M (2 ^ n) : ℕ) ≤ (Learning.classicalExactNM n M : ℝ) ∧
        (Learning.classicalExactNM n M : ℝ) ≤ c₂ * (min M (2 ^ n) : ℕ) := by
  refine ⟨1 / 6, 1, by norm_num, by norm_num, fun n M hM2 hMN => ⟨?_, ?_⟩⟩
  · have hcard : Fintype.card (Qubits n) = 2 ^ n := by simp [Qubits]
    set K := min (M - 1) (2 ^ n) with hK
    have hK1 : 1 ≤ K := by
      have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega
    obtain ⟨I, -, hI⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Qubits n))) (n := K) (by simp [hcard, hK])
    let C0 : Finset (Qubits n → Bool) := insert (fun _ => false) (I.image NMAux.pt)
    have hC0 : C0.card ≤ M := by
      refine (Finset.card_insert_le _ _).trans ?_
      have := Finset.card_image_le (s := I) (f := NMAux.pt)
      omega
    have hMcard : M ≤ Fintype.card (Qubits n → Bool) := by
      simp only [Fintype.card_fun, Fintype.card_bool, hcard]; exact hMN
    obtain ⟨C, hsub, hCcard⟩ := Finset.exists_superset_card_eq hC0 hMcard
    have hD := NMAux.lower I C (hsub (Finset.mem_insert_self _ _))
      (fun i hi => hsub (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hi)))
      _ (NMAux.classicalExact_mem C)
    have hle : classicalExactComplexity C ≤ classicalExactNM n M :=
      Finset.le_sup (Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hCcard⟩)
    have hle' : (classicalExactComplexity C : ℝ) ≤ classicalExactNM n M := by exact_mod_cast hle
    have hmin : min M (2 ^ n) ≤ 2 * K := by omega
    have hmin' : ((min M (2 ^ n) : ℕ) : ℝ) ≤ 2 * K := by exact_mod_cast hmin
    have hK1' : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    rw [hI] at hD
    linarith
  · have hle : classicalExactNM n M ≤ min M (2 ^ n) := by
      apply Finset.sup_le
      intro C hC
      rw [Finset.mem_powersetCard] at hC
      refine (NMAux.classicalExact_le C).trans ?_
      have : Fintype.card (Qubits n) = 2 ^ n := by simp [Qubits]
      rw [this, hC.2]; omega
    rw [one_mul]; exact_mod_cast hle
