-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P15.remark_I_2_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:11:52.265761+00:00
-- url     : https://prove2.me/submissions/3e35399b-df4a-4e2f-b85e-c8d18a3d7d6b

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P15

namespace X6P15

open Filter Topology Function

universe u v

section

variable {k : ℕ} {E : Fin k → Type u}
    [∀ i, TopologicalSpace (E i)] [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)]
    {F : Type v} [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

/-- Telescoping difference quotient of a continuous multilinear map. -/
lemma key_tendsto (m : MultilinearMap ℝ E F) (hm : Continuous m) (y v : (i : Fin k) → E i) :
    Tendsto (fun t : ℝ => t⁻¹ • (m (y + t • v) - m y)) (𝓝[≠] (0 : ℝ))
      (𝓝 (∑ i, m (update y i (v i)))) := by
  classical
  let z : ℕ → ℝ → (i : Fin k) → E i := fun n t l => if (l : ℕ) < n then y l + t • v l else y l
  let Q : ℝ → F := fun t => ∑ i : Fin k, m (update (z i t) i (v i))
  have hQc : Continuous Q := by
    apply continuous_finsetSum; intro i _
    apply hm.comp
    apply continuous_pi; intro l
    by_cases hl : l = i
    · subst hl; simp only [update_self]; exact continuous_const
    · simp only [update_of_ne hl, z]
      split_ifs
      · exact continuous_const.add (continuous_id.smul continuous_const)
      · exact continuous_const
  have hQ0 : Q 0 = ∑ i, m (update y i (v i)) := by
    simp only [Q, z, zero_smul, add_zero, ite_self]
  have hstep : ∀ t : ℝ, ∀ i : Fin k,
      m (z (i + 1) t) - m (z i t) = t • m (update (z i t) i (v i)) := by
    intro t i
    have e1 : z (i + 1) t = update (z i t) i (y i + t • v i) := by
      funext l
      by_cases hl : l = i
      · subst hl; simp [z]
      · simp only [update_of_ne hl, z]
        have : (l : ℕ) ≠ i := fun h => hl (Fin.ext h)
        by_cases h : (l : ℕ) < i
        · simp [h, Nat.lt_succ_of_lt h]
        · have h' : ¬ (l : ℕ) < i + 1 := by omega
          simp [h, h']
    have e2 : z i t = update (z i t) i (y i) := by
      funext l
      by_cases hl : l = i
      · subst hl; simp [z]
      · simp [update_of_ne hl]
    rw [e1, MultilinearMap.map_update_add, MultilinearMap.map_update_smul, ← e2]
    abel
  have htel : ∀ t : ℝ, m (y + t • v) - m y = t • Q t := by
    intro t
    have hk : z k t = y + t • v := by
      funext l; simp [z, l.isLt]
    have h0 : z 0 t = y := by funext l; simp [z]
    rw [← hk, ← h0]
    have := Finset.sum_range_sub (fun n => m (z n t)) k
    rw [← this, ← Fin.sum_univ_eq_sum_range (fun n => m (z (n + 1) t) - m (z n t)) k]
    simp only [hstep, Q, Finset.smul_sum]
  have hlim : Tendsto Q (𝓝[≠] (0 : ℝ)) (𝓝 (Q 0)) :=
    (hQc.tendsto 0).mono_left nhdsWithin_le_nhds
  rw [hQ0] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [htel, smul_smul, inv_mul_cancel₀ ht, one_smul]

/-- Slot assignments: `none` = the point, `some r` = the `r`-th direction. -/
def slot {j : ℕ} (τ : Fin k → Option (Fin j)) (x : (i : Fin k) → E i)
    (a : Fin j → (i : Fin k) → E i) : (i : Fin k) → E i :=
  fun i => (τ i).elim (x i) (fun r => a r i)

def terms (k : ℕ) : (j : ℕ) → List (Fin k → Option (Fin j))
  | 0 => [fun _ => none]
  | j + 1 => (terms k j).flatMap (fun τ => ((List.finRange k).filter (fun i => (τ i).isNone)).map
      (fun i => update (fun l => (τ l).map Fin.castSucc) i (some (Fin.last j))))

def G (m : MultilinearMap ℝ E F) (j : ℕ) (x : (i : Fin k) → E i)
    (a : Fin j → (i : Fin k) → E i) : F :=
  ((terms k j).map (fun τ => m (slot τ x a))).sum

lemma slot_cont {j : ℕ} (τ : Fin k → Option (Fin j)) :
    Continuous (fun p : ((i : Fin k) → E i) × (Fin j → (i : Fin k) → E i) => slot τ p.1 p.2) := by
  apply continuous_pi; intro i
  unfold slot
  cases τ i with
  | none => exact (continuous_apply i).comp continuous_fst
  | some r => exact (continuous_apply i).comp ((continuous_apply r).comp continuous_snd)

lemma G_cont (m : MultilinearMap ℝ E F) (hm : Continuous m) (j : ℕ) :
    Continuous (fun p : ((i : Fin k) → E i) × (Fin j → (i : Fin k) → E i) => G m j p.1 p.2) := by
  unfold G
  induction (terms k j) with
  | nil => simpa using continuous_const
  | cons τ l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hm.comp (slot_cont τ)).add ih

omit [TopologicalSpace F] [Module ℝ F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma list_sum_sub {α : Type*} (l : List α) (f g : α → F) :
    (l.map f).sum - (l.map g).sum = (l.map (fun i => f i - g i)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ← ih]; abel

omit [∀ i, TopologicalSpace (E i)] [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)] in
lemma slot_none {j : ℕ} (x : (i : Fin k) → E i) (a : Fin j → (i : Fin k) → E i) :
    slot (fun _ => none) x a = x := by
  funext i; rfl

lemma list_filter_sum {α : Type*} (l : List α) (p : α → Bool) (g : α → F) :
    ((l.filter p).map g).sum = (l.map (fun i => if p i then g i else 0)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : p a <;> simp [List.filter_cons, h, ih]

lemma term_tendsto (m : MultilinearMap ℝ E F) (hm : Continuous m) {j : ℕ}
    (τ : Fin k → Option (Fin j)) (x h : (i : Fin k) → E i) (a : Fin j → (i : Fin k) → E i) :
    Tendsto (fun t : ℝ => t⁻¹ • (m (slot τ (x + t • h) a) - m (slot τ x a))) (𝓝[≠] (0 : ℝ))
      (𝓝 ((((List.finRange k).filter (fun i => (τ i).isNone)).map
        (fun i => m (update (slot τ x a) i (h i)))).sum)) := by
  classical
  let L0 : (i : Fin k) → E i := fun i => if (τ i).isNone then h i else 0
  have hs : ∀ t : ℝ, slot τ (x + t • h) a = slot τ x a + t • L0 := by
    intro t; funext i
    simp only [slot, L0, Pi.add_apply, Pi.smul_apply]
    cases τ i <;> simp
  simp only [hs]
  have := key_tendsto m hm (slot τ x a) L0
  convert this using 2
  rw [list_filter_sum, Fin.sum_univ_def]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : τ i = none
  · simp [hi, L0]
  · simp [hi, L0, MultilinearMap.map_update_zero]

lemma slot_update {j : ℕ} (τ : Fin k → Option (Fin j)) (i0 : Fin k) (hi0 : (τ i0).isNone)
    (x : (i : Fin k) → E i) (a : Fin (j + 1) → (i : Fin k) → E i) :
    slot (update (fun l => (τ l).map Fin.castSucc) i0 (some (Fin.last j))) x a =
      update (slot τ x (fun r => a r.castSucc)) i0 (a (Fin.last j) i0) := by
  classical
  funext l
  by_cases hl : l = i0
  · subst hl; simp [slot]
  · rw [update_of_ne hl]
    simp only [slot, update_of_ne hl]
    cases τ l <;> simp

lemma G_succ (m : MultilinearMap ℝ E F) (j : ℕ) (x : (i : Fin k) → E i)
    (a : Fin (j + 1) → (i : Fin k) → E i) :
    G m (j + 1) x a = ((terms k j).map (fun τ =>
      (((List.finRange k).filter (fun i => (τ i).isNone)).map
        (fun i => m (update (slot τ x (fun r => a r.castSucc)) i (a (Fin.last j) i)))).sum)).sum := by
  classical
  simp only [G, terms, List.flatMap, List.map_flatten, List.sum_flatten, List.map_map]
  congr 1
  apply List.map_congr_left
  intro τ _
  simp only [Function.comp_def, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_filter] at hi
  simp only [Function.comp, slot_update τ i hi.2 x a]

lemma G_tendsto (m : MultilinearMap ℝ E F) (hm : Continuous m) (j : ℕ) (x h : (i : Fin k) → E i)
    (a : Fin j → (i : Fin k) → E i) :
    Tendsto (fun t : ℝ => t⁻¹ • (G m j (x + t • h) a - G m j x a)) (𝓝[≠] (0 : ℝ))
      (𝓝 (G m (j + 1) x (Fin.snoc a h))) := by
  rw [G_succ]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  have e : ∀ t : ℝ, t⁻¹ • (G m j (x + t • h) a - G m j x a) =
      ((terms k j).map (fun τ => t⁻¹ • (m (slot τ (x + t • h) a) - m (slot τ x a)))).sum := by
    intro t
    simp only [G]
    rw [list_sum_sub, List.smul_sum, List.map_map]
    rfl
  simp only [e]
  apply tendsto_list_sum
  intro τ _
  exact term_tendsto m hm τ x h a

lemma none_count (j : ℕ) : ∀ τ ∈ terms k j,
    j + (Finset.univ.filter (fun i => (τ i).isNone)).card = k := by
  classical
  induction j with
  | zero => intro τ hτ; simp [terms] at hτ; subst hτ; simp
  | succ j ih =>
    intro τ' hτ'
    simp only [terms, List.mem_flatMap, List.mem_map, List.mem_filter] at hτ'
    obtain ⟨τ, hτ, i0, ⟨-, hi0⟩, rfl⟩ := hτ'
    have hc := ih τ hτ
    have hset : (Finset.univ.filter (fun i =>
        ((update (fun l => (τ l).map Fin.castSucc) i0 (some (Fin.last j))) i).isNone)) =
        (Finset.univ.filter (fun i => (τ i).isNone)).erase i0 := by
      ext l
      by_cases hl : l = i0
      · subst hl; simp
      · simp [hl, update_of_ne hl]
    rw [hset, Finset.card_erase_of_mem (by simpa using hi0)]
    have : 0 < (Finset.univ.filter (fun i => (τ i).isNone)).card :=
      Finset.card_pos.2 ⟨i0, by simpa using hi0⟩
    omega

lemma terms_succ_k : terms k (k + 1) = [] := by
  classical
  apply List.eq_nil_iff_forall_not_mem.2
  intro τ' hτ'
  simp only [terms, List.mem_flatMap, List.mem_map, List.mem_filter] at hτ'
  obtain ⟨τ, hτ, i0, ⟨-, hi0⟩, -⟩ := hτ'
  have hc := none_count k τ hτ
  have : 0 < (Finset.univ.filter (fun i => (τ i).isNone)).card :=
    Finset.card_pos.2 ⟨i0, by simpa using hi0⟩
  omega

end

end X6P15

open X6P15 Filter Topology Function QAlgorithms.Papers.Independent.Next46.P15

universe u v

theorem solution
    (k : ℕ) (E : Fin k → Type u)
    [∀ i, TopologicalSpace (E i)] [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)]
    [∀ i, LocallyConvexSpace ℝ (E i)] [∀ i, T2Space (E i)]
    {F : Type v} [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    [LocallyConvexSpace ℝ F] [T2Space F]
    (m : MultilinearMap ℝ E F) (hm : Continuous m) :
    IsMBCFiniteOn Set.univ (fun x => m x) 1 ∧
    IsMBSmoothOn Set.univ (fun x => m x) ∧
    (∀ x h : (i : Fin k) → E i,
      directionalDerivative (fun y => m y) x h =
        ∑ i : Fin k, m (Function.update x i (h i))) ∧
    (∀ (x : (i : Fin k) → E i) (h : Fin (k + 1) → ((i : Fin k) → E i)),
      iteratedDirectional (fun y => m y) (k + 1) x h = 0) := by
  classical
  -- uniqueness of directional derivatives
  have uniq : ∀ (f : ((i : Fin k) → E i) → F) (x h : (i : Fin k) → E i) (y : F),
      HasDirectionalDerivative f x h y → directionalDerivative f x h = y := by
    intro f x h y hy
    have hs : HasDirectionalDerivative f x h (directionalDerivative f x h) :=
      Classical.epsilon_spec (p := HasDirectionalDerivative f x h) ⟨y, hy⟩
    exact tendsto_nhds_unique hs hy
  have hG : ∀ j x a, iteratedDirectional (fun y => m y) j x a = G m j x a := by
    intro j
    induction j with
    | zero => intro x a; simp [iteratedDirectional, G, terms, slot_none]
    | succ j ih =>
      intro x a
      simp only [iteratedDirectional]
      have hf : (fun y => iteratedDirectional (fun y => m y) j y (fun i => a i.castSucc)) =
          fun y => G m j y (fun i => a i.castSucc) := by
        funext y; exact ih y _
      rw [hf]
      apply uniq
      have := G_tendsto m hm j x (a (Fin.last j)) (fun i => a i.castSucc)
      have e : Fin.snoc (fun i : Fin j => a i.castSucc) (a (Fin.last j)) = a := Fin.snoc_init_self a
      rw [e] at this
      exact this
  have hGf : ∀ j, (fun p : ((i : Fin k) → E i) × (Fin j → (i : Fin k) → E i) =>
      iteratedDirectional (fun y => m y) j p.1 p.2) = fun p => G m j p.1 p.2 := by
    intro j; funext p; exact hG j p.1 p.2
  refine ⟨⟨?_, ?_⟩, ⟨G m, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro j _ x _ a h
    have hf : (fun y => iteratedDirectional (fun y => m y) j y a) = fun y => G m j y a := by
      funext y; exact hG j y a
    rw [hf, hG]
    exact G_tendsto m hm j x h a
  · intro j _
    rw [hGf]
    exact (G_cont m hm j).continuousOn
  · intro x _
    simp [G, terms, slot_none]
  · intro n
    exact (G_cont m hm n).continuousOn
  · intro n x _ a h
    exact G_tendsto m hm n x h a
  · intro x h
    apply uniq
    exact key_tendsto m hm x h
  · intro x h
    rw [hG]
    simp [G, terms_succ_k]
