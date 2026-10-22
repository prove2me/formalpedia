-- Prove2me | solution 1 for ProjSchedTW.Complexity.cumFeasLang_mem_NP
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T10:55:25.765206+00:00
-- url     : https://prove2.me/submissions/d202c20f-9036-45c8-b00f-2dcb5cf781c2

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_ProjSchedTW_Complexity_Cumulative
import Theorems.Thm_ProjSchedTW_Complexity_cumCheck_len_filter_polytime
import Theorems.Thm_ProjSchedTW_Complexity_cumCheck_wf_filter_polytime
import Theorems.Thm_ProjSchedTW_Complexity_cumCheck_time_filter_polytime
import Theorems.Thm_ProjSchedTW_Complexity_cumCheck_inv_filter_polytime
import Theorems.Thm_ProjSchedTW_Complexity_cumCheck_acyc_filter_polytime
import Theorems.Thm_CookPvsNP_mem_P_of_polyReducible
import Theorems.Thm_CookPvsNP_stack_program_polytime
import Theorems.Thm_CookPvsNP_polyTimeComputable_comp

set_option autoImplicit false

section D0bfAll


open CookPvsNP

namespace D0bfN1

/-- The 3-state machine that accepts iff the scanned input square is non-blank. -/
def M1 (A : Type) : TM A where
  Q := Fin 3
  q₀ := 0
  qaccept := 1
  qreject := 2
  accept_ne_reject := by decide
  δ := fun _ s => (if s.isSome then 1 else 2, s, Move.right)

theorem step_halt {A : Type} (M : TM A) (c : Cfg A M.Q) (h : M.IsHalting c) : M.step c = c := by
  unfold TM.step
  rw [if_pos h]

theorem run_succ_eq (A : Type) (w : List A) (m : ℕ) :
    (M1 A).run (m + 1) ((M1 A).init w) = (M1 A).step ((M1 A).init w) := by
  unfold TM.run
  rw [Function.iterate_succ_apply]
  apply Function.iterate_fixed
  have hh : (M1 A).IsHalting ((M1 A).step ((M1 A).init w)) := by
    unfold TM.IsHalting
    cases w <;> simp [TM.step, TM.init, TM.IsHalting, M1]
  exact step_halt _ _ hh

theorem state_step (A : Type) (w : List A) :
    ((M1 A).step ((M1 A).init w)).state = if w = [] then (2 : Fin 3) else 1 := by
  cases w <;> simp [TM.step, TM.init, TM.IsHalting, M1]

theorem nonempty_mem_P (A : Type) [Fintype A] : {w : List A | w ≠ []} ∈ P A := by
  refine ⟨A, inferInstance, Function.Embedding.refl A, M1 A, 1, fun w => ?_, fun w => ?_⟩
  · unfold TM.HaltsWithin
    rw [run_succ_eq]
    unfold TM.IsHalting
    rw [state_step]
    simp only [List.map_eq_nil_iff]
    split_ifs <;> simp [M1]
  · simp only [Set.mem_ofPred_eq, TM.Accepts]
    constructor
    · intro hw
      refine ⟨0 + 1, ?_⟩
      rw [run_succ_eq, state_step]
      simp [hw, M1]
    · rintro ⟨n, hn⟩ hw
      subst hw
      cases n with
      | zero => simp [TM.run, TM.init, M1] at hn
      | succ m =>
        rw [run_succ_eq, state_step] at hn
        simp [M1] at hn

end D0bfN1

set_option autoImplicit false

/-! N2 for d0bf0960: feasible instances have natural, polynomially bounded feasible schedules. -/

open CookPvsNP ProjSchedTW.Complexity

namespace D0bfN2

open CumInstance

lemma mem_activeSet (x : CumInstance) (S : Fin (x.n + 2) → ℝ) (k : Fin x.m) (t : ℝ)
    (i : Fin (x.n + 2)) :
    i ∈ x.activeSet S k t ↔
      (x.r i k < 0 ∧ S i ≤ t) ∨ (0 < x.r i k ∧ S i + (x.p i : ℝ) ≤ t) := by
  unfold activeSet
  rw [Finset.mem_filter]
  simp

lemma inventory_congr (x : CumInstance) (S S' : Fin (x.n + 2) → ℝ) (k : Fin x.m) (t t' : ℝ)
    (h1 : ∀ i, (S i ≤ t ↔ S' i ≤ t')) (h2 : ∀ i, (S i + x.p i ≤ t ↔ S' i + x.p i ≤ t')) :
    x.inventory S k t = x.inventory S' k t' := by
  unfold inventory
  congr 1
  ext i
  rw [mem_activeSet, mem_activeSet, h1, h2]

lemma invFeas_of_transfer (x : CumInstance) (S S' : Fin (x.n + 2) → ℝ)
    (hS : x.InventoryFeasible S)
    (h : ∀ t : ℝ, 0 ≤ t → ∃ t' : ℝ, 0 ≤ t' ∧ (∀ i, (S' i ≤ t ↔ S i ≤ t')) ∧
      (∀ i, (S' i + x.p i ≤ t ↔ S i + x.p i ≤ t'))) : x.InventoryFeasible S' := by
  intro k t ht
  obtain ⟨t', ht', h1, h2⟩ := h t ht
  rw [inventory_congr x S' S k t t' h1 h2]
  exact hS k t' ht'

/-- (a) Rounding every start time down keeps a schedule feasible. -/
lemma floor_feasible (x : CumInstance) (S : Fin (x.n + 2) → ℝ) (h : x.Feasible S) :
    x.Feasible (fun i => ((⌊S i⌋₊ : ℕ) : ℝ)) := by
  obtain ⟨⟨h0, hnn, harc⟩, hinv⟩ := h
  refine ⟨⟨?_, fun i => Nat.cast_nonneg _, ?_⟩, ?_⟩
  · simp [h0]
  · intro e he
    have hz := harc e he
    have h1 : ((⌊S e.1⌋₊ : ℕ) : ℝ) = ((⌊S e.1⌋ : ℤ) : ℝ) := by
      rw [← Int.natCast_floor_eq_floor (hnn _)]; norm_cast
    have h2 : ((⌊S e.2⌋₊ : ℕ) : ℝ) = ((⌊S e.2⌋ : ℤ) : ℝ) := by
      rw [← Int.natCast_floor_eq_floor (hnn _)]; norm_cast
    show ((x.δ e.1 e.2 : ℤ) : ℝ) ≤ ((⌊S e.2⌋₊ : ℕ) : ℝ) - ((⌊S e.1⌋₊ : ℕ) : ℝ)
    rw [h1, h2]
    have h3 : ⌊S e.1⌋ + x.δ e.1 e.2 ≤ ⌊S e.2⌋ := by
      rw [← Int.floor_add_intCast]
      exact Int.floor_mono (by linarith)
    have h4 : ((⌊S e.1⌋ + x.δ e.1 e.2 : ℤ) : ℝ) ≤ ((⌊S e.2⌋ : ℤ) : ℝ) := by exact_mod_cast h3
    push_cast at h4
    linarith
  · apply invFeas_of_transfer x S _ hinv
    intro t ht
    classical
    set N := ⌊t⌋₊ with hN
    let T : Finset ℝ := insert (N : ℝ) ((Finset.univ.image (fun i => S i) ∪
      Finset.univ.image (fun i => S i + x.p i)).filter (· < (N : ℝ) + 1))
    have hne : T.Nonempty := ⟨_, Finset.mem_insert_self _ _⟩
    have hlt : ∀ a ∈ T, a < (N : ℝ) + 1 := by
      intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · linarith
      · exact (Finset.mem_filter.1 ha).2
    have hmax : T.max' hne < (N : ℝ) + 1 := hlt _ (Finset.max'_mem _ _)
    have key1 : ∀ i, (S i ≤ T.max' hne ↔ S i < (N : ℝ) + 1) := by
      intro i
      constructor
      · intro hi; linarith
      · intro hi
        apply Finset.le_max'
        apply Finset.mem_insert_of_mem
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)), hi⟩
    have key2 : ∀ i, (S i + x.p i ≤ T.max' hne ↔ S i + x.p i < (N : ℝ) + 1) := by
      intro i
      constructor
      · intro hi; linarith
      · intro hi
        apply Finset.le_max'
        apply Finset.mem_insert_of_mem
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem
          (fun i => S i + x.p i) (Finset.mem_univ _)), hi⟩
    refine ⟨T.max' hne, ?_, ?_, ?_⟩
    · exact le_trans (Nat.cast_nonneg N) (T.le_max' _ (Finset.mem_insert_self _ _))
    · intro i
      rw [key1]
      have e1 : ((⌊S i⌋₊ : ℕ) : ℝ) ≤ t ↔ ⌊S i⌋₊ ≤ N := (Nat.le_floor_iff ht).symm
      rw [e1, ← Nat.lt_succ_iff, Nat.floor_lt (hnn i)]
      push_cast; rfl
    · intro i
      rw [key2]
      have e1 : ((⌊S i⌋₊ : ℕ) : ℝ) + (x.p i : ℝ) ≤ t ↔ ⌊S i⌋₊ + x.p i ≤ N := by
        rw [← Nat.cast_add]; exact (Nat.le_floor_iff ht).symm
      rw [e1, ← Nat.floor_add_natCast (hnn i), ← Nat.lt_succ_iff,
        Nat.floor_lt (by have := hnn i; positivity)]
      push_cast; rfl

/-- The compression threshold `D = 1 + ∑ |z|` over all numbers of the instance code. -/
def Dc (x : CumInstance) : ℕ := 1 + (x.code.map Int.natAbs).sum

lemma natAbs_le_Dc (x : CumInstance) (z : ℤ) (hz : z ∈ x.code) : z.natAbs + 1 ≤ Dc x := by
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := Int.natAbs) hz)
  unfold Dc; omega

lemma p_mem_code (x : CumInstance) (i : Fin (x.n + 2)) : (x.p i : ℤ) ∈ x.code := by
  unfold CumInstance.code
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_right
  exact List.mem_ofFn.2 ⟨i, rfl⟩

lemma δ_mem_code (x : CumInstance) (i j : Fin (x.n + 2)) : x.δ i j ∈ x.code := by
  unfold CumInstance.code
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_right
  rw [List.mem_flatten]
  refine ⟨[if (i, j) ∈ x.E then (1 : ℤ) else 0, x.δ i j], ?_, by simp⟩
  rw [List.mem_flatten]
  exact ⟨_, List.mem_ofFn.2 ⟨i, rfl⟩, List.mem_ofFn.2 ⟨j, rfl⟩⟩

lemma hpDc (x : CumInstance) (i : Fin (x.n + 2)) : x.p i + 1 ≤ Dc x := by
  simpa using natAbs_le_Dc x _ (p_mem_code x i)

lemma hδDc (x : CumInstance) (i j : Fin (x.n + 2)) : x.δ i j + 1 ≤ (Dc x : ℤ) := by
  have h1 := natAbs_le_Dc x _ (δ_mem_code x i j)
  have h3 : x.δ i j ≤ ((x.δ i j).natAbs : ℤ) := Int.le_natAbs
  have h4 : ((x.δ i j).natAbs : ℤ) + 1 ≤ (Dc x : ℤ) := by exact_mod_cast h1
  linarith

/-- (b) Closing a gap of length `D` below `T` by one unit keeps a natural schedule feasible. -/
lemma shift_feasible (x : CumInstance) (S : Fin (x.n + 2) → ℕ)
    (h : x.Feasible (fun i => (S i : ℝ))) (D : ℕ) (hpD : ∀ i, x.p i + 1 ≤ D)
    (hδD : ∀ i j, x.δ i j + 1 ≤ (D : ℤ)) (T : ℕ) (hT : 1 ≤ T)
    (hgap : ∀ j, S j < T → S j + D < T) :
    x.Feasible (fun i => ((if T ≤ S i then S i - 1 else S i : ℕ) : ℝ)) := by
  obtain ⟨⟨h0, -, harc⟩, hinv⟩ := h
  have hS0 : S 0 = 0 := by simpa using h0
  have hc : ∀ i, ((if T ≤ S i then S i - 1 else S i : ℕ) : ℝ) =
      if T ≤ S i then (S i : ℝ) - 1 else (S i : ℝ) := by
    intro i
    split_ifs with hi
    · rw [Nat.cast_sub (by omega)]; simp
    · rfl
  refine ⟨⟨?_, fun i => Nat.cast_nonneg _, ?_⟩, ?_⟩
  · have : ¬ T ≤ S 0 := by omega
    simp [this, hS0]
  · intro e he
    have hz : x.δ e.1 e.2 ≤ (S e.2 : ℤ) - S e.1 := by
      have h5 := harc e he
      have h6 : ((x.δ e.1 e.2 : ℤ) : ℝ) ≤ (((S e.2 : ℤ) - (S e.1 : ℤ) : ℤ) : ℝ) := by
        push_cast; exact h5
      exact Int.cast_le.mp h6
    have g1 := hgap e.1
    have g2 := hgap e.2
    have hd := hδD e.1 e.2
    have hint : x.δ e.1 e.2 ≤ ((if T ≤ S e.2 then S e.2 - 1 else S e.2 : ℕ) : ℤ) -
        ((if T ≤ S e.1 then S e.1 - 1 else S e.1 : ℕ) : ℤ) := by
      split_ifs <;> omega
    show ((x.δ e.1 e.2 : ℤ) : ℝ) ≤ (((if T ≤ S e.2 then S e.2 - 1 else S e.2 : ℕ)) : ℝ) -
      (((if T ≤ S e.1 then S e.1 - 1 else S e.1 : ℕ)) : ℝ)
    generalize (if T ≤ S e.2 then S e.2 - 1 else S e.2) = A at hint ⊢
    generalize (if T ≤ S e.1 then S e.1 - 1 else S e.1) = B at hint ⊢
    have h7 : ((x.δ e.1 e.2 : ℤ) : ℝ) ≤ ((((A : ℤ) - (B : ℤ)) : ℤ) : ℝ) := Int.cast_le.mpr hint
    push_cast at h7
    exact h7
  · apply invFeas_of_transfer x _ _ hinv
    intro t ht
    refine ⟨if t < (T : ℝ) - 1 then t else t + 1, ?_, ?_, ?_⟩
    · split_ifs <;> linarith
    · intro i
      rw [hc i]
      by_cases hi : T ≤ S i
      · have hr : (T : ℝ) ≤ S i := by exact_mod_cast hi
        rw [if_pos hi]
        split_ifs <;> constructor <;> intro <;> linarith
      · have hr : (S i : ℝ) + x.p i + 2 ≤ T := by
          have := hgap i (by omega)
          have := hpD i
          exact_mod_cast (show S i + x.p i + 2 ≤ T by omega)
        rw [if_neg hi]
        split_ifs <;> constructor <;> intro <;> linarith [(Nat.cast_nonneg (x.p i) : (0 : ℝ) ≤ _)]
    · intro i
      rw [hc i]
      by_cases hi : T ≤ S i
      · have hr : (T : ℝ) ≤ S i := by exact_mod_cast hi
        rw [if_pos hi]
        split_ifs <;> constructor <;> intro <;> linarith
      · have hr : (S i : ℝ) + x.p i + 2 ≤ T := by
          have := hgap i (by omega)
          have := hpD i
          exact_mod_cast (show S i + x.p i + 2 ≤ T by omega)
        rw [if_neg hi]
        split_ifs <;> constructor <;> intro <;> linarith

/-- In a schedule without gaps of length `D`, every start time is at most `D` times the number of
strictly earlier activities. -/
lemma bound_of_nogap (x : CumInstance) (S : Fin (x.n + 2) → ℕ) (D : ℕ)
    (hng : ∀ i, 1 ≤ S i → ∃ j, S j < S i ∧ S i ≤ S j + D) :
    ∀ i, S i ≤ D * (Finset.univ.filter fun j => S j < S i).card := by
  intro i
  induction' hv : S i using Nat.strong_induction_on with v ih generalizing i
  subst hv
  rcases Nat.eq_zero_or_pos (S i) with h | h
  · rw [h]; exact Nat.zero_le _
  obtain ⟨j, hj1, hj2⟩ := hng i h
  have ihj := ih (S j) hj1 j rfl
  have hsub : (Finset.univ.filter fun l => S l < S j) ⊂
      (Finset.univ.filter fun l => S l < S i) := by
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨j, by simp [hj1], by simp⟩
    · intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
      omega
  have hcard := Finset.card_lt_card hsub
  calc S i ≤ S j + D := hj2
    _ ≤ D * (Finset.univ.filter fun l => S l < S j).card + D := by omega
    _ = D * ((Finset.univ.filter fun l => S l < S j).card + 1) := by ring
    _ ≤ D * (Finset.univ.filter fun l => S l < S i).card :=
      Nat.mul_le_mul_left _ hcard

/-- (c) A feasible natural schedule can be compressed to one with `S_i ≤ D (n+1)`. -/
lemma exists_bounded (x : CumInstance) (S : Fin (x.n + 2) → ℕ)
    (h : x.Feasible (fun i => (S i : ℝ))) (D : ℕ) (hpD : ∀ i, x.p i + 1 ≤ D)
    (hδD : ∀ i j, x.δ i j + 1 ≤ (D : ℤ)) :
    ∃ S' : Fin (x.n + 2) → ℕ, x.Feasible (fun i => (S' i : ℝ)) ∧
      ∀ i, S' i ≤ D * (x.n + 1) := by
  induction' hs : ∑ i, S i using Nat.strong_induction_on with m ih generalizing S
  subst hs
  by_cases hg : ∃ T, 1 ≤ T ∧ (∃ i, T ≤ S i) ∧ ∀ j, S j < T → S j + D < T
  · obtain ⟨T, hT, ⟨i, hi⟩, hgap⟩ := hg
    have hf := shift_feasible x S h D hpD hδD T hT hgap
    refine ih _ ?_ _ hf rfl
    apply Finset.sum_lt_sum
    · intro j _; split_ifs <;> omega
    · exact ⟨i, Finset.mem_univ _, by rw [if_pos hi]; omega⟩
  · refine ⟨S, h, fun i => ?_⟩
    have hng : ∀ i, 1 ≤ S i → ∃ j, S j < S i ∧ S i ≤ S j + D := by
      intro i hi
      by_contra hc
      push Not at hc
      exact hg ⟨S i, hi, ⟨i, le_rfl⟩, fun j hj => hc j hj⟩
    have hb := bound_of_nogap x S D hng i
    have hcard : (Finset.univ.filter fun j => S j < S i).card ≤ x.n + 1 := by
      have : (Finset.univ.filter fun j => S j < S i) ⊂ Finset.univ := by
        rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
        exact ⟨i, Finset.mem_univ _, by simp⟩
      have := Finset.card_lt_card this
      simp only [Finset.card_univ, Fintype.card_fin] at this
      omega
    exact le_trans hb (Nat.mul_le_mul_left _ hcard)

lemma len_encNat (v : ℕ) : (encNat v).length = v.size + 1 := by
  simp [encNat, Nat.size_eq_bits_len]

lemma len_encInts (l : List ℤ) :
    (l.map fun z => z.natAbs.size + 1).sum ≤ (encInts l).length := by
  induction l with
  | nil => simp [encInts]
  | cons a l ih =>
    simp only [encInts, List.flatMap_cons, List.length_append, List.map_cons,
      List.sum_cons] at ih ⊢
    have : a.natAbs.size + 1 ≤ (encInt a).length := by
      simp only [encInt, List.length_append, len_encNat]; omega
    omega

lemma length_le_sum (l : List ℤ) : l.length ≤ (l.map fun z => z.natAbs.size + 1).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega

lemma one_add_sum_le (l : List ℤ) :
    1 + (l.map Int.natAbs).sum ≤ 2 ^ (l.map fun z => z.natAbs.size + 1).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 : a.natAbs < 2 ^ a.natAbs.size := Nat.lt_size_self _
    rw [pow_add, pow_add, pow_one]
    generalize 2 ^ (l.map fun z => z.natAbs.size + 1).sum = F at ih ⊢
    generalize 2 ^ a.natAbs.size = P at h1 ⊢
    have hF : 1 ≤ F := by omega
    have hP : 1 ≤ P := by omega
    have e1 : P ≤ P * F := Nat.le_mul_of_pos_right _ hF
    have e2 : F ≤ P * F := Nat.le_mul_of_pos_left _ hP
    nlinarith [e1, e2]

lemma len_encNats_le (B : ℕ) (xs : List ℕ) (h : ∀ v ∈ xs, v < 2 ^ B) :
    (encNats xs).length ≤ xs.length * (B + 1) := by
  induction xs with
  | nil => simp [encNats]
  | cons a l ih =>
    simp only [encNats, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    have ha : a.size ≤ B := Nat.size_le.2 (h a (by simp))
    have := ih (fun v hv => h v (by simp [hv]))
    rw [len_encNat]; nlinarith

lemma rank_exists {α : Type} [Fintype α] (ord : α → ℕ) : ∃ ord' : α → ℕ,
    (∀ a b, ord a < ord b → ord' a < ord' b) ∧ ∀ a, ord' a < Fintype.card α := by
  classical
  refine ⟨fun a => (Finset.univ.filter fun j => ord j < ord a).card, ?_, ?_⟩
  · intro a b hab
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨a, by simp [hab], by simp⟩
    · intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
      omega
  · intro a
    apply lt_of_lt_of_le (Finset.card_lt_card ?_) (le_of_eq Finset.card_univ)
    rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
    exact ⟨a, Finset.mem_univ _, by simp⟩

end D0bfN2

namespace D0bf

open CumInstance D0bfN2

/-- Certificate relation: `y` lists natural start times `S` and a numbering `ord`. -/
def Rchk (acyc : Bool) (w y : List BSym) : Prop :=
  ∃ x : CumInstance, x.WellFormed ∧ w = x.encode ∧
    ∃ S ord : Fin (x.n + 2) → ℕ, y = encNats (List.ofFn S ++ List.ofFn ord) ∧
      x.Feasible (fun i => (S i : ℝ)) ∧ (acyc = true → ∀ e ∈ x.E, ord e.1 < ord e.2)

def Cof (acyc : Bool) : CumInstance → Prop :=
  if acyc then CumInstance.IsAcyclic else fun _ => True

/-- N2: integral, polynomially bounded certificates. -/
theorem N2_certificate (acyc : Bool) : ∃ k : ℕ, ∀ w : List BSym,
    w ∈ cumFeasLang (Cof acyc) ↔ ∃ y : List BSym, y.length ≤ w.length ^ k ∧ Rchk acyc w y := by
  refine ⟨4, fun w => ⟨?_, ?_⟩⟩
  · rintro ⟨x, hwf, hC, ⟨S, hS⟩, rfl⟩
    obtain ⟨S', hS', hb⟩ :=
      exists_bounded x _ (floor_feasible x S hS) (Dc x) (hpDc x) (hδDc x)
    obtain ⟨ord, hord⟩ : ∃ ord : Fin (x.n + 2) → ℕ,
        acyc = true → ∀ e ∈ x.E, ord e.1 < ord e.2 := by
      cases acyc
      · exact ⟨fun _ => 0, by simp⟩
      · obtain ⟨o, ho⟩ : x.IsAcyclic := by simpa [Cof] using hC
        exact ⟨o, fun _ => ho⟩
    obtain ⟨ord', hmono, hlt⟩ := rank_exists ord
    simp only [Fintype.card_fin] at hlt
    refine ⟨encNats (List.ofFn S' ++ List.ofFn ord'), ?_, x, hwf, rfl, S', ord', rfl, hS', ?_⟩
    · set L := x.encode.length with hL
      have hsum := len_encInts x.code
      have hpow := one_add_sum_le x.code
      have hlen := length_le_sum x.code
      have hDc : Dc x ≤ 2 ^ L := by
        unfold Dc
        exact le_trans hpow (Nat.pow_le_pow_right (by norm_num) hsum)
      have hcode : x.n + 2 ≤ x.code.length := by
        have : (List.ofFn fun i => (x.p i : ℤ)).length ≤ x.code.length := by
          unfold CumInstance.code
          simp only [List.length_append]
          omega
        simp only [List.length_ofFn] at this
        exact this
      have hn : x.n + 2 ≤ L := by
        have : x.encode.length = (encInts x.code).length := rfl
        omega
      have hL2 : L < 2 ^ L := Nat.lt_two_pow_self
      have h2L : 2 ^ (2 * L) = 2 ^ L * 2 ^ L := by rw [two_mul, pow_add]
      have hB : ∀ v ∈ List.ofFn S' ++ List.ofFn ord', v < 2 ^ (2 * L) := by
        intro v hv
        simp only [List.mem_append, List.mem_ofFn] at hv
        rw [h2L]
        rcases hv with ⟨i, rfl⟩ | ⟨i, rfl⟩
        · have := hb i
          have h3 : Dc x * (x.n + 1) ≤ 2 ^ L * L := Nat.mul_le_mul hDc (by omega)
          have h4 : 2 ^ L * L < 2 ^ L * 2 ^ L :=
            Nat.mul_lt_mul_of_pos_left hL2 (by positivity)
          omega
        · have := hlt i
          have h4 : 2 ^ L ≤ 2 ^ L * 2 ^ L := Nat.le_mul_of_pos_right _ (by positivity)
          omega
      have hy := len_encNats_le (2 * L) _ hB
      simp only [List.length_append, List.length_ofFn] at hy
      have hL3 : 3 ≤ L := by have := hwf.1; omega
      have h44 : L ^ 4 = (L * L) * (L * L) := by ring
      rw [h44]
      have h5 : (x.n + 2 + (x.n + 2)) * (2 * L + 1) ≤ (2 * L) * (2 * L + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      have hA : 9 ≤ L * L := Nat.mul_le_mul hL3 hL3
      have hB2 : 9 * (L * L) ≤ (L * L) * (L * L) := Nat.mul_le_mul_right _ hA
      have hC : L ≤ L * L := Nat.le_mul_self L
      have h6 : (2 * L) * (2 * L + 1) ≤ (L * L) * (L * L) := by nlinarith [hA, hB2, hC]
      omega
    · intro h e he
      exact hmono _ _ (hord h e he)
  · rintro ⟨y, -, x, hwf, rfl, S, ord, -, hS, hord⟩
    refine ⟨x, hwf, ?_, ⟨_, hS⟩, rfl⟩
    cases acyc
    · simp [Cof]
    · simp only [Cof, if_true]
      exact ⟨ord, hord rfl⟩

end D0bf

set_option autoImplicit false

/-! N3b for d0bf0960: index layout of `CumInstance.code`. -/

open CookPvsNP ProjSchedTW.Complexity

namespace D0bfN3a

open CumInstance

lemma mem_activeSet (x : CumInstance) (S : Fin (x.n + 2) → ℝ) (k : Fin x.m) (t : ℝ)
    (i : Fin (x.n + 2)) :
    i ∈ x.activeSet S k t ↔
      (x.r i k < 0 ∧ S i ≤ t) ∨ (0 < x.r i k ∧ S i + (x.p i : ℝ) ≤ t) := by
  unfold activeSet
  rw [Finset.mem_filter]
  simp

/-- Inventory of resource `k` at natural time `T` for natural start times `S`. -/
def invN (x : CumInstance) (S : Fin (x.n + 2) → ℕ) (k : Fin x.m) (T : ℕ) : ℤ :=
  ∑ i ∈ Finset.univ.filter (fun i => (x.r i k < 0 ∧ S i ≤ T) ∨ (0 < x.r i k ∧ S i + x.p i ≤ T)),
    x.r i k

lemma inventory_eq_invN_of (x : CumInstance) (S : Fin (x.n + 2) → ℕ) (k : Fin x.m) (t : ℝ)
    (T : ℕ) (h1 : ∀ i, ((S i : ℝ) ≤ t ↔ S i ≤ T))
    (h2 : ∀ i, ((S i : ℝ) + (x.p i : ℝ) ≤ t ↔ S i + x.p i ≤ T)) :
    x.inventory (fun i => (S i : ℝ)) k t = invN x S k T := by
  unfold inventory invN
  congr 1
  ext i
  rw [mem_activeSet, Finset.mem_filter, h1, h2]
  simp

lemma inventory_natCast (x : CumInstance) (S : Fin (x.n + 2) → ℕ) (k : Fin x.m) (T : ℕ) :
    x.inventory (fun i => (S i : ℝ)) k (T : ℝ) = invN x S k T :=
  inventory_eq_invN_of x S k T T (fun i => by exact_mod_cast Iff.rfl)
    (fun i => by exact_mod_cast Iff.rfl)

/-- Event times: all `S i` and `S i + p i`. -/
def events (x : CumInstance) (S : Fin (x.n + 2) → ℕ) : Finset ℕ :=
  Finset.univ.image (fun i => S i) ∪ Finset.univ.image (fun i => S i + x.p i)

lemma inventory_eq_event (x : CumInstance) (S : Fin (x.n + 2) → ℕ) (h0 : S 0 = 0) (k : Fin x.m)
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ T ∈ events x S, x.inventory (fun i => (S i : ℝ)) k t = invN x S k T := by
  classical
  set F : Finset ℕ := (events x S).filter (fun T : ℕ => (T : ℝ) ≤ t) with hF
  have hne : F.Nonempty := ⟨0, by
    rw [hF, Finset.mem_filter]
    refine ⟨?_, by simpa using ht⟩
    unfold events
    exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨0, Finset.mem_univ _, h0⟩)⟩
  set T := F.max' hne with hT
  have hTF : T ∈ F := F.max'_mem hne
  rw [hF, Finset.mem_filter] at hTF
  refine ⟨T, hTF.1, inventory_eq_invN_of x S k t T ?_ ?_⟩
  · intro i
    constructor
    · intro h
      have : S i ∈ F := by
        rw [hF, Finset.mem_filter]
        exact ⟨Finset.mem_union_left _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩), h⟩
      exact F.le_max' _ this
    · intro h
      have : ((S i : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast h
      linarith [hTF.2]
  · intro i
    constructor
    · intro h
      have : S i + x.p i ∈ F := by
        rw [hF, Finset.mem_filter]
        refine ⟨Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩), ?_⟩
        push_cast; exact h
      exact F.le_max' _ this
    · intro h
      have : ((S i + x.p i : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast h
      push_cast at this
      linarith [hTF.2]

/-- N3a: event-time characterization of inventory-feasibility for natural schedules. -/
theorem invFeasible_iff (x : CumInstance) (S : Fin (x.n + 2) → ℕ) (h0 : S 0 = 0) :
    x.InventoryFeasible (fun i => (S i : ℝ)) ↔
      ∀ k, ∀ i, (x.Rlow k ≤ invN x S k (S i) ∧ invN x S k (S i) ≤ x.Rup k) ∧
        (x.Rlow k ≤ invN x S k (S i + x.p i) ∧ invN x S k (S i + x.p i) ≤ x.Rup k) := by
  constructor
  · intro h k i
    have a := h k (S i : ℝ) (by positivity)
    have b := h k ((S i + x.p i : ℕ) : ℝ) (by positivity)
    rw [inventory_natCast] at a b
    exact ⟨a, b⟩
  · intro h k t ht
    obtain ⟨T, hTe, hT⟩ := inventory_eq_event x S h0 k t ht
    rw [hT]
    unfold events at hTe
    rcases Finset.mem_union.1 hTe with hT1 | hT1 <;>
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hT1
    · exact (h k i).1
    · exact (h k i).2

end D0bfN3a


open CookPvsNP ProjSchedTW.Complexity

namespace D0bfN3b

open CumInstance

lemma getD_flatten_uniform {α : Type} (L : ℕ) (d : α) :
    ∀ (l : List (List α)), (∀ y ∈ l, y.length = L) → ∀ (q t : ℕ), t < L →
      l.flatten.getD (q * L + t) d = (l.getD q []).getD t d := by
  intro l
  induction l with
  | nil => intro _ q t _; simp
  | cons y l ih =>
    intro hl q t ht
    have hy : y.length = L := hl y (by simp)
    rw [List.flatten_cons]
    cases q with
    | zero =>
      rw [List.getD_append _ _ _ _ (by rw [hy]; omega)]
      simp
    | succ q =>
      rw [List.getD_append_right _ _ _ _ (by rw [hy]; nlinarith)]
      have : (q + 1) * L + t - y.length = q * L + t := by rw [hy]; ring_nf; omega
      rw [this, ih (fun z hz => hl z (by simp [hz])) q t ht]
      simp

lemma length_flatten_uniform {α : Type} (L : ℕ) :
    ∀ (l : List (List α)), (∀ y ∈ l, y.length = L) → l.flatten.length = l.length * L := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons y l ih =>
    intro hl
    rw [List.flatten_cons, List.length_append, hl y (by simp),
      ih (fun z hz => hl z (by simp [hz]))]
    rw [List.length_cons]; ring

/-- Index layout, with `N = n + 2`. -/
def oA (N : ℕ) : ℕ := 2 + N
def oR (N : ℕ) : ℕ := 2 + N + 2 * (N * N)
def oL (N m : ℕ) : ℕ := oR N + N * m
def oU (N m : ℕ) : ℕ := oL N m + m
def lenC (N m : ℕ) : ℕ := oU N m + m

def arcsL (x : CumInstance) : List (List ℤ) :=
  (List.ofFn fun i => List.ofFn fun j =>
      [if (i, j) ∈ x.E then (1 : ℤ) else 0, x.δ i j]).flatten

def rsL (x : CumInstance) : List (List ℤ) :=
  List.ofFn fun i => List.ofFn fun k => x.r i k

lemma code_eq (x : CumInstance) : x.code =
    [(x.n : ℤ), (x.m : ℤ)] ++ List.ofFn (fun i => (x.p i : ℤ)) ++ (arcsL x).flatten ++
      (rsL x).flatten ++ List.ofFn x.Rlow ++ List.ofFn x.Rup := rfl

lemma arcsL_uniform (x : CumInstance) : ∀ y ∈ arcsL x, y.length = 2 := by
  intro y hy
  unfold arcsL at hy
  rw [List.mem_flatten] at hy
  obtain ⟨l, hl, hyl⟩ := hy
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hl
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hyl
  simp

lemma arcsL_rows (x : CumInstance) :
    ∀ y ∈ (List.ofFn fun i : Fin (x.n + 2) => List.ofFn fun j : Fin (x.n + 2) =>
      [if (i, j) ∈ x.E then (1 : ℤ) else 0, x.δ i j]), y.length = x.n + 2 := by
  intro y hy
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
  simp

lemma rsL_uniform (x : CumInstance) : ∀ y ∈ rsL x, y.length = x.m := by
  intro y hy
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
  simp

lemma len_arcs (x : CumInstance) : (arcsL x).flatten.length = 2 * ((x.n + 2) * (x.n + 2)) := by
  rw [length_flatten_uniform 2 _ (arcsL_uniform x)]
  unfold arcsL
  rw [length_flatten_uniform _ _ (arcsL_rows x)]
  simp; ring

lemma len_rs (x : CumInstance) : (rsL x).flatten.length = (x.n + 2) * x.m := by
  rw [length_flatten_uniform _ _ (rsL_uniform x)]
  simp [rsL]

lemma length_code (x : CumInstance) : x.code.length = lenC (x.n + 2) x.m := by
  rw [code_eq]
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_ofFn,
    len_arcs, len_rs]
  try simp only [lenC, oU, oL, oR]
  try ring

lemma getD_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) :
    (List.ofFn f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

lemma arcsL_getD (x : CumInstance) (i j : Fin (x.n + 2)) :
    (arcsL x).getD (i * (x.n + 2) + j) [] =
      [if (i, j) ∈ x.E then (1 : ℤ) else 0, x.δ i j] := by
  unfold arcsL
  rw [getD_flatten_uniform _ _ _ (arcsL_rows x) _ _ j.isLt, getD_ofFn, getD_ofFn]

lemma code_getD_n (x : CumInstance) : x.code.getD 0 0 = x.n := by
  rw [code_eq]; simp

lemma code_getD_m (x : CumInstance) : x.code.getD 1 0 = x.m := by
  rw [code_eq]; simp

/-- lengths of the prefixes of the code -/
lemma len0 (x : CumInstance) :
    ([(x.n : ℤ), (x.m : ℤ)] ++ List.ofFn (fun i => (x.p i : ℤ))).length = 2 + (x.n + 2) := by
  simp; omega

lemma len1 (x : CumInstance) :
    ([(x.n : ℤ), (x.m : ℤ)] ++ List.ofFn (fun i => (x.p i : ℤ)) ++ (arcsL x).flatten).length =
      oR (x.n + 2) := by
  rw [List.length_append, len0, len_arcs]; simp [oR]

lemma len2 (x : CumInstance) :
    ([(x.n : ℤ), (x.m : ℤ)] ++ List.ofFn (fun i => (x.p i : ℤ)) ++ (arcsL x).flatten ++
      (rsL x).flatten).length = oL (x.n + 2) x.m := by
  rw [List.length_append, len1, len_rs]; rfl

lemma len3 (x : CumInstance) :
    ([(x.n : ℤ), (x.m : ℤ)] ++ List.ofFn (fun i => (x.p i : ℤ)) ++ (arcsL x).flatten ++
      (rsL x).flatten ++ List.ofFn x.Rlow).length = oU (x.n + 2) x.m := by
  rw [List.length_append, len2, List.length_ofFn]; rfl

lemma code_getD_p (x : CumInstance) (i : Fin (x.n + 2)) : x.code.getD (2 + i) 0 = x.p i := by
  rw [code_eq]
  have hi := i.isLt
  have h1 := len1 x
  have h2 := len2 x
  have h3 := len3 x
  have e0 : 2 + (x.n + 2) ≤ oR (x.n + 2) := by simp only [oR]; omega
  have e2 : oR (x.n + 2) ≤ oL (x.n + 2) x.m := by simp [oL]
  have e3 : oL (x.n + 2) x.m ≤ oU (x.n + 2) x.m := by simp [oU]
  rw [List.getD_append _ _ _ _ (by rw [h3]; omega),
    List.getD_append _ _ _ _ (by rw [h2]; omega),
    List.getD_append _ _ _ _ (by rw [h1]; omega),
    List.getD_append _ _ _ _ (by rw [len0]; omega),
    List.getD_append_right _ _ _ _ (by simp)]
  have : 2 + (i : ℕ) - [(x.n : ℤ), (x.m : ℤ)].length = i := by simp
  rw [this, getD_ofFn]

lemma code_getD_arc (x : CumInstance) (i j : Fin (x.n + 2)) (s : ℕ) (hs : s < 2) :
    x.code.getD (oA (x.n + 2) + 2 * (i * (x.n + 2) + j) + s) 0 =
      [if (i, j) ∈ x.E then (1 : ℤ) else 0, x.δ i j].getD s 0 := by
  rw [code_eq]
  have hi := i.isLt
  have hj := j.isLt
  have hij : (i : ℕ) * (x.n + 2) + j < (x.n + 2) * (x.n + 2) := by nlinarith
  have h0 := len0 x
  have h1 := len1 x
  have h2 := len2 x
  have h3 := len3 x
  have e2 : oR (x.n + 2) ≤ oL (x.n + 2) x.m := by simp [oL]
  have e3 : oL (x.n + 2) x.m ≤ oU (x.n + 2) x.m := by simp [oU]
  have hlt : oA (x.n + 2) + 2 * (i * (x.n + 2) + j) + s < oR (x.n + 2) := by
    simp only [oA, oR]; omega
  rw [List.getD_append _ _ _ _ (by rw [h3]; omega),
    List.getD_append _ _ _ _ (by rw [h2]; omega),
    List.getD_append _ _ _ _ (by rw [h1]; omega),
    List.getD_append_right _ _ _ _ (by rw [h0]; simp only [oA]; omega)]
  have : oA (x.n + 2) + 2 * (i * (x.n + 2) + j) + s -
      ([(x.n : ℤ), (x.m : ℤ)] ++ List.ofFn (fun i => (x.p i : ℤ))).length =
      (i * (x.n + 2) + j) * 2 + s := by rw [h0]; simp only [oA]; omega
  rw [this, getD_flatten_uniform _ _ _ (arcsL_uniform x) _ _ hs, arcsL_getD]

lemma code_getD_ind (x : CumInstance) (i j : Fin (x.n + 2)) :
    x.code.getD (oA (x.n + 2) + 2 * (i * (x.n + 2) + j)) 0 =
      if (i, j) ∈ x.E then (1 : ℤ) else 0 := by
  have := code_getD_arc x i j 0 (by norm_num)
  simpa using this

lemma code_getD_δ (x : CumInstance) (i j : Fin (x.n + 2)) :
    x.code.getD (oA (x.n + 2) + 2 * (i * (x.n + 2) + j) + 1) 0 = x.δ i j := by
  have := code_getD_arc x i j 1 (by norm_num)
  simpa using this

lemma code_getD_r (x : CumInstance) (i : Fin (x.n + 2)) (k : Fin x.m) :
    x.code.getD (oR (x.n + 2) + (i * x.m + k)) 0 = x.r i k := by
  rw [code_eq]
  have hi := i.isLt
  have hk := k.isLt
  have hik : (i : ℕ) * x.m + k < (x.n + 2) * x.m := by nlinarith
  have h1 := len1 x
  have h2 := len2 x
  have h3 := len3 x
  have e3 : oL (x.n + 2) x.m ≤ oU (x.n + 2) x.m := by simp [oU]
  have hlt : oR (x.n + 2) + (i * x.m + k) < oL (x.n + 2) x.m := by simp only [oL]; omega
  rw [List.getD_append _ _ _ _ (by rw [h3]; omega),
    List.getD_append _ _ _ _ (by rw [h2]; omega),
    List.getD_append_right _ _ _ _ (by rw [h1]; omega)]
  have : oR (x.n + 2) + (i * x.m + k) -
      ([(x.n : ℤ), (x.m : ℤ)] ++ List.ofFn (fun i => (x.p i : ℤ)) ++ (arcsL x).flatten).length =
      i * x.m + k := by rw [h1]; omega
  rw [this, getD_flatten_uniform _ _ _ (rsL_uniform x) _ _ hk]
  unfold rsL
  rw [getD_ofFn, getD_ofFn]

lemma code_getD_low (x : CumInstance) (k : Fin x.m) :
    x.code.getD (oL (x.n + 2) x.m + k) 0 = x.Rlow k := by
  rw [code_eq]
  have hk := k.isLt
  have h2 := len2 x
  have h3 := len3 x
  rw [List.getD_append _ _ _ _ (by rw [h3]; simp only [oU]; omega),
    List.getD_append_right _ _ _ _ (by rw [h2]; omega)]
  have : oL (x.n + 2) x.m + k - ([(x.n : ℤ), (x.m : ℤ)] ++ List.ofFn (fun i => (x.p i : ℤ)) ++
      (arcsL x).flatten ++ (rsL x).flatten).length = k := by rw [h2]; omega
  rw [this, getD_ofFn]

lemma code_getD_up (x : CumInstance) (k : Fin x.m) :
    x.code.getD (oU (x.n + 2) x.m + k) 0 = x.Rup k := by
  rw [code_eq]
  have h3 := len3 x
  rw [List.getD_append_right _ _ _ _ (by rw [h3]; omega)]
  have : oU (x.n + 2) x.m + k - ([(x.n : ℤ), (x.m : ℤ)] ++ List.ofFn (fun i => (x.p i : ℤ)) ++
      (arcsL x).flatten ++ (rsL x).flatten ++ List.ofFn x.Rlow).length = k := by rw [h3]; omega
  rw [this, getD_ofFn]

/-! ## The Boolean-style specification over the decoded lists -/

def gi (c : List ℤ) (k : ℕ) : ℤ := c.getD k 0
def gd (d : List ℕ) (k : ℕ) : ℕ := d.getD k 0
def aIdx (N i j : ℕ) : ℕ := oA N + 2 * (i * N + j)

/-- inventory at natural time `T`, read off the code `c` and the start times `d`. -/
def invC (c : List ℤ) (d : List ℕ) (N m k T : ℕ) : ℤ :=
  ∑ i ∈ Finset.range N,
    if (gi c (oR N + (i * m + k)) < 0 ∧ gd d i ≤ T) ∨
        (0 < gi c (oR N + (i * m + k)) ∧ gd d i + (gi c (2 + i)).toNat ≤ T)
      then gi c (oR N + (i * m + k)) else 0

def GoodNM (acyc : Bool) (c : List ℤ) (d : List ℕ) (n m : ℕ) : Prop :=
  c.length = lenC (n + 2) m ∧ d.length = 2 * (n + 2) ∧
  (∀ i < n + 2, 0 ≤ gi c (2 + i)) ∧
  (∀ i < n + 2, ∀ j < n + 2, gi c (aIdx (n + 2) i j) = 0 ∨ gi c (aIdx (n + 2) i j) = 1) ∧
  gi c 2 = 0 ∧ gi c (2 + (n + 1)) = 0 ∧
  (∀ i < n + 2, gi c (aIdx (n + 2) i i) = 0) ∧
  (∀ k < m, gi c (oL (n + 2) m + k) ≤ gi c (oU (n + 2) m + k)) ∧
  (∀ k < m, gi c (oL (n + 2) m + k) ≤ ∑ i ∈ Finset.range (n + 2), gi c (oR (n + 2) + (i * m + k)) ∧
     ∑ i ∈ Finset.range (n + 2), gi c (oR (n + 2) + (i * m + k)) ≤ gi c (oU (n + 2) m + k)) ∧
  gd d 0 = 0 ∧
  (∀ i < n + 2, ∀ j < n + 2, gi c (aIdx (n + 2) i j) = 1 →
     gi c (aIdx (n + 2) i j + 1) ≤ (gd d j : ℤ) - gd d i) ∧
  (∀ k < m, ∀ i < n + 2,
     (gi c (oL (n + 2) m + k) ≤ invC c d (n + 2) m k (gd d i) ∧
        invC c d (n + 2) m k (gd d i) ≤ gi c (oU (n + 2) m + k)) ∧
     (gi c (oL (n + 2) m + k) ≤ invC c d (n + 2) m k (gd d i + (gi c (2 + i)).toNat) ∧
        invC c d (n + 2) m k (gd d i + (gi c (2 + i)).toNat) ≤ gi c (oU (n + 2) m + k))) ∧
  (acyc = true → ∀ i < n + 2, ∀ j < n + 2, gi c (aIdx (n + 2) i j) = 1 →
     gd d (n + 2 + i) < gd d (n + 2 + j))

/-- The decidable specification checked by the stack program. -/
def Good (acyc : Bool) (c : List ℤ) (d : List ℕ) : Prop :=
  1 ≤ gi c 0 ∧ 0 ≤ gi c 1 ∧ GoodNM acyc c d (gi c 0).toNat (gi c 1).toNat

lemma gd_S {N : ℕ} (S ord : Fin N → ℕ) (i : ℕ) (hi : i < N) :
    gd (List.ofFn S ++ List.ofFn ord) i = S ⟨i, hi⟩ := by
  unfold gd
  rw [List.getD_append _ _ _ _ (by simpa using hi)]
  exact getD_ofFn S ⟨i, hi⟩ 0

lemma gd_ord {N : ℕ} (S ord : Fin N → ℕ) (i : ℕ) (hi : i < N) :
    gd (List.ofFn S ++ List.ofFn ord) (N + i) = ord ⟨i, hi⟩ := by
  unfold gd
  rw [List.getD_append_right _ _ _ _ (by simp)]
  have : N + i - (List.ofFn S).length = i := by simp
  rw [this]
  exact getD_ofFn ord ⟨i, hi⟩ 0

lemma invC_code (x : CumInstance) (S ord : Fin (x.n + 2) → ℕ) (k : ℕ) (hk : k < x.m) (T : ℕ) :
    invC x.code (List.ofFn S ++ List.ofFn ord) (x.n + 2) x.m k T =
      D0bfN3a.invN x S ⟨k, hk⟩ T := by
  unfold invC D0bfN3a.invN
  rw [Finset.sum_filter, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hr : gi x.code (oR (x.n + 2) + (i * x.m + k)) = x.r i ⟨k, hk⟩ :=
    code_getD_r x i ⟨k, hk⟩
  have hp : gi x.code (2 + i) = x.p i := code_getD_p x i
  rw [hr, hp, gd_S S ord i i.isLt, Int.toNat_natCast]

lemma sum_code (x : CumInstance) (k : ℕ) (hk : k < x.m) :
    ∑ i ∈ Finset.range (x.n + 2), gi x.code (oR (x.n + 2) + (i * x.m + k)) =
      ∑ i, x.r i ⟨k, hk⟩ := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl (fun i _ => code_getD_r x i ⟨k, hk⟩)

theorem good_code_iff (acyc : Bool) (x : CumInstance) (S ord : Fin (x.n + 2) → ℕ) :
    Good acyc x.code (List.ofFn S ++ List.ofFn ord) ↔
      x.WellFormed ∧ S 0 = 0 ∧ (∀ e ∈ x.E, x.δ e.1 e.2 ≤ (S e.2 : ℤ) - S e.1) ∧
      (∀ k, ∀ i, (x.Rlow k ≤ D0bfN3a.invN x S k (S i) ∧ D0bfN3a.invN x S k (S i) ≤ x.Rup k) ∧
        (x.Rlow k ≤ D0bfN3a.invN x S k (S i + x.p i) ∧
          D0bfN3a.invN x S k (S i + x.p i) ≤ x.Rup k)) ∧
      (acyc = true → ∀ e ∈ x.E, ord e.1 < ord e.2) := by
  have h0 : gi x.code 0 = x.n := code_getD_n x
  have h1 : gi x.code 1 = x.m := code_getD_m x
  have hp : ∀ i (hi : i < x.n + 2), gi x.code (2 + i) = x.p ⟨i, hi⟩ :=
    fun i hi => code_getD_p x ⟨i, hi⟩
  have hind : ∀ i (hi : i < x.n + 2) j (hj : j < x.n + 2), gi x.code (aIdx (x.n + 2) i j) =
      if ((⟨i, hi⟩ : Fin (x.n + 2)), (⟨j, hj⟩ : Fin (x.n + 2))) ∈ x.E then 1 else 0 :=
    fun i hi j hj => code_getD_ind x ⟨i, hi⟩ ⟨j, hj⟩
  have hδ : ∀ i (hi : i < x.n + 2) j (hj : j < x.n + 2),
      gi x.code (aIdx (x.n + 2) i j + 1) = x.δ ⟨i, hi⟩ ⟨j, hj⟩ :=
    fun i hi j hj => code_getD_δ x ⟨i, hi⟩ ⟨j, hj⟩
  have hlo : ∀ k (hk : k < x.m), gi x.code (oL (x.n + 2) x.m + k) = x.Rlow ⟨k, hk⟩ :=
    fun k hk => code_getD_low x ⟨k, hk⟩
  have hup : ∀ k (hk : k < x.m), gi x.code (oU (x.n + 2) x.m + k) = x.Rup ⟨k, hk⟩ :=
    fun k hk => code_getD_up x ⟨k, hk⟩
  have hS : ∀ i (hi : i < x.n + 2), gd (List.ofFn S ++ List.ofFn ord) i = S ⟨i, hi⟩ :=
    gd_S S ord
  have hO : ∀ i (hi : i < x.n + 2),
      gd (List.ofFn S ++ List.ofFn ord) (x.n + 2 + i) = ord ⟨i, hi⟩ := gd_ord S ord
  have e0 : (0 : Fin (x.n + 2)) = ⟨0, by omega⟩ := Fin.ext (by simp)
  have eL : Fin.last (x.n + 1) = ⟨x.n + 1, by omega⟩ := Fin.ext (by simp)
  unfold Good GoodNM
  rw [h0, h1]
  simp only [Int.toNat_natCast]
  constructor
  · rintro ⟨hn1, -, -, -, -, -, hp0, hpl, hloop, hRR, hRs, hS0, harc, hinv, hac⟩
    refine ⟨⟨by exact_mod_cast hn1, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · have e := hp 0 (by omega)
      rw [Nat.add_zero, hp0] at e
      rw [e0]; exact_mod_cast e.symm
    · have e := hp (x.n + 1) (by omega)
      rw [hpl] at e
      rw [eL]; exact_mod_cast e.symm
    · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ he heq
      simp only [Fin.mk.injEq] at heq
      subst heq
      have e := hloop i hi
      rw [hind i hi i hi, if_pos he] at e
      exact one_ne_zero e
    · rintro ⟨k, hk⟩
      have e := hRR k hk
      rwa [hlo k hk, hup k hk] at e
    · rintro ⟨k, hk⟩
      have e := hRs k hk
      rwa [hlo k hk, hup k hk, sum_code x k hk] at e
    · have e := hS 0 (by omega)
      rw [hS0] at e
      rw [e0]; exact e.symm
    · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ he
      have e := harc i hi j hj (by rw [hind i hi j hj, if_pos he])
      rwa [hδ i hi j hj, hS i hi, hS j hj] at e
    · rintro ⟨k, hk⟩ ⟨i, hi⟩
      have e := hinv k hk i hi
      rwa [invC_code x S ord k hk, invC_code x S ord k hk, hlo k hk, hup k hk, hS i hi,
        hp i hi, Int.toNat_natCast] at e
    · intro ha
      rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ he
      have e := hac ha i hi j hj (by rw [hind i hi j hj, if_pos he])
      rwa [hO i hi, hO j hj] at e
  · rintro ⟨⟨hn1, hp0, hpl, hloop, hRR, hRs⟩, hS0, harc, hinv, hac⟩
    refine ⟨by exact_mod_cast hn1, by positivity, length_code x, by simp; ring, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi; rw [hp i hi]; positivity
    · intro i hi j hj; rw [hind i hi j hj]; split_ifs <;> simp
    · have e := hp 0 (by omega)
      rw [Nat.add_zero] at e
      rw [e, ← e0, hp0]; rfl
    · rw [hp (x.n + 1) (by omega), ← eL, hpl]; rfl
    · intro i hi
      rw [hind i hi i hi, if_neg]
      intro he
      exact hloop _ he rfl
    · intro k hk; rw [hlo k hk, hup k hk]; exact hRR _
    · intro k hk; rw [hlo k hk, hup k hk, sum_code x k hk]; exact hRs _
    · rw [hS 0 (by omega), ← e0, hS0]
    · intro i hi j hj h
      rw [hind i hi j hj] at h
      split_ifs at h with he
      · rw [hδ i hi j hj, hS i hi, hS j hj]; exact harc _ he
      · exact absurd h (by norm_num)
    · intro k hk i hi
      rw [invC_code x S ord k hk, invC_code x S ord k hk, hlo k hk, hup k hk, hS i hi,
        hp i hi, Int.toNat_natCast]
      exact hinv _ _
    · intro ha i hi j hj h
      rw [hind i hi j hj] at h
      split_ifs at h with he
      · rw [hO i hi, hO j hj]; exact hac ha _ he
      · exact absurd h (by norm_num)

/-! ## Decoding: every `Good` pair comes from an instance and a schedule -/

def decX (c : List ℤ) : CumInstance where
  n := (gi c 0).toNat
  m := (gi c 1).toNat
  p i := (gi c (2 + i)).toNat
  E := Finset.univ.filter fun e => gi c (aIdx ((gi c 0).toNat + 2) e.1 e.2) = 1
  δ i j := gi c (aIdx ((gi c 0).toNat + 2) i j + 1)
  r i k := gi c (oR ((gi c 0).toNat + 2) + (i * (gi c 1).toNat + k))
  Rlow k := gi c (oL ((gi c 0).toNat + 2) (gi c 1).toNat + k)
  Rup k := gi c (oU ((gi c 0).toNat + 2) (gi c 1).toNat + k)

lemma decX_code (c : List ℤ) (h0 : 0 ≤ gi c 0) (h1 : 0 ≤ gi c 1)
    (hlen : c.length = lenC ((gi c 0).toNat + 2) (gi c 1).toNat)
    (hp : ∀ i < (gi c 0).toNat + 2, 0 ≤ gi c (2 + i))
    (hA : ∀ i < (gi c 0).toNat + 2, ∀ j < (gi c 0).toNat + 2,
      gi c (aIdx ((gi c 0).toNat + 2) i j) = 0 ∨ gi c (aIdx ((gi c 0).toNat + 2) i j) = 1) :
    (decX c).code = c := by
  set X := decX c with hX
  have hn : X.n = (gi c 0).toNat := rfl
  have hm : X.m = (gi c 1).toNat := rfl
  have hlen' : c.length = lenC (X.n + 2) X.m := hlen
  have hA' : ∀ i < X.n + 2, ∀ j < X.n + 2,
      gi c (aIdx (X.n + 2) i j) = 0 ∨ gi c (aIdx (X.n + 2) i j) = 1 := hA
  have hp' : ∀ i < X.n + 2, 0 ≤ gi c (2 + i) := hp
  have hEX : ∀ i j : Fin (X.n + 2), (i, j) ∈ X.E ↔ gi c (aIdx (X.n + 2) i j) = 1 := by
    intro i j
    change (i, j) ∈ Finset.filter (fun e : Fin (X.n + 2) × Fin (X.n + 2) =>
      gi c (aIdx (X.n + 2) e.1 e.2) = 1) Finset.univ ↔ _
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hL : X.code.length = c.length := by rw [length_code, hlen']
  apply List.ext_getElem hL
  intro t ht1 ht2
  rw [← List.getD_eq_getElem _ 0 ht1, ← List.getD_eq_getElem _ 0 ht2]
  have ht : t < lenC (X.n + 2) X.m := hlen' ▸ ht2
  change X.code.getD t 0 = gi c t
  rcases Nat.lt_or_ge t 2 with h | h
  · interval_cases t
    · rw [code_getD_n, hn]; exact Int.toNat_of_nonneg h0
    · rw [code_getD_m, hm]; exact Int.toNat_of_nonneg h1
  rcases Nat.lt_or_ge t (2 + (X.n + 2)) with h' | h'
  · obtain ⟨i, rfl⟩ : ∃ i, t = 2 + i := ⟨t - 2, by omega⟩
    have hi : i < X.n + 2 := by omega
    refine (code_getD_p X ⟨i, hi⟩).trans ?_
    exact Int.toNat_of_nonneg (hp' i hi)
  rcases Nat.lt_or_ge t (oR (X.n + 2)) with h'' | h''
  · have hN : 0 < X.n + 2 := by omega
    obtain ⟨i, j, s, hi, hj, hs, rfl⟩ : ∃ i j s, i < X.n + 2 ∧ j < X.n + 2 ∧ s < 2 ∧
        t = oA (X.n + 2) + 2 * (i * (X.n + 2) + j) + s := by
      have e1 := Nat.div_add_mod (t - oA (X.n + 2)) 2
      have e2 := Nat.div_add_mod' ((t - oA (X.n + 2)) / 2) (X.n + 2)
      have hq : (t - oA (X.n + 2)) / 2 < (X.n + 2) * (X.n + 2) := by
        simp only [oA, oR] at h' h'' ⊢; omega
      refine ⟨(t - oA (X.n + 2)) / 2 / (X.n + 2), (t - oA (X.n + 2)) / 2 % (X.n + 2),
        (t - oA (X.n + 2)) % 2, (Nat.div_lt_iff_lt_mul hN).2 hq, Nat.mod_lt _ hN,
        Nat.mod_lt _ (by norm_num), ?_⟩
      have hoA : oA (X.n + 2) = 2 + (X.n + 2) := rfl
      omega
    have e := code_getD_arc X ⟨i, hi⟩ ⟨j, hj⟩ s hs
    refine e.trans ?_
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
    · simp only [List.getD_cons_zero]
      split_ifs with hm'
      · exact ((hEX _ _).1 hm').symm
      · rcases hA' i hi j hj with h3 | h3
        · exact h3.symm
        · exact absurd ((hEX ⟨i, hi⟩ ⟨j, hj⟩).2 h3) hm'
    · simp only [List.getD_cons_succ, List.getD_cons_zero]
      rfl
  rcases Nat.lt_or_ge t (oL (X.n + 2) X.m) with h3 | h3
  · have hM : 0 < X.m := by
      rcases Nat.eq_zero_or_pos X.m with h0' | h0'
      · simp only [oL, h0', Nat.mul_zero, Nat.add_zero] at h3; omega
      · exact h0'
    obtain ⟨i, k, hi, hk, rfl⟩ : ∃ i k, i < X.n + 2 ∧ k < X.m ∧
        t = oR (X.n + 2) + (i * X.m + k) := by
      have e2 := Nat.div_add_mod' (t - oR (X.n + 2)) X.m
      have hq : t - oR (X.n + 2) < (X.n + 2) * X.m := by simp only [oL] at h3; omega
      refine ⟨(t - oR (X.n + 2)) / X.m, (t - oR (X.n + 2)) % X.m,
        (Nat.div_lt_iff_lt_mul hM).2 hq, Nat.mod_lt _ hM, ?_⟩
      omega
    exact (code_getD_r X ⟨i, hi⟩ ⟨k, hk⟩).trans rfl
  rcases Nat.lt_or_ge t (oU (X.n + 2) X.m) with h4 | h4
  · obtain ⟨k, rfl⟩ : ∃ k, t = oL (X.n + 2) X.m + k := ⟨t - oL (X.n + 2) X.m, by omega⟩
    have hk : k < X.m := by simp only [oU] at h4; omega
    exact (code_getD_low X ⟨k, hk⟩).trans rfl
  · obtain ⟨k, rfl⟩ : ∃ k, t = oU (X.n + 2) X.m + k := ⟨t - oU (X.n + 2) X.m, by omega⟩
    have hk : k < X.m := by simp only [lenC] at ht; omega
    exact (code_getD_up X ⟨k, hk⟩).trans rfl

lemma d_eq (d : List ℕ) (N : ℕ) (hd : d.length = 2 * N) :
    d = List.ofFn (fun i : Fin N => gd d i) ++ List.ofFn (fun i : Fin N => gd d (N + i)) := by
  have hL : d.length = (List.ofFn (fun i : Fin N => gd d i) ++
      List.ofFn (fun i : Fin N => gd d (N + i))).length := by simp; omega
  apply List.ext_getElem hL
  intro t h1 h2
  rw [← List.getD_eq_getElem _ 0 h1, ← List.getD_eq_getElem _ 0 h2]
  change gd d t = gd _ t
  rcases Nat.lt_or_ge t N with h | h
  · rw [gd_S _ _ t h]
  · obtain ⟨i, rfl⟩ : ∃ i, t = N + i := ⟨t - N, by omega⟩
    rw [gd_ord _ _ i (by omega)]

/-- Real-valued feasibility of a natural schedule in event-time form (via N3a). -/
lemma feasible_iff_nat (x : CumInstance) (S : Fin (x.n + 2) → ℕ) :
    x.Feasible (fun i => (S i : ℝ)) ↔
      S 0 = 0 ∧ (∀ e ∈ x.E, x.δ e.1 e.2 ≤ (S e.2 : ℤ) - S e.1) ∧
      (∀ k, ∀ i, (x.Rlow k ≤ D0bfN3a.invN x S k (S i) ∧ D0bfN3a.invN x S k (S i) ≤ x.Rup k) ∧
        (x.Rlow k ≤ D0bfN3a.invN x S k (S i + x.p i) ∧
          D0bfN3a.invN x S k (S i + x.p i) ≤ x.Rup k)) := by
  unfold Feasible TimeFeasible
  constructor
  · rintro ⟨⟨h0, -, harc⟩, hinv⟩
    have h0' : S 0 = 0 := by simp only at h0; exact_mod_cast h0
    refine ⟨h0', fun e he => ?_, (D0bfN3a.invFeasible_iff x S h0').1 hinv⟩
    have h2 := harc e he
    simp only at h2
    have h3 : ((x.δ e.1 e.2 : ℤ) : ℝ) ≤ (((S e.2 : ℤ) - (S e.1 : ℤ) : ℤ) : ℝ) := by
      push_cast; exact h2
    exact Int.cast_le.1 h3
  · rintro ⟨h0, harc, hinv⟩
    refine ⟨⟨by simp [h0], fun i => by positivity, fun e he => ?_⟩,
      (D0bfN3a.invFeasible_iff x S h0).2 hinv⟩
    have h3 := (Int.cast_le (R := ℝ)).2 (harc e he)
    push_cast at h3
    simpa using h3

end D0bfN3b


namespace D0bfN3b

/-- N3b: membership in the checking language, as a specification over decoded number lists. -/
theorem checkLang_iff (acyc : Bool) (u : List (Option (BSym ⊕ BSym))) :
    u ∈ checkLang (D0bf.Rchk acyc) ↔ ∃ c : List ℤ, ∃ d : List ℕ,
      u = (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr) ∧
        Good acyc c d := by
  constructor
  · rintro ⟨w, y, ⟨x, hwf, rfl, S, ord, rfl, hF, hac⟩, rfl⟩
    obtain ⟨h0, harc, hinv⟩ := (feasible_iff_nat x S).1 hF
    exact ⟨x.code, List.ofFn S ++ List.ofFn ord, rfl,
      (good_code_iff acyc x S ord).2 ⟨hwf, h0, harc, hinv, hac⟩⟩
  · rintro ⟨c, d, rfl, hG⟩
    have hG2 := hG
    obtain ⟨g0, g1, hlen, hdl, hp, hA, -⟩ := hG2
    have hx := decX_code c (by omega) g1 hlen hp hA
    set x := decX c with hxdef
    have hd := d_eq d (x.n + 2) hdl
    set S : Fin (x.n + 2) → ℕ := fun i => gd d i with hSdef
    set ord : Fin (x.n + 2) → ℕ := fun i => gd d (x.n + 2 + i) with hOdef
    have hG' : Good acyc x.code (List.ofFn S ++ List.ofFn ord) := by
      rw [hx, ← hd]; exact hG
    obtain ⟨hwf, h0, harc, hinv, hac⟩ := (good_code_iff acyc x S ord).1 hG'
    refine ⟨encInts c, encNats d, ⟨x, hwf, ?_, S, ord, ?_,
      (feasible_iff_nat x S).2 ⟨h0, harc, hinv⟩, hac⟩, rfl⟩
    · rw [CumInstance.encode, hx]
    · rw [← hd]

end D0bfN3b
open CookPvsNP ProjSchedTW.Complexity

namespace D0bfR

lemma encInts_cons (z : ℤ) (l : List ℤ) : encInts (z :: l) = encInt z ++ encInts l := by
  simp [encInts]


def bval' : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (bval' l)

lemma bval'_bits (n : ℕ) : bval' (Nat.bits n) = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bval']
  | bit b n hn ih => rw [Nat.bits_append_bit _ _ hn]; simp [bval', ih]

lemma sep_split_inj : ∀ {u u' R R' : List BSym}, BSym.sep ∉ u → BSym.sep ∉ u' →
    u ++ BSym.sep :: R = u' ++ BSym.sep :: R' → u = u' ∧ R = R' := by
  intro u
  induction u with
  | nil =>
    intro u' R R' _ hu' h
    rcases u' with _ | ⟨a, u'⟩
    · simpa using h
    · simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hu'
  | cons a u ih =>
    intro u' R R' hu hu' h
    rcases u' with _ | ⟨b, u'⟩
    · simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hu
    · simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := ih (fun hm => hu (List.mem_cons_of_mem _ hm))
        (fun hm => hu' (List.mem_cons_of_mem _ hm)) h.2
      exact ⟨by rw [h.1, h1], h2⟩

def digU (z : ℤ) : List BSym :=
  (if z < 0 then [BSym.minus] else []) ++
    (Nat.bits z.natAbs).map (fun b => if b then BSym.one else BSym.zero)

lemma encInt_eq_digU (z : ℤ) : encInt z = digU z ++ [BSym.sep] := by
  simp [encInt, encNat, digU]

lemma sep_not_mem_digU (z : ℤ) : BSym.sep ∉ digU z := by
  simp only [digU, List.mem_append, List.mem_map, not_or]
  constructor
  · split_ifs <;> simp
  · rintro ⟨b, -, hb⟩; cases b <;> simp at hb

lemma map_bits_inj {a b : List Bool}
    (h : a.map (fun b => if b then BSym.one else BSym.zero) =
      b.map (fun b => if b then BSym.one else BSym.zero)) : a = b := by
  refine List.map_injective_iff.mpr ?_ h
  intro x y hxy; cases x <;> cases y <;> simp_all

lemma digU_inj {z z' : ℤ} (h : digU z = digU z') : z = z' := by
  have key : ∀ {z z' : ℤ}, digU z = digU z' → (z < 0 ↔ z' < 0) := by
    intro z z' h
    by_contra hne
    simp only [digU] at h
    rcases lt_or_ge z 0 with hz | hz <;> rcases lt_or_ge z' 0 with hz' | hz'
    · exact hne (iff_of_true hz hz')
    · rw [if_pos hz, if_neg (not_lt.2 hz')] at h
      cases hb : Nat.bits z'.natAbs with
      | nil => rw [hb] at h; simp at h
      | cons c l => rw [hb] at h; cases c <;> simp at h
    · rw [if_neg (not_lt.2 hz), if_pos hz'] at h
      cases hb : Nat.bits z.natAbs with
      | nil => rw [hb] at h; simp at h
      | cons c l => rw [hb] at h; cases c <;> simp at h
    · exact hne (iff_of_false (not_lt.2 hz) (not_lt.2 hz'))
  have hs := key h
  have habs : z.natAbs = z'.natAbs := by
    simp only [digU] at h
    by_cases hz : z < 0
    · rw [if_pos hz, if_pos (hs.1 hz)] at h
      simp only [List.singleton_append, List.cons.injEq, true_and] at h
      rw [← bval'_bits z.natAbs, ← bval'_bits z'.natAbs, map_bits_inj h]
    · rw [if_neg hz, if_neg (fun h' => hz (hs.2 h'))] at h
      simp only [List.nil_append] at h
      rw [← bval'_bits z.natAbs, ← bval'_bits z'.natAbs, map_bits_inj h]
  omega

lemma encInts_inj : ∀ (l l' : List ℤ), encInts l = encInts l' → l = l' := by
  intro l
  induction l with
  | nil =>
    intro l' h
    rcases l' with _ | ⟨z, l'⟩
    · rfl
    · rw [encInts_cons, encInt_eq_digU] at h; simp [encInts] at h
  | cons z l ih =>
    intro l' h
    rcases l' with _ | ⟨z', l'⟩
    · rw [encInts_cons, encInt_eq_digU] at h; simp [encInts] at h
    · rw [encInts_cons, encInts_cons, encInt_eq_digU, encInt_eq_digU] at h
      simp only [List.append_assoc, List.singleton_append] at h
      obtain ⟨h1, h2⟩ := sep_split_inj (sep_not_mem_digU z) (sep_not_mem_digU z') h
      rw [digU_inj h1, ih l' h2]


/-! ## splitting at the unique `none` -/

lemma none_split_inj {α β : Type} : ∀ {w w' : List α} {y y' : List β},
    w.map (some ∘ Sum.inl) ++ (none : Option (α ⊕ β)) :: y.map (some ∘ Sum.inr) =
      w'.map (some ∘ Sum.inl) ++ none :: y'.map (some ∘ Sum.inr) → w = w' ∧ y = y' := by
  intro w
  induction w with
  | nil =>
    intro w' y y' h
    rcases w' with _ | ⟨a, w'⟩
    · simp only [List.map_nil, List.nil_append, List.cons.injEq, true_and] at h
      exact ⟨rfl, List.map_injective_iff.2 (fun a b hab => by
        simpa using hab) h⟩
    · simp at h
  | cons a w ih =>
    intro w' y y' h
    rcases w' with _ | ⟨b, w'⟩
    · simp at h
    · simp only [List.map_cons, List.cons_append, List.cons.injEq, Function.comp_apply,
        Option.some.injEq, Sum.inl.injEq] at h
      obtain ⟨h1, h2⟩ := ih h.2
      exact ⟨by rw [h.1, h1], h2⟩

lemma encNats_eq (d : List ℕ) : encNats d = encInts (d.map (fun k : ℕ => (k : ℤ))) := by
  induction d with
  | nil => rfl
  | cons a d ih =>
    simp only [encNats, List.flatMap_cons, List.map_cons, encInts] at ih ⊢
    rw [ih]
    simp [encInt]

lemma encNats_inj {d d' : List ℕ} (h : encNats d = encNats d') : d = d' := by
  rw [encNats_eq, encNats_eq] at h
  exact (List.map_injective_iff.2 (Nat.cast_injective (R := ℤ))) (encInts_inj _ _ h)

def Glen (c : List ℤ) (d : List ℕ) : Prop :=
  1 ≤ c.getD 0 0 ∧ 0 ≤ c.getD 1 0 ∧
          c.length = 2 + ((c.getD 0 0).toNat + 2) +
            2 * (((c.getD 0 0).toNat + 2) * ((c.getD 0 0).toNat + 2)) +
            ((c.getD 0 0).toNat + 2) * (c.getD 1 0).toNat + (c.getD 1 0).toNat +
            (c.getD 1 0).toNat ∧
          d.length = 2 * ((c.getD 0 0).toNat + 2)

def Gwf (c : List ℤ) (d : List ℕ) : Prop :=
  (∀ i < d.length / 2, 0 ≤ c.getD (2 + i) 0) ∧
            (c.getD 2 0 = 0 ∧ c.getD (2 + (d.length / 2 - 1)) 0 = 0) ∧
            (∀ q < d.length / 2 * (d.length / 2), c.getD (2 + d.length / 2 + 2 * q) 0 = 0 ∨
              c.getD (2 + d.length / 2 + 2 * q) 0 = 1) ∧
            (∀ i < d.length / 2, c.getD (2 + d.length / 2 + 2 * (i * (d.length / 2) + i)) 0 = 0)

def Gtime (c : List ℤ) (d : List ℕ) : Prop :=
  d.getD 0 0 = 0 ∧ ∀ i < d.length / 2, ∀ j < d.length / 2,
            c.getD (2 + d.length / 2 + 2 * (i * (d.length / 2) + j)) 0 = 1 →
              c.getD (2 + d.length / 2 + 2 * (i * (d.length / 2) + j) + 1) 0 ≤
                (d.getD j 0 : ℤ) - d.getD i 0

def Ginv (c : List ℤ) (d : List ℕ) : Prop :=
  ∀ N M : ℕ, N = d.length / 2 →
            M = (c.length - (2 * N * N + N + 2) + (N + 2) - 1) / (N + 2) → ∀ k < M,
            (c.getD (2 + N + 2 * (N * N) + N * M + k) 0 ≤
                ∑ i ∈ Finset.range N, c.getD (2 + N + 2 * (N * N) + (i * M + k)) 0 ∧
              ∑ i ∈ Finset.range N, c.getD (2 + N + 2 * (N * N) + (i * M + k)) 0 ≤
                c.getD (2 + N + 2 * (N * N) + N * M + M + k) 0) ∧
            ∀ i < N, ∀ T : ℕ, (T = d.getD i 0 ∨ T = d.getD i 0 + (c.getD (2 + i) 0).toNat) →
              (c.getD (2 + N + 2 * (N * N) + N * M + k) 0 ≤
                  ∑ j ∈ Finset.range N,
                    (if (c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 < 0 ∧ d.getD j 0 ≤ T) ∨
                        (0 < c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 ∧
                          d.getD j 0 + (c.getD (2 + j) 0).toNat ≤ T)
                      then c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 else 0) ∧
                ∑ j ∈ Finset.range N,
                    (if (c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 < 0 ∧ d.getD j 0 ≤ T) ∨
                        (0 < c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 ∧
                          d.getD j 0 + (c.getD (2 + j) 0).toNat ≤ T)
                      then c.getD (2 + N + 2 * (N * N) + (j * M + k)) 0 else 0) ≤
                  c.getD (2 + N + 2 * (N * N) + N * M + M + k) 0)

def Gac (c : List ℤ) (d : List ℕ) : Prop :=
  ∀ i < d.length / 2, ∀ j < d.length / 2,
            c.getD (2 + d.length / 2 + 2 * (i * (d.length / 2) + j)) 0 = 1 →
              d.getD (d.length / 2 + i) 0 < d.getD (d.length / 2 + j) 0


/-! ## v3 assembly: five stack-program filters over the decoded pair `(c, d)` -/

abbrev A := Option (BSym ⊕ BSym)

def Ew (c : List ℤ) (d : List ℕ) : List A :=
  (encInts c).map (some ∘ Sum.inl) ++ none :: (encNats d).map (some ∘ Sum.inr)

lemma Ew_ne_nil (c : List ℤ) (d : List ℕ) : Ew c d ≠ [] := by simp [Ew]

lemma Ew_inj {c c' : List ℤ} {d d' : List ℕ} (h : Ew c d = Ew c' d') : c = c' ∧ d = d' := by
  obtain ⟨h1, h2⟩ := none_split_inj h
  exact ⟨encInts_inj _ _ h1, encNats_inj h2⟩

/-! ### the index layout under `Glen` -/

lemma arcs_iff (N : ℕ) (P : ℕ → Prop) :
    (∀ q < N * N, P q) ↔ ∀ i < N, ∀ j < N, P (i * N + j) := by
  constructor
  · intro h i hi j hj
    apply h
    calc i * N + j < i * N + N := by omega
      _ = (i + 1) * N := by ring
      _ ≤ N * N := Nat.mul_le_mul_right _ hi
  · intro h q hq
    have hN : 0 < N := by
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · subst h0; simp at hq
      · exact h0
    have := h (q / N) (Nat.div_lt_of_lt_mul hq) (q % N) (Nat.mod_lt _ hN)
    rwa [Nat.div_add_mod'] at this

lemma M_eq (n m L : ℕ)
    (hL : L = 2 + (n + 2) + 2 * ((n + 2) * (n + 2)) + (n + 2) * m + m + m) :
    (L - (2 * (n + 2) * (n + 2) + (n + 2) + 2) + (n + 2 + 2) - 1) / (n + 2 + 2) = m := by
  have e3 : L - (2 * (n + 2) * (n + 2) + (n + 2) + 2) + (n + 2 + 2) - 1 =
      (n + 3) + m * (n + 2 + 2) := by
    have hL' : L = (2 * (n + 2) * (n + 2) + (n + 2) + 2) + m * (n + 2 + 2) := by rw [hL]; ring
    rw [hL', Nat.add_sub_cancel_left]
    exact Nat.sub_eq_of_eq_add (by ring)
  rw [e3, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega), Nat.zero_add]

lemma Glen_of_good {acyc : Bool} {c : List ℤ} {d : List ℕ} (h : D0bfN3b.Good acyc c d) :
    Glen c d :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

set_option maxHeartbeats 1000000 in
lemma good_iff (acyc : Bool) (c : List ℤ) (d : List ℕ) (hl : Glen c d) :
    D0bfN3b.Good acyc c d ↔ Gwf c d ∧ Gtime c d ∧ Ginv c d ∧ (acyc = true → Gac c d) := by
  obtain ⟨h0, h1, hlen, hdl⟩ := hl
  have hN : d.length / 2 = (c.getD 0 0).toNat + 2 := by omega
  have hM := M_eq (c.getD 0 0).toNat (c.getD 1 0).toNat c.length hlen
  unfold D0bfN3b.Good D0bfN3b.GoodNM Gwf Gtime Ginv Gac
  simp only [D0bfN3b.gi, D0bfN3b.gd, D0bfN3b.aIdx, D0bfN3b.oA, D0bfN3b.oR, D0bfN3b.oL,
    D0bfN3b.oU, D0bfN3b.lenC, D0bfN3b.invC, hN]
  set n := (c.getD 0 0).toNat with hn
  set m := (c.getD 1 0).toNat with hm
  have e1 : n + 2 - 1 = n + 1 := by omega
  rw [e1]
  constructor
  · rintro ⟨-, -, -, -, g3, g4, g5a, g5b, g6, -, g8, g9, g10, g11, g12⟩
    refine ⟨⟨g3, ⟨g5a, g5b⟩, (arcs_iff (n + 2) (fun q => c.getD (2 + (n + 2) + 2 * q) 0 = 0 ∨
      c.getD (2 + (n + 2) + 2 * q) 0 = 1)).2 g4, g6⟩, ⟨g9, g10⟩, ?_, g12⟩
    intro N M hN' hM' k hk
    subst hN'
    rw [hM] at hM'
    subst hM'
    refine ⟨g8 k hk, fun i hi T hT => ?_⟩
    rcases hT with rfl | rfl
    · exact (g11 k hk i hi).1
    · exact (g11 k hk i hi).2
  · rintro ⟨⟨w1, ⟨w2, w3⟩, w4, w5⟩, ⟨t1, t2⟩, iv, ac⟩
    have iv' := iv (n + 2) m rfl hM.symm
    refine ⟨h0, h1, hlen, hdl, w1, (arcs_iff (n + 2) (fun q => c.getD (2 + (n + 2) + 2 * q) 0 = 0 ∨
      c.getD (2 + (n + 2) + 2 * q) 0 = 1)).1 w4, w2, w3, w5,
      fun k hk => le_trans (iv' k hk).1.1 (iv' k hk).1.2, fun k hk => (iv' k hk).1, t1, t2,
      fun k hk i hi => ⟨(iv' k hk).2 i hi _ (Or.inl rfl), (iv' k hk).2 i hi _ (Or.inr rfl)⟩, ac⟩

/-! ### the filters -/

open Classical in
noncomputable def filt (P : List A → Prop) (u : List A) : List A := if P u then u else []

lemma filt_filt (P Q : List A → Prop) (u : List A) :
    filt P (filt Q u) = filt (fun v => Q v ∧ P v) u := by
  unfold filt
  by_cases hQ : Q u <;> by_cases hP : P u <;> simp [hQ, hP]

lemma ptc_of_exec {P : List A → Prop}
    (h : ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K) (p : StackProg K A) (ki ko : K) (k : ℕ),
      ∀ u : List A, ∃ s n, n ≤ u.length ^ k + k ∧ p.Exec (fun j => if j = ki then u else []) s n ∧
        s ko = filt P u) : PolyTimeComputable (filt P) := by
  classical
  obtain ⟨K, _, _, p, ki, ko, k, hp⟩ := h
  exact CookPvsNP.stack_program_polytime p ki ko _ k hp

lemma ptc_kill (Q : List A → Prop)
    (h : ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K) (p : StackProg K A) (ki ko : K) (k : ℕ),
      ∀ u : List A, ∃ s n, n ≤ u.length ^ k + k ∧ p.Exec (fun j => if j = ki then u else []) s n ∧
        (Q u → s ko = []) ∧ (¬Q u → s ko = u)) : PolyTimeComputable (filt (fun u => ¬Q u)) := by
  apply ptc_of_exec
  obtain ⟨K, i1, i2, p, ki, ko, k, hp⟩ := h
  refine ⟨K, i1, i2, p, ki, ko, k, fun u => ?_⟩
  obtain ⟨s, n, h1, h2, h3, h4⟩ := hp u
  refine ⟨s, n, h1, h2, ?_⟩
  unfold filt
  by_cases hq : Q u
  · rw [if_neg (not_not.mpr hq)]; exact h3 hq
  · rw [if_pos hq]; exact h4 hq

lemma ptc_keep (Q : List A → Prop)
    (h : ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K) (p : StackProg K A) (ki ko : K) (k : ℕ),
      ∀ u : List A, ∃ s n, n ≤ u.length ^ k + k ∧ p.Exec (fun j => if j = ki then u else []) s n ∧
        (Q u → s ko = u) ∧ (¬Q u → s ko = [])) : PolyTimeComputable (filt Q) := by
  apply ptc_of_exec
  obtain ⟨K, i1, i2, p, ki, ko, k, hp⟩ := h
  refine ⟨K, i1, i2, p, ki, ko, k, fun u => ?_⟩
  obtain ⟨s, n, h1, h2, h3, h4⟩ := hp u
  refine ⟨s, n, h1, h2, ?_⟩
  unfold filt
  by_cases hq : Q u
  · rw [if_pos hq]; exact h3 hq
  · rw [if_neg hq]; exact h4 hq

def Plen (u : List A) : Prop := ∃ c d, u = Ew c d ∧ Glen c d
def Qwf (u : List A) : Prop := ∃ c d, u = Ew c d ∧ ¬Gwf c d
def Qtime (u : List A) : Prop := ∃ c d, u = Ew c d ∧ ¬Gtime c d
def Qinv (u : List A) : Prop := ∃ c d, u = Ew c d ∧ ¬Ginv c d
def Qac (u : List A) : Prop := ∃ c d, u = Ew c d ∧ ¬Gac c d

lemma ptc_len : PolyTimeComputable (filt Plen) :=
  ptc_keep Plen ProjSchedTW.Complexity.cumCheck_len_filter_polytime
lemma ptc_wf : PolyTimeComputable (filt (fun u => ¬Qwf u)) :=
  ptc_kill Qwf ProjSchedTW.Complexity.cumCheck_wf_filter_polytime
lemma ptc_time : PolyTimeComputable (filt (fun u => ¬Qtime u)) :=
  ptc_kill Qtime ProjSchedTW.Complexity.cumCheck_time_filter_polytime
lemma ptc_inv : PolyTimeComputable (filt (fun u => ¬Qinv u)) :=
  ptc_kill Qinv ProjSchedTW.Complexity.cumCheck_inv_filter_polytime
lemma ptc_acyc : PolyTimeComputable (filt (fun u => ¬Qac u)) :=
  ptc_kill Qac ProjSchedTW.Complexity.cumCheck_acyc_filter_polytime

lemma conj_iff (acyc : Bool) (u : List A) :
    (∃ c d, u = Ew c d ∧ D0bfN3b.Good acyc c d) ↔
      Plen u ∧ ¬Qwf u ∧ ¬Qtime u ∧ ¬Qinv u ∧ (acyc = true → ¬Qac u) := by
  constructor
  · rintro ⟨c, d, rfl, hg⟩
    have hl : Glen c d := Glen_of_good hg
    obtain ⟨gw, gt, gi, ga⟩ := (good_iff acyc c d hl).1 hg
    refine ⟨⟨c, d, rfl, hl⟩, ?_, ?_, ?_, fun ha => ?_⟩
    · rintro ⟨c', d', he, hn⟩; obtain ⟨rfl, rfl⟩ := Ew_inj he; exact hn gw
    · rintro ⟨c', d', he, hn⟩; obtain ⟨rfl, rfl⟩ := Ew_inj he; exact hn gt
    · rintro ⟨c', d', he, hn⟩; obtain ⟨rfl, rfl⟩ := Ew_inj he; exact hn gi
    · rintro ⟨c', d', he, hn⟩; obtain ⟨rfl, rfl⟩ := Ew_inj he; exact hn (ga ha)
  · rintro ⟨⟨c, d, rfl, hl⟩, hw, ht, hi, ha⟩
    refine ⟨c, d, rfl, (good_iff acyc c d hl).2 ⟨?_, ?_, ?_, fun h => ?_⟩⟩
    · by_contra hn; exact hw ⟨c, d, rfl, hn⟩
    · by_contra hn; exact ht ⟨c, d, rfl, hn⟩
    · by_contra hn; exact hi ⟨c, d, rfl, hn⟩
    · by_contra hn; exact ha h ⟨c, d, rfl, hn⟩

lemma checkLang_iff' (acyc : Bool) (u : List A) :
    u ∈ checkLang (D0bf.Rchk acyc) ↔
      Plen u ∧ ¬Qwf u ∧ ¬Qtime u ∧ ¬Qinv u ∧ (acyc = true → ¬Qac u) :=
  (D0bfN3b.checkLang_iff acyc u).trans (conj_iff acyc u)

lemma Plen_ne_nil {u : List A} (h : Plen u) : u ≠ [] := by
  obtain ⟨c, d, rfl, -⟩ := h
  exact Ew_ne_nil c d

theorem N3_ptc (acyc : Bool) : ∃ f : List A → List A, PolyTimeComputable f ∧
    ∀ u, u ∈ checkLang (D0bf.Rchk acyc) ↔ f u ≠ [] := by
  classical
  have base := CookPvsNP.polyTimeComputable_comp _ _ (CookPvsNP.polyTimeComputable_comp _ _
    (CookPvsNP.polyTimeComputable_comp _ _ ptc_len ptc_wf) ptc_time) ptc_inv
  cases acyc with
  | false =>
    refine ⟨_, base, fun u => ?_⟩
    simp only [Function.comp_apply, filt_filt]
    rw [checkLang_iff']
    unfold filt
    constructor
    · rintro ⟨h1, h2, h3, h4, -⟩
      rw [if_pos ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩]
      exact Plen_ne_nil h1
    · intro h
      by_cases hc : ((Plen u ∧ ¬Qwf u) ∧ ¬Qtime u) ∧ ¬Qinv u
      · exact ⟨hc.1.1.1, hc.1.1.2, hc.1.2, hc.2, by simp⟩
      · rw [if_neg hc] at h; exact absurd rfl h
  | true =>
    refine ⟨_, CookPvsNP.polyTimeComputable_comp _ _ base ptc_acyc, fun u => ?_⟩
    simp only [Function.comp_apply, filt_filt]
    rw [checkLang_iff']
    unfold filt
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩
      rw [if_pos ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5 rfl⟩]
      exact Plen_ne_nil h1
    · intro h
      by_cases hc : (((Plen u ∧ ¬Qwf u) ∧ ¬Qtime u) ∧ ¬Qinv u) ∧ ¬Qac u
      · exact ⟨hc.1.1.1.1, hc.1.1.1.2, hc.1.1.2, hc.1.2, fun _ => hc.2⟩
      · rw [if_neg hc] at h; exact absurd rfl h

theorem mem_NP_of (acyc : Bool) : cumFeasLang (D0bf.Cof acyc) ∈ NP BSym := by
  classical
  obtain ⟨k, hk⟩ := D0bf.N2_certificate acyc
  obtain ⟨f, hf, hfu⟩ := N3_ptc acyc
  refine ⟨BSym, inferInstance, inferInstance, D0bf.Rchk acyc, k, ?_, hk⟩
  exact CookPvsNP.mem_P_of_polyReducible _ {w : List A | w ≠ []} ⟨f, hf, fun u => hfu u⟩
    (D0bfN1.nonempty_mem_P _)

end D0bfR

end D0bfAll

theorem solution :
    ProjSchedTW.Complexity.cumFeasLang (fun _ => True) ∈ CookPvsNP.NP ProjSchedTW.Complexity.BSym ∧
      ProjSchedTW.Complexity.cumFeasLang ProjSchedTW.Complexity.CumInstance.IsAcyclic ∈
        CookPvsNP.NP ProjSchedTW.Complexity.BSym :=
  ⟨D0bfR.mem_NP_of false, D0bfR.mem_NP_of true⟩
