-- Prove2me | solution 1 for TheoryOfGames.ThreePerson.all_solutions
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T03:02:55.053318+00:00
-- url     : https://prove2.me/submissions/c5618756-6ff6-438b-81cc-5852d72599ba

import Mathlib
import Definitions.Def_TheoryOfGames_ThreePerson_Solution
import Definitions.Def_TheoryOfGames_ThreePerson_ReducedThreePerson

set_option autoImplicit false

namespace P32269

open TheoryOfGames.ThreePerson

/-- Coordinate form of an imputation of `redV`. -/
def Imp (a : Fin 3 → ℝ) : Prop :=
  -1 ≤ a 0 ∧ -1 ≤ a 1 ∧ -1 ≤ a 2 ∧ a 0 + a 1 + a 2 = 0

/-- Pair domination: two coordinates of `a` exceed those of `b`. -/
def PD (a b : Fin 3 → ℝ) : Prop :=
  (b 0 < a 0 ∧ b 1 < a 1) ∨ (b 0 < a 0 ∧ b 2 < a 2) ∨ (b 1 < a 1 ∧ b 2 < a 2)

/-- Coordinate form of a solution. -/
def SolC (V : Set (Fin 3 → ℝ)) : Prop :=
  (∀ a ∈ V, Imp a) ∧ (∀ a ∈ V, ∀ b ∈ V, ¬ PD a b) ∧
    (∀ b, Imp b → b ∉ V → ∃ a ∈ V, PD a b)

lemma imp_mk (a : Fin 3 → ℝ) (h0 : -1 ≤ a 0) (h1 : -1 ≤ a 1) (h2 : -1 ≤ a 2)
    (hs : a 0 + a 1 + a 2 = 0) : Imp a := ⟨h0, h1, h2, hs⟩

lemma pd01 {a b : Fin 3 → ℝ} (h0 : b 0 < a 0) (h1 : b 1 < a 1) : PD a b := Or.inl ⟨h0, h1⟩
lemma pd02 {a b : Fin 3 → ℝ} (h0 : b 0 < a 0) (h2 : b 2 < a 2) : PD a b :=
  Or.inr (Or.inl ⟨h0, h2⟩)
lemma pd12 {a b : Fin 3 → ℝ} (h1 : b 1 < a 1) (h2 : b 2 < a 2) : PD a b :=
  Or.inr (Or.inr ⟨h1, h2⟩)

lemma ext3 (a b : Fin 3 → ℝ) (h0 : a 0 = b 0) (h1 : a 1 = b 1) (h2 : a 2 = b 2) : a = b := by
  funext l
  fin_cases l
  · exact h0
  · exact h1
  · exact h2

@[simp] lemma vec3_two (x y z : ℝ) : (![x, y, z] : Fin 3 → ℝ) 2 = z := rfl

lemma redV_single (i : Fin 3) : redV {i} = -1 := by simp [redV]

lemma imp_iff (a : Fin 3 → ℝ) : IsImputation redV a ↔ Imp a := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := h1 0; rwa [redV_single] at this
    · have := h1 1; rwa [redV_single] at this
    · have := h1 2; rwa [redV_single] at this
    · simpa [Fin.sum_univ_three] using h2
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨fun i => ?_, ?_⟩
    · rw [redV_single]
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
    · simpa [Fin.sum_univ_three] using h3

lemma fs3 (S : Finset (Fin 3)) :
    S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {2} ∨ S = {0, 1} ∨ S = {0, 2} ∨ S = {1, 2} ∨
      S = {0, 1, 2} := by
  revert S; decide

lemma dom_to_PD (a b : Fin 3 → ℝ) (hb : Imp b) (h : Dominates redV a b) : PD a b := by
  obtain ⟨S, hne, heff, hlt⟩ := h
  obtain ⟨b0, b1, b2, bs⟩ := hb
  unfold IsEffective at heff
  unfold PD
  rcases fs3 S with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp at hne
  · have := hlt 0 (by simp); simp [redV] at heff; linarith
  · have := hlt 1 (by simp); simp [redV] at heff; linarith
  · have := hlt 2 (by simp); simp [redV] at heff; linarith
  · exact Or.inl ⟨hlt 0 (by simp), hlt 1 (by simp)⟩
  · exact Or.inr (Or.inl ⟨hlt 0 (by simp), hlt 2 (by simp)⟩)
  · exact Or.inr (Or.inr ⟨hlt 1 (by simp), hlt 2 (by simp)⟩)
  · have h0 := hlt 0 (by simp)
    have h1 := hlt 1 (by simp)
    have h2 := hlt 2 (by simp)
    have hc : ({0, 1, 2} : Finset (Fin 3)).card = 3 := by decide
    have hsum : ∑ i ∈ ({0, 1, 2} : Finset (Fin 3)), a i = a 0 + a 1 + a 2 := by
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
      ring
    rw [hsum] at heff
    simp only [redV, hc] at heff
    norm_num at heff
    linarith

lemma pair_eff (a : Fin 3 → ℝ) (ha : Imp a) (j k : Fin 3) (hjk : j ≠ k) :
    IsEffective redV {j, k} a := by
  obtain ⟨a0, a1, a2, as⟩ := ha
  unfold IsEffective
  have hc : ({j, k} : Finset (Fin 3)).card = 2 := Finset.card_pair hjk
  rw [Finset.sum_pair hjk]
  simp only [redV, hc]
  norm_num
  fin_cases j <;> fin_cases k <;> simp at hjk ⊢ <;> linarith

lemma PD_to_dom (a b : Fin 3 → ℝ) (ha : Imp a) (h : PD a b) : Dominates redV a b := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨{0, 1}, by simp, pair_eff a ha 0 1 (by decide), ?_⟩
    intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption
  · refine ⟨{0, 2}, by simp, pair_eff a ha 0 2 (by decide), ?_⟩
    intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption
  · refine ⟨{1, 2}, by simp, pair_eff a ha 1 2 (by decide), ?_⟩
    intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption

lemma sol_iff (V : Set (Fin 3 → ℝ)) : IsSolution redV V ↔ SolC V := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hI : ∀ a ∈ V, Imp a := fun a ha => (imp_iff a).1 (h1 a ha)
    refine ⟨hI, ?_, ?_⟩
    · intro a ha b hb hp
      exact h2 a ha b hb (PD_to_dom a b (hI a ha) hp)
    · intro b hb hbV
      obtain ⟨a, ha, hd⟩ := h3 b ((imp_iff b).2 hb) hbV
      exact ⟨a, ha, dom_to_PD a b hb hd⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun a ha => (imp_iff a).2 (h1 a ha), ?_, ?_⟩
    · intro a ha b hb hd
      exact h2 a ha b hb (dom_to_PD a b (h1 b hb) hd)
    · intro b hb hbV
      obtain ⟨a, ha, hp⟩ := h3 b ((imp_iff b).1 hb) hbV
      exact ⟨a, ha, PD_to_dom a b (h1 a ha) hp⟩

lemma mem_line (i : Fin 3) (c : ℝ) (a : Fin 3 → ℝ) : a ∈ lineSet i c ↔ Imp a ∧ a i = c := by
  simp only [lineSet, Set.mem_ofPred_eq, imp_iff]

lemma mem_mid (a : Fin 3 → ℝ) :
    a ∈ middlePointsSet ↔
      a = ![-1, 1 / 2, 1 / 2] ∨ a = ![1 / 2, -1, 1 / 2] ∨ a = ![1 / 2, 1 / 2, -1] := by
  simp [middlePointsSet]

lemma eq_vec (b : Fin 3 → ℝ) (x y z : ℝ) (h0 : b 0 = x) (h1 : b 1 = y) (h2 : b 2 = z) :
    b = ![x, y, z] := by
  funext l
  fin_cases l
  · simpa using h0
  · simpa using h1
  · simpa using h2

/-! ### The listed sets are solutions -/

lemma mid_sol : SolC middlePointsSet := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rcases (mem_mid a).1 ha with rfl | rfl | rfl <;> (unfold Imp; norm_num)
  · intro a ha b hb hp
    rcases (mem_mid a).1 ha with rfl | rfl | rfl <;>
      rcases (mem_mid b).1 hb with rfl | rfl | rfl <;> (unfold PD at hp; norm_num at hp)
  · intro b hb hbm
    obtain ⟨b0, b1, b2, bs⟩ := hb
    by_cases h12 : b 1 < 1 / 2 ∧ b 2 < 1 / 2
    · refine ⟨![-1, 1 / 2, 1 / 2], (mem_mid _).2 (Or.inl rfl), ?_⟩
      refine Or.inr (Or.inr ⟨?_, ?_⟩) <;> norm_num <;> linarith [h12.1, h12.2]
    by_cases h02 : b 0 < 1 / 2 ∧ b 2 < 1 / 2
    · refine ⟨![1 / 2, -1, 1 / 2], (mem_mid _).2 (Or.inr (Or.inl rfl)), ?_⟩
      refine Or.inr (Or.inl ⟨?_, ?_⟩) <;> norm_num <;> linarith [h02.1, h02.2]
    by_cases h01 : b 0 < 1 / 2 ∧ b 1 < 1 / 2
    · refine ⟨![1 / 2, 1 / 2, -1], (mem_mid _).2 (Or.inr (Or.inr rfl)), ?_⟩
      refine Or.inl ⟨?_, ?_⟩ <;> norm_num <;> linarith [h01.1, h01.2]
    exfalso
    apply hbm
    rw [mem_mid]
    push_neg at h12 h02 h01
    rcases lt_or_ge (b 0) (1 / 2) with c0 | c0
    · have := h01 c0; have := h02 c0
      exact Or.inl (eq_vec b _ _ _ (by linarith) (by linarith) (by linarith))
    · rcases lt_or_ge (b 1) (1 / 2) with c1 | c1
      · have := h12 c1
        exact Or.inr (Or.inl (eq_vec b _ _ _ (by linarith) (by linarith) (by linarith)))
      · exact Or.inr (Or.inr (eq_vec b _ _ _ (by linarith) (by linarith) (by linarith)))

lemma line_sol (i : Fin 3) (c : ℝ) (hc1 : -1 ≤ c) (hc2 : c < 1 / 2) : SolC (lineSet i c) := by
  refine ⟨fun a ha => ((mem_line i c a).1 ha).1, ?_, ?_⟩
  · intro a ha b hb hp
    obtain ⟨⟨a0, a1, a2, as⟩, ai⟩ := (mem_line i c a).1 ha
    obtain ⟨⟨b0, b1, b2, bs⟩, bi⟩ := (mem_line i c b).1 hb
    unfold PD at hp
    fin_cases i <;> simp at ai bi <;> rcases hp with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
  · intro b hb hbV
    have hbi : b i ≠ c := fun h => hbV ((mem_line i c b).2 ⟨hb, h⟩)
    obtain ⟨b0, b1, b2, bs⟩ := hb
    have W : ∀ α : Fin 3 → ℝ, Imp α → α i = c → PD α b → ∃ a ∈ lineSet i c, PD a b :=
      fun α h1 h2 h3 => ⟨α, (mem_line i c α).2 ⟨h1, h2⟩, h3⟩
    fin_cases i <;> simp at hbi
    · rcases lt_or_gt_of_ne hbi with hlt | hgt
      · by_cases h1 : b 1 < 1 - c
        · exact W ![c, 1 - c, -1] (imp_mk _ (by norm_num; linarith) (by norm_num; linarith)
            (by norm_num) (by norm_num <;> ring)) rfl (pd01 (by norm_num; linarith) (by norm_num; linarith))
        · exact W ![c, -1, 1 - c] (imp_mk _ (by norm_num; linarith) (by norm_num)
            (by norm_num; linarith) (by norm_num <;> ring)) rfl
            (pd02 (by norm_num; linarith) (by norm_num; linarith))
      · exact W ![c, b 1 + (b 0 - c) / 2, b 2 + (b 0 - c) / 2]
          (imp_mk _ (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
            (by norm_num; linarith)) rfl
          (pd12 (by norm_num; linarith) (by norm_num; linarith))
    · rcases lt_or_gt_of_ne hbi with hlt | hgt
      · by_cases h0 : b 0 < 1 - c
        · exact W ![1 - c, c, -1] (imp_mk _ (by norm_num; linarith) (by norm_num; linarith)
            (by norm_num) (by norm_num <;> ring)) rfl (pd01 (by norm_num; linarith) (by norm_num; linarith))
        · exact W ![-1, c, 1 - c] (imp_mk _ (by norm_num) (by norm_num; linarith)
            (by norm_num; linarith) (by norm_num <;> ring)) rfl
            (pd12 (by norm_num; linarith) (by norm_num; linarith))
      · exact W ![b 0 + (b 1 - c) / 2, c, b 2 + (b 1 - c) / 2]
          (imp_mk _ (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
            (by norm_num; linarith)) rfl
          (pd02 (by norm_num; linarith) (by norm_num; linarith))
    · rcases lt_or_gt_of_ne hbi with hlt | hgt
      · by_cases h0 : b 0 < 1 - c
        · exact W ![1 - c, -1, c] (imp_mk _ (by norm_num; linarith) (by norm_num)
            (by norm_num; linarith) (by norm_num <;> ring)) rfl
            (pd02 (by norm_num; linarith) (by norm_num; linarith))
        · exact W ![-1, 1 - c, c] (imp_mk _ (by norm_num) (by norm_num; linarith)
            (by norm_num; linarith) (by norm_num <;> ring)) rfl
            (pd12 (by norm_num; linarith) (by norm_num; linarith))
      · exact W ![b 0 + (b 2 - c) / 2, b 1 + (b 2 - c) / 2, c]
          (imp_mk _ (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
            (by norm_num; linarith)) rfl
          (pd01 (by norm_num; linarith) (by norm_num; linarith))

/-! ### Every solution is listed -/

lemma share (V : Set (Fin 3 → ℝ)) (hV : SolC V) (a : Fin 3 → ℝ) (ha : a ∈ V)
    (b : Fin 3 → ℝ) (hb : b ∈ V) : a 0 = b 0 ∨ a 1 = b 1 ∨ a 2 = b 2 := by
  obtain ⟨hI, hN, -⟩ := hV
  obtain ⟨a0, a1, a2, as⟩ := hI a ha
  obtain ⟨b0, b1, b2, bs⟩ := hI b hb
  have n1 := hN a ha b hb
  have n2 := hN b hb a ha
  unfold PD at n1 n2
  by_contra h
  push_neg at h
  obtain ⟨h0, h1, h2⟩ := h
  rcases lt_or_gt_of_ne h0 with c0 | c0 <;> rcases lt_or_gt_of_ne h1 with c1 | c1 <;>
    rcases lt_or_gt_of_ne h2 with c2 | c2
  all_goals first
    | exact n1 (Or.inl ⟨c0, c1⟩)
    | exact n1 (Or.inr (Or.inl ⟨c0, c2⟩))
    | exact n1 (Or.inr (Or.inr ⟨c1, c2⟩))
    | exact n2 (Or.inl ⟨c0, c1⟩)
    | exact n2 (Or.inr (Or.inl ⟨c0, c2⟩))
    | exact n2 (Or.inr (Or.inr ⟨c1, c2⟩))
    | linarith

lemma nonempty_of_sol (V : Set (Fin 3 → ℝ)) (hV : SolC V) : ∃ a, a ∈ V := by
  by_cases h : (0 : Fin 3 → ℝ) ∈ V
  · exact ⟨0, h⟩
  · obtain ⟨a, ha, -⟩ := hV.2.2 0 (by unfold Imp; norm_num) h
    exact ⟨a, ha⟩

lemma line_case (V : Set (Fin 3 → ℝ)) (hV : SolC V) (i : Fin 3) (c : ℝ)
    (hc : ∀ g ∈ V, g i = c) : -1 ≤ c ∧ c < 1 / 2 ∧ V = lineSet i c := by
  obtain ⟨a, ha⟩ := nonempty_of_sol V hV
  obtain ⟨hI, hN, hE⟩ := hV
  have hc1 : -1 ≤ c := by
    obtain ⟨a0, a1, a2, -⟩ := hI a ha
    have := hc a ha
    fin_cases i <;> simp at this <;> linarith
  refine ⟨hc1, ?_, ?_⟩
  · by_contra hge
    push_neg at hge
    have key : ∀ β : Fin 3 → ℝ, Imp β → β i = -1 → (∀ α ∈ V, ¬ PD α β) → False := by
      intro β hβ hβi hnd
      have hβV : β ∉ V := fun hm => by have := hc β hm; linarith
      obtain ⟨α, hα, hp⟩ := hE β hβ hβV
      exact hnd α hα hp
    fin_cases i
    · refine key ![-1, 1 / 2, 1 / 2] (imp_mk _ (by norm_num) (by norm_num) (by norm_num)
        (by norm_num <;> ring)) rfl ?_
      intro α hα hp
      obtain ⟨a0, a1, a2, as⟩ := hI α hα
      have h := hc α hα
      simp at h
      rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> norm_num at h1 h2 <;> linarith
    · refine key ![1 / 2, -1, 1 / 2] (imp_mk _ (by norm_num) (by norm_num) (by norm_num)
        (by norm_num <;> ring)) rfl ?_
      intro α hα hp
      obtain ⟨a0, a1, a2, as⟩ := hI α hα
      have h := hc α hα
      simp at h
      rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> norm_num at h1 h2 <;> linarith
    · refine key ![1 / 2, 1 / 2, -1] (imp_mk _ (by norm_num) (by norm_num) (by norm_num)
        (by norm_num <;> ring)) rfl ?_
      intro α hα hp
      obtain ⟨a0, a1, a2, as⟩ := hI α hα
      have h := hc α hα
      simp at h
      rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> norm_num at h1 h2 <;> linarith
  · ext b
    rw [mem_line]
    constructor
    · intro hb
      exact ⟨hI b hb, hc b hb⟩
    · rintro ⟨hb, hbi⟩
      by_contra hbV
      obtain ⟨α, hα, hp⟩ := hE b hb hbV
      obtain ⟨a0, a1, a2, as⟩ := hI α hα
      obtain ⟨b0, b1, b2, bs⟩ := hb
      have hαi := hc α hα
      unfold PD at hp
      fin_cases i <;> simp at hαi hbi <;>
        rcases hp with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> linarith

lemma vne (β A : Fin 3 → ℝ) (i : Fin 3) (h : A i < β i) : β ≠ A := by
  rintro rfl
  exact lt_irrefl _ h

set_option maxHeartbeats 2000000 in
lemma tri_sub (V : Set (Fin 3 → ℝ)) (hV : SolC V) (A B C : Fin 3 → ℝ)
    (hA : A ∈ V) (hB : B ∈ V) (hC : C ∈ V) (e0 : A 0 = B 0) (e1 : A 1 = C 1) (e2 : B 2 = C 2)
    (hs : A 2 ≠ B 2) : ∀ d ∈ V, d = A ∨ d = B ∨ d = C := by
  have hS := share V hV
  obtain ⟨hI, -, -⟩ := hV
  obtain ⟨A0, A1, A2, As⟩ := hI A hA
  obtain ⟨B0, B1, B2, Bs⟩ := hI B hB
  obtain ⟨C0, C1, C2, Cs⟩ := hI C hC
  intro d hd
  obtain ⟨d0, d1, d2, ds⟩ := hI d hd
  rcases hS d hd A hA with h1 | h1 | h1 <;> rcases hS d hd B hB with h2 | h2 | h2 <;>
    rcases hS d hd C hC with h3 | h3 | h3
  all_goals first
    | exact Or.inl (ext3 _ _ (by linarith) (by linarith) (by linarith))
    | exact Or.inr (Or.inl (ext3 _ _ (by linarith) (by linarith) (by linarith)))
    | exact Or.inr (Or.inr (ext3 _ _ (by linarith) (by linarith) (by linarith)))
    | (exfalso; rcases lt_or_gt_of_ne hs with hs' | hs' <;> linarith)

set_option maxHeartbeats 1000000 in
/-- The triangle case: three points of `V` pairwise sharing distinct coordinates. -/
lemma tri_case (V : Set (Fin 3 → ℝ)) (hV : SolC V) (A B C : Fin 3 → ℝ)
    (hA : A ∈ V) (hB : B ∈ V) (hC : C ∈ V) (e0 : A 0 = B 0) (e1 : A 1 = C 1) (e2 : B 2 = C 2)
    (hs : A 2 ≠ B 2) : V = middlePointsSet := by
  have hS := share V hV
  obtain ⟨hI, hN, hE⟩ := hV
  obtain ⟨A0, A1, A2, As⟩ := hI A hA
  obtain ⟨B0, B1, B2, Bs⟩ := hI B hB
  obtain ⟨C0, C1, C2, Cs⟩ := hI C hC
  have hsub := tri_sub V ⟨hI, hN, hE⟩ A B C hA hB hC e0 e1 e2 hs
  -- an imputation outside {A,B,C} not dominated by A, B, C gives a contradiction
  have key : ∀ β : Fin 3 → ℝ, Imp β → β ≠ A → β ≠ B → β ≠ C → ¬ PD A β → ¬ PD B β →
      ¬ PD C β → False := by
    intro β hβ nA nB nC pA pB pC
    by_cases hβV : β ∈ V
    · rcases hsub β hβV with h | h | h
      · exact nA h
      · exact nB h
      · exact nC h
    · obtain ⟨α, hα, hp⟩ := hE β hβ hβV
      rcases hsub α hα with rfl | rfl | rfl
      · exact pA hp
      · exact pB hp
      · exact pC hp
  rcases lt_or_gt_of_ne hs with hlt | hgt
  · -- s > 0 where s = B 2 - A 2
    have k01 : A 0 + A 1 = 1 := by
      by_contra hne
      have hl : A 0 + A 1 < 1 := lt_of_le_of_ne (by linarith) hne
      set d := (1 - A 0 - A 1) / 2 with hd
      have hd0 : 0 < d := by rw [hd]; linarith
      apply key ![A 0 + d, A 1, -A 0 - A 1 - d]
      · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith
      · exact vne _ _ 0 (by simp; linarith)
      · exact vne _ _ 0 (by simp; linarith)
      · exact vne _ _ 0 (by simp; linarith)
      all_goals
        intro h; unfold PD at h
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp at h1 h2 <;> linarith
    have k02 : B 0 + B 2 = 1 := by
      by_contra hne
      have hl : B 0 + B 2 < 1 := lt_of_le_of_ne (by linarith) hne
      set d := (1 - B 0 - B 2) / 2 with hd
      have hd0 : 0 < d := by rw [hd]; linarith
      apply key ![B 0 + d, -B 0 - B 2 - d, B 2]
      · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith
      · exact vne _ _ 0 (by simp; linarith)
      · exact vne _ _ 0 (by simp; linarith)
      · exact vne _ _ 0 (by simp; linarith)
      all_goals
        intro h; unfold PD at h
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp at h1 h2 <;> linarith
    have k12 : C 1 + C 2 = 1 := by
      by_contra hne
      have hl : C 1 + C 2 < 1 := lt_of_le_of_ne (by linarith) hne
      set d := (1 - C 1 - C 2) / 2 with hd
      have hd0 : 0 < d := by rw [hd]; linarith
      apply key ![-C 1 - C 2 - d, C 1 + d, C 2]
      · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith
      · exact vne _ _ 1 (by simp; linarith)
      · exact vne _ _ 1 (by simp; linarith)
      · exact vne _ _ 1 (by simp; linarith)
      all_goals
        intro h; unfold PD at h
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp at h1 h2 <;> linarith
    have eA : A = ![1 / 2, 1 / 2, -1] := eq_vec A _ _ _ (by linarith) (by linarith) (by linarith)
    have eB : B = ![1 / 2, -1, 1 / 2] := eq_vec B _ _ _ (by linarith) (by linarith) (by linarith)
    have eC : C = ![-1, 1 / 2, 1 / 2] := eq_vec C _ _ _ (by linarith) (by linarith) (by linarith)
    ext d
    rw [mem_mid]
    constructor
    · intro hd
      rcases hsub d hd with rfl | rfl | rfl
      · exact Or.inr (Or.inr eA)
      · exact Or.inr (Or.inl eB)
      · exact Or.inl eC
    · rintro (rfl | rfl | rfl)
      · rw [← eC]; exact hC
      · rw [← eB]; exact hB
      · rw [← eA]; exact hA
  · -- s < 0: the point u - s/3 is undominated
    exfalso
    set s := B 2 - A 2 with hsd
    have hs0 : s < 0 := by rw [hsd]; linarith
    apply key ![A 0 - s / 3, A 1 - s / 3, B 2 - s / 3]
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith
    · exact vne _ _ 0 (by simp; linarith)
    · exact vne _ _ 0 (by simp; linarith)
    · exact vne _ _ 1 (by simp; linarith)
    all_goals
      intro h; unfold PD at h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp at h1 h2 <;> linarith

lemma forward (V : Set (Fin 3 → ℝ)) (hV : SolC V) :
    V = middlePointsSet ∨ ∃ i : Fin 3, ∃ c : ℝ, -1 ≤ c ∧ c < 1 / 2 ∧ V = lineSet i c := by
  by_cases hL : ∃ i : Fin 3, ∃ c : ℝ, ∀ g ∈ V, g i = c
  · obtain ⟨i, c, hc⟩ := hL
    exact Or.inr ⟨i, c, line_case V hV i c hc⟩
  left
  push_neg at hL
  have hS := share V hV
  have hI := hV.1
  obtain ⟨X, hX, -⟩ := hL 0 0
  obtain ⟨Y, hY, hY0⟩ := hL 0 (X 0)
  obtain ⟨X0, X1, X2, Xs⟩ := hI X hX
  obtain ⟨Y0, Y1, Y2, Ys⟩ := hI Y hY
  rcases hS X hX Y hY with h | h | h
  · exact absurd h.symm hY0
  · obtain ⟨Z, hZ, hZ1⟩ := hL 1 (X 1)
    obtain ⟨Z0, Z1, Z2, Zs⟩ := hI Z hZ
    rcases hS Z hZ X hX with g | g | g
    · rcases hS Z hZ Y hY with k | k | k
      · exact absurd (by linarith) hY0
      · exact absurd (by linarith) hZ1
      · -- (X,Z) share 0, (X,Y) share 1, (Z,Y) share 2
        exact tri_case V hV X Z Y hX hZ hY g.symm h k
          (fun e => hZ1 (by linarith))
    · exact absurd g hZ1
    · rcases hS Z hZ Y hY with k | k | k
      · -- (X,Z) share 2, (X,Y) share 1, (Y,Z) share 0
        exact tri_case V hV Y Z X hY hZ hX k.symm h.symm g
          (fun e => hZ1 (by linarith))
      · exact absurd (by linarith) hZ1
      · exact absurd (by linarith) hY0
  · obtain ⟨Z, hZ, hZ2⟩ := hL 2 (X 2)
    obtain ⟨Z0, Z1, Z2, Zs⟩ := hI Z hZ
    rcases hS Z hZ X hX with g | g | g
    · rcases hS Z hZ Y hY with k | k | k
      · exact absurd (by linarith) hY0
      · -- (X,Z) share 0, (X,Y) share 2, (Y,Z) share 1
        exact tri_case V hV Z X Y hZ hX hY g k h
          (fun e => hZ2 (by linarith))
      · exact absurd (by linarith) hZ2
    · rcases hS Z hZ Y hY with k | k | k
      · -- (X,Z) share 1, (X,Y) share 2, (Y,Z) share 0
        exact tri_case V hV Z Y X hZ hY hX k g h.symm
          (fun e => hZ2 (by linarith))
      · exact absurd (by linarith) hY0
      · exact absurd (by linarith) hZ2
    · exact absurd g hZ2

end P32269

open TheoryOfGames.ThreePerson in
theorem solution (V : Set (Fin 3 → ℝ)) :
    IsSolution redV V ↔
      V = middlePointsSet ∨
        ∃ i : Fin 3, ∃ c : ℝ, -1 ≤ c ∧ c < 1 / 2 ∧ V = lineSet i c := by
  rw [P32269.sol_iff]
  constructor
  · intro h
    exact P32269.forward V h
  · rintro (rfl | ⟨i, c, h1, h2, rfl⟩)
    · exact P32269.mid_sol
    · exact P32269.line_sol i c h1 h2
