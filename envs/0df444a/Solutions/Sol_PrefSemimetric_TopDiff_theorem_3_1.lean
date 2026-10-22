-- Prove2me | solution 1 for PrefSemimetric.TopDiff.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T17:20:08.104208+00:00
-- url     : https://prove2.me/submissions/7765c3f9-0e2b-48ba-93e5-6187469b8cdb

import Mathlib
import Definitions.Def_PrefSemimetric_TopDiff_Model

open PrefSemimetric.TopDiff

theorem ps_mem_max {X : Type*} (S : Finset X) (R : X → X → Prop) (x : X) :
    x ∈ maxSet S R ↔ x ∈ S ∧ ∀ y ∈ S, ¬ asymmPart R y x := by
  unfold maxSet; simp [Finset.mem_filter]

theorem ps_key {X : Type*} [Fintype X] [DecidableEq X]
    (R R0 T : X → X → Prop) (hT : IsAcyclicOrder T)
    (h : OneStepToward R R0 T) (S : Finset X) (x : X) :
    ¬ (x ∈ symmDiff (maxSet S R) (maxSet S R0) ∧ x ∈ symmDiff (maxSet S R0) (maxSet S T)) := by
  obtain ⟨_, h⟩ := h
  simp only [Finset.mem_symmDiff]
  rcases h with ⟨a, b, hRab, rfl, hTab, hTx⟩ | ⟨a, b, hRab, hRba, rfl, hTab⟩
  · have hasym : ∀ y z, asymmPart (ominus R a b) y z ↔ asymmPart R y z ∧ ¬ (y = a ∧ z = b) := by
      intro y z
      simp only [asymmPart, ominus]
      obtain ⟨hr1, hr2⟩ := hRab
      by_cases e1 : y = a <;> by_cases e2 : z = b <;> by_cases e3 : z = a <;> by_cases e4 : y = b <;>
        simp_all
    have hne : x ≠ b → (x ∈ maxSet S R ↔ x ∈ maxSet S (ominus R a b)) := by
      intro hxb
      rw [ps_mem_max, ps_mem_max]
      simp only [hasym]
      constructor
      · rintro ⟨hx, h⟩; exact ⟨hx, fun y hy hh => h y hy hh.1⟩
      · rintro ⟨hx, h⟩; exact ⟨hx, fun y hy hh => h y hy ⟨hh, fun e => hxb e.2⟩⟩
    have h10 : x ∈ maxSet S R → x ∈ maxSet S (ominus R a b) := by
      rw [ps_mem_max, ps_mem_max]; simp only [hasym]
      rintro ⟨hx, h⟩; exact ⟨hx, fun y hy hh => h y hy hh.1⟩
    have h0T : x = b → x ∈ maxSet S (ominus R a b) → x ∈ maxSet S T := by
      rintro rfl
      rw [ps_mem_max, ps_mem_max]; simp only [hasym]
      rintro ⟨hx, h⟩
      refine ⟨hx, fun y hy hyT => ?_⟩
      have hya : y ≠ a := by rintro rfl; exact hTab hyT
      exact h y hy ⟨hTx y hyT, fun e => hya e.1⟩
    by_cases hxb : x = b
    · have := h0T hxb; tauto
    · have := hne hxb; tauto
  · have hab : a ≠ b := by
      rintro rfl; exact hTab.2 (hT.1 a)
    have hasym : ∀ y z, asymmPart (oplus R a b) y z ↔ asymmPart R y z ∨ (y = a ∧ z = b) := by
      intro y z
      simp only [asymmPart, oplus]
      simp only [asymmPart] at hRab hRba
      by_cases e1 : y = a <;> by_cases e2 : z = b <;> by_cases e3 : z = a <;> by_cases e4 : y = b <;>
        simp_all
    have hne : x ≠ b → (x ∈ maxSet S R ↔ x ∈ maxSet S (oplus R a b)) := by
      intro hxb
      rw [ps_mem_max, ps_mem_max]
      simp only [hasym]
      constructor
      · rintro ⟨hx, h⟩; refine ⟨hx, fun y hy hh => ?_⟩
        rcases hh with hh | hh
        · exact h y hy hh
        · exact hxb hh.2
      · rintro ⟨hx, h⟩; exact ⟨hx, fun y hy hh => h y hy (Or.inl hh)⟩
    have h01 : x ∈ maxSet S (oplus R a b) → x ∈ maxSet S R := by
      rw [ps_mem_max, ps_mem_max]; simp only [hasym]
      rintro ⟨hx, h⟩; exact ⟨hx, fun y hy hh => h y hy (Or.inl hh)⟩
    have h1T : x = b → x ∈ maxSet S R → x ∉ maxSet S (oplus R a b) → x ∉ maxSet S T := by
      rintro rfl hR h0 hTm
      rw [ps_mem_max] at hR hTm h0
      simp only [hasym] at h0
      apply h0
      refine ⟨hR.1, fun y hy hh => ?_⟩
      rcases hh with hh | ⟨rfl, -⟩
      · exact hR.2 y hy hh
      · exact hTm.2 y hy hTab
    by_cases hxb : x = b
    · have := h1T hxb; tauto
    · have := hne hxb; tauto


theorem ps_add {X : Type*} [Fintype X] [DecidableEq X] (w : X → ℝ) (R P T : X → X → Prop)
    (h : ∀ (S : Finset X) x,
      ¬ (x ∈ symmDiff (maxSet S R) (maxSet S P) ∧ x ∈ symmDiff (maxSet S P) (maxSet S T))) :
    Dmu w R T = Dmu w R P + Dmu w P T := by
  unfold Dmu
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  have hd : Disjoint (symmDiff (maxSet S R) (maxSet S P)) (symmDiff (maxSet S P) (maxSet S T)) :=
    Finset.disjoint_left.2 (fun x h1 h2 => h S x ⟨h1, h2⟩)
  have hu : symmDiff (maxSet S R) (maxSet S T) =
      symmDiff (maxSet S R) (maxSet S P) ∪ symmDiff (maxSet S P) (maxSet S T) := by
    ext x
    have := h S x
    simp only [Finset.mem_union, Finset.mem_symmDiff] at this ⊢
    tauto
  rw [hu, Finset.sum_union hd]

theorem ps_prop (r p q t : Prop)
    (k : ¬ (((p ∧ ¬ q) ∨ (q ∧ ¬ p)) ∧ ((q ∧ ¬ t) ∨ (t ∧ ¬ q))))
    (i : ¬ (((r ∧ ¬ p) ∨ (p ∧ ¬ r)) ∧ ((p ∧ ¬ t) ∨ (t ∧ ¬ p)))) :
    ¬ (((r ∧ ¬ q) ∨ (q ∧ ¬ r)) ∧ ((q ∧ ¬ t) ∨ (t ∧ ¬ q))) := by
  by_cases hr : r <;> by_cases hp : p <;> by_cases hq : q <;> by_cases ht : t <;> simp_all

theorem ps_chain {X : Type*} [Fintype X] [DecidableEq X]
    (R R0 T : X → X → Prop) (hT : IsAcyclicOrder T) (h : InBetween R R0 T) :
    ∀ (S : Finset X) x,
      ¬ (x ∈ symmDiff (maxSet S R) (maxSet S R0) ∧ x ∈ symmDiff (maxSet S R0) (maxSet S T)) := by
  induction h with
  | single h => exact ps_key _ _ T hT h
  | @tail P Q _ hPQ ih =>
    intro S x
    have k := ps_key P Q T hT hPQ S x
    have i := ih S x
    simp only [Finset.mem_symmDiff] at k i ⊢
    exact ps_prop _ _ _ _ k i


theorem ps_acyclic_of_rank {X : Type*} (R : X → X → Prop) (hrefl : ∀ x, R x x)
    (f : X → ℕ) (hf : ∀ x y, asymmPart R x y → f x < f y) : IsAcyclicOrder R := by
  refine ⟨hrefl, ?_⟩
  intro x hx
  have key : ∀ y z, Relation.TransGen (asymmPart R) y z → f y < f z := by
    intro y z h
    induction h with
    | single h => exact hf _ _ h
    | tail _ h ih => exact lt_trans ih (hf _ _ h)
  exact lt_irrefl _ (key x x hx)

theorem ps_asymm_AB {X : Type*} (a b : X) (hab : a ≠ b) (y x : X) :
    asymmPart (prefAB a b) y x ↔ (y ≠ a ∧ y ≠ b ∧ (x = a ∨ x = b)) := by
  simp only [asymmPart, prefAB]
  by_cases h1 : y = a <;> by_cases h2 : y = b <;> by_cases h3 : x = a <;> by_cases h4 : x = b <;>
    simp_all [eq_comm]

theorem ps_asymm_ABplus {X : Type*} (a b : X) (hab : a ≠ b) (y x : X) :
    asymmPart (prefABplus a b) y x ↔ ((y ≠ a ∧ y ≠ b ∧ (x = a ∨ x = b)) ∨ (y = a ∧ x = b)) := by
  simp only [asymmPart, prefABplus, prefAB]
  by_cases h1 : y = a <;> by_cases h2 : y = b <;> by_cases h3 : x = a <;> by_cases h4 : x = b <;>
    simp_all [eq_comm]

theorem ps_eq8 {X : Type*} [Fintype X] [DecidableEq X]
    (w : X → ℝ) (a b : X) (hab : a ≠ b) :
    IsAcyclicOrder (prefAB a b) ∧ IsAcyclicOrder (prefABplus a b) ∧
      Dmu w (prefAB a b) (prefABplus a b) = w b := by
  classical
  let f : X → ℕ := fun x => if x = b then 2 else if x = a then 1 else 0
  refine ⟨?_, ?_, ?_⟩
  · apply ps_acyclic_of_rank (prefAB a b) (fun x => Or.inl rfl) f
    intro y x h
    rw [ps_asymm_AB a b hab] at h
    obtain ⟨h1, h2, h3⟩ := h
    rcases h3 with rfl | rfl <;> simp [f, h1, h2, hab, Ne.symm hab]
  · apply ps_acyclic_of_rank (prefABplus a b) (fun x => Or.inl (Or.inl rfl)) f
    intro y x h
    rw [ps_asymm_ABplus a b hab] at h
    rcases h with ⟨h1, h2, h3⟩ | ⟨rfl, rfl⟩
    · rcases h3 with rfl | rfl <;> simp [f, h1, h2, hab, Ne.symm hab]
    · simp [f, hab, Ne.symm hab]
  · have hdiff : ∀ S : Finset X, symmDiff (maxSet S (prefAB a b)) (maxSet S (prefABplus a b)) =
        if S = {a, b} then {b} else ∅ := by
      intro S
      have hSab : S = {a, b} ↔ (a ∈ S ∧ b ∈ S ∧ ∀ y ∈ S, y = a ∨ y = b) := by
        constructor
        · rintro rfl; simp
        · rintro ⟨ha, hb, hall⟩
          ext y; simp only [Finset.mem_insert, Finset.mem_singleton]
          constructor
          · exact hall y
          · rintro (rfl | rfl) <;> assumption
      ext x
      simp only [Finset.mem_symmDiff, maxSet, Finset.mem_filter, ps_asymm_AB a b hab,
        ps_asymm_ABplus a b hab]
      split_ifs with hS
      · rw [hSab] at hS
        obtain ⟨ha, hb, hall⟩ := hS
        simp only [Finset.mem_singleton]
        constructor
        · rintro (⟨⟨hx, h⟩, hn⟩ | ⟨⟨hx, h⟩, hn⟩)
          · by_contra hxb
            apply hn
            refine ⟨hx, fun y hy hc => ?_⟩
            rcases hc with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
            · rcases hall y hy with h' | h' <;> simp_all
            · exact hxb h2
          · exfalso; apply hn; refine ⟨hx, fun y hy hc => h y hy (Or.inl hc)⟩
        · rintro rfl
          left
          refine ⟨⟨hb, fun y hy hc => ?_⟩, fun hc => ?_⟩
          · rcases hall y hy with h' | h' <;> simp_all
          · exact hc.2 a ha (Or.inr ⟨rfl, rfl⟩)
      · rw [hSab] at hS
        simp only [Finset.notMem_empty, iff_false]
        rintro (⟨⟨hx, h⟩, hn⟩ | ⟨⟨hx, h⟩, hn⟩)
        · apply hn
          refine ⟨hx, fun y hy hc => ?_⟩
          rcases hc with hc | ⟨rfl, rfl⟩
          · exact h y hy hc
          · apply hS
            refine ⟨hy, hx, fun z hz => ?_⟩
            by_contra hzab
            push_neg at hzab
            exact h z hz ⟨hzab.1, hzab.2, Or.inr rfl⟩
        · exact hn ⟨hx, fun y hy hc => h y hy (Or.inl hc)⟩
    unfold Dmu
    simp only [hdiff]
    rw [Finset.sum_eq_single ({a, b} : Finset X)]
    · simp
    · intro S _ hS; simp [hS]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem ps_count {X : Type*} [Fintype X] [DecidableEq X] (a b : X) (F : Finset X)
    (haF : a ∉ F) (hbF : b ∉ F) (P : Finset X → Prop) [DecidablePred P]
    (hP : ∀ S, P S ↔ a ∈ S ∧ b ∈ S ∧ ∀ y ∈ S, y ≠ a → y ≠ b → y ∈ F) :
    (Finset.univ.filter P).card = 2 ^ F.card := by
  have heq : Finset.univ.filter P = F.powerset.image (fun U => insert a (insert b U)) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hP, Finset.mem_image,
      Finset.mem_powerset]
    constructor
    · rintro ⟨ha, hb, hS⟩
      refine ⟨(S.erase a).erase b, ?_, ?_⟩
      · intro y hy
        simp only [Finset.mem_erase] at hy
        exact hS y hy.2.2 hy.2.1 hy.1
      · ext y
        simp only [Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro (rfl | rfl | ⟨_, _, hy⟩) <;> assumption
        · intro hy
          by_cases h1 : y = a
          · exact Or.inl h1
          · by_cases h2 : y = b
            · exact Or.inr (Or.inl h2)
            · exact Or.inr (Or.inr ⟨h2, h1, hy⟩)
    · rintro ⟨U, hU, rfl⟩
      refine ⟨by simp, by simp, ?_⟩
      intro y hy h1 h2
      simp only [Finset.mem_insert] at hy
      rcases hy with rfl | rfl | hy
      · exact absurd rfl h1
      · exact absurd rfl h2
      · exact hU hy
  rw [heq, Finset.card_image_of_injOn, Finset.card_powerset]
  intro U hU V hV h
  simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset] at hU hV
  have hUa : a ∉ U := fun h => haF (hU h)
  have hUb : b ∉ U := fun h => hbF (hU h)
  have hVa : a ∉ V := fun h => haF (hV h)
  have hVb : b ∉ V := fun h => hbF (hV h)
  ext y
  have := congrArg (fun T => y ∈ T) h
  simp only [Finset.mem_insert] at this
  by_cases h1 : y = a
  · subst h1; simp [hUa, hVa]
  · by_cases h2 : y = b
    · subst h2; simp [hUb, hVb]
    · simpa [h1, h2] using this

theorem ps_dmu_eq {X : Type*} [Fintype X] [DecidableEq X] (w : X → ℝ) (R R' : X → X → Prop)
    (b : X) (P : Finset X → Prop) [DecidablePred P]
    (hd : ∀ S x, x ∈ symmDiff (maxSet S R) (maxSet S R') ↔ x = b ∧ P S) :
    Dmu w R R' = (Finset.univ.filter P).card * w b := by
  unfold Dmu
  have : ∀ S : Finset X, symmDiff (maxSet S R) (maxSet S R') = if P S then {b} else ∅ := by
    intro S; ext x; rw [hd]; split_ifs with h <;> simp [h]
  simp only [this]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> simp

theorem ps_ax3 {X : Type*} [Fintype X] [DecidableEq X]
    (w : X → ℝ) :
    Axiom3 (Dmu w) := by
  classical
  intro R a b hR hab
  have hrefl : ∀ x, ¬ asymmPart R x x := fun x h => h.2 (hR.1 x)
  have hD : Dmu w (prefAB a b) (prefABplus a b) = w b := (ps_eq8 w a b hab).2.2
  rw [hD]
  set F : Finset X := Finset.univ.filter (fun x => x ≠ a ∧ x ≠ b ∧ ¬ asymmPart R x b) with hF
  have haF : a ∉ F := by simp [hF]
  have hbF : b ∉ F := by simp [hF]
  constructor
  · intro hab' hba' _
    have hasym : ∀ y z, asymmPart (oplus R a b) y z ↔ asymmPart R y z ∨ (y = a ∧ z = b) := by
      intro y z
      simp only [asymmPart, oplus]
      simp only [asymmPart] at hab' hba'
      by_cases e1 : y = a <;> by_cases e2 : z = b <;> by_cases e3 : z = a <;> by_cases e4 : y = b <;>
        simp_all
    let P : Finset X → Prop := fun S => a ∈ S ∧ b ∈ S ∧ ∀ y ∈ S, ¬ asymmPart R y b
    have hd : ∀ S x, x ∈ symmDiff (maxSet S R) (maxSet S (oplus R a b)) ↔ x = b ∧ P S := by
      intro S x
      simp only [Finset.mem_symmDiff, ps_mem_max, hasym, P]
      by_cases hxb : x = b
      · subst hxb
        constructor
        · rintro (⟨⟨hx, h⟩, hn⟩ | ⟨⟨hx, h⟩, hn⟩)
          · refine ⟨rfl, ?_, hx, h⟩
            by_contra haS
            apply hn
            refine ⟨hx, fun y hy hh => ?_⟩
            rcases hh with hh | ⟨rfl, _⟩
            · exact h y hy hh
            · exact haS hy
          · exact absurd ⟨hx, fun y hy hh => h y hy (Or.inl hh)⟩ hn
        · rintro ⟨-, ha, hb, h⟩
          left
          exact ⟨⟨hb, h⟩, fun hc => hc.2 a ha (Or.inr ⟨rfl, rfl⟩)⟩
      · simp only [hxb, false_and, iff_false]
        rintro (⟨⟨hx, h⟩, hn⟩ | ⟨⟨hx, h⟩, hn⟩)
        · apply hn; refine ⟨hx, fun y hy hh => ?_⟩
          try simp only [hxb, and_false, or_false] at hh
          exact h y hy hh
        · exact hn ⟨hx, fun y hy hh => h y hy (Or.inl hh)⟩
    rw [ps_dmu_eq w R (oplus R a b) b P hd]
    have hc : (Finset.univ.filter P).card = 2 ^ F.card := by
      apply ps_count a b F haF hbF
      intro S
      simp only [P, hF, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨ha, hb, h⟩; exact ⟨ha, hb, fun y hy h1 h2 => ⟨h1, h2, h y hy⟩⟩
      · rintro ⟨ha, hb, h⟩
        refine ⟨ha, hb, fun y hy => ?_⟩
        by_cases h1 : y = a
        · subst h1; exact hab'
        · by_cases h2 : y = b
          · subst h2; exact hrefl _
          · exact (h y hy h1 h2).2.2
    have hN : Nb b R = F.card + 1 := by
      unfold Nb
      have : Finset.univ.filter (fun x => x ≠ b ∧ ¬ asymmPart R x b) = insert a F := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, hF]
        constructor
        · rintro ⟨h1, h2⟩
          by_cases hxa : x = a
          · exact Or.inl hxa
          · exact Or.inr ⟨hxa, h1, h2⟩
        · rintro (rfl | ⟨_, h1, h2⟩)
          · exact ⟨hab, hab'⟩
          · exact ⟨h1, h2⟩
      convert (congrArg Finset.card this).trans (Finset.card_insert_of_notMem haF) using 2
      ext x; simp
    rw [hc, hN, Nat.add_sub_cancel]
    push_cast; ring
  · intro hab'
    have hasym : ∀ y z, asymmPart (ominus R a b) y z ↔ asymmPart R y z ∧ ¬ (y = a ∧ z = b) := by
      intro y z
      simp only [asymmPart, ominus]
      obtain ⟨hr1, hr2⟩ := hab'
      by_cases e1 : y = a <;> by_cases e2 : z = b <;> by_cases e3 : z = a <;> by_cases e4 : y = b <;>
        simp_all
    let P : Finset X → Prop := fun S => a ∈ S ∧ b ∈ S ∧ ∀ y ∈ S, y ≠ a → ¬ asymmPart R y b
    have hd : ∀ S x, x ∈ symmDiff (maxSet S R) (maxSet S (ominus R a b)) ↔ x = b ∧ P S := by
      intro S x
      simp only [Finset.mem_symmDiff, ps_mem_max, hasym, P]
      by_cases hxb : x = b
      · subst hxb
        constructor
        · rintro (⟨⟨hx, h⟩, hn⟩ | ⟨⟨hx, h⟩, hn⟩)
          · exact absurd ⟨hx, fun y hy hh => h y hy hh.1⟩ hn
          · refine ⟨rfl, ?_, hx, fun y hy hya hh => h y hy ⟨hh, fun e => hya e.1⟩⟩
            by_contra haS
            apply hn
            refine ⟨hx, fun y hy hh => ?_⟩
            have hya : y ≠ a := by rintro rfl; exact haS hy
            exact h y hy ⟨hh, fun e => hya e.1⟩
        · rintro ⟨-, ha, hb, h⟩
          right
          refine ⟨⟨hb, fun y hy hh => h y hy (fun e => hh.2 ⟨e, rfl⟩) hh.1⟩, fun hc => ?_⟩
          exact hc.2 a ha hab'
      · simp only [hxb, false_and, iff_false]
        rintro (⟨⟨hx, h⟩, hn⟩ | ⟨⟨hx, h⟩, hn⟩)
        · exact hn ⟨hx, fun y hy hh => h y hy hh.1⟩
        · exact hn ⟨hx, fun y hy hh => h y hy ⟨hh, by simp⟩⟩
    rw [ps_dmu_eq w R (ominus R a b) b P hd]
    have hc : (Finset.univ.filter P).card = 2 ^ F.card := by
      apply ps_count a b F haF hbF
      intro S
      simp only [P, hF, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨ha, hb, h⟩; exact ⟨ha, hb, fun y hy h1 h2 => ⟨h1, h2, h y hy h1⟩⟩
      · rintro ⟨ha, hb, h⟩
        refine ⟨ha, hb, fun y hy h1 => ?_⟩
        by_cases h2 : y = b
        · subst h2; exact hrefl _
        · exact (h y hy h1 h2).2.2
    have hN : Nb b R = F.card := by
      unfold Nb
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hF]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h1, h2⟩
        rintro rfl; exact h2 hab'
      · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
    rw [hc, hN]
    push_cast; ring

theorem ps_agree1 {X : Type*} [Fintype X] [DecidableEq X]
    (d : (X → X → Prop) → (X → X → Prop) → ℝ) (hd : IsSemimetric d) (h3 : Axiom3 d)
    (w : X → ℝ) (hw : ∀ a b, a ≠ b → w b = d (prefAB a b) (prefABplus a b))
    (R : X → X → Prop) (hR : IsAcyclicOrder R) (a b : X) (hab : a ≠ b) :
    (¬ asymmPart R a b → ¬ asymmPart R b a → IsAcyclicOrder (oplus R a b) →
        d R (oplus R a b) = Dmu w R (oplus R a b)) ∧
      (asymmPart R a b → d R (ominus R a b) = Dmu w R (ominus R a b)) := by
  have hD : Dmu w (prefAB a b) (prefABplus a b) = w b := (ps_eq8 w a b hab).2.2
  constructor
  · intro h1 h2 h4
    rw [(h3 R a b hR hab).1 h1 h2 h4, (ps_ax3 w R a b hR hab).1 h1 h2 h4, hD, hw a b hab]
  · intro h1
    rw [(h3 R a b hR hab).2 h1, (ps_ax3 w R a b hR hab).2 h1, hD, hw a b hab]


section
variable {X : Type*}

theorem ps_asymm_ominus (R : X → X → Prop) (a b : X) (h : asymmPart R a b) (x y : X) :
    asymmPart (ominus R a b) x y ↔ asymmPart R x y ∧ ¬ (x = a ∧ y = b) := by
  obtain ⟨h1, h2⟩ := h
  simp only [asymmPart, ominus]
  by_cases hx : x = a <;> by_cases hy : y = b <;> by_cases hx' : x = b <;> by_cases hy' : y = a <;>
    simp_all

theorem ps_symm_ominus (R : X → X → Prop) (a b : X) (h : asymmPart R a b) (x y : X) :
    symmPart (ominus R a b) x y ↔ symmPart R x y := by
  obtain ⟨h1, h2⟩ := h
  simp only [symmPart, ominus]
  by_cases hx : x = a <;> by_cases hy : y = b <;> by_cases hx' : x = b <;> by_cases hy' : y = a <;>
    simp_all

theorem ps_asymm_oplus (R : X → X → Prop) (a b : X) (hab : a ≠ b) (h1 : ¬ R a b) (h2 : ¬ R b a)
    (x y : X) : asymmPart (oplus R a b) x y ↔ asymmPart R x y ∨ (x = a ∧ y = b) := by
  simp only [asymmPart, oplus]
  by_cases hx : x = a <;> by_cases hy : y = b <;> by_cases hx' : x = b <;> by_cases hy' : y = a <;>
    simp_all [eq_comm]

theorem ps_symm_oplus (R : X → X → Prop) (a b : X) (hab : a ≠ b) (h1 : ¬ R a b) (h2 : ¬ R b a)
    (x y : X) : symmPart (oplus R a b) x y ↔ symmPart R x y := by
  simp only [symmPart, oplus]
  by_cases hx : x = a <;> by_cases hy : y = b <;> by_cases hx' : x = b <;> by_cases hy' : y = a <;>
    simp_all [eq_comm]

theorem ps_tg_add (S : X → X → Prop) (a b : X) {u v : X}
    (h : Relation.TransGen (fun x y => S x y ∨ (x = a ∧ y = b)) u v) :
    Relation.TransGen S u v ∨ (Relation.ReflTransGen S u a ∧ Relation.ReflTransGen S b v) := by
  induction h with
  | single h =>
    rcases h with h | ⟨rfl, rfl⟩
    · exact Or.inl (Relation.TransGen.single h)
    · exact Or.inr ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | tail _ h ih =>
    rcases ih with ih | ⟨ih1, ih2⟩ <;> rcases h with h | ⟨rfl, rfl⟩
    · exact Or.inl (ih.tail h)
    · exact Or.inr ⟨ih.to_reflTransGen, Relation.ReflTransGen.refl⟩
    · exact Or.inr ⟨ih1, ih2.tail h⟩
    · exact Or.inr ⟨ih1, Relation.ReflTransGen.refl⟩

theorem ps_path (R T : X → X → Prop) (x : X) : ∀ z, Relation.TransGen (asymmPart R) z x →
    Relation.TransGen (asymmPart T) z x ∨
      ∃ a v, asymmPart R a v ∧ ¬ asymmPart T a v ∧ Relation.ReflTransGen (asymmPart T) v x := by
  intro z h
  induction h using Relation.TransGen.head_induction_on with
  | @single z h =>
    by_cases hT : asymmPart T z x
    · exact Or.inl (Relation.TransGen.single hT)
    · exact Or.inr ⟨z, x, h, hT, Relation.ReflTransGen.refl⟩
  | @head z c h _ ih =>
    rcases ih with ih | ih
    · by_cases hT : asymmPart T z c
      · exact Or.inl (Relation.TransGen.head hT ih)
      · exact Or.inr ⟨z, c, h, hT, ih.to_reflTransGen⟩
    · exact Or.inr ih

theorem ps_step [Finite X] (R T : X → X → Prop) (hT : IsAcyclicOrder T)
    (hsymm : ∀ x y, symmPart R x y ↔ symmPart T x y)
    (hne : ∃ x y, ¬ (asymmPart R x y ↔ asymmPart T x y)) :
    (∃ a b, asymmPart R a b ∧ ¬ asymmPart T a b ∧ ∀ x, asymmPart T x b → asymmPart R x b) ∨
    (∃ a b, a ≠ b ∧ ¬ R a b ∧ ¬ R b a ∧ asymmPart T a b ∧
      ¬ Relation.ReflTransGen (asymmPart R) b a) := by
  classical
  by_cases hc : ∃ a b, asymmPart R a b ∧ ¬ asymmPart T a b ∧ ∀ x, asymmPart T x b → asymmPart R x b
  · exact Or.inl hc
  right
  push_neg at hc
  have hE : ∃ y b, asymmPart T y b ∧ ¬ asymmPart R y b := by
    obtain ⟨x, y, hxy⟩ := hne
    by_cases h1 : asymmPart R x y
    · have h2 : ¬ asymmPart T x y := fun h => hxy ⟨fun _ => h, fun _ => h1⟩
      obtain ⟨z, hz⟩ := hc x y h1 h2
      exact ⟨z, y, hz⟩
    · have h2 : asymmPart T x y := by
        by_contra h2; exact hxy ⟨fun h => absurd h h1, fun h => absurd h h2⟩
      exact ⟨x, y, h2, h1⟩
  let r : X → X → Prop := fun b' b => Relation.TransGen (asymmPart T) b' b
  have hwf : WellFounded r := by
    haveI : IsTrans X r := ⟨fun _ _ _ h1 h2 => Relation.TransGen.trans h1 h2⟩
    haveI : IsIrrefl X r := ⟨fun x => hT.2 x⟩
    exact Finite.wellFounded_of_trans_of_irrefl r
  obtain ⟨y0, b0, hy0⟩ := hE
  obtain ⟨b, ⟨x, hxb⟩, hmin⟩ := hwf.has_min {b | ∃ y, asymmPart T y b ∧ ¬ asymmPart R y b}
    ⟨b0, y0, hy0⟩
  have hxb' : x ≠ b := fun h => by subst h; exact hxb.1.2 hxb.1.1
  have hnp : ¬ Relation.TransGen (asymmPart R) b x := by
    intro hp
    rcases ps_path R T x b hp with h | ⟨a, v, h1, h2, h3⟩
    · exact hT.2 b (h.tail hxb.1)
    · obtain ⟨y, hy⟩ := hc a v h1 h2
      exact hmin v ⟨y, hy⟩ (Relation.TransGen.tail' h3 hxb.1)
  refine ⟨x, b, hxb', ?_, ?_, hxb.1, ?_⟩
  · intro h
    have : R b x := by by_contra hh; exact hxb.2 ⟨h, hh⟩
    exact hxb.1.2 ((hsymm x b).1 ⟨h, this⟩).2
  · intro h
    by_cases hh : R x b
    · exact hxb.1.2 ((hsymm x b).1 ⟨hh, h⟩).2
    · exact hnp (Relation.TransGen.single ⟨h, hh⟩)
  · intro h
    rcases Relation.reflTransGen_iff_eq_or_transGen.1 h with h | h
    · exact hxb' h
    · exact hnp h

open Classical in
noncomputable def psM [Fintype X] (P T : X → X → Prop) : ℕ :=
  (Finset.univ.filter (fun p : X × X => ¬ (asymmPart P p.1 p.2 ↔ asymmPart T p.1 p.2))).card

theorem ps_m_lt [Fintype X] (P R0 T : X → X → Prop) (a b : X)
    (hout : ∀ x y, ¬ (x = a ∧ y = b) → (asymmPart R0 x y ↔ asymmPart P x y))
    (hin : ¬ (asymmPart P a b ↔ asymmPart T a b)) (hin0 : (asymmPart R0 a b ↔ asymmPart T a b)) :
    psM R0 T < psM P T := by
  classical
  unfold psM
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨(a, b), by simpa using hin, by simpa using hin0⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    by_cases hq : p.1 = a ∧ p.2 = b
    · rw [hq.1, hq.2]; exact hin
    · rwa [← hout p.1 p.2 hq]
end

theorem ps_t22 {X : Type*} [Fintype X] [DecidableEq X]
    (R T : X → X → Prop) (hR : IsAcyclicOrder R) (hT : IsAcyclicOrder T) (hne : R ≠ T)
    (hsymm : ∀ x y, symmPart R x y ↔ symmPart T x y) :
    InBetween R T T := by
  classical
  suffices H : ∀ n, ∀ P, psM P T = n → IsAcyclicOrder P → P ≠ T →
      (∀ x y, symmPart P x y ↔ symmPart T x y) → InBetween P T T from
    H _ R rfl hR hne hsymm
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hm hP hPT hPs
  have hd : ∃ x y, ¬ (asymmPart P x y ↔ asymmPart T x y) := by
    by_contra hc
    push_neg at hc
    apply hPT
    funext x y
    apply propext
    have e1 := hc x y
    have e2 := hPs x y
    have e3 := hc y x
    simp only [asymmPart, symmPart] at e1 e2 e3
    by_cases p1 : P x y <;> by_cases p2 : P y x <;> by_cases t1 : T x y <;> by_cases t2 : T y x <;>
      simp_all
  have key : ∃ R0, OneStepToward P R0 T ∧ psM R0 T < psM P T ∧
      ∀ x y, symmPart R0 x y ↔ symmPart T x y := by
    rcases ps_step P T hT hPs hd with ⟨a, b, h1, h2, h3⟩ | ⟨a, b, hab, h1, h2, h3, h4⟩
    · have hab : a ≠ b := by rintro rfl; exact h1.2 h1.1
      refine ⟨ominus P a b, ⟨⟨fun x => ⟨hP.1 x, fun h => hab (h.1.symm.trans h.2)⟩,
        fun x hx => hP.2 x (Relation.TransGen.mono
          (fun u v h => ((ps_asymm_ominus P a b h1 u v).1 h).1) _ _ hx)⟩,
        Or.inl ⟨a, b, h1, rfl, h2, h3⟩⟩, ?_, ?_⟩
      · apply ps_m_lt P _ T a b
        · intro x y hq
          rw [ps_asymm_ominus P a b h1]
          simp only [hq, not_false_eq_true, and_true]
        · exact fun h => h2 (h.1 h1)
        · exact ⟨fun h => absurd ⟨rfl, rfl⟩ ((ps_asymm_ominus P a b h1 a b).1 h).2,
            fun h => absurd h h2⟩
      · intro x y
        exact (ps_symm_ominus P a b h1 x y).trans (hPs x y)
    · refine ⟨oplus P a b, ⟨⟨fun x => ⟨Or.inl (hP.1 x), fun h => hab (h.2.symm.trans h.1)⟩,
        fun z hz => ?_⟩, Or.inr ⟨a, b, fun h => h1 h.1, fun h => h2 h.1, rfl, h3⟩⟩, ?_, ?_⟩
      · have hz' := Relation.TransGen.mono
          (p := fun x y => asymmPart P x y ∨ (x = a ∧ y = b))
          (fun u v h => (ps_asymm_oplus P a b hab h1 h2 u v).1 h) _ _ hz
        rcases ps_tg_add (asymmPart P) a b hz' with h | ⟨h5, h6⟩
        · exact hP.2 z h
        · exact h4 (h6.trans h5)
      · apply ps_m_lt P _ T a b
        · intro x y hq
          rw [ps_asymm_oplus P a b hab h1 h2]
          simp only [hq, or_false]
        · exact fun h => h1 (h.2 h3).1
        · exact ⟨fun _ => h3, fun _ => (ps_asymm_oplus P a b hab h1 h2 a b).2 (Or.inr ⟨rfl, rfl⟩)⟩
      · intro x y
        exact (ps_symm_oplus P a b hab h1 h2 x y).trans (hPs x y)
  obtain ⟨R0, hstep, hlt, hs0⟩ := key
  by_cases h0 : R0 = T
  · rw [h0] at hstep
    exact Relation.TransGen.single hstep
  · exact Relation.TransGen.head hstep (ih _ (hm ▸ hlt) R0 rfl hstep.1 h0 hs0)


theorem ps_single {X : Type*} [Fintype X] [DecidableEq X]
    (d : (X → X → Prop) → (X → X → Prop) → ℝ) (hd : IsSemimetric d) (h3 : Axiom3 d)
    (w : X → ℝ) (hw : ∀ a b, a ≠ b → w b = d (prefAB a b) (prefABplus a b))
    (P Q T : X → X → Prop) (hP : IsAcyclicOrder P) (hs : OneStepToward P Q T) :
    d P Q = Dmu w P Q := by
  rcases hs with ⟨hQ, ⟨a, b, h1, rfl, _, _⟩ | ⟨a, b, n1, n2, rfl, hTab⟩⟩
  · have hab : a ≠ b := by rintro rfl; exact h1.2 h1.1
    exact (ps_agree1 d hd h3 w hw P hP a b hab).2 h1
  · have hab : a ≠ b := by rintro rfl; exact hTab.2 hTab.1
    exact (ps_agree1 d hd h3 w hw P hP a b hab).1 n1 n2 hQ

theorem ps_agree2 {X : Type*} [Fintype X] [DecidableEq X]
    (d : (X → X → Prop) → (X → X → Prop) → ℝ) (hd : IsSemimetric d)
    (h1 : Axiom1 d) (h3 : Axiom3 d)
    (w : X → ℝ) (hw : ∀ a b, a ≠ b → w b = d (prefAB a b) (prefABplus a b))
    (R T : X → X → Prop) (hR : IsAcyclicOrder R) (hT : IsAcyclicOrder T)
    (hsymm : ∀ x y, symmPart R x y ↔ symmPart T x y) :
    d R T = Dmu w R T := by
  by_cases hRT : R = T
  · subst hRT
    rw [(hd R R R hR hR hR).2.1]
    simp [Dmu]
  have hIB := ps_t22 R T hR hT hRT hsymm
  suffices H : ∀ P, InBetween P T T → IsAcyclicOrder P → d P T = Dmu w P T from H R hIB hR
  intro P h
  unfold InBetween at h
  induction h using Relation.TransGen.head_induction_on with
  | @single P hs =>
    intro hP
    exact ps_single d hd h3 w hw P T T hP hs
  | @head P Q hs hQT ih =>
    intro hP
    have e1 : d P T = d P Q + d Q T := h1 P Q T hP hT (Relation.TransGen.single hs)
    have e2 : Dmu w P T = Dmu w P Q + Dmu w Q T := ps_add w P Q T (ps_key P Q T hT hs)
    rw [e1, e2, ih hs.1, ps_single d hd h3 w hw P Q T hP hs]

def psP0 {X : Type*} (a b c : X) : X → X → Prop :=
  fun x y => x = y ∨ (x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ (y = a ∨ y = b ∨ y = c))

section
variable {X : Type*} (a b c : X) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
include hab hbc hac

theorem ps_P0_asymm (y x : X) : asymmPart (psP0 a b c) y x ↔
    (y ≠ a ∧ y ≠ b ∧ y ≠ c ∧ (x = a ∨ x = b ∨ x = c)) := by
  simp only [asymmPart, psP0]
  by_cases h1 : y = a <;> by_cases h2 : y = b <;> by_cases h3 : y = c <;>
    by_cases h4 : x = a <;> by_cases h5 : x = b <;> by_cases h6 : x = c <;> simp_all [eq_comm]

theorem ps_P1_asymm (y x : X) : asymmPart (oplus (psP0 a b c) a b) y x ↔
    ((y ≠ a ∧ y ≠ b ∧ y ≠ c ∧ (x = a ∨ x = b ∨ x = c)) ∨ (y = a ∧ x = b)) := by
  simp only [asymmPart, psP0, oplus]
  by_cases h1 : y = a <;> by_cases h2 : y = b <;> by_cases h3 : y = c <;>
    by_cases h4 : x = a <;> by_cases h5 : x = b <;> by_cases h6 : x = c <;> simp_all [eq_comm]

theorem ps_Q1_asymm (y x : X) : asymmPart (oplus (psP0 a b c) c b) y x ↔
    ((y ≠ a ∧ y ≠ b ∧ y ≠ c ∧ (x = a ∨ x = b ∨ x = c)) ∨ (y = c ∧ x = b)) := by
  simp only [asymmPart, psP0, oplus]
  by_cases h1 : y = a <;> by_cases h2 : y = b <;> by_cases h3 : y = c <;>
    by_cases h4 : x = a <;> by_cases h5 : x = b <;> by_cases h6 : x = c <;> simp_all [eq_comm]

theorem ps_P2_asymm (y x : X) : asymmPart (oplus (oplus (psP0 a b c) a b) c b) y x ↔
    ((y ≠ a ∧ y ≠ b ∧ y ≠ c ∧ (x = a ∨ x = b ∨ x = c)) ∨ (y = a ∧ x = b) ∨ (y = c ∧ x = b)) := by
  simp only [asymmPart, psP0, oplus]
  by_cases h1 : y = a <;> by_cases h2 : y = b <;> by_cases h3 : y = c <;>
    by_cases h4 : x = a <;> by_cases h5 : x = b <;> by_cases h6 : x = c <;> simp_all [eq_comm]

theorem ps_P2_eq : oplus (oplus (psP0 a b c) c b) a b = oplus (oplus (psP0 a b c) a b) c b := by
  funext y x
  apply propext
  simp only [psP0, oplus]
  by_cases h1 : y = a <;> by_cases h2 : y = b <;> by_cases h3 : y = c <;>
    by_cases h4 : x = a <;> by_cases h5 : x = b <;> by_cases h6 : x = c <;> simp_all [eq_comm]
end

theorem ps_l34 {X : Type*} [Fintype X] [DecidableEq X]
    (d : (X → X → Prop) → (X → X → Prop) → ℝ) (hd : IsSemimetric d)
    (h1 : Axiom1 d) (h3 : Axiom3 d) (a b c : X) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    d (prefAB a b) (prefABplus a b) = d (prefAB c b) (prefABplus c b) := by
  classical
  have hcb : c ≠ b := Ne.symm hbc
  set P0 := psP0 a b c with hP0
  set P1 := oplus P0 a b with hP1
  set Q1 := oplus P0 c b with hQ1
  set P2 := oplus P1 c b with hP2
  have hQ2 : oplus Q1 a b = P2 := ps_P2_eq a b c hab hbc hac
  let f : X → ℕ := fun x => if x = b then 2 else if x = a ∨ x = c then 1 else 0
  have hfb : f b = 2 := by simp [f]
  have hfa : f a = 1 := by simp [f, hab]
  have hfc : f c = 1 := by simp [f, hcb]
  have hf0 : ∀ y, y ≠ a → y ≠ b → y ≠ c → f y = 0 := by
    intro y h1 h2 h3; simp [f, h1, h2, h3]
  have hbase : ∀ y x, (y ≠ a ∧ y ≠ b ∧ y ≠ c ∧ (x = a ∨ x = b ∨ x = c)) → f y < f x := by
    rintro y x ⟨h1, h2, h3, h4 | h4 | h4⟩ <;> subst h4 <;> simp [hf0 y h1 h2 h3, hfa, hfb, hfc]
  have hrefl0 : ∀ x, P0 x x := fun x => Or.inl rfl
  have hA0 : IsAcyclicOrder P0 := ps_acyclic_of_rank P0 hrefl0 f (by
    intro y x h; rw [ps_P0_asymm a b c hab hbc hac] at h; exact hbase y x h)
  have hA1 : IsAcyclicOrder P1 := ps_acyclic_of_rank P1
    (fun x => by simp only [P1, oplus]; exact ⟨Or.inl (Or.inl rfl), fun h => hab (h.2.symm.trans h.1)⟩) f (by
    intro y x h; rw [ps_P1_asymm a b c hab hbc hac] at h
    rcases h with h | ⟨rfl, rfl⟩
    · exact hbase y x h
    · rw [hfa, hfb]; norm_num)
  have hB1 : IsAcyclicOrder Q1 := ps_acyclic_of_rank Q1
    (fun x => by simp only [Q1, oplus]; exact ⟨Or.inl (Or.inl rfl), fun h => hcb (h.2.symm.trans h.1)⟩) f (by
    intro y x h; rw [ps_Q1_asymm a b c hab hbc hac] at h
    rcases h with h | ⟨rfl, rfl⟩
    · exact hbase y x h
    · rw [hfc, hfb]; norm_num)
  have hA2 : IsAcyclicOrder P2 := ps_acyclic_of_rank P2
    (fun x => by
      simp only [P2, P1, oplus]
      exact ⟨Or.inl ⟨Or.inl (Or.inl rfl), fun h => hab (h.2.symm.trans h.1)⟩,
        fun h => hcb (h.2.symm.trans h.1)⟩) f (by
    intro y x h; rw [ps_P2_asymm a b c hab hbc hac] at h
    rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hbase y x h
    · rw [hfa, hfb]; norm_num
    · rw [hfc, hfb]; norm_num)
  have hN0 : Nb b P0 = 2 := by
    unfold Nb; rw [Finset.card_eq_two]
    refine ⟨a, c, hac, ?_⟩
    ext x; simp only [P0, P1, Q1, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, ps_P0_asymm a b c hab hbc hac]
    by_cases h1 : x = a <;> by_cases h2 : x = b <;> by_cases h3 : x = c <;> simp_all
  have hN1 : Nb b P1 = 1 := by
    unfold Nb; rw [Finset.card_eq_one]
    refine ⟨c, ?_⟩
    ext x; simp only [P0, P1, Q1, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, ps_P1_asymm a b c hab hbc hac]
    by_cases h1 : x = a <;> by_cases h2 : x = b <;> by_cases h3 : x = c <;> simp_all
  have hM1 : Nb b Q1 = 1 := by
    unfold Nb; rw [Finset.card_eq_one]
    refine ⟨a, ?_⟩
    ext x; simp only [P0, P1, Q1, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, ps_Q1_asymm a b c hab hbc hac]
    by_cases h1 : x = a <;> by_cases h2 : x = b <;> by_cases h3 : x = c <;> simp_all
  have n0ab : ¬ asymmPart P0 a b := by rw [ps_P0_asymm a b c hab hbc hac]; simp
  have n0ba : ¬ asymmPart P0 b a := by rw [ps_P0_asymm a b c hab hbc hac]; simp
  have n0cb : ¬ asymmPart P0 c b := by rw [ps_P0_asymm a b c hab hbc hac]; simp
  have n0bc : ¬ asymmPart P0 b c := by rw [ps_P0_asymm a b c hab hbc hac]; simp
  have n1cb : ¬ asymmPart P1 c b := by rw [ps_P1_asymm a b c hab hbc hac]; simp [hac, Ne.symm hac]
  have n1bc : ¬ asymmPart P1 b c := by rw [ps_P1_asymm a b c hab hbc hac]; simp [hab, Ne.symm hab]
  have m1ab : ¬ asymmPart Q1 a b := by rw [ps_Q1_asymm a b c hab hbc hac]; simp [hac]
  have m1ba : ¬ asymmPart Q1 b a := by rw [ps_Q1_asymm a b c hab hbc hac]; simp [hbc]
  have p2ab : asymmPart P2 a b := by rw [ps_P2_asymm a b c hab hbc hac]; simp
  have p2cb : asymmPart P2 c b := by rw [ps_P2_asymm a b c hab hbc hac]; simp
  have e1 : d P0 P1 = 2 ^ (Nb b P0 - 1) * d (prefAB a b) (prefABplus a b) :=
    (h3 P0 a b hA0 hab).1 n0ab n0ba hA1
  have e2 : d P1 P2 = 2 ^ (Nb b P1 - 1) * d (prefAB c b) (prefABplus c b) :=
    (h3 P1 c b hA1 hcb).1 n1cb n1bc hA2
  have e3 : d P0 Q1 = 2 ^ (Nb b P0 - 1) * d (prefAB c b) (prefABplus c b) :=
    (h3 P0 c b hA0 hcb).1 n0cb n0bc hB1
  have e4 : d Q1 (oplus Q1 a b) = 2 ^ (Nb b Q1 - 1) * d (prefAB a b) (prefABplus a b) :=
    (h3 Q1 a b hB1 hab).1 m1ab m1ba (hQ2 ▸ hA2)
  rw [hQ2] at e4
  rw [hN0] at e1 e3; rw [hN1] at e2; rw [hM1] at e4
  have i1 : d P0 P2 = d P0 P1 + d P1 P2 :=
    h1 P0 P1 P2 hA0 hA2 (Relation.TransGen.single ⟨hA1, Or.inr ⟨a, b, n0ab, n0ba, rfl, p2ab⟩⟩)
  have i2 : d P0 P2 = d P0 Q1 + d Q1 P2 :=
    h1 P0 Q1 P2 hA0 hA2 (Relation.TransGen.single ⟨hB1, Or.inr ⟨c, b, n0cb, n0bc, rfl, hQ2 ▸ p2cb⟩⟩)
  norm_num at e1 e2 e3 e4
  linarith


theorem ps_dmu_axiom1 {X : Type*} [Fintype X] [DecidableEq X] (w : X → ℝ) :
    Axiom1 (Dmu w) := by
  intro R R0 T _ hT h
  exact ps_add w R R0 T (ps_chain R R0 T hT h)

theorem ps_ominus_acyc {X : Type*} (R : X → X → Prop) (a b : X) (hR : IsAcyclicOrder R)
    (h : asymmPart R a b) : IsAcyclicOrder (ominus R a b) := by
  have hab : a ≠ b := by rintro rfl; exact h.2 h.1
  exact ⟨fun x => ⟨hR.1 x, fun h' => hab (h'.1.symm.trans h'.2)⟩,
    fun x hx => hR.2 x (Relation.TransGen.mono
      (fun u v h' => ((ps_asymm_ominus R a b h u v).1 h').1) _ _ hx)⟩

theorem ps_dmu_congr {X : Type*} [Fintype X] [DecidableEq X] (w : X → ℝ)
    (R R1 T T1 : X → X → Prop) (h1 : asymmPart R1 = asymmPart R)
    (h2 : asymmPart T1 = asymmPart T) : Dmu w R1 T1 = Dmu w R T := by
  have h1' : ∀ x y, asymmPart R1 x y = asymmPart R x y := fun x y => by rw [h1]
  have h2' : ∀ x y, asymmPart T1 x y = asymmPart T x y := fun x y => by rw [h2]
  have m1 : ∀ S, maxSet S R1 = maxSet S R := by
    intro S; ext x; simp only [maxSet, Finset.mem_filter, h1']
  have m2 : ∀ S, maxSet S T1 = maxSet S T := by
    intro S; ext x; simp only [maxSet, Finset.mem_filter, h2']
  unfold Dmu
  simp only [m1, m2]

def psStrip {X : Type*} (R : X → X → Prop) : X → X → Prop := fun x y => x = y ∨ asymmPart R x y

theorem ps_strip_asymm {X : Type*} (R : X → X → Prop) : asymmPart (psStrip R) = asymmPart R := by
  funext x y
  apply propext
  simp only [asymmPart, psStrip]
  by_cases hxy : x = y
  · subst hxy; simp
  · by_cases p1 : R x y <;> by_cases p2 : R y x <;> simp_all [eq_comm]

theorem ps_strip_symm {X : Type*} (R : X → X → Prop) (x y : X) :
    symmPart (psStrip R) x y ↔ x = y := by
  simp only [symmPart, psStrip, asymmPart]
  by_cases hxy : x = y
  · subst hxy; simp
  · by_cases p1 : R x y <;> by_cases p2 : R y x <;> simp_all [eq_comm]

theorem ps_strip_acyc {X : Type*} (R : X → X → Prop) (hR : IsAcyclicOrder R) :
    IsAcyclicOrder (psStrip R) := by
  refine ⟨fun x => Or.inl rfl, ?_⟩
  rw [ps_strip_asymm]
  exact hR.2

theorem solution {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (d : (X → X → Prop) → (X → X → Prop) → ℝ) (hd : IsSemimetric d) :
    (Axiom1 d ∧ Axiom3 d ∧ Axiom4 d) ↔
      ∃ w : X → ℝ, (∀ x, 0 ≤ w x) ∧
        ∀ R T, IsAcyclicOrder R → IsAcyclicOrder T → d R T = Dmu w R T := by
  classical
  constructor
  · rintro ⟨h1, h3, h4⟩
    let w : X → ℝ := fun b =>
      if h : ∃ a, a ≠ b then d (prefAB h.choose b) (prefABplus h.choose b) else 0
    have hw : ∀ a b, a ≠ b → w b = d (prefAB a b) (prefABplus a b) := by
      intro a b hab
      have hex : ∃ a, a ≠ b := ⟨a, hab⟩
      simp only [w, dif_pos hex]
      by_cases hc : hex.choose = a
      · rw [hc]
      · exact ps_l34 d hd h1 h3 hex.choose b a hex.choose_spec (Ne.symm hab) hc
    have hw0 : ∀ x, 0 ≤ w x := by
      intro b
      by_cases hex : ∃ a, a ≠ b
      · obtain ⟨a, hab⟩ := hex
        rw [hw a b hab]
        have := ps_eq8 (fun _ => (0:ℝ)) a b hab
        exact (hd _ _ _ this.1 this.2.1 this.2.1).1
      · simp only [w, dif_neg hex, le_refl]
    refine ⟨w, hw0, fun R T hR hT => ?_⟩
    have hR1 := ps_strip_acyc R hR
    have hT1 := ps_strip_acyc T hT
    have hsame : ∀ x y, symmPart (psStrip R) x y ↔ symmPart (psStrip T) x y :=
      fun x y => (ps_strip_symm R x y).trans (ps_strip_symm T x y).symm
    have e := ps_agree2 d hd h1 h3 w hw _ _ hR1 hT1 hsame
    have z1 : d R (psStrip R) = 0 := h4 _ _ hR hR1 (fun x y => by rw [ps_strip_asymm])
    have z2 : d (psStrip T) T = 0 := h4 _ _ hT1 hT (fun x y => by rw [ps_strip_asymm])
    have z3 : d (psStrip R) R = 0 := h4 _ _ hR1 hR (fun x y => by rw [ps_strip_asymm])
    have z4 : d T (psStrip T) = 0 := h4 _ _ hT hT1 (fun x y => by rw [ps_strip_asymm])
    have t1 := (hd R (psStrip R) T hR hR1 hT).2.2.2
    have t2 := (hd (psStrip R) (psStrip T) T hR1 hT1 hT).2.2.2
    have t3 := (hd (psStrip R) R (psStrip T) hR1 hR hT1).2.2.2
    have t4 := (hd R T (psStrip T) hR hT hT1).2.2.2
    rw [ps_dmu_congr w R (psStrip R) T (psStrip T) (ps_strip_asymm R) (ps_strip_asymm T)] at e
    linarith
  · rintro ⟨w, hw0, hdw⟩
    refine ⟨?_, ?_, ?_⟩
    · intro R R0 T hR hT hIB
      have hR0 : IsAcyclicOrder R0 := by
        unfold InBetween at hIB
        cases hIB with
        | single h => exact h.1
        | tail _ h => exact h.1
      rw [hdw R T hR hT, hdw R R0 hR hR0, hdw R0 T hR0 hT]
      exact ps_dmu_axiom1 w R R0 T hR hT hIB
    · intro R a b hR hab
      have e8 := ps_eq8 w a b hab
      rw [hdw _ _ e8.1 e8.2.1, e8.2.2]
      constructor
      · intro n1 n2 hO
        rw [hdw R _ hR hO, (ps_ax3 w R a b hR hab).1 n1 n2 hO, e8.2.2]
      · intro h
        rw [hdw R _ hR (ps_ominus_acyc R a b hR h), (ps_ax3 w R a b hR hab).2 h, e8.2.2]
    · intro R T hR hT hs
      rw [hdw R T hR hT]
      have hTR : asymmPart T = asymmPart R := by
        funext x y; exact propext (hs x y).symm
      rw [ps_dmu_congr w R R R T rfl hTR]
      simp [Dmu]
