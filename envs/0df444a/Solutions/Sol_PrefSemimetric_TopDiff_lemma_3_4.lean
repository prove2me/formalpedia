-- Prove2me | solution 1 for PrefSemimetric.TopDiff.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T17:11:23.019078+00:00
-- url     : https://prove2.me/submissions/7c4c59a7-f3dd-4720-bdb9-7d4333cc27e2

import Mathlib
import Definitions.Def_PrefSemimetric_TopDiff_Model

open PrefSemimetric.TopDiff

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

theorem solution {X : Type*} [Fintype X] [DecidableEq X]
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
