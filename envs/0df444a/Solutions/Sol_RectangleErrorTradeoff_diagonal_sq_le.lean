-- Prove2me | solution 1 for RectangleErrorTradeoff.diagonal_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T21:24:01.909586+00:00
-- url     : https://prove2.me/submissions/c6ff57ed-0de5-4597-a1e1-1b16eae3ee28

import Mathlib

set_option autoImplicit false

theorem solution {A I : Type*} [DecidableEq A] [Fintype I]
    (left right : I → A → Prop) (diag : Finset A) (bad : Finset (A × A))
    (positive : ∀ a ∈ diag, (∃ i, left i a ∧ right i a))
    (includesErrors : ∀ a ∈ diag, ∀ b ∈ diag,
      a ≠ b → (∃ i, left i a ∧ right i b) → (a,b) ∈ bad) :
    diag.card^2 ≤ Fintype.card I * (diag.card + bad.card) := by
  classical
  let D := {a // a ∈ diag}
  let label (a : D) : I := Classical.choose (positive a.val a.property)
  have tagged (a : D) : left (label a) a.val ∧ right (label a) a.val :=
    Classical.choose_spec (positive a.val a.property)
  let group (i : I) : Finset D := Finset.univ.filter fun a => label a = i
  let pairs : Finset (D × D) := Finset.univ.filter fun p => label p.1 = label p.2
  have diagSize : Fintype.card D = diag.card := Fintype.card_coe diag
  have countGroup : (∑ i : I, (group i).card) = diag.card := by
    rw [← diagSize]
    simpa only [group, Finset.card_univ] using
      (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset D)) (t := (Finset.univ : Finset I))
        (f := label) (fun _ _ => Finset.mem_univ _)).symm
  have fibers (i : I) :
      pairs.filter (fun p => label p.1 = i) = (group i ×ˢ group i) := by
    apply Finset.ext
    intro p
    rw [Finset.mem_product]
    simp only [pairs, group, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨same, first⟩ => ⟨first,same.symm.trans first⟩,
      fun ⟨first,second⟩ => ⟨first.trans second.symm,first⟩⟩
  have sumPairs : pairs.card = ∑ i : I, (group i).card ^ 2 := by
    calc
      pairs.card = ∑ i : I, (pairs.filter (fun p => label p.1 = i)).card :=
        Finset.card_eq_sum_card_fiberwise
          (s := pairs) (t := (Finset.univ : Finset I)) (f := fun p => label p.1)
          (fun _ _ => Finset.mem_univ _)
      _ = _ := Finset.sum_congr rfl (fun i _ => by rw [fibers i,Finset.card_product,pow_two])
  let equalPairs := pairs.filter fun p => p.1 = p.2
  let crossPairs := pairs.filter fun p => p.1 ≠ p.2
  have diagUpper : equalPairs.card ≤ diag.card := by
    apply Finset.card_le_card_of_injOn (fun p : D × D => p.1.val)
    · intro p _
      exact p.1.property
    · intro p hp q hq same
      have hp' : p.1 = p.2 := (Finset.mem_filter.mp hp).2
      have hq' : q.1 = q.2 := (Finset.mem_filter.mp hq).2
      have first : p.1 = q.1 := Subtype.ext same
      exact Prod.ext first (hp'.symm.trans (first.trans hq'))
  have crossUpper : crossPairs.card ≤ bad.card := by
    apply Finset.card_le_card_of_injOn (fun p : D × D => (p.1.val,p.2.val))
    · intro p present
      obtain ⟨seen, different⟩ := Finset.mem_filter.mp present
      have common : label p.1 = label p.2 := (Finset.mem_filter.mp seen).2
      exact includesErrors _ p.1.property _ p.2.property
        (fun h => different (Subtype.ext h)) ⟨label p.1,(tagged p.1).1,common.symm ▸ (tagged p.2).2⟩
    · intro p _ q _ same
      exact Prod.ext (Subtype.ext (congrArg Prod.fst same)) (Subtype.ext (congrArg Prod.snd same))
  have split : equalPairs.card + crossPairs.card = pairs.card :=
    Finset.card_filter_add_card_filter_not (s := pairs) (fun p => p.1 = p.2)
  have bound : pairs.card ≤ diag.card + bad.card := by omega
  have cauchy : (∑ i : I, (group i).card)^2 ≤ Fintype.card I * ∑ i : I, (group i).card^2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset I) (fun _ => (1 : ℕ))
      (fun i => (group i).card)
  rw [countGroup, ← sumPairs] at cauchy
  exact cauchy.trans (Nat.mul_le_mul_left _ bound)

#print axioms solution
