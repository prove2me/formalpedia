-- Prove2me | solution 1 for SkutellaCQP.MaxSNP.half_and_three
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:15:07.594968+00:00
-- url     : https://prove2.me/submissions/4f864f8f-dc22-4087-a87e-ae142225d5d5

import Mathlib
import Definitions.Def_SkutellaCQP_MaxSNP_Setting

open SkutellaCQP.MaxSNP Finset

theorem solution {n m : ℕ} (I : Occ3Max3Sat n m) (hI : I.IsValid) :
    (m : ℝ) / 2 ≤ optSat I ∧ n ≤ 3 * m := by
  classical
  have hcover : (univ : Finset (Fin m)) ⊆
      (univ.filter fun c => Satisfies (fun _ => true) (I.clause c)) ∪
      (univ.filter fun c => Satisfies (fun _ => false) (I.clause c)) := by
    intro c hc
    have hne : (I.clause c).Nonempty := card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one (hI.1 c).1)
    obtain ⟨⟨x, b⟩, hb⟩ := hne
    cases b
    · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨mem_univ _, ⟨(x, false), hb, rfl⟩⟩))
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨mem_univ _, ⟨(x, true), hb, rfl⟩⟩))
  have hc : m ≤ satCount I (fun _ => true) + satCount I (fun _ => false) := by
    simpa [satCount] using (card_le_card hcover).trans (card_union_le _ _)
  have ht : satCount I (fun _ => true) ≤ optSat I := le_sup (mem_univ _)
  have hf : satCount I (fun _ => false) ≤ optSat I := le_sup (mem_univ _)
  constructor
  · have hn : m ≤ 2 * optSat I := by omega
    have hr : (m : ℝ) ≤ 2 * (optSat I : ℝ) := by exact_mod_cast hn
    linarith
  · have hvars : (univ : Finset (Fin n)) ⊆ univ.biUnion (fun c => (I.clause c).image Prod.fst) := by
      intro x hx
      obtain ⟨c, b, hb⟩ := hI.2.2 x
      exact mem_biUnion.mpr ⟨c, mem_univ _, mem_image.mpr ⟨(x,b), hb, rfl⟩⟩
    calc
      n = (univ : Finset (Fin n)).card := by simp
      _ ≤ (univ.biUnion fun c => (I.clause c).image Prod.fst).card := card_le_card hvars
      _ ≤ ∑ c, ((I.clause c).image Prod.fst).card := card_biUnion_le
      _ ≤ ∑ c, (I.clause c).card := sum_le_sum (fun c _ => card_image_le)
      _ ≤ ∑ _c : Fin m, 3 := sum_le_sum (fun c _ => (hI.1 c).2)
      _ = 3 * m := by simp [Nat.mul_comm]

#print axioms solution
