-- Prove2me | solution 1 for OnlineCAP.proposition_3_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:37:49.969426+00:00
-- url     : https://prove2.me/submissions/d9a24034-6337-4f25-8578-ce79511f98dd

import Mathlib
import Definitions.Def_OnlineCAP_crosses
import Definitions.Def_OnlineCAP_RL
import Definitions.Def_OnlineCAP_RT

open MeasureTheory Filter Asymptotics

open OnlineCAP in
theorem solution (n i j a b : ℕ) (hij : i < j) (hjn : j < n) (ha : 1 ≤ a) (hab : a ≤ b)
    (hbn : b ≤ n - 1) :
    crosses s((⟨i, by omega⟩ : Fin n), (⟨j, hjn⟩ : Fin n))
        (Finset.univ.filter (fun v : Fin n => a ≤ v.val ∧ v.val ≤ b)) ↔
      ((i : ℝ), (j : ℝ)) ∈ RL a b ∪ RT a b := by
  have h1 : (i : ℝ) ≤ (a : ℝ) - 1 ↔ i + 1 ≤ a := by
    rw [le_sub_iff_add_le]; norm_cast
  have h2 : (b : ℝ) + 1 ≤ (j : ℝ) ↔ b + 1 ≤ j := by norm_cast
  have hL : crosses s((⟨i, by omega⟩ : Fin n), (⟨j, hjn⟩ : Fin n))
        (Finset.univ.filter (fun v : Fin n => a ≤ v.val ∧ v.val ≤ b)) ↔
      ((a ≤ i ∧ i ≤ b) ∨ (a ≤ j ∧ j ≤ b)) ∧ (¬ (a ≤ i ∧ i ≤ b) ∨ ¬ (a ≤ j ∧ j ≤ b)) := by
    unfold crosses
    constructor
    · rintro ⟨⟨v, hv, hvC⟩, ⟨w, hw, hwC⟩⟩
      rw [Sym2.mem_iff] at hv hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hvC hwC
      constructor
      · rcases hv with rfl | rfl
        · exact Or.inl hvC
        · exact Or.inr hvC
      · rcases hw with rfl | rfl
        · exact Or.inl hwC
        · exact Or.inr hwC
    · rintro ⟨hA, hB⟩
      constructor
      · rcases hA with hA | hA
        · exact ⟨⟨i, by omega⟩, Sym2.mem_mk_left _ _, by simpa using hA⟩
        · exact ⟨⟨j, hjn⟩, Sym2.mem_mk_right _ _, by simpa using hA⟩
      · rcases hB with hB | hB
        · exact ⟨⟨i, by omega⟩, Sym2.mem_mk_left _ _, by simpa using hB⟩
        · exact ⟨⟨j, hjn⟩, Sym2.mem_mk_right _ _, by simpa using hB⟩
  rw [hL]
  simp only [RL, RT, Set.mem_union, Set.mem_prod, Set.mem_Iic, Set.mem_Icc, Set.mem_Ici, h1, h2,
    Nat.cast_le]
  omega
