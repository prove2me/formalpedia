-- Prove2me | solution 1 for Pi.exists_upper_bounds_of_forall_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T07:51:45.353994+00:00
-- url     : https://prove2.me/submissions/af7bc58a-2b49-40be-a21d-129c3415531a

import Mathlib
import Definitions.Def_WassDDRO_Extremal_Setting
import Definitions.Def_WassDDRO_Reduction_Setting

-- carved verbatim out of submission 9d9b1da1-23a8-4b1d-b0ad-3d6a8366c2eb, lines 709-763

section
set_option autoImplicit false

theorem solution {N : ℕ} (hN : 0 < N)
    (T : Fin N → Set ℝ) (hne : ∀ i, (T i).Nonempty) (B : ℝ)
    (hbound : ∀ r : Fin N → ℝ, (∀ i, r i∈T i) → (∑ i, r i) ≤ B) :
    ∃ s : Fin N → ℝ, (∀ i r, r∈T i → r ≤ s i) ∧ (∑ i, s i) ≤ B := by
  classical
  choose r0 hr0 using hne
  have hbdd : ∀ i, BddAbove (T i) := by
    intro i
    refine ⟨B-(∑ j ∈ Finset.univ.erase i, r0 j),?_⟩
    intro r hr
    have hu : ∀ j, Function.update r0 i r j ∈ T j := by
      intro j
      by_cases hji : j=i
      · subst j
        simpa using hr
      · simpa [Function.update_of_ne hji] using hr0 j
    have hh := hbound (Function.update r0 i r) hu
    rw [←Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hh
    have hs : (∑ j ∈ Finset.univ.erase i, Function.update r0 i r j) =
        ∑ j ∈ Finset.univ.erase i, r0 j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _
    rw [Function.update_self,hs] at hh
    linarith
  let s : Fin N → ℝ := fun i => sSup (T i)
  refine ⟨s,fun i r hr => le_csSup (hbdd i) hr,?_⟩
  by_contra hh
  have hgap : 0 < (∑ i, s i)-B := sub_pos.mpr (lt_of_not_ge hh)
  let η := ((∑ i, s i)-B)/(2*(N : ℝ))
  have hη : 0 < η := by dsimp [η];exact div_pos hgap (by positivity)
  have happ : ∀ i, ∃ r∈T i, s i-η<r := by
    intro i
    exact exists_lt_of_lt_csSup ⟨r0 i,hr0 i⟩ (by dsimp [s];linarith)
  choose r hr hrap using happ
  have hsum : (∑ i, (s i-η)) ≤ ∑ i, r i := Finset.sum_le_sum (fun i _ => (hrap i).le)
  have hu := hbound r hr
  have hcalc : (∑ i, (s i-η)) = (∑ i, s i)-(N : ℝ)*η := by
    rw [Finset.sum_sub_distrib]
    simp
  have hηeq : (2*(N : ℝ))*η = (∑ i, s i)-B := by
    dsimp [η]
    field_simp
  rw [hcalc] at hsum
  nlinarith

end
