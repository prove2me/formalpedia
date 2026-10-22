-- Prove2me | solution 2 for Tegmark.spacelike_slice
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:44:19.641867+00:00
-- url     : https://prove2.me/submissions/4e9c8c45-5804-42c6-b683-053f223785b6

import Mathlib
import Definitions.Def_Tegmark_sig
import Definitions.Def_Tegmark_phys
import Definitions.Def_Tegmark_ensemble
set_option autoImplicit false

open Tegmark

theorem solution (n : ℕ) : HasSpacelikeHyperplane n 1 := by
  refine ⟨LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ⊕ Fin 1 => ℝ) (Sum.inr 0), ?_, ?_⟩
  · intro h
    have := LinearMap.congr_fun h (Pi.single (Sum.inr 0) 1 : World n 1)
    simp at this
  · intro v hv hne
    have hv0 : v (Sum.inr 0) = 0 := by simpa using hv
    have hex : ∃ i : Fin n, v (Sum.inl i) ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply hne
      funext x
      rcases x with i | j
      · exact hc i
      · have : j = 0 := Subsingleton.elim _ _
        subst this; exact hv0
    obtain ⟨i, hi⟩ := hex
    unfold teg
    have h1 : 0 < ∑ i, v (Sum.inl i) ^ 2 :=
      lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun i => v (Sum.inl i) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i))
    simp [hv0]
    exact h1
