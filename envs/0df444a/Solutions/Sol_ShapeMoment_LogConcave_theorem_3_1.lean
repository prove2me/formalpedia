-- Prove2me | solution 1 for ShapeMoment.LogConcave.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:42:24.495005+00:00
-- url     : https://prove2.me/submissions/c2f9f42a-3f3c-487e-8238-facfdca2ced9

import Mathlib

set_option autoImplicit false

open Set

theorem solution (n : ℕ) (S : Set (Fin n → ℝ)) (c : (Fin n → ℝ) → ℝ)
    (hne : S.Nonempty) (hcompact : IsCompact S)
    (hlsc : LowerSemicontinuous c) (hqc : QuasiconcaveOn ℝ Set.univ c) :
    ∃ x ∈ S.extremePoints ℝ, IsMinOn c S x := by
  obtain ⟨x, hxS, hxmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne hcompact (hlsc.lowerSemicontinuousOn S)
  by_contra hcon
  -- every extreme point has value strictly above the minimum
  have hext : ∀ e ∈ S.extremePoints ℝ, c x < c e := by
    intro e he
    have h1 : c x ≤ c e := isMinOn_iff.1 hxmin e (extremePoints_subset he)
    refine lt_of_le_of_ne h1 fun h => hcon ⟨e, he, isMinOn_iff.2 fun y hy => ?_⟩
    rw [← h]; exact isMinOn_iff.1 hxmin y hy
  set V : Set (Fin n → ℝ) := {y | c x < c y} with hV
  have hVopen : IsOpen V := hlsc.isOpen_preimage (c x)
  have hVconv : Convex ℝ V := by
    intro a ha b hb s t hs ht hst
    have hq := hqc (min (c a) (c b))
    have ha' : a ∈ {y ∈ (univ : Set (Fin n → ℝ)) | min (c a) (c b) ≤ c y} := ⟨mem_univ _, min_le_left _ _⟩
    have hb' : b ∈ {y ∈ (univ : Set (Fin n → ℝ)) | min (c a) (c b) ≤ c y} := ⟨mem_univ _, min_le_right _ _⟩
    have := (hq ha' hb' hs ht hst).2
    exact lt_of_lt_of_le (lt_min ha hb) this
  have hxV : x ∉ V := fun h => lt_irrefl (c x) h
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hVconv hVopen hxV
  obtain ⟨z, hzS, hz⟩ := hcompact.exists_isMaxOn hne f.continuous.continuousOn
  have hexp : IsExposed ℝ S ({ y ∈ S | ∀ w ∈ S, f w ≤ f y }) := fun _ => ⟨f, rfl⟩
  obtain ⟨e, he⟩ := (hexp.isCompact hcompact).extremePoints_nonempty ⟨z, hzS, hz⟩
  have heS : e ∈ S.extremePoints ℝ := hexp.isExtreme.extremePoints_subset_extremePoints he
  have h1 : f x ≤ f e := he.1.2 x hxS
  have h2 : f e < f x := hf e (hext e heS)
  exact absurd h1 (not_le.2 h2)
