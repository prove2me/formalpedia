-- Prove2me | solution 1 for TenChallenges.challenge_04_r1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:57:34.219685+00:00
-- url     : https://prove2.me/submissions/09a04e87-6656-4a2e-9cb9-306a277bad95

import Definitions.Def_TenChallenges_Challenge_04

open SimpleGraph

open TenChallenges in
theorem solution : statement_04 1 := by
  intro W V _ _ _ H G hB
  classical
  obtain ⟨X, Y, hbip, hcov, hX, hY⟩ := hB
  unfold SidorenkoFor homDensity
  have hVpos : (0:ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  by_cases hE : ∃ a b, H.Adj a b
  · obtain ⟨a, b, hab⟩ := hE
    have hab' : a ≠ b := H.ne_of_adj hab
    have hX1 := (Set.ncard_le_one (s := X)).mp hX
    have hY1 := (Set.ncard_le_one (s := Y)).mp hY
    have hall : ∀ w : W, w = a ∨ w = b := by
      intro w
      have hw : w ∈ X ∪ Y := by rw [hcov]; exact Set.mem_univ w
      rcases hbip.mem_of_adj hab with ⟨haX, hbY⟩ | ⟨haY, hbX⟩
      · rcases hw with hw | hw
        · exact Or.inl (hX1 w hw a haX)
        · exact Or.inr (hY1 w hw b hbY)
      · rcases hw with hw | hw
        · exact Or.inr (hX1 w hw b hbX)
        · exact Or.inl (hY1 w hw a haY)
    have hadj : ∀ x y : W, H.Adj x y ↔ x ≠ y := by
      intro x y
      refine ⟨H.ne_of_adj, fun hxy => ?_⟩
      rcases hall x with rfl | rfl <;> rcases hall y with rfl | rfl
      · exact absurd rfl hxy
      · exact hab
      · exact hab.symm
      · exact absurd rfl hxy
    have hW : Fintype.card W = 2 := by
      have huniv : (Finset.univ : Finset W) = {a, b} := by
        ext w
        simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
        exact hall w
      rw [← Finset.card_univ, huniv, Finset.card_pair_eq_two_iff.mpr hab']
    have hedge : H.edgeSet = {s(a, b)} := by
      ext e
      induction e using Sym2.ind with
      | h x y =>
        rw [SimpleGraph.mem_edgeSet, hadj, Set.mem_singleton_iff, Sym2.eq_iff]
        constructor
        · intro hxy
          rcases hall x with rfl | rfl <;> rcases hall y with rfl | rfl
          · exact absurd rfl hxy
          · exact Or.inl ⟨rfl, rfl⟩
          · exact Or.inr ⟨rfl, rfl⟩
          · exact absurd rfl hxy
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact hab'
          · exact hab'.symm
    have hcardE : Nat.card H.edgeSet = 1 := by
      rw [hedge, Nat.card_unique]
    let e : W ≃ Fin 2 := Fintype.equivFinOfCardEq hW
    have hhom : Nat.card {f : W → V // ∀ ⦃x y : W⦄, H.Adj x y → G.Adj (f x) (f y)} =
        Nat.card {f : Fin 2 → V // ∀ ⦃x y : Fin 2⦄, (completeGraph (Fin 2)).Adj x y →
          G.Adj (f x) (f y)} := by
      apply Nat.card_congr
      refine Equiv.subtypeEquiv (Equiv.arrowCongr e (Equiv.refl V)) (fun f => ?_)
      constructor
      · intro hf i j hij
        have hij' : i ≠ j := hij
        simp only [Equiv.arrowCongr_apply, Equiv.refl_apply, Function.comp_apply]
        apply hf
        rw [hadj]
        intro h
        exact hij' (by simpa using congrArg e h)
      · intro hf x y hxy
        have h1 := hf (x := e x) (y := e y)
          (show e x ≠ e y from fun h => (hadj x y).mp hxy (e.injective h))
        simpa [Equiv.arrowCongr_apply] using h1
    simp only [hcardE, pow_one, hhom, hW, Fintype.card_fin, ge_iff_le, le_refl]
  · push_neg at hE
    have hedge : H.edgeSet = ∅ := by
      ext e
      induction e using Sym2.ind with
      | h x y => simp [hE x y]
    have hcardE : Nat.card H.edgeSet = 0 := by
      rw [hedge]
      simp
    have hhom : Nat.card {f : W → V // ∀ ⦃x y : W⦄, H.Adj x y → G.Adj (f x) (f y)} =
        Fintype.card V ^ Fintype.card W := by
      rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun f x y h => absurd h (hE x y))),
        Nat.card_eq_fintype_card, Fintype.card_fun]
    rw [hcardE, pow_zero, hhom, ge_iff_le]
    push_cast
    exact (div_self (pow_pos hVpos _).ne').ge
