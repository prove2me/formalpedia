-- Prove2me | solution 1 for Supermodularity.Games.exists_monotone_greatest_least_equilibrium
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-27T01:51:52.407976+00:00
-- url     : https://prove2.me/submissions/c0f18a6a-b888-4dbc-a696-2c93824ce37c

import Mathlib
import Definitions.Def_Supermodularity_Games_IsSupermodularGame
import Definitions.Def_Supermodularity_Games_IsEquilibrium
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder

open Supermodularity.Games

/-- Counterexample: one player with strategies in `ℝ²`, parameter `t : Bool`,
`S false = [0,1] × {0}`, `S true = [0,1] × {1}`, payoffs
`F false y = y₀ - 11 y₀ y₁`, `F true y = 2 y₀ + y₁ - 3 y₀ y₁`.  All hypotheses hold, but the
unique equilibrium moves from `(1,0)` to `(0,1)`, so no monotone selection of greatest
equilibria exists. -/
theorem solution : ¬ (∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    {m : ι → ℕ} {T : Type} [PartialOrder T]
    (S : T → Set (∀ i, Fin (m i) → ℝ)) (f : T → ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (hgame : ∀ t, IsSupermodularGame (S t) (f t))
    (hSne : ∀ t, (S t).Nonempty) (hScompact : ∀ t, IsCompact (S t))
    (hSinc : ∀ ⦃t t' : T⦄, t ≤ t' →
      Supermodularity.Lattices.InducedSetOrder (S t) (S t'))
    (husc : ∀ t i (x : ∀ i, Fin (m i) → ℝ),
      UpperSemicontinuousOn (fun y : Fin (m i) → ℝ => f t i (Function.update x i y))
        {y : Fin (m i) → ℝ | Function.update x i y ∈ S t})
    (hdiff : ∀ i, ∀ x ∈ (⋃ t : T, projOthers (S t) i),
      Supermodularity.Monotonicity.IncreasingDifferencesOn
        (fun (y : Fin (m i) → ℝ) (t : T) => f t i (Function.update x i y))
        ((⋃ t : T, proj (S t) i) ×ˢ (Set.univ : Set T))),
    ∃ g l : T → (∀ i, Fin (m i) → ℝ),
      (∀ t, IsGreatest {x' : ∀ i, Fin (m i) → ℝ | IsEquilibrium (S t) (f t) x'} (g t)) ∧
      (∀ t, IsLeast {x' : ∀ i, Fin (m i) → ℝ | IsEquilibrium (S t) (f t) x'} (l t)) ∧
      Monotone g ∧ Monotone l) := by
  intro H
  let c : Bool → ℝ := fun t => if t then 1 else 0
  let S : Bool → Set (Unit → Fin 2 → ℝ) :=
    fun t => {x | x () 1 = c t ∧ 0 ≤ x () 0 ∧ x () 0 ≤ 1}
  let F : Bool → (Fin 2 → ℝ) → ℝ := fun t y =>
    if t then 2 * y 0 + y 1 - 3 * y 0 * y 1 else y 0 - 11 * y 0 * y 1
  let f : Bool → Unit → (Unit → Fin 2 → ℝ) → ℝ := fun t i x => F t (x i)
  have hupd : ∀ (x : Unit → Fin 2 → ℝ) (i : Unit) (y : Fin 2 → ℝ),
      Function.update x i y = fun _ => y := by
    intro x i y; funext j; cases i; cases j; simp
  have hfu : ∀ t (x : Unit → Fin 2 → ℝ) (i : Unit) (y : Fin 2 → ℝ),
      f t i (Function.update x i y) = F t y := by
    intro t x i y; simp only [f, hupd]
  have hproj : ∀ t, proj (S t) () ⊆ {y : Fin 2 → ℝ | y 1 = c t ∧ 0 ≤ y 0 ∧ y 0 ≤ 1} := by
    rintro t y ⟨x, hx⟩
    rw [hupd] at hx
    exact hx
  have hc01 : ∀ t, 0 ≤ c t ∧ c t ≤ 1 := by intro t; cases t <;> simp [c]
  -- the game hypotheses
  have hgame : ∀ t, IsSupermodularGame (S t) (f t) := by
    intro t
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro a ha b hb
      refine ⟨?_, ?_, ?_⟩
      · show max (a () 1) (b () 1) = c t
        rw [ha.1, hb.1, max_self]
      · show 0 ≤ max (a () 0) (b () 0)
        exact le_max_of_le_left ha.2.1
      · show max (a () 0) (b () 0) ≤ 1
        exact max_le ha.2.2 hb.2.2
    · intro a ha b hb
      refine ⟨?_, ?_, ?_⟩
      · show min (a () 1) (b () 1) = c t
        rw [ha.1, hb.1, min_self]
      · show 0 ≤ min (a () 0) (b () 0)
        exact le_min ha.2.1 hb.2.1
      · show min (a () 0) (b () 0) ≤ 1
        exact min_le_of_left_le ha.2.2
    · intro i x _ y1 hy1 y2 hy2
      cases i
      simp only [hfu]
      have h1 := hproj t hy1
      have h2 := hproj t hy2
      rcases le_total (y1 0) (y2 0) with h | h
      · have hle : y1 ≤ y2 := by
          intro k; fin_cases k
          · exact h
          · show y1 1 ≤ y2 1
            rw [h1.1, h2.1]
        rw [sup_eq_right.mpr hle, inf_eq_left.mpr hle]; linarith
      · have hle : y2 ≤ y1 := by
          intro k; fin_cases k
          · exact h
          · show y2 1 ≤ y1 1
            rw [h1.1, h2.1]
        rw [sup_eq_left.mpr hle, inf_eq_right.mpr hle]
    · intro i x' x'' _ y1 _ y2 _ _
      simp only [hfu, sub_self, le_refl]
  have hSne : ∀ t, (S t).Nonempty := fun t =>
    ⟨fun _ => ![0, c t], by simp [S]⟩
  have hScompact : ∀ t, IsCompact (S t) := by
    intro t
    have hbox : IsCompact (Set.univ.pi fun _ : Unit =>
        Set.univ.pi fun _ : Fin 2 => Set.Icc (-1 : ℝ) 2) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
    refine hbox.of_isClosed_subset ?_ ?_
    · have hc0 : Continuous fun x : Unit → Fin 2 → ℝ => x () 0 :=
        (continuous_apply 0).comp (continuous_apply ())
      have hc1 : Continuous fun x : Unit → Fin 2 → ℝ => x () 1 :=
        (continuous_apply 1).comp (continuous_apply ())
      exact (isClosed_eq hc1 continuous_const).inter
        ((isClosed_le continuous_const hc0).inter (isClosed_le hc0 continuous_const))
    · intro x hx u _ k _
      cases u
      obtain ⟨h1, h0, h0'⟩ := hx
      have := hc01 t
      fin_cases k
      · exact ⟨by simp; linarith, by simp; linarith⟩
      · simp only [Fin.mk_one, Fin.isValue]
        rw [h1]; exact ⟨by linarith, by linarith⟩
  have hSinc : ∀ ⦃t t' : Bool⦄, t ≤ t' →
      Supermodularity.Lattices.InducedSetOrder (S t) (S t') := by
    intro t t' htt' a ha b hb
    have hct : c t ≤ c t' := by
      rcases t with _ | _ <;> rcases t' with _ | _
      · simp [c]
      · simp [c]
      · exact absurd htt' (by decide)
      · simp [c]
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · show min (a () 1) (b () 1) = c t
      rw [ha.1, hb.1]; exact min_eq_left hct
    · show 0 ≤ min (a () 0) (b () 0)
      exact le_min ha.2.1 hb.2.1
    · show min (a () 0) (b () 0) ≤ 1
      exact min_le_of_left_le ha.2.2
    · show max (a () 1) (b () 1) = c t'
      rw [ha.1, hb.1]; exact max_eq_right hct
    · show 0 ≤ max (a () 0) (b () 0)
      exact le_max_of_le_left ha.2.1
    · show max (a () 0) (b () 0) ≤ 1
      exact max_le ha.2.2 hb.2.2
  have husc : ∀ t i (x : Unit → Fin 2 → ℝ),
      UpperSemicontinuousOn (fun y : Fin 2 → ℝ => f t i (Function.update x i y))
        {y : Fin 2 → ℝ | Function.update x i y ∈ S t} := by
    intro t i x
    simp only [hfu]
    apply UpperSemicontinuous.upperSemicontinuousOn
    apply Continuous.upperSemicontinuous
    have h0 : Continuous fun y : Fin 2 → ℝ => y 0 := continuous_apply 0
    have h1 : Continuous fun y : Fin 2 → ℝ => y 1 := continuous_apply 1
    cases t
    · show Continuous (fun y : Fin 2 → ℝ => y 0 - 11 * y 0 * y 1)
      fun_prop
    · show Continuous (fun y : Fin 2 → ℝ => 2 * y 0 + y 1 - 3 * y 0 * y 1)
      fun_prop
  have hdiff : ∀ i, ∀ x ∈ (⋃ t : Bool, projOthers (S t) i),
      Supermodularity.Monotonicity.IncreasingDifferencesOn
        (fun (y : Fin 2 → ℝ) (t : Bool) => f t i (Function.update x i y))
        ((⋃ t : Bool, proj (S t) i) ×ˢ (Set.univ : Set Bool)) := by
    intro i x _ t' t'' hlt y1 hy1 y2 hy2 hle
    cases i
    have hft : t' = false ∧ t'' = true := by
      revert hlt; cases t' <;> cases t'' <;> decide
    obtain ⟨rfl, rfl⟩ := hft
    simp only [hfu, F]
    obtain ⟨⟨hs1, -⟩, -⟩ := hy1
    obtain ⟨⟨hs2, -⟩, -⟩ := hy2
    obtain ⟨t1, ht1⟩ := Set.mem_iUnion.mp hs1
    obtain ⟨t2, ht2⟩ := Set.mem_iUnion.mp hs2
    have a1 := hproj t1 ht1
    have a2 := hproj t2 ht2
    have b1 := hc01 t1
    have b2 := hc01 t2
    have l0 : y1 0 ≤ y2 0 := hle 0
    have l1 : y1 1 ≤ y2 1 := hle 1
    simp only [if_true, Bool.false_eq_true, if_false]
    nlinarith [mul_le_mul l0 l1 (by linarith [a1.1]) (by linarith [a2.2.1])]
  obtain ⟨g, l, hg, -, hgm, -⟩ :=
    @H Unit _ _ (fun _ => 2) Bool _ S f hgame hSne hScompact hSinc husc hdiff
  -- the equilibria
  have hg0 : g false () 0 = 1 := by
    obtain ⟨⟨h1, h0, h0'⟩, heq⟩ := (hg false).1
    by_contra hne
    have hlt : g false () 0 < 1 := lt_of_le_of_ne h0' hne
    have hfeas : Function.update (g false) () ![1, 0] ∈ S false := by
      rw [hupd]; simp [S, c]
    have := heq () ![1, 0] hfeas
    rw [hfu] at this
    simp only [f, F, c, if_false, Bool.false_eq_true] at this h1
    simp at this
    rw [h1] at this
    linarith
  have hg1 : g true () 0 = 0 := by
    obtain ⟨⟨h1, h0, h0'⟩, heq⟩ := (hg true).1
    by_contra hne
    have hlt : 0 < g true () 0 := lt_of_le_of_ne h0 (Ne.symm hne)
    have hfeas : Function.update (g true) () ![0, 1] ∈ S true := by
      rw [hupd]; simp [S, c]
    have := heq () ![0, 1] hfeas
    rw [hfu] at this
    simp only [f, F, c, if_true] at this h1
    simp at this
    rw [h1] at this
    linarith
  have := hgm (show (false : Bool) ≤ true from by decide) () 0
  rw [hg0, hg1] at this
  norm_num at this
