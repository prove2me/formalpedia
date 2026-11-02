-- Prove2me | solution 1 for WilliamsonShmoys.lower_half_plane_bridge_for_planar_drawing__p2m_3e6d8a60_d3d3_4ec8_8c95_56c4b76ce917_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:36:23.751078+00:00
-- url     : https://prove2.me/submissions/875f914b-22dc-4530-9ea2-69180a1ef7d6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hdraw : Function.Injective p ∧
      (∀ a b, a < b → G.Adj a b →
        ContinuousOn (arc a b) (Set.Icc 0 1) ∧ Set.InjOn (arc a b) (Set.Icc 0 1) ∧
        arc a b 0 = p a ∧ arc a b 1 = p b ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w) ∧
      (∀ a b c d, a < b → c < d → G.Adj a b → G.Adj c d →
        (a, b) ≠ (c, d) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          arc a b t = arc c d s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)))
    {u v : V}
    (hpu : (p u).2 = 0) (hpv : (p v).2 = 0)
    (hx : (p u).1 < (p v).1)
    (hvertices : ∀ w, w ≠ u → w ≠ v → 0 < (p w).2)
    (harcs : ∀ a b, a < b → G.Adj a b →
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 < (arc a b t).2) :
    ∃ gamma : ℝ → ℝ × ℝ,
      ContinuousOn gamma (Set.Icc (0 : ℝ) 1) ∧ Set.InjOn gamma (Set.Icc (0 : ℝ) 1) ∧
      gamma 0 = p u ∧ gamma 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w) ∧
      (∀ a b, a < b → G.Adj a b → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        gamma t = arc a b s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) := by
  let gamma : ℝ → ℝ × ℝ := fun t => ((p u).1 + t * ((p v).1 - (p u).1), 0)
  have hleft (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) : (p u).1 < (gamma t).1 := by
    have hm := mul_pos ht.1 (sub_pos.mpr hx)
    dsimp [gamma]
    linarith
  have hright (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) : (gamma t).1 < (p v).1 := by
    have hm := mul_pos (sub_pos.mpr ht.2) (sub_pos.mpr hx)
    dsimp [gamma]
    linarith
  have havert (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) (w : V) : gamma t ≠ p w := by
    intro heq
    by_cases hwu : w = u
    · subst w
      have he := congrArg Prod.fst heq
      have hl := hleft t ht
      dsimp [gamma] at he
      linarith
    · by_cases hwv : w = v
      · subst w
        have he := congrArg Prod.fst heq
        have hr := hright t ht
        dsimp [gamma] at he
        linarith
      · have hw := hvertices w hwu hwv
        have he := congrArg Prod.snd heq
        dsimp [gamma] at he
        linarith
  refine ⟨gamma, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [gamma]; fun_prop
  · intro x hx' y hy' hxy
    have he := congrArg Prod.fst hxy
    have hd : 0 < (p v).1 - (p u).1 := sub_pos.mpr hx
    rcases lt_trichotomy x y with hxy' | hxy' | hyx'
    · have hm := mul_pos hd (sub_pos.mpr hxy')
      dsimp [gamma] at he
      linarith
    · exact hxy'
    · have hm := mul_pos hd (sub_pos.mpr hyx')
      dsimp [gamma] at he
      linarith
  · apply Prod.ext
    · simp [gamma]
    · simpa [gamma] using hpu.symm
  · apply Prod.ext
    · simp [gamma]
    · simpa [gamma] using hpv.symm
  · intro t ht w
    exact havert t ht w
  · intro a b hab hadj t ht s hs heq
    have hts : t = 0 ∨ t = 1 := by
      by_contra hnot
      have ht0 : 0 < t := by
        rcases ne_or_eq t 0 with h | h
        · exact lt_of_le_of_ne ht.1 (Ne.symm h)
        · exact False.elim (hnot (Or.inl h))
      have ht1 : t < 1 := by
        rcases ne_or_eq t 1 with h | h
        · exact lt_of_le_of_ne ht.2 h
        · exact False.elim (hnot (Or.inr h))
      have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht0, ht1⟩
      rcases eq_or_ne s 0 with hs0 | hs0
      · have hend := hdraw.2.1 a b hab hadj
        have hstart : arc a b 0 = p a := hend.2.2.1
        have he' : gamma t = p a := by simpa [hs0, hstart] using heq
        exact (havert t ht' a) he'
      · rcases eq_or_ne s 1 with hs1 | hs1
        · have hend := hdraw.2.1 a b hab hadj
          have hfinish : arc a b 1 = p b := hend.2.2.2.1
          have he' : gamma t = p b := by simpa [hs1, hfinish] using heq
          exact (havert t ht' b) he'
        · have hs0' : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
          have hs1' : s < 1 := lt_of_le_of_ne hs.2 hs1
          have hpos := harcs a b hab hadj s ⟨hs0', hs1'⟩
          have hy := congrArg Prod.snd heq
          dsimp [gamma] at hy
          linarith
    have hsends : s = 0 ∨ s = 1 := by
      by_contra hnot
      have hs0 : 0 < s := by
        rcases ne_or_eq s 0 with h | h
        · exact lt_of_le_of_ne hs.1 (Ne.symm h)
        · exact False.elim (hnot (Or.inl h))
      have hs1 : s < 1 := by
        rcases ne_or_eq s 1 with h | h
        · exact lt_of_le_of_ne hs.2 h
        · exact False.elim (hnot (Or.inr h))
      have hpos := harcs a b hab hadj s ⟨hs0, hs1⟩
      have hy := congrArg Prod.snd heq
      dsimp [gamma] at hy
      linarith
    exact ⟨hts, hsends⟩