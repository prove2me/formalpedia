-- Prove2me | solution 1 for ThinFlowSP.Breakpoints.theorem_14
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T08:31:14.142888+00:00
-- url     : https://prove2.me/submissions/90b920be-46fc-40fa-bcf6-f1166b3b6db1

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Model

namespace ThinFlowSP.Breakpoints

theorem rhoArc_mono {G : Net} (Astar : Finset G.A) (ν : G.A → ℝ) (a : G.A) (hν : 0 < ν a)
    {lv lv' xa xa' : ℝ} (hl : lv ≤ lv') (hx : xa ≤ xa') :
    rhoArc Astar ν a lv xa ≤ rhoArc Astar ν a lv' xa' := by
  have h : xa / ν a ≤ xa' / ν a := div_le_div_of_nonneg_right hx hν.le
  unfold rhoArc
  split_ifs
  · exact h
  · exact max_le_max hl h

theorem rhoArc_strict {G : Net} (Astar : Finset G.A) (ν : G.A → ℝ) (a : G.A) (hν : 0 < ν a)
    {lv lv' xa xa' : ℝ} (hl : lv < lv') (hx : xa < xa') :
    rhoArc Astar ν a lv xa < rhoArc Astar ν a lv' xa' := by
  have h : xa / ν a < xa' / ν a := div_lt_div_of_pos_right hx hν
  unfold rhoArc
  split_ifs
  · exact h
  · exact max_lt (lt_max_of_lt_left hl) (lt_max_of_lt_right h)

theorem lower_of_labels {G : Net} {Astar : Finset G.A} {ν : G.A → ℝ} {x : G.A → ℝ}
    {l : G.V → ℝ} (hl : IsThinFlowLabels G Astar ν x l) (a : G.A) (hw : G.head a ≠ G.s) :
    l (G.head a) ≤ rhoArc Astar ν a (l (G.tail a)) (x a) :=
  (hl.2.1 _ hw).2 ⟨a, rfl, rfl⟩

/-- Net outflow summed over a vertex set, as a sum over arcs. -/
theorem sum_net (G : Net) (y : G.A → ℝ) (U : Finset G.V) :
    ∑ u ∈ U, (outflow G y u - inflow G y u) =
      ∑ a, ((if G.tail a ∈ U then y a else 0) - (if G.head a ∈ U then y a else 0)) := by
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  congr 1
  · unfold outflow
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_ite_eq]
  · unfold inflow
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_ite_eq]

theorem net_t (G : Net) (hst : G.s ≠ G.t) (y : G.A → ℝ) (val : ℝ) (hy : IsStaticFlow G y val) :
    outflow G y G.t - inflow G y G.t = -val := by
  have h := sum_net G y Finset.univ
  simp only [Finset.mem_univ, if_true, sub_self, Finset.sum_const_zero] at h
  rw [Fintype.sum_eq_add G.s G.t hst (fun v hv => hy.2.1 v hv.1 hv.2), hy.2.2] at h
  linarith

theorem thm14 (G : Net) (Astar : Finset G.A) (ν : G.A → ℝ)
    (hG : IsShortestPathGraph G) (hst : G.s ≠ G.t) (hν : ∀ a, 0 < ν a)
    (x xh : G.A → ℝ) (l lh : G.V → ℝ) (val valh : ℝ)
    (hx : IsStaticFlow G x val) (hxh : IsStaticFlow G xh valh)
    (hl : IsThinFlowLabels G Astar ν x l) (hlh : IsThinFlowLabels G Astar ν xh lh)
    (hval : val ≤ valh) (hs : l G.s ≤ lh G.s) :
    ∀ v, l v ≤ lh v := by
  by_contra hcon
  push Not at hcon
  set U : Finset G.V := Finset.univ.filter fun v => lh v < l v with hU
  have memU : ∀ v, v ∈ U ↔ lh v < l v := fun v => by simp [hU]
  have sU : G.s ∉ U := by rw [memU]; exact not_lt.mpr hs
  -- no arc enters `s`
  have head_ne_s : ∀ a, G.head a ≠ G.s := by
    intro a ha
    apply hG.1 G.s
    exact Relation.TransGen.tail' (hG.2 (G.tail a)) ⟨a, rfl, ha⟩
  -- arcs leaving `U`
  have hout : ∀ a, G.tail a ∈ U → G.head a ∉ U → x a ≤ xh a := by
    intro a ht hh
    by_contra hlt
    push Not at hlt
    rw [memU] at ht hh
    apply hh
    have hpos : 0 < x a := lt_of_le_of_lt (hxh.1 a) hlt
    rw [hl.2.2 a hpos]
    exact lt_of_le_of_lt (lower_of_labels hlh a (head_ne_s a))
      (rhoArc_strict Astar ν a (hν a) ht hlt)
  -- arcs entering `U`
  have hin : ∀ a, G.tail a ∉ U → G.head a ∈ U → xh a ≤ x a := by
    intro a ht hh
    by_contra hlt
    push Not at hlt
    rw [memU] at ht hh
    push Not at ht
    have hpos : 0 < xh a := lt_of_le_of_lt (hx.1 a) hlt
    have h1 := hlh.2.2 a hpos
    have h2 := lower_of_labels hl a (head_ne_s a)
    have h3 := rhoArc_mono Astar ν a (hν a) ht hlt.le
    linarith
  -- the cut sum is non-negative
  set g : G.A → ℝ := fun a =>
    (if G.tail a ∈ U then x a - xh a else 0) - (if G.head a ∈ U then x a - xh a else 0) with hg
  have hsum : 0 ≤ ∑ a, g a := by
    have e1 := sum_net G x U
    have e2 := sum_net G xh U
    have : ∑ u ∈ U, ((outflow G x u - inflow G x u) -
        (outflow G xh u - inflow G xh u)) = ∑ a, g a := by
      rw [Finset.sum_sub_distrib, e1, e2, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      simp only [hg]
      split_ifs <;> ring
    rw [← this]
    apply Finset.sum_nonneg
    intro u hu
    have hus : u ≠ G.s := fun e => sU (e ▸ hu)
    by_cases hut : u = G.t
    · subst hut
      rw [net_t G hst x val hx, net_t G hst xh valh hxh]
      linarith
    · rw [hx.2.1 u hus hut, hxh.2.1 u hus hut]; simp
  have hnp : ∀ a ∈ Finset.univ, g a ≤ 0 := by
    intro a _
    simp only [hg]
    by_cases ht : G.tail a ∈ U <;> by_cases hh : G.head a ∈ U
    · simp [ht, hh]
    · simp only [ht, hh, if_true, if_false]; linarith [hout a ht hh]
    · simp only [ht, hh, if_true, if_false]; linarith [hin a ht hh]
    · simp [ht, hh]
  have hzero : ∀ a, g a = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonpos hnp).mp (le_antisymm (Finset.sum_nonpos hnp) hsum)
    exact fun a => this a (Finset.mem_univ a)
  have hin_eq : ∀ a, G.tail a ∉ U → G.head a ∈ U → x a = xh a := by
    intro a ht hh
    have := hzero a
    simp only [hg, ht, hh, if_true, if_false] at this
    linarith
  -- a minimal vertex of `U`
  have : IsTrans G.V (Relation.TransGen (Adj G)) := ⟨fun _ _ _ => Relation.TransGen.trans⟩
  have : Std.Irrefl (Relation.TransGen (Adj G)) := ⟨hG.1⟩
  have wf := Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen (Adj G))
  have hne : (U : Set G.V).Nonempty := by
    obtain ⟨v, hv⟩ := hcon
    exact ⟨v, (memU v).mpr hv⟩
  obtain ⟨w, hwU, hmin⟩ := wf.has_min (U : Set G.V) hne
  have hwU' : w ∈ U := hwU
  have hws : w ≠ G.s := fun e => sU (e ▸ hwU')
  obtain ⟨⟨a0, ha0, hlhw⟩, -⟩ := hlh.2.1 w hws
  have hv0 : G.tail a0 ∉ U := by
    intro h
    exact hmin (G.tail a0) h (Relation.TransGen.single ⟨a0, rfl, ha0⟩)
  have hv0' : l (G.tail a0) ≤ lh (G.tail a0) := by
    rw [memU] at hv0; exact not_lt.mp hv0
  have hxa : x a0 = xh a0 := hin_eq a0 hv0 (ha0 ▸ hwU')
  have h1 : l w ≤ rhoArc Astar ν a0 (l (G.tail a0)) (x a0) := by
    have := lower_of_labels hl a0 (ha0 ▸ hws)
    rw [ha0] at this; exact this
  have h2 := rhoArc_mono Astar ν a0 (hν a0) hv0' hxa.le
  have h3 : l w ≤ lh w := by rw [hlhw]; exact h1.trans h2
  exact absurd ((memU w).mp hwU') (not_lt.mpr h3)

end ThinFlowSP.Breakpoints

open ThinFlowSP.Breakpoints in
theorem solution (G : Net) (Astar : Finset G.A) (ν : G.A → ℝ)
    (hG : IsShortestPathGraph G) (hst : G.s ≠ G.t) (hν : ∀ a, 0 < ν a)
    (x xh : G.A → ℝ) (l lh : G.V → ℝ) (val valh : ℝ)
    (hx : IsStaticFlow G x val) (hxh : IsStaticFlow G xh valh)
    (hl : IsThinFlowLabels G Astar ν x l) (hlh : IsThinFlowLabels G Astar ν xh lh)
    (hval : val ≤ valh) (hs : l G.s ≤ lh G.s) :
    ∀ v, l v ≤ lh v :=
  thm14 G Astar ν hG hst hν x xh l lh val valh hx hxh hl hlh hval hs
