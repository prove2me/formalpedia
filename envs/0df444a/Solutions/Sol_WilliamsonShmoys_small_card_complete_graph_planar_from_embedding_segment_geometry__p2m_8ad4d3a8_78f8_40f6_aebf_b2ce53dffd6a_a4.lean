-- Prove2me | solution 1 for WilliamsonShmoys.small_card_complete_graph_planar_from_embedding_segment_geometry__p2m_8ad4d3a8_78f8_40f6_aebf_b2ce53dffd6a_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:51:38.538205+00:00
-- url     : https://prove2.me/submissions/2192ac14-f9b5-412c-8143-dc524b615d4b

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (p : V -> Prod Real Real) (hp : Function.Injective p) (u v : V)
    (huv : u < v) (hvertices : forall w : V, Or (w = u) (w = v)) :
    And (ContinuousOn (fun t : Real => (1 - t) • p u + t • p v) (Set.Icc 0 1))
      (And (Set.InjOn (fun t : Real => (1 - t) • p u + t • p v) (Set.Icc 0 1))
        (And ((fun t : Real => (1 - t) • p u + t • p v) 0 = p u)
          (And ((fun t : Real => (1 - t) • p u + t • p v) 1 = p v)
            (forall t : Real, Set.Ioo (0 : Real) 1 t -> forall w : V,
              Not ((fun t : Real => (1 - t) • p u + t • p v) t = p w))))) := by
  let f : Real → Prod Real Real := fun t => (1 - t) • p u + t • p v
  have hcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hne : p u ≠ p v := by
    intro h
    exact (ne_of_lt huv) (hp h)
  have hinj : Set.InjOn f (Set.Icc (0 : Real) 1) := by
    intro x hx y hy hxy
    have hcoord : (p u).1 ≠ (p v).1 ∨ (p u).2 ≠ (p v).2 := by
      by_contra h
      push_neg at h
      exact hne (Prod.ext h.1 h.2)
    rcases hcoord with hfst | hsnd
    · have hc : (1 - x) * (p u).1 + x * (p v).1 =
          (1 - y) * (p u).1 + y * (p v).1 := by
        simpa [f] using congrArg Prod.fst hxy
      have hlin : x * ((p v).1 - (p u).1) = y * ((p v).1 - (p u).1) := by
        calc
          x * ((p v).1 - (p u).1) = ((1 - x) * (p u).1 + x * (p v).1) - (p u).1 := by ring
          _ = ((1 - y) * (p u).1 + y * (p v).1) - (p u).1 := by rw [hc]
          _ = y * ((p v).1 - (p u).1) := by ring
      exact mul_right_cancel₀ (sub_ne_zero.mpr (Ne.symm hfst)) hlin
    · have hc : (1 - x) * (p u).2 + x * (p v).2 =
          (1 - y) * (p u).2 + y * (p v).2 := by
        simpa [f] using congrArg Prod.snd hxy
      have hlin : x * ((p v).2 - (p u).2) = y * ((p v).2 - (p u).2) := by
        calc
          x * ((p v).2 - (p u).2) = ((1 - x) * (p u).2 + x * (p v).2) - (p u).2 := by ring
          _ = ((1 - y) * (p u).2 + y * (p v).2) - (p u).2 := by rw [hc]
          _ = y * ((p v).2 - (p u).2) := by ring
      exact mul_right_cancel₀ (sub_ne_zero.mpr (Ne.symm hsnd)) hlin
  have hzero : f 0 = p u := by simp [f]
  have hone : f 1 = p v := by simp [f]
  refine ⟨hcont.continuousOn, hinj, hzero, hone, ?_⟩
  intro t ht w
  rcases hvertices w with hwu | hwv
  · subst w
    intro h
    have hxt : t ∈ Set.Icc (0 : Real) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hmem : (0 : Real) ∈ Set.Icc (0 : Real) 1 := by norm_num
    have heq : f t = f 0 := by simpa [f] using h.trans hzero.symm
    have hval := hinj hxt hmem heq
    exact (ne_of_gt ht.1) hval
  · subst w
    intro h
    have hxt : t ∈ Set.Icc (0 : Real) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hmem : (1 : Real) ∈ Set.Icc (0 : Real) 1 := by norm_num
    have heq : f t = f 1 := by simpa [f] using h.trans hone.symm
    have hval := hinj hxt hmem heq
    exact (ne_of_lt ht.2) hval