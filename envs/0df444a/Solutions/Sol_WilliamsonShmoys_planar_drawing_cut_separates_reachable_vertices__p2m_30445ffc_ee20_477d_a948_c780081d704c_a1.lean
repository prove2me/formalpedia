-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_cut_separates_reachable_vertices__p2m_30445ffc_ee20_477d_a948_c780081d704c_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:01:53.197405+00:00
-- url     : https://prove2.me/submissions/41e4c0ce-80f6-44b6-9981-e37328afdec4

-- ID: bc9d21a3-e9b7-4fa6-a15f-8ee7eb19a650 | NAME: WilliamsonShmoys.planar_drawing_cut_separates_reachable_vertices__p2m_30445ffc_ee20_477d_a948_c780081d704c_a1 | 未本地编译验证
import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (A B : Set V)
    (hdisjoint : Disjoint A B) (hcover : A ∪ B = Set.univ)
    (hcut : ∀ u, u ∈ A → ∀ v, v ∈ B → ¬ K.Adj u v)
    (u v : V) (hu : u ∈ A) (hv : v ∈ B) :
    ¬ K.Reachable u v := by
  classical
  intro hr
  have hr' : Relation.ReflTransGen K.Adj u v := by
    simpa only [SimpleGraph.reachable_eq_reflTransGen] using hr
  have hA : u ∈ A → v ∈ A :=
    Relation.ReflTransGen.head_induction_on
      (motive := fun a _ => a ∈ A → v ∈ A) hr'
      (by intro hvA; exact hvA)
      (by
        intro a c hac hcv ih ha
        have hcAB : c ∈ A ∪ B := by rw [hcover]; simp
        rcases hcAB with hcA | hcB
        · exact ih hcA
        · exact False.elim ((hcut a ha c hcB) hac))
  exact (Set.disjoint_left.mp hdisjoint) (hA hu) hv
