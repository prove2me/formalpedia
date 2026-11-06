-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_component_partition__p2m_8191f462_9581_40b2_8ed6_f73b850717b9_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:29:56.867368+00:00
-- url     : https://prove2.me/submissions/667fbc51-5f12-4862-b25a-16ddd96d63db

-- ID: 541f4d18-a1f1-4871-8c63-71c1d558c1ee | NAME: WilliamsonShmoys.finite_graph_component_partition__p2m_8191f462_9581_40b2_8ed6_f73b850717b9_a1 | 未本地编译验证
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open Finset

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) :
    ∃ C : V → Finset V,
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
      (Finset.univ.biUnion C = Finset.univ) ∧
      (∀ u v, L.Adj u v → ∃ i, u ∈ C i ∧ v ∈ C i) := by
  classical
  by_cases hV : (Finset.univ : Finset V).Nonempty
  · obtain ⟨a, _ha⟩ := hV
    let C : V → Finset V := fun i => if i = a then Finset.univ else ∅
    refine ⟨C, ?_, ?_, ?_⟩
    · intro i j hij
      by_cases hi : i = a
      · have hj : j ≠ a := by
          intro hja
          exact hij (hi.trans hja.symm)
        simp [C, hi, hj]
      · simp [C, hi]
    · ext x
      constructor
      · intro _
        exact Finset.mem_univ x
      · intro _
        exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, by simp [C]⟩
    · intro u v huv
      exact ⟨a, by simp [C], by simp [C]⟩
  · have huniv : (Finset.univ : Finset V) = ∅ := by
      ext x
      constructor
      · intro hx
        exfalso
        exact hV ⟨x, hx⟩
      · intro _
        exact Finset.mem_univ x
    refine ⟨fun _ : V => (∅ : Finset V), ?_, ?_, ?_⟩
    · intro i j hij
      simp
    · simp [huniv]
    · intro u v huv
      exfalso
      exact hV ⟨u, Finset.mem_univ u⟩
