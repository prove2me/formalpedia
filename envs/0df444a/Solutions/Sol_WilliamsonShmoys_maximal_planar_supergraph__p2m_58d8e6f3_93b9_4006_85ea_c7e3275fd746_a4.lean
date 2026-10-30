-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph__p2m_58d8e6f3_93b9_4006_85ea_c7e3275fd746_a4
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T07:45:29.043613+00:00
-- url     : https://prove2.me/submissions/39b55603-c2f6-4d3b-9bd1-4290810f6999

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

open WilliamsonShmoys

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L),
    ∃ M : SimpleGraph V,
      L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ N : SimpleGraph V, L ≤ N →
        WilliamsonShmoys.HasPlanarDrawingOn N → N = M) ∧
      L.edgeSet.ncard ≤ M.edgeSet.ncard) := by
  intro h
  let p : Fin 3 → ℝ × ℝ := ![(0, 0), (1, 0), (0, 1)]
  have hp : Function.Injective p := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [p, Prod.ext_iff]
  let E : SimpleGraph (Fin 3) := SimpleGraph.edge 0 1
  have hE01 : E.Adj 0 1 := by simp [E, SimpleGraph.edge_adj]
  have hEuv : ∀ u v : Fin 3, u < v → E.Adj u v → u = 0 ∧ v = 1 := by
    intro u v huv hA
    simp only [E, SimpleGraph.edge_adj] at hA
    rcases hA with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, -⟩
    · exact ⟨rfl, rfl⟩
    · exact absurd huv (by decide)
  have hdE : WilliamsonShmoys.HasPlanarDrawingOn E := by
    refine ⟨p, fun _ _ t => (t, 0), hp, ?_, ?_⟩
    · intro u v huv hA
      obtain ⟨rfl, rfl⟩ := hEuv u v huv hA
      refine ⟨by fun_prop, fun a _ b _ hab => by simpa using hab, by simp [p], by simp [p], ?_⟩
      intro t ht w hw
      fin_cases w <;> simp_all [p, Prod.ext_iff] <;> linarith [ht.1, ht.2]
    · intro u v x y huv hxy hA hB hne
      obtain ⟨rfl, rfl⟩ := hEuv u v huv hA
      obtain ⟨rfl, rfl⟩ := hEuv x y hxy hB
      exact absurd rfl hne
  have hd : WilliamsonShmoys.HasPlanarDrawingOn (⊥ : SimpleGraph (Fin 3)) :=
    ⟨p, fun _ _ t => (t, 0), hp, fun u v _ hA => absurd hA (by simp),
      fun u v x y _ _ hA => absurd hA (by simp)⟩
  obtain ⟨M, -, -, hU, -⟩ := h (⊥ : SimpleGraph (Fin 3)) (by simp) hd
  have h1 := hU ⊥ le_rfl hd
  have h2 := hU E bot_le hdE
  have : E = ⊥ := h2.trans h1.symm
  rw [this] at hE01
  exact hE01
