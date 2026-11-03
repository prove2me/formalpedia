-- Prove2me | solution 1 for WilliamsonShmoys.maximum_edge_planar_graph_connected__p2m_fb475999_bbbb_4d3f_8e03_a58caa743876_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-02T11:58:24.837791+00:00
-- url     : https://prove2.me/submissions/9780d26c-d883-42ed-b7ea-80ef4b3f5b77

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
      (Q : SimpleGraph V) (dQ : DecidableRel Q.Adj)
      (hcard : 2 ≤ Fintype.card V)
      (hQ : HasPlanarDrawingOn Q)
      (hmax : ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
        HasPlanarDrawingOn K →
        (letI : DecidableRel Q.Adj := dQ
         letI : DecidableRel K.Adj := dK
         Q.edgeFinset.card ≤ K.edgeFinset.card)),
      Q.Connected) := by
  classical
  intro h
  let Q : SimpleGraph (Fin 2) := ⊥
  let dQ : DecidableRel Q.Adj := fun a b => isFalse (by simp [Q])
  letI : DecidableRel Q.Adj := dQ
  have hcard : 2 ≤ Fintype.card (Fin 2) := by simp
  have hQ : HasPlanarDrawingOn Q := by
    let p : Fin 2 → ℝ × ℝ := fun v => ((v.val : ℝ), 0)
    let arc : Fin 2 → Fin 2 → ℝ → ℝ × ℝ := fun _ _ _ => (0, 0)
    refine ⟨p, arc, ?_⟩
    refine ⟨?_, ?_⟩
    · intro a b hab
      have hv : (a.val : ℝ) = (b.val : ℝ) := by
        simpa [p] using congrArg Prod.fst hab
      exact Fin.ext (by exact_mod_cast hv)
    · refine ⟨?_, ?_⟩
      · intro u v huv hadj
        simp [Q] at hadj
      · intro u v x y huv hxy hadj hadj' hne t ht s hs heq
        simp [Q] at hadj
  have hc : Q.Connected := h (V := Fin 2) Q dQ hcard hQ (by
    intro K dK hK
    letI : DecidableRel K.Adj := dK
    calc
      _ = 0 := by
        apply Finset.card_eq_zero.mpr
        apply (@SimpleGraph.edgeFinset_eq_empty (Fin 2) Q (Q.fintypeEdgeSet)).mpr
        rfl
      _ ≤ _ := Nat.zero_le _)
  have hnot : ¬ Q.Connected := by
    simpa [Q] using (SimpleGraph.not_connected_bot (V := Fin 2))
  exact hnot hc
