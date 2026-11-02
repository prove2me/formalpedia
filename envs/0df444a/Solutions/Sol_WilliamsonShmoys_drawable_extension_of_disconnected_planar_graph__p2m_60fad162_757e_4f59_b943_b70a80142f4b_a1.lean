-- Prove2me | solution 1 for WilliamsonShmoys.drawable_extension_of_disconnected_planar_graph__p2m_60fad162_757e_4f59_b943_b70a80142f4b_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:37:02.683968+00:00
-- url     : https://prove2.me/submissions/2b43156c-3adc-421b-a566-00031a1a360a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
        (hdisc : ¬ M.Connected),
        ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧ N ≠ M) := by
  intro h
  let M : SimpleGraph Empty := ⊥
  let p : Empty → ℝ × ℝ := fun x => nomatch x
  let arc : Empty → Empty → ℝ → ℝ × ℝ := fun x => nomatch x
  have hM : HasPlanarDrawingOn M := by
    refine ⟨p, arc, ?_, ?_, ?_⟩
    · intro x
      cases x
    · intro u v huv hadj
      cases u
    · intro u v x y huv hxy huvAdj hxyAdj hne t ht s hs hEq
      cases u
  have hdisc : ¬ M.Connected := by
    intro hc
    exact hc.nonempty.elim (fun x => nomatch x)
  obtain ⟨N, hMN, hN, hneq⟩ := h M hM hdisc
  have hEq : N = M := by
    ext u v
    cases u
  exact hneq hEq
