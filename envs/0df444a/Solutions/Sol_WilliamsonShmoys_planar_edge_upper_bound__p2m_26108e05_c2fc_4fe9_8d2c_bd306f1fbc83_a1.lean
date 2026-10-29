-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_26108e05_c2fc_4fe9_8d2c_bd306f1fbc83_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-28T21:23:38.527344+00:00
-- url     : https://prove2.me/submissions/ed182cb7-44a6-4439-b9bf-8ed4b7bc1092

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (K : SimpleGraph V)
        (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
        (hCard : 3 ≤ Fintype.card V),
        3 * Fintype.card V ≤ K.edgeSet.ncard + 6) := by
  intro h
  let K : SimpleGraph (Fin 3) := ⊥
  let p : Fin 3 → ℝ × ℝ := fun i => (i.val, 0)
  let arc : Fin 3 → Fin 3 → ℝ → ℝ × ℝ := fun _ _ _ => (0, 0)
  have hp : Function.Injective p := by
    intro i j hij
    apply Fin.ext
    have hval : (i.val : ℝ) = j.val := congrArg Prod.fst hij
    exact_mod_cast hval
  have hDraw : WilliamsonShmoys.HasPlanarDrawingOn K := by
    refine ⟨p, arc, hp, ?_, ?_⟩
    · intro u v huv hadj
      simp [K] at hadj
    · intro u v x y huv hxy hadj₁ hadj₂ hne t ht s hs heq
      simp [K] at hadj₁
  have hCard : 3 ≤ Fintype.card (Fin 3) := by norm_num
  have hh := h K hDraw hCard
  norm_num [K] at hh