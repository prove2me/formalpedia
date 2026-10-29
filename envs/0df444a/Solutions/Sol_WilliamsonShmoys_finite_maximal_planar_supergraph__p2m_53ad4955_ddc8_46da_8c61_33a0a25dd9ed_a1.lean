-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_planar_supergraph__p2m_53ad4955_ddc8_46da_8c61_33a0a25dd9ed_a1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:48:59.348248+00:00
-- url     : https://prove2.me/submissions/2ef55c68-819b-4efb-bf31-85a988815b66

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ S : SimpleGraph V,
      (∀ u v, R.Adj u v → S.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn S ∧
      ∀ T : SimpleGraph V,
        (∀ u v, S.Adj u v → T.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn T →
        ∀ u v, T.Adj u v → S.Adj u v := by
  obtain ⟨S, hRS, hSm⟩ := Finite.exists_le_maximal (p := WilliamsonShmoys.HasPlanarDrawingOn) hR
  refine ⟨S, fun u v h => hRS h, hSm.prop, ?_⟩
  intro T hST hT u v huv
  have hle : S ≤ T := fun x y h => hST x y h
  exact hSm.2 hT hle huv
