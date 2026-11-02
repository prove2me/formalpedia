-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_extension_exists__p2m_bf2a6b94_c712_4371_81b2_f7600a9fcb4a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:43:36.067076+00:00
-- url     : https://prove2.me/submissions/10ee0702-a1c5-4bb0-a8f9-33084797a83a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) := by
  classical
  let encode : SimpleGraph V → V → V → Bool := fun G u v => decide (G.Adj u v)
  have hencode : Function.Injective encode := by
    intro G₁ G₂ h
    apply SimpleGraph.adj_injective
    funext u v
    apply propext
    have huv := congrFun (congrFun h u) v
    have huv' := congrArg (fun b : Bool => b = true) huv
    simpa [encode] using huv'
  letI : Finite (SimpleGraph V) := Finite.of_injective encode hencode
  let S : Set (SimpleGraph V) :=
    {K | H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨H, le_rfl, hH⟩
  obtain ⟨K, hK, hKmax⟩ := hSfinite.exists_maximal hSnonempty
  refine ⟨K, hK.1, hK.2, ?_⟩
  intro L hKL hL
  have hLinS : L ∈ S := ⟨hK.1.trans hKL, hL⟩
  have hLK : L ≤ K := hKmax hLinS hKL
  exact le_antisymm hLK hKL
