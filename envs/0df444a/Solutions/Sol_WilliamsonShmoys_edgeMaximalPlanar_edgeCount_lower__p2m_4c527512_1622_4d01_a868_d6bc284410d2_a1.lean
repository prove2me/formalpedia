-- Prove2me | solution 1 for WilliamsonShmoys.edgeMaximalPlanar_edgeCount_lower__p2m_4c527512_1622_4d01_a868_d6bc284410d2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:58:15.7802+00:00
-- url     : https://prove2.me/submissions/24e795b4-0a27-40ee-ab23-bf56359d604c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_edgeMaximalPlanar_triangulatedExtension__p2m_07c9f31b_494b_4180_969f_c152b9627c5e_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → HasPlanarDrawingOn H → H = K)
    (hconn : K.Connected)
    (hn : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ K.edgeFinset.card := by
  obtain ⟨H, hHdec, hKH, hHplanar, hcount⟩ :=
    WilliamsonShmoys.edgeMaximalPlanar_triangulatedExtension__p2m_07c9f31b_494b_4180_969f_c152b9627c5e_a1
      K hK hconn hn
  letI : DecidableRel H.Adj := hHdec
  have hHK : H = K := hmax H hKH hHplanar
  have hedge : H.edgeFinset = K.edgeFinset := by
    ext e
    simp [SimpleGraph.mem_edgeFinset, hHK]
  have hcountK : 3 * Fintype.card V - 6 = K.edgeFinset.card := by
    calc
      3 * Fintype.card V - 6 = H.edgeFinset.card := hcount
      _ = K.edgeFinset.card := congrArg Finset.card hedge
  exact le_of_eq hcountK