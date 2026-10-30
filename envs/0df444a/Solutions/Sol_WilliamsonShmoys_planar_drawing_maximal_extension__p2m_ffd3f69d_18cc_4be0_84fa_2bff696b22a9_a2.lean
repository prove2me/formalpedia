-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_ffd3f69d_18cc_4be0_84fa_2bff696b22a9_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:07:22.493908+00:00
-- url     : https://prove2.me/submissions/64744250-b331-437e-b735-7e4902fe2fc3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_set_exists_maximal__p2m_0d714fcf_7da8_48c8_afc4_fedf819778b0_a2
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V, M ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H := by
  classical
  let S : Set (SimpleGraph V) := {H | M ≤ H ∧ HasPlanarDrawingOn H}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨M, le_rfl, hM⟩
  obtain ⟨H, hHmem, hHmax⟩ :=
    finite_set_exists_maximal__p2m_0d714fcf_7da8_48c8_afc4_fedf819778b0_a2
      S hSfinite hSnonempty
  refine ⟨H, hHmem.1, hHmem.2, ?_⟩
  intro K hHK hKplanar
  have hMK : M ≤ K := le_trans hHmem.1 hHK
  have hKmem : K ∈ S := ⟨hMK, hKplanar⟩
  have hKH : K ≤ H := hHmax K hKmem hHK
  exact le_antisymm hKH hHK