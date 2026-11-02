-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_86ac92fe_a077_498c_8a86_bf0c24de864c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:40:49.44738+00:00
-- url     : https://prove2.me/submissions/978b49e9-b453-4247-8495-fb16dff6b4eb

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_of_le__p2m_138d462c_20bd_43cc_9c59_565c454fd505_a1
import Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_of_downward_closed__p2m_138d462c_20bd_43cc_9c59_565c454fd505_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ Q : SimpleGraph V,
      G ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧
        ∀ R : SimpleGraph V,
          Q ≤ R → WilliamsonShmoys.HasPlanarDrawingOn R → R ≤ Q := by
  exact WilliamsonShmoys.exists_maximal_extension_of_downward_closed__p2m_138d462c_20bd_43cc_9c59_565c454fd505_a1
    WilliamsonShmoys.HasPlanarDrawingOn
    (fun hHK hK =>
      WilliamsonShmoys.planarDrawingOn_of_le__p2m_138d462c_20bd_43cc_9c59_565c454fd505_a1 hHK hK)
    G hG