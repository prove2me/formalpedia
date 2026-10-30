-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_extension_maximal__p2m_eacf956f_cefb_4210_bf9e_9cc0b6fb5cbc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:51:42.8187+00:00
-- url     : https://prove2.me/submissions/1cd975b1-e3b7-4c4a-ae1f-a1ec0a540e81

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_partial_order_maximal_above__p2m_c73a1eef_abb4_46aa_80da_3fb553ccc4a8_a1
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (P : SimpleGraph V → Prop) (μ : SimpleGraph V → Nat)
    (hK : P K)
    (hmono : ∀ G J : SimpleGraph V, G ≤ J → μ G ≤ μ J) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ P H ∧
      (∀ J : SimpleGraph V, H ≤ J → P J → J = H) ∧
      μ K ≤ μ H := by
  classical
  obtain ⟨H, hKH, hPH, hmax⟩ :=
    WilliamsonShmoys.finite_partial_order_maximal_above__p2m_c73a1eef_abb4_46aa_80da_3fb553ccc4a8_a1
      (Q := fun G : SimpleGraph V => K ≤ G ∧ P G) K ⟨le_rfl, hK⟩
  refine ⟨H, hKH, hPH.2, ?_, ?_⟩
  · intro J hHJ hPJ
    exact hmax J hHJ ⟨hKH.trans hHJ, hPJ⟩
  · exact hmono K H hKH