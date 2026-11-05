-- Prove2me | solution 1 for WilliamsonShmoys.bridge_extension_strict_edgeSet__p2m_1743449e_70b2_453d_82e4_df1f7d1e75bd_a3
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T18:39:14.240271+00:00
-- url     : https://prove2.me/submissions/182ecf2a-a369-4393-9df5-9e64582bca02

import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [DecidableEq V] {K L : SimpleGraph V}
    (hsub : K.edgeSet ⊆ L.edgeSet)
    {u v : V} (hnot : ¬ K.Reachable u v) (hadj : L.Adj u v) :
    K.edgeSet ⊂ L.edgeSet := by
  classical
  have hKuv : ¬ K.Adj u v := fun h => hnot h.reachable
  have heL : Sym2.mk u v ∈ L.edgeSet := by simpa using hadj
  have heK : Sym2.mk u v ∉ K.edgeSet := by simpa using hKuv
  exact (Set.ssubset_iff_of_subset hsub).2 ⟨Sym2.mk u v, heL, heK⟩
