-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_planar_strict_extension__p2m_24141c0a_e101_43b3_b89f_9504b9363753_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:52:52.410867+00:00
-- url     : https://prove2.me/submissions/af0adaeb-65c2-41ad-86fd-a87e6b987de2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_vertices_separated_by_unreachability__p2m_282a2a61_c7fa_4a1e_ac79_616c5409586a_a1
import Theorems.Thm_WilliamsonShmoys_planar_strict_extension_of_separated_vertices__p2m_282a2a61_c7fa_4a1e_ac79_616c5409586a_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn G)
    (hV : 0 < Fintype.card V)
    (hdisconnected : Not G.Connected) :
    Exists (fun K : SimpleGraph V =>
      And (LE.le G K) (And (Not (K = G)) (HasPlanarDrawingOn K))) := by
  have hne : Nonempty V := Fintype.card_pos_iff.mp hV
  have hpairs :=
    WilliamsonShmoys.disconnected_vertices_separated_by_unreachability__p2m_282a2a61_c7fa_4a1e_ac79_616c5409586a_a1
      G hne hdisconnected
  cases hpairs with
  | intro u hrest =>
    cases hrest with
    | intro v hnotReachable =>
      have hext :=
        WilliamsonShmoys.planar_strict_extension_of_separated_vertices__p2m_282a2a61_c7fa_4a1e_ac79_616c5409586a_a1
          G hplanar u v hnotReachable
      cases hext with
      | intro K hrest =>
        cases hrest with
        | intro hsub hrest =>
          cases hrest with
          | intro hstrict hadjPlanar =>
            cases hadjPlanar with
            | intro hadj hKplanar =>
              exact Exists.intro K (And.intro hsub (And.intro hstrict hKplanar))