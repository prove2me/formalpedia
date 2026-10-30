-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_induce__p2m_4414481d_333a_4f96_8a2d_2d6fda1fe3c0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:56:31.545984+00:00
-- url     : https://prove2.me/submissions/12522b9d-fafe-4639-826b-c7922255c8e6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (S : Finset V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    WilliamsonShmoys.HasPlanarDrawingOn (L.induce (S : Set V)) := by
  classical
  cases hDraw with
  | intro p hprops =>
    cases hprops with
    | intro arc hprops =>
      cases hprops with
      | intro hp_inj hprops =>
        cases hprops with
        | intro hp_edge hp_cross =>
          refine Exists.intro (fun x => p x.1)
            (Exists.intro (fun x y t => arc x.1 y.1 t) ?_)
          refine And.intro ?_ (And.intro ?_ ?_)
          · intro x y hxy
            apply Subtype.ext
            exact hp_inj hxy
          · intro x y hxy hadj
            change L.Adj x.1 y.1 at hadj
            have hval : x.1 < y.1 := hxy
            cases hp_edge x.1 y.1 hval hadj with
            | intro hcont hprops =>
              cases hprops with
              | intro hinj hprops =>
                cases hprops with
                | intro hzero hprops =>
                  cases hprops with
                  | intro hone hno_vertex =>
                    exact And.intro hcont (And.intro hinj
                      (And.intro hzero (And.intro hone
                        (fun t ht w => hno_vertex t ht w.1))))
          · intro x y z w hxy hzw hadjxy hadjzw hne
            change L.Adj x.1 y.1 at hadjxy
            change L.Adj z.1 w.1 at hadjzw
            have hxy' : x.1 < y.1 := hxy
            have hzw' : z.1 < w.1 := hzw
            have hne' : Not ((x.1, y.1) = (z.1, w.1)) := by
              intro heq
              apply hne
              apply Prod.ext
              · apply Subtype.ext
                exact congrArg Prod.fst heq
              · apply Subtype.ext
                exact congrArg Prod.snd heq
            exact hp_cross x.1 y.1 z.1 w.1 hxy' hzw' hadjxy hadjzw hne'
