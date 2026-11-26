-- Prove2me | solution 1 for TDLC.Refutation.pathGrade_embed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:24:33.858401+00:00
-- url     : https://prove2.me/submissions/d11810fa-9eb2-4d3d-8fed-478e9316910d

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Refutation

set_option autoImplicit true
open TDLC TDLC.Refutation
universe u v
variable {G : Type v} (g : GroupData G) (mark : Marker.{u})
namespace TDLC.Refutation
theorem _root_.solution {A : Type u} {x y : A} (s : Step x y) (val : A → G) :
    pathGrade g mark (Path.lEmbed s) val = grade g mark s val := g.mul_one _
end TDLC.Refutation
