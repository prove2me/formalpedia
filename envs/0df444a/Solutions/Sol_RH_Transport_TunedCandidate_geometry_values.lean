-- Prove2me | solution 1 for RH.Transport.TunedCandidate.geometry_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:16:32.703197+00:00
-- url     : https://prove2.me/submissions/0808571b-209f-4242-8d51-22602728b825

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution :
    ell = 625643953 / 3750000000 ∧
    lx = 2661585647 / 7500000000 ∧
    ly = 3587126447 / 7500000000 ∧
    h = 2029900753 / 2500000000 := by
  norm_num [ell, Geometry.ell, lx, ly, h, lxAt, lyAt, hAt, p, b]
end RH.Transport.TunedCandidate
