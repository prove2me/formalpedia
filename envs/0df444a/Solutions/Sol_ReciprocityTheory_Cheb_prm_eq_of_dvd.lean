-- Prove2me | solution 1 for ReciprocityTheory.Cheb.prm_eq_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:45:53.546799+00:00
-- url     : https://prove2.me/submissions/27ded3aa-f32b-4adf-a866-c479cbf0df36

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerFac

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution {E : Type} [Field E] [NumberField E] {p q : Prm E}
    (h : p.asIdeal ∣ q.asIdeal) : p = q :=
  IsDedekindDomain.HeightOneSpectrum.ext ((prime_dvd_prime_iff_eq p.prime q.prime).1 h)
end ReciprocityTheory.Cheb
