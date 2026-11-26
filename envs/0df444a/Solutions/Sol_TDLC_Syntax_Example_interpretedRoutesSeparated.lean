-- Prove2me | solution 1 for TDLC.Syntax.Example.interpretedRoutesSeparated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:28:17.819931+00:00
-- url     : https://prove2.me/submissions/a0add7d0-5c50-444b-ae2e-1e000171aaae

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Syntax
import Theorems.Thm_TDLC_Syntax_noCell_of_parity_ne

set_option autoImplicit true
open TDLC TDLC.Syntax
open TDLC.Syntax.Example
namespace TDLC.Syntax.Example
theorem _root_.solution (ρ : Env U Γ) :
    ¬ Nonempty (TDLC.Path2 (TDLC.Path.lEmbed (interpret betaRoute ρ))
      (TDLC.Path.lEmbed (interpret etaRoute ρ))) :=
  noCell_of_parity_ne betaRoute etaRoute (by decide) ρ
end TDLC.Syntax.Example
