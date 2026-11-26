-- Prove2me | solution 1 for TunnellMap.oddEquivOfBalance_apply_residual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:25:04.234413+00:00
-- url     : https://prove2.me/submissions/5f12404a-b66e-49e0-80cd-33a82e349e23

import Definitions.Def_TunnellMap_ComputableDirect
import Definitions.Def_TunnellMap_ComputablePipeline
import Definitions.Def_TunnellMap_FullAssembly
import Definitions.Def_TunnellMap_ComputableFullMap
import Theorems.Thm_TunnellMap_residual_orbit_card_eq


set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
variable [Fintype (BOddRep n)] [Fintype (ARep n)]
namespace TunnellMap
theorem _root_.solution (hn : Odd n) (hnpos : 0 < n)
    (hbal : Fintype.card (BOddRep n) = Fintype.card (ARep n))
    (q : BOddRep n) (hd : ¬ DirectSourceUsed q) :
    oddEquivOfBalance hn hnpos hbal q =
      (residualEquivOfOrbitCard hnpos (residual_orbit_card_eq hn hnpos hbal)
        ⟨q, hd⟩).1 := by
  classical
  show (Equiv.sumCompl DirectTargetUsed)
    (Equiv.sumCongr (directSubsetEquiv hn)
      (residualEquivOfOrbitCard hnpos (residual_orbit_card_eq hn hnpos hbal))
      ((Equiv.sumCompl DirectSourceUsed).symm q)) = _
  rw [Equiv.sumCompl_symm_apply_of_neg hd]
  rfl
end TunnellMap
