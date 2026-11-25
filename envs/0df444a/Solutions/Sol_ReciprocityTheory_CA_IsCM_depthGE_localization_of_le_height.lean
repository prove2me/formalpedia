-- Prove2me | solution 1 for ReciprocityTheory.CA.IsCM.depthGE_localization_of_le_height
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:45:47.229027+00:00
-- url     : https://prove2.me/submissions/81e9578d-b03c-4807-a708-8816ab0e2bb8

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularOfLeHeight
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
import Theorems.Thm_ReciprocityTheory_CA_depthGE_localization_of_isWeaklyRegular
import Theorems.Thm_ReciprocityTheory_CA_IsCM_exists_isRegular_of_le_height


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence
variable {R : Type*} [CommRing R] [IsLocalRing R]
namespace ReciprocityTheory.CA
namespace IsCM
theorem _root_.solution (h : IsCM R) (P : Ideal R) [P.IsPrime] {r : ℕ}
    (hr : (r : ℕ∞) ≤ P.height) : DepthGE (Localization.AtPrime P) r := by
  obtain ⟨rs, hlen, hmem, hreg⟩ := h.exists_isRegular_of_le_height (Ideal.IsPrime.ne_top ‹_›) hr
  subst hlen
  exact depthGE_localization_of_isWeaklyRegular P hmem hreg.1
end IsCM
end ReciprocityTheory.CA
