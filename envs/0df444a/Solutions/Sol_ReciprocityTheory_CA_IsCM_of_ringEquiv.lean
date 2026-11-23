-- Prove2me | solution 1 for ReciprocityTheory.CA.IsCM.of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:48:48.462965+00:00
-- url     : https://prove2.me/submissions/036f5b63-e592-490d-8986-55c96554363c

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge
import Theorems.Thm_ReciprocityTheory_CA_DepthGE_of_ringEquiv

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
theorem _root_.solution {S : Type*} [CommRing S] [IsLocalRing S] (e : R ≃+* S)
    (h : IsCM R) : IsCM S := by
  obtain ⟨hN, n, hn, hd⟩ := h
  exact ⟨isNoetherianRing_of_ringEquiv R e, n, (ringKrullDim_eq_of_ringEquiv e).symm.trans hn,
    hd.of_ringEquiv e⟩
end IsCM
end ReciprocityTheory.CA
