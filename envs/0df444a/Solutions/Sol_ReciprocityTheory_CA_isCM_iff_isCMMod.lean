-- Prove2me | solution 1 for ReciprocityTheory.CA.isCM_iff_isCMMod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:12.116202+00:00
-- url     : https://prove2.me/submissions/b68d8cdc-f251-46ed-854c-0fab43829775

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge

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
theorem _root_.solution : IsCM R ↔ IsCMMod R R := by
  have hd : Module.supportDim R R = ringKrullDim R := Module.supportDim_self_eq_ringKrullDim R
  constructor
  · rintro ⟨h1, n, hn, h2⟩
    exact ⟨h1, Module.Finite.self R, n, hd.trans hn, h2⟩
  · rintro ⟨h1, -, n, hn, h2⟩
    exact ⟨h1, n, hd.symm.trans hn, h2⟩
end ReciprocityTheory.CA
