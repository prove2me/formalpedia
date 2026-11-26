-- Prove2me | solution 1 for TunnellMap.FreeInvolution.exists_unique_sign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:12:56.464808+00:00
-- url     : https://prove2.me/submissions/d1d70555-62b1-4eb2-91b5-009d98a6aa2f

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
import Theorems.Thm_TunnellMap_FreeInvolution_signAct_inj_sign
import Theorems.Thm_TunnellMap_FreeInvolution_signOf_mem
import Theorems.Thm_TunnellMap_FreeInvolution_signAct_signOf_canonicalPoint

set_option autoImplicit true
open TunnellMap
open TunnellMap.FreeInvolution
variable {X : Type*} (I : FreeInvolution X)
variable {K : Type*} [LinearOrder K]
namespace TunnellMap.FreeInvolution
theorem _root_.solution (key : X → K) (hkey : Function.Injective key)
    (x : X) :
    ∃! σ : ℤ, (σ = 1 ∨ σ = -1) ∧
      I.signAct σ (I.canonicalRepresentative key hkey (I.orbit x)) = x := by
  refine ⟨I.signOf key x, ⟨I.signOf_mem key x, ?_⟩, ?_⟩
  · rw [canonicalRepresentative_orbit]
    exact I.signAct_signOf_canonicalPoint key x
  · rintro τ ⟨hτ, hτx⟩
    rw [canonicalRepresentative_orbit] at hτx
    refine I.signAct_inj_sign (x := I.canonicalPoint key x) hτ
      (I.signOf_mem key x) ?_
    rw [hτx, I.signAct_signOf_canonicalPoint key x]
end TunnellMap.FreeInvolution
