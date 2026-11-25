-- Prove2me | solution 1 for ReciprocityTheory.CA.isCM_quotient_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:24:56.681151+00:00
-- url     : https://prove2.me/submissions/05a87f99-cf75-4078-9fc4-51a518beb6e6

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge
import Theorems.Thm_ReciprocityTheory_CA_depthGE_quotient_iff

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
theorem _root_.solution [IsNoetherianRing R] (I : Ideal R) [IsLocalRing (R ⧸ I)] :
    IsCM (R ⧸ I) ↔ IsCMMod R (R ⧸ I) := by
  have hfin : Module.Finite R (R ⧸ I) :=
    Module.Finite.of_surjective (Submodule.mkQ I) (Submodule.mkQ_surjective I)
  have hd : Module.supportDim R (R ⧸ I) = ringKrullDim (R ⧸ I) := by
    rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator, Ideal.annihilator_quotient]
  constructor
  · rintro ⟨-, n, hn, h⟩
    exact ⟨inferInstance, hfin, n, hd.trans hn, (depthGE_quotient_iff I n).mp h⟩
  · rintro ⟨-, -, n, hn, h⟩
    exact ⟨inferInstance, n, hd.symm.trans hn, (depthGE_quotient_iff I n).mpr h⟩
end ReciprocityTheory.CA
