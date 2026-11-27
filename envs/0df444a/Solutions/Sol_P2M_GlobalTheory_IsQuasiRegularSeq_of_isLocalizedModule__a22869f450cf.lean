-- Prove2me | solution 1 for P2M_GlobalTheory_IsQuasiRegularSeq_of_isLocalizedModule__a22869f450cf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:52:03.10036+00:00
-- url     : https://prove2.me/submissions/1e8b7ed6-5ac4-4b38-8e61-4631b66119dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_of_linearEquiv
import Theorems.Thm_GlobalTheory_isQuasiRegularSeq_algebraMap_iff
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_of_isLocalizedModule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (S : Type*) [CommRing S] [Algebra R S]
variable {N : Type*} [AddCommGroup N] [Module R N]
namespace GlobalTheory
namespace IsQuasiRegularSeq
theorem _root_.solution (T : Submonoid R) (g : M →ₗ[R] N)
    [IsLocalizedModule T g] {f : ι → R} (h : IsQuasiRegularSeq M f) : IsQuasiRegularSeq N f :=
  ((isQuasiRegularSeq_algebraMap_iff (Localization T) f).mp
    (h.of_isLocalizedModule (Localization T) T (LocalizedModule.mkLinearMap T M))).of_linearEquiv
    (IsLocalizedModule.iso T g)
end IsQuasiRegularSeq
end GlobalTheory
