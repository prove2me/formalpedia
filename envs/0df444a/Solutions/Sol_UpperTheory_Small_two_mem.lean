-- Prove2me | solution 1 for UpperTheory.Small.two_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:15:02.363628+00:00
-- url     : https://prove2.me/submissions/694228d8-3bb5-43c6-8016-f8d5cbbdd60d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_SmallFacts
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open UpperTheory UpperTheory.Small
open Formalism.BasicNotions
variable {R : Ranks} (H : Host R)
namespace UpperTheory.Small
theorem _root_.solution : 2 ∈ H.small := by
  simp only [Formalism.HC.HostRaw.small, Nat.mem_primeFactors]
  refine ⟨Nat.prime_two, ?_, (H.QS_pos).ne'⟩
  have he : 2 ≤ R.e := H.two_le_e
  exact dvd_trans (dvd_pow_self 2 (by omega)) H.tower_dvd
end UpperTheory.Small
