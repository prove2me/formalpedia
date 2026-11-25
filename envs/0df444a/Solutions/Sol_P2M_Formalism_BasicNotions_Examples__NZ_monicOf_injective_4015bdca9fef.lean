-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_monicOf_injective_4015bdca9fef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:53:16.203236+00:00
-- url     : https://prove2.me/submissions/c32baac7-381a-4fb6-970a-9db9cae222b7

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_NonsquarefreeMonicBoundHolds
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeD
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeE
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
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open Polynomial Formalism.CyclotomicNorms NumberField IsDedekindDomain
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution {K : Type} [Field K] {N : ℕ} : Function.Injective (monicOf (K := K) (N := N)) := by
  intro a b h
  funext i
  have h2 := congrArg (fun p => Polynomial.coeff p i) h
  simpa [monicOf, Polynomial.coeff_X_pow, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Fin.val_inj,
    (Fin.is_lt i).ne] using h2
end Formalism.BasicNotions.Examples₂.NZ
