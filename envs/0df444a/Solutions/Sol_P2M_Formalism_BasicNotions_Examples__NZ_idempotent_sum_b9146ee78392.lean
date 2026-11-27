-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_idempotent_sum_b9146ee78392
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:51:20.544083+00:00
-- url     : https://prove2.me/submissions/e8928a7e-da73-490c-bfe3-1688355df4c3

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_NonsquarefreeMonicBoundHolds
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeD
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeE
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_seriesIdempotent_idem_ee159254e771

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open Polynomial Formalism.CyclotomicNorms NumberField IsDedekindDomain
variable {R : Ranks} {H : Host R}
attribute [local instance] neZero_g fact_g Classical.propDecidable
variable {what₂ : Rows.Data R} (N : NData R H what₂)
variable {K : Type} [Field K]
variable (es : ∀ k, (ZMod (H.g k))[X] → MonoidAlgebra K (GL (Fin R.r) (ZMod (H.g k))))
  (hidem : ∀ k f, es k f * es k f = es k f) (hcen : ∀ k f a, es k f * a = a * es k f)
  (horth : ∀ k f f', f ≠ f' → es k f * es k f' = 0)
variable {N}
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution {A : NAut N} (X : NTypes A) : X.e0 * X.e0 = X.e0 := by
  rw [e0_eq X]
  exact seriesIdempotent_idem N X.eSer X.eSer_idem X.eSer_orth
end Formalism.BasicNotions.Examples₂.NZ
