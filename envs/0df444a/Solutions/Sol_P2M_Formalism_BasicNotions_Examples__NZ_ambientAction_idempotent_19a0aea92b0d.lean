-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_ambientAction_idempotent_19a0aea92b0d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:09:06.436797+00:00
-- url     : https://prove2.me/submissions/afbb5158-0cc6-4582-a94b-b2560007f408

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_NonsquarefreeMonicBoundHolds
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeD
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeE

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
theorem _root_.solution {A : NAut N} (X : NTypes A) (μ) : X.onAmb μ X.e0 = X.cenAmb μ ⟨X.e0, idempotent_mem_center X⟩ := by
  unfold Formalism.BasicNotions.NTypes.onAmb
  rw [dif_pos (idempotent_mem_center X)]
end Formalism.BasicNotions.Examples₂.NZ
