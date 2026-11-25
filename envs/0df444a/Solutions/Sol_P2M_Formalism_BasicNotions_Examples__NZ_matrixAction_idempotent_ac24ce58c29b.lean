-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_matrixAction_idempotent_ac24ce58c29b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:09:08.402049+00:00
-- url     : https://prove2.me/submissions/2556bdfc-24d6-41ad-b1fd-158a0bd3d6d7

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
theorem _root_.solution {A : NAut N} (X : NTypes A) (μ j) : X.onMt μ j X.e0 = X.cenMt μ j ⟨X.e0, idempotent_mem_center X⟩ := by
  unfold Formalism.BasicNotions.NTypes.onMt
  rw [dif_pos (idempotent_mem_center X)]
end Formalism.BasicNotions.Examples₂.NZ
