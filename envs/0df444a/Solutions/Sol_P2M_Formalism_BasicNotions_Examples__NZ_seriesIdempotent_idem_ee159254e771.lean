-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_seriesIdempotent_idem_ee159254e771
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:28:37.250946+00:00
-- url     : https://prove2.me/submissions/68c35473-449b-47fc-9cca-58f53db2f1dd

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_NonsquarefreeMonicBoundHolds
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeD
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeE
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_monicOf_injective_4015bdca9fef
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_eSum_idem_d70afd6df18d


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
include hidem horth
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution : e0F N es * e0F N es = e0F N es := by
  unfold e0F
  apply eSum_idem
  · intro i x
    exact hidem i.1 (monicOf x)
  · intro i x y hxy
    exact horth i.1 _ _ (fun h => hxy (monicOf_injective h))
end Formalism.BasicNotions.Examples₂.NZ
