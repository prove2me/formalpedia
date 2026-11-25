-- Prove2me | solution 1 for ReciprocityTheory.Cheb.uphi_torsion_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:46:14.225799+00:00
-- url     : https://prove2.me/submissions/806b25f0-946a-4a98-b5d3-2653e27c0ae7

import Definitions.Def_ReciprocityTheory_Chebotarev_Ucoord
import Definitions.Def_ReciprocityTheory_Chebotarev_UnitPart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution {ζ : (𝓞 E)ˣ} (hζ : ζ ∈ torsion E) (x : mixedSpace E) :
    uphi (ζ • x) = uphi x := by
  unfold uphi ucoord
  rw [norm_unit_smul, logMap_torsion_smul x hζ]
end ReciprocityTheory.Cheb
