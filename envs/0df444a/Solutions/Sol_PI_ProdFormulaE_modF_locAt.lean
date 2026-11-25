-- Prove2me | solution 1 for PI.ProdFormulaE.modF_locAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:24:03.903212+00:00
-- url     : https://prove2.me/submissions/4edd764a-9deb-47b4-bc31-80e11ae3f954

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormMod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ModFIotaFinitePlace
import Theorems.Thm_PI_ProdFormulaE_modF_iota

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel IsDedekindDomain NumberField
open PI PI.ProdFormulaE
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
namespace PI.ProdFormulaE
theorem _root_.solution (hI : IndexFormula) (hC : CardStep) (L : Formalism.MainNotions.S.Loc.LocAt F E sig p)
    [IsNonarchimedeanLocalField L.Fp] (z : F) :
    modF L.Fp (L.ιF z) = HeightOneSpectrum.adicAbv F p z :=
  modF_iota p L.ιF hI hC L.dense L.val z
end PI.ProdFormulaE
