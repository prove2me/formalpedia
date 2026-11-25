-- Prove2me | solution 1 for PI.ProdFormulaE.modF_localization_eq_adicAbv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:29:05.103271+00:00
-- url     : https://prove2.me/submissions/1790ae42-7eb2-4453-a65f-3de1de440816

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ResCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ModFIotaFinitePlace
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormIndex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_CardQuotientEqAbsNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormSt
import Theorems.Thm_PI_ProdFormulaE_card_quotient_eq_absNorm
import Theorems.Thm_PI_ProdFormulaE_modF_locAt
import Theorems.Thm_PI_ProdFormulaE_modulus_mul_card_quotient


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
open PI PI.ProdFormulaE
namespace PI.ProdFormulaE
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
    (L : Formalism.MainNotions.S.Loc.LocAt F E sig p) [IsNonarchimedeanLocalField L.Fp] (z : F) :
    modF L.Fp (L.ιF z) = NumberField.HeightOneSpectrum.adicAbv F p z :=
  modF_locAt modulus_mul_card_quotient card_quotient_eq_absNorm L z
end PI.ProdFormulaE
