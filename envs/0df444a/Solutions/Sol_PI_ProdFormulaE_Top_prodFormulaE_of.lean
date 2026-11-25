-- Prove2me | solution 1 for PI.ProdFormulaE.Top.prodFormulaE_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:53:02.289568+00:00
-- url     : https://prove2.me/submissions/3f624871-1508-41e6-84f5-5f260a4bbc2e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ProdFormulaE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ResCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_BasisEApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_DenEqOneOfForallPadicNormLeOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ProdFormulaEOf
import Theorems.Thm_PI_ProdFormulaE_Top_clause1
import Theorems.Thm_PI_ProdFormulaE_Top_clause2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField MeasureTheory ValuativeRel Formalism.MainNotions.S.Loc
open PI PI.ProdFormulaE PI.ProdFormulaE.Top
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}
namespace PI.ProdFormulaE.Top
theorem _root_.solution (hH : St.HaarAlg) (hN : St.NormLoc) (hT : Tr.TrSum) (hI : St.TrInt)
    (hR : St.ResCharIff) : PI.ProdFormulaE.ProdFormulaE := by
  intro F E _ _ _ _ _ sig h2 L
  exact ⟨fun M hM x hx => clause1 hH hN h2 L M hM x hx, fun x => clause2 hT hI hR h2 L x⟩
end PI.ProdFormulaE.Top
