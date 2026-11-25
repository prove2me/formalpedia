-- Prove2me | solution 1 for PI.ProdFormulaE.Top.fam_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:05:19.46083+00:00
-- url     : https://prove2.me/submissions/0fc56d51-22fb-4172-a06f-f0b8b03dd83e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ProdFormulaE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ResCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_BasisEApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_DenEqOneOfForallPadicNormLeOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ProdFormulaEOf

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
theorem _root_.solution (hR : St.ResCharIff) (L : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p)
    (q : ℕ) [hq : Fact q.Prime] : (fam L q).Over := by
  refine ⟨Subtype.val_injective, fun p => ⟨?_, fun h => ⟨⟨p, (hR F p q hq.out).2 h⟩, rfl⟩⟩⟩
  rintro ⟨i, rfl⟩
  exact (hR F i.1 q hq.out).1 i.2
end PI.ProdFormulaE.Top
