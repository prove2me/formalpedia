-- Prove2me | solution 1 for PI.ProdFormulaE.iota_mem_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:06:00.805607+00:00
-- url     : https://prove2.me/submissions/2d250591-740a-4b51-ba75-a2fd72a83f82

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormMod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ModFIotaFinitePlace

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
variable {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
  {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (ι : F →+* K)
namespace PI.ProdFormulaE
theorem _root_.solution (hv : ∀ x y : F, (ι x ≤ᵥ ι y) ↔ p.valuation F x ≤ p.valuation F y)
    (a : 𝓞 F) : ι (a : F) ∈ 𝒪[K] := by
  rw [Valuation.mem_integer_iff, ← map_one (valuation K), ← Valuation.Compatible.vle_iff_le,
    ← map_one ι, hv, map_one]
  exact p.valuation_le_one a
end PI.ProdFormulaE
