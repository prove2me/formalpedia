-- Prove2me | solution 1 for PI.ProdFormulaE.modF_iota_finitePlace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:23:59.728277+00:00
-- url     : https://prove2.me/submissions/ed59ad58-19f1-4f7d-bf41-cc0d5d3d8954

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
namespace PI.ProdFormulaE
theorem _root_.solution {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ι : F →+* K) (hI : IndexFormula) (hC : CardStep) (hd : DenseRange ι)
    (hv : ∀ x y : F, (ι x ≤ᵥ ι y) ↔ p.valuation F x ≤ p.valuation F y) (z : F) :
    modF K (ι z) = FinitePlace.mk p z := by
  rw [modF_iota p ι hI hC hd hv z, FinitePlace.mk_apply, FinitePlace.norm_embedding]
end PI.ProdFormulaE
