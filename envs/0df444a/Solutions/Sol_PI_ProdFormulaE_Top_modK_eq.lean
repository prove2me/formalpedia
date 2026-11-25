-- Prove2me | solution 1 for PI.ProdFormulaE.Top.modK_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:33:16.472925+00:00
-- url     : https://prove2.me/submissions/4a162d80-6ce9-4535-b3ec-4d21ec309c4c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ProdFormulaE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ResCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_BasisEApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_DenEqOneOfForallPadicNormLeOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ProdFormulaEOf
import Theorems.Thm_PI_ProdFormulaE_Top_modF_nonneg
import Theorems.Thm_P2M_PI_ProdFormulaE_Base_isUnit__E_fad958e51c22
import Theorems.Thm_P2M_PI_ProdFormulaE_Base_norm__E_43cbd3b26469


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
theorem _root_.solution (hH : St.HaarAlg) (hN : St.NormLoc) (h2 : Module.finrank F E = 2)
    {p : HeightOneSpectrum (𝓞 F)} (L : LocAt F E sig p) (M : Model L.Fp L.Ep) (hM : M.OK)
    {x : E} (hx : x ≠ 0) :
    M.modK (L.ιE x) = FinitePlace.mk p (Algebra.norm F x) := by
  haveI := L.lf
  haveI := hM.borel
  haveI := hM.haar.haar
  haveI := L.free
  haveI := Base.finite L
  haveI := L.top
  unfold Model.modK
  rw [hH L.Fp L.Ep M.mu (L.ιE x) (Base.isUnit_ιE L hx) _, hM.haar.volR, mul_one,
    ENNReal.toReal_ofReal (modF_nonneg _), Base.norm_ιE L h2, hN F p L.Fp L.ιF L.dense L.val]
end PI.ProdFormulaE.Top
