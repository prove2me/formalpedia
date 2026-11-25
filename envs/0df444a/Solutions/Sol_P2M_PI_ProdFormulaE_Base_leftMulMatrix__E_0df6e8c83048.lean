-- Prove2me | solution 1 for P2M_PI_ProdFormulaE_Base_leftMulMatrix__E_0df6e8c83048
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:21:46.834459+00:00
-- url     : https://prove2.me/submissions/0eaded1d-191a-4661-94ca-bb01fe8b9787

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ProdFormulaE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_BasisEApply
import Theorems.Thm_PI_ProdFormulaE_Base_basisE_apply
import Theorems.Thm_PI_ProdFormulaE_Base_basisE_repr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField Formalism.MainNotions.S.Loc
open PI PI.ProdFormulaE PI.ProdFormulaE.Base
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
namespace PI.ProdFormulaE.Base
theorem _root_.solution (L : LocAt F E sig p) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι F E) (h : Module.finrank F E = 2) (x : E) :
    Algebra.leftMulMatrix (basisE L b h) (L.ιE x) = (Algebra.leftMulMatrix b x).map L.ιF := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    basisE_apply, ← map_mul, basisE_repr]
end PI.ProdFormulaE.Base
