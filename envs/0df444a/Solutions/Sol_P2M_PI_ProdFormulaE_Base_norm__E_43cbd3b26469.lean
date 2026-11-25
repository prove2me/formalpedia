-- Prove2me | solution 1 for P2M_PI_ProdFormulaE_Base_norm__E_43cbd3b26469
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:27:31.82199+00:00
-- url     : https://prove2.me/submissions/478def45-24f5-434c-8a45-4655e9b507ac

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ProdFormulaE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_BasisEApply
import Theorems.Thm_P2M_PI_ProdFormulaE_Base_leftMulMatrix__E_0df6e8c83048

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
theorem _root_.solution (L : LocAt F E sig p) (h : Module.finrank F E = 2) (x : E) :
    Algebra.norm L.Fp (L.ιE x) = L.ιF (Algebra.norm F x) := by
  classical
  let b := Module.finBasisOfFinrankEq F E h
  rw [Algebra.norm_eq_matrix_det (basisE L b h), Algebra.norm_eq_matrix_det b,
    leftMulMatrix_ιE, RingHom.map_det]
  rfl
end PI.ProdFormulaE.Base
