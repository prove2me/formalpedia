-- Prove2me | solution 1 for P2M_PI_ProdFormulaE_Base_isUnit__E_fad958e51c22
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:18:47.29347+00:00
-- url     : https://prove2.me/submissions/c792c733-44d2-4050-ad4b-a819bcee6732

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ProdFormulaE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_BasisEApply

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
theorem _root_.solution (L : LocAt F E sig p) {x : E} (hx : x ≠ 0) : IsUnit (L.ιE x) :=
  (isUnit_iff_ne_zero.mpr hx).map L.ιE
end PI.ProdFormulaE.Base
