-- Prove2me | solution 1 for PI.ProdFormulaE.Base.basisE_repr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:11:51.659164+00:00
-- url     : https://prove2.me/submissions/ed9066d6-0436-4625-981d-92a568b96043

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ProdFormulaE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_BasisEApply
import Theorems.Thm_PI_ProdFormulaE_Base_basisE_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField Formalism.MainNotions.S.Loc
open PI PI.ProdFormulaE PI.ProdFormulaE.Base
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
namespace PI.ProdFormulaE.Base
theorem _root_.solution (L : LocAt F E sig p) {ι : Type*} [Fintype ι] (b : Module.Basis ι F E)
    (h : Module.finrank F E = 2) (y : E) (i : ι) :
    (basisE L b h).repr (L.ιE y) i = L.ιF (b.repr y i) := by
  have hy : L.ιE y = ∑ j, L.ιF (b.repr y j) • basisE L b h j := by
    simp only [basisE_apply]; exact ιE_eq_sum L b y
  rw [hy, Module.Basis.repr_sum_self]
end PI.ProdFormulaE.Base
