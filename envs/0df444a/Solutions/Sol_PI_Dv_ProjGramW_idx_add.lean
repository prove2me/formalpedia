-- Prove2me | solution 1 for PI.Dv.ProjGramW.idx_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:12.871817+00:00
-- url     : https://prove2.me/submissions/707f686c-4227-4a4a-bc14-252e35ad9412

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.ProjGramW
theorem _root_.solution (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {M N P : Submodule (𝓞 K) V}
    (hM : M.FG) (hN : N.FG) (hP : P.FG) (hMN : Submodule.span K (M : Set V) = Submodule.span K (N : Set V))
    (hPN : Submodule.span K (P : Set V) = Submodule.span K (N : Set V)) :
    idxAt w M P = idxAt w M N + idxAt w N P :=
  (hI K V w M N hM hN hMN).2.1 P hP hPN
end PI.Dv.ProjGramW
