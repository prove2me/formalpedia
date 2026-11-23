-- Prove2me | solution 1 for PI.Dv.TIW.idx_chain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:01:53.309558+00:00
-- url     : https://prove2.me/submissions/512e6978-b0b5-4145-b6df-6b3d59328e07

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxNonnegOfLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.TIW
theorem _root_.solution (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (M N P : Submodule (𝓞 K) V) (hM : M.FG) (hN : N.FG)
    (hP : P.FG) (h1 : Submodule.span K (M : Set V) = Submodule.span K (N : Set V))
    (h2 : Submodule.span K (P : Set V) = Submodule.span K (N : Set V)) :
    idxAt w M P = idxAt w M N + idxAt w N P :=
  (hI K V w M N hM hN h1).2.1 P hP h2
end PI.Dv.TIW
