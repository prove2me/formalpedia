-- Prove2me | solution 1 for PI.Dv.TIW.span_latPow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:29.253805+00:00
-- url     : https://prove2.me/submissions/1af93b45-f7fc-4494-8e24-a6f321161bf9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxSmulSubMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MatVTransvection
import Theorems.Thm_PI_Dv_TIW_span_pi_eq


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
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] (M : Submodule (𝓞 K) V) :
    Submodule.span K ((latPow n M : Submodule (𝓞 K) (n → V)) : Set (n → V)) =
      Submodule.pi Set.univ fun _ : n => Submodule.span K (M : Set V) :=
  span_pi_eq _
end PI.Dv.TIW
