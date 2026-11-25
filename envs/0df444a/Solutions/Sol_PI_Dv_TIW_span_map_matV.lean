-- Prove2me | solution 1 for PI.Dv.TIW.span_map_matV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:58:23.709384+00:00
-- url     : https://prove2.me/submissions/6ef634bf-b84d-4f34-824a-a29d7376fa57

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxSmulSubMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MatVTransvection
import Theorems.Thm_PI_Dv_TIW_map_matV_pi

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
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n K) (hA : A.det ≠ 0)
    (L : Submodule (𝓞 K) (n → V)) (S : Submodule K V)
    (hL : Submodule.span K (L : Set (n → V)) = Submodule.pi Set.univ fun _ : n => S) :
    Submodule.span K ((L.map ((matV A).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (n → V)) : Set (n → V)) =
      Submodule.pi Set.univ fun _ : n => S := by
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hL, map_matV_pi A hA]
end PI.Dv.TIW
