-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.S_pX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:34:34.614819+00:00
-- url     : https://prove2.me/submissions/3409d623-4965-4233-b483-98034f2de46f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianIsotropicProjComplement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.PG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.VolSemiDirect.W.PG.Dat
variable {D : Dat A n r}
namespace PI.VolSemiDirect.W.PG.Dat
theorem _root_.solution {S : (n → A) →ₗ[A] (n → A)} (hS : ∀ a, S (D.e a) = D.e a) (u : n → A) :
    S (D.pX u) = D.pX u := by
  simp only [Dat.pX.eq_1, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum,
    map_smul, hS]
end PI.VolSemiDirect.W.PG.Dat
