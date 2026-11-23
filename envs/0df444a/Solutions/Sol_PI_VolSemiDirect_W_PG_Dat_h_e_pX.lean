-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.h_e_pX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:36.493798+00:00
-- url     : https://prove2.me/submissions/252040a2-b3df-4f81-a83e-e455bef85645

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
theorem _root_.solution (H : D.Hyp) (b : Fin r) (u : n → A) : D.h (D.e b) (D.pX u) = 0 := by
  have key : ∀ x y, D.h x y = D.hL x y := fun _ _ => rfl
  have H3 : ∀ a c, D.hL (D.e a) (D.e c) = 0 := fun a c => H.3 a c
  rw [key]
  simp only [Dat.pX.eq_1, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum,
    map_smul, H3, smul_zero, Finset.sum_const_zero]
end PI.VolSemiDirect.W.PG.Dat
