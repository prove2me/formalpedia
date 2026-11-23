-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.L_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:25:28.192722+00:00
-- url     : https://prove2.me/submissions/8eb73847-a880-4ebc-add0-f3a240680684

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianIsotropicProjComplement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec

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
variable (D : Dat A n r)
namespace PI.VolSemiDirect.W.PG.Dat
theorem _root_.solution (w : Fin r → n → A) (s : Fin r → Fin r → A) (v : n → A) :
    D.L w s v = v + ∑ b, D.h (D.e b) v • (w b + ∑ a, s a b • D.e a) -
      ∑ a, D.h (w a) (D.pW v) • D.e a := by
  simp only [L, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply,
    LinearMap.smulRight_apply, LinearMap.comp_apply]
  rfl
end PI.VolSemiDirect.W.PG.Dat
