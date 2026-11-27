-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.Pi_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:20:55.398267+00:00
-- url     : https://prove2.me/submissions/c63626d9-4ecb-4609-a2f0-4cb2c8cb8cb7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianIsotropicProjComplement
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_Pi_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pU_f
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pW_f


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
theorem _root_.solution (H : D.Hyp) (S : (n → A) →ₗ[A] (n → A)) (a : Fin r) : D.Pi S (D.f a) = D.f a := by
  rw [Pi_apply, pU_f H, pW_f H, map_zero, map_zero, add_zero]
end PI.VolSemiDirect.W.PG.Dat
