-- Prove2me | solution 1 for PI.WittUnramWork.sHom_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:22:58.882021+00:00
-- url     : https://prove2.me/submissions/a03b12f5-4286-4ba1-90b1-7472dc2d8053

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WittUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittUnramified_GhostComponentG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WittUnramWork
open WittVector Finset
variable {p : ℕ} [hp : Fact p.Prime] {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]
variable (p Qq) [Invertible (p : Qq)] (F : W →+* W)
variable (hF : ∀ x : W, ∃ y : W, F x = x ^ p + (p : W) * y)
include hF
namespace PI.WittUnramWork
theorem _root_.solution (hinj : Function.Injective (algebraMap W Qq)) (x : W) :
    (sHom p Qq F hF hinj x).coeff 0 = x := by
  apply hinj
  rw [← G_coeff_zero p Qq F x, ← map_sFun p Qq F hF hinj x, WittVector.map_coeff]
  try rfl
end PI.WittUnramWork
