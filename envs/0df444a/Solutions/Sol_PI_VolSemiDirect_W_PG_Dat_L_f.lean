-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.L_f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:01:22.534077+00:00
-- url     : https://prove2.me/submissions/bc8cf893-af89-42f2-9362-3ea5875bf332

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_L_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_smul_right
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
theorem _root_.solution (H : D.Hyp) (w : Fin r → n → A) (s : Fin r → Fin r → A) (b : Fin r) :
    D.L w s (D.f b) = D.f b + (w b + ∑ a, s a b • D.e a) := by
  have hz0 : ∀ x, D.h x 0 = 0 := fun x => by simpa using h_smul_right (D := D) x 0 0
  simp [L_apply, pW_f H, H.ef, hz0, Finset.sum_add_distrib]
end PI.VolSemiDirect.W.PG.Dat
