-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.pW_S_pX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:50:51.272842+00:00
-- url     : https://prove2.me/submissions/4878aff5-3b8b-467c-889e-27a15c0e6e75

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pW_span
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pX_mem_span
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_S_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.LevelKSplit.W.SemiG.Dat
variable {D : Dat A n r}
namespace PI.LevelKSplit.W.SemiG.Dat
theorem _root_.solution (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)} (hX : D.MapX S) (u : n → A) :
    D.pW (S (D.pX u)) = 0 :=
  pW_span H (S_span hX (pX_mem_span u))
end PI.LevelKSplit.W.SemiG.Dat
