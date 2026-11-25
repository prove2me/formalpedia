-- Prove2me | solution 1 for PI.WittUnramWork.G_frob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:14:21.13857+00:00
-- url     : https://prove2.me/submissions/e99c95a7-1caa-4601-95ed-ddd0e6e1fcae

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
namespace PI.WittUnramWork
theorem _root_.solution (x : W) : G p Qq F (F x) = frobenius (G p Qq F x) := by
  apply (ghostEquiv p Qq).injective
  funext n
  have h1 : (ghostEquiv p Qq) (G p Qq F (F x)) n = ghostComponent n (G p Qq F (F x)) := by
    rw [← WittVector.ghostMap_apply, ← WittVector.ghostEquiv_coe p Qq]
    rfl
  have h2 : (ghostEquiv p Qq) (frobenius (G p Qq F x)) n = ghostComponent n (frobenius (G p Qq F x)) := by
    rw [← WittVector.ghostMap_apply, ← WittVector.ghostEquiv_coe p Qq]
    rfl
  rw [h1, h2, WittVector.ghostComponent_frobenius, ghostComponent_G, ghostComponent_G,
    ← Function.iterate_succ_apply]
end PI.WittUnramWork
