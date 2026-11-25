-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.xxw_tr_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:31:36.271535+00:00
-- url     : https://prove2.me/submissions/0d0119b3-fdd3-4ed7-9054-7c23e5ba575c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_FreeCoordinateAffineInvertible
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_xxw_eN_eq
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_xxw_diff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {E : Type} [Field E]
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {n' c' n c : ℕ} (ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)) (t : FC n' c' n c → E) :
    Tr ρ t = xxwLin ρ t + Tr ρ 0 := by
  funext f
  simp only [Tr, Pi.add_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [xxw_eN_eq]
  have h := xxw_diff (E := E) t f.1.2
  rw [sub_eq_iff_eq_add] at h
  rw [h, map_add, Pi.add_apply]
  rfl
end PI.TwistedEisensteinNonvanishing.W
