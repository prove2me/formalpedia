-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.UG.isSymm_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:38:23.961022+00:00
-- url     : https://prove2.me/submissions/245792bc-2133-4aa5-aa0e-203aa51a74c0

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_GmapLocEqOfFrame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_ExistsIsomMove
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_UG_star_h
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula PI.UnitaryGroupMassFormula.CntFormula.UG
open Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V}
namespace PI.UnitaryGroupMassFormula.CntFormula.UG
theorem _root_.solution (hs : h.IsSymm) {u : K} (hus : star u = u) : (u⁻¹ • h).IsSymm := by
  have H : ∀ a b : V, star ((u⁻¹ • h) a b) = (u⁻¹ • h) b a := by
    intro a b
    simp only [LinearMap.smul_apply, smul_eq_mul, star_mul', star_inv₀, hus, star_h hs]
  first | exact H | exact ⟨H⟩
end PI.UnitaryGroupMassFormula.CntFormula.UG
