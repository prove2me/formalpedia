-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_quotLaurent_smul_eq_zero_d36d759dd77d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:08:16.618073+00:00
-- url     : https://prove2.me/submissions/a63b6793-bccd-474f-95db-83611b8168ff

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoFiltGraded
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_laurent_smul_eq_zero_b71283610103

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
variable {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]
variable (M₁ M₂ : FinGradedSub (S := S) (x := x) E)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {p : Poly S N} (hp : p ∈ primeOf (S := S) x) (y : quotLaurent M₁ M₂) :
    p • y = 0 := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
    Submodule.coe_subtype, Submodule.coe_smul, laurent_smul_eq_zero hp]
  exact zero_mem _
end GroundTheory.Heights₂.Heights.Kleiman
