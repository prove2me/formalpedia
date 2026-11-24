-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.comm_img
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:23:19.498802+00:00
-- url     : https://prove2.me/submissions/688217e8-a6f4-4cfc-9ee3-178c21098b5d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_CommOfBounded
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_QequivApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_KeyDef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_ExistsGoodForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (g : V ≃ₗ[ℂ] V) {S Λ : AddSubgroup V}
    (hg1 : relIdx S (imgLat (g : V →ₗ[ℂ] V) S) ≠ 0) (hg2 : relIdx (imgLat (g : V →ₗ[ℂ] V) S) S ≠ 0)
    (h1 : relIdx S Λ ≠ 0) (h2 : relIdx Λ S ≠ 0) :
    relIdx S (imgLat (g : V →ₗ[ℂ] V) Λ) ≠ 0 ∧ relIdx (imgLat (g : V →ₗ[ℂ] V) Λ) S ≠ 0 := by
  have hinj : Function.Injective (g : V →ₗ[ℂ] V).toAddMonoidHom := g.injective
  have hm : ∀ A B : AddSubgroup V, relIdx (imgLat (g : V →ₗ[ℂ] V) A) (imgLat (g : V →ₗ[ℂ] V) B) = relIdx A B :=
    fun A B => AddSubgroup.relIndex_map_map_of_injective A B hinj
  refine ⟨?_, ?_⟩
  · exact AddSubgroup.relIndex_ne_zero_trans hg1 (by rw [← hm S Λ] at h1; exact h1)
  · exact AddSubgroup.relIndex_ne_zero_trans (by rw [← hm Λ S] at h2; exact h2) hg2
end PI.UnitaryGroupMassFormula.UnimodLocStd
