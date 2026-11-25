-- Prove2me | solution 1 for PI.VolStabW.exists_basis_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:37:16.137199+00:00
-- url     : https://prove2.me/submissions/6ee24d55-cce6-4b2e-b4de-71aeeaf6e9c5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntD
import Theorems.Thm_PI_VolStabW_exists_anti
import Theorems.Thm_PI_VolStabW_anti_coeff
import Theorems.Thm_PI_VolStabW_sigma_invol


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.VolStabW
theorem _root_.solution (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) :
    ∃ (δ : E) (D0 : F) (c : Module.Basis (Fin 2) F E), δ ≠ 0 ∧ σ δ = -δ ∧
      δ * δ = algebraMap F E D0 ∧ D0 ≠ 0 ∧ c 0 = 1 ∧ c 1 = δ := by
  obtain ⟨δ, hδ0, hσδ⟩ := exists_anti σ hCM
  have hinv := sigma_invol σ hCM.2.2.2
  have li : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := anti_coeff σ hδ0 hσδ s t (by rw [hst, map_zero])
    subst ht
    simp only [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.1 hst).resolve_right one_ne_zero, rfl⟩
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by
    rw [hCM.2.2.1]; rfl
  let c := basisOfLinearIndependentOfCardEqFinrank li hcard
  have hc0 : c 0 = 1 := by simp [c]
  have hc1 : c 1 = δ := by simp [c]
  have hsum := c.sum_repr (δ * δ)
  rw [Fin.sum_univ_two, hc0, hc1] at hsum
  have hβ : c.repr (δ * δ) 1 = 0 := by
    refine anti_coeff σ hδ0 hσδ (c.repr (δ * δ) 0) _ ?_
    rw [hsum, map_mul, hσδ]; ring
  rw [hβ, zero_smul, add_zero, Algebra.smul_def, mul_one] at hsum
  refine ⟨δ, c.repr (δ * δ) 0, c, hδ0, hσδ, hsum.symm, ?_, hc0, hc1⟩
  intro h0
  rw [h0, map_zero] at hsum
  exact hδ0 (mul_self_eq_zero.1 hsum.symm)
end PI.VolStabW
