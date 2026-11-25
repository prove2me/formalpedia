-- Prove2me | solution 1 for PI.WfSubstProof.substSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:29:44.607519+00:00
-- url     : https://prove2.me/submissions/8a906dac-4a0a-4607-9a7f-a4d3639a9027

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WfSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatMemWf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittSubstitution_CoeffMapMem
import Theorems.Thm_PI_WfSubstProof_exists_lift
import Theorems.Thm_PI_WfSubstProof_coeff_map_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WfSubstProof
namespace PI.WfSubstProof
theorem _root_.solution : PI.SubstSub := by
  intro A _ S σ f a hf ha ha0 n
  have hf' : ∀ e : Unit →₀ ℕ, MvPowerSeries.coeff e f ∈ S := fun e => by
    have he : e = Finsupp.single () (e ()) := by
      ext
      simp
    rw [he]
    exact hf (e ())
  obtain ⟨fS, rfl⟩ := exists_lift S f hf'
  obtain ⟨aS, rfl⟩ := exists_lift S a ha
  have haS0 : MvPowerSeries.constantCoeff aS = 0 := by
    have h0 := ha0
    rw [MvPowerSeries.constantCoeff_map] at h0
    exact Subtype.val_injective h0
  have hsub : PowerSeries.HasSubst aS := PowerSeries.HasSubst.of_constantCoeff_zero haS0
  have key : PowerSeries.subst (MvPowerSeries.map S.subtype aS) (MvPowerSeries.map S.subtype fS : PowerSeries A) =
      MvPowerSeries.map S.subtype (PowerSeries.subst aS fS) :=
    (PowerSeries.map_subst hsub fS).symm
  rw [key]
  exact coeff_map_mem S _ n
end PI.WfSubstProof
