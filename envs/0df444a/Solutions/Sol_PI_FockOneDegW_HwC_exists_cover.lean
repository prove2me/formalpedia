-- Prove2me | solution 1 for PI.FockOneDegW.HwC.exists_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:39:52.367306+00:00
-- url     : https://prove2.me/submissions/af25d783-670b-4cc3-b95d-256f54af6beb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_CoeffXMulPderivSelf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_HighestWeightExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW PI.FockOneDegW.HwC
namespace PI.FockOneDegW.HwC
theorem _root_.solution {p q r s : ℕ} (U : Submodule ℂ (Pol p q r s)) [FiniteDimensional ℂ U] :
    ∃ S : Finset (Ln p q r s →₀ ℕ), ∀ u ∈ U, u.support ⊆ S := by
  classical
  let bs := Module.finBasis ℂ U
  refine ⟨Finset.univ.biUnion fun k => ((bs k : U) : Pol p q r s).support, fun u hu => ?_⟩
  have e : (⟨u, hu⟩ : U) = ∑ k, (bs.repr ⟨u, hu⟩ k) • bs k := (bs.sum_repr _).symm
  have e' : u = ∑ k, (bs.repr ⟨u, hu⟩ k) • ((bs k : U) : Pol p q r s) := by
    have h := congrArg Subtype.val e
    rw [Submodule.coe_sum] at h
    simp only [Submodule.coe_smul] at h
    exact h
  rw [e']
  exact MvPolynomial.support_sum.trans (Finset.biUnion_mono fun k _ => MvPolynomial.support_smul)
end PI.FockOneDegW.HwC
