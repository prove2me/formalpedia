-- Prove2me | solution 1 for PI.QnCovDetW.sum_fun_eq_sum_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:07:13.744605+00:00
-- url     : https://prove2.me/submissions/047aad56-eeb2-47b6-8aec-cf4ed7673fee

import Definitions.Def_Formalism_PeriodIntegrals_ContractionsCovariantIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantDeterminantScaling_IntCastMulEqSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnCovDetW
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnCovDetW
theorem _root_.solution {M : Type*} [AddCommMonoid M] {n : ℕ}
    (g : (Fin n → Fin n) → M) (hg : ∀ c, ¬ Function.Injective c → g c = 0) :
    ∑ c, g c = ∑ σ : Equiv.Perm (Fin n), g σ := by
  classical
  have h2 : ∑ σ : Equiv.Perm (Fin n), g σ = ∑ c ∈ Finset.univ.filter Function.Injective, g c := by
    refine Finset.sum_nbij (fun σ => (σ : Fin n → Fin n)) (fun σ _ => by simpa using σ.injective)
      (by intro a _ b _ h; exact DFunLike.coe_injective h) (by
        intro c hc
        have hc' : Function.Injective c := (Finset.mem_filter.1 (Finset.mem_coe.1 hc)).2
        exact ⟨Equiv.ofBijective c (Finite.injective_iff_bijective.1 hc'),
          Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩) (fun _ _ => rfl)
  rw [h2, Finset.sum_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs with h
  · rfl
  · exact hg c h
end PI.QnCovDetW
