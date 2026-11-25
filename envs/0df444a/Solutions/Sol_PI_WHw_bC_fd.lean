-- Prove2me | solution 1 for PI.WHw.bC_fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:21:53.019804+00:00
-- url     : https://prove2.me/submissions/1c8001fb-bb4f-4247-9534-a8606b8a091f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ClosedEqNablaC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_BCRowGenMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ConstructionB
import Theorems.Thm_PI_WHw_bC_dualWeyl_le_homog
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
noncomputable section
namespace PI.WHw
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.REAL MvPolynomial
private theorem homogeneousSubmodule_le_span_bounded_monomials (σ : Type) [Fintype σ] (N : ℕ) :
    homogeneousSubmodule σ ℂ N ≤ Submodule.span ℂ ((fun d => (monomial d (1 : ℂ) : MvPolynomial σ ℂ)) ''
      Set.range (fun e : σ → Fin (N + 1) => Finsupp.equivFunOnFinite.symm (fun v => (e v : ℕ)))) := by
  intro f hf
  rw [mem_homogeneousSubmodule] at hf
  rw [f.as_sum]
  refine Submodule.sum_mem _ (fun d hd => ?_)
  have hdeg := hf (MvPolynomial.mem_support_iff.mp hd)
  have hle : ∀ v, d v ≤ N := by
    intro v
    rw [Finsupp.weight_apply, Finsupp.sum] at hdeg
    simp only [Pi.one_apply, smul_eq_mul, mul_one] at hdeg
    by_cases hv : v ∈ d.support
    · rw [← hdeg]
      exact Finset.single_le_sum (fun i _ => Nat.zero_le _) hv
    · have h0 : d v = 0 := by simpa [Finsupp.mem_support_iff] using hv
      rw [h0]
      exact Nat.zero_le _
  rw [show monomial d (coeff d f) = coeff d f • monomial d (1 : ℂ) by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, ⟨fun v => ⟨d v, Nat.lt_succ_of_le (hle v)⟩, ?_⟩, rfl⟩)
  ext v
  simp
end PI.WHw
end
end

set_option autoImplicit false
noncomputable section
open PI PI.WHw
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.REAL MvPolynomial
namespace PI.WHw
theorem _root_.solution (r n : ℕ) (ν : Fin n → ℕ) : FiniteDimensional ℂ (dualWeyl ℂ r n ν) := by
  have h1 := (bC_dualWeyl_le_homog r n ν).trans (homogeneousSubmodule_le_span_bounded_monomials (Fin r × Fin n) (∑ s, ν s))
  haveI := FiniteDimensional.span_of_finite ℂ ((Set.finite_range (fun e : (Fin r × Fin n) → Fin ((∑ s, ν s) + 1) =>
    Finsupp.equivFunOnFinite.symm (fun v => (e v : ℕ)))).image
      (fun d => (monomial d (1 : ℂ) : MvPolynomial (Fin r × Fin n) ℂ)))
  exact Submodule.finiteDimensional_of_le h1
end PI.WHw
