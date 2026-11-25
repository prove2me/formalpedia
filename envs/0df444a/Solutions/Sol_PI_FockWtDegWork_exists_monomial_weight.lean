-- Prove2me | solution 1 for PI.FockWtDegWork.exists_monomial_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:46:57.494776+00:00
-- url     : https://prove2.me/submissions/9f4e3c35-494d-4248-bf37-7e5c008bae50

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockWeightDegree_ExistsMonomialWeight
import Theorems.Thm_PI_FockWtDegWork_coeff_of_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action
open PI PI.FockWtDegWork
namespace PI.FockWtDegWork
theorem _root_.solution {σ ι : Type*} [Fintype σ]
    (T : ι → Module.End ℂ (MvPolynomial σ ℂ)) (f : ι → (σ →₀ ℕ) → ℚ)
    (hT : ∀ a β, T a (MvPolynomial.monomial β 1) =
      ((f a β : ℚ) : ℂ) • MvPolynomial.monomial β 1)
    (μ : ι → ℚ) (d : ℕ) (P : MvPolynomial σ ℂ) (hP : P ∈ homog σ d) (h0 : P ≠ 0)
    (hw : ∀ a, (T a - ((μ a : ℚ) : ℂ) • (LinearMap.id : Module.End ℂ (MvPolynomial σ ℂ))) P = 0) :
    ∃ α : σ →₀ ℕ, ∑ i, α i = d ∧ ∀ a, μ a = f a α := by
  obtain ⟨α, hα⟩ : ∃ α, MvPolynomial.coeff α P ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact h0 (MvPolynomial.ext _ _ fun β => by simp [hne β])
  refine ⟨α, ?_, fun a => ?_⟩
  · have hh : MvPolynomial.IsHomogeneous P d := (MvPolynomial.mem_homogeneousSubmodule d P).1 hP
    have h2 := hh hα
    have key : ∑ i ∈ α.support, α i = ∑ i, α i :=
      Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by simpa using hi
    first
      | (rw [← key]; exact h2)
      | (rw [← key]; simpa [Finsupp.weight_apply, Finsupp.sum] using h2)
      | (rw [← key]; simpa [Finsupp.degree_eq_weight_one.symm, Finsupp.degree] using h2)
      | (rw [← key]; simpa [Finsupp.degree, Finsupp.weight, Finsupp.sum] using h2)
  · have h1 := coeff_of_diag (T a) (fun β => ((f a β : ℚ) : ℂ)) (hT a) P α
    have h2 : T a P = ((μ a : ℚ) : ℂ) • P := by
      have h3 := hw a
      rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h3
      exact h3
    rw [h2, MvPolynomial.coeff_smul, smul_eq_mul] at h1
    have h3 : ((μ a : ℚ) : ℂ) = ((f a α : ℚ) : ℂ) := mul_right_cancel₀ hα h1
    exact_mod_cast h3
end PI.FockWtDegWork
