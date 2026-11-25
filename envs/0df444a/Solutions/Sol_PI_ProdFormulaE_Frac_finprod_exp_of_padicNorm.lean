-- Prove2me | solution 1 for PI.ProdFormulaE.Frac.finprod_exp_of_padicNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:22:12.885127+00:00
-- url     : https://prove2.me/submissions/b2aec4d7-cd2a-4d3d-8ea5-29c84041e1a9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_DenEqOneOfForallPadicNormLeOne
import Theorems.Thm_PI_ProdFormulaE_Frac_den_sub_sum_eq_one
import Theorems.Thm_PI_ProdFormulaE_Frac_exp_two_pi_of_den_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open PI PI.ProdFormulaE PI.ProdFormulaE.Frac
namespace PI.ProdFormulaE.Frac
theorem _root_.solution {ι : Type*} (ℓ : ι → ℕ) (hℓ : ∀ i, (ℓ i).Prime) (a : ι → ℚ)
    (ha : ∀ i, ∃ n : ℕ, (a i).den = ℓ i ^ n) (fib : ℕ → Finset ι)
    (hfib : ∀ i q, i ∈ fib q ↔ ℓ i = q) (hfin : {i | (a i).den ≠ 1}.Finite)
    (t : ℚ) (ht : ∀ q : ℕ, q.Prime → padicNorm q (t - ∑ i ∈ fib q, a i) ≤ 1) :
    (Function.mulSupport fun i => Complex.exp (2 * Real.pi * Complex.I * (a i : ℂ))).Finite ∧
    ∏ᶠ i, Complex.exp (2 * Real.pi * Complex.I * (a i : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) := by
  classical
  set I := hfin.toFinset with hIdef
  have hI : ∀ i, i ∉ I → (a i).den = 1 := by
    intro i hi
    by_contra h
    exact hi (hfin.mem_toFinset.2 h)
  have hsub : (Function.mulSupport fun i => Complex.exp (2 * Real.pi * Complex.I * (a i : ℂ))) ⊆
      (I : Set ι) := by
    intro i hi
    by_contra h
    exact hi (exp_two_pi_of_den_eq_one (hI i h))
  refine ⟨I.finite_toSet.subset hsub, ?_⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub, ← Complex.exp_sum]
  have h1 := exp_two_pi_of_den_eq_one (den_sub_sum_eq_one ℓ hℓ a ha fib hfib I hI t ht)
  have key : 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) =
      2 * Real.pi * Complex.I * (((t - ∑ i ∈ I, a i : ℚ)) : ℂ) +
        ∑ i ∈ I, 2 * Real.pi * Complex.I * (a i : ℂ) := by
    push_cast
    rw [← Finset.mul_sum]
    ring
  rw [key, Complex.exp_add, h1, one_mul]
end PI.ProdFormulaE.Frac
