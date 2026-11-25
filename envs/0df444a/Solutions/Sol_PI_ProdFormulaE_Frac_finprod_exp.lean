-- Prove2me | solution 1 for PI.ProdFormulaE.Frac.finprod_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:26:48.304437+00:00
-- url     : https://prove2.me/submissions/3d11fd1c-0257-474c-b7fb-5458f7017bf9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_DenEqOneOfForallPadicNormLeOne
import Theorems.Thm_PI_ProdFormulaE_Frac_finprod_exp_of_padicNorm

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
    (hfib : ∀ i q, i ∈ fib q ↔ ℓ i = q) (hfin : {i | (a i).den ≠ 1}.Finite) (t : ℚ)
    (ht : ∀ (q : ℕ) [Fact q.Prime], ‖(t : ℚ_[q]) - ∑ i ∈ fib q, (a i : ℚ_[q])‖ ≤ 1) :
    (Function.mulSupport fun i => Complex.exp (2 * Real.pi * Complex.I * (a i : ℂ))).Finite ∧
    ∏ᶠ i, Complex.exp (2 * Real.pi * Complex.I * (a i : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) := by
  refine finprod_exp_of_padicNorm ℓ hℓ a ha fib hfib hfin t ?_
  intro q hq
  haveI : Fact q.Prime := ⟨hq⟩
  have h := ht q
  have e : ‖((t - ∑ i ∈ fib q, a i : ℚ) : ℚ_[q])‖ = _ := Padic.eq_padicNorm (t - ∑ i ∈ fib q, a i)
  have h' : ((padicNorm q (t - ∑ i ∈ fib q, a i) : ℚ) : ℝ) ≤ 1 := by
    rw [← e]
    push_cast
    exact h
  exact_mod_cast h'
end PI.ProdFormulaE.Frac
