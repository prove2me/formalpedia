-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.phiM_ker_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:47:35.763886+00:00
-- url     : https://prove2.me/submissions/a04c69ad-ce59-4e66-a7a5-88051ed25a2a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_MuMEvalPowEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_muM_common
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_muM_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_muM_eval_pow_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM Polynomial
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (f : MonoidAlgebra ℤ (muM l)) (hf : phiM l f = 0) : psiM l f = 0 := by
  classical
  obtain ⟨n, hn, hln, hS⟩ := muM_common l f.coeff.support
  obtain ⟨g, hg, hgen⟩ := muM_exists_gen l n hn
  have hk : ∀ a : muM l, ∃ k : ℕ, a ∈ f.coeff.support → g ^ k = (a : ℂ_[l]) := by
    intro a
    by_cases ha : a ∈ f.coeff.support
    · obtain ⟨k, hk⟩ := hgen a (hS a ha)
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose k hk using hk
  let p : ℤ[X] := ∑ a ∈ f.coeff.support, C (f.coeff a) * X ^ (k a)
  have h1 : p.eval₂ (Int.castRingHom ℂ_[l]) g = 0 := by
    rw [← hf, phiM, MonoidAlgebra.lift_apply, Finsupp.sum, eval₂_finsetSum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, hk a ha]
    simp [zsmul_eq_mul]
  have h2 := muM_eval_pow_eq_zero l n hn hln g hg p h1
  rw [← h2, psiM, MonoidAlgebra.lift_apply, Finsupp.sum, eval₂_finsetSum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, ← pow_mul, mul_comm l, pow_mul, hk a ha]
  simp [zsmul_eq_mul]
end ReciprocityTheory.ChartRestriction.L1
