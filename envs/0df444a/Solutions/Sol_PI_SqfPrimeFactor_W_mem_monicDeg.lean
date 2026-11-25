-- Prove2me | solution 1 for PI.SqfPrimeFactor.W.mem_monicDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:33:10.966039+00:00
-- url     : https://prove2.me/submissions/03e32d15-8edb-4b58-9325-6873996a9d31

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_BigPrimes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_MonicDegFnNatDegree
import Theorems.Thm_PI_SqfPrimeFactor_W_monicDeg_fn_monic
import Theorems.Thm_PI_SqfPrimeFactor_W_monicDeg_fn_natDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfPrimeFactor PI.SqfPrimeFactor.W
variable {g : ℕ} [Fact g.Prime]
namespace PI.SqfPrimeFactor.W
theorem _root_.solution {d : ℕ} {f : (ZMod g)[X]} :
    f ∈ monicDeg g d ↔ f.Monic ∧ f.natDegree = d := by
  constructor
  · intro hf
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hf
    exact ⟨monicDeg_fn_monic d c, monicDeg_fn_natDegree d c⟩
  · rintro ⟨hm, hd⟩
    refine Finset.mem_image.2 ⟨fun i => f.coeff i, Finset.mem_univ _, ?_⟩
    show X ^ d + ∑ i : Fin d, C (f.coeff i) * X ^ (i : ℕ) = f
    rw [Fin.sum_univ_eq_sum_range (fun i => C (f.coeff i) * X ^ i) d]
    have h := hm.as_sum
    rw [hd] at h
    exact h.symm
end PI.SqfPrimeFactor.W
