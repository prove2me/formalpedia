-- Prove2me | solution 1 for PI.SqfPrimeFactor.W.mem_bad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:41:13.683093+00:00
-- url     : https://prove2.me/submissions/38644e2d-4980-4a17-b9bc-03297bd82b53

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_MonicDegFnNatDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_SquarefreeCountEstimate
import Theorems.Thm_PI_SqfPrimeFactor_W_mem_irrDeg
import Theorems.Thm_PI_SqfPrimeFactor_W_mem_monicDeg


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
open PI.SqfLab
variable {g : ℕ} [Fact g.Prime]
namespace PI.SqfPrimeFactor.W
theorem _root_.solution {r p : ℕ} {f : (ZMod g)[X]} (hf : f ∈ bad g r p) :
    ∃ q h : (ZMod g)[X], f = q * h ∧ q.Monic ∧ q.natDegree = p ∧ Irreducible q ∧
      h.Monic ∧ h.natDegree = r - p := by
  obtain ⟨⟨q, h⟩, hx, rfl⟩ := Finset.mem_image.1 hf
  simp only [Finset.mem_product, mem_irrDeg, mem_monicDeg] at hx
  obtain ⟨⟨⟨hqm, hqd⟩, hqi⟩, hhm, hhd⟩ := hx
  exact ⟨q, h, rfl, hqm, hqd, hqi, hhm, hhd⟩
end PI.SqfPrimeFactor.W
