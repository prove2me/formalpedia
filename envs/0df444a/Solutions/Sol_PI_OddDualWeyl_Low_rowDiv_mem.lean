-- Prove2me | solution 1 for PI.OddDualWeyl.Low.rowDiv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:59:04.811082+00:00
-- url     : https://prove2.me/submissions/a0e07b0e-b6ec-4993-85f5-d465546133d4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl PI.OddDualWeyl.Low
variable {R : Type*} [CommRing R]
namespace PI.OddDualWeyl.Low
theorem _root_.solution {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (a b : Fin r) (j : ℕ)
    {f : MvPolynomial (Fin r × Fin n) R} (hf : f ∈ weyl R r n hn ν) :
    rowDiv R a b j f ∈ weyl R r n hn ν := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact Submodule.subset_span ⟨(a, b, j) :: w, rfl⟩
  | zero => simp [rowDiv]
  | add x y _ _ hx hy => simpa [rowDiv] using add_mem hx hy
  | smul c x _ hx => simpa [rowDiv] using Submodule.smul_mem _ c hx
end PI.OddDualWeyl.Low
