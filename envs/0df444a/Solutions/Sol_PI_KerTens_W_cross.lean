-- Prove2me | solution 1 for PI.KerTens.W.cross
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:04:10.951999+00:00
-- url     : https://prove2.me/submissions/5c6565a3-f612-4b53-b009-66d6d7f6d229

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerTens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorSpanning_MatHHOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorSpanning_TensSpans
import Theorems.Thm_PI_KerTens_W_slice_th


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open PI PI.KerTens PI.KerTens.W
open Formalism.L2.Th1.H (Sesq matH alphaQ qOf opU Th fixedBy)
namespace PI.KerTens.W
theorem _root_.solution (c : ℝ) (L : PeriodPair) {n : Type} [Fintype n] [DecidableEq n] (ΛM : AddSubgroup (n → ℂ))
    (θ : (n → ℂ) → ℂ)
    (hyp : ∀ F ∈ Th (matH (hOne L n)) (alphaQ c (matH (hOne L n))) ΛM, ∃ a : ℂ, F = a • θ)
    {N N' : ℕ} (F : (n → Fin N' → Fin N → ℂ) → ℂ)
    (hF : F ∈ Th (formV (Formalism.L2.Th1.F.area L) n N N') (alphaQ c (formV (Formalism.L2.Th1.F.area L) n N N'))
      (powLat ΛM N N'))
    (w : n → Fin N' → Fin N → ℂ) (b : Fin N' × Fin N) (t t' : n → ℂ) :
    F (upd w b t) * θ t' = θ t * F (upd w b t') := by
  obtain ⟨a, ha⟩ := hyp _ (slice_th c L ΛM F hF w b)
  have e1 := congrFun ha t
  have e2 := congrFun ha t'
  simp only [Pi.smul_apply, smul_eq_mul] at e1 e2
  rw [e1, e2]
  ring
end PI.KerTens.W
