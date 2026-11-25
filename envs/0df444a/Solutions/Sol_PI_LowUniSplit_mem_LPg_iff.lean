-- Prove2me | solution 1 for PI.LowUniSplit.mem_LPg_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:07:43.561131+00:00
-- url     : https://prove2.me/submissions/10b489f3-22c3-472a-9d5b-9caf5b614dc2

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerUnipotentSplit_SecondFactorMemLowerTriangular
import Theorems.Thm_PI_LowUniSplit_conj_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.LowUniSplit
open Formalism.FourierDecayAlt.C2
variable {m : ℕ}
namespace PI.LowUniSplit
theorem _root_.solution (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0)
    (l : Matrix (Fin m) (Fin m) ℂ) (hl : l ∈ LTset m) :
    l ∈ LPg (monoP w d) ↔ ∀ i j, w.symm i < w.symm j → l i j = 0 := by
  constructor
  · rintro ⟨-, h1, -⟩ i j hij
    have := h1 (w.symm i) (w.symm j) hij
    rw [conj_apply w d hd] at this
    simpa [hd] using this
  · intro h
    refine ⟨hl, fun a b hab => ?_, fun a => ?_⟩
    · rw [conj_apply w d hd]
      have := h (w a) (w b) (by simpa using hab)
      simp [this]
    · rw [conj_apply w d hd, hl.2]
      field_simp [hd a]
end PI.LowUniSplit
