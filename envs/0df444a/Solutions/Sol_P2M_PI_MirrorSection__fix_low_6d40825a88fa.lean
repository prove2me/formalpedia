-- Prove2me | solution 1 for P2M_PI_MirrorSection__fix_low_6d40825a88fa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:01:50.976072+00:00
-- url     : https://prove2.me/submissions/ec9241d9-0e09-45a4-a892-cd9568e5580d

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_HpkRowEsI
import Theorems.Thm_P2M_PI_MirrorSection__col_eq_524aef35e814

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
open PI PI.MirrorSection₂
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}
namespace PI.MirrorSection₂
theorem _root_.solution {g : B.Mat k r} (hfix : ∀ b : Fin r, g *ᵥ bvec (eI k r b) = bvec (eI k r b)) {a : ℕ}
    (har : a ≤ r) : ∀ y ∈ lowS k r a, g *ᵥ y = y := by
  intro y hy
  funext i
  simp only [Matrix.mulVec, dotProduct]
  have hterm : ∀ l : Fin (2 * r + k + 1), g i l * y l = if i = l then y l else 0 := by
    intro l
    by_cases hl : a ≤ l.val
    · rw [hy l hl]
      simp
    · have hlr : l.val < r := by omega
      have hle : (eI k r ⟨l.val, hlr⟩) = l := Fin.ext rfl
      have := congrFun (hfix ⟨l.val, hlr⟩) i
      rw [col_eq, hle] at this
      simp only at this
      rw [this]
      by_cases hil : i = l
      · subst hil
        simp [bvec]
      · simp [bvec, Pi.single_apply, hil]
  rw [Finset.sum_congr rfl (fun l _ => hterm l)]
  simp
end PI.MirrorSection₂
