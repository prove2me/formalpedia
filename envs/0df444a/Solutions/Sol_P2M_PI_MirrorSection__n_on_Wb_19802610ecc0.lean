-- Prove2me | solution 1 for P2M_PI_MirrorSection__n_on_Wb_19802610ecc0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:45:10.837607+00:00
-- url     : https://prove2.me/submissions/d58dac14-6b7b-4666-9104-da055a46fe5f

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_HpkRowEsI

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
theorem _root_.solution {n : B.Mat k r} (hn : n ∈ Nset k r) {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) :
    n *ᵥ u - u ∈ lowS k r r := by
  intro i hi
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
  have hterm : ∀ l : Fin (2 * r + k + 1), n i l * u l = if i = l then u l else 0 := by
    intro l
    by_cases hl : l.val < r ∨ r + k < l.val
    · rw [hu l hl]
      simp
    · push Not at hl
      rw [hn.2.2 i l hl.1 hl.2 hi]
      by_cases hil : i = l <;> simp [hil]
  rw [Finset.sum_congr rfl (fun l _ => hterm l)]
  simp
end PI.MirrorSection₂
