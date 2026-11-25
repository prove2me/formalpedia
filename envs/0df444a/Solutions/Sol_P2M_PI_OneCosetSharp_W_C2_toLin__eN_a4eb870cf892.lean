-- Prove2me | solution 1 for P2M_PI_OneCosetSharp_W_C2_toLin__eN_a4eb870cf892
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:45:02.797297+00:00
-- url     : https://prove2.me/submissions/f0606c8a-8bd0-47b3-9409-ba6341177efa

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_EntryEmbedMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W PI.OneCosetSharp.W.C2
open Loc LocE
variable {k : Type} [Field k]
namespace PI.OneCosetSharp.W.C2
theorem _root_.solution {A B : ℕ} (X : Matrix (Fin B) (Fin A) k) (i : ℕ) (hi : i < A) :
    Matrix.toLin' X (eN k A i) = fun l => X l ⟨i, hi⟩ := by
  funext l
  rw [Matrix.toLin'_apply]
  show ∑ j, X l j * PI.OneCosetSharp.Loc.eN k A i j = X l ⟨i, hi⟩
  rw [Finset.sum_eq_single ⟨i, hi⟩]
  · simp [PI.OneCosetSharp.Loc.eN]
  · intro b _ hb
    have hb' : (b : ℕ) ≠ i := fun h => hb (Fin.ext h)
    simp [PI.OneCosetSharp.Loc.eN, hb']
  · intro h
    exact absurd (Finset.mem_univ _) h
end PI.OneCosetSharp.W.C2
