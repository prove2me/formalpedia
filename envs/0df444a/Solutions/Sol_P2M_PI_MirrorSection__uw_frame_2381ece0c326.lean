-- Prove2me | solution 1 for P2M_PI_MirrorSection__uw_frame_2381ece0c326
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:44:52.670676+00:00
-- url     : https://prove2.me/submissions/40786804-4a4a-4f32-a4e2-53ff8fea28fd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_HpkRowEsI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_IsMonomialConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_Forward
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_MirrorDecompOf
import Theorems.Thm_PI_StabPairsW_mul_of_col


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
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW
variable {k r : ℕ}
namespace PI.MirrorSection₂
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z) :
    h * Ff k r z = Ff k r z := by
  have hfix : ∀ b, h *ᵥ fvec k r z b = fvec k r z b := by
    intro b
    unfold fvec
    split_ifs with ha
    · exact (hh.2.1 ⟨b.val, ha⟩).1
    · exact hh.2.2
  have := mul_of_col z h 1 (fun b => by
    rw [hfix b]
    simp [Matrix.one_apply])
  rwa [Matrix.mul_one] at this
end PI.MirrorSection₂
