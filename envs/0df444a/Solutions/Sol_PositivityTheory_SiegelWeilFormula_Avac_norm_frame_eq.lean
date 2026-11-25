-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Avac.norm_frame_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:55:38.454812+00:00
-- url     : https://prove2.me/submissions/ce98d6a7-bfa5-4adc-bbd2-8e8ceca8a5f0

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnitaryFramesPreserveNormSqSumStatement
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_VacuumIwasawa_FrameLin
import Theorems.Thm_GlobalTheory_T_unitary_frames_preserve_norm_sq_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Avac
variable {m : ℕ}
namespace PositivityTheory.SiegelWeilFormula.Avac
theorem _root_.solution (hm : 1 ≤ m) (J : Matrix (Fin m) (Fin m) ℂ) (fr fr' : GL (Fin m) ℂ) (ζ ζ' : ℂ) (s s' : ℤˣ)
    (hζ : ζ = 1 ∨ ζ = Complex.I) (hζ' : ζ' = 1 ∨ ζ' = Complex.I)
    (h : ζ • (fr.1ᵀ * J * fr.1.map star) = ((s : ℤ) : ℂ) • 1) (h' : ζ' • (fr'.1ᵀ * J * fr'.1.map star) = ((s' : ℤ) : ℂ) • 1)
    (v : Fin m → ℂ) : ∑ a, ‖((fr⁻¹).1 *ᵥ v) a‖ ^ 2 = ∑ a, ‖((fr'⁻¹).1 *ᵥ v) a‖ ^ 2 :=
  GlobalTheory.T.unitary_frames_preserve_norm_sq_sum m hm J fr fr' ζ ζ' s s' hζ hζ' h h' v
end PositivityTheory.SiegelWeilFormula.Avac
