-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.divZ_of_rcp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:48:35.929923+00:00
-- url     : https://prove2.me/submissions/ce43886b-aa9c-4e37-80d3-234367ad134b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivA
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_divZ_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution {T : Fm n →ₗ[ℂ] Fm n} (hT : RCP T) {i : ℕ} {Q : Fm n} (hQ : DivZ i Q) : DivZ i (T Q) := by
  obtain ⟨R, rfl⟩ := (divZ_iff i Q).1 hQ
  exact (divZ_iff i _).2 ⟨T R, hT R _⟩
end PositivityTheory.Rg.Sw.SP
