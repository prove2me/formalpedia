-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.Mi.opE_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:48:54.640543+00:00
-- url     : https://prove2.me/submissions/b0f563da-91e1-4b73-87bd-59bd4b986949

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCoreA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP PositivityTheory.Rg.Sw.SP.Mi
variable {R : Type} [CommRing R]
namespace PositivityTheory.Rg.Sw.SP.Mi
theorem _root_.solution (α r : R) {ρ : ℕ} (p q : Fin ρ) (f : Pm R ρ) : opE α p q (C r * f) = C r * opE α p q f := by
  have h0 : del p q (C r : Pm R ρ) = 0 := by
    rw [← algebraMap_eq]; exact (del p q).map_algebraMap r
  change C α * X (q, p) * (C r * f) + del p q (C r * f) = C r * (C α * X (q, p) * f + del p q f)
  rw [Derivation.leibniz, h0, smul_zero, add_zero, smul_eq_mul]
  ring
end PositivityTheory.Rg.Sw.SP.Mi
