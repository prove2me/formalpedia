-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.Mi.del_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:50:55.486154+00:00
-- url     : https://prove2.me/submissions/9c3a1d1e-d223-4917-a962-2bddf9265de5

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCore
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorIter

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP PositivityTheory.Rg.Sw.SP.Mi
variable {R : Type} [CommRing R] {ρ : ℕ}
namespace PositivityTheory.Rg.Sw.SP.Mi
theorem _root_.solution (p q : Fin ρ) (r : R) (g : Pm R ρ) : del p q (C r * g) = C r * del p q g := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, MvPolynomial.derivation_C, mul_zero, add_zero]
end PositivityTheory.Rg.Sw.SP.Mi
