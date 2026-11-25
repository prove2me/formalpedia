-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.Mi.del_CX_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:48:49.193848+00:00
-- url     : https://prove2.me/submissions/6aa18a93-9709-4a69-a822-3871f00027bf

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorB

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
namespace PositivityTheory.Rg.Sw.SP.Mi
theorem _root_.solution {R : Type} [CommRing R] {ρ : ℕ} (p q : Fin ρ) (α : R) (a b : Fin ρ) (g : Pm R ρ) :
    del p q (C α * X (a, b) * g) = C α * (X (a, p) * X (q, b)) * g + C α * X (a, b) * del p q g := by
  rw [Derivation.leibniz, Derivation.leibniz, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    MvPolynomial.derivation_C, del, mkDerivation_X]
  ring
end PositivityTheory.Rg.Sw.SP.Mi
