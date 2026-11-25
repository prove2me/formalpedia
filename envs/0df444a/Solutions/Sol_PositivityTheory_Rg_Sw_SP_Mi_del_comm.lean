-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.Mi.del_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:50:58.690351+00:00
-- url     : https://prove2.me/submissions/be7a40a8-5235-4b83-a0e4-f54b18ba1c7f

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
theorem _root_.solution {R : Type} [CommRing R] {ρ : ℕ} (p q p' q' : Fin ρ) (g : Pm R ρ) :
    del p q (del p' q' g) = del p' q' (del p q g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [del]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f ad hf =>
    simp only [Derivation.leibniz, map_add, smul_eq_mul, hf]
    simp only [del, mkDerivation_X, Derivation.leibniz, smul_eq_mul]
    ring
end PositivityTheory.Rg.Sw.SP.Mi
