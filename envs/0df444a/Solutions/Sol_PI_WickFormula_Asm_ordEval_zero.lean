-- Prove2me | solution 1 for PI.WickFormula.Asm.ordEval_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:15:44.915283+00:00
-- url     : https://prove2.me/submissions/e856c47b-eaa1-4648-9543-3685dbbce054

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_DeltaEqGdelta
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_XdegLeTotalDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula PI.WickFormula.Asm
variable {k AA M : Type} [CommRing k] [Algebra ℚ k] [Ring AA] [Algebra k AA] [AddCommGroup M]
  [Module AA M] {r s : ℕ}
namespace PI.WickFormula.Asm
theorem _root_.solution (h1 : OrdLin) (a : Fin r → AA) (a' : Fin s → AA) :
    ordEval a a' (0 : MvPolynomial (Fin r ⊕ Fin s) k) = 0 := by
  obtain ⟨f, hf⟩ := h1 k AA r s a a'
  rw [← hf, map_zero]
end PI.WickFormula.Asm
