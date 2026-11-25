-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.sImage_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:54:07.248785+00:00
-- url     : https://prove2.me/submissions/34bcf30d-a898-4da3-a392-82655eb18b4c

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgebraicIndependentOfDerivations
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsDualDerivations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
open MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
theorem _root_.solution {Ω : Type} [Field Ω] {D m : ℕ} (x : Fin m → Ω) (p : Fin (D + 1) × Fin (m + 1)) :
    sImage (D := D) x p =
      algebraMap (MvPolynomial (SVars D m) Ω) (SField Ω D m) (gFam x (eIdx D m p)) := by
  rcases p with ⟨i, j⟩
  induction j using Fin.cases <;> induction i using Fin.cases <;>
    simp [ReciprocityTheory.MultiplicativeHeights.sImage, eIdx, gFam, yPoly]
end ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
