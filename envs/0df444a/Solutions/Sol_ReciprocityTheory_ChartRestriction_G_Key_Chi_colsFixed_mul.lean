-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.colsFixed_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:42:24.001464+00:00
-- url     : https://prove2.me/submissions/7703e3e4-3dcf-486d-b7b2-274674ca24d4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenCol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.solution {k : ℕ} {O M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hO : ColsFixed k O) (hM : ColsFixed k M) : ColsFixed k (O * M) := by
  intro i hi
  refine ⟨fun r => ?_, fun r => ?_⟩
  · have e : (O * M) r (Sum.inl i) = (O * (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)) r (Sum.inl i) := by
      simp only [Matrix.mul_apply, (hM i hi).1]
    rw [e, Matrix.mul_one, (hO i hi).1]
  · have e : (O * M) r (Sum.inr i) = (O * (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)) r (Sum.inr i) := by
      simp only [Matrix.mul_apply, (hM i hi).2]
    rw [e, Matrix.mul_one, (hO i hi).2]
end ReciprocityTheory.ChartRestriction.G.Key.Chi
