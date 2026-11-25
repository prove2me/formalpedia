-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.mapC_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:15:49.386796+00:00
-- url     : https://prove2.me/submissions/3e802bb0-5b37-408a-a3c4-e0522bfac891

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.solution {g : ℕ} (U : (Matrix (Fin g) (Fin g) ℤ)ˣ) :
    ((U⁻¹ : (Matrix (Fin g) (Fin g) ℤ)ˣ) : Matrix (Fin g) (Fin g) ℤ).map (fun x : ℤ => (x : ℂ)) *
      (U : Matrix (Fin g) (Fin g) ℤ).map (fun x : ℤ => (x : ℂ)) = 1 := by
  have h : (((U⁻¹ : (Matrix (Fin g) (Fin g) ℤ)ˣ) : Matrix (Fin g) (Fin g) ℤ) *
      (U : Matrix (Fin g) (Fin g) ℤ)).map (Int.castRingHom ℂ) = 1 := by
    rw [Units.inv_mul]
    simp
  exact (Matrix.map_mul (f := Int.castRingHom ℂ)).symm.trans h
end ReciprocityTheory.ChartRestriction.G.Key.Chi
