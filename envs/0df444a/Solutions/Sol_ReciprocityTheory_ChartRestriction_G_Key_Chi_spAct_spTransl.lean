-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.spAct_spTransl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:00.6938+00:00
-- url     : https://prove2.me/submissions/c768d9a7-9cc2-4980-b2d4-3c49b9fe3c5e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_cMat_spTransl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_jAut_spTransl

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
theorem _root_.solution {g : ℕ} (S : Matrix (Fin g) (Fin g) ℤ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    spAct (spTransl S) τ = τ + S.map (fun x : ℤ => (x : ℂ)) := by
  simp [spAct, jAut_spTransl, cMat_spTransl]
end ReciprocityTheory.ChartRestriction.G.Key.Chi
