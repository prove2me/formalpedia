-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeUpperGL_rat_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:41:17.065434+00:00
-- url     : https://prove2.me/submissions/35f3a6ba-175d-4be0-baba-ed3dfa978a5b

import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.ModularForms.NormTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) [Fact p.Prime] (i : Option (Fin p)) :
    (lpsHeckeUpperGL ℚ p i).map (Rat.castHom ℝ)=lpsHeckeUpperGL ℝ p i := by
  apply Units.ext
  ext r c
  simp [Matrix.GeneralLinearGroup.map_apply,lpsHeckeUpperGL,Matrix.map_apply]
end QEC.Coding.TannerLiftedProduct
