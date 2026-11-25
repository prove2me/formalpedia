-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.specMap_constSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:12:25.175632+00:00
-- url     : https://prove2.me/submissions/6f3e85f4-e956-4a9d-8b56-9875f96fc43b

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {S : Scheme.{0}} (s : S ⟶ Spec (.of ℂ)) (U : S.affineOpens) :
    Spec.map (CommRingCat.ofHom (constSec s U.1)) = U.2.fromSpec ≫ s := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top (Spec (.of ℂ))) U.2 le_top
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [← h, ← Spec.map_comp]
  rfl
end ReciprocityTheory.AnForm.R
