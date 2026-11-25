-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.AffPres.le_bdIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:56:16.830494+00:00
-- url     : https://prove2.me/submissions/d95a129b-ad12-4eb9-a955-587c221d0b05

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsBasicOpenCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace IrreducibleComponentPreimages
noncomputable section
variable {W : Scheme.{0}}
variable {s : W ⟶ Spec (.of ℂ)}
namespace ReciprocityTheory.AnForm.R
namespace AffPres
theorem _root_.solution (P : AffPres s) (Z : W.IdealSheafData) : P.K ≤ P.bdIdeal Z := by
  intro g hg
  show P.secHom g ∈ Z.ideal P.affOpen
  have h0 : P.secHom g = 0 := by
    simp only [AffPres.secHom, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hg, map_zero]
  rw [h0]
  exact zero_mem _
end AffPres
end ReciprocityTheory.AnForm.R
