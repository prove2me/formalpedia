-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:27:31.396193+00:00
-- url     : https://prove2.me/submissions/f63a9762-b55c-4d36-aadb-5bf88ffc434a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_Affine
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_isPullback_resLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
universe u
variable {G B G' B' : Scheme.{u}} {g : G' ⟶ G} {q' : G' ⟶ B'} {q : G ⟶ B} {b : B' ⟶ B}
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
theorem _root_.solution (sq : IsPullback g q' q b) (hq : IsAffineHom q) {V : B.Opens}
    (hV : IsAffineOpen V) {V' : B'.Opens} (hV' : IsAffineOpen V')
    (hle : V' ≤ b ⁻¹ᵁ V) (hleG : q' ⁻¹ᵁ V' ≤ g ⁻¹ᵁ (q ⁻¹ᵁ V)) :
    IsPushout (q.app V) (b.appLE V V' hle) (g.appLE (q ⁻¹ᵁ V) (q' ⁻¹ᵁ V') hleG) (q'.app V') := by
  have : IsAffine V.toScheme := hV
  have : IsAffine V'.toScheme := hV'
  have : IsAffine (q ⁻¹ᵁ V).toScheme := hV.preimage q
  have P := isPushout_appTop_of_isPullback (isPullback_resLE sq V V' hle hleG)
  rw [← Scheme.Hom.appLE_eq_app, ← Scheme.Hom.appLE_eq_app]
  refine P.of_iso V.topIso (q ⁻¹ᵁ V).topIso V'.topIso (q' ⁻¹ᵁ V').topIso ?_ ?_ ?_ ?_ <;>
    simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
