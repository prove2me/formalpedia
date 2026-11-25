-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPullback_resLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:17:25.981694+00:00
-- url     : https://prove2.me/submissions/a296fec6-92df-4c42-bb05-ca4612b1c4c0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_Affine

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
theorem _root_.solution (sq : IsPullback g q' q b) (V : B.Opens) (V' : B'.Opens)
    (hle : V' ≤ b ⁻¹ᵁ V) (hleG : q' ⁻¹ᵁ V' ≤ g ⁻¹ᵁ (q ⁻¹ᵁ V)) :
    IsPullback (g.resLE (q ⁻¹ᵁ V) (q' ⁻¹ᵁ V') hleG) (q'.resLE V' (q' ⁻¹ᵁ V') le_rfl)
      (q.resLE V (q ⁻¹ᵁ V) le_rfl) (b.resLE V V' hle) := by
  have outer : IsPullback ((q' ⁻¹ᵁ V').ι ≫ g) (q' ∣_ V') q (V'.ι ≫ b) :=
    (isPullback_morphismRestrict q' V').flip.paste_horiz sq
  rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_eq_morphismRestrict]
  refine IsPullback.of_right (h₁₂ := (q ⁻¹ᵁ V).ι) (h₂₂ := V.ι) (v₁₃ := q) ?_ ?_
    (isPullback_morphismRestrict q V).flip
  · rw [Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι]
    exact outer
  · rw [← cancel_mono V.ι]
    simp only [Category.assoc, morphismRestrict_ι, Scheme.Hom.resLE_comp_ι]
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, sq.w, ← Category.assoc,
      ← morphismRestrict_ι, Category.assoc]
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
