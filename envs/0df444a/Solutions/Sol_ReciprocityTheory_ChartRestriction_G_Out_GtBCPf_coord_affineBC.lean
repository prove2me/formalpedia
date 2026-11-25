-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.coord_affineBC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:32:38.565676+00:00
-- url     : https://prove2.me/submissions/94ea3f72-e9f5-4514-a17d-d53fbbba3718

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_Affine
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_isPushout_appLE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_bijective_liftNC_of_isPushout

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
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
theorem _root_.solution {G B G' B' : Scheme.{u}} {g : G' ⟶ G} {q' : G' ⟶ B'} {q : G ⟶ B}
    {b : B' ⟶ B}
    (sq : IsPullback g q' q b) (hq : IsAffineHom q) {X : Type u} [AddCommMonoid X]
    {V : B.Opens} (hV : IsAffineOpen V) {V' : B'.Opens} (hV' : IsAffineOpen V')
    (hle : V' ≤ b ⁻¹ᵁ V) (hleG : q' ⁻¹ᵁ V' ≤ g ⁻¹ᵁ (q ⁻¹ᵁ V))
    (φ : Multiplicative X →* Γ(G, q ⁻¹ᵁ V)) (φ' : Multiplicative X →* Γ(G', q' ⁻¹ᵁ V'))
    (hφ' : ∀ x, φ' x = g.appLE (q ⁻¹ᵁ V) (q' ⁻¹ᵁ V') hleG (φ x))
    (hφ : Function.Bijective
      (AddMonoidAlgebra.liftNCRingHom (q.app V).hom φ (fun _ _ => Commute.all _ _))) :
    Function.Bijective
      (AddMonoidAlgebra.liftNCRingHom (q'.app V').hom φ' (fun _ _ => Commute.all _ _)) := bijective_liftNC_of_isPushout (isPushout_appLE sq hq hV hV' hle hleG) φ φ' hφ' hφ
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
