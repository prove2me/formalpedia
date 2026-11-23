-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.LocalResidues.gs_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:51.410782+00:00
-- url     : https://prove2.me/submissions/465d7b88-f99e-4c13-b229-bf8e474799da

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_JetApproximation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_LocalResidues

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.LocalResidues
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {k : Type} [Field k] {X W Z : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.H1.LocalResidues
theorem _root_.solution {Y' : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) (q : X ⟶ Y') (e : Y' ⟶ Spec (CommRingCat.of k))
    [IsIso e] (hq : q ≫ e = p) (y : X) (a : Γ(Y', ⊤)) : ∃ c : k, gs q y ⊤ a = kappa p y c := by
  subst hq
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom ((inv (e.app ⊤)).hom a), ?_⟩
  have h1 : (e.app ⊤).hom ((inv (e.app ⊤)).hom a) = a := by
    exact congrArg (fun f => f.hom a) (IsIso.inv_hom_id (e.app ⊤))
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom ((inv (e.app ⊤)).hom a)) = (inv (e.app ⊤)).hom a := by
    exact congrArg (fun f => f.hom ((inv (e.app ⊤)).hom a)) (Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id
  simp only [kappa, gs, RingHom.comp_apply, h2]
  rw [dif_pos (show q y ∈ (⊤ : Y'.Opens) from trivial)]
  first
    | (show _ = (X.presheaf.germ _ y _).hom ((q.app ⊤).hom ((e.app ⊤).hom ((inv (e.app ⊤)).hom a)))
       rw [h1])
    | (simp [Scheme.Hom.comp_app, h1]; done)
    | (erw [Scheme.Hom.comp_app, CommRingCat.hom_comp, RingHom.comp_apply, h1]; rfl)
    | (simp only [Scheme.Hom.comp_app, CommRingCat.hom_comp, RingHom.comp_apply, h1]; clear * -; done)
end ReciprocityTheory.ChartRestriction.G.H1.LocalResidues
