-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.dvd_descend
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:11.51329+00:00
-- url     : https://prove2.me/submissions/7a66dfea-466c-491b-822e-b3db3c3143db

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi
variable {V : Type} [CommRing V] {X Z : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (r : Z ⟶ X) [Flat r] (z : Z) {a b : X.presheaf.stalk (r z)}
    (h : (r.stalkMap z).hom a ∣ (r.stalkMap z).hom b) : a ∣ b := by
  letI : Algebra (X.presheaf.stalk (r z)) (Z.presheaf.stalk z) := (r.stalkMap z).hom.toAlgebra
  haveI : Module.Flat (X.presheaf.stalk (r z)) (Z.presheaf.stalk z) := Flat.stalkMap r z
  haveI : IsLocalHom (algebraMap (X.presheaf.stalk (r z)) (Z.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (r.stalkMap z).hom)
  haveI : Module.FaithfullyFlat (X.presheaf.stalk (r z)) (Z.presheaf.stalk z) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [← Ideal.mem_span_singleton] at h ⊢
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := Z.presheaf.stalk z) (Ideal.span {a}),
    Ideal.mem_comap, Ideal.map_span, Set.image_singleton]
  exact h
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
