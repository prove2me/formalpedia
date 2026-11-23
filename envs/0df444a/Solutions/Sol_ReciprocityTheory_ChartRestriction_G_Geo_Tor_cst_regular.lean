-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst_regular
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:55.704561+00:00
-- url     : https://prove2.me/submissions/c3b29117-8ccc-419c-a284-737ee7e764cd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
theorem _root_.solution [IsDomain V] (p : X ⟶ Sp V) [Flat p] (x : X) {a : V} (ha : a ≠ 0) : IsLeftRegular (cst p x a) := by
  have hU : IsAffineOpen (⊤ : (Sp V).Opens) := isAffineOpen_top _
  let y : (⊤ : (Sp V).Opens) := ⟨p x, trivial⟩
  haveI := hU.isLocalization_stalk y
  letI : Algebra Γ(Sp V, ⊤) ((Sp V).presheaf.stalk (p x)) :=
    TopCat.Presheaf.algebra_section_stalk (Sp V).presheaf y
  have hloc : Module.Flat Γ(Sp V, ⊤) ((Sp V).presheaf.stalk (p x)) :=
    IsLocalization.flat _ (hU.primeIdealOf y).asIdeal.primeCompl
  have hg : ((Sp V).presheaf.germ ⊤ (p x) trivial).hom.Flat :=
    RingHom.flat_algebraMap_iff.mpr hloc
  have hi : (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom.Flat :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).inv)
  let φ : V →+* X.presheaf.stalk x :=
    (p.stalkMap x).hom.comp (((Sp V).presheaf.germ ⊤ (p x) trivial).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)
  have hφ : φ.Flat := (hi.comp hg).comp (Flat.stalkMap p x)
  have hφe : ∀ b, φ b = cst p x b := by
    intro b
    change (p.stalkMap x).hom (((Sp V).presheaf.germ ⊤ (p x) trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b)) =
      gs p x ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b)
    unfold gs
    rw [dif_pos (show p x ∈ (⊤ : (Sp V).Opens) from trivial)]
    exact Scheme.Hom.germ_stalkMap_apply p ⊤ x trivial _
  letI : Algebra V (X.presheaf.stalk x) := φ.toAlgebra
  haveI : Module.Flat V (X.presheaf.stalk x) := hφ
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := X.presheaf.stalk x)
    (mem_nonZeroDivisors_of_ne_zero ha)
  intro s s' hss
  apply hreg
  simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, hφe]
  exact hss
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
