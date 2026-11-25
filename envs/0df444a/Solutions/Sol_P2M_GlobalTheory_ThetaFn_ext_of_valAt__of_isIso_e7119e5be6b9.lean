-- Prove2me | solution 1 for P2M_GlobalTheory_ThetaFn_ext_of_valAt__of_isIso_e7119e5be6b9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:34:28.823965+00:00
-- url     : https://prove2.me/submissions/4f2308a8-4e84-4e91-ac02-3cd20acb03a3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter
variable {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X)
namespace GlobalTheory.ThetaFn
theorem _root_.solution [IsIso x] {U : X.Opens} {f f' : Γ(X, U)}
    (h : ⊤ ≤ x ⁻¹ᵁ U → valAt' x U f = valAt' x U f') : f = f' := by
  by_cases hU : ⊤ ≤ x ⁻¹ᵁ U
  · have h1 := h hU
    rw [valAt', valAt', dif_pos hU, dif_pos hU] at h1
    have h2 := (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).1 h1
    have hinj : Function.Injective (x.appLE U ⊤ hU).hom := by
      rw [Scheme.Hom.appLE_congr x hU rfl (top_unique hU).symm
        (fun φ => Function.Injective φ.hom), Scheme.Hom.appLE_eq_app]
      exact (ConcreteCategory.bijective_of_isIso (x.app U)).1
    exact hinj h2
  · have hb : U = ⊥ := by
      refine bot_unique fun y hy => hU ?_
      obtain ⟨q, rfl⟩ := x.surjective y
      intro q' _
      obtain rfl : q' = q := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
      exact hy
    subst hb
    exact Subsingleton.elim _ _
end GlobalTheory.ThetaFn
