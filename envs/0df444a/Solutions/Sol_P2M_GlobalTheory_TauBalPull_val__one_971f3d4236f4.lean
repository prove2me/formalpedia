-- Prove2me | solution 1 for P2M_GlobalTheory_TauBalPull_val__one_971f3d4236f4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:39:56.288425+00:00
-- url     : https://prove2.me/submissions/4b1da1ee-d2d6-4a6f-9491-713b09fc3bfe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBalOfIsPullDeg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.TauBalPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TauPull
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}
namespace GlobalTheory.TauBalPull
theorem _root_.solution {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {K : Type} [Fintype K]
    {ψ : K → ((A ⊗ A).left ⟶ A.left)} {ε : K → ℤ} (u : LB.Gen (LB.LinComb L ψ ε))
    (h₀ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (lift η[A] η[A]).left) (LB.oneGen L))
    {T : Over S} {z : T.left} {J} (hJ : Good L z J) : val u (lift (1 : T ⟶ A) (1 : T ⟶ A)).left z J = 1 := by
  have e : lift (1 : T ⟶ A) (1 : T ⟶ A) = toUnit T ≫ lift η[A] η[A] := by rw [comp_lift]; rfl
  have := val_corr hJ h₀ (toUnit T).left
  rw [val_pull hJ, val_one] at this
  rw [e]; exact this
end GlobalTheory.TauBalPull
