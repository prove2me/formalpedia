-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:44.891255+00:00
-- url     : https://prove2.me/submissions/5d69db6c-d76e-4569-a6b3-dbf9507bca72

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cubAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (b : TF (R := R) F ⟶ D.P.A) {K : Type} [Fintype K] {φ : D.X → K → ((TF (R := R) F).left ⟶ D.P.A.left)}
    {ε : K → ℤ} (v : ∀ χ, LB.Gen (LB.LinComb D.P.L (φ χ) ε)) (hv : ∀ χ, (v χ).IsGen)
    (hF : ∀ χ, FormEq (φ χ) ε (DegPre.gtφ D F b χ) DegPre.gtε)
    (h₀ : ∀ y J, Good D.P.L y J → val (v 0) (𝟙 _) y J = 1)
    (hm : ∀ χ χ' y J, Good D.P.L y J → val (v (χ + χ')) (𝟙 _) y J * th D y J (cP D _ χ) (cP D _ χ') b =
      val (v χ) (𝟙 _) y J * val (v χ') (𝟙 _) y J) :
    ∃ g : GtPtF D F, g.b = b ∧ ∀ χ y J, Good D.P.L y J → val (g.s χ) (𝟙 _) y J = val (v χ) (𝟙 _) y J := by
  choose s hs hsv using fun χ => exists_gen D.P.isLB (hF χ) (v χ) (hv χ)
  refine ⟨{ b := b, s := s, isGen := hs, s_zero := ?_, mult := ?_ }, rfl, ?_⟩
  · refine corr_of_val D.P.isLB (fun y J hy => ?_)
    refine (hsv 0 _ (𝟙 _) y J hy).trans ?_
    exact (h₀ y J hy).trans (val_one _).symm
  · intro χ χ'
    refine corr_of_val D.P.isLB (fun y J hy => ?_)
    refine (val_mul (hJ := hy) ..).trans ?_
    refine Eq.trans ?_ (val_mul (hJ := hy) ..).symm
    rw [val_cubAt hy, hsv (χ + χ') _ (𝟙 _) y J hy, hsv χ _ (𝟙 _) y J hy, hsv χ' _ (𝟙 _) y J hy]
    exact hm χ χ' y J hy
  · intro χ y J hy
    exact hsv χ _ (𝟙 _) y J hy
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
