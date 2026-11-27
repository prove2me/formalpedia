-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.cub_at_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:39:41.001962+00:00
-- url     : https://prove2.me/submissions/c56d5b87-d3be-4f5f-9bb9-4586c2603241

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExtVCat
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_eSec_th__1cd1bf797aec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_eSec_face
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of
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
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {L : RigLB G} (c : CubicalStr G L) (z : (𝟙_ (Over S)).left) (q₀ : L.L.ι)
    (hq₀ : eSec G z ∈ L.L.U q₀) :
    gm (eSec (G3 G)) z (LB.wchart L.L (thφ G (x3 G)) (fun _ => q₀)) (c.t.s (fun _ => q₀)) = 1 := by
  classical
  let J : ((𝟙_ (Over S)).left ⟶ G.left) → L.L.ι := fun χ =>
    if χ = eSec G then q₀ else (exists_chart L.isLB (χ z)).choose
  have hJ : Good L.L z J := fun χ => by
    by_cases h : χ = eSec G
    · subst h; simp only [J, if_pos rfl]; exact hq₀
    · simp only [J, if_neg h]; exact (exists_chart L.isLB (χ z)).choose_spec
  have hv := val_corr hJ (c.face 0) (eSec (G2 G))
  have hv2 : val (φ := thφ G (x3 G)) (ε := thε) c.t (eSec (G2 G) ≫ (faceMap G 0).left) z J = 1 :=
    (val_pull hJ (φ := thφ G (x3 G)) (ε := thε) c.t (faceMap G 0).left (eSec (G2 G))).symm.trans
      (hv.trans (val_one _))
  have hm : ∀ I, J ((eSec (G2 G) ≫ (faceMap G 0).left) ≫ thφ G (x3 G) I) = q₀ := fun I => by
    rw [eSec_face, eSec_thφ]; simp [J]
  rw [val_of (φ := thφ G (x3 G)) (ε := thε) c.t _ z J (fun _ => q₀) hm, eSec_face] at hv2
  exact hv2
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
