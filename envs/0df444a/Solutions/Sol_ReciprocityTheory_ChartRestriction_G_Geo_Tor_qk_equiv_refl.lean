-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.qk_equiv_refl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:43:02.140796+00:00
-- url     : https://prove2.me/submissions/6403efae-668d-4179-8c60-3bbbbc0d1c6c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cPoint_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isAdd_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isZero_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isIota_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_zero_gt
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__944b82dcaa95
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tau_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV


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
theorem _root_.solution (hB : D.TauBimult) {k : ℕ} (q : QkPt D F k) : QkPt.Equiv D F q q := by
  obtain ⟨h, hh⟩ := exists_zero_gt (D := D) (F := F)
  obtain ⟨hb, hv⟩ := (isZero_iff h).1 hh
  refine ⟨0, by simp, h, (isIota_iff 0 h).2 ⟨hb.trans (cPoint_zero _).symm, fun χ y J hJ => ?_⟩,
    (isAdd_iff _ _ _).2 ⟨by rw [hb, _root_.mul_one], fun χ y J hJ => ?_⟩⟩
  · have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
    have t := tau_mul (𝟙 (TF (R := R) F)) hJ hB 0 0 χ
    rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
    exact (hv χ y J hJ).trans (mul_eq_left.1 t.symm).symm
  · have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
    rw [hv χ y J hJ, hb, C.face₃]
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
