-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftUnpacking.exists_zero_qk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:54:10.673315+00:00
-- url     : https://prove2.me/submissions/4db905f6-00c8-4729-a8ec-79f27dc9adba

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_CanonicalLiftUnpacking
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tau_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cPoint_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_zero_gt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isAdd_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isIota_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isZero_iff


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftUnpacking
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftUnpacking
theorem _root_.solution (hB : D.TauBimult) (k : ℕ) :
    ∃ p0 : QkPt D F k, p0.y = 0 ∧ p0.g.IsZero ∧ p0.g.IsAdd p0.g p0.g := by
  obtain ⟨g, hg⟩ := exists_zero_gt (D := D) (F := F)
  have hz := (isZero_iff g).1 hg
  have hadd : g.IsAdd g g := by
    rw [isAdd_iff]
    refine ⟨by rw [hz.1, _root_.mul_one], fun χ y J hJ => ?_⟩
    have hc := isCub_cubV (c := D.cub) hJ
    rw [hz.2 χ y J hJ, hz.1, _root_.one_mul, _root_.one_mul]
    exact (hc.s01 _ _ _).trans (hc.face _ _)
  have hiota : GtPtF.IsIota (0 : D.X) g := by
    rw [isIota_iff]
    refine ⟨by rw [hz.1, cPoint_zero], fun χ y J hJ => ?_⟩
    have hc := isCub_cubV (c := D.cub) hJ
    have h1 := tau_mul (σ := 𝟙 (TF (R := R) F)) (z := y) (J := J) hJ hB 0 0 χ
    simp only [th, add_zero, cPoint_zero, hc.face, _root_.mul_one, Over.id_left] at h1
    rw [add_zero] at h1
    rw [hz.2 χ y J hJ]
    exact (mul_left_cancel (h1.symm.trans (_root_.mul_one _).symm)).symm
  exact ⟨⟨0, g, ⟨g, ⟨fun _ => g, hg, fun _ => hadd, rfl⟩, hiota⟩⟩, rfl, hg, hadd⟩
end ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftUnpacking
