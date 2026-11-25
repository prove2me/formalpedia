-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GRPf.cc_cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:31:43.312657+00:00
-- url     : https://prove2.me/submissions/0c03602b-76cf-49be-9be6-f98283a789fd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeRatio

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
open MvPowerSeries
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.GRPf
variable {O k : Type} [CommRing O] [StarRing O] [CommRing k] [Algebra ℚ k]
variable {T : Type} (χ : T → O →+* k) (cc : T → T) (hcc : ∀ σ a, χ (cc σ) a = χ σ (star a))
  (hunit : ∀ σ τ, σ ≠ τ → ∃ a, IsUnit (χ σ a - χ τ a))
include hunit
include hcc
namespace ReciprocityTheory.ChartRestriction.G.TB.GRPf
theorem _root_.solution {c : k} (hc : c ≠ 0) (σ : T) : cc (cc σ) = σ := by
  by_contra hne
  obtain ⟨a, ha⟩ := hunit _ _ hne
  rw [hcc, hcc, star_star, sub_self] at ha
  have h01 := isUnit_zero_iff.1 ha
  apply hc
  calc c = c * 1 := (mul_one c).symm
    _ = c * 0 := by rw [h01]
    _ = 0 := mul_zero c
end ReciprocityTheory.ChartRestriction.G.TB.GRPf
