-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbap_isCompact_pts_sphere
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:56:54.773364+00:00
-- url     : https://prove2.me/submissions/293ba863-2166-4dd7-8bf4-aa32f1698761

import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_ExistsAnalyticGraphChartMvPolynomial
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamStB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {Ω : Type} [Field Ω] [CharZero Ω]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {J : Type} [Fintype J] (P : Ideal (MvPolynomial J ℤ)) :
    IsCompact (pts P ∩ Metric.sphere (0 : J → ℂ) 1) := by
  have hZ : IsClosed {z : J → ℂ | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0} := by
    have : {z : J → ℂ | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0} =
        ⋂ f ∈ P, {z : J → ℂ | eval z (map (Int.castRingHom ℂ) f) = 0} := by
      ext z
      simp
    rw [this]
    exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval _) continuous_const
  have : pts P ∩ Metric.sphere (0 : J → ℂ) 1 =
      {z : J → ℂ | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0} ∩ Metric.sphere 0 1 := by
    ext z
    simp only [pts, conePts, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_sphere_zero_iff_norm]
    constructor
    · rintro ⟨⟨_, h⟩, h1⟩
      exact ⟨h, h1⟩
    · rintro ⟨h, h1⟩
      refine ⟨⟨fun h0 => ?_, h⟩, h1⟩
      rw [h0, norm_zero] at h1
      exact zero_ne_one h1
  rw [this]
  exact (isCompact_sphere 0 1).inter_left hZ
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
