-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_measurableSet_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:48:10.43939+00:00
-- url     : https://prove2.me/submissions/95fbb869-9345-40ec-82ef-89867632a391

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_measurableSet_pts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory Filter Topology
variable {J : Type} [Fintype J] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {O : Set (J → ℂ)} {q : (J → ℂ) → Fin D → ℂ} (hO : IsOpen O)
    (hq : ContinuousOn q O) (P : Ideal (MvPolynomial J ℤ)) {A : Set (Fin D → ℂ)}
    (hA : MeasurableSet A) : MeasurableSet {z | z ∈ O ∧ z ∈ pts P ∧ q z ∈ A} := by
  classical
  have hmeas : Measurable (O.piecewise q (fun _ => (0 : Fin D → ℂ))) :=
    ContinuousOn.measurable_piecewise hq continuousOn_const hO.measurableSet
  have hset : {z | z ∈ O ∧ z ∈ pts P ∧ q z ∈ A} =
      O ∩ pts P ∩ (O.piecewise q (fun _ => (0 : Fin D → ℂ))) ⁻¹' A := by
    ext z
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨h1, h2⟩, ?_⟩
      show O.piecewise q (fun _ => (0 : Fin D → ℂ)) z ∈ A
      rwa [Set.piecewise_eq_of_mem _ _ _ h1]
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, h2, ?_⟩
      have h3' : O.piecewise q (fun _ => (0 : Fin D → ℂ)) z ∈ A := h3
      rwa [Set.piecewise_eq_of_mem _ _ _ h1] at h3'
  rw [hset]
  exact (hO.measurableSet.inter (adens_measurableSet_pts P)).inter (hmeas hA)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
