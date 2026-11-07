-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.measurableSet_triangleHit_of_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:52:19.660096+00:00
-- url     : https://prove2.me/submissions/4526d81e-69ad-4dff-af2d-22a98b18b6c9

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_JointTriangleHit
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_isClosed_jointTriangleHit

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped BigOperators
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution {Y : Type*} [MeasurableSpace Y]
    (r p : Y → Fin 3 → Space) (z : Y → Space) (ρ : Y → ℝ)
    (hr : Measurable r) (hp : Measurable p) (hz : Measurable z) (hρ : Measurable ρ) :
    MeasurableSet {y | p y ∈ triangleHit (r y) (z y) (ρ y)} := by
  let F : Y → TriangleHitData := fun y => (r y,z y,ρ y,p y)
  have htail : Measurable (fun y => (ρ y,p y)) := hρ.prodMk hp
  have hmiddle : Measurable (fun y => (z y,ρ y,p y)) := hz.prodMk htail
  have hF : Measurable F := hr.prodMk hmiddle
  have hclosed : MeasurableSet
      {d : TriangleHitData | d.2.2.2 ∈ triangleHit d.1 d.2.1 d.2.2.1} :=
    isClosed_jointTriangleHit.measurableSet
  have hpull : MeasurableSet
      (F ⁻¹' {d : TriangleHitData | d.2.2.2 ∈ triangleHit d.1 d.2.1 d.2.2.1}) :=
    hclosed.preimage hF
  exact hpull
end QEC.Coding.ProbabilisticConstruction.SphericalCap
