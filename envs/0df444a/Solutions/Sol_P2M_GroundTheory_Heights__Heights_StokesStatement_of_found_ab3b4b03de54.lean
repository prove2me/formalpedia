-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StokesStatement_of_found_ab3b4b03de54
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:10:46.644454+00:00
-- url     : https://prove2.me/submissions/4a302cb1-d3d3-403b-8127-20cfe381ed57

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsBilinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegrePartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_Stokes
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsDegZeroSmooth_mul_ac2f2d59f4e1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isDegZeroSmooth_log_6908ea6c59be


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar ptsIntegral pot segre)
namespace GroundTheory.Heights₂.Heights
namespace StokesStatement
theorem _root_.solution (hBil : PtsBilinear.Statement) (hPart : SegrePartition.Statement)
    (hChart : SegreChart.Statement) (hSV : StokesOnVariety.Statement) :
    ReciprocityTheory.ChartRestriction.G.Geo.StokesStatement := by
  classical
  intro K _ ι _ P n L B B' hP hL hB hB' hB0 hB'0
  have hw := isDegZeroSmooth_log hB hB0
  have hw' := isDegZeroSmooth_log hB' hB'0
  have hne : ∀ k, Nonempty (ι k) := fun k => by
    obtain ⟨i, -⟩ := hP.2.1.2.2 k
    exact ⟨i⟩
  obtain ⟨δ, hδ, ρ, hρs, hρ1, hρ0⟩ := hPart K ι hne

  have hpiece : ∀ i, IsDegZeroSmooth (fun z => ρ i z * Real.log (B.h z)) := fun i => (hρs i).mul hw

  have key : ∀ i, ptsIntegral P (Fin.cons (fun z => Real.log (B'.h z)) (pot L))
        (fun z => ρ i z * Real.log (B.h z)) =
      ptsIntegral P (Fin.cons (fun z => ρ i z * Real.log (B.h z)) (pot L))
        (fun z => Real.log (B'.h z)) := by
    intro i
    obtain ⟨m, Js, U, V, Φ, hJ, hU, h1, h2⟩ := hChart K ι P n L (fun z => ρ i z * Real.log (B.h z))
      (fun z => Real.log (B'.h z)) i δ hP hL (hpiece i) hw' hδ
      (fun z hz => by simp only [hρ0 i z hz, zero_mul])
    rw [h1, h2]
    refine Finset.sum_congr rfl fun J hJs => ?_
    obtain ⟨hJp, hJd, hUs, hVs, hΦs⟩ := hJ J hJs
    exact hSV m n J U V Φ hJp hJd hUs hVs hΦs (Or.inl hU)
  have hsum : (fun z => Real.log (B.h z)) = fun z => ∑ i, ρ i z * Real.log (B.h z) := by
    funext z
    rw [← Finset.sum_mul, hρ1 z, one_mul]
  obtain ⟨hA, hC⟩ := hBil K ι P n L _ (fun i z => ρ i z * Real.log (B.h z))
    (fun z => Real.log (B'.h z)) hP hL hpiece hw'
  calc ptsIntegral P (Fin.cons (fun z => Real.log (B'.h z)) (pot L)) (fun z => Real.log (B.h z))
      = ptsIntegral P (Fin.cons (fun z => Real.log (B'.h z)) (pot L))
          (fun z => ∑ i, ρ i z * Real.log (B.h z)) := by rw [← hsum]
    _ = ∑ i, ptsIntegral P (Fin.cons (fun z => Real.log (B'.h z)) (pot L))
          (fun z => ρ i z * Real.log (B.h z)) := hA
    _ = ∑ i, ptsIntegral P (Fin.cons (fun z => ρ i z * Real.log (B.h z)) (pot L))
          (fun z => Real.log (B'.h z)) := Finset.sum_congr rfl fun i _ => key i
    _ = ptsIntegral P (Fin.cons (fun z => ∑ i, ρ i z * Real.log (B.h z)) (pot L))
          (fun z => Real.log (B'.h z)) := hC.symm
    _ = ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot L))
          (fun z => Real.log (B'.h z)) := by rw [← hsum]
end StokesStatement
end GroundTheory.Heights₂.Heights
