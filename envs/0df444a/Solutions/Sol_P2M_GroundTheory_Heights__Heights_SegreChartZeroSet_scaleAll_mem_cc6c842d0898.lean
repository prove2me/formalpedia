-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SegreChartZeroSet_scaleAll_mem_cc6c842d0898
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:40:57.166355+00:00
-- url     : https://prove2.me/submissions/fddc4eda-c946-4ff8-b1ba-2af10bc2faf7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartZeroSet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartZeroSet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_scaleBlock_mem_zeroLocus


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre scaleBlock scaleBlock_mem_zeroLocus)
open ComplexSets
open GroundTheory.Heights₂.Heights.SegreChartZeroSet
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.SegreChartZeroSet
theorem _root_.solution (P : Ideal (MRing ι)) (hP : IsMultiHomogIdeal P) (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : (fun p => c p.1 * z p) ∈ mcPts P := by
  have key : ∀ s : Finset K,
      (fun p : Σ k, ι k => (if p.1 ∈ s then c p.1 else 1) * z p) ∈ mcPts P := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hz
    | insert k s hk ih =>
      have h := scaleBlock_mem_zeroLocus P hP k (hc k) ih
      convert h using 1
      funext p
      simp only [scaleBlock, Finset.mem_insert]
      by_cases hpk : p.1 = k
      · subst hpk
        simp [hk]
      · simp [hpk]
  simpa using key Finset.univ
end GroundTheory.Heights₂.Heights.SegreChartZeroSet
