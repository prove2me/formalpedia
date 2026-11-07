-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.isClosed_largeWeightHit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:10:49.587055+00:00
-- url     : https://prove2.me/submissions/b1888816-62b3-4aec-ba85-0423d147e419

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_barycenterMap_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply


attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.barycenterMap_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped BigOperators
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (r : Fin 3 → Space) (z : Space) (ρ : ℝ) (i : Fin 3) :
    IsClosed (largeWeightHit r z ρ i) := by
  let E : Set ((Fin 3 → Space) × stdSimplex ℝ (Fin 3)) :=
    {pw | (1:ℝ)/3 ≤ (pw.2 : Fin 3 → ℝ) i ∧
      dist (∑ j, (pw.2 : Fin 3 → ℝ) j • (r j+pw.1 j)) z ≤ ρ}
  have hwcont (j : Fin 3) : Continuous
      (fun pw : (Fin 3 → Space) × stdSimplex ℝ (Fin 3) => (pw.2 : Fin 3 → ℝ) j) :=
    (continuous_apply j).comp (continuous_subtype_val.comp continuous_snd)
  have hpcont (j : Fin 3) : Continuous
      (fun pw : (Fin 3 → Space) × stdSimplex ℝ (Fin 3) => r j+pw.1 j) :=
    continuous_const.add ((continuous_apply j).comp continuous_fst)
  have hsum : Continuous (fun pw : (Fin 3 → Space) × stdSimplex ℝ (Fin 3) =>
      ∑ j, (pw.2 : Fin 3 → ℝ) j • (r j+pw.1 j)) :=
    continuous_finset_sum _ (fun j _ => (hwcont j).smul (hpcont j))
  have hc : IsClosed E := by
    change IsClosed
      ({pw : (Fin 3 → Space) × stdSimplex ℝ (Fin 3) | (1:ℝ)/3 ≤ (pw.2 : Fin 3 → ℝ) i} ∩
       {pw : (Fin 3 → Space) × stdSimplex ℝ (Fin 3) |
         dist (∑ j, (pw.2 : Fin 3 → ℝ) j • (r j+pw.1 j)) z ≤ ρ})
    exact (isClosed_le continuous_const (hwcont i)).inter
      (isClosed_le (hsum.dist continuous_const) continuous_const)
  have he : largeWeightHit r z ρ i = Prod.fst '' E := by
    ext p
    simp only [largeWeightHit,E,mem_setOf_eq,mem_image,Prod.exists]
    aesop
  rw [he]
  exact isClosedMap_fst_of_compactSpace _ hc
end QEC.Coding.ProbabilisticConstruction.SphericalCap
