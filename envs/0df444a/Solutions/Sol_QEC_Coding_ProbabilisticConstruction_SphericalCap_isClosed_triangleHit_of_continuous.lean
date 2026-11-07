-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.isClosed_triangleHit_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:45:35.848688+00:00
-- url     : https://prove2.me/submissions/4b356516-bab4-4759-81af-04e88bfe1d2e

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_JointTriangleHit
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_barycenterMap_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_triangleHit_iff_weights
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.barycenterMap_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped BigOperators
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution {Y : Type*} [TopologicalSpace Y]
    (r p : Y → Fin 3 → Space) (z : Y → Space) (ρ : Y → ℝ)
    (hr : Continuous r) (hp : Continuous p) (hz : Continuous z) (hρ : Continuous ρ) :
    IsClosed {y | p y ∈ triangleHit (r y) (z y) (ρ y)} := by
  let E : Set (Y × stdSimplex ℝ (Fin 3)) :=
    {yw | dist (∑ j, (yw.2 : Fin 3 → ℝ) j • (r yw.1 j+p yw.1 j))
      (z yw.1) ≤ ρ yw.1}
  have hw (j : Fin 3) : Continuous
      (fun yw : Y × stdSimplex ℝ (Fin 3) => (yw.2 : Fin 3 → ℝ) j) :=
    (continuous_apply j).comp (continuous_subtype_val.comp continuous_snd)
  have hv (j : Fin 3) : Continuous
      (fun yw : Y × stdSimplex ℝ (Fin 3) => r yw.1 j+p yw.1 j) :=
    (((continuous_apply j).comp hr).comp continuous_fst).add
      (((continuous_apply j).comp hp).comp continuous_fst)
  have hs : Continuous (fun yw : Y × stdSimplex ℝ (Fin 3) =>
      ∑ j, (yw.2 : Fin 3 → ℝ) j • (r yw.1 j+p yw.1 j)) :=
    continuous_finset_sum _ fun j _ => (hw j).smul (hv j)
  have hc : IsClosed E :=
    isClosed_le (hs.dist (hz.comp continuous_fst)) (hρ.comp continuous_fst)
  have he : {y | p y ∈ triangleHit (r y) (z y) (ρ y)} = Prod.fst '' E := by
    ext y
    simp only [Set.mem_setOf_eq, triangleHit_iff_weights, Set.mem_image, Prod.exists]
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨y,w,hw,rfl⟩
    · rintro ⟨y',w,hw,he⟩
      subst y'
      exact ⟨w,hw⟩
  rw [he]
  exact isClosedMap_fst_of_compactSpace _ hc
end QEC.Coding.ProbabilisticConstruction.SphericalCap
