-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_preferredCuspCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:14:31.86725+00:00
-- url     : https://prove2.me/submissions/7de9d459-8a62-4cad-acf8-21f65c6df979

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledForgetLevel_cuspSource
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledForgetLevel_sameCuspCoordinate
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspCoordinate_preferred_phase
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspForgetLevel_projection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspRepresentative_orbit


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ))) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledTopology M
    let ρ := lpsOriginalCuspRepresentative M c
    let d := lpsOriginalCuspForgetLevel N M hNM c
    ∃ α : ℂ, α ≠ 0 ∧ ‖α‖ = 1 ∧ ∀ q : ℂ,
      q ∈ (lpsOriginalFilledCuspChart M c).target →
      α * q ^ lpsOriginalCuspLevelDegree N M ρ ∈
        (lpsOriginalFilledCuspChart N d).target ∧
      lpsOriginalFilledForgetLevel N M hNM
        ((lpsOriginalFilledCuspChart M c).symm q) =
        (lpsOriginalFilledCuspChart N d).symm
          (α * q ^ lpsOriginalCuspLevelDegree N M ρ) ∧
      lpsOriginalFilledCuspChart N d
        (lpsOriginalFilledForgetLevel N M hNM
          ((lpsOriginalFilledCuspChart M c).symm q)) =
        α * q ^ lpsOriginalCuspLevelDegree N M ρ := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledTopology M
  let ρ := lpsOriginalCuspRepresentative M c
  let d := lpsOriginalCuspForgetLevel N M hNM c
  let eM := lpsOriginalFilledCuspChart M c
  let eN := lpsOriginalFilledCuspChart N d
  have hc : lpsOriginalCuspOrbit N ρ = d := by
    rw [← lpsOriginalCuspForgetLevel_projection N M hNM ρ]
    rw [lpsOriginalCuspRepresentative_orbit]
  obtain ⟨α,hα,hαnorm,hphase⟩ := lpsOriginalFilledCuspCoordinate_preferred_phase N ρ
  rw [hc] at hphase
  refine ⟨α,hα,hαnorm,?_⟩
  intro q hq
  have hx : eM.symm q ∈ (lpsOriginalFilledCuspPartialEquiv M ρ).source :=
    eM.map_target hq
  have hy := lpsOriginalFilledForgetLevel_cuspSource N M hNM ρ (eM.symm q) hx
  obtain ⟨hs,hcoord⟩ := hphase (lpsOriginalFilledForgetLevel N M hNM (eM.symm q)) hy
  have hqcoord : eN (lpsOriginalFilledForgetLevel N M hNM (eM.symm q)) =
      α * q ^ lpsOriginalCuspLevelDegree N M ρ := by
    rw [hcoord,lpsOriginalFilledForgetLevel_sameCuspCoordinate N M hNM ρ (eM.symm q) hx]
    change α * (eM (eM.symm q)) ^ lpsOriginalCuspLevelDegree N M ρ =
      α * q ^ lpsOriginalCuspLevelDegree N M ρ
    rw [eM.right_inv hq]
  refine ⟨?_,?_,hqcoord⟩
  · rw [← hqcoord]
    exact eN.map_source hs
  · rw [← hqcoord]
    exact (eN.left_inv hs).symm
end QEC.Coding.TannerLiftedProduct
