-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_avoid_bb0cc9dacafe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:08:24.418122+00:00
-- url     : https://prove2.me/submissions/3bfecea9-a5ce-402c-93ea-0920b381ec71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PClosedPointUnitSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_coord_mem_e0cbe1c6e1f6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_chartLat_mul_mem_accbe6f6e583
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_max_317237edee38
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_IsUnitAt_mul_5d9adfcd55aa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_not_isUnitAt_mul_260a18dd0eb1

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
open ReciprocityTheory.ChartRestriction.G.Geo NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')
variable [NumberField K']
namespace GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
theorem _root_.solution (hy : IsArithVar (mCoordIdeal y) 1) (P : HeightOneSpectrum (𝓞 K'))
    (S : Finset (HeightOneSpectrum (𝓞 K')))
    (hS : ∀ P' ∈ S, ∃ (k : ℕ) (h : K'), h ∈ chartLat y 1 k ∧ IsUnitAt y P k h ∧ ¬IsUnitAt y P' k h) :
    ∃ (k : ℕ) (z : K'), 1 ≤ k ∧ z ∈ chartLat y 1 k ∧ IsUnitAt y P k z ∧
      ∀ P' ∈ S, ¬IsUnitAt y P' k z := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    obtain ⟨t, -, ht⟩ := exists_max y hy P
    exact ⟨1, _, le_rfl, coord_mem y t, fun u => by simpa using ht u, by simp⟩
  | @insert P'' S hP'' ih =>
    obtain ⟨k, z, hk, hz, hzP, hzS⟩ := ih (fun P' hP' => hS P' (Finset.mem_insert_of_mem hP'))
    obtain ⟨l, h, hh, hhP, hhP''⟩ := hS P'' (Finset.mem_insert_self _ _)
    refine ⟨k + l, z * h, by omega, chartLat_mul_mem y hz hh, hzP.mul y hhP, ?_⟩
    intro P' hP'
    rcases Finset.mem_insert.mp hP' with rfl | hP'
    · have := not_isUnitAt_mul y hy hhP'' hz
      rwa [mul_comm h z, Nat.add_comm l k] at this
    · exact not_isUnitAt_mul y hy (hzS P' hP') hh
end GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
