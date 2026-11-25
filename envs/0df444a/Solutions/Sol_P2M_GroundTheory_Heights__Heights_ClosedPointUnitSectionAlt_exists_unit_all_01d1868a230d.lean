-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_unit_all_01d1868a230d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:46:20.174186+00:00
-- url     : https://prove2.me/submissions/bc7dcccd-dc13-4a05-b130-72e4202ac17e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PClosedPointUnitSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_coord_mem_e0cbe1c6e1f6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_chartLat_pow_mem_2f024e5dc2e9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_max_317237edee38
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_IsUnitAt_pow_204d807c4e92
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_not_isUnitAt_pow_66f34090600d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_isUnitAt_add_c542c0248662
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_sep_7bec6285acde
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_avoid_bb0cc9dacafe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveAffineCharts_exists_chart_3dcf866b6f14


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
theorem _root_.solution (hy : IsArithVar (mCoordIdeal y) 1) (S : Finset (HeightOneSpectrum (𝓞 K'))) :
    ∃ (d : ℕ) (G : K'), 1 ≤ d ∧ G ≠ 0 ∧ G ∈ chartLat y 1 d ∧ ∀ P ∈ S, IsUnitAt y P d G := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    obtain ⟨t, ht⟩ := CurveAffineCharts.exists_chart y hy
    exact ⟨1, _, le_rfl, ht, coord_mem y t, by simp⟩
  | @insert P S hP ih =>
    obtain ⟨d, G, hd, hG0, hG, hGS⟩ := ih
    by_cases hu : IsUnitAt y P d G
    · refine ⟨d, G, hd, hG0, hG, fun P' hP' => ?_⟩
      rcases Finset.mem_insert.mp hP' with rfl | hP'
      · exact hu
      · exact hGS P' hP'
    obtain ⟨k, z, hk, hz, hzP, hzS⟩ :=
      exists_avoid y hy P S fun P' hP' => exists_sep y hy hG (hGS P' hP') hu
    have hG' : G ^ k ∈ chartLat y 1 (d * k) := chartLat_pow_mem y hG k
    have hz' : z ^ d ∈ chartLat y 1 (d * k) := by
      rw [Nat.mul_comm]
      exact chartLat_pow_mem y hz d
    have hunitP : IsUnitAt y P (d * k) (G ^ k + z ^ d) := by
      rw [add_comm]
      have h1 : IsUnitAt y P (d * k) (z ^ d) := by
        rw [Nat.mul_comm]
        exact hzP.pow y d
      have h2 : ¬IsUnitAt y P (d * k) (G ^ k) := by
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        exact not_isUnitAt_pow y hy hu hG k'
      exact isUnitAt_add y hy h1 h2
    refine ⟨d * k, G ^ k + z ^ d, by simpa using Nat.mul_le_mul hd hk, ?_, add_mem hG' hz', ?_⟩
    · intro h0
      obtain ⟨t, ht0, -⟩ := exists_max y hy P
      have := hunitP t
      rw [h0, map_zero] at this
      exact pow_ne_zero _ ((Valuation.ne_zero_iff _).mpr ht0) (le_antisymm this zero_le)
    · intro P' hP'
      rcases Finset.mem_insert.mp hP' with rfl | hP'
      · exact hunitP
      · have h1 : IsUnitAt y P' (d * k) (G ^ k) := (hGS P' hP').pow y k
        have h2 : ¬IsUnitAt y P' (d * k) (z ^ d) := by
          obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
          rw [Nat.mul_comm]
          exact not_isUnitAt_pow y hy (hzS P' hP') hz d'
        exact isUnitAt_add y hy h1 h2
end GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
