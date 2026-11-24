-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_coeff_eq_zero_of_tri_fd257542d139
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:35.129827+00:00
-- url     : https://prove2.me/submissions/cda0566e-8977-4c95-9a16-726830eaa066

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueSat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinGradedFrameIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_repr_sum_smul_c443a2f82c23

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
universe u v w
open GroundTheory.Heights₂.Heights.NumbersDVR.GradedFrameCharacterisation
variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.NumbersDVR.GradedFrameCharacterisation
theorem _root_.solution (w : Module.Basis (Fin N) Ω E) (bb : Fin N → E)
    (hup : ∀ q j : Fin N, q < j → w.repr (bb q) j = 0) (hd : ∀ q, w.repr (bb q) q ≠ 0)
    (a : Fin N → Ω) (n : ℕ) (h : ∀ j : Fin N, n ≤ (j : ℕ) → w.repr (∑ q, a q • bb q) j = 0) :
    ∀ q : Fin N, n ≤ (q : ℕ) → a q = 0 := by
  classical
  by_contra hne
  push Not at hne
  set T := Finset.univ.filter (fun q : Fin N => n ≤ (q : ℕ) ∧ a q ≠ 0) with hT
  have hTne : T.Nonempty := by
    obtain ⟨q, hq, hq'⟩ := hne
    exact ⟨q, by simp [hT, hq, hq']⟩
  have hq0 : T.max' hTne ∈ T := T.max'_mem hTne
  have hq0' := hq0
  simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hq0'
  have hsum : w.repr (∑ q, a q • bb q) (T.max' hTne) =
      a (T.max' hTne) * w.repr (bb (T.max' hTne)) (T.max' hTne) := by
    rw [repr_sum_smul, Finset.sum_eq_single (T.max' hTne)]
    · intro q _ hq
      rcases lt_or_gt_of_ne hq with hlt | hgt
      · rw [hup q _ hlt, mul_zero]
      · have haq : a q = 0 := by
          by_contra haq
          have hmem : q ∈ T := by
            simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨le_trans hq0'.1 (le_of_lt (Fin.lt_def.mp hgt)), haq⟩
          exact absurd (T.le_max' q hmem) (not_le.mpr hgt)
        rw [haq, zero_mul]
    · simp
  have h0 := h _ hq0'.1
  rw [hsum] at h0
  exact mul_ne_zero hq0'.2 (hd _) h0
end GroundTheory.Heights₂.Heights.NumbersDVR.GradedFrameCharacterisation
