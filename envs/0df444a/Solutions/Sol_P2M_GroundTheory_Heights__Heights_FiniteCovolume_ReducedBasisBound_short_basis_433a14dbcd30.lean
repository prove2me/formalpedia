-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_ReducedBasisBound_short_basis_433a14dbcd30
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:40:04.14309+00:00
-- url     : https://prove2.me/submissions/17fad8ab-8ab6-4e33-8105-1e918a995e36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StReducedBasisBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeGram
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearIndependentRealOfInt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PReducedBasisBound
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_bounds_a050c0d6526e
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_decompose_4fac0870e84b
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_exists_lift_4f41a057c0ff
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_mem_zsmul_of_proj_eq_zero_f3d0fb732dc2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open Module Submodule Matrix GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
noncomputable section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace ReducedBasisBound
theorem _root_.solution {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (m : ℕ) : ∀ lam : ℝ, 0 < lam → ∀ C : ℝ, ∃ R : ℝ,
    ∀ b : Fin m → W, LinearIndependent ℝ b → Sep (span ℤ (Set.range b)) lam →
      (gram ℝ b).det ≤ C → ∃ b' : Fin m → W, span ℤ (Set.range b') = span ℤ (Set.range b) ∧
        ∀ i, ‖b' i‖ ≤ R := by
  induction m with
  | zero => exact fun _ _ _ => ⟨0, fun b _ _ _ => ⟨b, rfl, fun i => i.elim0⟩⟩
  | succ m ih =>
    intro lam hlam C
    obtain ⟨g, hg, hgb⟩ := (bounds (W := W) m).1 (lam / 2) (half_pos hlam)
    obtain ⟨R', hR'⟩ := ih (lam / 2) (half_pos hlam) (C / lam ^ 2)
    refine ⟨|R'| + Real.sqrt (C / g), fun b hb hsep hC => ?_⟩
    obtain ⟨v, c, hvL, hv, hlv, hmin, hc, hmemc, hsepc, hdet⟩ := decompose b hb hlam hsep
    have hgc := hgb c hc hsepc
    have hv2 : ‖v‖ ^ 2 ≤ C / g := by
      rw [le_div_iff₀ hg]
      nlinarith [mul_le_mul_of_nonneg_left hgc (sq_nonneg ‖v‖)]
    have hvR : ‖v‖ ≤ Real.sqrt (C / g) := (le_abs_self _).trans (Real.abs_le_sqrt hv2)
    have hcC : (gram ℝ c).det ≤ C / lam ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have h2 : lam ^ 2 ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ hlam.le hlv 2
      nlinarith [hg.le.trans hgc]
    obtain ⟨c', hc'span, hc'R⟩ := hR' c hc hsepc hcC
    set L := span ℤ (Set.range b) with hL
    have hlift : ∀ i, ∃ y ∈ L, proj v y = c' i ∧ ‖y‖ ≤ ‖c' i‖ + ‖v‖ / 2 := by
      intro i
      have hci : c' i ∈ span ℤ (Set.range c) := hc'span ▸ subset_span ⟨i, rfl⟩
      obtain ⟨x, hx, hxe⟩ := (hmemc _).1 hci
      obtain ⟨y, hyL, hy, hyn⟩ := exists_lift hvL hv hx
      exact ⟨y, hyL, hy.trans hxe, hxe ▸ hyn⟩
    choose y hyL hy hyn using hlift
    refine ⟨Fin.cons v y, le_antisymm ?_ ?_, fun i => ?_⟩
    · rw [span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hvL
      · simpa using hyL j
    · intro x hx
      obtain ⟨k, hk⟩ := (mem_span_range_iff_exists_fun ℤ).1
        (hc'span ▸ (hmemc (proj v x)).2 ⟨x, hx, rfl⟩)
      have hzL : ∑ j, k j • y j ∈ L := L.sum_mem fun j _ => L.smul_mem _ (hyL j)
      have h0 : proj v (x - ∑ j, k j • y j) = 0 := by
        rw [map_sub, map_sum, ← hk, sub_eq_zero]
        simp [map_zsmul, hy]
      obtain ⟨n, hn⟩ := mem_zsmul_of_proj_eq_zero hvL hv hmin (L.sub_mem hx hzL) h0
      have hxe : x = n • v + ∑ j, k j • y j := by rw [← hn]; abel
      rw [hxe]
      refine add_mem (smul_mem _ _ (subset_span ⟨0, by simp⟩))
        (sum_mem fun j _ => smul_mem _ _ (subset_span ⟨j.succ, by simp⟩))
    · have hs := Real.sqrt_nonneg (C / g)
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        linarith [abs_nonneg R']
      · simp only [Fin.cons_succ]
        linarith [hyn j, hc'R j, le_abs_self R']
end ReducedBasisBound
end GroundTheory.Heights₂.Heights.FiniteCovolume
