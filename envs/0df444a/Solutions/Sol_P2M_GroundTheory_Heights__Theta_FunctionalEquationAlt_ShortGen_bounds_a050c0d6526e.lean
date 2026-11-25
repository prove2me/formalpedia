-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_bounds_a050c0d6526e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:35:23.530082+00:00
-- url     : https://prove2.me/submissions/ebba8bf3-596c-4e8a-b652-171d8cd69024

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearIndependentRealOfInt
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_mem_zsmul_of_proj_eq_zero_f3d0fb732dc2
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_exists_lift_4f41a057c0ff
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_decompose_4fac0870e84b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
open Module Submodule Matrix
open scoped RealInnerProductSpace
noncomputable section
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
namespace GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
theorem _root_.solution (m : ℕ) :
    (∀ lam : ℝ, 0 < lam → ∃ g : ℝ, 0 < g ∧ ∀ b : Fin m → W, LinearIndependent ℝ b →
        Sep (span ℤ (Set.range b)) lam → g ≤ (gram ℝ b).det) ∧
    (∀ lam : ℝ, 0 < lam → ∀ C : ℝ, ∃ R : ℝ, ∀ b : Fin m → W, LinearIndependent ℝ b →
        Sep (span ℤ (Set.range b)) lam → (gram ℝ b).det ≤ C →
        span ℤ (Set.range b) ≤ span ℤ {x | x ∈ span ℤ (Set.range b) ∧ ‖x‖ ≤ R}) := by
  induction m with
  | zero =>
    refine ⟨fun lam _ => ⟨1, one_pos, fun b _ _ => by simp⟩, fun lam _ C => ⟨0, fun b _ _ _ => ?_⟩⟩
    have : Set.range b = ∅ := Set.range_eq_empty b
    simp [this]
  | succ m ih =>
    refine ⟨fun lam hlam => ?_, fun lam hlam C => ?_⟩
    · obtain ⟨g, hg, hgb⟩ := ih.1 (lam / 2) (half_pos hlam)
      refine ⟨lam ^ 2 * g, by positivity, fun b hb hsep => ?_⟩
      obtain ⟨v, c, -, -, hlv, -, hc, -, hsepc, hdet⟩ := decompose b hb hlam hsep
      rw [hdet]
      have h1 := hgb c hc hsepc
      have h2 : lam ^ 2 ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ hlam.le hlv 2
      exact mul_le_mul h2 h1 hg.le (sq_nonneg _)
    · obtain ⟨g, hg, hgb⟩ := ih.1 (lam / 2) (half_pos hlam)
      obtain ⟨R', hR'⟩ := ih.2 (lam / 2) (half_pos hlam) (C / lam ^ 2)
      refine ⟨|R'| + Real.sqrt (C / g), fun b hb hsep hC => ?_⟩
      obtain ⟨v, c, hvL, hv, hlv, hmin, hc, hmemc, hsepc, hdet⟩ := decompose b hb hlam hsep
      have hgc := hgb c hc hsepc
      have hv2 : ‖v‖ ^ 2 ≤ C / g := by
        rw [le_div_iff₀ hg]
        calc ‖v‖ ^ 2 * g ≤ ‖v‖ ^ 2 * (gram ℝ c).det :=
              mul_le_mul_of_nonneg_left hgc (sq_nonneg _)
          _ = (gram ℝ b).det := hdet.symm
          _ ≤ C := hC
      have hvR : ‖v‖ ≤ Real.sqrt (C / g) := (le_abs_self _).trans (Real.abs_le_sqrt hv2)
      have hcC : (gram ℝ c).det ≤ C / lam ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        have h2 : lam ^ 2 ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ hlam.le hlv 2
        have hc0 : 0 ≤ (gram ℝ c).det := hg.le.trans hgc
        nlinarith
      have hgen := hR' c hc hsepc hcC
      set L := span ℤ (Set.range b) with hL
      set N := span ℤ {x | x ∈ L ∧ ‖x‖ ≤ |R'| + Real.sqrt (C / g)} with hN
      have hNL : N ≤ L := span_le.2 fun x hx => hx.1
      have hvN : v ∈ N := subset_span ⟨hvL, by linarith [abs_nonneg R']⟩
      have hlift : ∀ u ∈ span ℤ {x | x ∈ span ℤ (Set.range c) ∧ ‖x‖ ≤ R'},
          ∃ y ∈ N, proj v y = u := by
        intro u hu
        induction hu using Submodule.span_induction with
        | mem u hu =>
          obtain ⟨hu1, hu2⟩ := hu
          obtain ⟨x, hx, rfl⟩ := (hmemc u).1 hu1
          obtain ⟨y, hyL, hy, hyn⟩ := exists_lift hvL hv hx
          refine ⟨y, subset_span ⟨hyL, ?_⟩, hy⟩
          linarith [le_abs_self R', norm_nonneg v]
        | zero => exact ⟨0, N.zero_mem, map_zero _⟩
        | add u u' _ _ hu hu' =>
          obtain ⟨y, hy, rfl⟩ := hu
          obtain ⟨y', hy', rfl⟩ := hu'
          exact ⟨y + y', N.add_mem hy hy', map_add _ _ _⟩
        | smul k u _ hu =>
          obtain ⟨y, hy, rfl⟩ := hu
          exact ⟨k • y, N.smul_mem k hy, map_zsmul _ _ _⟩
      intro x hx
      obtain ⟨y, hyN, hy⟩ := hlift (proj v x) (hgen ((hmemc _).2 ⟨x, hx, rfl⟩))
      have hxy : x - y ∈ L := L.sub_mem hx (hNL hyN)
      have h0 : proj v (x - y) = 0 := by rw [map_sub, hy, sub_self]
      obtain ⟨k, hk⟩ := mem_zsmul_of_proj_eq_zero hvL hv hmin hxy h0
      have hxe : x = k • v + y := by
        rw [← hk]
        abel
      rw [hxe]
      exact N.add_mem (N.smul_mem k hvN) hyN
end GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
