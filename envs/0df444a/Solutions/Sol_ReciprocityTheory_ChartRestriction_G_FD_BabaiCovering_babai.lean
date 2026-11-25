-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.BabaiCovering.babai
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:53:14.827156+00:00
-- url     : https://prove2.me/submissions/304c9074-ebc9-4486-867d-779ddc2d101a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BabaiCovering

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.BabaiCovering
open Submodule Module
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
namespace ReciprocityTheory.ChartRestriction.G.FD.BabaiCovering
theorem _root_.solution : ∀ (m : ℕ) (y : Fin m → V) (v : V), v ∈ span ℝ (Set.range y) →
    ∃ x ∈ span ℤ (Set.range y), ‖v - x‖ ^ 2 ≤ (1 / 4) * ∑ i, ‖y i‖ ^ 2 := by
  have key : ∀ (m : ℕ) (y : Fin m → V) (c : Fin m → ℝ), ∃ n : Fin m → ℤ,
      ‖∑ i, (c i - (n i : ℝ)) • y i‖ ^ 2 ≤ (1 / 4) * ∑ i, ‖y i‖ ^ 2 := by
    intro m
    induction m with
    | zero => intro y c; exact ⟨fun i => i.elim0, by simp⟩
    | succ m ih =>
      intro y c
      obtain ⟨n, hn⟩ := ih (fun i => y i.castSucc) (fun i => c i.castSucc)
      set u := ∑ i : Fin m, (c i.castSucc - (n i : ℝ)) • y i.castSucc with hu
      set w := y (Fin.last m) with hw
      set f := Int.fract (c (Fin.last m)) with hfd
      have hf0 : 0 ≤ f := Int.fract_nonneg _
      have hf1 : f < 1 := Int.fract_lt_one _
      have havg : (1 - f) * ‖u + f • w‖ ^ 2 + f * ‖u + (f - 1) • w‖ ^ 2 =
          ‖u‖ ^ 2 + f * (1 - f) * ‖w‖ ^ 2 := by
        rw [norm_add_sq_real, norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_right,
          real_inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
        ring
      have hq : f * (1 - f) ≤ 1 / 4 := by nlinarith [sq_nonneg (f - 1 / 2)]
      have hbound : ‖u‖ ^ 2 + f * (1 - f) * ‖w‖ ^ 2 ≤ (1 / 4) * ∑ i, ‖y i‖ ^ 2 := by
        rw [Fin.sum_univ_castSucc]
        have h1 := mul_le_mul_of_nonneg_right hq (sq_nonneg ‖w‖)
        nlinarith [hn]
      have hsplit : ∀ N : ℤ, ∑ i, (c i - ((Fin.snoc (α := fun _ => ℤ) n N i : ℤ) : ℝ)) • y i =
          u + (c (Fin.last m) - (N : ℝ)) • w := by
        intro N
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, hu, hw]
      by_cases hc : ‖u + f • w‖ ^ 2 ≤ ‖u + (f - 1) • w‖ ^ 2
      · refine ⟨Fin.snoc (α := fun _ => ℤ) n ⌊c (Fin.last m)⌋, ?_⟩
        rw [hsplit, ← Int.fract]
        nlinarith [mul_nonneg hf0 (sub_nonneg.mpr hc)]
      · refine ⟨Fin.snoc (α := fun _ => ℤ) n (⌊c (Fin.last m)⌋ + 1), ?_⟩
        have e : c (Fin.last m) - (((⌊c (Fin.last m)⌋ + 1 : ℤ)) : ℝ) = f - 1 := by
          rw [hfd, Int.fract]
          push_cast
          ring
        rw [hsplit, e]
        push_neg at hc
        nlinarith [mul_nonneg (sub_nonneg.mpr hf1.le) (sub_nonneg.mpr hc.le)]
  intro m y v hv
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
  obtain ⟨n, hn⟩ := key m y c
  refine ⟨∑ i, (n i) • y i, Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), ?_⟩
  have e : v - ∑ i, (n i) • y i = ∑ i, (c i - (n i : ℝ)) • y i := by
    rw [← hc, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sub_smul, Int.cast_smul_eq_zsmul]
  rw [e]
  exact hn
end ReciprocityTheory.ChartRestriction.G.FD.BabaiCovering
