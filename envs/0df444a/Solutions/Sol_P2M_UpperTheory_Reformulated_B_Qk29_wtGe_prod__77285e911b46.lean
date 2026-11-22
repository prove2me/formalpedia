-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:35.612841+00:00
-- url     : https://prove2.me/submissions/e956f342-2021-4a8c-8045-0c5141c7e92e

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WtGeProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem UpperTheory.Reformulated.B.Qk29.dot_add {ι : Type*} (a b : ι →₀ ℕ) (r : ι → ℝ) :
    UpperTheory.Reformulated.B.Qk29.dot (a + b) r = UpperTheory.Reformulated.B.Qk29.dot a r + UpperTheory.Reformulated.B.Qk29.dot b r := by
  unfold UpperTheory.Reformulated.B.Qk29.dot
  apply Finsupp.sum_add_index'
  · intro i; simp
  · intro i m n; push_cast; ring
private theorem UpperTheory.Reformulated.B.Qk29.wtGe_one {K : Type*} [NormedField K] {ι : Type*} {pi : ℝ}
    (hpi : 0 < pi) (r : ι → ℝ) : UpperTheory.Reformulated.B.Qk29.WtGe pi r 0 (1 : MvPowerSeries ι K) := by
  classical
  intro n
  unfold UpperTheory.Reformulated.B.Qk29.MonoWtGe
  rw [MvPowerSeries.coeff_one]
  split_ifs with h
  · subst h
    simp [UpperTheory.Reformulated.B.Qk29.dot]
  · rw [norm_zero]
    exact (Real.rpow_pos_of_pos hpi _).le
private theorem UpperTheory.Reformulated.B.Qk29.wtGe_mul {K : Type*} [NormedField K] {ι : Type*}
    [IsUltrametricDist K] {pi : ℝ} (hpi : 0 < pi) {r : ι → ℝ} {a b : ℝ}
    {f g : MvPowerSeries ι K} (hf : UpperTheory.Reformulated.B.Qk29.WtGe pi r a f)
    (hg : UpperTheory.Reformulated.B.Qk29.WtGe pi r b g) : UpperTheory.Reformulated.B.Qk29.WtGe pi r (a + b) (f * g) := by
  classical
  intro n
  unfold UpperTheory.Reformulated.B.Qk29.MonoWtGe
  rw [MvPowerSeries.coeff_mul]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_pos_of_pos hpi _).le
  intro p hp
  have hn : p.1 + p.2 = n := by simpa using hp
  have h1 := hf p.1
  have h2 := hg p.2
  unfold UpperTheory.Reformulated.B.Qk29.MonoWtGe at h1 h2
  have he : a + b - UpperTheory.Reformulated.B.Qk29.dot n r =
      (a - UpperTheory.Reformulated.B.Qk29.dot p.1 r) + (b - UpperTheory.Reformulated.B.Qk29.dot p.2 r) := by
    rw [← hn, UpperTheory.Reformulated.B.Qk29.dot_add]; ring
  rw [he, Real.rpow_add hpi, norm_mul]
  exact mul_le_mul h1 h2 (norm_nonneg _) (Real.rpow_pos_of_pos hpi _).le
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qk29
theorem _root_.solution.{u, v, w} :
    ∀ {K : Type u} [inst : NormedField K] {ι : Type v} [IsUltrametricDist K] {pi : ℝ},
      (0 : ℝ) < pi →
        ∀ {r : ι → ℝ} {α : Type w} (s : Finset α) (wt : α → ℝ) (F : α → MvPowerSeries ι K),
          (∀ i ∈ s, UpperTheory.Reformulated.B.Qk29.WtGe pi r (wt i) (F i)) → UpperTheory.Reformulated.B.Qk29.WtGe pi r (∑ i ∈ s, wt i) (∏ i ∈ s, F i) := by
  intro K inst ι _ pi hpi r α s wt F h
  classical
  induction s using Finset.induction_on with
  | empty => simpa using UpperTheory.Reformulated.B.Qk29.wtGe_one hpi r
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact UpperTheory.Reformulated.B.Qk29.wtGe_mul hpi (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end UpperTheory.Reformulated.B.Qk29
