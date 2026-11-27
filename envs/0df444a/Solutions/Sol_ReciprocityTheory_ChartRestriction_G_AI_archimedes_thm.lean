-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.archimedes_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:25:38.725557+00:00
-- url     : https://prove2.me/submissions/44afe005-e8ad-4ce1-bafa-e5f42e977f4c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LintegralIoiOfRealMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_integrable_mul_inner
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_moment1_perp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_moment2_perp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_moment2_swap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_exists_basis_zero_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_arch0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.AI
open MeasureTheory
section moments
variable {u : E3} {f : ℝ → ℝ}
end moments
private theorem integral_const_mul_sphereMeasure (c : ℝ) (g : S2 → ℝ) :
    ∫ n, c * g n ∂sphereMeasure = c * ∫ n, g n ∂sphereMeasure := by
  exact integral_const_mul c g
end ReciprocityTheory.ChartRestriction.G.AI
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open MeasureTheory
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution : ArchimedesStatement := by
  unfold ArchimedesStatement
  intro u v w f hu hf
  obtain ⟨b, hb⟩ := exists_basis_zero_eq hu
  have hf1 : IntervalIntegrable (fun t => f t * t) MeasureTheory.volume (-1) 1 :=
    hf.mul_continuousOn continuousOn_id
  have hf2 : IntervalIntegrable (fun t => f t * t * t) MeasureTheory.volume (-1) 1 :=
    hf1.mul_continuousOn continuousOn_id
  obtain ⟨hI, h0⟩ := arch0 u f hu hf
  have h1 : ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) u ∂sphereMeasure
      = 1 / 2 * ∫ t in (-1 : ℝ)..1, f t * t := (arch0 u (fun t => f t * t) hu hf1).2
  have hI1 : Integrable (fun n : S2 => f (inner ℝ (n : E3) u) * inner ℝ (n : E3) u) sphereMeasure :=
    integrable_mul_inner hI u
  have h2 : ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) u * inner ℝ (n : E3) u ∂sphereMeasure
      = 1 / 2 * ∫ t in (-1 : ℝ)..1, f t * t * t := (arch0 u (fun t => f t * t * t) hu hf2).2
  have hI2 : Integrable (fun n : S2 => f (inner ℝ (n : E3) u) * inner ℝ (n : E3) u * inner ℝ (n : E3) u)
      sphereMeasure := integrable_mul_inner hI1 u
  have horth : ∀ i j : Fin 3, i ≠ j → inner ℝ (b i) (b j) = 0 := fun i j h => b.orthonormal.2 h
  have hnorm : ∀ i : Fin 3, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  have hbu : ∀ i : Fin 3, i ≠ 0 → inner ℝ (b i) u = 0 := by
    intro i hi; rw [← hb]; exact horth i 0 hi
  have hexp : ∀ x y : E3, inner ℝ x y = ∑ i, inner ℝ (b i) y * inner ℝ x (b i) := by
    intro x y
    rw [← b.sum_inner_mul_inner x y]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hX : ∀ i : Fin 3, i ≠ 0 → ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) u * inner ℝ (n : E3) (b i) ∂sphereMeasure = 0 :=
    fun i hi => moment1_perp (u := u) (f := fun t => f t * t) hI1 (hbu i hi)
  have hG : ∀ i j : Fin 3, Integrable (fun n : S2 =>
      f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b i) * inner ℝ (n : E3) (b j)) sphereMeasure :=
    fun i j => integrable_mul_inner (integrable_mul_inner hI (b i)) (b j)
  have hpt1 : ∀ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) v =
      ∑ i, inner ℝ (b i) v * (f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b i)) := by
    intro n
    rw [hexp (n : E3) v, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hkey1 : ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) v ∂sphereMeasure =
      ∑ i, inner ℝ (b i) v * ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b i) ∂sphereMeasure := by
    simp only [hpt1]
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun i _ => integral_const_mul_sphereMeasure _ _
    · intro i _; exact (integrable_mul_inner hI (b i)).const_mul _
  have hpt : ∀ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) v * inner ℝ (n : E3) w =
      ∑ i, ∑ j, (inner ℝ (b i) v * inner ℝ (b j) w) *
        (f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b i) * inner ℝ (n : E3) (b j)) := by
    intro n
    rw [hexp (n : E3) v, hexp (n : E3) w]
    simp only [Fin.sum_univ_three]
    ring
  have hkey : ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) v * inner ℝ (n : E3) w ∂sphereMeasure =
      ∑ i, ∑ j, (inner ℝ (b i) v * inner ℝ (b j) w) * ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b i) * inner ℝ (n : E3) (b j) ∂sphereMeasure := by
    simp only [hpt]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_finsetSum]
      · exact Finset.sum_congr rfl (fun j _ => integral_const_mul_sphereMeasure _ _)
      · intro j _; exact (hG i j).const_mul _
    · intro i _; exact integrable_finsetSum _ (fun j _ => (hG i j).const_mul _)
  have hM00 : ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b 0) * inner ℝ (n : E3) (b 0) ∂sphereMeasure = 1 / 2 * ∫ t in (-1 : ℝ)..1, f t * t * t := by
    rw [hb]; exact h2
  have hM0 : ∀ j : Fin 3, j ≠ 0 → ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b 0) * inner ℝ (n : E3) (b j) ∂sphereMeasure = 0 := by
    intro j hj; rw [hb]; exact hX j hj
  have hM0' : ∀ j : Fin 3, j ≠ 0 → ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b j) * inner ℝ (n : E3) (b 0) ∂sphereMeasure = 0 := by
    intro j hj
    have e : (fun n : S2 => f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b j) * inner ℝ (n : E3) (b 0)) =
        fun n : S2 => f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b 0) * inner ℝ (n : E3) (b j) := by
      funext n; ring
    rw [e]; exact hM0 j hj
  have hM12 : ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b 1) * inner ℝ (n : E3) (b 2) ∂sphereMeasure = 0 :=
    moment2_perp hI (hbu 1 (by decide)) (horth 1 2 (by decide))
  have hM21 : ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b 2) * inner ℝ (n : E3) (b 1) ∂sphereMeasure = 0 :=
    moment2_perp hI (hbu 2 (by decide)) (horth 2 1 (by decide))
  have hM22 : ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b 2) * inner ℝ (n : E3) (b 2) ∂sphereMeasure = ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b 1) * inner ℝ (n : E3) (b 1) ∂sphereMeasure :=
    moment2_swap hI (hbu 1 (by decide)) (hbu 2 (by decide))
      (by rw [hnorm, hnorm])
  have hsq : ∀ n : S2, inner ℝ (n : E3) u * inner ℝ (n : E3) u + inner ℝ (n : E3) (b 1) * inner ℝ (n : E3) (b 1) +
      inner ℝ (n : E3) (b 2) * inner ℝ (n : E3) (b 2) = 1 := by
    intro n
    have hn : ‖(n : E3)‖ = 1 := norm_eq_of_mem_sphere n
    have h := hexp (n : E3) (n : E3)
    rw [Fin.sum_univ_three, hb, real_inner_self_eq_norm_sq, hn, one_pow,
      real_inner_comm (n : E3) u, real_inner_comm (n : E3) (b 1),
      real_inner_comm (n : E3) (b 2)] at h
    linarith
  have hsum : ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b 1) * inner ℝ (n : E3) (b 1) ∂sphereMeasure + ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b 2) * inner ℝ (n : E3) (b 2) ∂sphereMeasure =
      ∫ n : S2, f (inner ℝ (n : E3) u) ∂sphereMeasure - ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) u * inner ℝ (n : E3) u ∂sphereMeasure := by
    rw [← integral_add (hG 1 1) (hG 2 2), ← integral_sub hI hI2]
    congr 1; funext n
    linear_combination (f (inner ℝ (n : E3) u)) * hsq n
  have hQ : 2 * ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b 1) * inner ℝ (n : E3) (b 1) ∂sphereMeasure =
      1 / 2 * (∫ t in (-1 : ℝ)..1, f t) - 1 / 2 * ∫ t in (-1 : ℝ)..1, f t * t * t := by
    linarith [hsum, hM22, h0, h2]
  have hγ : inner ℝ (b 1) v * inner ℝ (b 1) w + inner ℝ (b 2) v * inner ℝ (b 2) w =
      inner ℝ v w - inner ℝ u v * inner ℝ u w := by
    have h := hexp v w
    rw [Fin.sum_univ_three, hb, real_inner_comm u v, real_inner_comm (b 1) v,
      real_inner_comm (b 2) v] at h
    linarith
  have hJ : ∫ t in (-1 : ℝ)..1, f t * (t ^ 2 * (inner ℝ u v * inner ℝ u w) +
        (1 - t ^ 2) / 2 * (inner ℝ v w - inner ℝ u v * inner ℝ u w)) =
      (inner ℝ u v * inner ℝ u w - (inner ℝ v w - inner ℝ u v * inner ℝ u w) / 2) *
          (∫ t in (-1 : ℝ)..1, f t * t * t) +
        (inner ℝ v w - inner ℝ u v * inner ℝ u w) / 2 * ∫ t in (-1 : ℝ)..1, f t := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hf2.const_mul _) (hf.const_mul _)]
    congr 1; funext t; ring
  refine ⟨hI, h0, ?_, ?_⟩
  · rw [hkey1, Fin.sum_univ_three, moment1_perp hI (hbu 1 (by decide)),
      moment1_perp hI (hbu 2 (by decide)), hb, h1, intervalIntegral.integral_mul_const]
    ring
  · rw [hkey, hJ]
    simp only [Fin.sum_univ_three]
    rw [hM00, hM0 1 (by decide), hM0 2 (by decide), hM0' 1 (by decide), hM0' 2 (by decide),
      hM12, hM21, hM22, hb]
    linear_combination (∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (b 1) * inner ℝ (n : E3) (b 1) ∂sphereMeasure) * hγ +
      ((inner ℝ v w - inner ℝ u v * inner ℝ u w) / 2) * hQ
end ReciprocityTheory.ChartRestriction.G.AI
