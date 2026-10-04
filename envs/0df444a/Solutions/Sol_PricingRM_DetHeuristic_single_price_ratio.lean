-- Prove2me | solution 1 for PricingRM.DetHeuristic.single_price_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T18:26:27.773313+00:00
-- url     : https://prove2.me/submissions/96c5de52-5953-4df1-bef3-ff374a58d19a

import Mathlib
import Definitions.Def_PricingRM_DetHeuristic_PricingModel

open MeasureTheory ProbabilityTheory
open scoped ENNReal

set_option autoImplicit false

namespace Cfe9ed03Aux

lemma cfe9_key {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : MemLp X 2 P) (C : ℝ) :
    ∫ ω, max (X ω - C) 0 ∂P ≤
        (Real.sqrt (variance X P + (C - ∫ ω, X ω ∂P) ^ 2) - (C - ∫ ω, X ω ∂P)) / 2 := by
  set Y : Ω → ℝ := fun ω => X ω - C with hYdef
  have hY : MemLp Y 2 P := hX.sub (memLp_const C)
  have hXi : Integrable X P := hX.integrable one_le_two
  have hYi : Integrable Y P := hY.integrable one_le_two
  have hVY : variance Y P = variance X P :=
    variance_sub_const hX.aestronglyMeasurable C
  have hEY : ∫ ω, Y ω ∂P = (∫ ω, X ω ∂P) - C := by
    simp only [hYdef]
    rw [integral_sub hXi (integrable_const C), integral_const]
    simp
  set A : Ω → ℝ := fun ω => |Y ω| with hAdef
  have hA : MemLp A 2 P := hY.abs
  have hAi : Integrable A P := hA.integrable one_le_two
  have hA2 : (A ^ 2) = (Y ^ 2) := by
    funext ω; simp [hAdef, sq_abs]
  have hvarA := variance_nonneg A P
  rw [variance_eq_sub hA, hA2] at hvarA
  have hvarY := variance_eq_sub hY
  rw [hVY] at hvarY
  -- (E A)^2 ≤ E[Y^2] = Var X + (C - E X)^2
  have hsq : (∫ ω, A ω ∂P) ^ 2 ≤ variance X P + (C - ∫ ω, X ω ∂P) ^ 2 := by
    have h1 : P[Y ^ 2] = variance X P + (∫ ω, Y ω ∂P) ^ 2 := by linarith
    rw [hEY] at h1
    have h2 : (∫ ω, A ω ∂P) ^ 2 ≤ P[Y ^ 2] := by linarith
    calc (∫ ω, A ω ∂P) ^ 2 ≤ P[Y ^ 2] := h2
      _ = variance X P + (C - ∫ ω, X ω ∂P) ^ 2 := by rw [h1]; ring
  have hEA0 : 0 ≤ ∫ ω, A ω ∂P := integral_nonneg (fun ω => abs_nonneg _)
  have hEA : ∫ ω, A ω ∂P ≤ Real.sqrt (variance X P + (C - ∫ ω, X ω ∂P) ^ 2) :=
    Real.le_sqrt_of_sq_le hsq
  have hmax : (fun ω => max (X ω - C) 0) = fun ω => (Y ω + A ω) / 2 := by
    funext ω
    simp only [hAdef, hYdef]
    rcases le_total 0 (X ω - C) with h | h
    · rw [max_eq_left h, abs_of_nonneg h]; ring
    · rw [max_eq_right h, abs_of_nonpos h]; ring
  rw [hmax, integral_div, integral_add hYi hAi, hEY]
  linarith


end Cfe9ed03Aux

namespace PricingRM.DetHeuristic

lemma cfe9_integrable_min (M : PricingModel 1) (C p : ℝ) :
    Integrable (fun x : ℝ => min x C) (M.μ 0 p) := by
  have h1 := M.integrable 0 p
  refine Integrable.mono' (h1.norm.add (integrable_const |C|)) ?_ ?_
  · exact (measurable_id.min measurable_const).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun x => ?_)
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rcases le_total x C with h | h
    · rw [min_eq_left h]; linarith [abs_nonneg C]
    · rw [min_eq_right h]; linarith [abs_nonneg x]

lemma cfe9_part2 (M : PricingModel 1) (C : ℝ) (p : ℝ) (hp : 0 ≤ p) :
    ∫⁻ x, ENNReal.ofReal (p * min x C) ∂(M.μ 0 p) ≤
      ENNReal.ofReal (p * min (meanDemand M 0 p) C) := by
  rcases lt_or_ge C 0 with hC | hC
  · have : ∀ x, ENNReal.ofReal (p * min x C) = 0 := fun x => by
      apply ENNReal.ofReal_of_nonpos
      exact mul_nonpos_of_nonneg_of_nonpos hp (le_trans (min_le_right _ _) hC.le)
    simp [this]
  · have hint : Integrable (fun x : ℝ => p * min x C) (M.μ 0 p) :=
      (cfe9_integrable_min M C p).const_mul p
    have hnn : 0 ≤ᵐ[M.μ 0 p] fun x : ℝ => p * min x C := by
      filter_upwards [M.nonneg 0 p] with x hx
      exact mul_nonneg hp (le_min hx hC)
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
    apply ENNReal.ofReal_le_ofReal
    rw [integral_const_mul]
    apply mul_le_mul_of_nonneg_left _ hp
    have hi := cfe9_integrable_min M C p
    apply le_min
    · unfold meanDemand
      exact integral_mono hi (M.integrable 0 p) (fun x => min_le_left x C)
    · calc ∫ x, min x C ∂(M.μ 0 p) ≤ ∫ _x, C ∂(M.μ 0 p) :=
            integral_mono hi (integrable_const C) (fun x => min_le_right x C)
        _ = C := by simp

lemma cfe9_opt_le (M : PricingModel 1) (C pdet : ℝ)
    (hopt : ∀ p : ℝ, 0 ≤ p → p * min (meanDemand M 0 p) C ≤ pdet * min (meanDemand M 0 pdet) C) :
    optValue M C ≤ ENNReal.ofReal (pdet * min (meanDemand M 0 pdet) C) := by
  simp only [optValue, valueToGo, add_zero]
  apply iSup₂_le
  intro p hp
  have hfin : (⟨1 - (0 + 1), by omega⟩ : Fin 1) = 0 := Subsingleton.elim _ _
  rw [hfin]
  exact (cfe9_part2 M C p hp).trans (ENNReal.ofReal_le_ofReal (hopt p hp))

end PricingRM.DetHeuristic

open MeasureTheory ProbabilityTheory PricingRM.DetHeuristic in
theorem solution (M : PricingModel 1) (C pdet : ℝ) (hp : 0 ≤ pdet)
    (hopt : ∀ p : ℝ, 0 ≤ p → p * min (meanDemand M 0 p) C ≤ pdet * min (meanDemand M 0 pdet) C)
    (hcap : meanDemand M 0 pdet ≤ C)
    (hL2 : MemLp (fun x : ℝ => x) 2 (M.μ 0 pdet))
    (hV : 0 < optValue M C) :
    (pdet * ∫ x, (x - max (x - C) 0) ∂(M.μ 0 pdet)) / (optValue M C).toReal ≥
      1 - (Real.sqrt (variance (fun x : ℝ => x) (M.μ 0 pdet)) /
        meanDemand M 0 pdet) / 2 := by
  set m := meanDemand M 0 pdet with hm
  set σ := Real.sqrt (variance (fun x : ℝ => x) (M.μ 0 pdet)) with hσ
  have hle := cfe9_opt_le M C pdet hopt
  rw [min_eq_left hcap] at hle
  have hfin : optValue M C ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hVr : 0 < (optValue M C).toReal := ENNReal.toReal_pos hV.ne' hfin
  have hpm : 0 < pdet * m := by
    by_contra h
    rw [not_lt] at h
    rw [ENNReal.ofReal_of_nonpos h] at hle
    exact absurd (lt_of_lt_of_le hV hle) (lt_irrefl 0)
  have hVle : (optValue M C).toReal ≤ pdet * m := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rwa [ENNReal.toReal_ofReal hpm.le] at this
  have hmpos : 0 < m := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  have hXi : Integrable (fun x : ℝ => x) (M.μ 0 pdet) := M.integrable 0 pdet
  have hmaxi : Integrable (fun x : ℝ => max (x - C) 0) (M.μ 0 pdet) :=
    (hXi.sub (integrable_const C)).pos_part
  have hsplit : ∫ x, (x - max (x - C) 0) ∂(M.μ 0 pdet) =
      m - ∫ x, max (x - C) 0 ∂(M.μ 0 pdet) := by
    rw [integral_sub hXi hmaxi]
    rfl
  have hkey := Cfe9ed03Aux.cfe9_key (M.μ 0 pdet) (fun x : ℝ => x) hL2 C
  have hmeq : ∫ x, x ∂(M.μ 0 pdet) = m := rfl
  rw [hmeq] at hkey
  have hvar : 0 ≤ variance (fun x : ℝ => x) (M.μ 0 pdet) := variance_nonneg _ _
  have hs : Real.sqrt (variance (fun x : ℝ => x) (M.μ 0 pdet) + (C - m) ^ 2) ≤ σ + (C - m) := by
    have h0 := Real.sqrt_nonneg (variance (fun x : ℝ => x) (M.μ 0 pdet))
    have h1 := Real.sq_sqrt hvar
    have ha : 0 ≤ C - m := by linarith
    exact Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hE : ∫ x, max (x - C) 0 ∂(M.μ 0 pdet) ≤ σ / 2 := by linarith
  have hN0 : 0 ≤ ∫ x, (x - max (x - C) 0) ∂(M.μ 0 pdet) := by
    apply integral_nonneg_of_ae
    filter_upwards [M.nonneg 0 pdet] with x hx
    have hC0 : 0 ≤ C := by linarith
    show (0:ℝ) ≤ x - max (x - C) 0
    rcases le_total (x - C) 0 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  rw [ge_iff_le, le_div_iff₀ hVr]
  have hid : (1 - σ / m / 2) * (pdet * m) = pdet * (m - σ / 2) := by
    field_simp
  rcases le_total 0 (1 - σ / m / 2) with ht | ht
  · calc (1 - σ / m / 2) * (optValue M C).toReal ≤ (1 - σ / m / 2) * (pdet * m) :=
          mul_le_mul_of_nonneg_left hVle ht
      _ = pdet * (m - σ / 2) := hid
      _ ≤ pdet * ∫ x, (x - max (x - C) 0) ∂(M.μ 0 pdet) := by
          rw [hsplit]
          exact mul_le_mul_of_nonneg_left (by linarith) hp
  · calc (1 - σ / m / 2) * (optValue M C).toReal ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg ht hVr.le
      _ ≤ pdet * ∫ x, (x - max (x - C) 0) ∂(M.μ 0 pdet) := mul_nonneg hp hN0
