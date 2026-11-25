-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.ctU_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:10:31.939582+00:00
-- url     : https://prove2.me/submissions/e5362728-8d1f-4c64-a673-35892ca96391

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColTorusC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
private theorem Hf_add_left_euclidean (a b c : EuclideanSpace ℂ ι) : Hf (a + b) c = Hf a c + Hf b c := by
  simp [Hf, add_mul, Finset.sum_add_distrib]
private theorem Hf_sub_leftSquareIntegrability (a b c : EuclideanSpace ℂ ι) : Hf (a - b) c = Hf a c - Hf b c := by
  simp [Hf, sub_mul, Finset.sum_sub_distrib]
private theorem Hf_smul_right' (a b : EuclideanSpace ℂ ι) (c : ℂ) :
    Hf a (c • b) = (starRingEnd ℂ) c * Hf a b := by
  simp only [Hf, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp <;> ring
private theorem Hf_swap_eq_conj' (a b : EuclideanSpace ℂ ι) : Hf b a = (starRingEnd ℂ) (Hf a b) := by
  simp only [Hf, map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
private theorem Hf_neg_right' (a c : EuclideanSpace ℂ ι) : Hf a (-c) = -Hf a c := by
  simp [Hf, Finset.sum_neg_distrib]
private theorem Hf_eq_inner_swap_euclidean (v w : EuclideanSpace ℂ ι) : Hf v w = @inner ℂ _ _ w v := by
  simp [Hf, PiLp.inner_apply, mul_comm]
end
end ReciprocityTheory.ChartRestriction.G.I2
namespace ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
variable {K : Submodule ℝ (EuclideanSpace ℂ ι)} (hK : ∀ a ∈ K, ∀ b ∈ K, (Hf a b).im = 0)
include hK
end
end ReciprocityTheory.ChartRestriction.G.I2
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (Y : GT ι) (w : EuclideanSpace ℂ ι) {q : ℕ} (hq : 1 ≤ q) {F : EuclideanSpace ℂ ι → ℂ}
    (hF : F ∈ (ctY Y w).Sec q) : ctU q (-((1 / (q : ℂ)) • w)) F ∈ Y.Sec q := by
  obtain ⟨hFd, hFe⟩ := hF
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  generalize hb : -((1 / (q : ℂ)) • w) = b
  change Differentiable ℂ (ctU q b F) ∧ ∀ γ ∈ lat Y.b, ∀ v, ctU q b F (v + γ) =
    Y.ka γ * cexp (q * Real.pi * Hf v γ + q * Real.pi * Hf γ γ / 2) * ctU q b F v
  refine ⟨?_, ?_⟩
  · have hd : Differentiable ℂ (fun t : EuclideanSpace ℂ ι => Hf t b) := by
      have hfun : (fun t : EuclideanSpace ℂ ι => Hf t b) = fun t => innerSL ℂ b t := by
        funext t
        simp [Hf_eq_inner_swap_euclidean]
      rw [hfun]
      exact (innerSL ℂ b).differentiable
    unfold ctU
    exact (((hd.const_mul _).sub_const _).cexp).mul (hFd.comp (differentiable_id.sub_const _))
  · intro γ hγ v
    have hγb : Hf γ b = -(1 / (q : ℂ)) * Hf γ w := by
      rw [← hb, Hf_neg_right', Hf_smul_right']
      simp
    have hbγ : Hf b γ = -(1 / (q : ℂ)) * (starRingEnd ℂ) (Hf γ w) := by
      rw [Hf_swap_eq_conj' γ b, hγb]
      simp
    have hsub : Hf γ w - (starRingEnd ℂ) (Hf γ w) = 2 * ((Hf γ w).im : ℂ) * I := by
      apply Complex.ext <;> simp <;> ring
    have hc : (q : ℂ) * (1 / (q : ℂ)) = 1 := mul_one_div_cancel hq0
    have key : cexp (q * Real.pi * Hf (v + γ) b - q * Real.pi * Hf b b / 2) *
        cexp (2 * Real.pi * (Hf γ w).im * I) *
        cexp (q * Real.pi * Hf (v - b) γ + q * Real.pi * Hf γ γ / 2) =
        cexp (q * Real.pi * Hf v γ + q * Real.pi * Hf γ γ / 2) *
        cexp (q * Real.pi * Hf v b - q * Real.pi * Hf b b / 2) := by
      simp only [← Complex.exp_add]
      congr 1
      rw [Hf_add_left_euclidean, Hf_sub_leftSquareIntegrability, hγb, hbγ]
      linear_combination (-(Real.pi : ℂ) * (Hf γ w - (starRingEnd ℂ) (Hf γ w))) * hc +
        (-(Real.pi : ℂ)) * hsub
    have hka : (ctY Y w).ka γ = Y.ka γ * cexp (2 * Real.pi * (Hf γ w).im * I) := rfl
    have hv : v + γ - b = (v - b) + γ := by abel
    simp only [ctU]
    rw [hv, hFe γ hγ (v - b), hka]
    linear_combination (Y.ka γ * F (v - b)) * key
end ReciprocityTheory.ChartRestriction.G.I2
