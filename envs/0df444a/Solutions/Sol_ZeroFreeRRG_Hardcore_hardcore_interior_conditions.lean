-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_interior_conditions
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:10:24.01531+00:00
-- url     : https://prove2.me/submissions/82ddea07-a8bb-4375-9a1d-b9dfa01aefd3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_ZeroFreeRRG_Hardcore_weak_ks_from_variational
import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_parameter_comparison
open scoped Classical
open BigOperators
namespace ZeroFreeRRG.Hardcore

private lemma hc_pi0 (z : ℂ) : Model.pi .hardcore z (0 : Fin 2) = 1-z := by
  simp [Model.pi, Model.Spin, Model.P, Fin.sum_univ_two] <;> ring
private lemma hc_pi1 (z : ℂ) : Model.pi .hardcore z (1 : Fin 2) = z := by
  simp [Model.pi, Model.Spin, Model.P, Fin.sum_univ_two] <;> ring
private lemma hc_k10 (z : ℂ) (hz : z ≠ 0) : Model.K .hardcore z (1 : Fin 2) (0 : Fin 2) = 1 := by
  simp [Model.K, Model.P, hc_pi1, hz]
private lemma hc_k11 (z : ℂ) : Model.K .hardcore z (1 : Fin 2) (1 : Fin 2) = 0 := by
  simp [Model.K, Model.P]

private lemma hc_eigenvalue (z : ℂ) (hz : z ≠ 0) (hz1 : z ≠ 1) (κ : ℂ)
    (hκ : κ ∈ Model.nonconstEig .hardcore z) : κ = -z / (1-z) := by
  obtain ⟨f, hf, hmean, hvec⟩ := hκ
  change Fin 2 → ℂ at f
  change (∑ i : Fin 2, Model.pi .hardcore z i * f i) = 0 at hmean
  change (Model.K .hardcore z).mulVec f = κ • f at hvec
  have hlinear : (1-z) * f (0 : Fin 2) + z * f (1 : Fin 2) = 0 := by
    simpa [Fin.sum_univ_two, hc_pi0, hc_pi1] using hmean
  have hv1 := congrFun hvec (1 : Fin 2)
  change (∑ x : Fin 2, Model.K .hardcore z (1 : Fin 2) x * f x) = κ * f (1 : Fin 2) at hv1
  have hf0 : f (0 : Fin 2) = κ * f (1 : Fin 2) := by
    simpa [Fin.sum_univ_two, hc_k10 z hz, hc_k11] using hv1
  have hf1 : f (1 : Fin 2) ≠ 0 := by
    intro hz'
    apply hf
    funext i
    change f i = (0 : ℂ)
    fin_cases i
    · simpa [hz'] using hf0
    · exact hz'
  have hp : ((1-z) * κ + z) * f (1 : Fin 2) = 0 := by rw [hf0] at hlinear; linear_combination hlinear
  have hh : (1-z) * κ + z = 0 := (mul_eq_zero.mp hp).resolve_right hf1
  have hn : 1-z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  apply (eq_div_iff hn).2
  linear_combination hh
end ZeroFreeRRG.Hardcore

namespace ZeroFreeRRG.Hardcore
private lemma hardcore_strict_KS (d : ℕ) (hd : 3 ≤ d) (α α' : ℝ)
    (hα : 0 < α) (hlt : α < α') (hα' : α' < 1 / 2)
    (hweak : ((d : ℝ) - 1) * (α' / (1 - α')) ^ 2 ≤ 1) :
    Condition2 .hardcore d α := by
  have ha' : 0 < α' := by linarith
  have ha1 : 0 < 1 - α := by linarith
  have ha1' : 0 < 1 - α' := by linarith
  have hpos : 0 < α / (1-α) := div_pos hα ha1
  have hlt' : α / (1-α) < α' / (1-α') := by
    apply (div_lt_div_iff₀ ha1 ha1').2
    nlinarith
  have hdpos : (0:ℝ) < (d:ℝ) - 1 := by
    have hd' : (3:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsquare : (α/(1-α))^2 < (α'/(1-α'))^2 := by nlinarith
  have hstrict : ((d : ℝ) - 1) * (α / (1 - α)) ^ 2 < 1 :=
    (mul_lt_mul_of_pos_left hsquare hdpos).trans_le hweak
  intro κ hκ
  have hc0 : (α:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hα)
  have hc1 : (α:ℂ) ≠ 1 := by exact_mod_cast (ne_of_lt (show α < 1 by linarith))
  rw [hc_eigenvalue (α:ℂ) hc0 hc1 κ hκ]
  have hnorm : ‖-(α:ℂ) / (1-(α:ℂ))‖ = α/(1-α) := by
    have hcoe : (1:ℂ) - (α:ℂ) = ((1-α:ℝ):ℂ) := by norm_cast
    rw [hcoe, norm_div, norm_neg, Complex.norm_real, Complex.norm_real]
    simp [Real.norm_eq_abs, abs_of_pos hα, abs_of_pos ha1]
  rw [hnorm]
  exact hstrict
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore

theorem _root_.solution (d : ℕ) (hd : 3 ≤ d) (α : ℝ)
    (hα : 0 < α) (hα2 : α < 1/2) (hint : InteriorVariationalRS .hardcore d α) :
    Condition1 .hardcore d α ∧ Condition2 .hardcore d α := by
  obtain ⟨α',hlt,hα',hrs⟩ := hint
  have ha' : 0 < α' := by linarith
  have hweak := (weak_ks_from_variational d 2 hd (by norm_num)).1 α' ha' hα' hrs
  exact ⟨(hardcore_parameter_comparison d hd α α' hα hlt hα' hrs).1,
    hardcore_strict_KS d hd α α' hα hlt hα' hweak⟩
end ZeroFreeRRG.Hardcore
