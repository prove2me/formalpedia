-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.lemma_4_17
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T03:57:04.360346+00:00
-- url     : https://prove2.me/submissions/fba9fab4-75b0-4fa4-97cb-03a53bd085b2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_ZeroFreeRRG_Hardcore_weak_ks_from_variational
import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_parameter_comparison
import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_parameter_comparison
import Definitions.Def_ZeroFreeRRG_Hardcore_Kernels
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
private lemma potts_pi (q : ℕ) (β : ℂ) (i : Fin q)
    (hq : (q:ℂ) ≠ 0) (ht : (q:ℂ) - 1 + β ≠ 0) :
    Model.pi (.potts q) β i = (q:ℂ)⁻¹ := by
  unfold Model.pi Model.P
  change (∑ j : Fin q, ((1:ℂ) + if i = j then β - 1 else 0) /
      ((q:ℂ) * ((q:ℂ) - 1 + β))) = (q:ℂ)⁻¹
  rw [← Finset.sum_div]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hs : (∑ j : Fin q, if i = j then β - 1 else 0) = β - 1 := by simp
  rw [hs]
  field_simp
  ring
end ZeroFreeRRG.Hardcore
namespace ZeroFreeRRG.Hardcore
private lemma potts_K (q : ℕ) (β : ℂ) (i j : Fin q)
    (hq : (q:ℂ) ≠ 0) (ht : (q:ℂ) - 1 + β ≠ 0) :
    Model.K (.potts q) β i j = ((1:ℂ) + if i = j then β - 1 else 0) /
      ((q:ℂ) - 1 + β) := by
  change Model.P (.potts q) β i j / Model.pi (.potts q) β i = _
  rw [potts_pi q β i hq ht]
  change (((1:ℂ) + if i = j then β - 1 else 0) /
      ((q:ℂ) * ((q:ℂ) - 1 + β))) / (q:ℂ)⁻¹ = _
  field_simp

private lemma potts_eigenvalue (q : ℕ) (β : ℂ) (hq : (q:ℂ) ≠ 0)
    (ht : (q:ℂ) - 1 + β ≠ 0) (κ : ℂ)
    (hκ : κ ∈ Model.nonconstEig (.potts q) β) :
    κ = (β - 1) / ((q:ℂ) - 1 + β) := by
  obtain ⟨f, hf, hmean, hvec⟩ := hκ
  change Fin q → ℂ at f
  change (∑ i : Fin q, Model.pi (.potts q) β i * f i) = 0 at hmean
  have hsum : (∑ i : Fin q, f i) = 0 := by
    simp only [potts_pi q β _ hq ht, ← Finset.mul_sum] at hmean
    exact (mul_eq_zero.mp hmean).resolve_left (inv_ne_zero hq)
  have hpoint : ∀ i : Fin q, ((Model.K (.potts q) β).mulVec f) i =
      ((β - 1) / ((q:ℂ) - 1 + β)) * f i := by
    intro i
    change (∑ j : Fin q, Model.K (.potts q) β i j * f j) = _
    simp only [potts_K q β i _ hq ht, div_mul_eq_mul_div, ← Finset.sum_div]
    congr 1
    have hid : (∑ j : Fin q, ((1:ℂ) + if i = j then β - 1 else 0) * f j) =
        (β - 1) * f i := by
      simp only [add_mul, one_mul, Finset.sum_add_distrib]
      rw [hsum, zero_add]
      simp
    rw [hid]
  obtain ⟨i, hi⟩ : ∃ i : Fin q, f i ≠ 0 := by
    by_contra h
    push Not at h
    apply hf
    funext i
    exact h i
  have hi' := congrFun hvec i
  rw [hpoint i] at hi'
  change ((β - 1) / ((q:ℂ) - 1 + β)) * f i = κ * f i at hi'
  exact (mul_right_cancel₀ hi (hi'.symm))
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
private lemma potts_strict_KS (d q : ℕ) (hd : 3 ≤ d) (hq : 2 ≤ q) (β' β : ℝ)
    (hβ' : 0 ≤ β') (hlt : β' < β) (hβ : β < 1)
    (hweak : ((d : ℝ) - 1) * ((1 - β') / ((q : ℝ) - 1 + β')) ^ 2 ≤ 1) :
    Condition2 (.potts q) d β := by
  have hq' : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hd' : (3:ℝ) ≤ d := by exact_mod_cast hd
  have hqpos : (0:ℝ) < q := by linarith
  have hden : 0 < (q:ℝ) - 1 + β := by linarith
  have hden' : 0 < (q:ℝ) - 1 + β' := by linarith
  have hpos : 0 < (1-β) / ((q:ℝ)-1+β) := div_pos (by linarith) hden
  have hlt' : (1-β) / ((q:ℝ)-1+β) < (1-β') / ((q:ℝ)-1+β') := by
    apply (div_lt_div_iff₀ hden hden').2
    nlinarith [mul_pos (sub_pos.mpr hlt) hqpos]
  have hdpos : (0:ℝ) < (d:ℝ) - 1 := by linarith
  have hsquare : ((1-β) / ((q:ℝ)-1+β))^2 < ((1-β') / ((q:ℝ)-1+β'))^2 := by nlinarith
  have hstrict : ((d : ℝ) - 1) * ((1-β) / ((q:ℝ)-1+β)) ^ 2 < 1 :=
    (mul_lt_mul_of_pos_left hsquare hdpos).trans_le hweak
  intro κ hκ
  have hcq : (q:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hqpos)
  have hct : (q:ℂ) - 1 + (β:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hden)
  rw [potts_eigenvalue q (β:ℂ) hcq hct κ hκ]
  have hnorm : ‖((β:ℂ)-1) / ((q:ℂ)-1+(β:ℂ))‖ = (1-β) / ((q:ℝ)-1+β) := by
    have hnum : (β:ℂ) - 1 = ((β-1:ℝ):ℂ) := by norm_cast
    have hden0 : (q:ℂ)-1+(β:ℂ) = (((q:ℝ)-1+β:ℝ):ℂ) := by norm_cast
    rw [hnum, hden0, norm_div, Complex.norm_real, Complex.norm_real]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_neg (show β - 1 < 0 by linarith), abs_of_pos hden]
    congr 1
    ring
  rw [hnorm]
  exact hstrict
end ZeroFreeRRG.Hardcore

namespace ZeroFreeRRG.Hardcore

theorem _root_.solution (d q : ℕ) (hd : 3 ≤ d) (hq : 2 ≤ q) :
    (∀ α : ℝ, 0 < α → α < 1 / 2 → InteriorVariationalRS .hardcore d α →
        Condition1 .hardcore d α ∧ Condition2 .hardcore d α) ∧
    (∀ β : ℝ, 0 < β → β < 1 → InteriorVariationalRS (.potts q) d β →
        Condition1 (.potts q) d β ∧ Condition2 (.potts q) d β) ∧
    (∀ α α' : ℝ, 0 < α → α < α' → α' < 1 / 2 →
        VariationalRS .hardcore d α' → VariationalRS .hardcore d α) ∧
    (∀ β' β : ℝ, 0 ≤ β' → β' < β → β < 1 →
        VariationalRS (.potts q) d β' → VariationalRS (.potts q) d β) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α hα _ hInt
    obtain ⟨α', hlt, hα', hrs⟩ := hInt
    have ha' : 0 < α' := by linarith
    have hweak := (weak_ks_from_variational d q hd hq).1 α' ha' hα' hrs
    exact ⟨(hardcore_parameter_comparison d hd α α' hα hlt hα' hrs).1,
      hardcore_strict_KS d hd α α' hα hlt hα' hweak⟩
  · intro β _ hβ hInt
    obtain ⟨β', hβ', hlt, hrs⟩ := hInt
    have hb' : β' < 1 := by linarith
    have hweak := (weak_ks_from_variational d q hd hq).2 β' hβ' hb' hrs
    exact ⟨(potts_parameter_comparison d q hd hq β' β hβ' hlt hβ hrs).1,
      potts_strict_KS d q hd hq β' β hβ' hlt hβ hweak⟩
  · intro α α' hα hlt hα' hrs
    exact (hardcore_parameter_comparison d hd α α' hα hlt hα' hrs).2
  · intro β' β hβ' hlt hβ hrs
    exact (potts_parameter_comparison d q hd hq β' β hβ' hlt hβ hrs).2
end ZeroFreeRRG.Hardcore
