-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.potts_lemma_4_17
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:05:19.180204+00:00
-- url     : https://prove2.me/submissions/550fa887-660d-4577-be03-30c74f354771

import Mathlib
import Theorems.Thm_ZeroFreeRRG_Hardcore_weak_ks_from_variational
import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_parameter_comparison
open scoped Classical
open BigOperators
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

theorem _root_.solution (d q : ℕ) (hd : 3 ≤ d) (hq : 2 ≤ q) :
    (∀ β : ℝ, 0 < β → β < 1 → InteriorVariationalRS (.potts q) d β →
        Condition1 (.potts q) d β ∧ Condition2 (.potts q) d β) ∧
    (∀ β' β : ℝ, 0 ≤ β' → β' < β → β < 1 →
        VariationalRS (.potts q) d β' → VariationalRS (.potts q) d β) := by
  constructor
  · intro β _ hβ hInt
    obtain ⟨β', hβ', hlt, hrs⟩ := hInt
    have hb' : β' < 1 := by linarith
    have hweak := (weak_ks_from_variational d q hd hq).2 β' hβ' hb' hrs
    exact ⟨(potts_parameter_comparison d q hd hq β' β hβ' hlt hβ hrs).1,
      potts_strict_KS d q hd hq β' β hβ' hlt hβ hweak⟩
  · intro β' β hβ' hlt hβ hrs
    exact (potts_parameter_comparison d q hd hq β' β hβ' hlt hβ hrs).2
end ZeroFreeRRG.Hardcore
