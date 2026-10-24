-- Prove2me | solution 1 for UniformPrecSched.Makespan.rounded_schedule_lift
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T03:34:25.564993+00:00
-- url     : https://prove2.me/submissions/188ca737-5f62-44af-9bed-d2e3925a5151

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_Model
import Definitions.Def_UniformPrecSched_Makespan_Rounding

set_option autoImplicit false

namespace UniformPrecSchedLiftAux

open UniformPrecSched.Makespan

theorem roundedSpeed_le {n m : ℕ} (I : Instance n m) {β v : ℝ} (hβ : 1 < β) (hv : 0 < v) :
    roundedSpeed I β v ≤ v := by
  unfold roundedSpeed
  have hM := maxSpeed_pos I
  set x : ℝ := Real.logb β (maxSpeed I / v) with hx
  have hβ0 : 0 < β := by linarith
  have hlt : x < ((⌊x⌋ + 1 : ℤ) : ℝ) := by
    push_cast
    exact Int.lt_floor_add_one x
  have h1 : β ^ (-(⌊x⌋ + 1)) = β ^ (-(((⌊x⌋ + 1 : ℤ) : ℝ))) := by
    rw [← Real.rpow_intCast]
    push_cast
    ring_nf
  rw [h1]
  have h2 : β ^ (-(((⌊x⌋ + 1 : ℤ) : ℝ))) ≤ β ^ (-x) := by
    apply Real.rpow_le_rpow_of_exponent_le hβ.le
    linarith
  have h3 : β ^ (-x) = v / maxSpeed I := by
    rw [Real.rpow_neg hβ0.le, hx, Real.rpow_logb hβ0 hβ.ne' (div_pos hM hv)]
    rw [inv_div]
  calc maxSpeed I * β ^ (-(((⌊x⌋ + 1 : ℤ) : ℝ))) ≤ maxSpeed I * (v / maxSpeed I) :=
        mul_le_mul_of_nonneg_left (h3 ▸ h2) hM.le
    _ = v := by field_simp

end UniformPrecSchedLiftAux

open UniformPrecSchedLiftAux in
open UniformPrecSched.Makespan in
theorem solution {n m : ℕ} (I : Instance n m) (α β : ℝ) (hα : 1 ≤ α) (hβ : 1 < β)
    (σ' : Schedule (roundInstance I α β hα hβ)) :
    ∃ σ : Schedule I, (∀ j, σ.μ j = keptEmb I α (σ'.μ j) ∧ σ.S j = σ'.S j) ∧
      σ.makespan ≤ σ'.makespan := by
  -- processing times shrink on the original machines
  have hle : ∀ j, I.p j / I.s (keptEmb I α (σ'.μ j)) ≤
      (roundInstance I α β hα hβ).p j / (roundInstance I α β hα hβ).s (σ'.μ j) := by
    intro j
    show I.p j / I.s (keptEmb I α (σ'.μ j)) ≤
      I.p j / roundedSpeed I β (I.s (keptEmb I α (σ'.μ j)))
    have hs := I.s_pos (keptEmb I α (σ'.μ j))
    have hr : 0 < roundedSpeed I β (I.s (keptEmb I α (σ'.μ j))) :=
      (roundInstance I α β hα hβ).s_pos (σ'.μ j)
    exact div_le_div_of_nonneg_left (I.p_pos j).le hr (roundedSpeed_le I hβ hs)
  let σ : Schedule I :=
    { μ := fun j => keptEmb I α (σ'.μ j)
      S := σ'.S
      S_nonneg := σ'.S_nonneg
      noOverlap := by
        intro i j hij hμ
        have hμ' : σ'.μ i = σ'.μ j := (keptEmb I α).injective hμ
        rcases σ'.noOverlap i j hij hμ' with h | h
        · left; linarith [hle i]
        · right; linarith [hle j]
      precedence := by
        intro i j hp
        have := σ'.precedence i j hp
        linarith [hle i] }
  refine ⟨σ, fun j => ⟨rfl, rfl⟩, ?_⟩
  have hC : ∀ j, σ.C j ≤ σ'.C j := by
    intro j
    show σ'.S j + I.p j / I.s (keptEmb I α (σ'.μ j)) ≤
      σ'.S j + (roundInstance I α β hα hβ).p j / (roundInstance I α β hα hβ).s (σ'.μ j)
    linarith [hle j]
  unfold Schedule.makespan
  split_ifs with h
  · apply Finset.sup'_le
    intro j hj
    exact (hC j).trans (Finset.le_sup' σ'.C hj)
  · exact le_refl _
