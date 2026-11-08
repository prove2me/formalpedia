-- Prove2me | solution 1 for TaylorInv.eq_18
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:46:00.034799+00:00
-- url     : https://prove2.me/submissions/040dde46-ecda-40ba-92a2-07da951c60a1

import Mathlib
import Definitions.Def_TaylorInv_Policies

open MeasureTheory ProbabilityTheory

open TaylorInv in
theorem solution {J P : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (M : Model J P Ω)
    {Dbar ϵbar Bbar Mbar σbar : ℝ} (hA : M.Assumptions Dbar ϵbar Bbar Mbar σbar μ)
    (hb : ∀ j, 0 < M.b j + M.h' j) :
    ∀ j ω, M.baseStock j ω = (M.γ j + M.noiseQuantile j) + ∑ p, M.β j p * M.X j p ω := by
  intro j ω
  have hh' : 0 ≤ M.h' j := le_trans hA.h₀_nonneg (hA.h₀_le_h' j)
  have hbpos : 0 < M.b j := by have := hA.h'_le_b j j; linarith [hb j]
  have hcf0 : 0 < M.critFrac j := by unfold Model.critFrac; exact div_pos hbpos (hb j)
  have hcf1 : M.critFrac j ≤ 1 := by
    unfold Model.critFrac; rw [div_le_one (hb j)]; linarith
  obtain ⟨S, hS⟩ : ∃ S : Set ℝ, S = {e : ℝ | M.critFrac j ≤ M.noiseCDF j e} := ⟨_, rfl⟩
  have hne : S.Nonempty := by
    refine ⟨M.hi j, ?_⟩
    rw [hS]
    show M.critFrac j ≤ ∫ x in Set.Iic (M.hi j), M.f j x
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hA.f_zero_off j x
      (fun hx' => hx (Set.mem_Iic.mpr hx'.2))), hA.f_integral j]
    exact hcf1
  have hbdd : BddBelow S := by
    refine ⟨M.lo j, fun e he => ?_⟩
    rw [hS] at he
    by_contra hlt
    push_neg at hlt
    have h0 : M.noiseCDF j e = 0 := by
      unfold Model.noiseCDF
      exact setIntegral_eq_zero_of_forall_eq_zero (fun x hx => hA.f_zero_off j x
        (fun hx' => by have := Set.mem_Iic.mp hx; linarith [hx'.1]))
    have he' : M.critFrac j ≤ M.noiseCDF j e := he
    linarith
  obtain ⟨m, hm⟩ : ∃ m, m = M.meanShift j ω := ⟨_, rfl⟩
  have himg : (OrderIso.addRight m) '' S = {z : ℝ | M.critFrac j ≤ M.condCDF j ω z} := by
    ext z
    constructor
    · rintro ⟨e, he, rfl⟩
      rw [hS] at he
      show M.critFrac j ≤ ∫ x in Set.Iic (e + m - M.meanShift j ω), M.f j x
      rw [← hm, add_sub_cancel_right]
      exact he
    · intro hz
      refine ⟨z - m, ?_, sub_add_cancel z m⟩
      rw [hS]
      show M.critFrac j ≤ ∫ x in Set.Iic (z - m), M.f j x
      rw [hm]
      exact hz
  have key := OrderIso.map_csInf' (OrderIso.addRight m) hne hbdd
  rw [himg] at key
  have hq : M.noiseQuantile j = sInf S := by rw [hS]; rfl
  unfold Model.baseStock
  rw [← key, OrderIso.addRight_apply, ← hq, hm]
  unfold Model.meanShift
  ring
