-- Prove2me | solution 1 for UniformPrecSched.Makespan.theorem_3_7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T13:04:23.079954+00:00
-- url     : https://prove2.me/submissions/f87fe93d-e4ca-40d1-a181-0f9106ac8649
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_Model
import Definitions.Def_UniformPrecSched_Makespan_LP
import Definitions.Def_UniformPrecSched_Makespan_Rounding
import Theorems.Thm_UniformPrecSched_Makespan_theorem_3_5
import Theorems.Thm_UniformPrecSched_Makespan_corollary_3_6
import Theorems.Thm_UniformPrecSched_Makespan_lp_lower_bound
import Theorems.Thm_UniformPrecSched_Makespan_speed_rounding
import Theorems.Thm_UniformPrecSched_Makespan_rounded_schedule_lift

set_option autoImplicit false

namespace Pda5cd3d0
open UniformPrecSched.Makespan


/-- the closed-form "asymptotic constant" step of Theorem 3.7, with c = 40 -/
theorem const_bound (m : ℕ) (hm : 2 ≤ m) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : K ≤ Real.log (Real.logb 2 m * m) + 1) :
    (K + 2 * Real.sqrt K + 1) * (Real.exp 1 * (1 + 1 / Real.logb 2 m)) ≤
      1.89 * Real.logb 2 m + 40 * Real.sqrt (Real.logb 2 m) := by
  have hL1 : (1 : ℝ) ≤ Real.logb 2 m := one_le_logb_two hm
  set L := Real.logb 2 m with hLdef
  have hm0 : (0 : ℝ) < m := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hL0 : 0 < L := by linarith
  have ha1 := Real.log_two_lt_d9
  have ha0 := Real.log_two_gt_d9
  have he1 := Real.exp_one_lt_d9
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  set a := Real.log 2 with ha
  set e := Real.exp 1 with he
  have hlogm : Real.log m = L * a := by
    rw [hLdef, Real.logb, div_mul_cancel₀]
    exact ne_of_gt (by linarith)
  set t := Real.sqrt L with ht
  have ht2 : t ^ 2 = L := Real.sq_sqrt hL0.le
  have ht1 : 1 ≤ t := by
    rw [ht]; exact Real.one_le_sqrt.mpr hL1
  have hlogL : Real.log L ≤ 2 * t - 2 := by
    have h1 : Real.log L = 2 * Real.log t := by
      rw [← ht2, Real.log_pow]; push_cast; ring
    have h2 := Real.log_le_sub_one_of_pos (show 0 < t by linarith)
    linarith
  have hlogLm : Real.log (L * m) = Real.log L + L * a := by
    rw [Real.log_mul (ne_of_gt hL0) (ne_of_gt hm0), hlogm]
  set s := Real.sqrt K with hs
  have hs2 : s ^ 2 = K := Real.sq_sqrt hK0
  have hs0 : 0 ≤ s := Real.sqrt_nonneg K
  have hKb : s ^ 2 ≤ a * t ^ 2 + 2 * t - 1 := by
    rw [hs2, ht2]; linarith
  have hst : s ≤ 2 * t := by nlinarith
  have hP : K + 2 * s + 1 ≤ a * t ^ 2 + 6 * t := by
    rw [← hs2]; nlinarith
  have hF0 : 0 ≤ e * (1 + 1 / L) := by positivity
  have hstep := mul_le_mul_of_nonneg_right hP hF0
  have hexp : (a * t ^ 2 + 6 * t) * (e * (1 + 1 / L)) =
      e * a * t ^ 2 + 6 * e * t + e * a + 6 * e / t := by
    rw [← ht2]
    have : t ≠ 0 := by positivity
    field_simp
    ring
  have h6 : 6 * e / t ≤ 6 * e := div_le_self (by positivity) ht1
  have hea : e * a ≤ 1.8842 := by nlinarith
  have hea2 : e * a * t ^ 2 ≤ 1.89 * t ^ 2 := by nlinarith
  have het : 6 * e * t ≤ 16.31 * t := by nlinarith
  have hsq : 40 * t = 40 * Real.sqrt L := by rw [ht]
  rw [← hsq]
  linarith

/-- `makespan` depends only on `μ` and `S`. -/
theorem makespan_congr {n m : ℕ} {I : Instance n m} (σ τ : Schedule I)
    (hμ : ∀ j, σ.μ j = τ.μ j) (hS : ∀ j, σ.S j = τ.S j) : σ.makespan = τ.makespan := by
  have hC : σ.C = τ.C := funext fun j => by simp [Schedule.C, hμ j, hS j]
  unfold Schedule.makespan
  rw [hC]

theorem makespan_nonneg {n m : ℕ} {I : Instance n m} (σ : Schedule I) : 0 ≤ σ.makespan := by
  unfold Schedule.makespan
  split_ifs with h
  · obtain ⟨j, -⟩ := h
    refine le_trans ?_ (Finset.le_sup' σ.C (Finset.mem_univ j))
    have := σ.S_nonneg j
    have : 0 < I.p j / I.s (σ.μ j) := div_pos (I.p_pos j) (I.s_pos _)
    simp only [Schedule.C]
    linarith
  · exact le_rfl


/-- Theorem 3.7 reduced to its five child nodes (theorem_3_5, corollary_3_6, lp_lower_bound,
speed_rounding, rounded_schedule_lift), whose statements are taken verbatim as hypotheses. -/
theorem theorem_3_7_reduction
    (H35 : ∀ {n m : ℕ} (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ)
      (C : Fin n → ℝ) (D : ℝ) (_hLP : LPOptimal I x C D) (k : Assignment I)
      (_hk : IsLPAssignment I x (Real.sqrt (numSpeeds I) + 1) k) (σ : Schedule I)
      (_hσ : IsSpeedListSchedule I k σ) (σstar : Schedule I),
      σ.makespan ≤ ((numSpeeds I : ℝ) + 2 * Real.sqrt (numSpeeds I) + 1) * σstar.makespan)
    (H36 : ∀ {n m : ℕ} (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ)
      (C : Fin n → ℝ) (D : ℝ) (_hLP : LPOptimal I x C D) (k : Assignment I)
      (_hk : IsLPAssignment I x (Real.sqrt (numSpeeds I) + 1) k) (σ : Schedule I)
      (_hσ : IsSpeedListSchedule I k σ),
      σ.makespan ≤ ((numSpeeds I : ℝ) + 2 * Real.sqrt (numSpeeds I) + 1) * D)
    (HLP : ∀ {n m : ℕ} (I : Instance n m),
      (∃ x C D, LPOptimal I x C D) ∧
        ∀ x C D, LPOptimal I x C D → ∀ σ : Schedule I, D ≤ σ.makespan)
    (HSR : ∀ {n m : ℕ} (I : Instance n m) (α β : ℝ) (hα : 1 ≤ α) (hβ : 1 < β),
      (numSpeeds (roundInstance I α β hα hβ) : ℝ) ≤ (⌊Real.logb β (α * m)⌋ : ℝ) + 1 ∧
        ∀ x C D, LPFeasible I x C D →
          ∃ x' C' D', LPFeasible (roundInstance I α β hα hβ) x' C' D' ∧
            D' ≤ β * (1 + 1 / α) * D)
    (HRL : ∀ {n m : ℕ} (I : Instance n m) (α β : ℝ) (hα : 1 ≤ α) (hβ : 1 < β)
      (σ' : Schedule (roundInstance I α β hα hβ)),
      ∃ σ : Schedule I, (∀ j, σ.μ j = keptEmb I α (σ'.μ j) ∧ σ.S j = σ'.S j) ∧
        σ.makespan ≤ σ'.makespan) :
    ∃ c : ℝ, ∀ (n m : ℕ) (I : Instance n m) (hm : 2 ≤ m),
      ∀ (x : Fin (numSpeeds I) → Fin n → ℝ) (C : Fin n → ℝ) (D : ℝ), LPOptimal I x C D →
      ∀ kA : Assignment I, IsLPAssignment I x (Real.sqrt (numSpeeds I) + 1) kA →
      ∀ σA : Schedule I, IsSpeedListSchedule I kA σA →
      ∀ (x' : Fin (numSpeeds (logRoundInstance I hm)) → Fin n → ℝ) (C' : Fin n → ℝ) (D' : ℝ),
        LPOptimal (logRoundInstance I hm) x' C' D' →
      ∀ kB : Assignment (logRoundInstance I hm),
        IsLPAssignment (logRoundInstance I hm) x'
          (Real.sqrt (numSpeeds (logRoundInstance I hm)) + 1) kB →
      ∀ σB' : Schedule (logRoundInstance I hm), IsSpeedListSchedule (logRoundInstance I hm) kB σB' →
      ∀ σB : Schedule I,
        (∀ j, σB.μ j = keptEmb I (Real.logb 2 m) (σB'.μ j) ∧ σB.S j = σB'.S j) →
      ∀ σstar : Schedule I,
        min σA.makespan σB.makespan ≤
          min ((numSpeeds I : ℝ) + 2 * Real.sqrt (numSpeeds I) + 1)
              (1.89 * Real.logb 2 m + c * Real.sqrt (Real.logb 2 m)) * σstar.makespan := by
  refine ⟨40, ?_⟩
  intro n m I hm x C D hLP kA hkA σA hσA x' C' D' hLP' kB hkB σB' hσB' σB hσB σstar
  have hL1 : (1 : ℝ) ≤ Real.logb 2 m := one_le_logb_two hm
  have hM0 : 0 ≤ σstar.makespan := makespan_nonneg σstar
  -- (A)
  have hA := H35 I x C D hLP kA hkA σA hσA σstar
  -- (B)
  obtain ⟨⟨xb, Cb, Db, hopt⟩, hlb⟩ := HLP I
  have hDb : Db ≤ σstar.makespan := hlb xb Cb Db hopt σstar
  obtain ⟨hK, hfeas⟩ := HSR I (Real.logb 2 m) (Real.exp 1) (one_le_logb_two hm) one_lt_exp_one
  obtain ⟨x'', C'', D'', hf'', hD''⟩ := hfeas xb Cb Db hopt.1
  have hD' : D' ≤ D'' := hLP'.2 x'' C'' D'' hf''
  obtain ⟨σl, hσl, hσlle⟩ :=
    HRL I (Real.logb 2 m) (Real.exp 1) (one_le_logb_two hm) one_lt_exp_one σB'
  have hBl : σB.makespan = σl.makespan :=
    makespan_congr σB σl (fun j => by rw [(hσB j).1, (hσl j).1])
      (fun j => by rw [(hσB j).2, (hσl j).2])
  have hB' := H36 (logRoundInstance I hm) x' C' D' hLP' kB hkB σB' hσB'
  set K' : ℕ := numSpeeds (logRoundInstance I hm) with hK'def
  have hX0 : 0 ≤ (K' : ℝ) + 2 * Real.sqrt K' + 1 := by positivity
  have hF0 : 0 ≤ Real.exp 1 * (1 + 1 / Real.logb 2 m) := by positivity
  have hD'M : D' ≤ Real.exp 1 * (1 + 1 / Real.logb 2 m) * σstar.makespan := by
    calc D' ≤ D'' := hD'
      _ ≤ Real.exp 1 * (1 + 1 / Real.logb 2 m) * Db := hD''
      _ ≤ _ := mul_le_mul_of_nonneg_left hDb hF0
  have hKb : (K' : ℝ) ≤ Real.log (Real.logb 2 m * m) + 1 := by
    have h1 : (K' : ℝ) ≤ (⌊Real.logb (Real.exp 1) (Real.logb 2 m * m)⌋ : ℝ) + 1 := hK
    have h2 : Real.logb (Real.exp 1) (Real.logb 2 m * m) = Real.log (Real.logb 2 m * m) := by
      simp [Real.logb, Real.log_exp]
    rw [h2] at h1
    have h3 := Int.floor_le (Real.log (Real.logb 2 m * m))
    linarith
  have hcb := const_bound m hm K' (by positivity) hKb
  have hB : σB.makespan ≤
      (1.89 * Real.logb 2 m + 40 * Real.sqrt (Real.logb 2 m)) * σstar.makespan := by
    calc σB.makespan = σl.makespan := hBl
      _ ≤ σB'.makespan := hσlle
      _ ≤ ((K' : ℝ) + 2 * Real.sqrt K' + 1) * D' := hB'
      _ ≤ ((K' : ℝ) + 2 * Real.sqrt K' + 1) *
          (Real.exp 1 * (1 + 1 / Real.logb 2 m) * σstar.makespan) :=
        mul_le_mul_of_nonneg_left hD'M hX0
      _ = ((K' : ℝ) + 2 * Real.sqrt K' + 1) *
          (Real.exp 1 * (1 + 1 / Real.logb 2 m)) * σstar.makespan := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcb hM0
  rw [min_mul_of_nonneg _ _ hM0]
  exact min_le_min hA hB

end Pda5cd3d0

open UniformPrecSched.Makespan Pda5cd3d0 in
theorem solution :
    ∃ c : ℝ, ∀ (n m : ℕ) (I : Instance n m) (hm : 2 ≤ m),
      ∀ (x : Fin (numSpeeds I) → Fin n → ℝ) (C : Fin n → ℝ) (D : ℝ), LPOptimal I x C D →
      ∀ kA : Assignment I, IsLPAssignment I x (Real.sqrt (numSpeeds I) + 1) kA →
      ∀ σA : Schedule I, IsSpeedListSchedule I kA σA →
      ∀ (x' : Fin (numSpeeds (logRoundInstance I hm)) → Fin n → ℝ) (C' : Fin n → ℝ) (D' : ℝ),
        LPOptimal (logRoundInstance I hm) x' C' D' →
      ∀ kB : Assignment (logRoundInstance I hm),
        IsLPAssignment (logRoundInstance I hm) x'
          (Real.sqrt (numSpeeds (logRoundInstance I hm)) + 1) kB →
      ∀ σB' : Schedule (logRoundInstance I hm), IsSpeedListSchedule (logRoundInstance I hm) kB σB' →
      ∀ σB : Schedule I,
        (∀ j, σB.μ j = keptEmb I (Real.logb 2 m) (σB'.μ j) ∧ σB.S j = σB'.S j) →
      ∀ σstar : Schedule I,
        min σA.makespan σB.makespan ≤
          min ((numSpeeds I : ℝ) + 2 * Real.sqrt (numSpeeds I) + 1)
              (1.89 * Real.logb 2 m + c * Real.sqrt (Real.logb 2 m)) * σstar.makespan :=
  theorem_3_7_reduction theorem_3_5 corollary_3_6 lp_lower_bound speed_rounding
    rounded_schedule_lift
