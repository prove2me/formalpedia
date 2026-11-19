-- Prove2me | solution 1 for SennottDP.SEN.thm_7_2_3_sen_acoi
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T03:58:55.043482+00:00
-- url     : https://prove2.me/submissions/544cb074-845f-468b-a32f-3e0ddcbbcb56

import Mathlib
import Definitions.Def_SennottDP_SEN_Assumptions
import Theorems.Thm_SennottDP_SEN_prop_7_7_1_sen_hstar_h
import Theorems.Thm_SennottDP_SEN_prop_7_7_2_h_acoi

set_option autoImplicit false
open scoped ENNReal NNReal
open Filter Topology SennottDP.SEN

theorem solution {S : Type} [Countable S] {Act : Type} (M : SennottDP.Discounted.MDC S Act) (z : S)
    (Mf : S → ℝ) (L : ℝ) (hSEN : SENAssumptions M z Mf L) :
    ∃ J : ℝ≥0,
      (∀ i, Tendsto (fun α : ℝ => ENNReal.ofReal (1 - α) * discValue M α i) (𝓝[<] 1)
        (𝓝 (J : ℝ≥0∞))) ∧
      (∃ h : S → ℝ, IsLimitFunction M z h) ∧
      (∀ h : S → ℝ, IsLimitFunction M z h →
        (∀ i, -L ≤ h i ∧ h i ≤ Mf i) ∧
        (∀ i, acoiMin M h i ≤ (((J : ℝ) + h i : ℝ) : EReal)) ∧
        ∀ e : StationaryPolicy M, RealizesACOI M h e →
          IsAverageOptimal M e.toPolicy ∧ (∀ i, avgCost M e.toPolicy i = (J : ℝ≥0∞)) ∧
          ∀ i, Tendsto (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) * expReal M e.toPolicy i n h)
            atTop (𝓝 0)) ∧
      (∀ fam : ℝ → StationaryPolicy M, (∀ α ∈ Set.Ioo (0 : ℝ) 1, RealizesDOE M α (fam α)) →
        ∀ f : StationaryPolicy M, IsLimitPoint M fam f →
          IsAverageOptimal M f.toPolicy ∧
          (∃ h : S → ℝ, IsAssociated M z fam f h) ∧
          ∀ h : S → ℝ, IsAssociated M z fam f h →
            (∀ i, ((M.C i (f.1 i) : ℝ) : EReal) + wsum (M.P i (f.1 i)) h ≤
              (((J : ℝ) + h i : ℝ) : EReal)) ∧
            ∀ i, Tendsto (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) * expReal M f.toPolicy i n h)
              atTop (𝓝 0)) ∧
      (∀ ψ : SennottDP.Discounted.Policy M, IsAverageOptimal M ψ → ∀ i,
        Tendsto (fun n : ℕ => horizonCost M ψ n i / (n : ℝ≥0∞)) atTop (𝓝 (avgCost M ψ i))) := by
  have h1 := prop_7_7_1_sen_hstar_h M z
  exact prop_7_7_2_h_acoi M z Mf (fun _ => L) (h1.2 Mf (fun _ => L) (h1.1 Mf L hSEN))
