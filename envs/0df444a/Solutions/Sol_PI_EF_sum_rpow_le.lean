-- Prove2me | solution 1 for PI.EF.sum_rpow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:37:40.413582+00:00
-- url     : https://prove2.me/submissions/65494705-2d84-43fd-a701-df3db3276c6d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Finset
namespace PI.EF
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    ∑ i ∈ range K, ((i : ℝ) + 2) ^ (-(1 + ε)) ≤ 1 / ε := by
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-(1 + ε))) (Set.Icc 1 (1 + (K : ℝ))) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have h1 := hanti.sum_le_integral
  beta_reduce at h1
  have h0 : (0 : ℝ) ∉ Set.uIcc 1 (1 + (K : ℝ)) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    linarith [h.1]
  rw [integral_rpow (Or.inr ⟨fun h => by linarith, h0⟩)] at h1
  have hexp : -(1 + ε) + 1 = -ε := by ring
  rw [hexp, Real.one_rpow] at h1
  have hpos : 0 ≤ (1 + (K : ℝ)) ^ (-ε) := Real.rpow_nonneg (by linarith) _
  have hrhs : ((1 + (K : ℝ)) ^ (-ε) - 1) / (-ε) ≤ 1 / ε := by
    rw [div_neg, ← neg_div, neg_sub]
    exact div_le_div_of_nonneg_right (by linarith) hε.le
  calc ∑ i ∈ range K, ((i : ℝ) + 2) ^ (-(1 + ε))
      = ∑ i ∈ range K, (1 + ((i + 1 : ℕ) : ℝ)) ^ (-(1 + ε)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        push_cast
        ring
    _ ≤ _ := h1
    _ ≤ 1 / ε := hrhs
end PI.EF
