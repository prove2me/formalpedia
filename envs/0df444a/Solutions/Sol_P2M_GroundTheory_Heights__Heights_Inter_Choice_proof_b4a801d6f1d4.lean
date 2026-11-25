-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_Choice_proof_b4a801d6f1d4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:13:48.117436+00:00
-- url     : https://prove2.me/submissions/541d47d9-50d6-40c1-ab6b-88406cd58547

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChoice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Choice_exists_form_avoid_26f0ac2ed4c2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.Inter
namespace Choice
theorem _root_.solution : Choice.Statement := by
  intro K _ ι _ P d a m Y x _ hY
  obtain ⟨d₀, hd₀⟩ := Choice.exists_form_avoid (R := ℤ) (Set.range x) (Set.finite_range x)
    (by rintro _ ⟨i, rfl⟩; exact (hY i).2.2.2.1)
  refine ⟨∑ l, (d₀ l + (a l).natAbs), fun k hk => ?_⟩
  have hle : ∀ l, d₀ l + (a l).natAbs ≤ k := fun l =>
    le_trans (Finset.single_le_sum (f := fun l => d₀ l + (a l).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)) hk
  have hnn : ∀ l, (d₀ l : ℤ) ≤ a l + k := by
    intro l
    have h1 := hle l
    omega
  refine ⟨?_, ?_⟩
  · obtain ⟨s, hs, hsx⟩ := hd₀ (fun l => (a l + k).toNat) (fun l => by
      have := hnn l
      show d₀ l ≤ (a l + k).toNat
      omega)
    exact ⟨fun l => (a l + k).toNat, s, fun l => Int.toNat_of_nonneg (le_trans (by positivity) (hnn l)),
      hs, fun i => hsx (x i) ⟨i, rfl⟩⟩
  · obtain ⟨t, ht, htx⟩ := hd₀ (fun _ => k) (fun l => le_trans (Nat.le_add_right _ _) (hle l))
    exact ⟨t, ht, fun i => htx (x i) ⟨i, rfl⟩⟩
end Choice
end GroundTheory.Heights₂.Heights.Inter
