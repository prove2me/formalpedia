-- Prove2me | solution 1 for StableFA.Discounted.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:03:33.55593+00:00
-- url     : https://prove2.me/submissions/24c165f3-ca4f-402a-9e64-6db12e812143

import Mathlib
import Definitions.Def_BertsekasSSPModel
import Definitions.Def_StableFA_Discounted_Setting
import Theorems.Thm_StableFA_Discounted_theorem_2_2_contraction

open Filter Topology
open StableFA.Discounted


theorem solution {n : ℕ} {C : Type} [Fintype C] (M : BertsekasSSPModel n C)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hp1 : ∀ i, ∀ u ∈ M.U i, ∑ j, M.p i u j = 1)
    (MF : (Fin n → ℝ) → (Fin n → ℝ)) (hMF : ∀ Y Z : Fin n → ℝ, ‖MF Y - MF Z‖ ≤ ‖Y - Z‖) :
    Compatible MF (BertsekasDiscountedBellmanOp M γ) ∧
    ∀ V W : Fin n → ℝ,
      ‖MF (BertsekasDiscountedBellmanOp M γ V) - MF (BertsekasDiscountedBellmanOp M γ W)‖ ≤
        γ * ‖V - W‖ := by
  have hb (V W : Fin n → ℝ) :
      ‖MF (BertsekasDiscountedBellmanOp M γ V) - MF (BertsekasDiscountedBellmanOp M γ W)‖ ≤
        γ * ‖V-W‖ :=
    (hMF _ _).trans (theorem_2_2_contraction M γ hγ0 hγ1 hp1 V W)
  have hc : ContractingWith ⟨γ, hγ0⟩ (MF ∘ BertsekasDiscountedBellmanOp M γ) := by
    refine ⟨hγ1, LipschitzWith.of_dist_le_mul ?_⟩
    intro V W
    change ‖MF (BertsekasDiscountedBellmanOp M γ V) - MF (BertsekasDiscountedBellmanOp M γ W)‖ ≤ γ * ‖V-W‖
    exact hb V W
  exact ⟨fun V => ⟨hc.fixedPoint _, hc.tendsto_iterate_fixedPoint V⟩, hb⟩


