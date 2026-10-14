-- Prove2me | solution 1 for StableFA.Discounted.corollary_3_1
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:11:44.312792+00:00
-- url     : https://prove2.me/submissions/6b09d7fe-06b3-44d5-8b76-765684ea655f

import Mathlib
import Definitions.Def_BertsekasSSPModel
import Definitions.Def_StableFA_Discounted_Setting
import Theorems.Thm_StableFA_Discounted_theorem_3_1

open Filter Topology
open StableFA.Discounted


theorem solution {n : ℕ} {C : Type} [Fintype C] (M : BertsekasSSPModel n C)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hp1 : ∀ i, ∀ u ∈ M.U i, ∑ j, M.p i u j = 1)
    (MF : (Fin n → ℝ) → (Fin n → ℝ)) (hMF : ∀ Y Z : Fin n → ℝ, ‖MF Y - MF Z‖ ≤ ‖Y - Z‖) :
    ∃ Vinf : Fin n → ℝ,
      (∀ V : Fin n → ℝ,
        Tendsto (fun k => (MF ∘ BertsekasDiscountedBellmanOp M γ)^[k] V) atTop (𝓝 Vinf)) ∧
      ∀ (V : Fin n → ℝ) (k : ℕ),
        ‖(MF ∘ BertsekasDiscountedBellmanOp M γ)^[k] V - Vinf‖ ≤ γ ^ k * ‖V - Vinf‖ := by
  have hb := (theorem_3_1 M γ hγ0 hγ1 hp1 MF hMF).2
  let f := MF ∘ BertsekasDiscountedBellmanOp M γ
  have hc : ContractingWith ⟨γ, hγ0⟩ f := by
    refine ⟨hγ1, LipschitzWith.of_dist_le_mul ?_⟩
    intro V W
    change ‖MF (BertsekasDiscountedBellmanOp M γ V) - MF (BertsekasDiscountedBellmanOp M γ W)‖ ≤ γ * ‖V-W‖
    exact hb V W
  refine ⟨hc.fixedPoint f, hc.tendsto_iterate_fixedPoint, ?_⟩
  intro V k
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      ‖f^[k+1] V - hc.fixedPoint f‖ = ‖f (f^[k] V) - f (hc.fixedPoint f)‖ := by
        rw [Function.iterate_succ_apply', hc.fixedPoint_isFixedPt.eq]
      _ ≤ γ * ‖f^[k] V - hc.fixedPoint f‖ := hb _ _
      _ ≤ γ * (γ^k * ‖V - hc.fixedPoint f‖) := mul_le_mul_of_nonneg_left ih hγ0
      _ = γ^(k+1) * ‖V - hc.fixedPoint f‖ := by ring


