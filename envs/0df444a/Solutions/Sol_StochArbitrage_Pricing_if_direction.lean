-- Prove2me | solution 1 for StochArbitrage.Pricing.if_direction
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T08:13:56.440673+00:00
-- url     : https://prove2.me/submissions/ea68ab42-38ea-466a-8267-70112ff13037

import Mathlib
import Definitions.Def_StochArbitrage_Pricing_Model
import Theorems.Thm_StochArbitrage_Pricing_concavity_bound
import Theorems.Thm_StochArbitrage_Pricing_convexification

open MeasureTheory Matrix
open StochArbitrage.Pricing

theorem solution {N R : ℕ} (M : Market N R) (U : Set (ℝ → ℝ))
    (K : Set (Fin N → ℝ)) (hS : M.Standing U K) :
    (∃ m ∈ convexHull ℝ (sdfSet U K), M.presentValue m ∈ M.polarCone) →
      M.strictSAOSet U K = ∅ := by
  rintro ⟨m, hm, σ, hσ, hq, hσa⟩
  ext δ
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hδ, hpos⟩
  -- the polar-cone price of `δ` is nonpositive
  have h2 : M.presentValue m ⬝ᵥ δ ≤ 0 := by
    rw [hq, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
    calc σ ⬝ᵥ (M.A *ᵥ δ) ≤ σ ⬝ᵥ M.aVec := dotProduct_le_dotProduct_of_nonneg_left hδ hσ
      _ = M.aVec ⬝ᵥ σ := dotProduct_comm _ _
      _ ≤ 0 := hσa
  -- convexification: some single SDF prices `δ` nonpositively
  obtain ⟨m', hm', hle⟩ := (convexification M U K hS δ hδ).1 ⟨m, hm, h2⟩
  obtain ⟨u, hu, κ, hκ, d, hd, rfl⟩ := hm'
  have hpv : M.presentValue (fun x => d * deriv u (x ⬝ᵥ κ)) =
      d • M.presentValue (fun x => deriv u (x ⬝ᵥ κ)) := by
    ext i
    simp only [Market.presentValue, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1; ext x; ring
  rw [hpv, smul_dotProduct, smul_eq_mul] at hle
  -- concavity bound: 0 < D ≤ marginal price
  have h3 := concavity_bound M U K hS u hu κ δ hκ hδ
  have h4 := hpos u hu κ hκ
  nlinarith
