-- Prove2me | solution 1 for StableFA.Discounted.theorem_6_2
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:19:10.613023+00:00
-- url     : https://prove2.me/submissions/a428c4af-ad81-440a-90dd-6953b5d46822

import Mathlib
import Definitions.Def_BertsekasSSPModel
import Definitions.Def_StableFA_Discounted_Setting
import Theorems.Thm_StableFA_Discounted_theorem_2_2_contraction
import Theorems.Thm_StableFA_Discounted_theorem_3_2

open Filter Topology
open StableFA.Discounted


theorem solution {n : ℕ} {C : Type} [Fintype C] (M : BertsekasSSPModel n C)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hp1 : ∀ i, ∀ u ∈ M.U i, ∑ j, M.p i u j = 1)
    (A : Averager n) (Vstar VA : Fin n → ℝ) (ε : ℝ)
    (hV : BertsekasDiscountedBellmanOp M γ Vstar = Vstar)
    (hVA : A.apply VA = VA) (hε : ‖VA - Vstar‖ = ε) :
    ∃ V₀ : Fin n → ℝ,
      (∀ V : Fin n → ℝ,
        Tendsto (fun k => (BertsekasDiscountedBellmanOp M γ ∘ A.apply)^[k] V) atTop (𝓝 V₀)) ∧
      ‖V₀ - Vstar‖ ≤ 2 * γ * ε / (1 - γ) := by
  have hA := (theorem_3_2 A).1
  let f := BertsekasDiscountedBellmanOp M γ ∘ A.apply
  have hb (V W : Fin n → ℝ) : ‖f V-f W‖ ≤ γ * ‖V-W‖ :=
    (theorem_2_2_contraction M γ hγ0 hγ1 hp1 _ _).trans
      (mul_le_mul_of_nonneg_left (hA V W) hγ0)
  have hc : ContractingWith ⟨γ,hγ0⟩ f := by
    refine ⟨hγ1, LipschitzWith.of_dist_le_mul ?_⟩
    intro V W
    change ‖f V-f W‖ ≤ γ * ‖V-W‖
    exact hb V W
  let V₀ := hc.fixedPoint f
  refine ⟨V₀, hc.tendsto_iterate_fixedPoint, ?_⟩
  have hfix : f V₀ = V₀ := hc.fixedPoint_isFixedPt.eq
  have hfit : ‖A.apply Vstar-Vstar‖ ≤ 2*ε := by
    calc
      ‖A.apply Vstar-Vstar‖ ≤ ‖A.apply Vstar-VA‖+‖VA-Vstar‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖A.apply Vstar-A.apply VA‖+ε := by rw [hVA,hε]
      _ ≤ ‖Vstar-VA‖+ε := add_le_add (hA _ _) le_rfl
      _ = 2*ε := by rw [norm_sub_rev, hε]; ring
  have hres : ‖f Vstar-Vstar‖ ≤ 2*γ*ε := by
    calc
      ‖f Vstar-Vstar‖ =
          ‖BertsekasDiscountedBellmanOp M γ (A.apply Vstar)-
            BertsekasDiscountedBellmanOp M γ Vstar‖ := by rw [hV]; rfl
      _ ≤ γ * ‖A.apply Vstar-Vstar‖ := theorem_2_2_contraction M γ hγ0 hγ1 hp1 _ _
      _ ≤ γ * (2*ε) := mul_le_mul_of_nonneg_left hfit hγ0
      _ = 2*γ*ε := by ring
  have herr : ‖V₀-Vstar‖ ≤ γ*‖V₀-Vstar‖ + 2*γ*ε := by
    calc
      ‖V₀-Vstar‖ = ‖f V₀-Vstar‖ := by rw [hfix]
      _ ≤ ‖f V₀-f Vstar‖ + ‖f Vstar-Vstar‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ γ*‖V₀-Vstar‖ + 2*γ*ε := add_le_add (hb _ _) hres
  apply (le_div_iff₀ (by linarith : 0 < 1-γ)).2
  nlinarith
