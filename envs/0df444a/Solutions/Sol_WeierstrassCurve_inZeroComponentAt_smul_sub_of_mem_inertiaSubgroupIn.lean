-- Prove2me | solution 1 for WeierstrassCurve.inZeroComponentAt_smul_sub_of_mem_inertiaSubgroupIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/a2ba6051-f940-5a97-890b-381315d89a8a

import Theorems.Thm_WeierstrassCurve_exists_criticalCentre_of_multiplicativeReduction
import Theorems.Thm_WeierstrassCurve_not_inZeroComponentAt_some_iff_of_criticalCentre
import Theorems.Thm_ValuationSubring_valuation_map_eq_of_mem_decompositionSubgroup
import Theorems.Thm_WeierstrassCurve_valuation_slope_smul_sub_slope_lt_one
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_sub_of_level_eq_of_branch_eq
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_add_of_antipodal
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_sub
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_smul
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Lie.OfAssociative
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_inZeroComponentAt_smul_sub_of_mem_inertiaSubgroupIn

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution
    (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point, W.InZeroComponentAt A (σ • P - P) := by
  classical
  intro σ hσ P
  have hσD : σ ∈ A.decompositionSubgroup ℚ := by
    obtain ⟨τ, -, hτ⟩ := hσ
    rw [← hτ]; exact τ.2
  have hiso := A.valuation_map_eq_of_mem_decompositionSubgroup hσD
  rcases P with _ | ⟨x, y, h⟩
  ·
    have : σ • (Point.zero : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) - Point.zero = 0 := by
      rw [sub_eq_zero]; rfl
    rw [this]; exact Or.inl rfl
  by_cases hP : W.InZeroComponentAt A (.some x y h)
  ·
    exact W.inZeroComponentAt_sub A (W.inZeroComponentAt_smul A hσD hP) hP
  ·
    obtain ⟨x₀, y₀, hx₀, hy₀, hFy, hFx, hnode, hbad, hfix⟩ :=
      W.exists_criticalCentre_of_multiplicativeReduction hq hΔ hqΔ hqc₄ A hA
    obtain ⟨hσx₀, hσy₀⟩ := hfix σ hσ
    have hX : A.valuation (x - x₀) < 1 :=
      (W.not_inZeroComponentAt_some_iff_of_criticalCentre A hx₀ hy₀ hFy hFx hnode hbad h).mp hP
    obtain ⟨h', hsmul⟩ : ∃ h' : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular (σ x) (σ y),
        σ • (Point.some x y h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) =
          Point.some (σ x) (σ y) h' := ⟨_, rfl⟩
    have hlevσ : A.valuation (σ x - x₀) = A.valuation (x - x₀) := by
      conv_lhs => rw [← hσx₀, ← map_sub]
      exact hiso _
    by_cases hsh : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
        - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (x - x₀) ^ 2
    ·
      obtain ⟨hlev, hbr⟩ := W.valuation_slope_smul_sub_slope_lt_one A hx₀ hy₀ hFy hFx σ hσ hσx₀ hσy₀
        h hX hsh
      have key := (W.inZeroComponentAt_sub_of_level_eq_of_branch_eq A hx₀ hy₀ hFy hFx hnode hbad
        h' h (by rw [hlev]; exact hX) hX hlev (by rw [hlev]; exact hsh) hbr).1
      rw [hsmul]
      exact key
    ·
      push Not at hsh
      have key := W.inZeroComponentAt_add_of_antipodal A hx₀ hy₀ hFy hFx hnode hbad
        h' ((((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.nonsingular_neg ..).mpr h)
        (by rw [hlevσ]; exact hX) (by rw [hlevσ]; exact hsh) hX hsh
      rw [sub_eq_add_neg, hsmul, neg_some]
      exact key

end S_WeierstrassCurve_inZeroComponentAt_smul_sub_of_mem_inertiaSubgroupIn
end P2MW
export P2MW.S_WeierstrassCurve_inZeroComponentAt_smul_sub_of_mem_inertiaSubgroupIn (solution)
