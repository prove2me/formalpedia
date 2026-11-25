-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartCone_eq_zero_iff_f230138033b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:11:38.86706+00:00
-- url     : https://prove2.me/submissions/1dfe58fe-1be0-4fc1-a5de-3d315e355115

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMult
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMultLemmas
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartIncl_injective_5ff86a6625e6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartIncl_chartEval_X_ff9f459061a4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitChartMult
variable {ι : Type} {n : ι → ℕ}
variable (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
variable [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.OrbitChartMult
theorem _root_.solution (hc : ∀ k, x k (c k) ≠ 0) (F : MvPolynomial (Coord n) ℤ) :
    chartCone x c (chartRing x c) F = 0 ↔ F ∈ orbitIdeal x := by
  let σ : MvPolynomial ι (AlgebraicClosure ℚ) →ₐ[AlgebraicClosure ℚ]
      MvPolynomial ι (AlgebraicClosure ℚ) := aeval fun k ↦ C (x k (c k)) * X k
  let σ' : MvPolynomial ι (AlgebraicClosure ℚ) →ₐ[AlgebraicClosure ℚ]
      MvPolynomial ι (AlgebraicClosure ℚ) := aeval fun k ↦ C (x k (c k))⁻¹ * X k
  have hσ : σ'.comp σ = AlgHom.id _ _ := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [σ, σ', AlgHom.comp_apply, aeval_X, map_mul, aeval_C, AlgHom.id_apply,
      algebraMap_eq, ← mul_assoc, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
  have hσi : Function.Injective σ := fun a b h ↦ by
    have := congrArg σ' h
    rwa [← AlgHom.comp_apply, ← AlgHom.comp_apply, hσ, AlgHom.id_apply, AlgHom.id_apply] at this
  have hcomp : (σ.toRingHom.comp (map (chartIncl x c))).comp
      (chartCone x c (chartRing x c)) =
      (Geo.mConeMap (ι := blockIdx n) (flatCone x)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp
    · intro p
      have h1 : chartIncl x c (chartEval x c (X p)) * x p.1 (c p.1) = x p.1 p.2 := by
        rw [chartIncl_chartEval_X, div_mul_cancel₀ _ (hc p.1)]
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, chartCone,
        coe_eval₂Hom, eval₂_X, aeval_X,
        map_mul, map_C, map_X, Algebra.algebraMap_self, RingHom.id_apply, Geo.mConeMap, σ, aeval_C,
        algebraMap_eq, flatCone]
      rw [← mul_assoc, ← C_mul, h1]
  have key : ∀ G, σ (map (chartIncl x c) (chartCone x c (chartRing x c) G)) =
      Geo.mConeMap (ι := blockIdx n) (flatCone x) G := fun G ↦ by
    have := congrArg (fun f ↦ f G) hcomp
    simpa using this
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, ← key]
  constructor
  · intro h
    rw [h, map_zero, map_zero]
  · intro h
    refine map_injective _ (chartIncl_injective x c) (hσi ?_)
    rw [h, map_zero, map_zero]
end GroundTheory.Heights₂.Heights.OrbitChartMult
