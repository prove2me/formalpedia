-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitConjSum_conjPt_eq_iff_c88f58f58153
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:45:37.949622+00:00
-- url     : https://prove2.me/submissions/eba1fb75-ca5d-4eca-be91-fa8a8ad7e44c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitConjSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitConjSumLemmas
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitConjSum_conj_chart_ne_zero_edf026820d33

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitConjSum
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.OrbitConjSum
theorem _root_.solution (x : Cone n (AlgebraicClosure ℚ)) (hx : BlockNonzero x)
    (c : (k : ι) → Fin (n k + 1)) (hc : ∀ k, x k (c k) ≠ 0) (σ σ' : coordField x →+* ℂ) :
    conjPt x hx σ = conjPt x hx σ' ↔ ∀ p, σ (ratio x c p) = σ' (ratio x c p) := by
  have hne := conj_chart_ne_zero x c hc
  constructor
  · intro h p
    let R : projPts (ι := blockIdx n) (orbitIdeal x) → Coord n → ℂ :=
      Quot.lift (fun z ↦ fun p ↦ (z : Coord n → ℂ) p / (z : Coord n → ℂ) ⟨p.1, c p.1⟩)
        (by
          rintro z z' ⟨a, ha, e⟩
          funext p
          simp only [e]
          exact (mul_div_mul_left _ _ (ha p.1)).symm)
    have := congrFun (congrArg R h) p
    rw [ratio, map_div₀, map_div₀]
    exact this
  · intro h
    refine Quot.sound ⟨fun k ↦ σ' (coordVec x k (c k)) / σ (coordVec x k (c k)),
      fun k ↦ div_ne_zero (hne σ' k) (hne σ k), funext fun p ↦ ?_⟩
    have e := h p
    rw [ratio, map_div₀, map_div₀, div_eq_div_iff (hne σ p.1) (hne σ' p.1)] at e
    show σ' (coordVec x p.1 p.2) =
      σ' (coordVec x p.1 (c p.1)) / σ (coordVec x p.1 (c p.1)) * σ (coordVec x p.1 p.2)
    rw [div_mul_eq_mul_div, eq_div_iff (hne σ p.1)]
    linear_combination -e
end GroundTheory.Heights₂.Heights.OrbitConjSum
