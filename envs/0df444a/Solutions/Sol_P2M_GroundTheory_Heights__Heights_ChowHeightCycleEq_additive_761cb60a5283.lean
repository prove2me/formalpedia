-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_additive_761cb60a5283
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:19:00.520386+00:00
-- url     : https://prove2.me/submissions/4a672a13-5ea1-482c-bf77-1d9461c45f43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ArchOfPlacesEmbedding
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_chowHt_sub_57687e4dc03a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_formNorm_one_star_7a2447a07dfa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_additive_of_conjInv_805252a1c276
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_meanShift_mul_d1c5c8b18f4b

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
open MvPolynomial MeasureTheory NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.ChowHeightCycleEq
variable {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChowHeightCycleEq
theorem _root_.solution (hA : ChowHeightMul.Statement) {K : Type} [Field K] [NumberField K]
    (S : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hS : ∀ w, IsUnit (S w))
    (f g : MvPolynomial (Fin (e + 1) × Fin n) K) (δ₁ δ₂ : ℕ) (hf : f ≠ 0) (hg : g ≠ 0) :
    ReciprocityTheory.ChartRestriction.G.Geo.chowHt (fun w => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (S w) (e + 1)) (f * g)
        (δ₁ + δ₂) =
      ReciprocityTheory.ChartRestriction.G.Geo.chowHt (fun w => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (S w) (e + 1)) f δ₁ +
        ReciprocityTheory.ChartRestriction.G.Geo.chowHt (fun w => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (S w) (e + 1)) g δ₂ := by
  classical
  let T : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ := fun w => if w.IsReal then 1 else S w
  have hT : ∀ w, IsUnit (T w) := by
    intro w
    by_cases h : w.IsReal
    · simp only [T, if_pos h]; exact isUnit_one
    · simp only [T, if_neg h]; exact hS w
  have hTr : ∀ w : InfinitePlace K, w.IsReal → ∀ u,
      IndefiniteRowSideFullHecke.ArithBezout.formNorm (T w) (star u) = IndefiniteRowSideFullHecke.ArithBezout.formNorm (T w) u := by
    intro w hw u
    simp only [T, if_pos hw]
    exact formNorm_one_star u
  have hsplit : ∀ (P : MvPolynomial (Fin (e + 1) × Fin n) K) (δ : ℕ),
      ReciprocityTheory.ChartRestriction.G.Geo.chowHt (fun w => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (S w) (e + 1)) P δ =
        ReciprocityTheory.ChartRestriction.G.Geo.chowHt (fun w => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (T w) (e + 1)) P δ +
          (∑ w : InfinitePlace K, (w.mult : ℝ) *
            (ReciprocityTheory.ChartRestriction.G.Geo.logMean (IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (S w) (e + 1))
                (map w.embedding P) -
              ReciprocityTheory.ChartRestriction.G.Geo.logMean (IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (T w) (e + 1))
                (map w.embedding P))) / Height.totalWeight K := by
    intro P δ
    rw [← chowHt_sub]
    ring
  have hterm : ∀ w : InfinitePlace K,
      (w.mult : ℝ) *
          (ReciprocityTheory.ChartRestriction.G.Geo.logMean (IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (S w) (e + 1))
              (map w.embedding (f * g)) -
            ReciprocityTheory.ChartRestriction.G.Geo.logMean (IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (T w) (e + 1))
              (map w.embedding (f * g))) =
        (w.mult : ℝ) *
            (ReciprocityTheory.ChartRestriction.G.Geo.logMean (IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (S w) (e + 1))
                (map w.embedding f) -
              ReciprocityTheory.ChartRestriction.G.Geo.logMean (IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (T w) (e + 1))
                (map w.embedding f)) +
          (w.mult : ℝ) *
            (ReciprocityTheory.ChartRestriction.G.Geo.logMean (IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (S w) (e + 1))
                (map w.embedding g) -
              ReciprocityTheory.ChartRestriction.G.Geo.logMean (IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (T w) (e + 1))
                (map w.embedding g)) := by
    intro w
    by_cases hw : w.IsReal
    · have hm := meanShift_mul hA w.embedding (InfinitePlace.isReal_iff.mp hw) (S w) (hS w) f g hf hg
      simp only [T, if_pos hw]
      unfold meanShift at hm
      rw [hm]
      ring
    · simp only [T, if_neg hw, sub_self, mul_zero, add_zero]
  rw [hsplit (f * g), hsplit f, hsplit g, additive_of_conjInv hA T hT hTr f g δ₁ δ₂ hf hg,
    Finset.sum_congr rfl fun w _ => hterm w, Finset.sum_add_distrib]
  ring
end GroundTheory.Heights₂.Heights.ChowHeightCycleEq
