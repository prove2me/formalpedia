-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsHeight_chowHt_eq_chowHeight_9bf18eb67ddd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:15:52.120802+00:00
-- url     : https://prove2.me/submissions/4e402dba-9c05-427c-ad08-8965be918f15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_mahler_eq_chowMean_15919a81f341
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_finsum_log_gaussNorm_2b096fa7246f

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
open MvPolynomial MeasureTheory NumberField Matrix ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.ObjectsHeight
variable {n : ℕ}
variable {k : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsHeight
theorem _root_.solution {e δ : ℕ} (H : ArchData ℚ n) (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : IsUnit S) (hH : ∀ σ u, (H.normAt σ).norm u = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u)
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℚ) :
    chowHt H (e + 1) δ f = IndefiniteRowSideFullHecke.ArithBezout.chowHeight S f δ := by
  have hσ : ∀ σ : ℚ →+* ℂ, σ = Rat.castHom ℂ := fun σ => Subsingleton.elim _ _
  have hw : Height.totalWeight ℚ = 1 := by
    rw [NumberField.totalWeight_eq_finrank, Module.finrank_self]
  have hmult : (default : InfinitePlace ℚ).mult = 1 := by
    have := NumberField.totalWeight_eq_sum_mult (K := ℚ)
    rw [hw, Fintype.sum_unique] at this
    exact this.symm
  unfold chowHt IndefiniteRowSideFullHecke.ArithBezout.chowHeight ReciprocityTheory.ChartRestriction.G.Geo.chowHt ReciprocityTheory.ChartRestriction.G.Geo.chowHeightOfForm
  rw [finsum_log_gaussNorm, Fintype.sum_subsingleton _ (Rat.castHom ℂ), Fintype.sum_unique,
    hmult, hw, hσ (default : InfinitePlace ℚ).embedding, Module.finrank_self,
    mahler_eq_chowMean S hS _ (hH _)]
  simp only [ReciprocityTheory.ChartRestriction.G.Geo.logMean, IndefiniteRowSideFullHecke.ArithBezout.chowMean]
  push_cast
  ring
end GroundTheory.Heights₂.Heights.ObjectsHeight
