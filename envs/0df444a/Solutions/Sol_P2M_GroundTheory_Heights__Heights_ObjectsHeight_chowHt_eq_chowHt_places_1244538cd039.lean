-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsHeight_chowHt_eq_chowHt_places_1244538cd039
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:06:23.335292+00:00
-- url     : https://prove2.me/submissions/ed70bb7d-abfa-4fcf-8046-980d759dde91

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_mahler_eq_chowMean_15919a81f341
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_finsum_log_gaussNorm_2b096fa7246f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_mahler_conjugate_deb3a01dd999
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_sum_embeddings_eq_1d9d079e577f

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] {e δ : ℕ} (H : ArchData K n)
    (S : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hS : ∀ w, IsUnit (S w))
    (hH : ∀ w u, (H.normAt w.embedding).norm u = IndefiniteRowSideFullHecke.ArithBezout.formNorm (S w) u)
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) :
    chowHt H (e + 1) δ f =
      ReciprocityTheory.ChartRestriction.G.Geo.chowHt (fun w => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (S w) (e + 1)) f δ := by
  have hsum := sum_embeddings_eq (fun σ => mahler (H.normAt σ) (e + 1) (f.map σ))
    fun σ => mahler_conjugate _ _ (H.conj_norm σ) σ f
  have hm : ∀ w : InfinitePlace K, mahler (H.normAt w.embedding) (e + 1) (f.map w.embedding) =
      ReciprocityTheory.ChartRestriction.G.Geo.logMean (IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (S w) (e + 1))
        (MvPolynomial.map w.embedding f) :=
    fun w => mahler_eq_chowMean (S w) (hS w) _ (hH w) _
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  unfold chowHt ReciprocityTheory.ChartRestriction.G.Geo.chowHt ReciprocityTheory.ChartRestriction.G.Geo.chowHeightOfForm
  rw [finsum_log_gaussNorm, Finset.sum_add_distrib, hsum, Finset.sum_const, Finset.card_univ,
    NumberField.Embeddings.card K ℂ, NumberField.totalWeight_eq_finrank, nsmul_eq_mul]
  simp_rw [hm]
  field_simp
  push_cast
  ring
end GroundTheory.Heights₂.Heights.ObjectsHeight
