-- Prove2me | solution 1 for TPG.integral_trajLaw
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T03:50:50.224899+00:00
-- url     : https://prove2.me/submissions/5272f321-932d-44a6-aefa-170828c1c79f

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Markov
import Theorems.Thm_TPG_trajLaw_eq_sum_map

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open TPG

/-- The embedding of a reward vector along a fixed state/action path is measurable. -/
private lemma TPG_measurable_embedPath {S : Type} [MeasurableSpace S] {T : ℕ}
    (x : Fin T → S) (z : Fin T → Bool) :
    Measurable (embedPath x z : (Fin T → ℝ) → Traj S T) := by
  unfold embedPath
  exact measurable_pi_lambda _ fun t =>
    measurable_const.prodMk (measurable_const.prodMk (measurable_pi_apply t))

/-- Path weights are nonnegative when every treatment probability lies in `[0, 1]`. -/
private lemma TPG_pathWeight_nonneg {S : Type} [Fintype S] (E : Env S) (T : ℕ) (q : ℕ → ℝ)
    (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1) (x : Fin T → S) (z : Fin T → Bool) :
    0 ≤ E.pathWeight T q x z := by
  unfold Env.pathWeight
  refine mul_nonneg (mul_nonneg ?_ ?_) ?_
  · refine Finset.prod_nonneg fun t _ => ?_
    split_ifs
    · exact E.ρ_nonneg _
    · exact zero_le_one
  · refine Finset.prod_nonneg fun s _ => Finset.prod_nonneg fun t _ => ?_
    split_ifs
    · exact E.P_nonneg _ _ _ _
    · exact zero_le_one
  · refine Finset.prod_nonneg fun t _ => ?_
    split_ifs
    · exact (hq _).1
    · exact sub_nonneg.2 (hq _).2

theorem solution {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T : ℕ) (q : ℕ → ℝ) (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1)
    (F : Traj S T → ℝ) (hF : Measurable F)
    (hint : ∀ p : (Fin T → S) × (Fin T → Bool),
      Integrable (fun y : Fin T → ℝ => F (embedPath p.1 p.2 y)) (E.rewardLaw p.1 p.2)) :
    Integrable F (E.trajLaw T q)
      ∧ ∫ ω, F ω ∂(E.trajLaw T q)
        = ∑ p : (Fin T → S) × (Fin T → Bool),
            E.pathWeight T q p.1 p.2 * ∫ y, F (embedPath p.1 p.2 y) ∂(E.rewardLaw p.1 p.2) := by
  rw [TPG.trajLaw_eq_sum_map]
  have hI : ∀ p ∈ (Finset.univ : Finset ((Fin T → S) × (Fin T → Bool))),
      Integrable F (ENNReal.ofReal (E.pathWeight T q p.1 p.2) •
        (E.rewardLaw p.1 p.2).map (embedPath p.1 p.2)) := by
    intro p _
    refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
    rw [integrable_map_measure hF.aestronglyMeasurable
      (TPG_measurable_embedPath p.1 p.2).aemeasurable]
    exact hint p
  refine ⟨integrable_finsetSum_measure.2 hI, ?_⟩
  rw [integral_finsetSum_measure hI]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_smul_measure,
    integral_map (TPG_measurable_embedPath p.1 p.2).aemeasurable hF.aestronglyMeasurable,
    ENNReal.toReal_ofReal (TPG_pathWeight_nonneg E T q hq p.1 p.2), smul_eq_mul]
