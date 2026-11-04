-- Prove2me | solution 1 for PerishBaseStock.Penalty.proposition_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T23:28:44.612274+00:00
-- url     : https://prove2.me/submissions/636e8bf7-724d-4888-b7a2-401e7171873c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PerishBaseStock_Penalty_lemma_6
import Theorems.Thm_PerishBaseStock_Penalty_eq_20
import Mathlib.Topology.Algebra.Order.LiminfLimsup
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
noncomputable section

namespace PerishPenaltyProp3Aux
open PerishBaseStock.Penalty PerishBaseStock.Lifetime

variable {m : ℕ}

lemma topLevel_cont : Continuous (fun x : State m => topLevel x) := by
  unfold topLevel
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

lemma outdate_cont :
    Continuous (fun p : State m × ℝ≥0 × ℝ≥0 => outdate p.1 p.2.1 p.2.2) := by
  unfold outdate firstLevel orderUpTo
  split_ifs
  · exact ((((continuous_apply _).comp continuous_fst).sub
      (NNReal.continuous_coe.comp (continuous_snd.comp continuous_snd))).max continuous_const)
  · exact ((((topLevel_cont.comp continuous_fst).add
      (NNReal.continuous_coe.comp (continuous_fst.comp continuous_snd))).sub
      (NNReal.continuous_coe.comp (continuous_snd.comp continuous_snd))).max continuous_const)

lemma step_cont :
    Continuous (fun p : State m × ℝ≥0 × ℝ≥0 => step p.1 p.2.1 p.2.2) := by
  refine continuous_pi (fun j => ?_)
  have hla : Continuous (fun p : State m × ℝ≥0 × ℝ≥0 => levelAbove p.1 p.2.1 j) := by
    unfold levelAbove orderUpTo
    split_ifs
    · exact (continuous_apply _).comp continuous_fst
    · exact (topLevel_cont.comp continuous_fst).add
        (NNReal.continuous_coe.comp (continuous_fst.comp continuous_snd))
  exact ((hla.sub (NNReal.continuous_coe.comp (continuous_snd.comp continuous_snd))).sub
    outdate_cont).max continuous_const

lemma run_meas (π : Policy m) (t : ℕ) :
    Measurable (fun d : CappedBaseStock.DemandPath => PerishBaseStock.Penalty.run π d t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have h : Measurable (fun d : CappedBaseStock.DemandPath =>
        (PerishBaseStock.Penalty.run π d t, π.φ t (PerishBaseStock.Penalty.run π d t), d t)) :=
      ih.prodMk (((π.measurable_φ t).comp ih).prodMk (measurable_pi_apply t))
    exact step_cont.measurable.comp h

lemma outdated_meas (π : Policy m) (t : ℕ) :
    Measurable (fun d : CappedBaseStock.DemandPath => PerishBaseStock.Penalty.outdated π d t) := by
  have h : Measurable (fun d : CappedBaseStock.DemandPath =>
      (PerishBaseStock.Penalty.run π d t, π.φ t (PerishBaseStock.Penalty.run π d t), d t)) :=
    (run_meas π t).prodMk (((π.measurable_φ t).comp (run_meas π t)).prodMk (measurable_pi_apply t))
  exact outdate_cont.measurable.comp h

end PerishPenaltyProp3Aux

open PerishBaseStock.Penalty PerishPenaltyProp3Aux in
theorem solution (c : Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw)
    (hP : DemandBounded P) :
    ENNReal.ofReal (c.h * LostSalesOrderUpTo.Asymptotic.expectedHolding P.law (floorLevel c P)) +
        ENNReal.ofReal c.θ * avgOutdating c P (floorLevel c P) ≤ OPT c P := by
  obtain ⟨π, hopt, hfl⟩ := lemma_6 c hc P hP
  rw [← hopt]
  set Sl := floorLevel c P with hSl
  set K := ENNReal.ofReal (c.h * LostSalesOrderUpTo.Asymptotic.expectedHolding P.law Sl) with hKdef
  set θ' := ENNReal.ofReal c.θ with hθ'
  set σ := baseStockPolicy c.m Sl with hσ
  have hmp := fun t => measurePreserving_eval_infinitePi (fun _ : ℕ => P.law) t
  have hK : ∀ t, ∫⁻ d, ENNReal.ofReal c.h * ENNReal.ofReal (max ((Sl : ℝ) - (d t : ℝ)) 0)
      ∂CappedBaseStock.demandPathLaw P = K := by
    intro t
    have hmeas : Measurable (fun x : ℝ≥0 => ENNReal.ofReal (max ((Sl : ℝ) - (x : ℝ)) 0)) := by
      fun_prop
    rw [lintegral_const_mul _ (by fun_prop)]
    unfold CappedBaseStock.demandPathLaw
    have hcm := (hmp t).lintegral_comp hmeas
    dsimp only [Function.eval] at hcm
    have hint : Integrable (fun x : ℝ≥0 => max ((Sl : ℝ) - (x : ℝ)) 0) P.law := by
      refine Integrable.mono' (integrable_const |(Sl : ℝ)|) ?_ (Eventually.of_forall (fun x => ?_))
      · exact ((continuous_const.sub NNReal.continuous_coe).max continuous_const).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by have := NNReal.coe_nonneg x; have := le_abs_self (Sl : ℝ); linarith)
          (abs_nonneg _)
    rw [hcm, ← ofReal_integral_eq_lintegral_ofReal hint
        (Eventually.of_forall (fun _ => le_max_right _ _)),
      ← ENNReal.ofReal_mul hc.h_pos.le]
    rfl
  have hper : ∀ t, K + θ' * ∫⁻ d, ENNReal.ofReal (outdated π d t) ∂CappedBaseStock.demandPathLaw P ≤
      ∫⁻ d, periodCost c π d t ∂CappedBaseStock.demandPathLaw P := by
    intro t
    rw [← hK t, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_add_left (by fun_prop)]
    apply lintegral_mono
    intro d
    show ENNReal.ofReal c.h * ENNReal.ofReal (max ((Sl : ℝ) - (d t : ℝ)) 0) +
      θ' * ENNReal.ofReal (outdated π d t) ≤ periodCost c π d t
    unfold periodCost
    have h1 : ENNReal.ofReal (max ((Sl : ℝ) - (d t : ℝ)) 0) ≤
        ENNReal.ofReal (max (totalLevel π d t - (d t : ℝ)) 0) :=
      ENNReal.ofReal_le_ofReal (max_le_max (by linarith [hfl d t]) le_rfl)
    calc _ ≤ ENNReal.ofReal c.h * ENNReal.ofReal (max (totalLevel π d t - (d t : ℝ)) 0) +
          θ' * ENNReal.ofReal (outdated π d t) := by gcongr
      _ ≤ _ := by rw [add_right_comm]; exact le_self_add
  have hnn : ∀ (ρ : PerishBaseStock.Lifetime.Policy c.m) d t, 0 ≤ outdated ρ d t := by
    intro ρ d t
    unfold outdated PerishBaseStock.Lifetime.outdate
    exact le_max_right _ _
  have hsum : ∀ T : ℕ, ∑ t ∈ Finset.range (T + 1), ∫⁻ d, ENNReal.ofReal (outdated σ d t)
      ∂CappedBaseStock.demandPathLaw P ≤ ∑ t ∈ Finset.range (T + 1), ∫⁻ d,
        ENNReal.ofReal (outdated π d t) ∂CappedBaseStock.demandPathLaw P := by
    intro T
    rw [← lintegral_finsetSum _ (fun t _ => (outdated_meas σ t).ennreal_ofReal),
      ← lintegral_finsetSum _ (fun t _ => (outdated_meas π t).ennreal_ofReal)]
    apply lintegral_mono
    intro d
    show ∑ t ∈ Finset.range (T + 1), ENNReal.ofReal (outdated σ d t) ≤
      ∑ t ∈ Finset.range (T + 1), ENNReal.ofReal (outdated π d t)
    rw [← ENNReal.ofReal_sum_of_nonneg (fun t _ => hnn σ d t),
      ← ENNReal.ofReal_sum_of_nonneg (fun t _ => hnn π d t)]
    exact ENNReal.ofReal_le_ofReal (eq_20 c hc P π d (hfl d) (T + 1) (by omega))
  unfold policyCost avgOutdating longRunAverage
  rw [← ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top,
    ← limsup_const_add atTop _ K (by isBoundedDefault) (by isBoundedDefault)]
  apply limsup_le_limsup (Eventually.of_forall (fun T => ?_)) (by isBoundedDefault)
    (by isBoundedDefault)
  have hT0 : ((T : ℝ≥0∞) + 1) ≠ 0 := by positivity
  have hTt : ((T : ℝ≥0∞) + 1) ≠ ⊤ := by simp
  have hpt : ∀ a : ℕ → ℝ≥0∞, (∑ t ∈ Finset.range (T + 1), (K + θ' * a t)) / ((T : ℝ≥0∞) + 1) =
      K + θ' * ((∑ t ∈ Finset.range (T + 1), a t) / ((T : ℝ≥0∞) + 1)) := by
    intro a
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.mul_sum, ENNReal.add_div]
    congr 1
    · push_cast
      rw [mul_comm]; exact ENNReal.mul_div_cancel_right hT0 hTt
    · exact mul_div_assoc _ _ _
  show K + θ' * ((∑ t ∈ Finset.range (T + 1), ∫⁻ d, ENNReal.ofReal (outdated σ d t)
      ∂CappedBaseStock.demandPathLaw P) / ((T : ℝ≥0∞) + 1)) ≤ _
  rw [← hpt]
  apply ENNReal.div_le_div_right
  calc ∑ t ∈ Finset.range (T + 1), (K + θ' * ∫⁻ d, ENNReal.ofReal (outdated σ d t)
        ∂CappedBaseStock.demandPathLaw P)
      ≤ ∑ t ∈ Finset.range (T + 1), (K + θ' * ∫⁻ d, ENNReal.ofReal (outdated π d t)
        ∂CappedBaseStock.demandPathLaw P) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hsum T) zero_le)
    _ ≤ _ := Finset.sum_le_sum (fun t _ => hper t)
