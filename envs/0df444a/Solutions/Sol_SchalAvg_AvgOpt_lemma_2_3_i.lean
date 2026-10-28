-- Prove2me | solution 1 for SchalAvg.AvgOpt.lemma_2_3_i
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T09:45:18.801205+00:00
-- url     : https://prove2.me/submissions/d56795df-3e35-4731-860e-ad3ea34012c0

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergLiang.ACOE

namespace SAlem23i

lemma key {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (μs : ℕ → Measure X)
    (hμ : ∀ B : Set X, MeasurableSet B → Tendsto (fun n => μs n B) atTop (𝓝 (μ B)))
    {h : X → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ x, h x ∂μ ≤ liminf (fun n => ∫⁻ x, h x ∂(μs n)) atTop := by
  rw [lintegral_eq_iSup_eapprox_lintegral hh]
  apply iSup_le
  intro n
  set s := SimpleFunc.eapprox h n
  have ht : Tendsto (fun k => s.lintegral (μs k)) atTop (𝓝 (s.lintegral μ)) := by
    unfold SimpleFunc.lintegral
    apply tendsto_finsetSum
    intro c hc
    obtain ⟨a, rfl⟩ := SimpleFunc.mem_range.1 hc
    exact ENNReal.Tendsto.const_mul (hμ _ (s.measurableSet_preimage _))
      (Or.inr (SimpleFunc.eapprox_lt_top h n a).ne)
  rw [← ht.liminf_eq]
  apply liminf_le_liminf _ (by isBoundedDefault) (by isBoundedDefault)
  refine Eventually.of_forall (fun k => ?_)
  rw [← SimpleFunc.lintegral_eq_lintegral]
  apply lintegral_mono
  intro a
  rw [← SimpleFunc.iSup_eapprox_apply hh a]
  exact le_iSup (fun n => SimpleFunc.eapprox h n a) n

theorem main {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (μs : ℕ → Measure X)
    (hμ : ∀ B : Set X, MeasurableSet B → Tendsto (fun n => μs n B) atTop (𝓝 (μ B)))
    (w : ℕ → X → ℝ≥0∞) (hw : ∀ n, Measurable (w n)) :
    ∫⁻ x, liminf (fun n => w n x) atTop ∂μ ≤
      liminf (fun n => ∫⁻ x, w n x ∂(μs n)) atTop := by
  set g := fun m x => ⨅ k ≥ m, w k x with hgdef
  have hg : ∀ m, Measurable (g m) := fun m =>
    Measurable.iInf (fun k => Measurable.iInf (fun _ => hw k))
  have hmono : Monotone g := fun m m' hmm' x =>
    biInf_mono (fun k hk => le_trans hmm' hk)
  have e : ∀ x, liminf (fun n => w n x) atTop = ⨆ m, g m x := fun x =>
    liminf_eq_iSup_iInf_of_nat
  simp_rw [e]
  rw [lintegral_iSup hg hmono]
  apply iSup_le
  intro m
  refine (key μ μs hμ (hg m)).trans ?_
  apply liminf_le_liminf _ (by isBoundedDefault) (by isBoundedDefault)
  filter_upwards [eventually_ge_atTop m] with n hn
  exact lintegral_mono (fun x => iInf₂_le n hn)

end SAlem23i

theorem solution {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (μs : ℕ → Measure X) [∀ n, IsProbabilityMeasure (μs n)]
    (hμ : ∀ B : Set X, MeasurableSet B → Tendsto (fun n => μs n B) atTop (𝓝 (μ B)))
    (w : ℕ → X → ℝ≥0∞) (hw : ∀ n, Measurable (w n)) :
    ∫⁻ x, liminf (fun n => w n x) atTop ∂μ ≤
      liminf (fun n => ∫⁻ x, w n x ∂(μs n)) atTop :=
  SAlem23i.main μ μs hμ w hw
