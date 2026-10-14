-- Prove2me | solution 1 for TPG.theorem_2_clt_and_hac
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T05:17:43.775744+00:00
-- url     : https://prove2.me/submissions/3dda1bf4-a53d-44ec-b35f-debdb3afccab

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Inference
import Theorems.Thm_TPG_lemma_3_clt
import Theorems.Thm_TPG_lemma_4_ideal_hac_consistency
import Theorems.Thm_TPG_lemma_5_feasible_hac_consistency

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open TPG

theorem solution {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (k : ℕ) (γ M v : ℝ) (L : ℕ → ℕ)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hmix : ∀ T : ℕ, E.Mixing T γ) (hM : E.RewardBound M)
    (hvar : E.AsymptoticVariance k v) (hstab : E.MeanStability k) (hL : IsBandwidth L) :
    E.TendstoNormal
        (fun (T : ℕ) (ω : Traj S T) =>
          Real.sqrt (T : ℝ) *
            (tpgEst (1 / 2) T k ω - ∫ ω', tpgEst (1 / 2) T k ω' ∂(E.expLaw T (1 / 2))))
        v
      ∧ E.TendstoInProb (fun (T : ℕ) (ω : Traj S T) => hacEst T k (L T) ω) v := by
  refine ⟨TPG.lemma_3_clt E k γ M v hγ0 hγ1 hmix hM hvar, ?_⟩
  have h4 := TPG.lemma_4_ideal_hac_consistency E k γ M v L hγ0 hγ1 hmix hM hvar hL
  have h5 := TPG.lemma_5_feasible_hac_consistency E k γ M v L hγ0 hγ1 hmix hM hvar hstab hL
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hsum := (h4 (ε / 2) hε2).add (h5 (ε / 2) hε2)
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun T => zero_le) (fun T => ?_)
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have htri : |hacEst T k (L T) ω - v|
      ≤ |E.hacIdeal T k (L T) ω - v|
        + |hacEst T k (L T) ω - E.hacIdeal T k (L T) ω - 0| := by
    have h := abs_add_le (E.hacIdeal T k (L T) ω - v)
      (hacEst T k (L T) ω - E.hacIdeal T k (L T) ω - 0)
    have he : E.hacIdeal T k (L T) ω - v + (hacEst T k (L T) ω - E.hacIdeal T k (L T) ω - 0)
        = hacEst T k (L T) ω - v := by ring
    rw [he] at h
    exact h
  linarith
