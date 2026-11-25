-- Prove2me | solution 1 for PandoraKnapsack.Skipping.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:35:14.62281+00:00
-- url     : https://prove2.me/submissions/f15b8208-4225-492d-8fb9-9a80d59c1153

import Theorems.Thm_PandoraKnapsack_Skipping_compiled_dyadic_sampler
import Theorems.Thm_PandoraKnapsack_Skipping_dyadic_plan_spec
import Theorems.Thm_PandoraKnapsack_Skipping_dyadic_sparse_half
import Theorems.Thm_PandoraKnapsack_Skipping_uniformAssignment_law
import Theorems.Thm_PandoraKnapsack_Skipping_alg1Policy_valid
import Theorems.Thm_PandoraKnapsack_Skipping_alg1Utility_bound
import Theorems.Thm_PandoraKnapsack_Skipping_lemma_5_2

open PandoraKnapsack.Skipping MeasureTheory

theorem solution :
    ∃ (P : Program) (k : ℕ), ∀ (n m T : ℕ) (I : Instance n m T), IsValid I →
        (∀ ω : Fin ((inputSize n m T + 2) ^ k) → unitInterval,
          Halted P (run I (extendDraws ω) P ((inputSize n m T + 2) ^ k)) ∧
          ∃ σ : SkipList n m,
            decodeOutput n m (run I (extendDraws ω) P ((inputSize n m T + 2) ^ k)).core.mem =
              some σ ∧ IsSkippingPolicy T σ) ∧
        Integrable (fun ω => skipValue I (outputPolicy I P ((inputSize n m T + 2) ^ k) ω))
          (drawLaw ((inputSize n m T + 2) ^ k)) ∧
        ∀ π : AdaptivePolicy n m,
          adaptValue I π ≤ 32 * ∫ ω, skipValue I (outputPolicy I P ((inputSize n m T + 2) ^ k) ω)
            ∂(drawLaw ((inputSize n m T + 2) ^ k)) := by
  obtain ⟨P,k,hP⟩ := compiled_dyadic_sampler
  refine ⟨P,k,?_⟩
  intro n m T I hI
  let B := (inputSize n m T + 2)^k
  obtain ⟨d,lab,hB,hinj,hsupp,hm⟩ := hP n m T I hI
  obtain ⟨hf,hw,happrox⟩ := dyadic_plan_spec I hI
  have hp (ω : Fin B → unitInterval) :
      outputPolicy I P B ω = alg1Policy (uniformAssignment hB lab (dyadicPlan I) ω) := by
    exact congrArg (fun o => o.getD []) (hm ω).2
  obtain ⟨hInt,hmean⟩ := uniformAssignment_law I _ hf hB lab hinj hsupp
  have hfun : (fun ω => skipValue I (outputPolicy I P B ω)) =
      (fun ω => skipValue I (alg1Policy (uniformAssignment hB lab (dyadicPlan I) ω))) :=
    funext fun ω => congrArg _ (hp ω)
  refine ⟨fun ω => ⟨(hm ω).1,_,(hm ω).2,alg1Policy_valid _⟩, hfun ▸ hInt, ?_⟩
  intro π
  obtain ⟨x,hx,ha⟩ := lemma_5_2 I hI π
  obtain ⟨z,hz,hs,hv⟩ := dyadic_sparse_half I hI T x hx
  have hsparse := happrox z hz hs
  have hround := alg1Utility_bound I hI _ hf (fun i j t _ => hw i j t)
  change adaptValue I π ≤ 32 * ∫ ω, skipValue I (outputPolicy I P B ω) ∂(drawLaw B)
  rw [hfun,hmean]
  linarith
