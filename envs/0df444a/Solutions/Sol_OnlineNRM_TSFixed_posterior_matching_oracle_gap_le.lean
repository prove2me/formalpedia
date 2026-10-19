-- Prove2me | solution 1 for OnlineNRM.TSFixed.posterior_matching_oracle_gap_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T14:51:01.417249+00:00
-- url     : https://prove2.me/submissions/23fc0e57-af7c-495a-8d26-d3f7c76ba517
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run
import Definitions.Def_OnlineNRM_TSFixed_OracleEntropy
import Theorems.Thm_ProbabilityTheory_finitePosteriorEntropy_bounds
import Theorems.Thm_OnlineNRM_TSFixed_posterior_matching_entropy_step
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed

theorem solution
    {N K T : ℕ} (hK : 1 ≤ K)
    (p : Fin N → Fin K → ℝ) (dbar : Fin N → ℝ)
    (hp : ∀ i k, 0 ≤ p i k)
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    (F : Kernel (Θ × Fin K) (Fin N → ℝ)) [IsMarkovKernel F]
    (hF : ∀ ρ k, ∀ᵐ x ∂(F (ρ, k)), ∀ i, x i ∈ Set.Icc 0 (dbar i))
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Ω → Θ) (θs : ℕ → Ω → Θ)
    (A : ℕ → Ω → Option (Fin K)) (D : ℕ → Ω → Fin N → ℝ)
    (xsel : Θ → Fin K → ℝ)
    (hθ : Measurable θ) (hθs : ∀ t, Measurable (θs t))
    (hA : ∀ t, Measurable (A t)) (hD : ∀ t, Measurable (D t))
    (hx : Measurable xsel)
    (hx0 : ∀ ρ k, 0 ≤ xsel ρ k)
    (hx1 : ∀ ρ, ∑ k : Fin K, xsel ρ k ≤ 1)
    (hsample : ∀ t < T, ∀ C : Set Θ, MeasurableSet C →
      condProb P (pastSigma θ θs A D t) (θs t ⁻¹' C) =ᵐ[P]
        condProb P (histSigma A D t) (θ ⁻¹' C))
    (hoffer : ∀ t < T, ∀ k : Fin K,
      condProb P (pastSigma θ θs A D t ⊔
          MeasurableSpace.comap (θs t) inferInstance) (A t ⁻¹' {some k}) =ᵐ[P]
        fun ω => xsel (θs t ω) k)
    (hdemand : ∀ t < T, ∀ B : Set (Fin N → ℝ), MeasurableSet B →
      condProb P (pastSigma θ θs A D t ⊔
          MeasurableSpace.comap (θs t) inferInstance ⊔
          MeasurableSpace.comap (A t) inferInstance) (D t ⁻¹' B) =ᵐ[P]
        fun ω => (demandLaw F (θ ω) (A t ω) B).toReal) :
    (∑ t ∈ Finset.range T,
      ∫ ω, lpObj p (meanDemand F (θ ω)) (xsel (θ ω)) -
        lpObj p (meanDemand F (θ ω)) (xsel (θs t ω)) ∂P) ≤
      pmax p dbar *
        Real.sqrt ((T : ℝ) * ((K : ℝ) + 1) * Real.log ((K : ℝ) + 1) / 2) := by
  classical
  -- Entropy is attached to the randomized oracle, rather than to the parameter.
  let w : Ω → Option (Fin K) → ℝ :=
    fun ω a => oracleActionWeights xsel (θ ω) a
  let H : ℕ → ℝ := fun t =>
    finitePosteriorEntropy P (histSigma A D t) w
  let g : ℕ → ℝ := fun t =>
    ∫ ω, lpObj p (meanDemand F (θ ω)) (xsel (θ ω)) -
      lpObj p (meanDemand F (θ ω)) (xsel (θs t ω)) ∂P

  have hw : ∀ a, Measurable (fun ω => w ω a) := by
    intro a
    cases a with
    | none =>
        change Measurable (fun ω => 1 - ∑ k : Fin K, xsel (θ ω) k)
        exact measurable_const.sub
          (Finset.measurable_sum Finset.univ
            (fun k _ => ((measurable_pi_apply k).comp hx).comp hθ))
    | some k =>
        exact ((measurable_pi_apply k).comp hx).comp hθ
  have hw0 : ∀ ω a, 0 ≤ w ω a := by
    intro ω a
    cases a with
    | none => exact sub_nonneg.mpr (hx1 (θ ω))
    | some k => exact hx0 (θ ω) k
  have hw1 : ∀ ω, ∑ a : Option (Fin K), w ω a = 1 := by
    intro ω
    simp [w, oracleActionWeights, Fintype.sum_option]

  have hH : ∀ t, 0 ≤ H t ∧ H t ≤ Real.log ((K : ℝ) + 1) := by
    intro t
    have hm : histSigma A D t ≤ mΩ := by
      unfold histSigma
      exact iSup_le fun s => iSup_le fun _ =>
        sup_le (hA s).comap_le (hD s).comap_le
    simpa only [H, Fintype.card_option, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
      using finitePosteriorEntropy_bounds P (histSigma A D t) hm w hw hw0 hw1

  -- Each step consumes entropy and controls the square of the expected gap.
  have hstep : ∀ t < T,
      0 ≤ H t - H (t + 1) ∧
      (g t) ^ 2 ≤ (pmax p dbar) ^ 2 * (((K : ℝ) + 1) / 2) *
        (H t - H (t + 1)) := by
    intro t ht
    exact posterior_matching_entropy_step hK p dbar hp F hF P θ θs A D xsel t
      hθ hθs hA hD hx hx0 hx1 (hsample t ht) (hoffer t ht) (hdemand t ht)

  -- The demand bound itself forces dbar to be nonnegative.
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure P
  let k₀ : Fin K := ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hK⟩
  obtain ⟨z, hz⟩ := (hF (θ ω₀) k₀).exists
  have hdbar : ∀ i, 0 ≤ dbar i := fun i => (hz i).1.trans (hz i).2
  have hR : 0 ≤ pmax p dbar := by
    have hn : (Finset.univ : Finset (Fin K)).Nonempty :=
      ⟨k₀, Finset.mem_univ _⟩
    rw [pmax, dif_pos hn]
    exact (Finset.sum_nonneg (fun i _ => mul_nonneg (hp i k₀) (hdbar i))).trans
      (Finset.le_sup' (fun k => ∑ i : Fin N, p i k * dbar i) (Finset.mem_univ k₀))

  let C : ℝ := (pmax p dbar) ^ 2 * (((K : ℝ) + 1) / 2)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hcs :
      (∑ t ∈ Finset.range T, g t) ^ 2 ≤
        (∑ t ∈ Finset.range T, C) *
          (∑ t ∈ Finset.range T, (H t - H (t + 1))) := by
    exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range T)
      (fun _ _ => hC)
      (fun t ht => (hstep t (Finset.mem_range.mp ht)).1)
      (fun t ht => (hstep t (Finset.mem_range.mp ht)).2)

  have htel : ∀ n : ℕ,
      (∑ t ∈ Finset.range n, (H t - H (t + 1))) = H 0 - H n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  have htotal :
      (∑ t ∈ Finset.range T, g t) ^ 2 ≤ (T : ℝ) * C * (H 0 - H T) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, htel T] using hcs
  have hent : H 0 - H T ≤ Real.log ((K : ℝ) + 1) := by
    linarith [(hH 0).2, (hH T).1]
  have htotal' :
      (∑ t ∈ Finset.range T, g t) ^ 2 ≤
        (T : ℝ) * C * Real.log ((K : ℝ) + 1) :=
    htotal.trans (mul_le_mul_of_nonneg_left hent
      (mul_nonneg (Nat.cast_nonneg T) hC))

  let B : ℝ := (T : ℝ) * ((K : ℝ) + 1) * Real.log ((K : ℝ) + 1) / 2
  have hlog : 0 ≤ Real.log ((K : ℝ) + 1) :=
    Real.log_nonneg (by
      have hk : (0 : ℝ) ≤ K := Nat.cast_nonneg K
      linarith)
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hsq :
      (∑ t ∈ Finset.range T, g t) ^ 2 ≤
        (pmax p dbar * Real.sqrt B) ^ 2 := by
    calc
      (∑ t ∈ Finset.range T, g t) ^ 2 ≤
          (T : ℝ) * C * Real.log ((K : ℝ) + 1) := htotal'
      _ = (pmax p dbar * Real.sqrt B) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hB]
          dsimp [C, B]
          ring
  exact le_of_sq_le_sq hsq (mul_nonneg hR (Real.sqrt_nonneg B))
