-- Prove2me | solution 1 for PoSShares.Stability.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:31:11.659361+00:00
-- url     : https://prove2.me/submissions/7891f21f-73f9-4238-a92d-41dafa7b82b7

import Mathlib
import Definitions.Def_PoSShares_Stability_Model
import Definitions.Def_PoSShares_Stability_VarianceSeq

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology PoSShares.Stability

theorem stab_cs_succ (N₀ : ℝ) (R : ℕ → ℝ) (t : ℕ) :
    coinSupply N₀ R (t + 1) = coinSupply N₀ R t + R (t + 1) := by
  unfold coinSupply
  rw [Finset.sum_Icc_succ_top (by omega)]
  ring

theorem stab_cs_pos {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (t : ℕ) :
    0 < coinSupply M.N₀ M.R t := by
  induction t with
  | zero => simpa [coinSupply] using M.N₀_pos
  | succ t ih => rw [stab_cs_succ]; linarith [M.R_nonneg (t + 1)]

theorem stab_coins_bd {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (t : ℕ) (ω : Ω) :
    0 ≤ coins M t ω ∧ coins M t ω ≤ coinSupply M.N₀ M.R t := by
  induction t with
  | zero => simpa [coins, coinSupply] using ⟨M.n₀_nonneg, M.n₀_le⟩
  | succ t ih =>
    have hR := M.R_nonneg (t + 1)
    have hξ := M.ξ_mem (t + 1) ω
    show 0 ≤ coins M t ω + M.R (t + 1) * M.ξ (t + 1) ω ∧
      coins M t ω + M.R (t + 1) * M.ξ (t + 1) ω ≤ coinSupply M.N₀ M.R (t + 1)
    rw [stab_cs_succ]
    rcases hξ with h | h <;> rw [h] <;> constructor <;> nlinarith [ih.1, ih.2]

theorem stab_share_bd {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (t : ℕ) (ω : Ω) :
    0 ≤ share M t ω ∧ share M t ω ≤ 1 := by
  have h := stab_coins_bd M t ω
  have hp := stab_cs_pos M t
  unfold share
  exact ⟨div_nonneg h.1 hp.le, (div_le_one hp).2 h.2⟩

theorem stab_coins_sm {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (t : ℕ) :
    StronglyMeasurable[M.ℱ t] (coins M t) := by
  induction t with
  | zero => exact stronglyMeasurable_const
  | succ t ih =>
    have h1 : StronglyMeasurable[M.ℱ (t + 1)] (coins M t) := ih.mono (M.ℱ.mono (Nat.le_succ t))
    exact h1.add (stronglyMeasurable_const.mul (M.ξ_meas (t + 1)))

theorem stab_share_sm {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (t : ℕ) :
    StronglyMeasurable[M.ℱ t] (share M t) := by
  have : share M t = (coinSupply M.N₀ M.R t)⁻¹ • coins M t := by
    funext ω; simp [share, div_eq_inv_mul]
  rw [this]
  exact (stab_coins_sm M t).const_smul _

theorem stab_share_sm0 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (t : ℕ) :
    StronglyMeasurable (share M t) := (stab_share_sm M t).mono (M.ℱ.le t)

theorem stab_xi_sm0 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (t : ℕ) :
    StronglyMeasurable (M.ξ t) := (M.ξ_meas t).mono (M.ℱ.le t)

theorem stab_integrable_of_bd {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → ℝ) (hf : StronglyMeasurable f) (C : ℝ) (hC : ∀ ω, |f ω| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun ω => by simpa using hC ω)

theorem stab_share_int {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (M : Model Ω) (t : ℕ) : Integrable (share M t) μ :=
  stab_integrable_of_bd μ _ (stab_share_sm0 M t) 1 fun ω => by
    have := stab_share_bd M t ω
    rw [abs_of_nonneg this.1]; exact this.2

theorem stab_xi_int {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (M : Model Ω) (t : ℕ) : Integrable (M.ξ t) μ :=
  stab_integrable_of_bd μ _ (stab_xi_sm0 M t) 1 fun ω => by
    rcases M.ξ_mem t ω with h | h <;> simp [h]

theorem stab_share_succ_eq {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (t : ℕ) (ω : Ω) :
    share M (t + 1) ω = (1 - M.R (t + 1) / coinSupply M.N₀ M.R (t + 1)) * share M t ω +
      M.R (t + 1) / coinSupply M.N₀ M.R (t + 1) * M.ξ (t + 1) ω := by
  have h1 := stab_cs_pos M t
  have h2 := stab_cs_pos M (t + 1)
  have h3 := stab_cs_succ M.N₀ M.R t
  unfold share
  rw [show coins M (t + 1) ω = coins M t ω + M.R (t + 1) * M.ξ (t + 1) ω from rfl]
  rw [h3] at h2 ⊢
  field_simp
  ring

theorem stab_condExp_share_succ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (M : Model Ω) (hPoS : IsPoS μ M) (t : ℕ) :
    μ[share M (t + 1) | M.ℱ t] =ᵐ[μ] share M t := by
  set c : ℝ := M.R (t + 1) / coinSupply M.N₀ M.R (t + 1) with hc
  have hX : share M (t + 1) = (1 - c) • share M t + c • M.ξ (t + 1) := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact stab_share_succ_eq M t ω
  have i1 := stab_share_int μ M t
  have i2 := stab_xi_int μ M (t + 1)
  have e : μ[share M t | M.ℱ t] = share M t :=
    condExp_of_stronglyMeasurable (M.ℱ.le t) (stab_share_sm M t) i1
  rw [hX]
  filter_upwards [condExp_add (μ := μ) (i1.smul (1 - c)) (i2.smul c) (M.ℱ t),
    condExp_smul (μ := μ) (1 - c) (share M t) (M.ℱ t),
    condExp_smul (μ := μ) c (M.ξ (t + 1)) (M.ℱ t), hPoS t] with ω h1 h2 h3 h4
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3 h4 ⊢
  rw [h1, h2, h3, h4, e]
  ring

theorem stab_condVar_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : Model Ω) (hPoS : IsPoS μ M) (t : ℕ) :
    condVar (M.ℱ t) (share M (t + 1)) μ =ᵐ[μ]
      fun ω => (M.R (t + 1) / coinSupply M.N₀ M.R (t + 1)) ^ 2 *
        (share M t ω * (1 - share M t ω)) := by
  set c : ℝ := M.R (t + 1) / coinSupply M.N₀ M.R (t + 1) with hc
  have hce := stab_condExp_share_succ μ M hPoS t
  have i1 := stab_share_int μ M t
  have i2 := stab_xi_int μ M (t + 1)
  have hsm := stab_share_sm M t
  have hbd : ∀ ω, |share M t ω| ≤ 1 := fun ω => by
    have := stab_share_bd M t ω
    rw [abs_of_nonneg this.1]; exact this.2
  -- first rewrite the condVar as a conditional expectation of an explicit function
  have h1 : condVar (M.ℱ t) (share M (t + 1)) μ =ᵐ[μ]
      μ[c ^ 2 • ((fun ω => 1 - 2 * share M t ω) * M.ξ (t + 1) + fun ω => share M t ω ^ 2)
        | M.ℱ t] := by
    unfold condVar
    refine condExp_congr_ae ?_
    filter_upwards [hce] with ω hω
    simp only [Pi.pow_apply, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [hω, stab_share_succ_eq M t ω]
    rcases M.ξ_mem (t + 1) ω with h | h <;> rw [h] <;> ring
  have i3 : Integrable (fun ω => 1 - 2 * share M t ω) μ := (integrable_const _).sub (i1.const_mul 2)
  have i4 : Integrable ((fun ω => 1 - 2 * share M t ω) * M.ξ (t + 1)) μ := by
    refine stab_integrable_of_bd μ _ ((stronglyMeasurable_const.sub ((stab_share_sm0 M t).const_mul 2)).mul (stab_xi_sm0 M (t + 1))) 1 fun ω => ?_
    have := stab_share_bd M t ω
    rcases M.ξ_mem (t + 1) ω with h | h <;> simp only [Pi.mul_apply, h] <;>
      rw [abs_le] <;> constructor <;> nlinarith [this.1, this.2]
  have i5 : Integrable (fun ω => share M t ω ^ 2) μ :=
    stab_integrable_of_bd μ _ ((stab_share_sm0 M t).pow 2) 1 fun ω => by
      have := stab_share_bd M t ω
      rw [abs_of_nonneg (sq_nonneg _)]; nlinarith [this.1, this.2]
  have hm1 : StronglyMeasurable[M.ℱ t] (fun ω => 1 - 2 * share M t ω) :=
    stronglyMeasurable_const.sub (hsm.const_mul 2)
  have e2 : μ[fun ω => share M t ω ^ 2 | M.ℱ t] = fun ω => share M t ω ^ 2 :=
    condExp_of_stronglyMeasurable (M.ℱ.le t) (hsm.pow 2) i5
  refine h1.trans ?_
  filter_upwards [condExp_smul (μ := μ) (c ^ 2)
      ((fun ω => 1 - 2 * share M t ω) * M.ξ (t + 1) + fun ω => share M t ω ^ 2) (M.ℱ t),
    condExp_add (μ := μ) i4 i5 (M.ℱ t),
    condExp_mul_of_stronglyMeasurable_left hm1 i4 i2, hPoS t] with ω h2 h3 h4 h5
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply] at h2 h3 h4 h5 ⊢
  rw [h2, h3, h4, h5, e2]
  ring


theorem stab_key (γ a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hγ : γ ≤ 1) :
    b ^ (γ - 1) + (1 - γ) * b ^ (γ - 2) * (b - a) ≤ a ^ (γ - 1) := by
  have hb2 : b ^ (γ - 2) = b ^ (γ - 1) / b := by
    rw [show γ - 2 = (γ - 1) - 1 by ring, Real.rpow_sub_one hb.ne']
  have hlog : Real.log (a / b) ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at hlog
  have hexp : 1 + (γ - 1) * (Real.log a - Real.log b) ≤
      Real.exp ((γ - 1) * (Real.log a - Real.log b)) := by
    linarith [Real.add_one_le_exp ((γ - 1) * (Real.log a - Real.log b))]
  have hA : a ^ (γ - 1) = b ^ (γ - 1) * Real.exp ((γ - 1) * (Real.log a - Real.log b)) := by
    rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb, ← Real.exp_add]
    congr 1; ring
  have hbp : 0 < b ^ (γ - 1) := Real.rpow_pos_of_pos hb _
  rw [hA, hb2]
  have h1 : (1 - γ) * (1 - a / b) ≤ (γ - 1) * (Real.log a - Real.log b) := by
    nlinarith
  have h2 : 1 + (1 - γ) * (1 - a / b) ≤ Real.exp ((γ - 1) * (Real.log a - Real.log b)) := by
    linarith
  calc b ^ (γ - 1) + (1 - γ) * (b ^ (γ - 1) / b) * (b - a)
      = b ^ (γ - 1) * (1 + (1 - γ) * (1 - a / b)) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 hbp.le

theorem solution (ρ γ N : ℝ) (R : ℕ → ℝ) (hρ : 0 < ρ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (hN : 0 < N)
    (hR : IsPowerReward ρ γ N R) :
    ∀ t : ℕ, 1 ≤ t → aSeq N R (t + 1) ≤ ρ / (1 - γ) * N ^ (γ - 1) := by
  obtain ⟨hγ0, hγ1⟩ := hγ
  have hs : ∀ t, N ≤ coinSupply N R t := by
    intro t
    induction t with
    | zero => simp [coinSupply]
    | succ t ih =>
      have h1 : R (t + 1) = ρ * coinSupply N R t ^ γ := by simpa using hR (t + 1) (by omega)
      have : 0 ≤ R (t + 1) := by
        rw [h1]; exact mul_nonneg hρ.le (Real.rpow_nonneg (by linarith) _)
      rw [stab_cs_succ]; linarith
  have hK : 0 < ρ / (1 - γ) := div_pos hρ (by linarith)
  -- one step
  have hstep : ∀ k, (R (k + 1) / coinSupply N R (k + 1)) ^ 2 ≤
      ρ / (1 - γ) * (coinSupply N R k ^ (γ - 1) - coinSupply N R (k + 1) ^ (γ - 1)) := by
    intro k
    have hsk : 0 < coinSupply N R k := lt_of_lt_of_le hN (hs k)
    have h1 : R (k + 1) = ρ * coinSupply N R k ^ γ := by simpa using hR (k + 1) (by omega)
    have hRpos : 0 < R (k + 1) := by rw [h1]; exact mul_pos hρ (Real.rpow_pos_of_pos hsk _)
    have hsuc := stab_cs_succ N R k
    have hS : 0 < coinSupply N R (k + 1) := by rw [hsuc]; linarith
    have key := stab_key γ (coinSupply N R k) (coinSupply N R (k + 1)) hsk hS hγ1.le
    have hdiff : coinSupply N R (k + 1) - coinSupply N R k = R (k + 1) := by rw [hsuc]; ring
    rw [hdiff] at key
    have hb2 : coinSupply N R (k + 1) ^ (γ - 2) =
        coinSupply N R (k + 1) ^ γ / coinSupply N R (k + 1) ^ 2 := by
      rw [Real.rpow_sub hS, Real.rpow_two]
    rw [hb2] at key
    have hmono : coinSupply N R k ^ γ ≤ coinSupply N R (k + 1) ^ γ :=
      Real.rpow_le_rpow hsk.le (by rw [hsuc]; linarith) hγ0
    have hleft : ρ * (coinSupply N R (k + 1) ^ γ / coinSupply N R (k + 1) ^ 2) * R (k + 1) ≤
        ρ / (1 - γ) * (coinSupply N R k ^ (γ - 1) - coinSupply N R (k + 1) ^ (γ - 1)) := by
      have hpos : 0 < 1 - γ := by linarith
      rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
      nlinarith [mul_le_mul_of_nonneg_left key hρ.le]
    refine le_trans ?_ hleft
    rw [div_pow]
    have hS2 : 0 < coinSupply N R (k + 1) ^ 2 := by positivity
    rw [div_le_iff₀ hS2]
    have : R (k + 1) * R (k + 1) = R (k + 1) * (ρ * coinSupply N R k ^ γ) := by rw [← h1]
    calc R (k + 1) ^ 2 = R (k + 1) * (ρ * coinSupply N R k ^ γ) := by rw [sq, ← h1]
      _ ≤ R (k + 1) * (ρ * coinSupply N R (k + 1) ^ γ) := by
          apply mul_le_mul_of_nonneg_left _ hRpos.le
          exact mul_le_mul_of_nonneg_left hmono hρ.le
      _ = _ := by field_simp
  -- accumulate
  have hacc : ∀ n, aSeq N R n ∈ Set.Icc (0 : ℝ) 1 ∧
      aSeq N R n ≤ ρ / (1 - γ) * (N ^ (γ - 1) - coinSupply N R n ^ (γ - 1)) := by
    intro n
    induction n with
    | zero => simp [aSeq_zero, coinSupply]
    | succ n ih =>
      obtain ⟨⟨h0, h1⟩, h2⟩ := ih
      have hc := hstep n
      have hc0 : 0 ≤ (R (n + 1) / coinSupply N R (n + 1)) ^ 2 := sq_nonneg _
      have hsn : 0 < coinSupply N R n := lt_of_lt_of_le hN (hs n)
      have hsn1 := hstep n
      have hunit : (R (n + 1) / coinSupply N R (n + 1)) ^ 2 ≤ 1 := by
        have hsuc := stab_cs_succ N R n
        have hRn : 0 ≤ R (n + 1) := by
          have h1 : R (n + 1) = ρ * coinSupply N R n ^ γ := by simpa using hR (n + 1) (by omega)
          rw [h1]; exact mul_nonneg hρ.le (Real.rpow_nonneg hsn.le _)
        have hS : 0 < coinSupply N R (n + 1) := by rw [hsuc]; linarith
        have : R (n + 1) / coinSupply N R (n + 1) ≤ 1 := by
          rw [div_le_one hS, hsuc]; linarith
        have h0' : 0 ≤ R (n + 1) / coinSupply N R (n + 1) := div_nonneg hRn hS.le
        nlinarith
      rw [aSeq_succ]
      refine ⟨⟨by nlinarith, by nlinarith⟩, ?_⟩
      nlinarith
  intro t _
  have := (hacc (t + 1)).2
  have hp : 0 ≤ ρ / (1 - γ) * coinSupply N R (t + 1) ^ (γ - 1) :=
    mul_nonneg hK.le (Real.rpow_nonneg (lt_of_lt_of_le hN (hs _)).le _)
  nlinarith
