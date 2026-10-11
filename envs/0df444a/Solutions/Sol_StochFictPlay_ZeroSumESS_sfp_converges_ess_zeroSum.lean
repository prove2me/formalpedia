-- Prove2me | solution 1 for StochFictPlay.ZeroSumESS.sfp_converges_ess_zeroSum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T14:56:30.193991+00:00
-- url     : https://prove2.me/submissions/896f19bc-8388-4add-8c42-05846a99c70a

import Mathlib
import Definitions.Def_StochFictPlay_ZeroSumESS_ChoiceModel
import Definitions.Def_StochFictPlay_ZeroSumESS_Dynamics
import Definitions.Def_StochFictPlay_ZeroSumESS_Game
import Definitions.Def_StochFictPlay_ZeroSumESS_Symmetric

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Filter Topology

namespace GapLib22

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- One-step algebra for the gap function. -/
theorem step_alg (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (L : E →ₗ[ℝ] E) (y c : E) (s : ℝ) :
    B ((1 - s) • y + s • c) (L ((1 - s) • y + s • c)) =
      B y (L y) + s * (B (c - y) (L y) + B y (L (c - y))) + s ^ 2 * B (c - y) (L (c - y)) := by
  simp only [map_add, map_smul, map_sub, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, smul_eq_mul]
  ring

set_option maxHeartbeats 800000 in
theorem gap_tendsto
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hBc : Continuous fun p : E × E => B p.1 p.2) (L : E →ₗ[ℝ] E)
    (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ c d, |B c d| ≤ K * ‖c‖ * ‖d‖)
    (Cf : E → E) (hCc : Continuous Cf) (W : E → ℝ) (hWc : Continuous W)
    (hSG : ∀ π π', W π + B (Cf π) (π' - π) ≤ W π')
    (X : Set E) (hXc : IsCompact X) (hXv : Convex ℝ X) (hCX : ∀ π, Cf π ∈ X)
    (hneg : ∀ a ∈ X, ∀ b ∈ X, B (b - a) (L (b - a)) ≤ 0)
    (π₀ : E) (y p : ℕ → E)
    (hy0 : y 0 = Cf π₀)
    (hyS : ∀ k : ℕ, y (k + 1) = (1 - 1 / ((k : ℝ) + 2)) • y k + (1 / ((k : ℝ) + 2)) • Cf (p k))
    (hκ : Tendsto (fun k => p k - L (y k)) atTop (𝓝 0))
    (hcrit : ∀ x π0, (∀ π, B x π - W π ≤ B x π0 - W π0) → Cf π0 = x) :
    ∀ yb, MapClusterPt yb atTop y → Cf (L yb) = yb := by
  classical
  have hLc : Continuous L := LinearMap.continuous_of_finiteDimensional L
  obtain ⟨R, hR⟩ := hXc.isBounded.exists_norm_le
  obtain ⟨KL, hKL0, hKL⟩ : ∃ KL : ℝ, 0 ≤ KL ∧ ∀ d, ‖L d‖ ≤ KL * ‖d‖ := by
    refine ⟨‖LinearMap.toContinuousLinearMap L‖, norm_nonneg _, fun d => ?_⟩
    exact (LinearMap.toContinuousLinearMap L).le_opNorm d
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hR _ (hCX 0))
  set s : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 2) with hs
  have hs0 : ∀ k, 0 < s k := fun k => by simp only [hs]; positivity
  have hs1 : ∀ k, s k ≤ 1 := fun k => by
    simp only [hs]
    rw [div_le_one (by positivity)]
    have : (0:ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hsT : Tendsto s atTop (𝓝 0) := by
    simp only [hs]
    have : Tendsto (fun k : ℕ => ((k : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    exact tendsto_const_nhds.div_atTop this
  -- y stays in X
  have hyX : ∀ k, y k ∈ X := by
    intro k
    induction k with
    | zero => rw [hy0]; exact hCX _
    | succ k ih =>
      rw [hyS k]
      exact hXv ih (hCX _) (by linarith [hs1 k]) ((hs0 k).le) (by simp)
  -- the V sequence
  obtain ⟨V, hV0, hVS⟩ : ∃ V : ℕ → ℝ, V 0 = B (y 0) π₀ - W π₀ ∧
      ∀ k, V (k + 1) = (1 - s k) * V k + s k * (B (Cf (p k)) (p k) - W (p k)) :=
    ⟨fun n => Nat.rec (B (y 0) π₀ - W π₀) (fun k v => (1 - s k) * v + s k * (B (Cf (p k)) (p k) - W (p k))) n,
      rfl, fun _ => rfl⟩
  have hV : ∀ k π, B (y k) π - W π ≤ V k := by
    intro k
    induction k with
    | zero =>
      intro π
      rw [hV0, hy0]
      have := hSG π₀ π
      rw [map_sub] at this
      linarith
    | succ k ih =>
      intro π
      rw [hVS k, hyS k]
      have h1 := hSG (p k) π
      rw [map_sub] at h1
      have h2 := ih π
      have h3 : (1 - s k) * (B (y k) π - W π) ≤ (1 - s k) * V k :=
        mul_le_mul_of_nonneg_left h2 (by linarith [hs1 k])
      have h4 : s k * (B (Cf (p k)) π - W π) ≤ s k * (B (Cf (p k)) (p k) - W (p k)) :=
        mul_le_mul_of_nonneg_left (by linarith) (hs0 k).le
      have e1 : B ((1 - s k) • y k + s k • Cf (p k)) π =
          (1 - s k) * B (y k) π + s k * B (Cf (p k)) π := by
        simp only [hs, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      have e2 : (1 - 1 / ((k : ℝ) + 2)) = 1 - s k := rfl
      rw [e2] at *
      rw [e1]
      nlinarith [h3, h4]
  set Γ : ℕ → ℝ := fun k => V k + W (L (y k)) - B (y k) (L (y k)) with hΓ
  have hΓ0 : ∀ k, 0 ≤ Γ k := fun k => by
    have := hV k (L (y k))
    simp only [hΓ]; linarith
  -- bounds
  have hCnorm : ∀ π, ‖Cf π‖ ≤ R := fun π => hR _ (hCX π)
  have hynorm : ∀ k, ‖y k‖ ≤ R := fun k => hR _ (hyX k)
  have hLstep : ∀ k, L (y (k + 1)) - L (y k) = s k • L (Cf (p k) - y k) := by
    intro k
    rw [hyS k]
    simp only [hs, map_add, map_smul, map_sub, smul_sub, sub_smul, one_smul]
    abel
  -- r_k tends to 0
  have hr : Tendsto (fun k => Cf (L (y (k + 1))) - Cf (p k)) atTop (𝓝 0) := by
    set K1 : Set E := Metric.cthickening 1 (L '' X) with hK1
    have hK1c : IsCompact K1 := (hXc.image hLc).cthickening
    have hUC : UniformContinuousOn Cf K1 := hK1c.uniformContinuousOn_of_continuous hCc.continuousOn
    have hdiff : Tendsto (fun k => L (y (k + 1)) - p k) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k => L (y (k + 1)) - L (y k)) atTop (𝓝 0) := by
        have : ∀ k, ‖L (y (k + 1)) - L (y k)‖ ≤ s k * (KL * (2 * R)) := by
          intro k
          have e := hLstep k
          rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (hs0 k)]
          have h2 := hKL (Cf (p k) - y k)
          have h3 : ‖Cf (p k) - y k‖ ≤ 2 * R := by
            calc ‖Cf (p k) - y k‖ ≤ ‖Cf (p k)‖ + ‖y k‖ := norm_sub_le _ _
              _ ≤ R + R := add_le_add (hCnorm _) (hynorm _)
              _ = 2 * R := by ring
          have h4 : KL * ‖Cf (p k) - y k‖ ≤ KL * (2 * R) := mul_le_mul_of_nonneg_left h3 hKL0
          calc s k * ‖L (Cf (p k) - y k)‖ ≤ s k * (KL * ‖Cf (p k) - y k‖) :=
                mul_le_mul_of_nonneg_left h2 (hs0 k).le
            _ ≤ s k * (KL * (2 * R)) := mul_le_mul_of_nonneg_left h4 (hs0 k).le
        refine squeeze_zero_norm this ?_
        simpa using hsT.mul_const (KL * (2 * R))
      have h2 := h1.sub hκ
      simp only [sub_zero] at h2
      refine h2.congr (fun k => ?_)
      abel
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuousOn_iff.1 hUC ε hε
    have hδ' := Metric.tendsto_atTop.1 hdiff (min δ 1 / 2) (by positivity)
    have hκ' := Metric.tendsto_atTop.1 hκ (min δ 1 / 2) (by positivity)
    obtain ⟨N1, hN1⟩ := hδ'
    obtain ⟨N2, hN2⟩ := hκ'
    refine ⟨max N1 N2, fun k hk => ?_⟩
    have hk1 := hN1 k (le_trans (le_max_left _ _) hk)
    have hk2 := hN2 k (le_trans (le_max_right _ _) hk)
    rw [dist_zero_right] at hk1 hk2
    have hmin1 : min δ 1 ≤ δ := min_le_left _ _
    have hmin2 : min δ 1 ≤ 1 := min_le_right _ _
    have hA : L (y (k + 1)) ∈ K1 :=
      Metric.self_subset_cthickening _ ⟨y (k + 1), hyX _, rfl⟩
    have hBm : p k ∈ K1 :=
      Metric.mem_cthickening_of_dist_le (p k) (L (y k)) 1 _ ⟨y k, hyX k, rfl⟩
        (by rw [dist_eq_norm]; linarith)
    have := hδε _ hA _ hBm (by
      rw [dist_eq_norm]; linarith)
    rw [dist_zero_right]
    rw [dist_eq_norm] at this
    exact this

  -- main step
  set ρ : ℕ → ℝ := fun k => 2 * K * R * ‖p k - L (y k)‖ +
      2 * K * KL * R * ‖Cf (L (y (k + 1))) - Cf (p k)‖ + s k * (K * KL * (2 * R) ^ 2) with hρ
  have hstep : ∀ k, Γ (k + 1) ≤ (1 - s k) * Γ k + s k * ρ k := by
    intro k
    obtain ⟨c, hc⟩ : ∃ c, c = Cf (p k) := ⟨_, rfl⟩
    obtain ⟨δ, hδ⟩ : ∃ δ, δ = p k - L (y k) := ⟨_, rfl⟩
    obtain ⟨r, hr'⟩ : ∃ r, r = Cf (L (y (k + 1))) - c := ⟨_, rfl⟩
    have hcX : c ∈ X := hc ▸ hCX _
    have hhneg : B (c - y k) (L (c - y k)) ≤ 0 := hneg _ (hyX k) _ hcX
    have hπ' : L (y (k + 1)) - L (y k) = s k • L (c - y k) := by rw [hc]; exact hLstep k
    have e1 : L (y k) - L (y (k + 1)) = -(s k • L (c - y k)) := by rw [← hπ']; abel
    have e2 : Cf (L (y (k + 1))) = c + r := by rw [hr']; abel
    have hq := step_alg B L (y k) c (s k)
    have hyk : y (k + 1) = (1 - s k) • y k + s k • c := by rw [hc]; exact hyS k
    rw [← hyk] at hq
    have hp : p k = L (y k) + δ := by rw [hδ]; abel
    have hV' : V (k + 1) = (1 - s k) * V k + s k * (B c (p k) - W (p k)) := by rw [hc]; exact hVS k
    have x1 : B (c - y k) (L (y k)) = B c (L (y k)) - B (y k) (L (y k)) := by
      simp only [map_sub, LinearMap.sub_apply]
    have x2 : B (y k) (L (c - y k)) = B (y k) (L c) - B (y k) (L (y k)) := by
      simp only [map_sub, LinearMap.sub_apply]
    have x3 : B c (L (c - y k)) = B c (L c) - B c (L (y k)) := by
      simp only [map_sub, LinearMap.sub_apply]
    have x4 : B (c - y k) (L (c - y k)) =
        B c (L c) - B c (L (y k)) - B (y k) (L c) + B (y k) (L (y k)) := by
      simp only [map_sub, LinearMap.sub_apply]; ring
    have hBcp : B c (p k) = B c (L (y k)) + B c δ := by rw [hp]; simp only [map_add]
    have F2' : W (L (y (k + 1))) ≤ W (L (y k)) + s k * (B c (L (c - y k)) + B r (L (c - y k))) := by
      have : B (c + r) (-(s k • L (c - y k))) =
          -(s k * (B c (L (c - y k)) + B r (L (c - y k)))) := by
        simp only [map_neg, map_smul, map_add, LinearMap.add_apply, LinearMap.neg_apply,
          LinearMap.smul_apply, smul_eq_mul]
      have F2 := hSG (L (y (k + 1))) (L (y k))
      rw [e1, e2, this] at F2
      linarith
    have F3 := hSG (L (y k)) (p k)
    have e3 : p k - L (y k) = δ := hδ.symm
    rw [e3] at F3
    have hs0k := hs0 k
    have b1 : B c δ ≤ K * R * ‖δ‖ := by
      have := hK c δ
      have h1 : K * ‖c‖ * ‖δ‖ ≤ K * R * ‖δ‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left (hc ▸ hCnorm _) hK0
      linarith [le_abs_self (B c δ)]
    have b2 : W (L (y k)) - W (p k) ≤ K * R * ‖δ‖ := by
      have h1 := hK (Cf (L (y k))) δ
      have h2 : K * ‖Cf (L (y k))‖ * ‖δ‖ ≤ K * R * ‖δ‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left (hCnorm _) hK0
      linarith [neg_abs_le (B (Cf (L (y k))) δ)]
    have hhn : ‖c - y k‖ ≤ 2 * R := by
      calc ‖c - y k‖ ≤ ‖c‖ + ‖y k‖ := norm_sub_le _ _
        _ ≤ R + R := add_le_add (hc ▸ hCnorm _) (hynorm _)
        _ = 2 * R := by ring
    have b3 : B r (L (c - y k)) ≤ K * KL * (2 * R) * ‖r‖ := by
      have h1 := hK r (L (c - y k))
      have h2 : ‖L (c - y k)‖ ≤ KL * (2 * R) :=
        (hKL _).trans (mul_le_mul_of_nonneg_left hhn hKL0)
      have h3 : K * ‖r‖ * ‖L (c - y k)‖ ≤ K * ‖r‖ * (KL * (2 * R)) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg hK0 (norm_nonneg _))
      nlinarith [le_abs_self (B r (L (c - y k)))]
    have b4 : -B (c - y k) (L (c - y k)) ≤ K * KL * (2 * R) ^ 2 := by
      have h1 := hK (c - y k) (L (c - y k))
      have h2 : ‖L (c - y k)‖ ≤ KL * (2 * R) :=
        (hKL _).trans (mul_le_mul_of_nonneg_left hhn hKL0)
      have h3 : K * ‖c - y k‖ * ‖L (c - y k)‖ ≤ K * (2 * R) * (KL * (2 * R)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hhn hK0) h2 (norm_nonneg _)
        positivity
      nlinarith [neg_abs_le (B (c - y k) (L (c - y k)))]
    have m1 := mul_le_mul_of_nonneg_left b1 hs0k.le
    have m2 := mul_le_mul_of_nonneg_left b2 hs0k.le
    have m3 := mul_le_mul_of_nonneg_left b3 hs0k.le
    have m4 := mul_le_mul_of_nonneg_left b4 (sq_nonneg (s k))
    have m5 : s k * B (c - y k) (L (c - y k)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs0k.le hhneg
    have hΓk : Γ (k + 1) = V (k + 1) + W (L (y (k + 1))) - B (y (k + 1)) (L (y (k + 1))) := rfl
    have hΓk' : Γ k = V k + W (L (y k)) - B (y k) (L (y k)) := rfl
    have hρk : ρ k = 2 * K * R * ‖δ‖ + 2 * K * KL * R * ‖r‖ + s k * (K * KL * (2 * R) ^ 2) := by
      show 2 * K * R * ‖p k - L (y k)‖ + 2 * K * KL * R * ‖Cf (L (y (k + 1))) - Cf (p k)‖ +
        s k * (K * KL * (2 * R) ^ 2) = _
      rw [← hδ, ← hc, ← hr']
    rw [hΓk, hΓk', hV', hq, hρk, x1, x2]
    rw [x3] at F2'
    generalize B c (L c) = a3 at *
    generalize B c (L (y k)) = a1 at *
    generalize B (y k) (L c) = a2 at *
    generalize B (y k) (L (y k)) = q at *
    generalize B c δ = bcd at *
    generalize B r (L (c - y k)) = brh at *
    generalize B (c - y k) (L (c - y k)) = bhh at *
    generalize s k = ss at *
    nlinarith [F2', hBcp, m1, m2, m3, m4, m5]
  have hρ0 : ∀ k, 0 ≤ ρ k := fun k => by
    have := hs0 k
    simp only [hρ]; positivity
  have hρT : Tendsto ρ atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => ‖p k - L (y k)‖) atTop (𝓝 0) := by simpa using hκ.norm
    have h2 : Tendsto (fun k => ‖Cf (L (y (k + 1))) - Cf (p k)‖) atTop (𝓝 0) := by
      simpa using hr.norm
    have := ((h1.const_mul (2 * K * R)).add (h2.const_mul (2 * K * KL * R))).add
      (hsT.mul_const (K * KL * (2 * R) ^ 2))
    simpa using this
  have hrec : ∀ k : ℕ, ((k : ℝ) + 2) * Γ (k + 1) ≤ ((k : ℝ) + 1) * Γ k + ρ k := by
    intro k
    have h := hstep k
    have hk2 : ((k : ℝ) + 2) * s k = 1 := by simp only [hs]; field_simp
    have hk3 : ((k : ℝ) + 2) * (1 - s k) = (k : ℝ) + 1 := by rw [mul_sub, hk2]; ring
    calc ((k : ℝ) + 2) * Γ (k + 1) ≤ ((k : ℝ) + 2) * ((1 - s k) * Γ k + s k * ρ k) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = ((k : ℝ) + 1) * Γ k + ρ k := by
          have : ((k : ℝ) + 2) * ((1 - s k) * Γ k + s k * ρ k) =
              (((k : ℝ) + 2) * (1 - s k)) * Γ k + (((k : ℝ) + 2) * s k) * ρ k := by ring
          rw [this, hk3, hk2]; ring
  have hsum : ∀ k : ℕ, ((k : ℝ) + 1) * Γ k ≤ Γ 0 + ∑ j ∈ Finset.range k, ρ j := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have := hrec k
      have e : (((k + 1 : ℕ) : ℝ) + 1) = (k : ℝ) + 2 := by push_cast; ring
      rw [e]
      linarith
  have hΓT : Tendsto Γ atTop (𝓝 0) := by
    have hc := hρT.cesaro
    have h0 : Tendsto (fun k : ℕ => Γ 0 * ((k : ℝ))⁻¹) atTop (𝓝 0) := by
      have := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (Γ 0)
      simpa using this
    refine squeeze_zero' (Eventually.of_forall hΓ0) ?_ (by simpa using h0.add hc)
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have h1 := hsum k
    have hsum0 : 0 ≤ ∑ j ∈ Finset.range k, ρ j := Finset.sum_nonneg (fun j _ => hρ0 j)
    have hG0 := hΓ0 0
    calc Γ k ≤ (Γ 0 + ∑ j ∈ Finset.range k, ρ j) / ((k : ℝ) + 1) := by
          rw [le_div_iff₀ (by positivity)]; linarith
      _ ≤ (Γ 0 + ∑ j ∈ Finset.range k, ρ j) / (k : ℝ) :=
          div_le_div_of_nonneg_left (by linarith) hkpos (by linarith)
      _ = Γ 0 * (k : ℝ)⁻¹ + (k : ℝ)⁻¹ * ∑ j ∈ Finset.range k, ρ j := by
          rw [div_eq_mul_inv]; ring
  intro yb hyb
  apply hcrit yb (L yb)
  intro π
  by_contra hcon
  push_neg at hcon
  set ψ : E → ℝ := fun x => B x π - W π - B x (L x) + W (L x) with hψ
  have hψc : Continuous ψ := by
    have h1 : Continuous fun x => B x π := hBc.comp (continuous_id.prodMk continuous_const)
    have h2 : Continuous fun x => B x (L x) := hBc.comp (continuous_id.prodMk hLc)
    exact ((h1.sub continuous_const).sub h2).add (hWc.comp hLc)
  have hψpos : 0 < ψ yb := by simp only [hψ]; linarith
  have hnb : {x | ψ yb / 2 < ψ x} ∈ 𝓝 yb :=
    (isOpen_lt continuous_const hψc).mem_nhds (by simp only [Set.mem_setOf_eq]; linarith)
  have hfreq := (mapClusterPt_iff_frequently.1 hyb) _ hnb
  have hev : ∀ᶠ k in atTop, Γ k < ψ yb / 2 :=
    hΓT.eventually (gt_mem_nhds (by linarith))
  obtain ⟨k, hk1, hk2⟩ := (hfreq.and_eventually hev).exists
  have := hV k π
  simp only [Set.mem_setOf_eq, hψ, hΓ] at hk1 hk2
  linarith

end GapLib22


set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Rajchman22

variable {Ω : Type*} [MeasurableSpace Ω]

/-- second moment of the partial sums of bounded pairwise orthogonal variables -/
theorem second_moment (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hm : ∀ j, Measurable (X j)) (hb : ∀ j ω, |X j ω| ≤ 1)
    (horth : ∀ i j, i < j → ∫ ω, X i ω * X j ω ∂P = 0) (k : ℕ) :
    ∫ ω, (∑ j ∈ Finset.range k, X j ω) ^ 2 ∂P ≤ k := by
  have hint : ∀ i j, Integrable (fun ω => X i ω * X j ω) P := by
    intro i j
    refine Integrable.of_bound ((hm i).mul (hm j)).aestronglyMeasurable 1 (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [hb i ω, hb j ω, abs_nonneg (X i ω), abs_nonneg (X j ω)]
  have hsq : ∀ ω, (∑ j ∈ Finset.range k, X j ω) ^ 2 =
      ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k, X i ω * X j ω := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
  simp_rw [hsq]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  have hcross : ∀ i j, i ≠ j → ∫ ω, X i ω * X j ω ∂P = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact horth i j h
    · have := horth j i h
      simpa [mul_comm] using this
  have hdiag : ∀ i, ∫ ω, X i ω * X i ω ∂P ≤ 1 := by
    intro i
    have : ∫ ω, X i ω * X i ω ∂P ≤ ∫ ω, (1 : ℝ) ∂P := by
      refine integral_mono (hint i i) (integrable_const _) fun ω => ?_
      nlinarith [hb i ω, abs_nonneg (X i ω), sq_abs (X i ω)]
    simpa using this
  calc ∑ i ∈ Finset.range k, ∫ ω, ∑ j ∈ Finset.range k, X i ω * X j ω ∂P
      = ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k, ∫ ω, X i ω * X j ω ∂P := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum _ (fun j _ => hint i j)]
    _ ≤ ∑ i ∈ Finset.range k, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [Finset.sum_eq_single i]
        · exact hdiag i
        · intro j _ hji; exact hcross i j (Ne.symm hji)
        · intro h; exact absurd hi h
    _ = k := by simp

theorem rajchman (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hm : ∀ j, Measurable (X j)) (hb : ∀ j ω, |X j ω| ≤ 1)
    (horth : ∀ i j, i < j → ∫ ω, X i ω * X j ω ∂P = 0) :
    ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => (1 / (k : ℝ)) * ∑ j ∈ Finset.range k, X j ω) atTop (𝓝 0) := by
  set S : ℕ → Ω → ℝ := fun k ω => ∑ j ∈ Finset.range k, X j ω with hS
  have hSm : ∀ k, Measurable (S k) := fun k => Finset.measurable_sum _ (fun j _ => hm j)
  have hSb : ∀ k ω, |S k ω| ≤ k := by
    intro k ω
    calc |S k ω| ≤ ∑ j ∈ Finset.range k, |X j ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range k, (1 : ℝ) := Finset.sum_le_sum fun j _ => hb j ω
      _ = k := by simp
  have hSd : ∀ k l ω, k ≤ l → |S l ω - S k ω| ≤ (l - k : ℕ) := by
    intro k l ω hkl
    have : S l ω - S k ω = ∑ j ∈ Finset.Ico k l, X j ω := by
      simp only [hS]
      rw [Finset.sum_Ico_eq_sub _ hkl]
    rw [this]
    calc |∑ j ∈ Finset.Ico k l, X j ω| ≤ ∑ j ∈ Finset.Ico k l, |X j ω| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.Ico k l, (1 : ℝ) := Finset.sum_le_sum fun j _ => hb j ω
      _ = (l - k : ℕ) := by simp
  set T : ℕ → Ω → ℝ := fun n ω => (S (n ^ 2) ω / ((n : ℝ) ^ 2)) ^ 2 with hT
  have hT0 : ∀ n ω, 0 ≤ T n ω := fun n ω => sq_nonneg _
  have hTm : ∀ n, Measurable (T n) := fun n => ((hSm _).div_const _).pow_const 2
  have hTb : ∀ n ω, T n ω ≤ 1 := by
    intro n ω
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [hT]
    · have hn : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
      have h1 := hSb (n ^ 2) ω
      have h2 : |S (n ^ 2) ω / (n : ℝ) ^ 2| ≤ 1 := by
        rw [abs_div, abs_of_pos hn, div_le_one hn]
        simpa using h1
      simp only [hT]
      nlinarith [abs_nonneg (S (n ^ 2) ω / (n : ℝ) ^ 2), sq_abs (S (n ^ 2) ω / (n : ℝ) ^ 2)]
  have hTi : ∀ n, Integrable (T n) P := fun n =>
    Integrable.of_bound (hTm n).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hT0 n ω)]; exact hTb n ω)
  have hTint : ∀ n, ∫ ω, T n ω ∂P ≤ 1 / (n : ℝ) ^ 2 := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [hT]
    · have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
      have e : ∀ ω, T n ω = (1 / ((n : ℝ) ^ 2) ^ 2) * (S (n ^ 2) ω) ^ 2 := by
        intro ω; simp only [hT]; rw [div_pow]; ring
      simp_rw [e]
      rw [integral_const_mul]
      have := second_moment P X hm hb horth (n ^ 2)
      have h2 : ∫ ω, (S (n ^ 2) ω) ^ 2 ∂P ≤ ((n ^ 2 : ℕ) : ℝ) := this
      have hpos : (0 : ℝ) ≤ 1 / ((n : ℝ) ^ 2) ^ 2 := by positivity
      calc 1 / ((n : ℝ) ^ 2) ^ 2 * ∫ ω, (S (n ^ 2) ω) ^ 2 ∂P
          ≤ 1 / ((n : ℝ) ^ 2) ^ 2 * ((n ^ 2 : ℕ) : ℝ) := mul_le_mul_of_nonneg_left h2 hpos
        _ = 1 / (n : ℝ) ^ 2 := by push_cast; field_simp
  -- almost sure convergence of T n to 0
  have hsumm : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := Real.summable_one_div_nat_pow.2 (by norm_num)
  have hlint : ∫⁻ ω, ∑' n, ENNReal.ofReal (T n ω) ∂P ≠ ⊤ := by
    rw [lintegral_tsum (fun n => (hTm n).ennreal_ofReal.aemeasurable)]
    have h1 : ∀ n, ∫⁻ ω, ENNReal.ofReal (T n ω) ∂P = ENNReal.ofReal (∫ ω, T n ω ∂P) := by
      intro n
      rw [ofReal_integral_eq_lintegral_ofReal (hTi n) (Eventually.of_forall (hT0 n))]
    simp_rw [h1]
    refine ne_top_of_le_ne_top (b := ∑' n : ℕ, ENNReal.ofReal (1 / (n : ℝ) ^ 2)) ?_ ?_
    · rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsumm]
      exact ENNReal.ofReal_ne_top
    · exact ENNReal.tsum_le_tsum fun n => ENNReal.ofReal_le_ofReal (hTint n)
  have hae1 : ∀ᵐ ω ∂P, ∑' n, ENNReal.ofReal (T n ω) ≠ ⊤ := by
    have hmeas : Measurable fun ω => ∑' n, ENNReal.ofReal (T n ω) :=
      Measurable.ennreal_tsum fun n => (hTm n).ennreal_ofReal
    filter_upwards [ae_lt_top hmeas hlint] with ω hω using hω.ne
  have hae2 : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => S (n ^ 2) ω / (n : ℝ) ^ 2) atTop (𝓝 0) := by
    filter_upwards [hae1] with ω hω
    have h1 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    have h3 : Tendsto (fun n => T n ω) atTop (𝓝 0) := by
      refine (h2.congr fun n => ?_).trans (by simp)
      simp [Function.comp, ENNReal.toReal_ofReal (hT0 n ω)]
    have h4 := (Real.continuous_sqrt.tendsto 0).comp h3
    simp only [Real.sqrt_zero] at h4
    refine tendsto_zero_iff_abs_tendsto_zero _ |>.2 ?_
    refine h4.congr fun n => ?_
    simp only [Function.comp, hT]
    exact Real.sqrt_sq_eq_abs _
  filter_upwards [hae2] with ω hω
  -- interpolation between squares
  set a : ℕ → ℝ := fun n => S (n ^ 2) ω / (n : ℝ) ^ 2 with ha
  have hsq : Tendsto (fun k : ℕ => Nat.sqrt k) atTop atTop := by
    refine tendsto_atTop_atTop.2 fun b => ⟨b ^ 2, fun k hk => ?_⟩
    exact Nat.le_sqrt'.2 hk
  have h1 : Tendsto (fun k : ℕ => a (Nat.sqrt k)) atTop (𝓝 0) := hω.comp hsq
  have h2 : Tendsto (fun k : ℕ => 2 / (Nat.sqrt k : ℝ)) atTop (𝓝 0) := by
    have := ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hsq)
    exact tendsto_const_nhds.div_atTop this
  have hbound : ∀ k : ℕ, 1 ≤ k → |(1 / (k : ℝ)) * S k ω| ≤ |a (Nat.sqrt k)| + 2 / (Nat.sqrt k : ℝ) := by
    intro k hk
    set n := Nat.sqrt k with hn
    have hn1 : 1 ≤ n := Nat.le_sqrt'.2 (by simpa using hk)
    have hnk : n ^ 2 ≤ k := by rw [sq]; exact Nat.sqrt_le k
    have hkn : k < (n + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt k
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
    have hkr : (n : ℝ) ^ 2 ≤ k := by exact_mod_cast hnk
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hd := hSd (n ^ 2) k ω hnk
    have hdn : ((k - n ^ 2 : ℕ) : ℝ) ≤ 2 * n := by
      have h' : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
      have : k - n ^ 2 ≤ 2 * n := by omega
      exact_mod_cast this
    have hdiff : |S k ω - S (n ^ 2) ω| ≤ 2 * n := hd.trans hdn
    have e : (1 / (k : ℝ)) * S k ω = (1 / (k : ℝ)) * S (n ^ 2) ω + (1 / (k : ℝ)) * (S k ω - S (n ^ 2) ω) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / k), ha]
      simp only
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)]
      calc 1 / (k : ℝ) * |S (n ^ 2) ω| ≤ 1 / ((n : ℝ) ^ 2) * |S (n ^ 2) ω| := by
            apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
            exact one_div_le_one_div_of_le (by positivity) hkr
        _ = |S (n ^ 2) ω| / (n : ℝ) ^ 2 := by ring
    · rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / k)]
      calc 1 / (k : ℝ) * |S k ω - S (n ^ 2) ω| ≤ 1 / ((n : ℝ) ^ 2) * (2 * n) := by
            apply mul_le_mul _ hdiff (abs_nonneg _) (by positivity)
            exact one_div_le_one_div_of_le (by positivity) hkr
        _ = 2 / (n : ℝ) := by field_simp
  have h3 : Tendsto (fun k : ℕ => |a (Nat.sqrt k)| + 2 / (Nat.sqrt k : ℝ)) atTop (𝓝 0) := by
    simpa using h1.abs.add h2
  refine squeeze_zero_norm' ?_ h3
  filter_upwards [eventually_ge_atTop 1] with k hk
  rw [Real.norm_eq_abs]
  exact hbound k hk

end Rajchman22


set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StochFictPlay.ZeroSumESS.Aux22

open StochFictPlay.ZeroSumESS

/-- the event that alternative `i` is the strict argmax of `π + e` -/
def Ev {m : ℕ} (π : Fin m → ℝ) (i : Fin m) : Set (Fin m → ℝ) :=
  {e | ∀ j, j ≠ i → π j + e j < π i + e i}

noncomputable abbrev μf {m : ℕ} (f : (Fin m → ℝ) → ℝ≥0∞) : Measure (Fin m → ℝ) :=
  (volume : Measure (Fin m → ℝ)).withDensity f

theorem choiceProb_eq {m : ℕ} (f : (Fin m → ℝ) → ℝ≥0∞) (π : Fin m → ℝ) (i : Fin m) :
    choiceProb f π i = (μf f).real (Ev π i) := rfl

theorem tie_null {n : ℕ} (j k : Fin n) (hjk : k ≠ j) (c : ℝ) :
    (volume : Measure (Fin n → ℝ)) {e | e k - e j = c} = 0 := by
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k -
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j
  have hL : ∀ e, L e = e k - e j := fun e => rfl
  have hne : LinearMap.ker L ≠ ⊤ := by
    intro h
    have hmem : (Pi.single k (1:ℝ) : Fin n → ℝ) ∈ LinearMap.ker L := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hL] at hmem
    simp [Ne.symm hjk] at hmem
  have h0 := Measure.addHaar_submodule (volume : Measure (Fin n → ℝ)) _ hne
  have hset : {e : Fin n → ℝ | e k - e j = c} =
      (fun e => e + (-(c • Pi.single k (1:ℝ)))) ⁻¹' (LinearMap.ker L : Set (Fin n → ℝ)) := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe, LinearMap.mem_ker, hL]
    simp [Ne.symm hjk]
    constructor <;> intro h <;> linarith
  rw [hset, measure_preimage_add_right]
  exact h0

theorem measurableSet_Ev {m : ℕ} (π : Fin m → ℝ) (i : Fin m) : MeasurableSet (Ev π i) := by
  have hAi : Ev π i = ⋂ j, ⋂ (_ : j ≠ i), {e : Fin m → ℝ | π j + e j < π i + e i} := by
    ext e; simp [Ev]
  rw [hAi]
  refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
  exact measurableSet_lt (by fun_prop) (by fun_prop)

theorem isOpen_Ev {m : ℕ} (π : Fin m → ℝ) (i : Fin m) : IsOpen (Ev π i) := by
  have : Ev π i = ⋂ j, {e : Fin m → ℝ | j ≠ i → π j + e j < π i + e i} := by
    ext e; simp [Ev]
  rw [this]
  refine isOpen_iInter_of_finite fun j => ?_
  by_cases h : j = i
  · simp [h]
  · simpa [h] using isOpen_lt (by fun_prop : Continuous fun e : Fin m → ℝ => π j + e j)
      (by fun_prop : Continuous fun e : Fin m → ℝ => π i + e i)

theorem Ev_nonempty {m : ℕ} (π : Fin m → ℝ) (i : Fin m) : (Ev π i).Nonempty := by
  refine ⟨fun j => -π j + if j = i then 1 else 0, ?_⟩
  intro j hj
  simp [hj]

theorem Ev_disjoint {m : ℕ} (π : Fin m → ℝ) {a b : Fin m} (hab : a ≠ b) (e : Fin m → ℝ)
    (ha : e ∈ Ev π a) (hb : e ∈ Ev π b) : False := by
  have h1 := ha b (Ne.symm hab)
  have h2 := hb a hab
  linarith

variable {m : ℕ} {f : (Fin m → ℝ) → ℝ≥0∞}

theorem isProb (hf : IsRegularDensity f) : IsProbabilityMeasure (μf f) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact hf.2.2.2.1

theorem mu_pos (hf : IsRegularDensity f) {U : Set (Fin m → ℝ)} (hU : IsOpen U)
    (hne : U.Nonempty) : 0 < μf f U := by
  have hfm : Measurable f := hf.1
  rw [withDensity_apply _ hU.measurableSet, pos_iff_ne_zero, Ne, lintegral_eq_zero_iff hfm,
    Filter.EventuallyEq, ae_restrict_iff' hU.measurableSet]
  intro h
  have h2 : ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)), x ∉ U := by
    filter_upwards [h] with x hx hxU
    exact (hf.2.1 x).ne' (hx hxU)
  exact (hU.measure_pos volume hne).ne' (measure_eq_zero_iff_ae_notMem.2 h2)

theorem ae_exists_Ev (hf : IsRegularDensity f) (π : Fin m → ℝ) [Nonempty (Fin m)] :
    ∀ᵐ e ∂(μf f), ∃ i, e ∈ Ev π i := by
  have hac : μf f ≪ volume := withDensity_absolutelyContinuous _ _
  have hnull : (volume : Measure (Fin m → ℝ))
      (⋃ j, ⋃ k, {e : Fin m → ℝ | k ≠ j ∧ e k - e j = π j - π k}) = 0 := by
    refine measure_iUnion_null fun j => measure_iUnion_null fun k => ?_
    by_cases hkj : k = j
    · simp [hkj]
    · exact measure_mono_null (fun e he => he.2) (tie_null j k hkj _)
  have h0 := hac hnull
  rw [measure_eq_zero_iff_ae_notMem] at h0
  filter_upwards [h0] with e he
  obtain ⟨j, -, hj⟩ :=
    Finset.exists_max_image Finset.univ (fun l => π l + e l) Finset.univ_nonempty
  refine ⟨j, fun k hkj => ?_⟩
  have hk2 := hj k (Finset.mem_univ _)
  rcases lt_or_eq_of_le hk2 with h | h
  · exact h
  · exact absurd (show e ∈ ⋃ j, ⋃ k, {e : Fin m → ℝ | k ≠ j ∧ e k - e j = π j - π k} from
      Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨k, hkj, by linarith⟩⟩) he

theorem sum_choiceProb (hf : IsRegularDensity f) [Nonempty (Fin m)] (π : Fin m → ℝ) :
    ∑ j, choiceProb f π j = 1 := by
  have := isProb hf
  have hdisj : Pairwise (Function.onFun Disjoint (Ev π)) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    intro e ha hb
    exact Ev_disjoint π hab e ha hb
  have hU : μf f (⋃ i, Ev π i) = 1 := by
    rw [← prob_compl_eq_zero_iff (MeasurableSet.iUnion (measurableSet_Ev π))]
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [ae_exists_Ev hf π] with e he hc
    exact hc (Set.mem_iUnion.2 he)
  rw [measure_iUnion hdisj (measurableSet_Ev π), tsum_fintype] at hU
  simp only [choiceProb_eq, Measure.real]
  rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top _ _), hU, ENNReal.toReal_one]

theorem choiceProb_pos (hf : IsRegularDensity f) (π : Fin m → ℝ) (i : Fin m) :
    0 < choiceProb f π i := by
  have := isProb hf
  rw [choiceProb_eq, Measure.real]
  exact ENNReal.toReal_pos (mu_pos hf (isOpen_Ev π i) (Ev_nonempty π i)).ne'
    (measure_ne_top _ _)

theorem choiceProb_nonneg (π : Fin m → ℝ) (i : Fin m) : 0 ≤ choiceProb f π i :=
  ENNReal.toReal_nonneg

theorem choiceProb_le_one (hf : IsRegularDensity f) [Nonempty (Fin m)] (π : Fin m → ℝ)
    (i : Fin m) : choiceProb f π i ≤ 1 := by
  rw [← sum_choiceProb hf π]
  exact Finset.single_le_sum (fun j _ => choiceProb_nonneg π j) (Finset.mem_univ i)

theorem mem_openSimplex (hf : IsRegularDensity f) [Nonempty (Fin m)] (π : Fin m → ℝ) :
    choiceProb f π ∈ openSimplex m :=
  ⟨fun i => choiceProb_pos hf π i, sum_choiceProb hf π⟩

theorem choiceProb_shift (π : Fin m → ℝ) (c : ℝ) :
    choiceProb f (fun j => π j + c) = choiceProb f π := by
  funext i
  have hE : Ev (fun j => π j + c) i = Ev π i := by
    ext e
    show (∀ j, j ≠ i → (π j + c) + e j < (π i + c) + e i) ↔ (∀ j, j ≠ i → π j + e j < π i + e i)
    constructor
    · intro h j hj; have := h j hj; linarith
    · intro h j hj; have := h j hj; linarith
  simp only [choiceProb_eq, hE]

theorem continuous_choiceProb (hf : IsRegularDensity f) : Continuous (choiceProb f) :=
  hf.2.2.2.2.continuous

/-! ### the potential -/

noncomputable def smax (x : Fin m → ℝ) : ℝ := ⨆ j, x j

theorem le_smax (x : Fin m → ℝ) (j : Fin m) : x j ≤ smax x :=
  le_ciSup (Finite.bddAbove_range x) j

theorem smax_le [Nonempty (Fin m)] {x : Fin m → ℝ} {c : ℝ} (h : ∀ j, x j ≤ c) : smax x ≤ c :=
  ciSup_le h

theorem exists_smax [Nonempty (Fin m)] (x : Fin m → ℝ) : ∃ j, smax x = x j := by
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := x)
  exact ⟨j, hj.symm⟩

theorem smax_add_const [Nonempty (Fin m)] (x : Fin m → ℝ) (c : ℝ) :
    smax (fun j => x j + c) = smax x + c := by
  apply le_antisymm
  · exact smax_le fun j => by linarith [le_smax x j]
  · obtain ⟨j, hj⟩ := exists_smax x
    rw [hj]; exact le_smax (fun j => x j + c) j

theorem smax_mono [Nonempty (Fin m)] {x y : Fin m → ℝ} (h : ∀ j, x j ≤ y j) : smax x ≤ smax y :=
  smax_le fun j => (h j).trans (le_smax y j)

theorem measurable_smax : Measurable (smax : (Fin m → ℝ) → ℝ) := by
  unfold smax
  exact Measurable.iSup fun j => measurable_pi_apply j

noncomputable def phi (π e : Fin m → ℝ) : ℝ := smax (fun j => π j + e j) - smax e

theorem abs_phi_le [Nonempty (Fin m)] (π e : Fin m → ℝ) : |phi π e| ≤ ‖π‖ := by
  have hb : ∀ j, |π j| ≤ ‖π‖ := fun j => by
    have := norm_le_pi_norm π j; rwa [Real.norm_eq_abs] at this
  rw [abs_le]
  constructor
  · have : smax e ≤ smax (fun j => π j + e j) + ‖π‖ := by
      apply smax_le; intro j
      have := le_smax (fun j => π j + e j) j
      have := (abs_le.1 (hb j)).1
      linarith
    unfold phi; linarith
  · have : smax (fun j => π j + e j) ≤ smax e + ‖π‖ := by
      apply smax_le; intro j
      have := le_smax e j
      have := (abs_le.1 (hb j)).2
      linarith
    unfold phi; linarith

theorem measurable_phi (π : Fin m → ℝ) : Measurable (phi π) := by
  unfold phi
  exact (measurable_smax.comp (by fun_prop)).sub measurable_smax

theorem integrable_phi (hf : IsRegularDensity f) [Nonempty (Fin m)] (π : Fin m → ℝ) :
    Integrable (phi π) (μf f) := by
  have := isProb hf
  exact Integrable.of_bound (measurable_phi π).aestronglyMeasurable ‖π‖
    (Eventually.of_forall fun e => by rw [Real.norm_eq_abs]; exact abs_phi_le π e)

/-- the potential `G(π) = E[max(π + ε) - max ε]` -/
noncomputable def G (f : (Fin m → ℝ) → ℝ≥0∞) (π : Fin m → ℝ) : ℝ := ∫ e, phi π e ∂(μf f)

theorem smax_of_Ev [Nonempty (Fin m)] {π e : Fin m → ℝ} {i : Fin m} (h : e ∈ Ev π i) :
    smax (fun j => π j + e j) = π i + e i := by
  apply le_antisymm
  · apply smax_le; intro j
    by_cases hj : j = i
    · subst hj; exact le_rfl
    · exact (h j hj).le
  · exact le_smax (fun j => π j + e j) i

/-- `C π` is a subgradient of `G` at `π`. -/
theorem G_sub (hf : IsRegularDensity f) [Nonempty (Fin m)] (π π' : Fin m → ℝ) :
    choiceProb f π ⬝ᵥ (π' - π) ≤ G f π' - G f π := by
  have := isProb hf
  set g : (Fin m → ℝ) → ℝ := fun e => ∑ i, (Ev π i).indicator (fun _ => π' i - π i) e with hg
  have hgi : ∀ i, Integrable ((Ev π i).indicator (fun _ : Fin m → ℝ => π' i - π i)) (μf f) :=
    fun i => (integrable_const _).indicator (measurableSet_Ev π i)
  have hint : ∫ e, g e ∂(μf f) = choiceProb f π ⬝ᵥ (π' - π) := by
    rw [hg, integral_finsetSum _ (fun i _ => hgi i)]
    simp only [dotProduct, choiceProb_eq, Pi.sub_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_indicator_const _ (measurableSet_Ev π i), smul_eq_mul]
  rw [← hint, G, G, ← integral_sub (integrable_phi hf π') (integrable_phi hf π)]
  refine integral_mono_ae (integrable_finsetSum _ (fun i _ => hgi i))
    ((integrable_phi hf π').sub (integrable_phi hf π)) ?_
  filter_upwards [ae_exists_Ev hf π] with e he
  obtain ⟨i, hi⟩ := he
  have hgv : g e = π' i - π i := by
    rw [hg]
    simp only
    rw [Finset.sum_eq_single i]
    · simp [Set.indicator_of_mem hi]
    · intro j _ hji
      rw [Set.indicator_of_notMem]
      intro hj
      exact Ev_disjoint π hji e hj hi
    · simp
  rw [hgv]
  simp only [Pi.sub_apply, phi]
  rw [smax_of_Ev hi]
  have := le_smax (fun j => π' j + e j) i
  linarith

theorem abs_dot_le (hf : IsRegularDensity f) [Nonempty (Fin m)] (π z : Fin m → ℝ) :
    |choiceProb f π ⬝ᵥ z| ≤ ∑ i, |z i| := by
  simp only [dotProduct]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_of_nonneg (choiceProb_nonneg π i)]
  exact mul_le_of_le_one_left (abs_nonneg _) (choiceProb_le_one hf π i)

theorem continuous_G (hf : IsRegularDensity f) [Nonempty (Fin m)] : Continuous (G f) := by
  have key : ∀ a b : Fin m → ℝ, dist (G f a) (G f b) ≤ (Fintype.card (Fin m) : ℝ) * dist a b := by
    intro a b
    have h1 := G_sub hf a b
    have h2 := G_sub hf b a
    have h3 := abs_dot_le hf a (b - a)
    have h4 := abs_dot_le hf b (a - b)
    have h5 : ∑ i, |(b - a) i| ≤ (Fintype.card (Fin m) : ℝ) * dist a b := by
      have : ∀ i ∈ Finset.univ, |(b - a) i| ≤ dist a b := fun i _ => by
        rw [Pi.sub_apply, abs_sub_comm, ← Real.dist_eq]; exact dist_le_pi_dist a b i
      have := Finset.sum_le_sum this
      simpa [Finset.sum_const, Finset.card_univ] using this
    have h6 : ∑ i, |(a - b) i| = ∑ i, |(b - a) i| := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [abs_sub_comm]
    rw [Real.dist_eq, abs_le]
    constructor
    · have := (abs_le.1 h4).1; linarith
    · have := (abs_le.1 h3).1; linarith
  have hK : 0 ≤ (Fintype.card (Fin m) : ℝ) := by positivity
  exact (LipschitzWith.of_dist_le_mul (K := ⟨_, hK⟩) key).continuous

theorem G_shift (hf : IsRegularDensity f) [Nonempty (Fin m)] (π : Fin m → ℝ) (c : ℝ) :
    G f (fun j => π j + c) = G f π + c := by
  have := isProb hf
  have : ∀ e, phi (fun j => π j + c) e = phi π e + c := by
    intro e
    simp only [phi]
    have := smax_add_const (fun j => π j + e j) c
    have h2 : (fun j => π j + c + e j) = (fun j => (π j + e j) + c) := by funext j; ring
    rw [h2, this]; ring
  simp only [G, this]
  rw [integral_add (integrable_phi hf π) (integrable_const c), integral_const]
  simp

theorem G_zero (hf : IsRegularDensity f) [Nonempty (Fin m)] : G f 0 = 0 := by
  have : ∀ e : Fin m → ℝ, phi 0 e = 0 := by
    intro e; simp [phi]
  simp [G, this]

/-- Lower bound used for coercivity. -/
theorem G_lower (hf : IsRegularDensity f) [Nonempty (Fin m)] (π : Fin m → ℝ) (k : Fin m)
    (lo R : ℝ) (hlo : ∀ j, lo ≤ π j) (hR : 0 ≤ R) :
    lo + (μf f).real (Metric.closedBall (0 : Fin m → ℝ) R) * (π k - lo) - 2 * R ≤ G f π := by
  have := isProb hf
  set B := Metric.closedBall (0 : Fin m → ℝ) R
  have hB : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  have hint : Integrable (fun e => B.indicator (fun _ => π k - lo) e + (lo - 2 * R)) (μf f) :=
    ((integrable_const _).indicator hB).add (integrable_const _)
  have hval : ∫ e, (B.indicator (fun _ => π k - lo) e + (lo - 2 * R)) ∂(μf f) =
      lo + (μf f).real B * (π k - lo) - 2 * R := by
    rw [integral_add ((integrable_const _).indicator hB) (integrable_const _),
      integral_indicator_const _ hB, integral_const]
    simp; ring
  rw [← hval, G]
  refine integral_mono hint (integrable_phi hf π) fun e => ?_
  have hlow : lo ≤ phi π e := by
    simp only [phi]
    have := smax_mono (x := fun j => e j + lo) (y := fun j => π j + e j) (fun j => by
      show e j + lo ≤ π j + e j; linarith [hlo j])
    rw [smax_add_const] at this
    linarith
  by_cases he : e ∈ B
  · rw [Set.indicator_of_mem he]
    have hb : ∀ j, |e j| ≤ R := by
      intro j
      have h1 : ‖e‖ ≤ R := by simpa [B] using he
      have := norm_le_pi_norm e j
      rw [Real.norm_eq_abs] at this; linarith
    have h1 : smax e ≤ R := smax_le fun j => (abs_le.1 (hb j)).2
    have h2 := le_smax (fun j => π j + e j) k
    have h3 := (abs_le.1 (hb k)).1
    simp only [phi] at *
    linarith
  · rw [Set.indicator_of_notMem he]
    linarith


/-! ### critical points, surjectivity, argmax -/

theorem crit (hf : IsRegularDensity f) [Nonempty (Fin m)] (y π0 : Fin m → ℝ)
    (h : ∀ s : ℝ, 0 < s → G f π0 - y ⬝ᵥ π0 ≤
        G f (π0 - s • (choiceProb f π0 - y)) - y ⬝ᵥ (π0 - s • (choiceProb f π0 - y))) :
    choiceProb f π0 = y := by
  set z := choiceProb f π0 - y with hz
  have key : ∀ s : ℝ, 0 < s → (choiceProb f (π0 - s • z) - y) ⬝ᵥ z ≤ 0 := by
    intro s hs
    have h1 := h s hs
    have h2 := G_sub hf (π0 - s • z) π0
    have e1 : π0 - (π0 - s • z) = s • z := by abel
    rw [e1, dotProduct_smul, smul_eq_mul] at h2
    have e2 : y ⬝ᵥ (π0 - s • z) = y ⬝ᵥ π0 - s * (y ⬝ᵥ z) := by
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    rw [e2] at h1
    rw [sub_dotProduct]
    have h3 : s * (choiceProb f (π0 - s • z) ⬝ᵥ z) ≤ s * (y ⬝ᵥ z) := by linarith
    have := le_of_mul_le_mul_left h3 hs
    linarith
  have hC := continuous_choiceProb hf
  have hcont : Continuous fun s : ℝ => (choiceProb f (π0 - s • z) - y) ⬝ᵥ z := by
    simp only [dotProduct]
    fun_prop
  have hlim : (choiceProb f (π0 - (0 : ℝ) • z) - y) ⬝ᵥ z ≤ 0 :=
    le_of_tendsto ((hcont.tendsto 0).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall (s := Set.Ioi (0 : ℝ)) fun s hs => key s hs)
  rw [zero_smul, sub_zero, ← hz] at hlim
  have hnn : 0 ≤ z ⬝ᵥ z := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hz0 : z = 0 := dotProduct_self_eq_zero.1 (le_antisymm hlim hnn)
  rw [hz] at hz0
  exact sub_eq_zero.1 hz0

theorem fenchel (hf : IsRegularDensity f) [Nonempty (Fin m)] (p π : Fin m → ℝ) :
    choiceProb f p ⬝ᵥ π - G f π ≤ choiceProb f p ⬝ᵥ p - G f p := by
  have := G_sub hf p π
  rw [dotProduct_sub] at this
  linarith

/-- equality in the subgradient inequality forces the choice probabilities to be ordered. -/
theorem strict_aux (hf : IsRegularDensity f) [Nonempty (Fin m)] (π π' : Fin m → ℝ)
    (h : G f π' - G f π ≤ choiceProb f π ⬝ᵥ (π' - π)) (i : Fin m) :
    choiceProb f π i ≤ choiceProb f π' i := by
  have := isProb hf
  set g : (Fin m → ℝ) → ℝ := fun e => ∑ i, (Ev π i).indicator (fun _ => π' i - π i) e with hg
  have hgi : ∀ i, Integrable ((Ev π i).indicator (fun _ : Fin m → ℝ => π' i - π i)) (μf f) :=
    fun i => (integrable_const _).indicator (measurableSet_Ev π i)
  have hint : ∫ e, g e ∂(μf f) = choiceProb f π ⬝ᵥ (π' - π) := by
    rw [hg, integral_finsetSum _ (fun i _ => hgi i)]
    simp only [dotProduct, choiceProb_eq, Pi.sub_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_indicator_const _ (measurableSet_Ev π i), smul_eq_mul]
  have hgint : Integrable g (μf f) := integrable_finsetSum _ (fun i _ => hgi i)
  have hFi : Integrable (fun e => (phi π' e - phi π e) - g e) (μf f) :=
    ((integrable_phi hf π').sub (integrable_phi hf π)).sub hgint
  have hgv : ∀ e i, e ∈ Ev π i → g e = π' i - π i := by
    intro e i hi
    rw [hg]
    simp only
    rw [Finset.sum_eq_single i]
    · simp [Set.indicator_of_mem hi]
    · intro j _ hji
      rw [Set.indicator_of_notMem]
      intro hj
      exact Ev_disjoint π hji e hj hi
    · simp
  have hF0 : 0 ≤ᵐ[μf f] (fun e => (phi π' e - phi π e) - g e) := by
    filter_upwards [ae_exists_Ev hf π] with e he
    obtain ⟨i, hi⟩ := he
    simp only [Pi.zero_apply, sub_nonneg]
    rw [hgv e i hi]
    simp only [phi]
    rw [smax_of_Ev hi]
    have := le_smax (fun j => π' j + e j) i
    linarith
  have hFint : ∫ e, ((phi π' e - phi π e) - g e) ∂(μf f) =
      G f π' - G f π - choiceProb f π ⬝ᵥ (π' - π) := by
    have e1 : ∫ e, ((phi π' e - phi π e) - g e) ∂(μf f) =
        ∫ e, (phi π' e - phi π e) ∂(μf f) - ∫ e, g e ∂(μf f) :=
      integral_sub (f := fun e => phi π' e - phi π e) (g := g)
        ((integrable_phi hf π').sub (integrable_phi hf π)) hgint
    have e2 : ∫ e, (phi π' e - phi π e) ∂(μf f) =
        ∫ e, phi π' e ∂(μf f) - ∫ e, phi π e ∂(μf f) :=
      integral_sub (integrable_phi hf π') (integrable_phi hf π)
    rw [e1, e2, hint]
    rfl
  have h0 : ∫ e, ((phi π' e - phi π e) - g e) ∂(μf f) = 0 :=
    le_antisymm (by rw [hFint]; linarith) (integral_nonneg_of_ae hF0)
  have hF : (fun e => (phi π' e - phi π e) - g e) =ᵐ[μf f] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hF0 hFi).1 h0
  have hae : Ev π i ≤ᵐ[μf f] Ev π' i := by
    filter_upwards [hF, ae_exists_Ev hf π'] with e hFe he2 hei
    obtain ⟨j, hj⟩ := he2
    simp only [Pi.zero_apply] at hFe
    rw [hgv e i hei] at hFe
    simp only [phi] at hFe
    rw [smax_of_Ev hj] at hFe
    have hsm : smax (fun l => π l + e l) = π i + e i := smax_of_Ev hei
    rw [hsm] at hFe
    by_cases hji : j = i
    · rw [← hji]; exact hj
    · exfalso
      have := hj i (Ne.symm hji)
      linarith
  rw [choiceProb_eq, choiceProb_eq, Measure.real, Measure.real]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hae)

/-! ### conditional mean of the argmax choice -/

theorem measurable_argmaxVec_apply {k : ℕ} (i : Fin k) :
    Measurable (fun v : Fin k → ℝ => argmaxVec v i) := by
  have hset : MeasurableSet {v : Fin k → ℝ | (∀ j, v j ≤ v i) ∧ (∀ j, j < i → v j < v i)} := by
    have h1 : {v : Fin k → ℝ | (∀ j, v j ≤ v i) ∧ (∀ j, j < i → v j < v i)} =
        (⋂ j, {v : Fin k → ℝ | v j ≤ v i}) ∩
          ⋂ j, ⋂ (_ : j < i), {v : Fin k → ℝ | v j < v i} := by
      ext v; simp
    rw [h1]
    refine MeasurableSet.inter ?_ ?_
    · exact MeasurableSet.iInter fun j =>
        measurableSet_le (measurable_pi_apply j) (measurable_pi_apply i)
    · exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
        measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i)
  unfold argmaxVec
  exact Measurable.ite hset measurable_const measurable_const

theorem argmaxVec_eq_indicator {m : ℕ} (π e : Fin m → ℝ) (k0 i0 : Fin m) (h : e ∈ Ev π i0) :
    argmaxVec (fun k => π k + e k) k0 = (Ev π k0).indicator (fun _ => (1 : ℝ)) e := by
  unfold argmaxVec
  by_cases hk : k0 = i0
  · subst hk
    rw [Set.indicator_of_mem h, if_pos]
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · by_cases hj : j = k0
      · subst hj; exact le_rfl
      · exact (h j hj).le
    · exact h j (ne_of_lt hj)
  · rw [Set.indicator_of_notMem (fun hk0 => Ev_disjoint π hk e hk0 h), if_neg]
    rintro ⟨h1, -⟩
    have := h1 i0
    have := h k0 hk
    simp only at *
    linarith

theorem integral_argmaxVec (hf : IsRegularDensity f) [Nonempty (Fin m)] (π : Fin m → ℝ)
    (k0 : Fin m) :
    ∫ e, argmaxVec (fun k => π k + e k) k0 ∂(μf f) = choiceProb f π k0 := by
  have := isProb hf
  have hae : (fun e => argmaxVec (fun k => π k + e k) k0) =ᵐ[μf f]
      (Ev π k0).indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [ae_exists_Ev hf π] with e he
    obtain ⟨i0, hi0⟩ := he
    exact argmaxVec_eq_indicator π e k0 i0 hi0
  rw [integral_congr_ae hae, integral_indicator_const _ (measurableSet_Ev π k0), smul_eq_mul,
    mul_one, choiceProb_eq]

theorem cm_argmax (hf : IsRegularDensity f) [Nonempty (Fin m)]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Ω → (Fin m → ℝ)) (hξ : Measurable ξ) (hlaw : P.map ξ = μf f)
    {H : Type*} [MeasurableSpace H] (w : Ω → ℝ × H) (hw : Measurable w)
    (hind : IndepFun w ξ P) (hb : ∀ ω, |(w ω).1| ≤ 1)
    (g : H → (Fin m → ℝ)) (hg : Measurable g) (k0 : Fin m) :
    ∫ ω, (w ω).1 * argmaxVec (fun k => g (w ω).2 k + ξ ω k) k0 ∂P =
      ∫ ω, (w ω).1 * choiceProb f (g (w ω).2) k0 ∂P := by
  have := isProb hf
  set κ : (ℝ × H) × (Fin m → ℝ) → ℝ :=
    fun q => q.1.1 * argmaxVec (fun k => g q.1.2 k + q.2 k) k0 with hκ
  have hκm : Measurable κ := by
    refine (measurable_fst.comp measurable_fst).mul ?_
    refine (measurable_argmaxVec_apply k0).comp ?_
    refine measurable_pi_lambda _ (fun k => ?_)
    exact ((measurable_pi_apply k).comp (hg.comp (measurable_snd.comp measurable_fst))).add
      (measurable_pi_apply k |>.comp measurable_snd)
  have hprod : P.map (fun ω => (w ω, ξ ω)) = (P.map w).prod (P.map ξ) :=
    (indepFun_iff_map_prod_eq_prod_map_map hw.aemeasurable hξ.aemeasurable).1 hind
  have hpm : Measurable (fun ω => (w ω, ξ ω)) := hw.prodMk hξ
  have hbκ : ∀ q : (ℝ × H) × (Fin m → ℝ), |q.1.1| ≤ 1 → |κ q| ≤ 1 := by
    intro q hq
    simp only [hκ]
    rw [abs_mul]
    have h1 : |argmaxVec (fun k => g q.1.2 k + q.2 k) k0| ≤ 1 := by
      unfold argmaxVec; split_ifs <;> simp
    nlinarith [abs_nonneg q.1.1, abs_nonneg (argmaxVec (fun k => g q.1.2 k + q.2 k) k0)]
  -- left side as an integral over the product
  have hL : ∫ ω, (w ω).1 * argmaxVec (fun k => g (w ω).2 k + ξ ω k) k0 ∂P =
      ∫ q, κ q ∂((P.map w).prod (P.map ξ)) := by
    rw [← hprod, integral_map hpm.aemeasurable hκm.aestronglyMeasurable]
  have hint : Integrable κ ((P.map w).prod (P.map ξ)) := by
    rw [← hprod, integrable_map_measure hκm.aestronglyMeasurable hpm.aemeasurable]
    refine Integrable.of_bound (hκm.comp hpm).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact hbκ _ (hb ω)
  rw [hL, integral_prod _ hint]
  simp_rw [hlaw]
  have hinner : ∀ a : ℝ × H, ∫ e, κ (a, e) ∂(μf f) = a.1 * choiceProb f (g a.2) k0 := by
    intro a
    simp only [hκ]
    rw [integral_const_mul, integral_argmaxVec hf (g a.2) k0]
  simp_rw [hinner]
  rw [integral_map hw.aemeasurable]
  exact (measurable_fst.mul ((measurable_pi_apply k0).comp (continuous_choiceProb hf).measurable
    |>.comp (hg.comp measurable_snd))).aestronglyMeasurable

end StochFictPlay.ZeroSumESS.Aux22


open scoped ENNReal

namespace StochFictPlay.ZeroSumESS.Aux22

/-! ### history σ-algebras and independence -/

section Hist

variable {Ω : Type*} {ι : Type*} {β : ι → Type*} [∀ i, MeasurableSpace (β i)]

/-- the σ-algebra generated by the variables `e j` with `τ j < t` -/
def HistG (e : ∀ i, Ω → β i) (τ : ι → ℕ) (t : ℕ) : MeasurableSpace Ω :=
  ⨆ j ∈ {j : ι | τ j < t}, MeasurableSpace.comap (e j) inferInstance

theorem HistG_mono (e : ∀ i, Ω → β i) (τ : ι → ℕ) {s t : ℕ} (h : s ≤ t) :
    HistG e τ s ≤ HistG e τ t :=
  iSup₂_mono' fun j hj => ⟨j, lt_of_lt_of_le hj h, le_rfl⟩

theorem HistG_le [mΩ : MeasurableSpace Ω] (e : ∀ i, Ω → β i) (he : ∀ i, Measurable (e i))
    (τ : ι → ℕ) (t : ℕ) : HistG e τ t ≤ mΩ :=
  iSup₂_le fun j _ => (he j).comap_le

theorem measurable_HistG (e : ∀ i, Ω → β i) (τ : ι → ℕ) {t : ℕ} (i : ι) (hi : τ i < t) :
    Measurable[HistG e τ t] (e i) := by
  have hle : MeasurableSpace.comap (e i) inferInstance ≤ HistG e τ t :=
    le_iSup₂ (f := fun (j : ι) (_ : j ∈ {j : ι | τ j < t}) =>
      MeasurableSpace.comap (e j) inferInstance) i hi
  exact (comap_measurable (e i)).mono hle le_rfl

theorem indep_HistG [mΩ : MeasurableSpace Ω] {P : Measure Ω} (e : ∀ i, Ω → β i)
    (he : ∀ i, Measurable (e i)) (hind : iIndepFun e P) (τ : ι → ℕ) (i : ι) :
    Indep (HistG e τ (τ i)) (MeasurableSpace.comap (e i) inferInstance) P := by
  have h1 := (iIndepFun_iff_iIndep (fun i => inferInstance) e P).1 hind
  have h2 := indep_iSup_of_disjoint (fun j => (he j).comap_le) h1
    (S := {j : ι | τ j < τ i}) (T := {i}) (by
      rw [Set.disjoint_singleton_right]; simp)
  rwa [iSup_singleton] at h2

end Hist

/-! ### law of large numbers from conditional means -/

section LLN

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem lln_of_cmp (P : Measure Ω) [IsProbabilityMeasure P] (ℋ : ℕ → MeasurableSpace Ω)
    (hℋle : ∀ t, ℋ t ≤ mΩ) (hmono : Monotone ℋ)
    (D M : ℕ → Ω → ℝ)
    (hD : ∀ t, Measurable[ℋ (t + 2)] (D t)) (hM : ∀ t, Measurable[ℋ (t + 1)] (M t))
    (hDb : ∀ t ω, 0 ≤ D t ω ∧ D t ω ≤ 1) (hMb : ∀ t ω, 0 ≤ M t ω ∧ M t ω ≤ 1)
    (hcmp : ∀ t (Y : Ω → ℝ), Measurable[ℋ (t + 1)] Y → (∀ ω, |Y ω| ≤ 1) →
      ∫ ω, Y ω * D t ω ∂P = ∫ ω, Y ω * M t ω ∂P) :
    ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => (1 / (k : ℝ)) * ∑ j ∈ Finset.range k, (D j ω - M j ω))
      atTop (𝓝 0) := by
  have hDm : ∀ t, Measurable (D t) := fun t => (hD t).mono (hℋle _) le_rfl
  have hMm : ∀ t, Measurable (M t) := fun t => (hM t).mono (hℋle _) le_rfl
  refine Rajchman22.rajchman P (fun t ω => D t ω - M t ω) (fun t => (hDm t).sub (hMm t))
    (fun t ω => ?_) (fun i j hij => ?_)
  · rw [abs_le]
    constructor <;> linarith [hDb t ω, hMb t ω]
  · have hXi : Measurable[ℋ (j + 1)] (fun ω => D i ω - M i ω) := by
      have h1 : Measurable[ℋ (j + 1)] (D i) :=
        (hD i).mono (hmono (by omega)) le_rfl
      have h2 : Measurable[ℋ (j + 1)] (M i) :=
        (hM i).mono (hmono (by omega)) le_rfl
      exact h1.sub h2
    have hb : ∀ ω, |D i ω - M i ω| ≤ 1 := fun ω => by
      rw [abs_le]; constructor <;> linarith [hDb i ω, hMb i ω]
    have hmi : Measurable (fun ω => D i ω - M i ω) := (hDm i).sub (hMm i)
    have h := hcmp j (fun ω => D i ω - M i ω) hXi hb
    have hDj : Integrable (fun ω => (D i ω - M i ω) * D j ω) P := by
      refine Integrable.of_bound (hmi.mul (hDm j)).aestronglyMeasurable 1
        (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      nlinarith [hb ω, abs_nonneg (D i ω - M i ω), abs_nonneg (D j ω),
        abs_of_nonneg (hDb j ω).1, (hDb j ω).2]
    have hMj : Integrable (fun ω => (D i ω - M i ω) * M j ω) P := by
      refine Integrable.of_bound (hmi.mul (hMm j)).aestronglyMeasurable 1
        (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      nlinarith [hb ω, abs_nonneg (D i ω - M i ω), abs_nonneg (M j ω),
        abs_of_nonneg (hMb j ω).1, (hMb j ω).2]
    have e : (fun ω => (D i ω - M i ω) * (D j ω - M j ω)) =
        fun ω => (D i ω - M i ω) * D j ω - (D i ω - M i ω) * M j ω := by
      funext ω; ring
    rw [e, integral_sub hDj hMj, h, sub_self]

end LLN

end StochFictPlay.ZeroSumESS.Aux22


namespace StochFictPlay.ZeroSumESS.Aux22

/-! ### standard SFP: measurability, conditional means -/

section SFP

variable {p : ℕ} {n : Fin p → ℕ}

theorem continuous_payoffVec (u : (α : Fin p) → Profile n → ℝ) (α : Fin p) (k : Fin (n α)) :
    Continuous (fun z : Mixed n => payoffVec u z α k) := by
  unfold payoffVec
  refine continuous_finset_sum _ fun s _ => ?_
  by_cases h : s α = k
  · simp only [h, if_true]
    refine continuous_const.mul (continuous_finset_prod _ fun β _ => ?_)
    exact (continuous_apply (s β)).comp (continuous_apply β)
  · simp only [h, if_false]
    exact continuous_const

theorem meas_sfpChoice {Ω : Type*} [m : MeasurableSpace Ω] (u : (α : Fin p) → Profile n → ℝ)
    (z : Ω → Mixed n) (hz : Measurable z)
    (εt : (α : Fin p) → Ω → (Fin (n α) → ℝ)) (hε : ∀ α, Measurable (εt α)) :
    Measurable (fun ω => sfpChoice u (z ω) εt ω) := by
  refine measurable_pi_lambda _ fun α => measurable_pi_lambda _ fun k => ?_
  show Measurable (fun ω => argmaxVec (fun k' => payoffVec u (z ω) α k' + εt α ω k') k)
  refine (measurable_argmaxVec_apply k).comp (measurable_pi_lambda _ fun k' => ?_)
  exact ((continuous_payoffVec u α k').measurable.comp hz).add
    ((measurable_pi_apply k').comp (hε α))

/-- history σ-algebra of standard SFP: generated by the shocks of times `< t` -/
abbrev HistS {Ω : Type*} (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (t : ℕ) :
    MeasurableSpace Ω :=
  HistG (β := fun i : ℕ × Fin p => Fin (n i.2) → ℝ) (fun i ω => ε i.1 i.2 ω) Prod.fst t

theorem meas_cum {Ω : Type*} [mΩ : MeasurableSpace Ω] (u : (α : Fin p) → Profile n → ℝ)
    (s₁ : Profile n) (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ))
    (he : ∀ t α, Measurable (ε t α)) (t : ℕ) :
    Measurable[HistS ε t] (sfpCum u s₁ ε t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    cases t with
    | zero => exact measurable_const
    | succ t =>
      have h1 : Measurable[HistS ε (t + 2)] (sfpCum u s₁ ε (t + 1)) :=
        ih.mono (HistG_mono _ _ (by omega)) le_rfl
      have hz : Measurable[HistS ε (t + 2)]
          (fun ω => (1 / ((t + 1 : ℕ) : ℝ)) • sfpCum u s₁ ε (t + 1) ω) :=
        h1.const_smul (1 / ((t + 1 : ℕ) : ℝ))
      have hεt : ∀ α, Measurable[HistS ε (t + 2)] (ε (t + 1) α) := fun α =>
        measurable_HistG (β := fun i : ℕ × Fin p => Fin (n i.2) → ℝ)
          (fun i ω => ε i.1 i.2 ω) Prod.fst (t := t + 2) (t + 1, α) (by simp)
      have h2 : Measurable[HistS ε (t + 2)] (fun ω => sfpChoice u
          ((1 / ((t + 1 : ℕ) : ℝ)) • sfpCum u s₁ ε (t + 1) ω) (ε (t + 1)) ω) :=
        @meas_sfpChoice p n Ω (HistS ε (t + 2)) u
          (fun ω => (1 / ((t + 1 : ℕ) : ℝ)) • sfpCum u s₁ ε (t + 1) ω) hz (ε (t + 1)) hεt
      have key : sfpCum u s₁ ε (t + 2) = fun ω => sfpCum u s₁ ε (t + 1) ω +
          sfpChoice u ((1 / ((t + 1 : ℕ) : ℝ)) • sfpCum u s₁ ε (t + 1) ω) (ε (t + 1)) ω := rfl
      rw [key]
      exact h1.add h2

theorem meas_belief {Ω : Type*} [mΩ : MeasurableSpace Ω] (u : (α : Fin p) → Profile n → ℝ)
    (s₁ : Profile n) (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ))
    (he : ∀ t α, Measurable (ε t α)) (t : ℕ) :
    Measurable[HistS ε t] (sfpBelief u s₁ ε t) :=
  Measurable.const_smul (meas_cum u s₁ ε he t) (1 / (t : ℝ))

theorem sfp_cmp {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hn : ∀ α, 1 ≤ n α) (u : (α : Fin p) → Profile n → ℝ)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (hε : IsShockFamily P f ε) (s₁ : Profile n)
    (α : Fin p) (k0 : Fin (n α)) (t : ℕ) (Y : Ω → ℝ) (hY : Measurable[HistS ε (t + 1)] Y)
    (hYb : ∀ ω, |Y ω| ≤ 1) :
    ∫ ω, Y ω * sfpChoice u (sfpBelief u s₁ ε (t + 1) ω) (ε (t + 1)) ω α k0 ∂P =
      ∫ ω, Y ω * pbr f u (sfpBelief u s₁ ε (t + 1) ω) α k0 ∂P := by
  have : Nonempty (Fin (n α)) := Fin.pos_iff_nonempty.1 (hn α)
  have he' : ∀ i : ℕ × Fin p, Measurable (fun ω => ε i.1 i.2 ω) := fun i => hε.1 i.1 i.2
  have hle : HistS ε (t + 1) ≤ mΩ :=
    HistG_le (β := fun i : ℕ × Fin p => Fin (n i.2) → ℝ) (fun i ω => ε i.1 i.2 ω) he' Prod.fst _
  have hz : Measurable[HistS ε (t + 1)] (sfpBelief u s₁ ε (t + 1)) :=
    meas_belief u s₁ ε hε.1 (t + 1)
  have hw' : Measurable[HistS ε (t + 1)] (fun ω => (Y ω, sfpBelief u s₁ ε (t + 1) ω)) :=
    hY.prodMk hz
  have hw : Measurable (fun ω => (Y ω, sfpBelief u s₁ ε (t + 1) ω)) := hw'.mono hle le_rfl
  have hind : IndepFun (fun ω => (Y ω, sfpBelief u s₁ ε (t + 1) ω)) (ε (t + 1) α) P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left
      (indep_HistG (β := fun i : ℕ × Fin p => Fin (n i.2) → ℝ) (fun i ω => ε i.1 i.2 ω) he'
        hε.2.2 Prod.fst (t + 1, α)) hw'.comap_le
  exact cm_argmax (f := f α) (hf α) P (ε (t + 1) α) (hε.1 _ _) (hε.2.1 (t + 1) α) _ hw hind
    (fun ω => hYb ω) (fun z => payoffVec u z α)
    (measurable_pi_lambda _ fun k => (continuous_payoffVec u α k).measurable) k0

end SFP

end StochFictPlay.ZeroSumESS.Aux22


namespace StochFictPlay.ZeroSumESS.Aux22

section SFP3

variable {p : ℕ} {n : Fin p → ℕ}

theorem argmaxVec_mem01 {k : ℕ} (v : Fin k → ℝ) (i : Fin k) :
    0 ≤ argmaxVec v i ∧ argmaxVec v i ≤ 1 := by
  unfold argmaxVec; split_ifs <;> simp

theorem continuous_pbr (u : (α : Fin p) → Profile n → ℝ)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (α : Fin p) (k : Fin (n α)) : Continuous (fun z : Mixed n => pbr f u z α k) := by
  show Continuous fun z : Mixed n => choiceProb (f α) (payoffVec u z α) k
  exact (continuous_apply k).comp ((continuous_choiceProb (hf α)).comp
    (continuous_pi fun k' => continuous_payoffVec u α k'))

theorem sfp_lln {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hn : ∀ α, 1 ≤ n α) (u : (α : Fin p) → Profile n → ℝ)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (hε : IsShockFamily P f ε) (s₁ : Profile n) :
    ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => (1 / (k : ℝ)) •
      ∑ j ∈ Finset.range k, (sfpChoice u (sfpBelief u s₁ ε (j + 1) ω) (ε (j + 1)) ω -
        pbr f u (sfpBelief u s₁ ε (j + 1) ω))) atTop (𝓝 0) := by
  have he' : ∀ i : ℕ × Fin p, Measurable (fun ω => ε i.1 i.2 ω) := fun i => hε.1 i.1 i.2
  have hall : ∀ c : (α : Fin p) × Fin (n α), ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ => (1 / (k : ℝ)) * ∑ j ∈ Finset.range k,
        (sfpChoice u (sfpBelief u s₁ ε (j + 1) ω) (ε (j + 1)) ω c.1 c.2 -
          pbr f u (sfpBelief u s₁ ε (j + 1) ω) c.1 c.2)) atTop (𝓝 0) := by
    intro c
    have : Nonempty (Fin (n c.1)) := Fin.pos_iff_nonempty.1 (hn c.1)
    refine lln_of_cmp P (HistS ε) (fun t => HistG_le (β := fun i : ℕ × Fin p => Fin (n i.2) → ℝ)
      (fun i ω => ε i.1 i.2 ω) he' Prod.fst t) (fun s t h => HistG_mono _ _ h)
      (fun j ω => sfpChoice u (sfpBelief u s₁ ε (j + 1) ω) (ε (j + 1)) ω c.1 c.2)
      (fun j ω => pbr f u (sfpBelief u s₁ ε (j + 1) ω) c.1 c.2) ?_ ?_ ?_ ?_ ?_
    · intro j
      have hz : Measurable[HistS ε (j + 2)] (sfpBelief u s₁ ε (j + 1)) :=
        (meas_belief u s₁ ε hε.1 (j + 1)).mono (HistG_mono _ _ (by omega)) le_rfl
      have hεt : ∀ α, Measurable[HistS ε (j + 2)] (ε (j + 1) α) := fun α =>
        measurable_HistG (β := fun i : ℕ × Fin p => Fin (n i.2) → ℝ)
          (fun i ω => ε i.1 i.2 ω) Prod.fst (t := j + 2) (j + 1, α) (by simp)
      have h2 : Measurable[HistS ε (j + 2)] (fun ω =>
          sfpChoice u (sfpBelief u s₁ ε (j + 1) ω) (ε (j + 1)) ω) :=
        @meas_sfpChoice p n Ω (HistS ε (j + 2)) u _ hz (ε (j + 1)) hεt
      exact (measurable_pi_apply c.2).comp ((measurable_pi_apply c.1).comp h2)
    · intro j
      exact (continuous_pbr u f hf c.1 c.2).measurable.comp (meas_belief u s₁ ε hε.1 (j + 1))
    · intro j ω
      exact argmaxVec_mem01 _ _
    · intro j ω
      exact ⟨choiceProb_nonneg _ _, choiceProb_le_one (hf c.1) _ _⟩
    · intro t Y hY hYb
      exact sfp_cmp P hn u f hf ε hε s₁ c.1 c.2 t Y hY hYb
  have hall' := (ae_all_iff).2 hall
  filter_upwards [hall'] with ω hω
  refine tendsto_pi_nhds.2 fun α => tendsto_pi_nhds.2 fun k => ?_
  have := hω ⟨α, k⟩
  simpa [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply] using this

end SFP3

end StochFictPlay.ZeroSumESS.Aux22


namespace StochFictPlay.ZeroSumESS.Aux22

section Mixed

variable {p : ℕ} {n : Fin p → ℕ}

/-- the pairing `∑_α x^α · π^α` on mixed profiles -/
noncomputable def Bm (n : Fin p → ℕ) : Mixed n →ₗ[ℝ] Mixed n →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x π => ∑ α, x α ⬝ᵥ π α)
    (fun x x' π => by simp [add_dotProduct, Finset.sum_add_distrib])
    (fun r x π => by simp [smul_dotProduct, Finset.mul_sum])
    (fun x π π' => by simp [dotProduct_add, Finset.sum_add_distrib])
    (fun r x π => by simp [dotProduct_smul, Finset.mul_sum])

theorem Bm_apply (x π : Mixed n) : Bm n x π = ∑ α, x α ⬝ᵥ π α := rfl

/-- the profile of choice probabilities -/
noncomputable def CfM (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) : Mixed n → Mixed n :=
  fun π α => choiceProb (f α) (π α)

/-- the sum of the potentials -/
noncomputable def WM (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) : Mixed n → ℝ :=
  fun π => ∑ α, G (f α) (π α)

theorem mixed_eq : mixedProfiles n = Set.pi Set.univ (fun α => stdSimplex ℝ (Fin (n α))) := by
  ext x; simp [mixedProfiles, Set.mem_pi]

theorem isCompact_mixed : IsCompact (mixedProfiles n) := by
  rw [mixed_eq]; exact isCompact_univ_pi (fun α => isCompact_stdSimplex ℝ (Fin (n α)))

theorem convex_mixed : Convex ℝ (mixedProfiles n) := by
  rw [mixed_eq]; exact convex_pi (fun α _ => convex_stdSimplex ℝ _)

variable {f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞}

theorem CfM_mem (hn : ∀ α, 1 ≤ n α) (hf : ∀ α, IsRegularDensity (f α)) (π : Mixed n) :
    CfM f π ∈ mixedProfiles n := by
  intro α
  have : Nonempty (Fin (n α)) := Fin.pos_iff_nonempty.1 (hn α)
  exact ⟨fun i => choiceProb_nonneg _ _, sum_choiceProb (hf α) _⟩

theorem continuous_CfM (hf : ∀ α, IsRegularDensity (f α)) : Continuous (CfM f) :=
  continuous_pi fun α => (continuous_choiceProb (hf α)).comp (continuous_apply α)

theorem continuous_WM (hn : ∀ α, 1 ≤ n α) (hf : ∀ α, IsRegularDensity (f α)) :
    Continuous (WM f) := by
  refine continuous_finset_sum _ fun α _ => ?_
  have : Nonempty (Fin (n α)) := Fin.pos_iff_nonempty.1 (hn α)
  exact (continuous_G (hf α)).comp (continuous_apply α)

theorem WM_sg (hn : ∀ α, 1 ≤ n α) (hf : ∀ α, IsRegularDensity (f α)) (π π' : Mixed n) :
    WM f π + Bm n (CfM f π) (π' - π) ≤ WM f π' := by
  have h : ∀ α ∈ Finset.univ, CfM f π α ⬝ᵥ (π' - π) α ≤ G (f α) (π' α) - G (f α) (π α) := by
    intro α _
    have : Nonempty (Fin (n α)) := Fin.pos_iff_nonempty.1 (hn α)
    exact G_sub (hf α) (π α) (π' α)
  have := Finset.sum_le_sum h
  rw [Finset.sum_sub_distrib] at this
  simp only [Bm_apply, WM]
  linarith

theorem Bm_bound (n : Fin p → ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ c d : Mixed n, |Bm n c d| ≤ K * ‖c‖ * ‖d‖ := by
  refine ⟨∑ α, (n α : ℝ), Finset.sum_nonneg fun α _ => Nat.cast_nonneg _, fun c d => ?_⟩
  rw [Bm_apply]
  have hc : ∀ α k, |c α k| ≤ ‖c‖ := fun α k =>
    (norm_le_pi_norm (c α) k).trans' (le_of_eq (Real.norm_eq_abs _).symm) |>.trans
      (norm_le_pi_norm c α)
  have hd : ∀ α k, |d α k| ≤ ‖d‖ := fun α k =>
    (norm_le_pi_norm (d α) k).trans' (le_of_eq (Real.norm_eq_abs _).symm) |>.trans
      (norm_le_pi_norm d α)
  calc |∑ α, c α ⬝ᵥ d α| ≤ ∑ α, |c α ⬝ᵥ d α| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ α, (n α : ℝ) * (‖c‖ * ‖d‖) := by
      refine Finset.sum_le_sum fun α _ => ?_
      simp only [dotProduct]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k, |c α k * d α k| ≤ ∑ k : Fin (n α), (‖c‖ * ‖d‖) := by
            refine Finset.sum_le_sum fun k _ => ?_
            rw [abs_mul]
            exact mul_le_mul (hc α k) (hd α k) (abs_nonneg _) (norm_nonneg _)
        _ = (n α : ℝ) * (‖c‖ * ‖d‖) := by simp
    _ = (∑ α, (n α : ℝ)) * ‖c‖ * ‖d‖ := by rw [← Finset.sum_mul, mul_assoc]

theorem continuous_Bm : Continuous fun q : Mixed n × Mixed n => Bm n q.1 q.2 := by
  simp only [Bm_apply, dotProduct]
  fun_prop

theorem crit_mixed (hn : ∀ α, 1 ≤ n α) (hf : ∀ α, IsRegularDensity (f α)) (x π0 : Mixed n)
    (h : ∀ π, Bm n x π - WM f π ≤ Bm n x π0 - WM f π0) : CfM f π0 = x := by
  funext α
  have : Nonempty (Fin (n α)) := Fin.pos_iff_nonempty.1 (hn α)
  have key : ∀ π' : Fin (n α) → ℝ,
      x α ⬝ᵥ π' - G (f α) π' ≤ x α ⬝ᵥ π0 α - G (f α) (π0 α) := by
    intro π'
    have h1 := h (Function.update π0 α π')
    have e : ∀ F : (β : Fin p) → (Fin (n β) → ℝ) → ℝ,
        ∑ β, F β (Function.update π0 α π' β) = F α π' + ∑ β ∈ Finset.univ.erase α, F β (π0 β) := by
      intro F
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ α), Function.update_self]
      congr 1
      refine Finset.sum_congr rfl fun β hβ => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hβ)]
    have e0 : ∀ F : (β : Fin p) → (Fin (n β) → ℝ) → ℝ,
        ∑ β, F β (π0 β) = F α (π0 α) + ∑ β ∈ Finset.univ.erase α, F β (π0 β) := by
      intro F
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ α)]
    simp only [Bm_apply, WM] at h1
    have h2 := e (fun β v => x β ⬝ᵥ v)
    have h3 := e (fun β v => G (f β) v)
    have h4 := e0 (fun β v => x β ⬝ᵥ v)
    have h5 := e0 (fun β v => G (f β) v)
    try simp only at h2 h3 h4 h5
    linarith
  have hcrit : ∀ s : ℝ, 0 < s →
      G (f α) (π0 α) - x α ⬝ᵥ π0 α ≤
        G (f α) (π0 α - s • (choiceProb (f α) (π0 α) - x α)) -
          x α ⬝ᵥ (π0 α - s • (choiceProb (f α) (π0 α) - x α)) := by
    intro s _
    have := key (π0 α - s • (choiceProb (f α) (π0 α) - x α))
    linarith
  exact crit (hf α) (x α) (π0 α) hcrit

end Mixed

end StochFictPlay.ZeroSumESS.Aux22


namespace StochFictPlay.ZeroSumESS.Aux22

section Mixed2

variable {p : ℕ} {n : Fin p → ℕ} {f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞}

theorem unique_rest_mixed (hn : ∀ α, 1 ≤ n α) (hf : ∀ α, IsRegularDensity (f α))
    (L : Mixed n →ₗ[ℝ] Mixed n) (x x' : Mixed n)
    (hneg : Bm n (x - x') (L (x - x')) ≤ 0)
    (hx : CfM f (L x) = x) (hx' : CfM f (L x') = x') : x = x' := by
  have hxα : ∀ β, choiceProb (f β) (L x β) = x β := fun β => congrFun hx β
  have hx'α : ∀ β, choiceProb (f β) (L x' β) = x' β := fun β => congrFun hx' β
  set A : Fin p → ℝ := fun β => G (f β) (L x' β) - G (f β) (L x β) - x β ⬝ᵥ (L x' β - L x β)
    with hA
  set B : Fin p → ℝ := fun β => G (f β) (L x β) - G (f β) (L x' β) - x' β ⬝ᵥ (L x β - L x' β)
    with hB
  have hA0 : ∀ β, 0 ≤ A β := fun β => by
    have : Nonempty (Fin (n β)) := Fin.pos_iff_nonempty.1 (hn β)
    have := G_sub (hf β) (L x β) (L x' β)
    rw [hxα β] at this
    simp only [hA]; linarith
  have hB0 : ∀ β, 0 ≤ B β := fun β => by
    have : Nonempty (Fin (n β)) := Fin.pos_iff_nonempty.1 (hn β)
    have := G_sub (hf β) (L x' β) (L x β)
    rw [hx'α β] at this
    simp only [hB]; linarith
  have hAB : ∀ β, A β + B β = (x β - x' β) ⬝ᵥ (L x β - L x' β) := fun β => by
    simp only [hA, hB, sub_dotProduct, dotProduct_sub]; ring
  have hsum : ∑ β, (A β + B β) ≤ 0 := by
    have : ∑ β, (A β + B β) = Bm n (x - x') (L (x - x')) := by
      rw [Bm_apply, map_sub]
      exact Finset.sum_congr rfl fun β _ => hAB β
    rw [this]; exact hneg
  have hle : ∀ β, A β + B β ≤ 0 := fun β =>
    (Finset.single_le_sum (f := fun β => A β + B β) (fun β _ => add_nonneg (hA0 β) (hB0 β))
      (Finset.mem_univ β)).trans hsum
  funext α
  have : Nonempty (Fin (n α)) := Fin.pos_iff_nonempty.1 (hn α)
  have hAα : A α ≤ 0 := by linarith [hle α, hB0 α]
  have hBα : B α ≤ 0 := by linarith [hle α, hA0 α]
  funext i
  have h1 := strict_aux (hf α) (L x α) (L x' α) (by
    rw [hxα α]; simp only [hA] at hAα; linarith) i
  have h2 := strict_aux (hf α) (L x' α) (L x α) (by
    rw [hx'α α]; simp only [hB] at hBα; linarith) i
  rw [hxα α, hx'α α] at h1
  rw [hx'α α, hxα α] at h2
  linarith

theorem gap_mixed (hn : ∀ α, 1 ≤ n α) (hf : ∀ α, IsRegularDensity (f α))
    (L : Mixed n →ₗ[ℝ] Mixed n)
    (hneg : ∀ a ∈ mixedProfiles n, ∀ b ∈ mixedProfiles n, Bm n (b - a) (L (b - a)) ≤ 0)
    (π₀ : Mixed n) (y q : ℕ → Mixed n) (hy0 : y 0 = CfM f π₀)
    (hyS : ∀ k : ℕ, y (k + 1) =
      (1 - 1 / ((k : ℝ) + 2)) • y k + (1 / ((k : ℝ) + 2)) • CfM f (q k))
    (hκ : Tendsto (fun k => q k - L (y k)) atTop (𝓝 0)) :
    ∀ yb, MapClusterPt yb atTop y → CfM f (L yb) = yb := by
  obtain ⟨K, hK0, hK⟩ := Bm_bound n
  exact GapLib22.gap_tendsto (Bm n) continuous_Bm L K hK0 hK (CfM f) (continuous_CfM hf)
    (WM f) (continuous_WM hn hf) (WM_sg hn hf) (mixedProfiles n) isCompact_mixed convex_mixed
    (CfM_mem hn hf) hneg π₀ y q hy0 hyS hκ (crit_mixed hn hf)

theorem exists_rest_mixed (hn : ∀ α, 1 ≤ n α) (hf : ∀ α, IsRegularDensity (f α))
    (L : Mixed n →ₗ[ℝ] Mixed n)
    (hneg : ∀ a ∈ mixedProfiles n, ∀ b ∈ mixedProfiles n, Bm n (b - a) (L (b - a)) ≤ 0) :
    ∃ x ∈ mixedProfiles n, CfM f (L x) = x := by
  obtain ⟨y, hy0, hyS⟩ : ∃ y : ℕ → Mixed n, y 0 = CfM f 0 ∧ ∀ k : ℕ, y (k + 1) =
      (1 - 1 / ((k : ℝ) + 2)) • y k + (1 / ((k : ℝ) + 2)) • CfM f (L (y k)) :=
    ⟨fun m => Nat.rec (CfM f 0) (fun k yk =>
      (1 - 1 / ((k : ℝ) + 2)) • yk + (1 / ((k : ℝ) + 2)) • CfM f (L yk)) m, rfl, fun _ => rfl⟩
  have hyX : ∀ k, y k ∈ mixedProfiles n := by
    intro k
    induction k with
    | zero => rw [hy0]; exact CfM_mem hn hf _
    | succ k ih =>
      rw [hyS k]
      have h0 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
      refine convex_mixed ih (CfM_mem hn hf _) ?_ (by positivity) (by ring)
      rw [sub_nonneg, div_le_one h0]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hcl := gap_mixed hn hf L hneg 0 y (fun k => L (y k)) hy0 hyS (by simpa using tendsto_const_nhds)
  have hmem : mixedProfiles n ∈ Filter.map y atTop :=
    Filter.mem_map.2 (Filter.Eventually.of_forall (fun k => hyX k))
  obtain ⟨x, hxX, hx⟩ := isCompact_mixed.exists_mapClusterPt (f := (atTop : Filter ℕ))
    (u := y) (Filter.le_principal_iff.2 hmem)
  exact ⟨x, hxX, hcl x hx⟩

/-- deterministic convergence: if the beliefs track the Cesàro mean of their own choice
probabilities, they converge to the unique rest point. -/
theorem converge_det (hn : ∀ α, 1 ≤ n α) (hf : ∀ α, IsRegularDensity (f α))
    (L : Mixed n →ₗ[ℝ] Mixed n)
    (hneg : ∀ a ∈ mixedProfiles n, ∀ b ∈ mixedProfiles n, Bm n (b - a) (L (b - a)) ≤ 0)
    (xs : Mixed n) (huniq : ∀ x ∈ mixedProfiles n, CfM f (L x) = x → x = xs)
    (z : ℕ → Mixed n)
    (hlim : Tendsto (fun k : ℕ => z (k + 1) - (1 / ((k : ℝ) + 1)) •
      (CfM f 0 + ∑ j ∈ Finset.range k, CfM f (L (z (j + 1))))) atTop (𝓝 0)) :
    Tendsto (fun k : ℕ => z (k + 1)) atTop (𝓝 xs) := by
  set y : ℕ → Mixed n := fun k => (1 / ((k : ℝ) + 1)) •
    (CfM f 0 + ∑ j ∈ Finset.range k, CfM f (L (z (j + 1)))) with hy
  have hy0 : y 0 = CfM f 0 := by simp [hy]
  have hyS : ∀ k : ℕ, y (k + 1) =
      (1 - 1 / ((k : ℝ) + 2)) • y k + (1 / ((k : ℝ) + 2)) • CfM f (L (z (k + 1))) := by
    intro k
    simp only [hy]
    rw [Finset.sum_range_succ, smul_smul]
    have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have e : (1 - 1 / ((k : ℝ) + 2)) * (1 / ((k : ℝ) + 1)) = 1 / ((k : ℝ) + 2) := by
      field_simp; ring
    rw [e, ← smul_add]
    push_cast
    congr 1
    · ring
    · abel
  have hyX : ∀ k, y k ∈ mixedProfiles n := by
    intro k
    induction k with
    | zero => rw [hy0]; exact CfM_mem hn hf _
    | succ k ih =>
      rw [hyS k]
      have h0 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
      refine convex_mixed ih (CfM_mem hn hf _) ?_ (by positivity) (by ring)
      rw [sub_nonneg, div_le_one h0]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hLc : Continuous L := LinearMap.continuous_of_finiteDimensional L
  have hκ : Tendsto (fun k => L (z (k + 1)) - L (y k)) atTop (𝓝 0) := by
    have := (hLc.tendsto 0).comp hlim
    simp only [map_zero] at this
    refine this.congr fun k => ?_
    simp [hy, map_sub]
  have hcl := gap_mixed hn hf L hneg 0 y (fun k => L (z (k + 1))) hy0 hyS hκ
  have hyT : Tendsto y atTop (𝓝 xs) := by
    refine isCompact_mixed.tendsto_nhds_of_unique_mapClusterPt (Eventually.of_forall hyX) ?_
    intro x hxX hx
    exact huniq x hxX (hcl x hx)
  have := hyT.add hlim
  simp only [add_zero] at this
  refine this.congr fun k => ?_
  simp [hy]

end Mixed2

end StochFictPlay.ZeroSumESS.Aux22


namespace StochFictPlay.ZeroSumESS.Aux22

section SFPCesaro

variable {p : ℕ} {n : Fin p → ℕ}

theorem cum_eq {Ω : Type*} (u : (α : Fin p) → Profile n → ℝ) (s₁ : Profile n)
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (ω : Ω) (k : ℕ) :
    sfpCum u s₁ ε (k + 1) ω = pureVec s₁ +
      ∑ j ∈ Finset.range k, sfpChoice u (sfpBelief u s₁ ε (j + 1) ω) (ε (j + 1)) ω := by
  induction k with
  | zero => simp [sfpCum]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih]
    rfl

theorem sfp_gap_identity {Ω : Type*} (u : (α : Fin p) → Profile n → ℝ) (s₁ : Profile n)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞)
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (ω : Ω) (c0 : Mixed n) (k : ℕ) :
    sfpBelief u s₁ ε (k + 1) ω - (1 / ((k : ℝ) + 1)) •
        (c0 + ∑ j ∈ Finset.range k, pbr f u (sfpBelief u s₁ ε (j + 1) ω)) =
      (1 / ((k : ℝ) + 1)) • (pureVec s₁ - c0) +
        ((k : ℝ) / ((k : ℝ) + 1)) • ((1 / (k : ℝ)) • ∑ j ∈ Finset.range k,
          (sfpChoice u (sfpBelief u s₁ ε (j + 1) ω) (ε (j + 1)) ω -
            pbr f u (sfpBelief u s₁ ε (j + 1) ω))) := by
  have hb : sfpBelief u s₁ ε (k + 1) ω = (1 / ((k : ℝ) + 1)) •
      (pureVec s₁ + ∑ j ∈ Finset.range k,
        sfpChoice u (sfpBelief u s₁ ε (j + 1) ω) (ε (j + 1)) ω) := by
    show (1 / (((k + 1 : ℕ)) : ℝ)) • sfpCum u s₁ ε (k + 1) ω = _
    rw [cum_eq]; push_cast; rfl
  rw [hb]
  have hsm : ((k : ℝ) / ((k : ℝ) + 1)) • ((1 / (k : ℝ)) • ∑ j ∈ Finset.range k,
      (sfpChoice u (sfpBelief u s₁ ε (j + 1) ω) (ε (j + 1)) ω -
        pbr f u (sfpBelief u s₁ ε (j + 1) ω))) =
      (1 / ((k : ℝ) + 1)) • ∑ j ∈ Finset.range k,
      (sfpChoice u (sfpBelief u s₁ ε (j + 1) ω) (ε (j + 1)) ω -
        pbr f u (sfpBelief u s₁ ε (j + 1) ω)) := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp
    · have hk : (k : ℝ) ≠ 0 := by positivity
      rw [smul_smul]
      congr 1
      field_simp
  rw [hsm, Finset.sum_sub_distrib]
  simp only [smul_add, smul_sub]
  abel

theorem tendsto_gap {Ω : Type*} (u : (α : Fin p) → Profile n → ℝ) (s₁ : Profile n)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞)
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (ω : Ω) (c0 : Mixed n)
    (h : Tendsto (fun k : ℕ => (1 / (k : ℝ)) •
      ∑ j ∈ Finset.range k, (sfpChoice u (sfpBelief u s₁ ε (j + 1) ω) (ε (j + 1)) ω -
        pbr f u (sfpBelief u s₁ ε (j + 1) ω))) atTop (𝓝 0)) :
    Tendsto (fun k : ℕ => sfpBelief u s₁ ε (k + 1) ω - (1 / ((k : ℝ) + 1)) •
        (c0 + ∑ j ∈ Finset.range k, pbr f u (sfpBelief u s₁ ε (j + 1) ω))) atTop (𝓝 0) := by
  simp_rw [sfp_gap_identity u s₁ f ε ω c0]
  have h1 : Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1)) • (pureVec s₁ - c0)) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const (pureVec s₁ - c0)
  have h2 : Tendsto (fun k : ℕ => ((k : ℝ) / ((k : ℝ) + 1))) atTop (𝓝 1) := by
    simpa using tendsto_natCast_div_add_atTop (1 : ℝ)
  have h3 := h2.smul h
  simp only [one_smul, smul_zero] at h3
  simpa using h1.add h3

end SFPCesaro

section ZS

variable {n : Fin 2 → ℕ}

theorem erase_fin2 (α : Fin 2) : (Finset.univ.erase α : Finset (Fin 2)) = {α + 1} := by
  fin_cases α <;> decide

/-- the payoff map of a two player game, as a linear map -/
noncomputable def Lm (u : (α : Fin 2) → Profile n → ℝ) : Mixed n →ₗ[ℝ] Mixed n where
  toFun x := payoffVec u x
  map_add' x y := by
    funext α i
    simp only [payoffVec, erase_fin2, Finset.prod_singleton, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs <;> simp [mul_add]
  map_smul' r x := by
    funext α i
    simp only [payoffVec, erase_fin2, Finset.prod_singleton, Pi.smul_apply, RingHom.id_apply,
      smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs <;> simp [mul_left_comm]

theorem Lm_apply (u : (α : Fin 2) → Profile n → ℝ) (x : Mixed n) : Lm u x = payoffVec u x := rfl

theorem Bm_Lm_zero (u : (α : Fin 2) → Profile n → ℝ) (hzs : ∀ s : Profile n, u 0 s = - u 1 s)
    (h : Mixed n) : Bm n h (Lm u h) = 0 := by
  have key : ∀ α, h α ⬝ᵥ payoffVec u h α = ∑ s : Profile n, u α s * ∏ β, h β (s β) := by
    intro α
    simp only [dotProduct, payoffVec]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← Finset.mul_prod_erase Finset.univ (fun β => h β (s β)) (Finset.mem_univ α)]
    ring
  rw [Bm_apply]
  show ∑ α, h α ⬝ᵥ payoffVec u h α = 0
  simp_rw [key]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [← Finset.sum_mul]
  have : ∑ α : Fin 2, u α s = 0 := by rw [Fin.sum_univ_two, hzs s]; ring
  rw [this, zero_mul]

end ZS

end StochFictPlay.ZeroSumESS.Aux22


namespace StochFictPlay.ZeroSumESS.Aux22

theorem part_ii {Ω : Type*} [MeasurableSpace Ω] (n : Fin 2 → ℕ) (hn : ∀ α, 1 ≤ n α)
    (u : (α : Fin 2) → Profile n → ℝ) (hzs : ∀ s : Profile n, u 0 s = - u 1 s)
    (f : (α : Fin 2) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℕ → (α : Fin 2) → Ω → (Fin (n α) → ℝ))
    (hε : IsShockFamily P f ε) (s₁ : Profile n) :
    ∃ xstar, restPoints (pField f u) (mixedProfiles n) = {xstar} ∧
      ∀ᵐ ω ∂P, Tendsto (fun t => sfpBelief u s₁ ε t ω) atTop (𝓝 xstar) := by
  have hneg : ∀ a ∈ mixedProfiles n, ∀ b ∈ mixedProfiles n,
      Bm n (b - a) (Lm u (b - a)) ≤ 0 :=
    fun a _ b _ => (Bm_Lm_zero u hzs _).le
  obtain ⟨xs, hxsX, hxs⟩ := exists_rest_mixed (f := f) hn hf (Lm u) hneg
  have huniq : ∀ x ∈ mixedProfiles n, CfM f (Lm u x) = x → x = xs := fun x _ hx =>
    unique_rest_mixed hn hf (Lm u) x xs (by rw [Bm_Lm_zero u hzs]) hx hxs
  have hpf : ∀ x, pField f u x = CfM f (Lm u x) - x := fun x => rfl
  refine ⟨xs, ?_, ?_⟩
  · ext x
    simp only [restPoints, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, h0⟩
      rw [hpf, sub_eq_zero] at h0
      exact huniq x hx h0
    · rintro rfl
      refine ⟨hxsX, ?_⟩
      rw [hpf, hxs, sub_self]
  · filter_upwards [sfp_lln P hn u f hf ε hε s₁] with ω hω
    have hlim0 := tendsto_gap u s₁ f ε ω (CfM f 0) hω
    have hlim : Tendsto (fun k : ℕ => sfpBelief u s₁ ε (k + 1) ω - (1 / ((k : ℝ) + 1)) •
        (CfM f 0 + ∑ j ∈ Finset.range k, CfM f (Lm u (sfpBelief u s₁ ε (j + 1) ω))))
        atTop (𝓝 0) := hlim0
    have := converge_det hn hf (Lm u) hneg xs huniq (fun t => sfpBelief u s₁ ε t ω) hlim
    exact (tendsto_add_atTop_iff_nat 1).1 this

end StochFictPlay.ZeroSumESS.Aux22


namespace StochFictPlay.ZeroSumESS.Aux22

section ESS

open Matrix in
theorem ess_negsemidef {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (xstar : Fin m → ℝ)
    (hess : IsInteriorESS A xstar) (d : Fin m → ℝ) (hd : ∑ i, d i = 0) :
    d ⬝ᵥ (A *ᵥ d) ≤ 0 := by
  obtain ⟨hint, N, hN, hesN⟩ := hess
  by_contra hcon
  push_neg at hcon
  have hd0 : d ≠ 0 := by
    rintro rfl
    simp at hcon
  have hopen : IsOpen (Set.pi Set.univ (fun _ : Fin m => Set.Ioi (0 : ℝ))) :=
    isOpen_set_pi Set.finite_univ (fun i _ => isOpen_Ioi)
  have hUn : N ∩ Set.pi Set.univ (fun _ : Fin m => Set.Ioi (0 : ℝ)) ∈ 𝓝 xstar :=
    Filter.inter_mem hN (hopen.mem_nhds (by simpa [Set.mem_pi] using hint.1))
  have hcont : Continuous (fun t : ℝ => xstar + t • d) := by fun_prop
  have h0 : (fun t : ℝ => xstar + t • d) ⁻¹' (N ∩ Set.pi Set.univ (fun _ : Fin m => Set.Ioi (0 : ℝ)))
      ∈ 𝓝 (0 : ℝ) := hcont.continuousAt.preimage_mem_nhds (by simpa using hUn)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 h0
  set s := δ / 2 with hsdef
  have hs : 0 < s := by positivity
  have hslt : s < δ := by linarith
  have key : ∀ t : ℝ, |t| = s → t * (d ⬝ᵥ (A *ᵥ xstar)) + t ^ 2 * (d ⬝ᵥ (A *ᵥ d)) < 0 := by
    intro t ht
    have htball : t ∈ Metric.ball (0 : ℝ) δ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, ht]; exact hslt
    have hmem := hball htball
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Ioi] at hmem
    obtain ⟨hmN, hpos⟩ := hmem
    have ht0 : t ≠ 0 := by
      rintro rfl; simp at ht; linarith
    have hsimp : xstar + t • d ∈ stdSimplex ℝ (Fin m) := by
      refine ⟨fun i => (hpos i).le, ?_⟩
      simp [Finset.sum_add_distrib, ← Finset.mul_sum, hd, hint.2]
    have hne : xstar + t • d ≠ xstar := by
      intro h
      have : t • d = 0 := by simpa using h
      rcases smul_eq_zero.1 this with h1 | h1
      · exact ht0 h1
      · exact hd0 h1
    have hlt := hesN (xstar + t • d) ⟨hsimp, hmN⟩ hne
    have expand : (xstar + t • d) ⬝ᵥ (A *ᵥ (xstar + t • d)) - xstar ⬝ᵥ (A *ᵥ (xstar + t • d)) =
        t * (d ⬝ᵥ (A *ᵥ xstar)) + t ^ 2 * (d ⬝ᵥ (A *ᵥ d)) := by
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul]
      ring
    linarith
  have h1 := key s (abs_of_pos hs)
  have h2 := key (-s) (by rw [abs_neg, abs_of_pos hs])
  nlinarith [mul_pos hs hs]

end ESS

end StochFictPlay.ZeroSumESS.Aux22


namespace StochFictPlay.ZeroSumESS.Aux22

section SymCore

open Matrix

/-- one player embedded into the profile formalism -/
abbrev n1 (m : ℕ) : Fin 1 → ℕ := fun _ => m

/-- the constant profile -/
def lift1 {m : ℕ} (x : Fin m → ℝ) : Mixed (n1 m) := fun _ => x

noncomputable def L1 {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) : Mixed (n1 m) →ₗ[ℝ] Mixed (n1 m) :=
  LinearMap.pi fun α => (Matrix.mulVecLin A).comp (LinearMap.proj α)

theorem L1_apply {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (x : Mixed (n1 m)) (α : Fin 1) :
    L1 A x α = A *ᵥ x α := rfl

theorem sym_core (m : ℕ) (hm : 1 ≤ m) (A : Matrix (Fin m) (Fin m) ℝ) (xstar : Fin m → ℝ)
    (hess : IsInteriorESS A xstar) (f : (Fin m → ℝ) → ℝ≥0∞) (hf : IsRegularDensity f) :
    ∃ xhat, restPoints (symField f A) (stdSimplex ℝ (Fin m)) = {xhat} ∧
      ∀ z : ℕ → (Fin m → ℝ),
        Tendsto (fun k : ℕ => z (k + 1) - (1 / ((k : ℝ) + 1)) •
          (choiceProb f 0 + ∑ j ∈ Finset.range k, choiceProb f (A *ᵥ z (j + 1))))
          atTop (𝓝 0) → Tendsto (fun k : ℕ => z (k + 1)) atTop (𝓝 xhat) := by
  set f' : (α : Fin 1) → (Fin (n1 m α) → ℝ) → ℝ≥0∞ := fun _ => f with hf'
  have hn : ∀ α : Fin 1, 1 ≤ n1 m α := fun _ => hm
  have hfr : ∀ α : Fin 1, IsRegularDensity (f' α) := fun _ => hf
  have hmem : ∀ x : Mixed (n1 m), x ∈ mixedProfiles (n1 m) ↔ x 0 ∈ stdSimplex ℝ (Fin m) := by
    intro x
    simp only [mixedProfiles, Set.mem_setOf_eq]
    exact ⟨fun h => h 0, fun h α => by rwa [Subsingleton.elim α 0]⟩
  have hneg : ∀ a ∈ mixedProfiles (n1 m), ∀ b ∈ mixedProfiles (n1 m),
      Bm (n1 m) (b - a) (L1 A (b - a)) ≤ 0 := by
    intro a ha b hb
    rw [hmem] at ha hb
    rw [Bm_apply, Fin.sum_univ_one]
    have hd : ∑ i, (b 0 - a 0) i = 0 := by
      simp only [Pi.sub_apply, Finset.sum_sub_distrib, ha.2, hb.2, sub_self]
    exact ess_negsemidef A xstar hess _ hd
  obtain ⟨xs, hxsX, hxs⟩ := exists_rest_mixed (f := f') hn hfr (L1 A) hneg
  refine ⟨xs 0, ?_, ?_⟩
  · ext x
    simp only [restPoints, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, h0⟩
      have hxl : lift1 x ∈ mixedProfiles (n1 m) := (hmem _).2 hx
      have hfix : CfM f' (L1 A (lift1 x)) = lift1 x := by
        funext α
        have : choiceProb f (A *ᵥ x) = x := by
          have := h0
          simp only [symField] at this
          exact sub_eq_zero.1 this
        exact this
      have := unique_rest_mixed hn hfr (L1 A) (lift1 x) xs
        (hneg xs hxsX _ hxl) hfix hxs
      exact congrFun this 0
    · rintro rfl
      refine ⟨(hmem _).1 hxsX, ?_⟩
      have := congrFun hxs 0
      simp only [symField]
      exact sub_eq_zero.2 this
  · intro z hz
    set z' : ℕ → Mixed (n1 m) := fun t => lift1 (z t) with hz'
    have hlim : Tendsto (fun k : ℕ => z' (k + 1) - (1 / ((k : ℝ) + 1)) •
        (CfM f' 0 + ∑ j ∈ Finset.range k, CfM f' (L1 A (z' (j + 1))))) atTop (𝓝 0) := by
      have hc : Continuous (lift1 : (Fin m → ℝ) → Mixed (n1 m)) :=
        continuous_pi fun _ => continuous_id
      have := (hc.tendsto 0).comp hz
      have h00 : lift1 (0 : Fin m → ℝ) = 0 := rfl
      rw [h00] at this
      refine this.congr fun k => ?_
      funext α
      simp [lift1, hz', CfM, L1_apply, hf', Finset.sum_apply]
    have := converge_det hn hfr (L1 A) hneg xs
      (fun x hx hfix => unique_rest_mixed hn hfr (L1 A) x xs (hneg xs hxsX x hx) hfix hxs)
      z' hlim
    exact ((continuous_apply 0).tendsto xs).comp this

end SymCore

end StochFictPlay.ZeroSumESS.Aux22


namespace StochFictPlay.ZeroSumESS.Aux22

section SymNoise

open Matrix

variable {m : ℕ}

/-- history σ-algebra of symmetric SFP -/
abbrev HistY {Ω : Type*} (ε : ℕ → Fin 2 → Ω → (Fin m → ℝ)) (t : ℕ) : MeasurableSpace Ω :=
  HistG (β := fun _ : ℕ × Fin 2 => Fin m → ℝ) (fun i ω => ε i.1 i.2 ω) Prod.fst t

theorem continuous_mulVec_coord (A : Matrix (Fin m) (Fin m) ℝ) (k : Fin m) :
    Continuous (fun z : Fin m → ℝ => (A *ᵥ z) k) :=
  (continuous_apply k).comp (Matrix.mulVecLin A).continuous_of_finiteDimensional

theorem meas_argmax_coord {Ω : Type*} [mΩ : MeasurableSpace Ω] (A : Matrix (Fin m) (Fin m) ℝ)
    (z : Ω → (Fin m → ℝ)) (hz : Measurable z) (e : Ω → (Fin m → ℝ)) (he : Measurable e)
    (k0 : Fin m) : Measurable (fun ω => argmaxVec (fun k => (A *ᵥ z ω) k + e ω k) k0) := by
  refine (measurable_argmaxVec_apply k0).comp (measurable_pi_lambda _ fun k => ?_)
  exact ((continuous_mulVec_coord A k).measurable.comp hz).add ((measurable_pi_apply k).comp he)

theorem meas_symStep {Ω : Type*} [mΩ : MeasurableSpace Ω] (A : Matrix (Fin m) (Fin m) ℝ)
    (z : Ω → (Fin m → ℝ)) (hz : Measurable z) (e : Fin 2 → Ω → (Fin m → ℝ))
    (he : ∀ r, Measurable (e r)) :
    Measurable (fun ω => ∑ r : Fin 2, argmaxVec (fun k => (A *ᵥ z ω) k + e r ω k)) := by
  refine measurable_pi_lambda _ fun k0 => ?_
  have : ∀ ω, (∑ r : Fin 2, argmaxVec (fun k => (A *ᵥ z ω) k + e r ω k)) k0 =
      ∑ r : Fin 2, argmaxVec (fun k => (A *ᵥ z ω) k + e r ω k) k0 := fun ω => by
    simp [Finset.sum_apply]
  simp_rw [this]
  exact Finset.measurable_sum _ fun r _ => meas_argmax_coord A z hz (e r) (he r) k0

theorem meas_symCum {Ω : Type*} [mΩ : MeasurableSpace Ω] (A : Matrix (Fin m) (Fin m) ℝ)
    (s₁ : Fin 2 → Fin m) (ε : ℕ → Fin 2 → Ω → (Fin m → ℝ)) (he : ∀ t r, Measurable (ε t r))
    (t : ℕ) : Measurable[HistY ε t] (symCum A s₁ ε t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    cases t with
    | zero => exact measurable_const
    | succ t =>
      have h1 : Measurable[HistY ε (t + 2)] (symCum A s₁ ε (t + 1)) :=
        ih.mono (HistG_mono _ _ (by omega)) le_rfl
      have hz : Measurable[HistY ε (t + 2)]
          (fun ω => (1 / (2 * ((t + 1 : ℕ) : ℝ))) • symCum A s₁ ε (t + 1) ω) :=
        h1.const_smul (1 / (2 * ((t + 1 : ℕ) : ℝ)))
      have hεt : ∀ r, Measurable[HistY ε (t + 2)] (ε (t + 1) r) := fun r =>
        measurable_HistG (β := fun _ : ℕ × Fin 2 => Fin m → ℝ)
          (fun i ω => ε i.1 i.2 ω) Prod.fst (t := t + 2) (t + 1, r) (by simp)
      have h2 : Measurable[HistY ε (t + 2)] (fun ω => ∑ r : Fin 2, argmaxVec (fun k =>
          (A *ᵥ ((1 / (2 * ((t + 1 : ℕ) : ℝ))) • symCum A s₁ ε (t + 1) ω)) k +
            ε (t + 1) r ω k)) :=
        @meas_symStep m Ω (HistY ε (t + 2)) A _ hz (fun r => ε (t + 1) r) hεt
      have key : symCum A s₁ ε (t + 2) = fun ω => symCum A s₁ ε (t + 1) ω +
          ∑ r : Fin 2, argmaxVec (fun k =>
            (A *ᵥ ((1 / (2 * ((t + 1 : ℕ) : ℝ))) • symCum A s₁ ε (t + 1) ω)) k +
              ε (t + 1) r ω k) := rfl
      rw [key]
      exact h1.add h2

theorem meas_symBelief {Ω : Type*} [mΩ : MeasurableSpace Ω] (A : Matrix (Fin m) (Fin m) ℝ)
    (s₁ : Fin 2 → Fin m) (ε : ℕ → Fin 2 → Ω → (Fin m → ℝ)) (he : ∀ t r, Measurable (ε t r))
    (t : ℕ) : Measurable[HistY ε t] (symBelief A s₁ ε t) :=
  Measurable.const_smul (meas_symCum A s₁ ε he t) (1 / (2 * (t : ℝ)))

theorem sym_cmp (hm : 1 ≤ m) {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Matrix (Fin m) (Fin m) ℝ)
    (f : (Fin m → ℝ) → ℝ≥0∞) (hf : IsRegularDensity f)
    (ε : ℕ → Fin 2 → Ω → (Fin m → ℝ)) (hε : IsSymShockFamily P f ε) (s₁ : Fin 2 → Fin m)
    (r : Fin 2) (k0 : Fin m) (t : ℕ) (Y : Ω → ℝ) (hY : Measurable[HistY ε (t + 1)] Y)
    (hYb : ∀ ω, |Y ω| ≤ 1) :
    ∫ ω, Y ω * argmaxVec (fun k => (A *ᵥ symBelief A s₁ ε (t + 1) ω) k + ε (t + 1) r ω k) k0 ∂P =
      ∫ ω, Y ω * choiceProb f (A *ᵥ symBelief A s₁ ε (t + 1) ω) k0 ∂P := by
  have : Nonempty (Fin m) := Fin.pos_iff_nonempty.1 hm
  have he' : ∀ i : ℕ × Fin 2, Measurable (fun ω => ε i.1 i.2 ω) := fun i => hε.1 i.1 i.2
  have hle : HistY ε (t + 1) ≤ mΩ :=
    HistG_le (β := fun _ : ℕ × Fin 2 => Fin m → ℝ) (fun i ω => ε i.1 i.2 ω) he' Prod.fst _
  have hz : Measurable[HistY ε (t + 1)] (symBelief A s₁ ε (t + 1)) :=
    meas_symBelief A s₁ ε hε.1 (t + 1)
  have hw' : Measurable[HistY ε (t + 1)] (fun ω => (Y ω, symBelief A s₁ ε (t + 1) ω)) :=
    hY.prodMk hz
  have hw : Measurable (fun ω => (Y ω, symBelief A s₁ ε (t + 1) ω)) := hw'.mono hle le_rfl
  have hind : IndepFun (fun ω => (Y ω, symBelief A s₁ ε (t + 1) ω)) (ε (t + 1) r) P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left
      (indep_HistG (β := fun _ : ℕ × Fin 2 => Fin m → ℝ) (fun i ω => ε i.1 i.2 ω) he'
        hε.2.2 Prod.fst (t + 1, r)) hw'.comap_le
  exact cm_argmax (f := f) hf P (ε (t + 1) r) (hε.1 _ _) (hε.2.1 (t + 1) r) _ hw hind
    (fun ω => hYb ω) (fun z => A *ᵥ z)
    (measurable_pi_lambda _ fun k => (continuous_mulVec_coord A k).measurable) k0

theorem sym_lln (hm : 1 ≤ m) {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Matrix (Fin m) (Fin m) ℝ)
    (f : (Fin m → ℝ) → ℝ≥0∞) (hf : IsRegularDensity f)
    (ε : ℕ → Fin 2 → Ω → (Fin m → ℝ)) (hε : IsSymShockFamily P f ε) (s₁ : Fin 2 → Fin m) :
    ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => (1 / (k : ℝ)) •
      ∑ j ∈ Finset.range k, ((1 / 2 : ℝ) • (∑ r : Fin 2, argmaxVec (fun k' =>
          (A *ᵥ symBelief A s₁ ε (j + 1) ω) k' + ε (j + 1) r ω k')) -
        choiceProb f (A *ᵥ symBelief A s₁ ε (j + 1) ω))) atTop (𝓝 0) := by
  have : Nonempty (Fin m) := Fin.pos_iff_nonempty.1 hm
  have he' : ∀ i : ℕ × Fin 2, Measurable (fun ω => ε i.1 i.2 ω) := fun i => hε.1 i.1 i.2
  have hall : ∀ k0 : Fin m, ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ => (1 / (k : ℝ)) * ∑ j ∈ Finset.range k,
        ((1 / 2 : ℝ) * ∑ r : Fin 2, argmaxVec (fun k' =>
          (A *ᵥ symBelief A s₁ ε (j + 1) ω) k' + ε (j + 1) r ω k') k0 -
          choiceProb f (A *ᵥ symBelief A s₁ ε (j + 1) ω) k0)) atTop (𝓝 0) := by
    intro k0
    refine lln_of_cmp P (HistY ε) (fun t => HistG_le (β := fun _ : ℕ × Fin 2 => Fin m → ℝ)
      (fun i ω => ε i.1 i.2 ω) he' Prod.fst t) (fun s t h => HistG_mono _ _ h)
      (fun j ω => (1 / 2 : ℝ) * ∑ r : Fin 2, argmaxVec (fun k' =>
          (A *ᵥ symBelief A s₁ ε (j + 1) ω) k' + ε (j + 1) r ω k') k0)
      (fun j ω => choiceProb f (A *ᵥ symBelief A s₁ ε (j + 1) ω) k0) ?_ ?_ ?_ ?_ ?_
    · intro j
      have hz : Measurable[HistY ε (j + 2)] (symBelief A s₁ ε (j + 1)) :=
        (meas_symBelief A s₁ ε hε.1 (j + 1)).mono (HistG_mono _ _ (by omega)) le_rfl
      have hεt : ∀ r, Measurable[HistY ε (j + 2)] (ε (j + 1) r) := fun r =>
        measurable_HistG (β := fun _ : ℕ × Fin 2 => Fin m → ℝ)
          (fun i ω => ε i.1 i.2 ω) Prod.fst (t := j + 2) (j + 1, r) (by simp)
      refine Measurable.const_mul (Finset.measurable_sum _ fun r _ => ?_) _
      exact @meas_argmax_coord m Ω (HistY ε (j + 2)) A _ hz _ (hεt r) k0
    · intro j
      refine ((continuous_apply k0).comp ((continuous_choiceProb hf).comp
        (Matrix.mulVecLin A).continuous_of_finiteDimensional)).measurable.comp
        (meas_symBelief A s₁ ε hε.1 (j + 1))
    · intro j ω
      have h0 : ∀ r : Fin 2, 0 ≤ argmaxVec (fun k' =>
          (A *ᵥ symBelief A s₁ ε (j + 1) ω) k' + ε (j + 1) r ω k') k0 ∧
          argmaxVec (fun k' => (A *ᵥ symBelief A s₁ ε (j + 1) ω) k' + ε (j + 1) r ω k') k0 ≤ 1 :=
        fun r => argmaxVec_mem01 _ _
      simp only [Fin.sum_univ_two]
      constructor <;> linarith [(h0 0).1, (h0 0).2, (h0 1).1, (h0 1).2]
    · intro j ω
      exact ⟨choiceProb_nonneg _ _, choiceProb_le_one hf _ _⟩
    · intro t Y hY hYb
      have hint : ∀ r : Fin 2, Integrable (fun ω => Y ω * argmaxVec (fun k' =>
          (A *ᵥ symBelief A s₁ ε (t + 1) ω) k' + ε (t + 1) r ω k') k0) P := by
        intro r
        have hYm : Measurable Y := hY.mono (HistG_le (β := fun _ : ℕ × Fin 2 => Fin m → ℝ)
          (fun i ω => ε i.1 i.2 ω) he' Prod.fst _) le_rfl
        have hzm : Measurable (symBelief A s₁ ε (t + 1)) :=
          (meas_symBelief A s₁ ε hε.1 (t + 1)).mono (HistG_le (β := fun _ : ℕ × Fin 2 =>
            Fin m → ℝ) (fun i ω => ε i.1 i.2 ω) he' Prod.fst _) le_rfl
        refine Integrable.of_bound (hYm.mul (meas_argmax_coord A _ hzm _ (hε.1 (t + 1) r) k0)).aestronglyMeasurable
          1 (Eventually.of_forall fun ω => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        have := argmaxVec_mem01 (fun k' => (A *ᵥ symBelief A s₁ ε (t + 1) ω) k' +
          ε (t + 1) r ω k') k0
        rw [abs_of_nonneg this.1]
        nlinarith [hYb ω, abs_nonneg (Y ω), this.2]
      have e : (fun ω => Y ω * ((1 / 2 : ℝ) * ∑ r : Fin 2, argmaxVec (fun k' =>
          (A *ᵥ symBelief A s₁ ε (t + 1) ω) k' + ε (t + 1) r ω k') k0)) = fun ω =>
          (1 / 2 : ℝ) * (Y ω * argmaxVec (fun k' =>
            (A *ᵥ symBelief A s₁ ε (t + 1) ω) k' + ε (t + 1) 0 ω k') k0) +
          (1 / 2 : ℝ) * (Y ω * argmaxVec (fun k' =>
            (A *ᵥ symBelief A s₁ ε (t + 1) ω) k' + ε (t + 1) 1 ω k') k0) := by
        funext ω; simp only [Fin.sum_univ_two]; ring
      rw [e, integral_add ((hint 0).const_mul _) ((hint 1).const_mul _), integral_const_mul,
        integral_const_mul, sym_cmp hm P A f hf ε hε s₁ 0 k0 t Y hY hYb,
        sym_cmp hm P A f hf ε hε s₁ 1 k0 t Y hY hYb]
      ring
  have hall' := (ae_all_iff).2 hall
  filter_upwards [hall'] with ω hω
  refine tendsto_pi_nhds.2 fun k0 => ?_
  refine (hω k0).congr fun k => ?_
  simp only [Pi.smul_apply, Finset.sum_apply, Pi.sub_apply, smul_eq_mul]

end SymNoise

end StochFictPlay.ZeroSumESS.Aux22


universe u

namespace StochFictPlay.ZeroSumESS.Aux22

section SymCesaro

open Matrix

variable {m : ℕ}

theorem symcum_eq {Ω : Type*} (A : Matrix (Fin m) (Fin m) ℝ) (s₁ : Fin 2 → Fin m)
    (ε : ℕ → Fin 2 → Ω → (Fin m → ℝ)) (ω : Ω) (k : ℕ) :
    symCum A s₁ ε (k + 1) ω = (Pi.single (s₁ 0) (1 : ℝ) + Pi.single (s₁ 1) (1 : ℝ)) +
      ∑ j ∈ Finset.range k, ∑ r : Fin 2, argmaxVec (fun k' =>
        (A *ᵥ symBelief A s₁ ε (j + 1) ω) k' + ε (j + 1) r ω k') := by
  induction k with
  | zero => simp [symCum]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih]
    rfl

theorem sym_gap_identity {Ω : Type*} (A : Matrix (Fin m) (Fin m) ℝ) (s₁ : Fin 2 → Fin m)
    (f : (Fin m → ℝ) → ℝ≥0∞) (ε : ℕ → Fin 2 → Ω → (Fin m → ℝ)) (ω : Ω) (c0 : Fin m → ℝ)
    (k : ℕ) :
    symBelief A s₁ ε (k + 1) ω - (1 / ((k : ℝ) + 1)) •
        (c0 + ∑ j ∈ Finset.range k, choiceProb f (A *ᵥ symBelief A s₁ ε (j + 1) ω)) =
      ((1 / 2 : ℝ) * (1 / ((k : ℝ) + 1))) •
          (Pi.single (s₁ 0) (1 : ℝ) + Pi.single (s₁ 1) (1 : ℝ) - (2 : ℝ) • c0) +
        ((k : ℝ) / ((k : ℝ) + 1)) • ((1 / (k : ℝ)) • ∑ j ∈ Finset.range k,
          ((1 / 2 : ℝ) • (∑ r : Fin 2, argmaxVec (fun k' =>
              (A *ᵥ symBelief A s₁ ε (j + 1) ω) k' + ε (j + 1) r ω k')) -
            choiceProb f (A *ᵥ symBelief A s₁ ε (j + 1) ω))) := by
  have hb : symBelief A s₁ ε (k + 1) ω = (1 / (2 * ((k : ℝ) + 1))) •
      ((Pi.single (s₁ 0) (1 : ℝ) + Pi.single (s₁ 1) (1 : ℝ)) +
        ∑ j ∈ Finset.range k, ∑ r : Fin 2, argmaxVec (fun k' =>
          (A *ᵥ symBelief A s₁ ε (j + 1) ω) k' + ε (j + 1) r ω k')) := by
    show (1 / (2 * (((k + 1 : ℕ)) : ℝ))) • symCum A s₁ ε (k + 1) ω = _
    rw [symcum_eq]; push_cast; rfl
  rw [hb]
  have hsm : ((k : ℝ) / ((k : ℝ) + 1)) • ((1 / (k : ℝ)) • ∑ j ∈ Finset.range k,
      ((1 / 2 : ℝ) • (∑ r : Fin 2, argmaxVec (fun k' =>
          (A *ᵥ symBelief A s₁ ε (j + 1) ω) k' + ε (j + 1) r ω k')) -
        choiceProb f (A *ᵥ symBelief A s₁ ε (j + 1) ω))) =
      (1 / ((k : ℝ) + 1)) • ∑ j ∈ Finset.range k,
      ((1 / 2 : ℝ) • (∑ r : Fin 2, argmaxVec (fun k' =>
          (A *ᵥ symBelief A s₁ ε (j + 1) ω) k' + ε (j + 1) r ω k')) -
        choiceProb f (A *ᵥ symBelief A s₁ ε (j + 1) ω)) := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp
    · have hk : (k : ℝ) ≠ 0 := by positivity
      rw [smul_smul]
      congr 1
      field_simp
  rw [hsm, Finset.sum_sub_distrib, ← Finset.smul_sum]
  have h1 : (1 / (2 * ((k : ℝ) + 1))) = (1 / 2 : ℝ) * (1 / ((k : ℝ) + 1)) := by
    field_simp
  rw [h1]
  have h2 : (1 / (k + 1 : ℝ)) = (1 / ((k : ℝ) + 1)) := rfl
  module

theorem sym_tendsto_gap {Ω : Type*} (A : Matrix (Fin m) (Fin m) ℝ) (s₁ : Fin 2 → Fin m)
    (f : (Fin m → ℝ) → ℝ≥0∞) (ε : ℕ → Fin 2 → Ω → (Fin m → ℝ)) (ω : Ω) (c0 : Fin m → ℝ)
    (h : Tendsto (fun k : ℕ => (1 / (k : ℝ)) •
      ∑ j ∈ Finset.range k, ((1 / 2 : ℝ) • (∑ r : Fin 2, argmaxVec (fun k' =>
          (A *ᵥ symBelief A s₁ ε (j + 1) ω) k' + ε (j + 1) r ω k')) -
        choiceProb f (A *ᵥ symBelief A s₁ ε (j + 1) ω))) atTop (𝓝 0)) :
    Tendsto (fun k : ℕ => symBelief A s₁ ε (k + 1) ω - (1 / ((k : ℝ) + 1)) •
        (c0 + ∑ j ∈ Finset.range k, choiceProb f (A *ᵥ symBelief A s₁ ε (j + 1) ω)))
        atTop (𝓝 0) := by
  simp_rw [sym_gap_identity A s₁ f ε ω c0]
  have h1 : Tendsto (fun k : ℕ => ((1 / 2 : ℝ) * (1 / ((k : ℝ) + 1))) •
      (Pi.single (s₁ 0) (1 : ℝ) + Pi.single (s₁ 1) (1 : ℝ) - (2 : ℝ) • c0)) atTop (𝓝 0) := by
    have := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2 : ℝ)).smul_const
      (Pi.single (s₁ 0) (1 : ℝ) + Pi.single (s₁ 1) (1 : ℝ) - (2 : ℝ) • c0)
    simpa using this
  have h2 : Tendsto (fun k : ℕ => ((k : ℝ) / ((k : ℝ) + 1))) atTop (𝓝 1) := by
    simpa using tendsto_natCast_div_add_atTop (1 : ℝ)
  have h3 := h2.smul h
  simp only [one_smul, smul_zero] at h3
  simpa using h1.add h3

theorem part_i {Ω : Type*} [MeasurableSpace Ω] (m : ℕ) (A : Matrix (Fin m) (Fin m) ℝ)
    (hess : ∃ xstar, IsInteriorESS A xstar) (f : (Fin m → ℝ) → ℝ≥0∞) (hf : IsRegularDensity f)
    (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℕ → Fin 2 → Ω → (Fin m → ℝ))
    (hε : IsSymShockFamily P f ε) (s₁ : Fin 2 → Fin m) :
    ∃ xhat, restPoints (symField f A) (stdSimplex ℝ (Fin m)) = {xhat} ∧
      ∀ᵐ ω ∂P, Tendsto (fun t => symBelief A s₁ ε t ω) atTop (𝓝 xhat) := by
  obtain ⟨xstar, hxs⟩ := hess
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      have := hxs.1.2
      simp at this
    · exact h
  obtain ⟨xhat, hrest, hconv⟩ := sym_core m hm A xstar hxs f hf
  refine ⟨xhat, hrest, ?_⟩
  filter_upwards [sym_lln hm P A f hf ε hε s₁] with ω hω
  have hlim0 := sym_tendsto_gap A s₁ f ε ω (choiceProb f 0) hω
  have := hconv (fun t => symBelief A s₁ ε t ω) hlim0
  exact (tendsto_add_atTop_iff_nat 1).1 this

end SymCesaro

end StochFictPlay.ZeroSumESS.Aux22

open scoped ENNReal in open MeasureTheory ProbabilityTheory Filter Topology Matrix in open StochFictPlay.ZeroSumESS in
theorem solution :
    (∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℝ), (∃ xstar, IsInteriorESS A xstar) →
      ∀ (f : (Fin m → ℝ) → ℝ≥0∞), IsRegularDensity f →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ε : ℕ → Fin 2 → Ω → (Fin m → ℝ)), IsSymShockFamily P f ε →
      ∀ (s₁ : Fin 2 → Fin m),
        ∃ xhat, restPoints (symField f A) (stdSimplex ℝ (Fin m)) = {xhat} ∧
          ∀ᵐ ω ∂P, Tendsto (fun t => symBelief A s₁ ε t ω) atTop (𝓝 xhat)) ∧
    (∀ (n : Fin 2 → ℕ), (∀ α, 1 ≤ n α) →
      ∀ (u : (α : Fin 2) → Profile n → ℝ), (∀ s : Profile n, u 0 s = -u 1 s) →
      ∀ (f : (α : Fin 2) → (Fin (n α) → ℝ) → ℝ≥0∞), (∀ α, IsRegularDensity (f α)) →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ε : ℕ → (α : Fin 2) → Ω → (Fin (n α) → ℝ)), IsShockFamily P f ε →
      ∀ (s₁ : Profile n),
        ∃ xstar, restPoints (pField f u) (mixedProfiles n) = {xstar} ∧
          ∀ᵐ ω ∂P, Tendsto (fun t => sfpBelief u s₁ ε t ω) atTop (𝓝 xstar)) := by
  refine ⟨?_, ?_⟩
  · intro m A hess f hf Ω _ P _ ε hε s₁
    exact StochFictPlay.ZeroSumESS.Aux22.part_i m A hess f hf P ε hε s₁
  · intro n hn u hzs f hf Ω _ P _ ε hε s₁
    exact StochFictPlay.ZeroSumESS.Aux22.part_ii n hn u hzs f hf P ε hε s₁
