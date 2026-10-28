-- Prove2me | solution 1 for QuantumWalkSearch.ApproxRAA.drift_third
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T22:37:06.604132+00:00
-- url     : https://prove2.me/submissions/50059188-58ad-434e-badb-d4ccc84caea4

import Mathlib
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Setting
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Circuit
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Tolerant

namespace Aux_QWS_dt

open QuantumWalkSearch.ApproxRAA Matrix

lemma norm_sq_ite (c : Prop) [Decidable c] (a : ℂ) :
    ‖(if c then a else 0)‖ ^ 2 = if c then ‖a‖ ^ 2 else 0 := by
  split_ifs <;> simp

lemma act_diag_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℂ)
    (v : EuclideanSpace ℂ ι) (p : ι) : (act (Matrix.diagonal d) v) p = d p * v p := by
  simp [act, mulVec_diagonal]

end Aux_QWS_dt

open QuantumWalkSearch.ApproxRAA Matrix Aux_QWS_dt in
theorem solution {X : Type*} [Fintype X] [DecidableEq X] {κ : ℕ → Type*}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (M : Finset X) (piState : EuclideanSpace ℂ (X × X)) (hπ : ‖piState‖ = 1)
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ)
    (hpM : markedWeight M piState < 1) (T : ℕ) :
    ‖muPerp M z R piState T 0 - phi M z R piState T 0‖ =
        Real.sqrt (2 - 2 * Real.cos (Real.arcsin (Real.sqrt (markedWeight M piState)))) ∧
      Real.sqrt (2 - 2 * Real.cos (Real.arcsin (Real.sqrt (markedWeight M piState)))) =
        2 * Real.sin (Real.arcsin (Real.sqrt (markedWeight M piState)) / 2) ∧
      2 * Real.sin (Real.arcsin (Real.sqrt (markedWeight M piState)) / 2) ≤
        Real.arcsin (Real.sqrt (markedWeight M piState)) := by
  obtain ⟨m, hm⟩ : ∃ m, m = markedWeight M piState := ⟨_, rfl⟩
  rw [← hm] at hpM ⊢
  have hm0 : 0 ≤ m := by rw [hm]; unfold markedWeight; positivity
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = Real.arcsin (Real.sqrt m) := ⟨_, rfl⟩
  rw [← hθ]
  have hθ0 : 0 ≤ θ := by rw [hθ]; exact Real.arcsin_nonneg.mpr (Real.sqrt_nonneg _)
  have hθ1 : θ ≤ Real.pi / 2 := by rw [hθ]; exact Real.arcsin_le_pi_div_two _
  have hcos : Real.cos θ = Real.sqrt (1 - m) := by
    rw [hθ, Real.cos_arcsin, Real.sq_sqrt hm0]
  have hs0 : 0 ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hcos2 : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h := Real.cos_sq_add_sin_sq (θ / 2)
    have h2 : Real.cos θ = Real.cos (2 * (θ / 2)) := by ring_nf
    rw [h2, Real.cos_two_mul]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · -- the norm computation
    rw [hcos]
    have hphi : phi M z R piState T 0 = initState z T piState := by
      simp [phi, approxRAA, act]
    rw [hphi]
    set v := initState z T piState with hv
    -- weights
    set a := ∑ p : X × X × Regs κ T, (if p.1 ∈ M then 0 else ‖v p‖ ^ 2) with ha
    set b := ∑ p : X × X × Regs κ T, (if p.1 ∈ M then ‖v p‖ ^ 2 else 0) with hb
    have hvp : ∀ p : X × X × Regs κ T, v p =
        if p.2.2 = zeroRegs z T then piState (p.1, p.2.1) else 0 := by
      intro p; simp [hv, initState, tensorZero]
    have hcollapse : ∀ (g : X → X → ℝ),
        (∑ p : X × X × Regs κ T, g p.1 p.2.1 * ‖v p‖ ^ 2) =
          ∑ q : X × X, g q.1 q.2 * ‖piState q‖ ^ 2 := by
      intro g
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [hvp, norm_sq_ite, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq' Finset.univ (zeroRegs z T)]
      simp
    have hab : a + b = 1 := by
      have h1 := hcollapse (fun _ _ => 1)
      simp only [one_mul] at h1
      calc a + b = ∑ p : X × X × Regs κ T, ‖v p‖ ^ 2 := by
            rw [ha, hb, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl (fun p _ => by split_ifs <;> simp)
        _ = ∑ q : X × X, ‖piState q‖ ^ 2 := h1
        _ = 1 := by rw [← EuclideanSpace.norm_sq_eq, hπ, one_pow]
    have hbm : b = m := by
      have h2 := hcollapse (fun x _ => if x ∈ M then 1 else 0)
      simp only [ite_mul, one_mul, zero_mul] at h2
      rw [hb, h2, hm]
      unfold markedWeight markedProj
      rw [EuclideanSpace.norm_sq_eq]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [act_diag_apply]
      split_ifs <;> simp
    have ha1 : a = 1 - m := by linarith
    have hapos : 0 < a := by linarith
    -- norm of u
    set u := act (unmarkedProj M) v with hu
    have hua : ‖u‖ ^ 2 = a := by
      rw [EuclideanSpace.norm_sq_eq, ha]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hu, unmarkedProj, act_diag_apply]
      split_ifs <;> simp
    have hun : ‖u‖ = Real.sqrt a := by
      rw [← hua, Real.sqrt_sq (norm_nonneg _)]
    have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr hapos
    -- the difference
    have hdiff : ‖muPerp M z R piState T 0 - v‖ ^ 2 = b + ((Real.sqrt a)⁻¹ - 1) ^ 2 * a := by
      have hmu : muPerp M z R piState T 0 = QuantumWalkSearch.ApproxRAA.normalize u := by
        simp [muPerp, hphi, hu, hv]
      have hentry : ∀ p, (QuantumWalkSearch.ApproxRAA.normalize u - v) p =
          if p.1 ∈ M then -v p else ((((Real.sqrt a)⁻¹ - 1 : ℝ)) : ℂ) * v p := by
        intro p
        have hup : u p = (if p.1 ∈ M then 0 else 1) * v p := by
          rw [hu, unmarkedProj, act_diag_apply]
        simp only [QuantumWalkSearch.ApproxRAA.normalize, PiLp.sub_apply, PiLp.smul_apply, hup,
          hun]
        split_ifs
        · simp
        · rw [Complex.real_smul]; push_cast; ring
      rw [hmu, EuclideanSpace.norm_sq_eq]
      simp only [hentry]
      rw [hb, ha, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      split_ifs
      · simp
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]; ring
    have hval : b + ((Real.sqrt a)⁻¹ - 1) ^ 2 * a = 2 - 2 * Real.sqrt (1 - m) := by
      rw [← ha1, hbm]
      have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt hapos.le
      have h3 : ((Real.sqrt a)⁻¹ - 1) ^ 2 * Real.sqrt a ^ 2 = (1 - Real.sqrt a) ^ 2 := by
        field_simp <;> ring
      have this : ((Real.sqrt a)⁻¹ - 1) ^ 2 * a = (1 - Real.sqrt a) ^ 2 := by
        rw [hsq] at h3; exact h3
      rw [this]
      nlinarith
    rw [← hval, ← hdiff, Real.sqrt_sq (norm_nonneg _)]
  · rw [hcos2]
    rw [show 2 - 2 * (1 - 2 * Real.sin (θ / 2) ^ 2) = (2 * Real.sin (θ / 2)) ^ 2 by ring]
    exact Real.sqrt_sq (by linarith)
  · have := Real.sin_le (by linarith : 0 ≤ θ / 2)
    linarith
