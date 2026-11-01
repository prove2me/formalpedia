-- Prove2me | solution 1 for ProxBundle.GPB.proposition_4_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T03:55:52.971855+00:00
-- url     : https://prove2.me/submissions/aaf330d6-2639-46e0-b4ff-240c54e13062

import Mathlib
import Definitions.Def_ProxBundle_GPB_Model
import Theorems.Thm_ProxBundle_GPB_lemma_4_6
import Theorems.Thm_ProxBundle_GPB_lemma_4_7

open ProxBundle.GPB

theorem solution {n : ℕ} (P : Instance n) (μ Mbar Lbar lam ε τ : ℝ)
    (x0 x0s : E n) (R : Run n)
    (hμ : 0 ≤ μ) (hM : 0 ≤ Mbar) (hL : 0 ≤ Lbar)
    (hA1 : P.A1 μ) (hA3 : P.A3 Mbar Lbar)
    (hlam : 0 < lam) (hε : 0 < ε)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (h29 : Cond29 μ lam ε τ Mbar Lbar)
    (hx0 : x0 ∈ P.D) (hopt : P.IsNearestOpt x0 x0s)
    (hrun : IsRun P μ lam ε τ x0 R)
    (j0 : ℕ) (hserious : R.t P lam j0 ≤ ε / 2)
    (hbefore : j0 = 0 ∨ ε < P.φ (R.y j0) - P.φ x0s) :
    ∃ j1 : ℕ, j0 < j1 ∧ R.t P lam j1 ≤ ε / 2 ∧
      (∀ i : ℕ, j0 < i → i < j1 → ε / 2 < R.t P lam i) ∧
      (((j1 - j0 : ℕ) : ℝ) ≤
        (⌈max (Real.log (4 * tbar Mbar Lbar lam ‖x0 - x0s‖ / ε)) 0 /
          (1 - τ)⌉ : ℝ) + 1) ∧
      (∀ Mf Lf : ℝ, 0 < Mf ^ 2 + ε * Lf → τ = tau38 μ lam ε Mf Lf →
        ((j1 - j0 : ℕ) : ℝ) ≤
          (⌈(1 + 8 * lamMu μ lam * (Mf ^ 2 + ε * Lf) / ε) *
            max (Real.log (4 * tbar Mbar Lbar lam ‖x0 - x0s‖ / ε)) 0⌉ : ℝ) + 1) := by
  classical
  set tb := tbar Mbar Lbar lam ‖x0 - x0s‖ with htb
  have h47 : R.t P lam (j0 + 1) ≤ tb :=
    ProxBundle.GPB.lemma_4_7 P μ Mbar Lbar lam ε τ x0 x0s R hμ hM hL hA1 hA3 hlam hε
      hτ0 hτ1 h29 hx0 hopt hrun j0 hserious hbefore
  have h1τ : 0 < 1 - τ := by linarith
  -- key estimate: a run of nulls j0+1, ..., j0+1+m forces (1-τ) m < log(4 t̄/ε)
  have hclaim : ∀ m : ℕ, (∀ i, j0 < i → i ≤ j0 + 1 + m → ε / 2 < R.t P lam i) →
      (1 - τ) * m < Real.log (4 * tb / ε) := by
    intro m hnull
    have hcontr : ∀ m', m' ≤ m → R.t P lam (j0 + 1 + m') - ε / 4 ≤
        τ ^ m' * (R.t P lam (j0 + 1) - ε / 4) := by
      intro m'
      induction m' with
      | zero => intro _; simp
      | succ m' ih =>
        intro hm'
        have h46 := ProxBundle.GPB.lemma_4_6 P μ Mbar Lbar lam ε τ x0 R hμ hM hL hA1 hA3
          hlam hε hτ0 hτ1 h29 hx0 hrun (j0 + 1 + m') (by omega) (hnull _ (by omega) (by omega))
        rw [show j0 + 1 + (m' + 1) = j0 + 1 + m' + 1 by ring, pow_succ]
        calc _ ≤ τ * (R.t P lam (j0 + 1 + m') - ε / 4) := h46
          _ ≤ τ * (τ ^ m' * (R.t P lam (j0 + 1) - ε / 4)) :=
              mul_le_mul_of_nonneg_left (ih (by omega)) hτ0.le
          _ = _ := by ring
    have hlast := hcontr m le_rfl
    have hnm := hnull (j0 + 1 + m) (by omega) le_rfl
    have hn1 := hnull (j0 + 1) (by omega) (by omega)
    have hpow : τ ^ m ≤ Real.exp ((τ - 1) * m) := by
      have h1 : τ ≤ Real.exp (τ - 1) := by
        have := Real.add_one_le_exp (τ - 1); linarith
      calc τ ^ m ≤ (Real.exp (τ - 1)) ^ m := pow_le_pow_left₀ hτ0.le h1 m
        _ = Real.exp ((τ - 1) * m) := by rw [← Real.exp_nat_mul]; ring_nf
    have hstep : ε / 4 < Real.exp ((τ - 1) * m) * tb := by
      have ha : 0 ≤ R.t P lam (j0 + 1) - ε / 4 := by linarith
      have e1 : τ ^ m * (R.t P lam (j0 + 1) - ε / 4) ≤
          Real.exp ((τ - 1) * m) * (R.t P lam (j0 + 1) - ε / 4) :=
        mul_le_mul_of_nonneg_right hpow ha
      have e2 : Real.exp ((τ - 1) * m) * (R.t P lam (j0 + 1) - ε / 4) ≤
          Real.exp ((τ - 1) * m) * tb :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      linarith
    have htbpos : 0 < tb := by
      by_contra h
      push Not at h
      have : Real.exp ((τ - 1) * m) * tb ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le h
      linarith
    have hexp : Real.exp ((1 - τ) * m) < 4 * tb / ε := by
      have e : Real.exp ((τ - 1) * m) * Real.exp ((1 - τ) * m) = 1 := by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      have := mul_lt_mul_of_pos_right hstep (Real.exp_pos ((1 - τ) * m))
      rw [mul_right_comm, e, one_mul] at this
      rw [lt_div_iff₀ hε]
      linarith
    exact (Real.lt_log_iff_exp_lt (by positivity)).mpr hexp
  -- the cycle ends
  have hex : ∃ j, j0 < j ∧ R.t P lam j ≤ ε / 2 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨m, hm⟩ := exists_nat_gt (Real.log (4 * tb / ε) / (1 - τ))
    have := hclaim m (fun i hi _ => hcon i hi)
    rw [div_lt_iff₀ h1τ] at hm
    linarith
  set j1 := Nat.find hex with hj1
  obtain ⟨hj1gt, hj1s⟩ := Nat.find_spec hex
  have hbtw : ∀ i, j0 < i → i < j1 → ε / 2 < R.t P lam i := by
    intro i h1 h2
    have := Nat.find_min hex h2
    push Not at this
    exact this h1
  -- the bound (59) with rounding
  have hX : (((j1 - j0 : ℕ) : ℝ)) ≤
      (⌈max (Real.log (4 * tb / ε)) 0 / (1 - τ)⌉ : ℝ) + 1 := by
    have hX0 : 0 ≤ max (Real.log (4 * tb / ε)) 0 / (1 - τ) :=
      div_nonneg (le_max_right _ _) h1τ.le
    rcases Nat.lt_or_ge (j1 - j0) 2 with hsmall | hbig
    · have : ((j1 - j0 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (by omega : j1 - j0 ≤ 1)
      have : (0:ℝ) ≤ (⌈max (Real.log (4 * tb / ε)) 0 / (1 - τ)⌉ : ℝ) := by
        exact_mod_cast Int.ceil_nonneg hX0
      linarith
    · set m := j1 - j0 - 2 with hm
      have hc := hclaim m (fun i h1 h2 => hbtw i h1 (by omega))
      have hmX : (m : ℝ) < max (Real.log (4 * tb / ε)) 0 / (1 - τ) := by
        rw [lt_div_iff₀ h1τ]
        have := le_max_left (Real.log (4 * tb / ε)) 0
        linarith
      have hmc : (m : ℝ) < (⌈max (Real.log (4 * tb / ε)) 0 / (1 - τ)⌉ : ℝ) :=
        lt_of_lt_of_le hmX (Int.le_ceil _)
      have hint : (m : ℤ) + 1 ≤ ⌈max (Real.log (4 * tb / ε)) 0 / (1 - τ)⌉ := by
        have : ((m : ℤ) : ℝ) < (⌈max (Real.log (4 * tb / ε)) 0 / (1 - τ)⌉ : ℝ) := by
          exact_mod_cast hmc
        exact_mod_cast this
      have hcast : ((m : ℤ) : ℝ) + 1 ≤ (⌈max (Real.log (4 * tb / ε)) 0 / (1 - τ)⌉ : ℝ) := by
        exact_mod_cast hint
      have : ((j1 - j0 : ℕ) : ℝ) = (m : ℝ) + 2 := by
        rw [hm]; norm_num [Nat.cast_sub (by omega : 2 ≤ j1 - j0)]
      push_cast at hcast
      linarith
  refine ⟨j1, hj1gt, hj1s, hbtw, hX, ?_⟩
  intro Mf Lf hpos hτeq
  have e : max (Real.log (4 * tb / ε)) 0 / (1 - τ) =
      (1 + 8 * lamMu μ lam * (Mf ^ 2 + ε * Lf) / ε) * max (Real.log (4 * tb / ε)) 0 := by
    have hinv : 1 / (1 - τ) = 1 + 8 * lamMu μ lam * (Mf ^ 2 + ε * Lf) / ε := by
      have hlm : 0 < 1 + lam * μ := by positivity
      rw [hτeq, tau38]
      unfold lamMu
      have hq : 0 < (1 + lam * μ) * ε / (8 * lam * (Mf ^ 2 + ε * Lf)) := by positivity
      have hne : 1 + (1 + lam * μ) * ε / (8 * lam * (Mf ^ 2 + ε * Lf)) ≠ 0 := by positivity
      field_simp
      ring
    rw [div_eq_mul_one_div, hinv, mul_comm]
  rw [← e]
  exact hX
