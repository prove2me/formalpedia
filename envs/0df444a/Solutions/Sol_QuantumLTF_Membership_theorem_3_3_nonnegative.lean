-- Prove2me | solution 1 for QuantumLTF.Membership.theorem_3_3_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:48:27.91756+00:00
-- url     : https://prove2.me/submissions/3e27fbcb-39ed-4630-80f5-02f9f796fd3d

import Theorems.Thm_QuantumLTF_Membership_theorem_3_3_single_run
import Theorems.Thm_QuantumLTF_Membership_coordinatewise_median_amplification_uniform

open QAlgorithms QuantumLTF.Membership

/-- **Theorem 3.3 (Gradient estimation).** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorem 3.3, p. 27 (PDF p. 28), Eqs. (49)–(51). For
`n ≥ 2`, under the conditions of Theorem 3.2 with `0 < ϵ ≤ 1/2`, let `g := ∇h_p = −w/⟨w, p⟩`, `0 < ϵ_g ≤ 10`,
`0 < γ ≤ 1/2`, `η := ρϵ_g / (48π(3n+1))`, `b := ⌈log₂((3n+1)/(ρϵ_g))⌉`. Given an oracle
`O_H : |x⟩|0⟩ → |x⟩|H̃_p(x)⟩` with `|H̃_p(x) − H_p(x)| ≤ η` for every `x ∈ G_b^n`, one calculates `g̃ ∈ Rⁿ` with
`‖g̃ − g‖_∞ ≤ ϵ_g` with probability at least `1 − γ`, using `O(log(1/γ))` queries to `O_H` and its inverse
and `O((n log²(n/ϵ_g) + log(1/ϵ)) log(1/γ))` other gates.

**Formalization Note.** `O_H` is any unitary with the stated action on `|x⟩|0⟩|0⟩`. The circuit depends on
the register format but not on `w, θ, p, O_H`. Of the conditions of Theorem 3.2 only
`1/10 ≤ |⟨w, p⟩| ≤ 3` is kept: the statement does not use `s` or `h̃` (a generalization). `queryCount` counts `O_H` and its inverse. The classical
median of p. 30 is inside the circuit. The value register has `O(log(1/ϵ) + log(1/η))` bits (p. 30),
a hypothesis with universal `C₁` before `C`. -/
theorem solution (C₁ : ℝ) (hC₁ : 0 ≤ C₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ ε εg γ : ℝ, 0 < ε → ε ≤ 1 / 2 → 0 < εg → εg ≤ 10 →
      0 < γ → γ ≤ 1 / 2 →
      let η : ℝ := rho n * εg / (48 * Real.pi * (3 * n + 1))
      let b : ℕ := ⌈Real.logb 2 ((3 * n + 1) / (rho n * εg))⌉₊
      ∀ Vb Vf W : ℕ, (Vb : ℝ) ≤ C₁ * (Real.log (1 / ε) + Real.log (1 / η)) →
        ∃ (m ℓo fo : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n * b + Vb + W) m)
          (oa : Fin n → (Fin ℓo ↪ Fin m)),
          Uncontrolled c ∧
          (c.queryCount 0 : ℝ) ≤ C * Real.log (1 / γ) ∧
          (c.gateCount : ℝ) ≤ C * (n * (Real.log (n / εg)) ^ 2 + Real.log (1 / ε)) *
            Real.log (1 / γ) ∧
          ∀ (w p : EuclideanSpace ℝ (Fin n)) (θ : ℝ), ‖w‖ = 1 →
            1 / 10 ≤ |inner ℝ w p| → |inner ℝ w p| ≤ 3 →
            ∀ Htil : (Fin n → Qubits b) → Qubits Vb,
              (∀ x, |fpVal Vb Vf (Htil x) - height w θ p (rho n • gridVec n b x)| ≤ η) →
            ∀ OH : Matrix (Qubits (n * b + Vb + W)) (Qubits (n * b + Vb + W)) ℂ,
              OH ∈ Matrix.unitaryGroup (Qubits (n * b + Vb + W)) ℂ →
              (∀ x, act OH (ket (regBasis n b Vb W x fun _ => false)) =
                ket (regBasis n b Vb W x (Htil x))) →
              open Classical in
              probEvent (act (c.unitary fun _ => OH) (zeroKet m))
                (fun z => ∀ i, |readFp (oa i) fo z - (-(w i) / inner ℝ w p)| ≤ εg) ≥ 1 - γ := by
  obtain ⟨Cs, hCs, hs⟩ := QuantumLTF.Membership.theorem_3_3_single_run C₁ hC₁
  obtain ⟨Cw, hCw, hmed⟩ := QuantumLTF.Membership.coordinatewise_median_amplification_uniform
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let F : ℝ := Cw * (Cs + 1) / Real.log 2 + Cw * (2 * Cs + (Cs + 1) / Real.log 2)
  refine ⟨F, by positivity, ?_⟩
  intro n hn ε εg γ hε hε2 hεg hεg10 hγ hγ2
  dsimp only
  intro Vb Vf W hVb
  obtain ⟨m, ℓo, fo, c₀, oa, hU₀, hq₀, hg₀, hw₀, hp₀⟩ :=
    hs n hn ε εg hε hε2 hεg hεg10 Vb Vf W hVb
  obtain ⟨m', c, out, hU, hq, hg, hp⟩ :=
    hmed n (n * ⌈Real.logb 2 ((3 * n + 1) /
      (rho n * εg))⌉₊ + Vb + W) m ℓo fo c₀ oa hU₀ γ hγ hγ2
  let S : ℝ := n * (Real.log (n / εg)) ^ 2 + Real.log (1 / ε)
  let L : ℝ := Real.log (1 / γ)
  have hL : Real.log 2 ≤ L := by
    dsimp [L]
    apply Real.log_le_log (by norm_num)
    exact (le_div_iff₀ hγ).2 (by nlinarith)
  have hSlog : Real.log 2 ≤ Real.log (1 / ε) := by
    apply Real.log_le_log (by norm_num)
    exact (le_div_iff₀ hε).2 (by nlinarith)
  have hquad0 : 0 ≤ (n : ℝ) * (Real.log (n / εg)) ^ 2 := by positivity
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact add_nonneg hquad0 (hlog2.le.trans hSlog)
  change (c₀.gateCount : ℝ) ≤ Cs * S at hg₀
  change (n * ℓo : ℝ) ≤ Cs * (S + 1) at hw₀
  change (c.queryCount 0 : ℝ) ≤ Cw * ((c₀.queryCount 0 : ℝ) + 1) * L at hq
  change (c.gateCount : ℝ) ≤ Cw * ((c₀.gateCount + n * ℓo : ℝ) + 1) * L at hg
  have hbase : Cs + 1 ≤ (Cs + 1) / Real.log 2 * S := by
    have hlogS : Real.log 2 ≤ S := by
      exact hSlog.trans (by dsimp [S]; linarith)
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    exact mul_le_mul_of_nonneg_left hlogS (by positivity)
  have hquery : Cw * (Cs + 1) ≤ F := by
    have hlogle : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
      norm_num at this ⊢
      exact this
    have h₁ : Cw * (Cs + 1) ≤ Cw * (Cs + 1) / Real.log 2 := by
      rw [le_div_iff₀ hlog2]
      nlinarith [mul_nonneg hCw.le (by positivity : (0 : ℝ) ≤ Cs + 1)]
    have h₂ : Cw * (Cs + 1) / Real.log 2 ≤ F := by
      dsimp [F]
      have : 0 ≤ Cw * (2 * Cs + (Cs + 1) / Real.log 2) := by positivity
      linarith
    exact h₁.trans h₂
  have hsecond : Cw * (2 * Cs * S + Cs + 1) ≤ F * S := by
    have h₁ : Cw * (2 * Cs * S + Cs + 1) ≤
        (Cw * (2 * Cs + (Cs + 1) / Real.log 2)) * S := by
      calc
        Cw * (2 * Cs * S + Cs + 1) ≤
            Cw * (2 * Cs * S + (Cs + 1) / Real.log 2 * S) := by
          apply mul_le_mul_of_nonneg_left _ hCw.le
          linarith [hbase]
        _ = (Cw * (2 * Cs + (Cs + 1) / Real.log 2)) * S := by ring
    have h₂ : (Cw * (2 * Cs + (Cs + 1) / Real.log 2)) * S ≤ F * S := by
      apply mul_le_mul_of_nonneg_right _ hS0
      dsimp [F]
      have : 0 ≤ Cw * (Cs + 1) / Real.log 2 := by positivity
      linarith
    exact h₁.trans h₂
  refine ⟨m', ℓo, fo, c, out, hU, ?_, ?_, ?_⟩
  · calc
      (c.queryCount 0 : ℝ) ≤ Cw * ((c₀.queryCount 0 : ℝ) + 1) * L := hq
      _ ≤ Cw * (Cs + 1) * L := by gcongr <;> linarith [hL]
      _ ≤ F * L := by gcongr <;> linarith [hL]
      _ = F * Real.log (1 / γ) := rfl
  · calc
      (c.gateCount : ℝ) ≤ Cw * ((c₀.gateCount + n * ℓo : ℝ) + 1) * L := hg
      _ ≤ Cw * (2 * Cs * S + Cs + 1) * L := by
        have hb : (c₀.gateCount + n * ℓo : ℝ) + 1 ≤ 2 * Cs * S + Cs + 1 := by
          have hcs : 0 ≤ Cs * S := mul_nonneg hCs.le hS0
          nlinarith
        gcongr <;> linarith [hL]
      _ ≤ F * S * L := by gcongr <;> linarith [hL]
      _ = F * (n * (Real.log (n / εg)) ^ 2 + Real.log (1 / ε)) *
          Real.log (1 / γ) := rfl
  · intro w p θ hw ha₁ ha₂ Htil hH OH hOH hact
    exact hp OH hOH (fun i => -(w i) / inner ℝ w p) εg (hp₀ w p θ hw ha₁ ha₂ Htil hH OH hOH hact)
