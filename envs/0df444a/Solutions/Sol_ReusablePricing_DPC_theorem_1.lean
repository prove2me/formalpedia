-- Prove2me | solution 1 for ReusablePricing.DPC.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T03:44:43.335459+00:00
-- url     : https://prove2.me/submissions/d8810224-be2a-42ad-b5a2-827180269305

import Mathlib
import Definitions.Def_ReusablePricing_DPC_Model
import Definitions.Def_ReusablePricing_DPC_Control
import Theorems.Thm_ReusablePricing_DPC_step2_bound

open Finset ReusablePricing.DPC

/-- Under the standing hypotheses, `min{φ_L, φ_U} < 1/2`: some type has a positive DET rate in
`(0, λ_U)` and A5 then forces `φ_L + φ_U < λ_U ≤ 1`. -/
lemma dpc_phi_small (P : Basic) (φL φU Ψ R : ℝ) (nl : ℕ)
    (hP : P.Standing φL φU Ψ R nl) : φL + φU < 1 := by
  obtain ⟨hMF, -, hW, -, hA5, hNb, -⟩ := hP
  obtain ⟨-, -, hn1, hT1, hdvd, -, -, -, -, hlamU1, -⟩ := hMF
  obtain ⟨-, -, -, hA5t⟩ := hA5
  obtain ⟨-, j, t, ht, hcnt, -⟩ := hNb
  rw [Finset.mem_Icc] at ht
  have hnT : P.n ≤ P.T := Nat.le_of_dvd (by omega) hdvd
  unfold Basic.cnt at hcnt
  obtain ⟨s, hs⟩ := Finset.card_pos.mp hcnt
  rw [Finset.mem_filter, Finset.mem_Icc] at hs
  have hsT : s ∈ Icc 1 P.T := by rw [Finset.mem_Icc]; omega
  rcases hW s hsT j with h0 | ⟨hpos, hlt⟩
  · linarith [hs.2]
  · obtain ⟨h1, h2⟩ := (hA5t s hsT).1 j hpos hlt
    linarith

/-- The choice `γ = δ / (2m)` in the exponent of Step 2. -/
lemma dpc_exp_choice (m nl ε : ℝ) (hm1 : 1 ≤ m) (hnlpos : 0 < nl) (hε1 : 1 < ε)
    (hε6 : ε ≤ 6 * m + 1) (hεnl' : ε < nl / 2) :
    0 < ((nl - 1) * (ε - 1) / (3 * nl)) / (2 * m) ∧
    ((nl - 1) * (ε - 1) / (3 * nl)) / (2 * m) ≤ 1 ∧
    Real.exp (m * (((nl - 1) * (ε - 1) / (3 * nl)) / (2 * m)) ^ 2 -
      ((nl - 1) * (ε - 1) / (3 * nl)) * (((nl - 1) * (ε - 1) / (3 * nl)) / (2 * m))) ≤
      2 * Real.exp (-(ε - 1) ^ 2 / (36 * m)) := by
  set δ : ℝ := (nl - 1) * (ε - 1) / (3 * nl) with hδ
  set γ : ℝ := δ / (2 * m) with hγ
  have hnl2 : (2 : ℝ) < nl := by linarith
  have hδpos : 0 < δ := by
    rw [hδ]; apply div_pos
    · apply mul_pos <;> linarith
    · linarith
  have hδle : δ ≤ (ε - 1) / 3 := by
    rw [hδ, div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have hγ0 : 0 < γ := by rw [hγ]; apply div_pos hδpos; linarith
  have hγ1 : γ ≤ 1 := by
    rw [hγ, div_le_one (by linarith)]; linarith
  refine ⟨hγ0, hγ1, ?_⟩
  have hmpos : 0 < m := by linarith
  have hexp_eq : m * γ ^ 2 - δ * γ = -(δ ^ 2) / (4 * m) := by
    rw [hγ]; field_simp; ring
  have h9 : 9 * δ ^ 2 * nl ^ 2 = (nl - 1) ^ 2 * (ε - 1) ^ 2 := by
    rw [hδ]; field_simp; ring
  have hw0 : 0 ≤ ε - 1 := by linarith
  have hw6 : ε - 1 ≤ 6 * m := by linarith
  have hdiff : (ε - 1) ^ 2 - 9 * δ ^ 2 ≤ 6 * m := by
    have hnl2' : (0 : ℝ) < nl ^ 2 := by positivity
    have e1 : ((ε - 1) ^ 2 - 9 * δ ^ 2) * nl ^ 2 = (ε - 1) ^ 2 * (2 * nl - 1) := by
      have : ((ε - 1) ^ 2 - 9 * δ ^ 2) * nl ^ 2
          = (ε - 1) ^ 2 * nl ^ 2 - 9 * δ ^ 2 * nl ^ 2 := by ring
      rw [this, h9]; ring
    have e2 : (ε - 1) ^ 2 * (2 * nl - 1) ≤ 2 * nl * (ε - 1) ^ 2 := by
      nlinarith [sq_nonneg (ε - 1)]
    have e3 : (ε - 1) ^ 2 ≤ 6 * m * (ε - 1) := by nlinarith
    have e4 : 2 * nl * (ε - 1) ^ 2 ≤ 12 * m * nl * (ε - 1) := by nlinarith
    have e5 : 12 * m * nl * (ε - 1) ≤ 6 * m * nl ^ 2 := by
      have : (ε - 1) ≤ nl / 2 := by linarith
      have h12 : 0 ≤ 12 * m * nl := by positivity
      have hh := mul_le_mul_of_nonneg_left this h12
      have heq : 12 * m * nl * (nl / 2) = 6 * m * nl ^ 2 := by ring
      linarith
    have : ((ε - 1) ^ 2 - 9 * δ ^ 2) * nl ^ 2 ≤ 6 * m * nl ^ 2 := by
      rw [e1]; linarith
    by_contra hc
    push Not at hc
    have := mul_lt_mul_of_pos_right hc hnl2'
    linarith
  have hexp_le : m * γ ^ 2 - δ * γ ≤ -(ε - 1) ^ 2 / (36 * m) + 1 / 6 := by
    rw [hexp_eq]
    have : -(δ ^ 2) / (4 * m) - (-(ε - 1) ^ 2 / (36 * m)) =
        ((ε - 1) ^ 2 - 9 * δ ^ 2) / (36 * m) := by
      field_simp; ring
    have h2 : ((ε - 1) ^ 2 - 9 * δ ^ 2) / (36 * m) ≤ 1 / 6 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  set X := Real.exp (-(ε - 1) ^ 2 / (36 * m)) with hX
  have hXpos : 0 < X := Real.exp_pos _
  calc Real.exp (m * γ ^ 2 - δ * γ) ≤ Real.exp (-(ε - 1) ^ 2 / (36 * m) + 1 / 6) :=
        Real.exp_le_exp.mpr hexp_le
    _ = X * Real.exp (1 / 6) := by rw [Real.exp_add]
    _ ≤ X * 2 := by
        apply mul_le_mul_of_nonneg_left _ hXpos.le
        have := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 6) (by norm_num) (by norm_num)
        linarith
    _ = 2 * X := by ring

/-- Combining the two terms of Step 2 into the form of display (3). -/
lemma dpc_combine (Ψ R J a TN E X L : ℝ) (hJ0 : 0 ≤ J) (ha : 0 ≤ a) (hTN : 0 ≤ TN)
    (hX : 0 ≤ X) (hE0 : 0 ≤ E) (hE : E ≤ 2 * X)
    (hL : L ≤ Ψ * J * a + 4 * R * J * TN * E) :
    L ≤ (|Ψ| * J + 8 * |R| * J + 1) * (a + TN * X) := by
  have t1 : Ψ * J * a ≤ (|Ψ| * J + 8 * |R| * J + 1) * a := by
    apply mul_le_mul_of_nonneg_right _ ha
    have := mul_le_mul_of_nonneg_right (le_abs_self Ψ) hJ0
    have : 0 ≤ 8 * |R| * J := by positivity
    linarith
  have a2 : 4 * R * J * TN * E ≤ 4 * |R| * J * (TN * E) := by
    have h1 : 4 * R * J * TN * E = (4 * R * J) * (TN * E) := by ring
    rw [h1]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have := mul_le_mul_of_nonneg_right (le_abs_self R) hJ0
    linarith
  have a3 : 4 * |R| * J * (TN * E) ≤ 4 * |R| * J * (TN * (2 * X)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left hE hTN
  have hk : 0 ≤ (|Ψ| * J + 1) * (TN * X) := by positivity
  have e : (|Ψ| * J + 8 * |R| * J + 1) * (a + TN * X)
      = (|Ψ| * J + 8 * |R| * J + 1) * a + 4 * |R| * J * (TN * (2 * X))
        + (|Ψ| * J + 1) * (TN * X) := by ring
  linarith

theorem solution :
    ∀ (J : ℕ) (Ψ R : ℝ), ∃ M₁ : ℝ, 0 < M₁ ∧
      ∀ (P : Basic) (φL φU : ℝ) (nl : ℕ) (ε : ℝ),
        P.J = J → P.Standing φL φU Ψ R nl →
        1 < ε → ε ≤ min (min φL φU * nl) (6 * P.minCapN + 1) →
        P.loss ε nl ≤
          M₁ * (ε / nl + ((P.T : ℝ) / P.n) *
            Real.exp (-(ε - 1) ^ 2 / (36 * P.minCapN))) := by
  intro J Ψ R
  refine ⟨|Ψ| * J + 8 * |R| * J + 1, by positivity, ?_⟩
  intro P φL φU nl ε hJ hP hε1 hε
  have hphi := dpc_phi_small P φL φU Ψ R nl hP
  obtain ⟨hMF, -, -, -, hA5, -, -⟩ := id hP
  obtain ⟨hI1, -, hn1, hT1, -, -, -, hC1, -, -, -⟩ := id hMF
  obtain ⟨hφL, hφU, -, -⟩ := hA5
  have hε' : ε ≤ min φL φU * nl := le_trans hε (min_le_left _ _)
  have hε6 : ε ≤ 6 * P.minCapN + 1 := le_trans hε (min_le_right _ _)
  have hm1 : (1 : ℝ) ≤ P.minCapN := by
    unfold Basic.minCapN
    apply le_min
    · have i0 : Fin P.I := ⟨0, by omega⟩
      have : P.C i0 ≤ Finset.univ.sup P.C := Finset.le_sup (Finset.mem_univ _)
      have := hC1 i0
      exact_mod_cast (by omega : 1 ≤ Finset.univ.sup P.C)
    · exact_mod_cast hn1
  have hmin : min φL φU < 1 / 2 := by
    rcases le_total φL φU with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  have hminpos : 0 < min φL φU := lt_min hφL hφU
  have hnlpos : (0 : ℝ) < nl := by
    by_contra hc
    push Not at hc
    have : min φL φU * nl ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hminpos.le hc
    linarith
  have hεnl' : ε < (nl : ℝ) / 2 := by nlinarith
  obtain ⟨hγ0, hγ1, hE⟩ := dpc_exp_choice P.minCapN nl ε hm1 hnlpos hε1 hε6 hεnl'
  have key := step2_bound P φL φU Ψ R nl ε _ hP hε1 hε' rfl _ hγ0 hγ1
  have hTpos : (0 : ℝ) < P.T := by exact_mod_cast hT1
  have hloss : P.loss ε nl ≤ Ψ * P.J * ε / nl + 4 * R * P.J * P.T / P.n *
      Real.exp (P.minCapN * (((nl - 1) * (ε - 1) / (3 * nl)) / (2 * P.minCapN)) ^ 2 -
        ((nl - 1) * (ε - 1) / (3 * nl)) * (((nl - 1) * (ε - 1) / (3 * nl)) / (2 * P.minCapN))) := by
    unfold Basic.loss
    rw [div_le_iff₀ hTpos, mul_comm]; exact key
  rw [hJ] at hloss
  refine dpc_combine Ψ R J (ε / nl) ((P.T : ℝ) / P.n) _ _ _ (by positivity) (by positivity)
    (by positivity) (Real.exp_pos _).le (Real.exp_pos _).le hE ?_
  rw [mul_div_assoc] at hloss
  convert hloss using 2
  ring
