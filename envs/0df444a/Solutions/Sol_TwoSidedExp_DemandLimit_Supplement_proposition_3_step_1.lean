-- Prove2me | solution 1 for TwoSidedExp.DemandLimit.Supplement.proposition_3_step_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:30:15.222896+00:00
-- url     : https://prove2.me/submissions/7e993e22-1d9e-4469-af3c-84ae12a02fc5

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting
import Definitions.Def_TwoSidedExp_DemandLimit_Supplement_Supply

open Filter Topology MeasureTheory

open TwoSidedExp
open TwoSidedExp.DemandLimit
open TwoSidedExp.DemandLimit.Supplement

/-- Proposition 3 Step 1, p. A8, on the closed design square. -/
theorem solution {Γ Θ : Type} [Fintype Γ] [Fintype Θ]
    (M : Model Γ Θ) (hM : M.Standing) (lam tau : ℕ → ℝ) (hlam : ∀ n, 0 < lam n) (htau : ∀ n, 0 < tau n)
    (hratio : Tendsto (fun n => lam n / tau n) atTop atTop)
    (aC aL : ℝ) (haC : 0 ≤ aC ∧ aC ≤ 1) (haL : 0 ≤ aL ∧ aL ≤ 1)
    (s : ℕ → Θ × Fin 2 → ℝ)
    (hs : ∀ n, (M.expt aC aL).IsSteady (lam n) (tau n) (s n)) :
    ∀ p : Θ × Fin 2, Tendsto (fun n => s n p) atTop (𝓝 0) := by
      set S := M.expt aC aL with hSdef
      have hφ : ∀ q, 0 ≤ S.φ q := by
        intro q
        simp only [hSdef, Model.expt]
        split_ifs
        · exact mul_nonneg haC.1 (hM.phi_pos q.1).le
        · exact mul_nonneg (by linarith [haC.2]) (hM.phi_pos q.1).le
      have hα : ∀ q p, 0 < S.α q p := by
        intro q p
        simp only [hSdef, Model.expt]
        split_ifs
        · exact hM.alphat_pos _ _
        · exact hM.alpha_pos _ _
      have hv : ∀ q p, 0 < S.v q p := by
        intro q p
        simp only [hSdef, Model.expt]
        split_ifs
        · exact hM.vt_pos _ _
        · exact hM.v_pos _ _
      have heps : ∀ q, 0 < S.eps q := fun q => hM.eps_pos q.1
      have hν : ∀ p, 0 < S.ν p := fun p => hM.nu_pos p.1
      have hφsum : ∑ q, S.φ q = 1 := by
        rw [Fintype.sum_prod_type]
        simp only [hSdef, Model.expt, Fin.sum_univ_two]
        simp only [show ¬ ((0 : Fin 2) = 1) from by decide, if_false, if_true]
        have : ∀ γ, (1 - aC) * M.sys.φ γ + aC * M.sys.φ γ = M.sys.φ γ := fun γ => by ring
        simp only [this, hM.phi_sum]
      have htl : Tendsto (fun n => tau n / lam n) atTop (𝓝 0) := by
        have := hratio.inv_tendsto_atTop
        refine this.congr (fun n => ?_)
        simp [inv_div]
      intro p
      set D : Γ × Fin 2 → ℝ := fun q => S.eps q + ∑ p', S.α q p' * S.v q p' * S.ρ p' with hD
      have hρ : ∀ p, 0 ≤ S.ρ p := fun p => ((hs 0).1 p).1.trans ((hs 0).1 p).2
      have hDpos : ∀ q, 0 < D q := fun q => by
        have : 0 ≤ ∑ p', S.α q p' * S.v q p' * S.ρ p' :=
          Finset.sum_nonneg fun p' _ => mul_nonneg (mul_pos (hα q p') (hv q p')).le (hρ p')
        simp only [hD]; linarith [heps q]
      set K := ∑ q, S.φ q * (S.α q p * S.v q p / D q) with hK
      have hKpos : 0 < K := by
        have hnn : ∀ q ∈ Finset.univ, 0 ≤ S.φ q * (S.α q p * S.v q p / D q) := fun q _ =>
          mul_nonneg (hφ q) (div_pos (mul_pos (hα q p) (hv q p)) (hDpos q)).le
        rcases (Finset.sum_nonneg hnn).lt_or_eq with h | h
        · exact h
        · exfalso
          have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h.symm
          have : ∀ q ∈ Finset.univ, S.φ q = 0 := fun q hq => by
            have := h0 q hq
            rcases mul_eq_zero.1 this with h1 | h1
            · exact h1
            · exact absurd h1 (div_pos (mul_pos (hα q p) (hv q p)) (hDpos q)).ne'
          rw [Finset.sum_eq_zero this] at hφsum
          exact zero_ne_one hφsum
      have hbound : ∀ n, s n p ≤ (S.ρ p * S.ν p / K) * (tau n / lam n) := by
        intro n
        obtain ⟨hin, heq⟩ := hs n
        have hsnn : ∀ p', 0 ≤ s n p' := fun p' => (hin p').1
        have h1 : s n p * K ≤ ∑ q, S.φ q * S.choice q p (s n) := by
          rw [hK, Finset.mul_sum]
          apply Finset.sum_le_sum
          intro q _
          have hnum : 0 ≤ S.α q p * S.v q p * s n p :=
            mul_nonneg (mul_pos (hα q p) (hv q p)).le (hsnn p)
          have hden : 0 < S.eps q + ∑ θ', S.α q θ' * S.v q θ' * s n θ' := by
            have : 0 ≤ ∑ θ', S.α q θ' * S.v q θ' * s n θ' :=
              Finset.sum_nonneg fun p' _ => mul_nonneg (mul_pos (hα q p') (hv q p')).le (hsnn p')
            linarith [heps q]
          have hle : S.eps q + ∑ θ', S.α q θ' * S.v q θ' * s n θ' ≤ D q := by
            simp only [hD]
            have : ∑ θ', S.α q θ' * S.v q θ' * s n θ' ≤ ∑ p', S.α q p' * S.v q p' * S.ρ p' :=
              Finset.sum_le_sum fun p' _ =>
                mul_le_mul_of_nonneg_left (hin p').2 (mul_pos (hα q p') (hv q p')).le
            linarith
          have := div_le_div_of_nonneg_left hnum hden hle
          calc s n p * (S.φ q * (S.α q p * S.v q p / D q))
              = S.φ q * (S.α q p * S.v q p * s n p / D q) := by ring
            _ ≤ S.φ q * (S.α q p * S.v q p * s n p / (S.eps q + ∑ θ', S.α q θ' * S.v q θ' * s n θ')) :=
              mul_le_mul_of_nonneg_left this (hφ q)
            _ = S.φ q * S.choice q p (s n) := by rfl
        have h2 := heq p
        have h3 : lam n * (s n p * K) ≤ S.ρ p * S.ν p * tau n := by
          have := mul_le_mul_of_nonneg_left h1 (hlam n).le
          have h4 : (S.ρ p - s n p) * (tau n * S.ν p) ≤ S.ρ p * S.ν p * tau n := by
            have := mul_pos (htau n) (hν p)
            nlinarith [hsnn p]
          linarith
        rw [div_mul_div_comm, le_div_iff₀ (mul_pos hKpos (hlam n))]
        nlinarith
      have hup : Tendsto (fun n => (S.ρ p * S.ν p / K) * (tau n / lam n)) atTop (𝓝 0) := by
        simpa using htl.const_mul (S.ρ p * S.ν p / K)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
        (fun n => ((hs n).1 p).1) hbound
