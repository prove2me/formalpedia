-- Prove2me | solution 1 for TwoSidedExp.DemandLimit.Supplement.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:30:36.175924+00:00
-- url     : https://prove2.me/submissions/3def08b9-9977-4e19-8fd1-480b0aebf22f

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting
import Definitions.Def_TwoSidedExp_DemandLimit_Supplement_Supply

open Filter Topology MeasureTheory

open TwoSidedExp
open TwoSidedExp.DemandLimit
open TwoSidedExp.DemandLimit.Supplement

/-- Proposition 3 (23), p. 20, on the closed design square. -/
theorem solution {Γ Θ : Type} [Fintype Γ] [Fintype Θ]
    (M : Model Γ Θ) (hM : M.Standing) (lam tau : ℕ → ℝ) (hlam : ∀ n, 0 < lam n) (htau : ∀ n, 0 < tau n)
    (hratio : Tendsto (fun n => lam n / tau n) atTop atTop)
    (aC aL : ℝ) (haC : 0 ≤ aC ∧ aC ≤ 1) (haL : 0 ≤ aL ∧ aL ≤ 1)
    (s : ℕ → Θ × Fin 2 → ℝ)
    (hs : ∀ n, (M.expt aC aL).IsSteady (lam n) (tau n) (s n)) :
    ∀ i j : Fin 2, Tendsto (fun n => M.Q (lam n) aC aL (s n) i j / tau n) atTop
      (𝓝 (∑ θ, ((∑ γ, (M.expt aC aL).φ (γ, i) * g M (γ, i) (θ, j)) /
        (∑ i' : Fin 2, ∑ γ, (M.expt aC aL).φ (γ, i') * g M (γ, i') (θ, j))) *
          (M.expt aC aL).ρ (θ, j) * M.sys.ν θ)) := by
            classical
            let E := M.expt aC aL
            let A : (Γ × Fin 2) → (Θ × Fin 2) → ℝ := fun q p => E.α q p * E.v q p
            let D : ℕ → (Γ × Fin 2) → ℝ := fun n q => E.eps q + ∑ p, A q p * s n p
            let U : (Γ × Fin 2) → ℝ := fun q => E.eps q + ∑ p, A q p * E.ρ p
            let K : ℕ → (Γ × Fin 2) → (Θ × Fin 2) → ℝ := fun n q p => A q p / D n q
            let B : ℕ → (Θ × Fin 2) → ℝ := fun n p => ∑ q, E.φ q * K n q p
            have hphi : ∀ q, 0 ≤ E.φ q := by
              intro q
              dsimp [E, Model.expt]
              split <;> exact mul_nonneg (by linarith [haC.1, haC.2]) (hM.phi_pos q.1).le
            have hphisum : ∑ q, E.φ q = 1 := by
              dsimp [E, Model.expt]
              rw [Fintype.sum_prod_type]
              simp only [Fin.sum_univ_two, zero_ne_one, ↓reduceIte]
              simp_rw [← add_mul]
              simp [hM.phi_sum]
            obtain ⟨q₀, _, hq₀⟩ := (Finset.sum_pos_iff_of_nonneg (fun q _ => hphi q)).mp
              (show 0 < ∑ q, E.φ q by rw [hphisum]; norm_num)
            have hA : ∀ q p, 0 < A q p := by
              intro q p
              dsimp [A, E, Model.expt]
              split <;> exact mul_pos (by first | exact hM.alphat_pos q.1 p.1 | exact hM.alpha_pos q.1 p.1)
                (by first | exact hM.vt_pos q.1 p.1 | exact hM.v_pos q.1 p.1)
            have heps : ∀ q, 0 < E.eps q := fun q => hM.eps_pos q.1
            have hnu : ∀ p, 0 < E.ν p := fun p => hM.nu_pos p.1
            have hs0 : ∀ n p, 0 ≤ s n p := fun n p => (hs n).1 p |>.1
            have hsρ : ∀ n p, s n p ≤ E.ρ p := fun n p => (hs n).1 p |>.2
            have hρ : ∀ p, 0 ≤ E.ρ p := fun p => (hs0 0 p).trans (hsρ 0 p)
            have hD : ∀ n q, 0 < D n q := by
              intro n q
              exact add_pos_of_pos_of_nonneg (heps q)
                (Finset.sum_nonneg (fun p _ => mul_nonneg (hA q p).le (hs0 n p)))
            have hU : ∀ q, 0 < U q := by
              intro q
              exact add_pos_of_pos_of_nonneg (heps q)
                (Finset.sum_nonneg (fun p _ => mul_nonneg (hA q p).le (hρ p)))
            have hDU : ∀ n q, D n q ≤ U q := by
              intro n q
              exact add_le_add_right (Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left
                (hsρ n p) (hA q p).le)) _
            have hK : ∀ n q p, 0 < K n q p := fun n q p => div_pos (hA q p) (hD n q)
            have hBlo : ∀ n p, E.φ q₀ * (A q₀ p / U q₀) ≤ B n p := by
              intro n p
              calc
                _ ≤ E.φ q₀ * K n q₀ p := mul_le_mul_of_nonneg_left
                  (div_le_div_of_nonneg_left (hA q₀ p).le (hD n q₀) (hDU n q₀)) (hphi q₀)
                _ ≤ _ := Finset.single_le_sum (fun q _ => mul_nonneg (hphi q) (hK n q p).le)
                  (Finset.mem_univ q₀)
            have hB : ∀ n p, 0 < B n p := fun n p => lt_of_lt_of_le
              (mul_pos hq₀ (div_pos (hA q₀ p) (hU q₀))) (hBlo n p)
            have hchoice : ∀ n q p, E.choice q p (s n) = K n q p * s n p := by
              intro n q p
              dsimp [MFSystem.choice, K, D, A]
              ring
            have hbalance : ∀ n p, (E.ρ p - s n p) * (tau n * E.ν p) = lam n * (s n p * B n p) := by
              intro n p
              have hh := (hs n).2 p
              change (E.ρ p - s n p) * (tau n * E.ν p) = _ at hh
              rw [show (∑ q, E.φ q * E.choice q p (s n)) = s n p * B n p by
                simp_rw [hchoice]; dsimp [B]; rw [Finset.mul_sum]; congr 1; funext q; ring] at hh
              exact hh
            have hinv : Tendsto (fun n => tau n / lam n) atTop (𝓝 0) := by
              simpa only [Function.comp_def, inv_div] using tendsto_inv_atTop_zero.comp hratio
            have hs_limit : ∀ p, Tendsto (fun n => s n p) atTop (𝓝 0) := by
              intro p
              let c := E.φ q₀ * (A q₀ p / U q₀)
              have hc : 0 < c := mul_pos hq₀ (div_pos (hA q₀ p) (hU q₀))
              have hbound : ∀ n, s n p ≤ (tau n / lam n) * (E.ρ p * E.ν p / c) := by
                intro n
                have hb := hbalance n p
                have hbc := mul_le_mul_of_nonneg_left (hBlo n p) (hs0 n p)
                have hle : lam n * (s n p * c) ≤ tau n * (E.ρ p * E.ν p) := by
                  calc
                    _ ≤ lam n * (s n p * B n p) := mul_le_mul_of_nonneg_left hbc (hlam n).le
                    _ = (E.ρ p - s n p) * (tau n * E.ν p) := hb.symm
                    _ ≤ E.ρ p * (tau n * E.ν p) := mul_le_mul_of_nonneg_right
                      (sub_le_self _ (hs0 n p)) (mul_pos (htau n) (hnu p)).le
                    _ = _ := by ring
                rw [← mul_div_assoc]
                apply (le_div_iff₀ hc).2
                apply (mul_le_mul_iff_right₀ (hlam n)).mp
                calc
                  _ ≤ tau n * (E.ρ p * E.ν p) := hle
                  _ = _ := by field_simp [ne_of_gt (hlam n)]
              exact squeeze_zero (fun n => hs0 n p) hbound (by simpa using hinv.mul_const (E.ρ p * E.ν p / c))
            have hDlim : ∀ q, Tendsto (fun n => D n q) atTop (𝓝 (E.eps q)) := by
              intro q
              have hh := tendsto_finsetSum Finset.univ (fun p _ => (hs_limit p).const_mul (A q p))
              simpa [D] using tendsto_const_nhds.add hh
            have hKlim : ∀ q p, Tendsto (fun n => K n q p) atTop (𝓝 (g M q p)) := by
              intro q p
              change Tendsto (fun n => A q p / D n q) atTop (𝓝 (A q p / E.eps q))
              exact tendsto_const_nhds.div (hDlim q) (ne_of_gt (heps q))
            let b : (Θ × Fin 2) → ℝ := fun p => ∑ q, E.φ q * g M q p
            have hblim : ∀ p, Tendsto (fun n => B n p) atTop (𝓝 (b p)) := by
              intro p
              exact tendsto_finsetSum Finset.univ (fun q _ => (hKlim q p).const_mul (E.φ q))
            have hg : ∀ q p, 0 < g M q p := by
              intro q p
              change 0 < A q p / E.eps q
              exact div_pos (hA q p) (heps q)
            have hbpos : ∀ p, 0 < b p := by
              intro p
              exact Finset.sum_pos' (fun q _ => mul_nonneg (hphi q) (hg q p).le)
                ⟨q₀, Finset.mem_univ _, mul_pos hq₀ (hg q₀ p)⟩
            let C : ℕ → Fin 2 → (Θ × Fin 2) → ℝ := fun n i p => ∑ γ, E.φ (γ, i) * K n (γ, i) p
            let c : Fin 2 → (Θ × Fin 2) → ℝ := fun i p => ∑ γ, E.φ (γ, i) * g M (γ, i) p
            have hclim : ∀ i p, Tendsto (fun n => C n i p) atTop (𝓝 (c i p)) := by
              intro i p
              exact tendsto_finsetSum Finset.univ (fun γ _ => (hKlim (γ, i) p).const_mul (E.φ (γ, i)))
            have hflow : ∀ n p, lam n / tau n * s n p = (E.ρ p - s n p) * E.ν p / B n p := by
              intro n p
              have hh := hbalance n p
              field_simp [ne_of_gt (htau n), ne_of_gt (hB n p)]
              nlinarith [hh]
            have hQ : ∀ n i j, M.Q (lam n) aC aL (s n) i j / tau n =
                ∑ θ, (C n i (θ, j) / B n (θ, j)) * (E.ρ (θ, j) - s n (θ, j)) * E.ν (θ, j) := by
              intro n i j
              unfold Model.Q
              change lam n * (∑ θ, ∑ γ, E.φ (γ, i) * E.choice (γ, i) (θ, j) (s n)) / tau n = _
              simp_rw [hchoice]
              rw [mul_div_assoc, Finset.sum_div, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro θ _
              have hc : (∑ γ, E.φ (γ, i) * (K n (γ, i) (θ, j) * s n (θ, j))) =
                  C n i (θ, j) * s n (θ, j) := by
                dsimp [C]
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro γ _
                ring
              rw [hc]
              calc
                _ = C n i (θ, j) * (lam n / tau n * s n (θ, j)) := by ring
                _ = _ := by rw [hflow]; ring
            have hbform : ∀ p, b p = ∑ i : Fin 2, ∑ γ, E.φ (γ, i) * g M (γ, i) p := by
              intro p
              dsimp [b]
              rw [Fintype.sum_prod_type, Finset.sum_comm]
            intro i j
            have hlim : Tendsto (fun n => ∑ θ, (C n i (θ, j) / B n (θ, j)) *
                (E.ρ (θ, j) - s n (θ, j)) * E.ν (θ, j)) atTop
                (𝓝 (∑ θ, (c i (θ, j) / b (θ, j)) * E.ρ (θ, j) * E.ν (θ, j))) := by
              apply tendsto_finsetSum
              intro θ _
              have hh := ((hclim i (θ, j)).div (hblim (θ, j)) (ne_of_gt (hbpos (θ, j)))).mul
                ((tendsto_const_nhds (x := E.ρ (θ, j))).sub (hs_limit (θ, j)))
              simpa using hh.mul_const (E.ν (θ, j))
            simp_rw [hQ]
            simpa only [hbform, c, E, Model.expt] using hlim
