-- Prove2me | solution 1 for StableCount.proposition_9_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:34:06.749201+00:00
-- url     : https://prove2.me/submissions/67304456-f06d-4acb-b476-acc65324084c

import Mathlib
import Theorems.Thm_StableCount_theorem_2
import Definitions.Def_StableCount_FiniteProblem

section
namespace StableCount

open StableMatching

namespace Dev.JLe

variable {n : ℕ}

theorem J_zero (Q : Member n) (hR : Q.R = 0) : Q.J = 1 := by
  haveI : IsEmpty (Fin Q.R) := ⟨fun i => by have := i.2; omega⟩
  unfold Member.J Member.Jon
  rw [Finset.univ_eq_empty]
  simp [Member.IsDownsetIn]

/-- every member satisfies `J ≤ e^F`, from the branching property of `F_h` (Theorem 2) -/
theorem J_le_exp (h : ℕ → ℝ) (hh : IsAdmissible h) :
    ∀ (k : ℕ) (Q : Member n), Q.R = k → (Q.J : ℝ) ≤ Real.exp (Q.Fh h) := by
  have hb := theorem_2 (n := n) h hh
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro Q hQ
    by_cases hR : Q.R = 0
    · have hF : Q.Fh h = 0 := hb.2.2.1 Q hR
      rw [J_zero Q hR, hF]
      simp
    · obtain ⟨a₁, a₂, h1, h2, hJ, hF⟩ := hb.2.2.2 Q hR
      have i1 := ih a₁.R (by simp only at h1; omega) a₁ rfl
      have i2 := ih a₂.R (by simp only at h2; omega) a₂ rfl
      have hJ' : (Q.J : ℝ) = (a₁.J : ℝ) + (a₂.J : ℝ) := by
        have : Q.J = a₁.J + a₂.J := hJ
        exact_mod_cast this
      rw [hJ']
      exact (add_le_add i1 i2).trans hF

end Dev.JLe

end StableCount
end

section
namespace StableCount

namespace Dev.P92

open Real

theorem one_sub_exp_pos {t : ℝ} (ht : 0 < t) : 0 < 1 - Real.exp (-t) := by
  have : Real.exp (-t) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  linarith

theorem lam_anti {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : lam b ≤ lam a := by
  unfold lam
  have h1 := one_sub_exp_pos ha
  have h2 : 1 - Real.exp (-a) ≤ 1 - Real.exp (-b) := by
    have : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have := Real.log_le_log h1 h2
  linarith

theorem lam_sub_le {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) :
    lam y - lam x ≤ Real.log (x / y) := by
  have hx : 0 < x := lt_of_lt_of_le hy hyx
  have hu := one_sub_exp_pos hx
  have hv := one_sub_exp_pos hy
  -- concavity of `1 - e^{-t}`
  have key : y * (1 - Real.exp (-x)) ≤ x * (1 - Real.exp (-y)) := by
    have hc : Real.exp ((1 - y / x) • (0 : ℝ) + (y / x) • (-x)) ≤
        (1 - y / x) • Real.exp 0 + (y / x) • Real.exp (-x) :=
      convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _)
        (by rw [sub_nonneg, div_le_one hx]; exact hyx) (by positivity) (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
    have e : y / x * -x = -y := by field_simp
    rw [e] at hc
    have h3 : (1 - y / x) + y / x * Real.exp (-x) ≥ Real.exp (-y) := hc
    have h4 : x * ((1 - y / x) + y / x * Real.exp (-x)) = x - y + y * Real.exp (-x) := by
      field_simp
    nlinarith [mul_le_mul_of_nonneg_left h3 hx.le]
  unfold lam
  have : -Real.log (1 - Real.exp (-y)) - -Real.log (1 - Real.exp (-x)) =
      Real.log ((1 - Real.exp (-x)) / (1 - Real.exp (-y))) := by
    rw [Real.log_div hu.ne' hv.ne']; ring
  rw [this]
  apply Real.log_le_log (div_pos hu hv)
  rw [div_le_div_iff₀ hv hy]
  linarith

variable {N M : ℕ} {hs : ℕ → ℝ} {C : ℝ}

theorem ext_gt {d : ℕ} (hd : N < d) :
    extend hs C N d = C / ((d : ℝ) * ((d : ℝ) - 1)) := by
  simp [extend, not_le.mpr hd]

theorem Hsum_succ (h : ℕ → ℝ) (d : ℕ) :
    Hsum h (d + 1) = Hsum h d + ((d : ℝ) + 2) * h (d + 1) := by
  unfold Hsum
  rw [Finset.sum_Icc_succ_top (by omega)]
  push_cast
  ring

theorem C_pos (hN : 3 ≤ N) (hC : 2 + 4 / ((N : ℝ) * ((N : ℝ) + 3)) ≤ C) : 2 < C := by
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have : 0 < 4 / ((N : ℝ) * ((N : ℝ) + 3)) := by positivity
  linarith

theorem step_bound (hN : 3 ≤ N) (hC : 2 + 4 / ((N : ℝ) * ((N : ℝ) + 3)) ≤ C) {c : ℕ}
    (hc : N + 1 ≤ c) :
    Real.log (extend hs C N c / extend hs C N (c + 1)) ≤ ((c : ℝ) + 2) * extend hs C N (c + 1) := by
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hD : (N : ℝ) + 1 ≤ c := by exact_mod_cast hc
  have hC2 := C_pos hN hC
  rw [ext_gt (by omega), ext_gt (by omega)]
  push_cast
  simp only [add_sub_cancel_right]
  set D : ℝ := (c : ℝ) with hDdef
  have hD1 : 0 < D - 1 := by linarith
  have hD0 : 0 < D := by linarith
  have hDne : D ≠ 0 := hD0.ne'
  have hD1ne : D - 1 ≠ 0 := hD1.ne'
  have hD2ne : D + 1 ≠ 0 := by positivity
  have hCne : C ≠ 0 := by linarith
  have e1 : C / (D * (D - 1)) / (C / ((D + 1) * D)) = (D + 1) / (D - 1) := by
    field_simp
  rw [e1]
  have e2 : ((D + 2) * (C / ((D + 1) * D))) = C * (D + 2) / (D * (D + 1)) := by
    field_simp
  rw [e2]
  calc Real.log ((D + 1) / (D - 1)) ≤ (D + 1) / (D - 1) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
    _ = 2 / (D - 1) := by field_simp; ring
    _ ≤ C * (D + 2) / (D * (D + 1)) := by
      rw [div_le_div_iff₀ hD1 (by positivity)]
      have hP : (N : ℝ) * ((N : ℝ) + 3) > 0 := by positivity
      have hCP : (C - 2) * ((N : ℝ) * ((N : ℝ) + 3)) ≥ 4 := by
        have h1 : 4 / ((N : ℝ) * ((N : ℝ) + 3)) ≤ C - 2 := by linarith
        rw [div_le_iff₀ hP] at h1
        linarith
      have hE : (N : ℝ) * ((N : ℝ) + 3) ≤ (D - 1) * (D + 2) := by nlinarith
      have := mul_le_mul_of_nonneg_left hE (by linarith : (0 : ℝ) ≤ C - 2)
      nlinarith

theorem admissible_of_feasible (hN : 3 ≤ N) (hM : N + 2 ≤ M) (hP : IsFeasibleP N M hs C) :
    IsAdmissible (extend hs C N) := by
  have hP' := hP
  dsimp only [IsFeasibleP] at hP'
  obtain ⟨F1, F2, F3, F4, F5, F6, F7, F8, F9⟩ := hP'
  have hC2 := C_pos hN F3
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  -- positivity and monotonicity
  have hNpos : 0 < extend hs C N N := by
    refine lt_of_lt_of_le ?_ F2
    positivity
  have hprefix : ∀ k d : ℕ, 1 ≤ d → d + k ≤ N →
      extend hs C N (d + k) ≤ extend hs C N d := by
    intro k
    induction k with
    | zero => intro d _ _; simp
    | succ k ih =>
      intro d hd hdk
      have := F1 (d + k) (by omega) (by omega)
      have h2 := ih d hd (by omega)
      rw [← add_assoc]
      exact this.trans h2
  have hpos : ∀ d, 1 ≤ d → 0 < extend hs C N d := by
    intro d hd
    by_cases hdN : d ≤ N
    · have := hprefix (N - d) d hd (by omega)
      rw [show d + (N - d) = N by omega] at this
      exact lt_of_lt_of_le hNpos this
    · rw [ext_gt (by omega)]
      have : (4 : ℝ) ≤ d := by exact_mod_cast (by omega : 4 ≤ d)
      have h1 : 0 < (d : ℝ) - 1 := by linarith
      positivity
  have hmono : ∀ d, 1 ≤ d → extend hs C N (d + 1) ≤ extend hs C N d := by
    intro d hd
    rcases lt_trichotomy d N with h1 | h1 | h1
    · exact F1 d hd h1
    · subst h1
      rw [ext_gt (by omega)]
      refine le_trans (le_of_eq ?_) F2
      push_cast
      congr 1
      ring
    · rw [ext_gt (by omega), ext_gt (by omega)]
      have : (4 : ℝ) ≤ d := by exact_mod_cast (by omega : 4 ≤ d)
      have h2 : 0 < (d : ℝ) - 1 := by linarith
      push_cast
      apply div_le_div_of_nonneg_left (by linarith) (by positivity)
      nlinarith
  -- the tail increments
  have hstep : ∀ c, N + 1 ≤ c →
      Real.log (extend hs C N c / extend hs C N (c + 1)) ≤
        ((c : ℝ) + 2) * extend hs C N (c + 1) := fun c hc => step_bound hN F3 hc
  -- `σ_d = H_d - λ(2 h_d)` is nondecreasing from `N + 1` on
  have hsig : ∀ c, N + 1 ≤ c →
      Hsum (extend hs C N) c - lam (2 * extend hs C N c) ≤
        Hsum (extend hs C N) (c + 1) - lam (2 * extend hs C N (c + 1)) := by
    intro c hc
    have hp1 := hpos (c + 1) (by omega)
    have hp0 := hpos c (by omega)
    have hm := hmono c (by omega)
    have h1 := lam_sub_le (x := 2 * extend hs C N c) (y := 2 * extend hs C N (c + 1))
      (by linarith) (by linarith)
    rw [mul_div_mul_left _ _ (two_ne_zero)] at h1
    have h2 := hstep c hc
    rw [Hsum_succ]
    linarith
  have hsig' : ∀ a b, N + 1 ≤ a → a ≤ b →
      Hsum (extend hs C N) a - lam (2 * extend hs C N a) ≤
        Hsum (extend hs C N) b - lam (2 * extend hs C N b) := by
    intro a b ha hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hab ih => exact ih.trans (hsig b (by omega))
  -- (H2)
  have hH2 : CondH2 (extend hs C N) := by
    intro d hd
    by_cases hdN : d ≤ N + 1
    · exact F7 d hd hdN
    · have h1 := hsig' (N + 1) d le_rfl (by omega)
      have h2 := F7 (N + 1) (by omega) le_rfl
      linarith
  -- (H3)
  have hAstep : ∀ c, N + 1 ≤ c →
      Aval (extend hs C N) (c + 1) - Aval (extend hs C N) c =
        ((c : ℝ) + 2) * extend hs C N (c + 1) := by
    intro c hc
    unfold Aval
    rw [if_neg (by omega), if_neg (by omega), Hsum_succ]
    ring
  have hf_step : ∀ t : ℝ, 0 ≤ t → ∀ c, N + 1 ≤ c →
      lam (t + extend hs C N (c + 1)) - Aval (extend hs C N) (c + 1) ≤
        lam (t + extend hs C N c) - Aval (extend hs C N) c := by
    intro t ht c hc
    have hp1 := hpos (c + 1) (by omega)
    have hp0 := hpos c (by omega)
    have hm := hmono c (by omega)
    have h1 := lam_sub_le (x := t + extend hs C N c) (y := t + extend hs C N (c + 1))
      (by linarith) (by linarith)
    have h2 : Real.log ((t + extend hs C N c) / (t + extend hs C N (c + 1))) ≤
        Real.log (extend hs C N c / extend hs C N (c + 1)) := by
      apply Real.log_le_log (by positivity)
      rw [div_le_div_iff₀ (by positivity) hp1]
      nlinarith
    have h3 := hstep c hc
    have h4 := hAstep c hc
    linarith
  have hf_all : ∀ t : ℝ, 0 ≤ t → ∀ c, N + 1 ≤ c →
      lam (t + extend hs C N c) - Aval (extend hs C N) c ≤
        lam (t + extend hs C N (N + 1)) - Aval (extend hs C N) (N + 1) := by
    intro t ht c hc
    induction c, hc using Nat.le_induction with
    | base => exact le_rfl
    | succ c hc' ih => exact (hf_step t ht c hc').trans ih
  have hf_reduce : ∀ t : ℝ, 0 ≤ t → ∀ c, 1 ≤ c → ∃ c', 1 ≤ c' ∧ c' ≤ N + 1 ∧
      lam (t + extend hs C N c) - Aval (extend hs C N) c ≤
        lam (t + extend hs C N c') - Aval (extend hs C N) c' := by
    intro t ht c hc
    by_cases hcN : c ≤ N + 1
    · exact ⟨c, hc, hcN, le_rfl⟩
    · exact ⟨N + 1, by omega, le_rfl, hf_all t ht c (by omega)⟩
  have hH3 : CondH3 (extend hs C N) := by
    intro a c ha hc
    have ht : 0 ≤ extend hs C N (a - 1) + 2 * extend hs C N a := by
      have := hpos (a - 1) (by omega)
      have := hpos a (by omega)
      linarith
    by_cases haM : a < M
    · obtain ⟨c', hc1, hc2, hle⟩ := hf_reduce _ ht c hc
      have := F8 a c' ha haM hc1 hc2
      linarith
    · have hM' : M ≤ a := by omega
      have hpc := hpos c hc
      have h1 : lam (extend hs C N (a - 1) + 2 * extend hs C N a + extend hs C N c) ≤
          lam (extend hs C N c) := lam_anti hpc (by linarith)
      obtain ⟨c', hc1, hc2, hle⟩ := hf_reduce 0 le_rfl c hc
      simp only [zero_add] at hle
      have h2 := F9 c' hc1 hc2
      have h3 := hsig' M a (by omega) hM'
      linarith
  exact ⟨hpos, hmono, F4, hH2, hH3, F5, F6⟩

end Dev.P92

end StableCount
end

section
namespace StableCount

open StableMatching

namespace Dev.P92b

open Filter Topology

theorem sum_Icc_eq_range (g : ℕ → ℝ) (m : ℕ) :
    ∑ d ∈ Finset.Icc 1 m, g d = ∑ i ∈ Finset.range m, g (i + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

variable {N : ℕ} {hs : ℕ → ℝ} {C : ℝ}

theorem tail_hasSum (hN : 3 ≤ N) (hC : 2 < C) :
    HasSum (fun k : ℕ => extend hs C N (k + N + 1)) (C / N) := by
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hform : ∀ k : ℕ, extend hs C N (k + N + 1) =
      C / ((k : ℝ) + N) - C / ((k : ℝ) + 1 + N) := by
    intro k
    rw [Dev.P92.ext_gt (by omega)]
    push_cast
    rw [show ((k : ℝ) + N + 1 - 1) = (k : ℝ) + N by ring,
      show ((k : ℝ) + 1 + N) = (k : ℝ) + N + 1 by ring]
    have h1 : (k : ℝ) + N ≠ 0 := by positivity
    have h2 : (k : ℝ) + N + 1 ≠ 0 := by positivity
    field_simp
    ring
  simp_rw [hform]
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · have hsum : ∀ m : ℕ, ∑ i ∈ Finset.range m, (C / ((i : ℝ) + N) - C / ((i : ℝ) + 1 + N)) =
        C / N - C / ((m : ℝ) + N) := by
      intro m
      have := Finset.sum_range_sub' (fun i : ℕ => C / ((i : ℝ) + N)) m
      simpa [add_assoc, add_comm, add_left_comm] using this
    simp_rw [hsum]
    have hlim : Tendsto (fun m : ℕ => C / ((m : ℝ) + N)) atTop (𝓝 0) := by
      apply Tendsto.div_atTop tendsto_const_nhds
      exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simpa using (tendsto_const_nhds (x := C / N)).sub hlim
  · intro k
    rw [← hform]
    rw [Dev.P92.ext_gt (by omega)]
    have : (0 : ℝ) < (k : ℝ) + N := by positivity
    have h3 : (1 : ℝ) < (↑(k + N + 1) : ℝ) - 0 := by push_cast; linarith
    have : (0 : ℝ) < (↑(k + N + 1) : ℝ) - 1 := by push_cast; linarith
    positivity

theorem W_le_tsum (h : ℕ → ℝ) (hh : IsAdmissible h) (hsum : Summable (fun d => h (d + 1))) (d : ℕ) :
    W h d ≤ ∑' d, h (d + 1) := by
  unfold W
  rw [sum_Icc_eq_range]
  exact hsum.sum_le_tsum _ (fun i _ => (hh.1 (i + 1) (by omega)).le)

end Dev.P92b

theorem chk_proposition_9_2 (N M : ℕ) (hN : 3 ≤ N) (hM : N + 2 ≤ M) (hs : ℕ → ℝ) (C : ℝ)
    (hP : IsFeasibleP N M hs C) :
    IsAdmissible (extend hs C N) ∧ Summable (fun d => extend hs C N (d + 1)) ∧
    ∑' d, extend hs C N (d + 1) = ∑ d ∈ Finset.Icc 1 N, extend hs C N d + C / (N : ℝ) ∧
    ∀ (n : ℕ) (Q : Member n),
      (Q.J : ℝ) ≤ Real.exp (Q.Fh (extend hs C N)) ∧
      Real.exp (Q.Fh (extend hs C N)) ≤ Real.exp ((n : ℝ) * ∑' d, extend hs C N (d + 1)) := by
  have hadm := Dev.P92.admissible_of_feasible hN hM hP
  have hP' := hP
  dsimp only [IsFeasibleP] at hP'
  have hC2 := Dev.P92.C_pos hN hP'.2.2.1
  have htail := Dev.P92b.tail_hasSum (hs := hs) hN hC2
  have hsumm : Summable (fun d => extend hs C N (d + 1)) := by
    rw [← summable_nat_add_iff N]
    have := htail.summable
    refine this.congr fun k => ?_
    simp only
  have htsum : ∑' d, extend hs C N (d + 1) =
      ∑ d ∈ Finset.Icc 1 N, extend hs C N d + C / (N : ℝ) := by
    rw [← Summable.sum_add_tsum_nat_add N hsumm, Dev.P92b.sum_Icc_eq_range]
    congr 1
    rw [← htail.tsum_eq]
  refine ⟨hadm, hsumm, htsum, fun n Q => ⟨Dev.JLe.J_le_exp _ hadm _ Q rfl, ?_⟩⟩
  apply Real.exp_le_exp.mpr
  unfold Member.Fh
  have hW : ∀ d, W (extend hs C N) d ≤ ∑' d, extend hs C N (d + 1) :=
    Dev.P92b.W_le_tsum _ hadm hsumm
  calc (1 / 2 : ℝ) * ∑ v : Fin n, (W (extend hs C N) (Q.dL .man v) +
        W (extend hs C N) (Q.dL .woman v))
      ≤ (1 / 2 : ℝ) * ∑ v : Fin n, ((∑' d, extend hs C N (d + 1)) +
        ∑' d, extend hs C N (d + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum fun v _ => add_le_add (hW _) (hW _)
    _ = (n : ℝ) * ∑' d, extend hs C N (d + 1) := by
        simp
        ring

end StableCount
end

theorem solution : type_of% @StableCount.chk_proposition_9_2 := @StableCount.chk_proposition_9_2
