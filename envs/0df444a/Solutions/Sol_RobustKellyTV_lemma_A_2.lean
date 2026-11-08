-- Prove2me | solution 1 for RobustKellyTV.lemma_A_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T01:51:08.797989+00:00
-- url     : https://prove2.me/submissions/1eac364a-1bae-42fe-ad9a-a59f327ce3f9

import Mathlib
import Definitions.Def_RobustKellyTV_Mck

namespace RobustKellyTV.Aux_RK

open RobustKellyTV

theorem prod_le_each {d : ℕ} (U : Fin d → ℝ) (h0 : ∀ i, 0 < U i) (h1 : ∀ i, U i ≤ 1) (i : Fin d) :
    ∏ j, U j ≤ U i := by
  rw [← Finset.mul_prod_erase Finset.univ U (Finset.mem_univ i)]
  have : ∏ j ∈ Finset.univ.erase i, U j ≤ 1 :=
    Finset.prod_le_one (fun j _ => (h0 j).le) (fun j _ => h1 j)
  nlinarith [h0 i]

end RobustKellyTV.Aux_RK

open RobustKellyTV RobustKellyTV.Aux_RK in
theorem solution {d : ℕ} (P pc : Fin d → ℝ) (hpc : ∀ i, 0 < pc i) :
    ∃ C : ℝ, ∀ σ : Setting d, σ.P = P → ∀ (T : ℕ) (N : Fin d → ℕ), ∑ i, N i = T →
      ∀ i, |Real.log (oracleE σ (smoothed pc N T) i)| ≤ C + Real.log ((T : ℝ) + 1) := by
  classical
  set S := ∑ j, pc j with hS
  refine ⟨Real.log 2 + ∑ j, |Real.log (pc j)| + Real.log (1 + S) + ∑ j, |Real.log (P j)|, ?_⟩
  intro σ hσP T N hN i
  subst hσP
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => (hpc j).le
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogS : 0 ≤ Real.log (1 + S) := Real.log_nonneg (by linarith)
  have hsumpc : ∀ j, -Real.log (pc j) ≤ ∑ j, |Real.log (pc j)| := fun j =>
    (neg_le_abs _).trans (Finset.single_le_sum (f := fun j => |Real.log (pc j)|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ j))
  have hsumP : ∀ j, -Real.log (σ.P j) ≤ ∑ j, |Real.log (σ.P j)| := fun j =>
    (neg_le_abs _).trans (Finset.single_le_sum (f := fun j => |Real.log (σ.P j)|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ j))
  have hsumpc0 : 0 ≤ ∑ j, |Real.log (pc j)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsumP0 : 0 ≤ ∑ j, |Real.log (σ.P j)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hT1 : (1 : ℝ) ≤ (T : ℝ) + 1 := by have : (0 : ℝ) ≤ T := Nat.cast_nonneg _; linarith
  have hlogT : 0 ≤ Real.log ((T : ℝ) + 1) := Real.log_nonneg hT1
  set U := smoothed pc N T with hU
  -- properties of U
  have hden : 0 < (T : ℝ) + S := by
    have : 0 < S := by
      have hd : 0 < d := by have := σ.two_le; omega
      exact Finset.sum_pos (fun j _ => hpc j) ⟨⟨0, hd⟩, Finset.mem_univ _⟩
    have : (0 : ℝ) ≤ T := Nat.cast_nonneg _
    linarith
  have hU0 : ∀ j, 0 < U j := by
    intro j
    rw [hU]
    unfold smoothed
    rw [← hS]
    exact div_pos (by have := hpc j; have : (0 : ℝ) ≤ N j := Nat.cast_nonneg _; linarith) hden
  have hUsum : ∑ j, U j = 1 := by
    rw [hU]
    unfold smoothed
    rw [← hS, ← Finset.sum_div, Finset.sum_add_distrib, ← hS]
    have : (∑ j, (N j : ℝ)) = T := by exact_mod_cast hN
    rw [this, div_self hden.ne']
  have hU1 : ∀ j, U j ≤ 1 := fun j => by
    rw [← hUsum]
    exact Finset.single_le_sum (fun k _ => (hU0 k).le) (Finset.mem_univ j)
  have hP1 : ∀ j, σ.P j ≤ 1 := fun j => by
    rw [← σ.P_sum]
    exact Finset.single_le_sum (fun k _ => (σ.P_pos k).le) (Finset.mem_univ j)
  obtain ⟨j0, hj0⟩ := σ.ε₀_lt
  have hε0 := σ.ε₀_pos
  have hε1 : σ.ε₀ < 1 := by linarith [σ.P_pos j0]
  -- lower bound on U i
  have hUi : Real.log (pc i) - Real.log (1 + S) - Real.log ((T : ℝ) + 1) ≤ Real.log (U i) := by
    have hle : pc i / ((1 + S) * ((T : ℝ) + 1)) ≤ U i := by
      rw [hU]
      unfold smoothed
      rw [← hS]
      have : (0 : ℝ) ≤ N i := Nat.cast_nonneg _
      have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
      calc pc i / ((1 + S) * ((T : ℝ) + 1)) ≤ pc i / ((T : ℝ) + S) := by
            apply div_le_div_of_nonneg_left (hpc i).le hden
            nlinarith
        _ ≤ ((N i : ℝ) + pc i) / ((T : ℝ) + S) := by
            apply div_le_div_of_nonneg_right (by linarith) hden.le
    have hpos : 0 < pc i / ((1 + S) * ((T : ℝ) + 1)) := by
      have := hpc i; positivity
    have := Real.log_le_log hpos hle
    rw [Real.log_div (hpc i).ne' (by positivity), Real.log_mul (by linarith) (by linarith)] at this
    linarith
  by_cases hnull : U ∈ nullBall σ
  · unfold oracleE
    rw [if_pos hnull, Real.log_one, abs_zero]
    linarith
  · -- existence of the roots
    have hlow : ∃ z, IsLowerRoot σ U z := by
      set f : ℝ → ℝ := fun z => ∑ j, max (z * σ.P j - U j) 0 - z * σ.ε₀ with hf
      have hfc : Continuous f := by rw [hf]; fun_prop
      set z0 := ∏ j, U j with hz0
      have hz0pos : 0 < z0 := Finset.prod_pos fun j _ => hU0 j
      have hz0le : z0 ≤ 1 := Finset.prod_le_one (fun j _ => (hU0 j).le) (fun j _ => hU1 j)
      set z1 := 2 / (1 - σ.ε₀) with hz1
      have hz1ge : 2 ≤ z1 := by
        rw [hz1, le_div_iff₀ (by linarith)]; linarith
      have hf0 : f z0 < 0 := by
        rw [hf]
        simp only
        have : ∑ j, max (z0 * σ.P j - U j) 0 = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          apply max_eq_right
          have h1 := prod_le_each U hU0 hU1 j
          have h2 : z0 * σ.P j ≤ z0 := by
            have := hP1 j; nlinarith
          linarith
        rw [this]
        nlinarith
      have hf1 : 0 < f z1 := by
        rw [hf]
        simp only
        have h1 : ∑ j, (z1 * σ.P j - U j) ≤ ∑ j, max (z1 * σ.P j - U j) 0 :=
          Finset.sum_le_sum fun j _ => le_max_left _ _
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, σ.P_sum, hUsum] at h1
        have hne : 1 - σ.ε₀ ≠ 0 := by linarith
        have h2 : z1 * (1 - σ.ε₀) = 2 := by rw [hz1, div_mul_cancel₀ _ hne]
        nlinarith
      obtain ⟨z, hz, hfz⟩ := intermediate_value_Icc (by linarith) hfc.continuousOn
        (show (0 : ℝ) ∈ Set.Icc (f z0) (f z1) from ⟨hf0.le, hf1.le⟩)
      refine ⟨z, lt_of_lt_of_le hz0pos hz.1, ?_⟩
      have := hfz
      rw [hf] at this
      simp only at this
      linarith
    have hup : ∃ z, IsUpperRoot σ U z := by
      set g : ℝ → ℝ := fun z => ∑ j, max (U j - z * σ.P j) 0 - z * σ.ε₀ with hg
      have hgc : Continuous g := by rw [hg]; fun_prop
      set z1 := ∑ j, 1 / σ.P j with hz1
      have hz1ge : ∀ j, 1 / σ.P j ≤ z1 := fun j =>
        Finset.single_le_sum (f := fun j => 1 / σ.P j)
          (fun k _ => (one_div_pos.mpr (σ.P_pos k)).le) (Finset.mem_univ j)
      have hz1pos : 0 < z1 := lt_of_lt_of_le (one_div_pos.mpr (σ.P_pos i)) (hz1ge i)
      have hg0 : g 0 = 1 := by
        rw [hg]
        simp only [zero_mul, sub_zero]
        rw [← hUsum]
        apply Finset.sum_congr rfl
        intro j _
        exact max_eq_left (hU0 j).le
      have hg1 : g z1 < 0 := by
        rw [hg]
        simp only
        have : ∑ j, max (U j - z1 * σ.P j) 0 = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          apply max_eq_right
          have h1 := hz1ge j
          have hPj := σ.P_pos j
          have h2 : 1 ≤ z1 * σ.P j := by
            rw [div_le_iff₀ hPj] at h1; linarith
          linarith [hU1 j]
        rw [this]
        nlinarith
      obtain ⟨z, hz, hgz⟩ := intermediate_value_Icc' hz1pos.le hgc.continuousOn
        (show (0 : ℝ) ∈ Set.Icc (g z1) (g 0) from ⟨hg1.le, by rw [hg0]; norm_num⟩)
      have hzne : z ≠ 0 := by
        intro h; rw [h, hg0] at hgz; norm_num at hgz
      refine ⟨z, lt_of_le_of_ne hz.1 (Ne.symm hzne), ?_⟩
      have := hgz
      rw [hg] at this
      simp only at this
      linarith
    have hlo : IsLowerRoot σ U (lowerThr σ U) := Classical.epsilon_spec hlow
    have hhi : IsUpperRoot σ U (upperThr σ U) := Classical.epsilon_spec hup
    set lo := lowerThr σ U with hlodef
    set hi := upperThr σ U with hhidef
    -- bounds on the thresholds
    have hlo_le : lo ≤ 1 / σ.P j0 := by
      obtain ⟨hlo0, hloeq⟩ := hlo
      have h1 : ∑ j, (lo * σ.P j - U j) ≤ ∑ j, max (lo * σ.P j - U j) 0 :=
        Finset.sum_le_sum fun j _ => le_max_left _ _
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, σ.P_sum, hUsum, hloeq] at h1
      have hPj := σ.P_pos j0
      rw [le_div_iff₀ hPj]
      have h3 := mul_lt_mul_of_pos_left hj0 hlo0
      linarith
    have hhi_ge : 1 / 2 ≤ hi := by
      obtain ⟨hhi0, hhieq⟩ := hhi
      have h1 : ∑ j, (U j - hi * σ.P j) ≤ ∑ j, max (U j - hi * σ.P j) 0 :=
        Finset.sum_le_sum fun j _ => le_max_left _ _
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, σ.P_sum, hUsum, hhieq] at h1
      have h3 := mul_lt_mul_of_pos_left hε1 hhi0
      linarith
    set w := U i / σ.P i with hw
    have hwpos : 0 < w := div_pos (hU0 i) (σ.P_pos i)
    have hwge : U i ≤ w := by
      rw [hw, le_div_iff₀ (σ.P_pos i)]
      nlinarith [hP1 i, hU0 i]
    have hwle : w ≤ 1 / σ.P i := by
      rw [hw]; exact div_le_div_of_nonneg_right (hU1 i) (σ.P_pos i).le
    unfold oracleE
    rw [if_neg hnull]
    unfold clip
    rw [← hlodef, ← hhidef, ← hw]
    set v := min hi (max lo w) with hv
    have hvlo : min hi w ≤ v := min_le_min le_rfl (le_max_right _ _)
    have hvpos : 0 < v := lt_of_lt_of_le (lt_min (by linarith) hwpos) hvlo
    have hvup : v ≤ max (1 / σ.P j0) (1 / σ.P i) :=
      (min_le_right _ _).trans (max_le_max hlo_le hwle)
    -- upper bound on log v
    have hup_log : Real.log v ≤ ∑ j, |Real.log (σ.P j)| := by
      have := Real.log_le_log hvpos hvup
      rcases le_total (1 / σ.P j0) (1 / σ.P i) with h | h
      · rw [max_eq_right h, one_div, Real.log_inv] at this
        linarith [hsumP i]
      · rw [max_eq_left h, one_div, Real.log_inv] at this
        linarith [hsumP j0]
    -- lower bound on log v
    have hlow_log : -(Real.log 2 + ∑ j, |Real.log (pc j)| + Real.log (1 + S)) -
        Real.log ((T : ℝ) + 1) ≤ Real.log v := by
      have hm := Real.log_le_log (lt_min (by linarith) hwpos) hvlo
      rcases le_total hi w with h | h
      · rw [min_eq_left h] at hm
        have : Real.log (1 / 2) ≤ Real.log hi := Real.log_le_log (by norm_num) hhi_ge
        rw [one_div, Real.log_inv] at this
        linarith
      · rw [min_eq_right h] at hm
        have := Real.log_le_log (hU0 i) hwge
        linarith [hsumpc i]
    rw [abs_le]
    constructor <;> linarith
