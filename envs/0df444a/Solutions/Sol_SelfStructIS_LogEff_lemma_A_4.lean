-- Prove2me | solution 1 for SelfStructIS.LogEff.lemma_A_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T18:21:20.934734+00:00
-- url     : https://prove2.me/submissions/cd7ea067-9c69-4d3b-ac56-6ab11e1cf1de

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model
import Definitions.Def_SelfStructIS_LogEff_Setting
import Definitions.Def_SelfStructIS_LogEff_Sampler
import Definitions.Def_SelfStructIS_LogEff_Tail

open MeasureTheory Filter Topology

lemma ssis_A4_key_log (a b : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    Real.log (1 + b) * Real.log a ≤ Real.log (1 + a) * Real.log b := by
  have hla : 0 < Real.log a := Real.log_pos ha
  have hlb : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  have hs1 : 1 ≤ Real.log b / Real.log a := by rw [le_div_iff₀ hla]; linarith
  have hbs : b = a ^ (Real.log b / Real.log a) := by
    rw [Real.rpow_def_of_pos (by linarith), mul_div_cancel₀ _ hla.ne',
      Real.exp_log (by linarith)]
  have hsup : 1 + a ^ (Real.log b / Real.log a) ≤ (1 + a) ^ (Real.log b / Real.log a) := by
    have ha0 : (0:ℝ) ≤ a := by linarith
    have h := NNReal.add_rpow_le_rpow_add (1 : NNReal) ⟨a, ha0⟩ hs1
    have h' : ((1 : NNReal) : ℝ) ^ (Real.log b / Real.log a) +
        ((⟨a, ha0⟩ : NNReal) : ℝ) ^ (Real.log b / Real.log a) ≤
        (((1 : NNReal) : ℝ) + ((⟨a, ha0⟩ : NNReal) : ℝ)) ^ (Real.log b / Real.log a) := by
      exact_mod_cast h
    simpa using h'
  have h1 : Real.log (1 + b) ≤ (Real.log b / Real.log a) * Real.log (1 + a) := by
    rw [← Real.log_rpow (by linarith)]
    calc Real.log (1 + b) = Real.log (1 + a ^ (Real.log b / Real.log a)) := by
          rw [← hbs]
      _ ≤ _ := Real.log_le_log (by positivity) hsup
  calc Real.log (1 + b) * Real.log a
      ≤ (Real.log b / Real.log a) * Real.log (1 + a) * Real.log a :=
        mul_le_mul_of_nonneg_right h1 hla.le
    _ = Real.log (1 + a) * Real.log b := by field_simp

open SelfStructIS.LogEff in
theorem solution (d : ℕ) (ρ u l : ℝ) (hρ : 0 < ρ) (hl : 0 < l) (hlu : l < u)
    (y : Fin d → ℝ) (hy : ∀ i, 0 ≤ y i) (hy_norm : 1 / cRho ρ u l ≤ ‖y‖)
    (x : Fin d → ℝ) (hx : Tmap .one ρ u l x = y) :
    (∀ i, y i * cRho ρ u l ≤ x i) ∧
      ∀ i, x i ≤ min (max (y i * cRho ρ u l ^ (Real.log (y i) / Real.log ‖y‖)) 1)
        (‖y‖ * cRho ρ u l) := by
  have hu : 0 < u := by linarith
  have hB0 : 0 < Real.log (u / l) := Real.log_pos (by rw [one_lt_div hl]; exact hlu)
  set B := Real.log (u / l) with hB
  set M := ‖fun j => Real.log (1 + |x j|)‖ with hM
  have hBρ : 0 < B / ρ := div_pos hB0 hρ
  have hc : cRho ρ u l = Real.exp (-(B / ρ)) := by
    unfold cRho
    rw [Real.rpow_def_of_pos (div_pos hl hu)]
    congr 1
    rw [← inv_div u l, Real.log_inv]; ring
  have hcpos : 0 < cRho ρ u l := by rw [hc]; exact Real.exp_pos _
  have hyi : ∀ i, y i = x i * Real.exp (B / ρ * (Real.log (1 + |x i|) / M)) := by
    intro i
    rw [← hx]
    simp only [Tmap, kappa, kappa1]
    rw [Real.rpow_def_of_pos (div_pos hu hl)]
    congr 2
    rw [← hB, ← hM]; ring
  have hx0 : ∀ i, 0 ≤ x i := by
    intro i
    have h1 := hyi i
    have he := Real.exp_pos (B / ρ * (Real.log (1 + |x i|) / M))
    by_contra h; push Not at h
    have := hy i
    nlinarith
  have habs : ∀ i, |x i| = x i := fun i => abs_of_nonneg (hx0 i)
  have hL0 : ∀ i, 0 ≤ Real.log (1 + |x i|) := fun i =>
    Real.log_nonneg (by linarith [abs_nonneg (x i)])
  have hLM : ∀ i, Real.log (1 + |x i|) ≤ M := by
    intro i
    have := norm_le_pi_norm (fun j => Real.log (1 + |x j|)) i
    rwa [Real.norm_of_nonneg (hL0 i)] at this
  have hinvc : 0 < 1 / cRho ρ u l := by positivity
  have hne : Nonempty (Fin d) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : y = 0 := Subsingleton.elim _ _
    rw [this, norm_zero] at hy_norm
    linarith
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ x Finset.univ_nonempty
  have hk' : ∀ j, x j ≤ x k := fun j => hk j (Finset.mem_univ j)
  have hMk : M = Real.log (1 + |x k|) := by
    apply le_antisymm _ (hLM k)
    refine (pi_norm_le_iff_of_nonneg (hL0 k)).2 (fun j => ?_)
    rw [Real.norm_of_nonneg (hL0 j), habs, habs]
    exact Real.log_le_log (by linarith [hx0 j]) (by linarith [hk' j])
  have hMpos : 0 < M := by
    by_contra hM0
    push Not at hM0
    have hxk : x k = 0 := by
      by_contra hne'
      have : 0 < x k := lt_of_le_of_ne (hx0 k) (Ne.symm hne')
      have : 0 < Real.log (1 + |x k|) := Real.log_pos (by rw [habs]; linarith)
      linarith
    have hy0 : ‖y‖ ≤ 0 := by
      refine (pi_norm_le_iff_of_nonneg le_rfl).2 (fun j => ?_)
      have hxj : x j = 0 := le_antisymm (hxk ▸ hk' j) (hx0 j)
      rw [hyi j, hxj]; simp
    linarith
  have hyk : y k = x k * Real.exp (B / ρ) := by
    rw [hyi k, ← hMk, div_self hMpos.ne', mul_one]
  have hyk_le : y k ≤ ‖y‖ := by
    have := norm_le_pi_norm y k
    rwa [Real.norm_of_nonneg (hy k)] at this
  have hratio : ∀ i, Real.log (1 + |x i|) / M ≤ 1 := fun i =>
    (div_le_one hMpos).2 (hLM i)
  refine ⟨fun i => ?_, fun i => ?_⟩
  · rw [hyi i, hc, mul_assoc, ← Real.exp_add]
    have : B / ρ * (Real.log (1 + |x i|) / M) + -(B / ρ) ≤ 0 := by
      have := mul_le_mul_of_nonneg_left (hratio i) hBρ.le
      linarith
    calc x i * Real.exp (B / ρ * (Real.log (1 + |x i|) / M) + -(B / ρ))
        ≤ x i * 1 := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 this) (hx0 i)
      _ = x i := mul_one _
  · refine le_min ?_ ?_
    · by_cases hxi : x i ≤ 1
      · exact le_trans hxi (le_max_right _ _)
      · push Not at hxi
        refine le_trans ?_ (le_max_left _ _)
        have hxk1 : 1 < x k := lt_of_lt_of_le hxi (hk' i)
        have hE := Real.exp_pos (B / ρ * (Real.log (1 + |x i|) / M))
        have hE1 : 1 ≤ Real.exp (B / ρ * (Real.log (1 + |x i|) / M)) :=
          Real.one_le_exp (mul_nonneg hBρ.le (div_nonneg (hL0 i) hMpos.le))
        have hyi1 : 1 < y i := by
          rw [hyi i]; nlinarith
        have hyk1 : 1 < y k := by
          rw [hyk]; nlinarith [Real.one_le_exp hBρ.le]
        have hlogyi : Real.log (y i) = Real.log (x i) + B / ρ * (Real.log (1 + |x i|) / M) := by
          rw [hyi i, Real.log_mul (by linarith) hE.ne', Real.log_exp]
        have hlogyk : Real.log (y k) = Real.log (x k) + B / ρ := by
          rw [hyk, Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp]
        have hlogyk0 : 0 < Real.log (y k) := Real.log_pos hyk1
        have hlognorm : Real.log (y k) ≤ Real.log ‖y‖ := Real.log_le_log (by linarith) hyk_le
        have hlognorm0 : 0 < Real.log ‖y‖ := lt_of_lt_of_le hlogyk0 hlognorm
        have hkey := ssis_A4_key_log (x i) (x k) hxi (hk' i)
        have hL0' : 0 ≤ Real.log (1 + x i) := by rw [← habs i]; exact hL0 i
        have hMk' : M = Real.log (1 + x k) := by rw [hMk, habs]
        -- r ≤ L_i / M
        have hr : Real.log (y i) / Real.log ‖y‖ ≤ Real.log (1 + |x i|) / M := by
          rw [div_le_div_iff₀ hlognorm0 hMpos, hlogyi, habs]
          have e1 : (Real.log (x i) + B / ρ * (Real.log (1 + x i) / M)) * M
              = Real.log (x i) * M + B / ρ * Real.log (1 + x i) := by
            field_simp
          rw [e1]
          calc Real.log (x i) * M + B / ρ * Real.log (1 + x i)
              ≤ Real.log (1 + x i) * Real.log (x k) + B / ρ * Real.log (1 + x i) := by
                rw [hMk']; linarith
            _ = Real.log (1 + x i) * Real.log (y k) := by rw [hlogyk]; ring
            _ ≤ Real.log (1 + x i) * Real.log ‖y‖ :=
                mul_le_mul_of_nonneg_left hlognorm hL0'
        generalize Real.log (y i) / Real.log ‖y‖ = r at hr ⊢
        rw [hc, ← Real.exp_mul, hyi i, mul_assoc, ← Real.exp_add]
        have : 0 ≤ B / ρ * (Real.log (1 + |x i|) / M) +
            -(B / ρ) * r := by
          have := mul_le_mul_of_nonneg_left hr hBρ.le
          linarith
        calc x i = x i * 1 := (mul_one _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_left (Real.one_le_exp this) (hx0 i)
    · rw [hc]
      calc x i ≤ x k := hk' i
        _ = y k * Real.exp (-(B / ρ)) := by
            rw [hyk, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
        _ ≤ ‖y‖ * Real.exp (-(B / ρ)) :=
            mul_le_mul_of_nonneg_right hyk_le (Real.exp_pos _).le
