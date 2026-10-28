-- Prove2me | solution 1 for SmoothCCP.PenaltyModel.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:05:30.075791+00:00
-- url     : https://prove2.me/submissions/b6d0ea9a-a11c-4374-9cf8-f1162e96b41e

import Mathlib
import Definitions.Def_SmoothCCP_PenaltyModel_Setting

open SmoothCCP.Feasibility

open SmoothCCP.PenaltyModel in
theorem solution {N : ℕ} (ε α : ℝ) (γ : ℝ → ℝ) (hε : 0 < ε)
    (hγmaps : ∀ y ∈ Set.Icc (-ε) ε, γ y ∈ Set.Icc (0 : ℝ) 1)
    (hγanti : StrictAntiOn γ (Set.Icc (-ε) ε))
    (hΓdiff : Differentiable ℝ (SmoothCCP.Feasibility.Gam ε γ))
    (hα0 : 0 < α) (hα1 : α < 1) (hN : 1 ≤ N) (hαN : ∀ k : ℤ, (1 - α) * N ≠ k)
    (z : Fin N → ℝ) :
    (∃! q : ℝ, ∑ i, SmoothCCP.Feasibility.Gam ε γ (z i - q) = (1 - α) * N) ∧
      ∑ i, SmoothCCP.Feasibility.Gam ε γ (z i - smoothQuantile ε γ α z) = (1 - α) * N := by
  set G := Gam ε γ with hG
  have G0 : ∀ y, ε ≤ y → G y = 0 := fun y hy => by
    simp only [hG, Gam]; rw [if_neg (by linarith), if_neg (by linarith)]
  have G1 : ∀ y, y ≤ -ε → G y = 1 := fun y hy => by
    simp only [hG, Gam]; rw [if_pos hy]
  have Gmid : ∀ y, -ε < y → y < ε → G y = γ y := fun y h1 h2 => by
    simp only [hG, Gam]; rw [if_neg (by linarith), if_pos h2]
  have Gbd : ∀ y, 0 ≤ G y ∧ G y ≤ 1 := by
    intro y
    by_cases h1 : y ≤ -ε
    · rw [G1 y h1]; norm_num
    · by_cases h2 : y < ε
      · rw [Gmid y (by linarith) h2]
        exact hγmaps y ⟨by linarith, h2.le⟩
      · rw [G0 y (by linarith)]; norm_num
  have Ganti : Antitone G := by
    intro y1 y2 h
    by_cases a1 : y2 ≤ -ε
    · rw [G1 y1 (le_trans h a1), G1 y2 a1]
    · by_cases a2 : y1 ≥ ε
      · rw [G0 y1 a2, G0 y2 (le_trans a2 h)]
      · by_cases a3 : y1 ≤ -ε
        · rw [G1 y1 a3]; exact (Gbd y2).2
        · by_cases a4 : y2 < ε
          · rw [Gmid y1 (by linarith) (by linarith), Gmid y2 (by linarith) a4]
            exact hγanti.antitoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, a4.le⟩ h
          · rw [G0 y2 (by linarith)]; exact (Gbd y1).1
  have Gcont : Continuous G := hΓdiff.continuous
  set h : ℝ → ℝ := fun q => ∑ i, G (z i - q) with hh
  have hcont : Continuous h :=
    continuous_finset_sum _ (fun i _ => Gcont.comp (continuous_const.sub continuous_id))
  have hmono : Monotone h := by
    intro q1 q2 hq
    exact Finset.sum_le_sum (fun i _ => Ganti (by linarith))
  set c := (1 - α) * (N : ℝ) with hc
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hc0 : 0 < c := by rw [hc]; nlinarith
  have hcN : c ≤ N := by rw [hc]; nlinarith
  set M := ∑ i, |z i| with hM
  have hzM : ∀ i, |z i| ≤ M := fun i =>
    Finset.single_le_sum (f := fun j => |z j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hlo : h (-M - ε) = 0 := by
    simp only [hh]
    apply Finset.sum_eq_zero
    intro i _
    apply G0
    have := neg_abs_le (z i); have := hzM i; linarith
  have hhi : h (M + ε) = N := by
    simp only [hh]
    rw [Finset.sum_congr rfl (fun i _ => G1 _ (by have := le_abs_self (z i); have := hzM i; linarith))]
    simp
  -- strict increase past a root
  have hstrict : ∀ q1 q2, q1 < q2 → h q1 = c → c < h q2 := by
    intro q1 q2 hq hq1
    have hex : ∃ i, 0 < G (z i - q1) ∧ G (z i - q1) < 1 := by
      by_contra hno
      push_neg at hno
      have h01 : ∀ i, G (z i - q1) = if G (z i - q1) = 1 then 1 else 0 := by
        intro i
        split_ifs with h1
        · exact h1
        · have a := Gbd (z i - q1)
          have b := hno i
          by_contra hne
          have : 0 < G (z i - q1) := lt_of_le_of_ne a.1 (Ne.symm hne)
          have := b this
          exact h1 (le_antisymm a.2 this)
      have hsum : h q1 = ((Finset.univ.filter (fun i => G (z i - q1) = 1)).card : ℝ) := by
        simp only [hh]
        rw [Finset.sum_congr rfl (fun i _ => h01 i), Finset.sum_ite, Finset.sum_const_zero,
          add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
      apply hαN ((Finset.univ.filter (fun i => G (z i - q1) = 1)).card : ℤ)
      rw [← hq1, hsum]
      push_cast; rfl
    obtain ⟨i, hi0, hi1⟩ := hex
    have hy1a : ¬ (z i - q1 ≤ -ε) := fun hc' => by rw [G1 _ hc'] at hi1; linarith
    have hy1b : z i - q1 < ε := by
      by_contra hc'; push_neg at hc'; rw [G0 _ hc'] at hi0; linarith
    have hgt : G (z i - q1) < G (z i - q2) := by
      by_cases hy2 : z i - q2 ≤ -ε
      · rw [G1 _ hy2]; exact hi1
      · rw [Gmid _ (by linarith) hy1b, Gmid _ (by linarith) (by linarith)]
        exact hγanti ⟨by linarith, by linarith⟩ ⟨by linarith, hy1b.le⟩ (by linarith)
    have hdiff : h q2 - h q1 = ∑ j, (G (z j - q2) - G (z j - q1)) := by
      simp only [hh]; rw [Finset.sum_sub_distrib]
    have hterm : G (z i - q2) - G (z i - q1) ≤ ∑ j, (G (z j - q2) - G (z j - q1)) :=
      Finset.single_le_sum (f := fun j => G (z j - q2) - G (z j - q1))
        (fun j _ => sub_nonneg.mpr (Ganti (by linarith))) (Finset.mem_univ i)
    linarith
  -- existence
  have hlohi : -M - ε ≤ M + ε := by
    have : 0 ≤ M := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    linarith
  obtain ⟨r, hr, hrc⟩ : ∃ r ∈ Set.Icc (-M - ε) (M + ε), h r = c := by
    have := intermediate_value_Icc hlohi hcont.continuousOn
    exact this ⟨by rw [hlo]; exact hc0.le, by rw [hhi]; exact hcN⟩
  refine ⟨⟨r, hrc, fun q hq => ?_⟩, ?_⟩
  · by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hstrict q r hlt hq; linarith
    · have := hstrict r q hlt hrc; linarith
  · -- the least root
    set S := {q : ℝ | c ≤ h q} with hS
    have hSdef : smoothQuantile ε γ α z = sInf S := rfl
    have hbdd : BddBelow S := by
      refine ⟨-M - ε, fun q hq => ?_⟩
      by_contra hlt
      push_neg at hlt
      have := hmono hlt.le
      rw [hlo] at this
      have hq' : c ≤ h q := hq
      linarith
    have hne : S.Nonempty := ⟨r, by rw [hS]; exact hrc.symm.le⟩
    have hclosed : IsClosed S := isClosed_le continuous_const hcont
    have hmem : sInf S ∈ S := hclosed.csInf_mem hne hbdd
    have hle : sInf S ≤ r := csInf_le hbdd (by rw [hS]; exact hrc.symm.le)
    rw [hSdef]
    have a1 : c ≤ h (sInf S) := hmem
    have a2 : h (sInf S) ≤ h r := hmono hle
    show h (sInf S) = c
    linarith
