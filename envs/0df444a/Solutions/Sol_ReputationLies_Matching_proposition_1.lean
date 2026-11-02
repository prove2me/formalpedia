-- Prove2me | solution 1 for ReputationLies.Matching.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T11:06:34.325346+00:00
-- url     : https://prove2.me/submissions/8d45744d-7707-4e4d-a671-ff7d0f60cd34

import Mathlib
import Definitions.Def_ReputationLies_Matching_Model
import Theorems.Thm_ReputationLies_Matching_step_4_bayes_belief
import Theorems.Thm_ReputationLies_Matching_step_5_threshold

open Set MeasureTheory ReputationLies.Matching

namespace RepLiesProp1Aux

theorem hire_eq (μ : Measure ℝ) (hμ : μ (Icc (0:ℝ) 1)ᶜ = 0) (f : ℝ → Bool) (s : ℝ)
    (hf : ∀ x ∈ Icc (0:ℝ) 1, (f x = true ↔ x ≤ s)) :
    μ {x | f x = true} = μ (Iic s) := by
  rw [← measure_inter_conull (s := {x | f x = true}) hμ,
    ← measure_inter_conull (s := Iic s) hμ]
  congr 1
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq, mem_Iic]
  constructor
  · rintro ⟨h, hx⟩; exact ⟨(hf x hx).1 h, hx⟩
  · rintro ⟨h, hx⟩; exact ⟨(hf x hx).2 h, hx⟩

theorem compl_null (μ : Measure ℝ) [IsProbabilityMeasure μ] (h1 : μ (Icc (0:ℝ) 1) = 1) :
    μ (Icc (0:ℝ) 1)ᶜ = 0 := by
  rw [measure_compl measurableSet_Icc (measure_ne_top _ _), h1, measure_univ]; simp

theorem pos_mass (P : Primitives) [IsProbabilityMeasure P.μB] (hZ : StrictMonoOn P.Z (Icc 0 1))
    (δ : ℝ) (hδ : δ ∈ Ioc (0:ℝ) 1) : 0 < P.μB.real (Ioc 0 δ) := by
  have hU : Iic (0:ℝ) ∪ Ioc 0 δ = Iic δ := Iic_union_Ioc_eq_Iic hδ.1.le
  have hD : Disjoint (Iic (0:ℝ)) (Ioc 0 δ) := by
    rw [Set.disjoint_left]; intro x hx hx'; exact absurd hx (not_le.mpr hx'.1)
  have := measureReal_union (μ := P.μB) hD measurableSet_Ioc
  rw [hU] at this
  have hz := hZ ⟨le_rfl, zero_le_one⟩ ⟨hδ.1.le, hδ.2⟩ hδ.1
  simp only [Primitives.Z, ← measureReal_def] at hz
  linarith

theorem rec_nonneg (P : Primitives) (σ : Profile) (hi : Bool) : 0 ≤ recProb P σ hi :=
  ENNReal.toReal_nonneg

theorem rec_le_one (P : Primitives) [IsProbabilityMeasure P.μB] (σ : Profile) (hi : Bool) :
    recProb P σ hi ≤ 1 := by
  unfold recProb; rw [← measureReal_def]; exact measureReal_le_one

theorem rec_pos (P : Primitives) [IsProbabilityMeasure P.μB] (hZ : StrictMonoOn P.Z (Icc 0 1))
    (σ : Profile) (hi : Bool) (δ : ℝ) (hδ : δ ∈ Ioc (0:ℝ) 1)
    (h : ∀ b ∈ Ioc (0:ℝ) δ, σ.σA b hi = true) : 0 < recProb P σ hi := by
  unfold recProb; rw [← measureReal_def]
  exact lt_of_lt_of_le (pos_mass P hZ δ hδ) (measureReal_mono (fun b hb => h b hb))

theorem rec_lt_one (P : Primitives) [IsProbabilityMeasure P.μB] (hZ : StrictMonoOn P.Z (Icc 0 1))
    (σ : Profile) (hi : Bool) (δ : ℝ) (hδ : δ ∈ Ioc (0:ℝ) 1)
    (h : ∀ b ∈ Ioc (0:ℝ) δ, σ.σA b hi = false) : recProb P σ hi < 1 := by
  unfold recProb; rw [← measureReal_def]
  have hD : Disjoint {b | σ.σA b hi = true} (Ioc 0 δ) := by
    rw [Set.disjoint_left]; intro x hx hx'
    simp only [mem_ofPred_eq] at hx
    rw [h x hx'] at hx; exact Bool.false_ne_true hx
  have h1 := measureReal_union (μ := P.μB) hD measurableSet_Ioc
  have h2 : P.μB.real ({b | σ.σA b hi = true} ∪ Ioc 0 δ) ≤ 1 := measureReal_le_one
  have h3 := pos_mass P hZ δ hδ
  linarith

theorem rec_zero (P : Primitives) (h01 : P.μB (Icc (0:ℝ) 1)ᶜ = 0) (σ : Profile) (hi : Bool)
    (h : ∀ b ∈ Icc (0:ℝ) 1, σ.σA b hi = false) : recProb P σ hi = 0 := by
  unfold recProb
  have : P.μB {b | σ.σA b hi = true} = 0 := by
    apply measure_mono_null _ h01
    intro b hb hb'
    simp only [mem_ofPred_eq] at hb
    rw [h b hb'] at hb; exact Bool.false_ne_true hb
  simp [this]

theorem rec_one (P : Primitives) [IsProbabilityMeasure P.μB] (h1 : P.μB (Icc (0:ℝ) 1) = 1)
    (σ : Profile) (hi : Bool)
    (h : ∀ b ∈ Icc (0:ℝ) 1, σ.σA b hi = true) : recProb P σ hi = 1 := by
  unfold recProb
  have : P.μB {b | σ.σA b hi = true} = 1 := by
    apply le_antisymm prob_le_one
    rw [← h1]; exact measure_mono (fun b hb => h b hb)
  simp [this]

theorem udiff (P : Primitives) (σ : Profile) (r b : ℝ) (hi : Bool) :
    utility P σ r b hi true - utility P σ r b hi false =
      hireProb P σ true * (b + ((if hi then P.v (r + P.g r) else P.v (r - P.c r)) - P.v r))
        - b * hireProb P σ false := by
  unfold utility; simp only [if_true, Bool.false_eq_true, if_false]; ring

/-- Basic facts shared by the characterization and existence parts. -/
theorem vfacts (P : Primitives) (hP : P.Standing) (r : ℝ) (hr : 0 < r) :
    0 < P.v (r + P.g r) - P.v r ∧ 0 < P.L r := by
  obtain ⟨-, -, -, -, -, hgc, -, hvd, hvd', -⟩ := hP
  have hvm : StrictMonoOn P.v (Ioi 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi 0) hvd.continuousOn
    intro x hx; rw [interior_Ioi] at hx; exact hvd' x hx
  obtain ⟨hg, hc, hcr⟩ := hgc r hr
  refine ⟨?_, ?_⟩
  · have := hvm (mem_Ioi.mpr hr) (mem_Ioi.mpr (by linarith : (0:ℝ) < r + P.g r))
      (by linarith : r < r + P.g r)
    linarith
  · have := hvm (mem_Ioi.mpr (by linarith : (0:ℝ) < r - P.c r)) (mem_Ioi.mpr hr)
      (by linarith : r - P.c r < r)
    unfold Primitives.L; linarith

/-- The threshold characterization of an arbitrary equilibrium (Steps 1–5 of the proof). -/
theorem charac (P : Primitives) (hP : P.Standing) (r : ℝ) (hr : 0 < r) (σ : Profile)
    (hσ : IsEquilibrium P σ r) : ∃ bstar ∈ Ioc (0 : ℝ) 1,
      (∀ b ∈ Icc (0 : ℝ) 1, σ.σA b true = true) ∧
      (∀ b ∈ Icc (0 : ℝ) 1, (σ.σA b false = true ↔ bstar < b)) ∧
      σ.sNR = P.sL ∧ (∀ x ∈ Icc (0 : ℝ) 1, (σ.σF x false = true ↔ x ≤ P.sL)) ∧
      σ.sR = P.sRof bstar ∧ (∀ x ∈ Icc (0 : ℝ) 1, (σ.σF x true = true ↔ x ≤ P.sRof bstar)) ∧
      (bstar = 1 ↔ P.Bbar ≤ P.L r) ∧ (bstar < 1 → P.lieGain bstar = P.L r) := by
  obtain ⟨hbayes4, -, -, -, h41⟩ := step_4_bayes_belief P hP
  obtain ⟨hlgM, -, hlg1, -⟩ := step_5_threshold P hP
  obtain ⟨hΔH, hL⟩ := vfacts P hP r hr
  obtain ⟨hsL, hsLH, hsH1, hp0, hp1, -, -, -, -, -, -, -, hμB, hμB1, -, hZ, hμX, hμX1, -, hF, -⟩ :=
    hP
  obtain ⟨hmA, -, hbest, htie, hfirm, hsR, hsNR, hbR, hbNR⟩ := hσ
  have hX0 := compl_null P.μX hμX1
  have hB0 := compl_null P.μB hμB1
  have hsRI : σ.sR ∈ Icc (0:ℝ) 1 := ⟨by linarith [hsR.1], by linarith [hsR.2]⟩
  have hsNRI : σ.sNR ∈ Icc (0:ℝ) 1 := ⟨by linarith [hsNR.1], by linarith [hsNR.2]⟩
  have hsLI : P.sL ∈ Icc (0:ℝ) 1 := ⟨hsL.le, by linarith⟩
  have hsHI : P.sH ∈ Icc (0:ℝ) 1 := ⟨by linarith, hsH1.le⟩
  have hhR : hireProb P σ true = P.F σ.sR := by
    unfold hireProb Primitives.F
    rw [hire_eq P.μX hX0 (fun x => σ.σF x true) σ.sR (fun x hx => (hfirm x hx).1)]
  have hhNR : hireProb P σ false = P.F σ.sNR := by
    unfold hireProb Primitives.F
    rw [hire_eq P.μX hX0 (fun x => σ.σF x false) σ.sNR (fun x hx => (hfirm x hx).2)]
  have hF0 : 0 ≤ P.F 0 := ENNReal.toReal_nonneg
  have hFle : ∀ x, P.F x ≤ 1 := fun x => by
    unfold Primitives.F; rw [← measureReal_def]; exact measureReal_le_one
  have hFsL : 0 < P.F P.sL := lt_of_le_of_lt hF0 (hF ⟨le_rfl, zero_le_one⟩ hsLI hsL)
  have hRge : P.F P.sL ≤ P.F σ.sR := hF.monotoneOn hsLI hsRI hsR.1
  have hNRge : P.F P.sL ≤ P.F σ.sNR := hF.monotoneOn hsLI hsNRI hsNR.1
  set hR := P.F σ.sR with hhRdef
  set hN := P.F σ.sNR with hhNdef
  -- utility differences
  have dH : ∀ b, utility P σ r b true true - utility P σ r b true false =
      b * (hR - hN) + hR * (P.v (r + P.g r) - P.v r) := by
    intro b; rw [udiff, hhR, hhNR]; simp only [if_true]; ring
  have dL : ∀ b, utility P σ r b false true - utility P σ r b false false =
      b * (hR - hN) - hR * P.L r := by
    intro b; rw [udiff, hhR, hhNR]; simp only [Bool.false_eq_true, if_false]
    unfold Primitives.L; ring
  have brT : ∀ b ∈ Icc (0:ℝ) 1, ∀ hi, σ.σA b hi = true →
      utility P σ r b hi false ≤ utility P σ r b hi true := by
    intro b hb hi h; have := hbest b hb hi false; rwa [h] at this
  have brF : ∀ b ∈ Icc (0:ℝ) 1, ∀ hi, σ.σA b hi = false →
      utility P σ r b hi true ≤ utility P σ r b hi false := by
    intro b hb hi h; have := hbest b hb hi true; rwa [h] at this
  -- Step A: high types with small bias recommend, so `R` is sent with positive probability
  have hrt_pos : 0 < recProb P σ true := by
    set δ := min 1 (hR * (P.v (r + P.g r) - P.v r) / 2) with hδ
    have hRpos : 0 < hR := lt_of_lt_of_le hFsL hRge
    have hprod : 0 < hR * (P.v (r + P.g r) - P.v r) := mul_pos hRpos hΔH
    have hδI : δ ∈ Ioc (0:ℝ) 1 := ⟨lt_min zero_lt_one (by linarith), min_le_left _ _⟩
    apply rec_pos P hZ σ true δ hδI
    intro b hb
    by_contra hne
    rw [Bool.not_eq_true] at hne
    have h1 := brF b ⟨hb.1.le, le_trans hb.2 hδI.2⟩ true hne
    have h2 := dH b
    have hbδ : b ≤ hR * (P.v (r + P.g r) - P.v r) / 2 := le_trans hb.2 (min_le_right _ _)
    have : -1 ≤ hR - hN := by linarith [hFle σ.sNR]
    nlinarith [hb.1]
  have hmT : 0 < msgProb P σ true := by
    unfold msgProb sendProb; simp only [if_true]
    have := rec_nonneg P σ false
    nlinarith
  have hsR_eq := hbR hmT
  -- Step B: sNR ≤ sR
  have hle : σ.sNR ≤ σ.sR := by
    by_contra hlt
    rw [not_le] at hlt
    have hRN : hR < hN := hF hsRI hsNRI hlt
    have hLno : ∀ b ∈ Icc (0:ℝ) 1, σ.σA b false = false := by
      intro b hb
      by_contra hne
      rw [Bool.not_eq_false] at hne
      have h1 := brT b hb false hne
      have h2 := dL b
      have hRpos : 0 < hR := lt_of_lt_of_le hFsL hRge
      nlinarith [hb.1, mul_pos hRpos hL]
    have hrf := rec_zero P hB0 σ false hLno
    have : σ.sR = P.sH := by
      rw [hsR_eq]; unfold bayesBelief msgProb sendProb
      simp only [if_true, hrf]
      have hx : P.p * recProb P σ true + (1 - P.p) * 0 ≠ 0 := by
        have := mul_pos hp0 hrt_pos; apply ne_of_gt; linarith
      rw [div_eq_iff hx]; ring
    linarith [hsNR.2]
  have hRN : hN ≤ hR := hF.monotoneOn hsNRI hsRI hle
  -- Step C: high types always recommend
  have hAt : ∀ b ∈ Icc (0:ℝ) 1, σ.σA b true = true := by
    intro b hb
    by_contra hne
    rw [Bool.not_eq_true] at hne
    have h1 := brF b hb true hne
    have h2 := dH b
    have hRpos : 0 < hR := lt_of_lt_of_le hFsL hRge
    nlinarith [hb.1, mul_pos hRpos hΔH]
  have hrt1 := rec_one P hμB1 σ true hAt
  -- Step D: sNR = sL
  have hrf_lt : recProb P σ false < 1 := by
    set δ := min 1 (P.F P.sL * P.L r / 2) with hδ
    have hprod : 0 < P.F P.sL * P.L r := mul_pos hFsL hL
    have hδI : δ ∈ Ioc (0:ℝ) 1 := ⟨lt_min zero_lt_one (by linarith), min_le_left _ _⟩
    apply rec_lt_one P hZ σ false δ hδI
    intro b hb
    by_contra hne
    rw [Bool.not_eq_false] at hne
    have h1 := brT b ⟨hb.1.le, le_trans hb.2 hδI.2⟩ false hne
    have h2 := dL b
    have hbδ : b ≤ P.F P.sL * P.L r / 2 := le_trans hb.2 (min_le_right _ _)
    have : hR - hN ≤ 1 := by linarith [hFle σ.sR]
    have : P.F P.sL * P.L r ≤ hR * P.L r := mul_le_mul_of_nonneg_right hRge hL.le
    nlinarith [hb.1]
  have hmF : 0 < msgProb P σ false := by
    unfold msgProb sendProb; simp only [Bool.false_eq_true, if_false, hrt1]
    nlinarith
  have hsNR_eq : σ.sNR = P.sL := by
    rw [hbNR hmF]; unfold bayesBelief msgProb sendProb
    simp only [Bool.false_eq_true, if_false, hrt1]
    have : 0 < 1 - recProb P σ false := by linarith
    have hx : P.p * (1 - 1) + (1 - P.p) * (1 - recProb P σ false) ≠ 0 := by
      have := mul_pos (sub_pos.2 hp1) this; apply ne_of_gt; linarith
    rw [div_eq_iff hx]; ring
  have hN_eq : hN = P.F P.sL := by rw [hhNdef, hsNR_eq]
  -- Step E: hR > F(sL)
  have hRgt : P.F P.sL < hR := by
    by_contra hc
    have heq : hR = P.F P.sL := le_antisymm (not_lt.mp hc) hRge
    have hLno : ∀ b ∈ Icc (0:ℝ) 1, σ.σA b false = false := by
      intro b hb
      by_contra hne
      rw [Bool.not_eq_false] at hne
      have h1 := brT b hb false hne
      have h2 := dL b
      rw [hN_eq, heq] at h2
      nlinarith [mul_pos hFsL hL]
    have hrf := rec_zero P hB0 σ false hLno
    have : σ.sR = P.sH := by
      rw [hsR_eq]; unfold bayesBelief msgProb sendProb
      simp only [if_true, hrf, hrt1]
      have hx : P.p * 1 + (1 - P.p) * 0 ≠ 0 := by apply ne_of_gt; linarith
      rw [div_eq_iff hx]; ring
    have : hR = P.F P.sH := by rw [hhRdef, this]
    have := hF hsLI hsHI hsLH
    linarith
  -- Step F: the threshold
  set t := hR * P.L r / (hR - P.F P.sL) with ht
  have hgap : 0 < hR - P.F P.sL := by linarith
  have hRpos : 0 < hR := by linarith
  have ht0 : 0 < t := div_pos (mul_pos hRpos hL) hgap
  have hiff : ∀ b ∈ Icc (0:ℝ) 1, (σ.σA b false = true ↔ t < b) := by
    intro b hb
    have h2 := dL b
    rw [hN_eq] at h2
    have key : t < b ↔ hR * P.L r < b * (hR - P.F P.sL) := by
      rw [ht, div_lt_iff₀ hgap]
    rw [key]
    constructor
    · intro h
      have h1 := brT b hb false h
      rcases lt_or_eq_of_le h1 with h3 | h3
      · linarith
      · have := htie b hb h3.symm
        rw [h] at this; exact absurd this (by decide)
    · intro h
      by_contra hne
      rw [Bool.not_eq_true] at hne
      have h1 := brF b hb false hne
      linarith
  set bstar := min t 1 with hbs
  have hbI : bstar ∈ Ioc (0:ℝ) 1 := ⟨lt_min ht0 zero_lt_one, min_le_right _ _⟩
  have hAf : ∀ b ∈ Icc (0:ℝ) 1, (σ.σA b false = true ↔ bstar < b) := by
    intro b hb
    rw [hiff b hb, hbs]
    constructor
    · intro h; exact lt_of_le_of_lt (min_le_left _ _) h
    · intro h
      rcases le_total t 1 with h1 | h1
      · rwa [min_eq_left h1] at h
      · rw [min_eq_right h1] at h; linarith [hb.2]
  -- Step G: the belief after `R`
  have hsRb : σ.sR = P.sRof bstar := by
    rw [hsR_eq]; exact hbayes4 σ bstar hbI (hmA true) (hmA false) hAt hAf
  have hlt1 : bstar < 1 → P.lieGain bstar = P.L r := by
    intro h
    have hbt : bstar = t := by
      rw [hbs] at h ⊢
      rcases le_total t 1 with h1 | h1
      · exact min_eq_left h1
      · rw [min_eq_right h1] at h; exact absurd h (lt_irrefl 1)
    unfold Primitives.lieGain
    rw [← hsRb, ← hhRdef, hbt, ht]
    field_simp
  refine ⟨bstar, hbI, hAt, hAf, hsNR_eq, ?_, hsRb, ?_, ?_, hlt1⟩
  · intro x hx; rw [← hsNR_eq]; exact (hfirm x hx).2
  · intro x hx; rw [← hsRb]; exact (hfirm x hx).1
  · constructor
    · intro h1
      have htge : 1 ≤ t := by
        rw [hbs] at h1
        by_contra hc; rw [not_le] at hc; rw [min_eq_left hc.le] at h1; linarith
      have hRH : hR = P.F P.sH := by rw [hhRdef, hsRb, h1, h41]
      rw [ht, le_div_iff₀ hgap] at htge
      unfold Primitives.Bbar
      rw [← hRH, div_le_iff₀ hRpos]
      linarith
    · intro hB
      by_contra hne
      have hb1 : bstar < 1 := lt_of_le_of_ne hbI.2 hne
      have := hlgM hbI ⟨zero_lt_one, le_rfl⟩ hb1
      rw [hlt1 hb1, hlg1] at this
      linarith

end RepLiesProp1Aux

namespace RepLiesProp1Aux

/-- Existence: the threshold profile is an equilibrium. -/
theorem exist (P : Primitives) (hP : P.Standing) (r : ℝ) (hr : 0 < r) :
    ∃ σ : Profile, IsEquilibrium P σ r := by
  obtain ⟨hbayes4, hmono4, -, h40, h41⟩ := step_4_bayes_belief P hP
  obtain ⟨hlgM, -, hlg1, hlgEx⟩ := step_5_threshold P hP
  obtain ⟨hΔH, hL⟩ := vfacts P hP r hr
  obtain ⟨hsL, hsLH, hsH1, hp0, hp1, -, -, -, -, -, -, -, hμB, hμB1, -, hZ, hμX, hμX1, -, hF, -⟩ :=
    hP
  have hex : ∃ bstar ∈ Ioc (0:ℝ) 1, (bstar < 1 → P.lieGain bstar = P.L r) ∧
      (bstar = 1 → P.Bbar ≤ P.L r) := by
    by_cases hB : P.Bbar ≤ P.L r
    · exact ⟨1, ⟨zero_lt_one, le_rfl⟩, fun h => absurd h (lt_irrefl 1), fun _ => hB⟩
    · obtain ⟨b, ⟨hb, hbv⟩, -⟩ := hlgEx (P.L r) hL (not_le.mp hB)
      exact ⟨b, ⟨hb.1, hb.2.le⟩, fun _ => hbv, fun h => absurd h hb.2.ne⟩
  obtain ⟨bstar, hbI, hlt1, heq1⟩ := hex
  have hX0 := compl_null P.μX hμX1
  have hshat : P.sL < P.shat := by unfold Primitives.shat; nlinarith
  have hsR1 : P.sRof 0 < P.sRof bstar := hmono4 ⟨le_rfl, zero_le_one⟩ ⟨hbI.1.le, hbI.2⟩ hbI.1
  have hsR2 : P.sRof bstar ≤ P.sRof 1 :=
    hmono4.monotoneOn ⟨hbI.1.le, hbI.2⟩ ⟨zero_le_one, le_rfl⟩ hbI.2
  rw [h40] at hsR1; rw [h41] at hsR2
  have hsLI : P.sL ∈ Icc (0:ℝ) 1 := ⟨hsL.le, by linarith⟩
  have hsRI : P.sRof bstar ∈ Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have hF0 : 0 ≤ P.F 0 := ENNReal.toReal_nonneg
  have hFsL : 0 < P.F P.sL := lt_of_le_of_lt hF0 (hF ⟨le_rfl, zero_le_one⟩ hsLI hsL)
  set hR := P.F (P.sRof bstar) with hhR
  have hRgt : P.F P.sL < hR := hF hsLI hsRI (by linarith)
  have hRpos : 0 < hR := by linarith
  -- (A) and (B)
  have hB_eq : bstar < 1 → bstar * (hR - P.F P.sL) = P.L r * hR := by
    intro h
    have := hlt1 h
    unfold Primitives.lieGain at this
    rw [← hhR] at this
    rw [← this]; field_simp
  have hA : bstar * (hR - P.F P.sL) ≤ P.L r * hR := by
    rcases lt_or_eq_of_le hbI.2 with h | h
    · exact (hB_eq h).le
    · have hBL := heq1 h
      have hRH : hR = P.F P.sH := by rw [hhR, h, h41]
      unfold Primitives.Bbar at hBL
      rw [← hRH, div_le_iff₀ hRpos] at hBL
      rw [h]; linarith
  let σ : Profile :=
    { σA := fun b hi => if bstar < b then true else hi
      σF := fun x m => if x ≤ (if m then P.sRof bstar else P.sL) then true else false
      sR := P.sRof bstar
      sNR := P.sL }
  have hAt : ∀ b ∈ Icc (0:ℝ) 1, σ.σA b true = true := by
    intro b _; simp [σ]
  have hAf : ∀ b ∈ Icc (0:ℝ) 1, (σ.σA b false = true ↔ bstar < b) := by
    intro b _; simp [σ]
  have hfirm : ∀ x ∈ Icc (0 : ℝ) 1,
      (σ.σF x true = true ↔ x ≤ σ.sR) ∧ (σ.σF x false = true ↔ x ≤ σ.sNR) := by
    intro x _; simp [σ]
  have hmA : ∀ hi, Measurable fun b => σ.σA b hi := by
    intro hi
    exact Measurable.ite (measurableSet_Ioi (a := bstar)) measurable_const measurable_const
  have hmF : ∀ m, Measurable fun x => σ.σF x m := by
    intro m
    exact Measurable.ite measurableSet_Iic measurable_const measurable_const
  have hhRp : hireProb P σ true = hR := by
    unfold hireProb
    rw [hire_eq P.μX hX0 (fun x => σ.σF x true) σ.sR (fun x hx => (hfirm x hx).1)]
    rfl
  have hhNp : hireProb P σ false = P.F P.sL := by
    unfold hireProb Primitives.F
    rw [hire_eq P.μX hX0 (fun x => σ.σF x false) σ.sNR (fun x hx => (hfirm x hx).2)]
  have dH : ∀ b, utility P σ r b true true - utility P σ r b true false =
      b * (hR - P.F P.sL) + hR * (P.v (r + P.g r) - P.v r) := by
    intro b; rw [udiff, hhRp, hhNp]; simp only [if_true]; ring
  have dL : ∀ b, utility P σ r b false true - utility P σ r b false false =
      b * (hR - P.F P.sL) - hR * P.L r := by
    intro b; rw [udiff, hhRp, hhNp]; simp only [Bool.false_eq_true, if_false]
    unfold Primitives.L; ring
  have lowpos : ∀ b ∈ Icc (0:ℝ) 1, bstar < b →
      utility P σ r b false false < utility P σ r b false true := by
    intro b hb h
    have h1 := hB_eq (lt_of_lt_of_le h hb.2)
    have h2 := dL b
    have := mul_lt_mul_of_pos_right h (by linarith : 0 < hR - P.F P.sL)
    linarith
  have hrt1 := rec_one P hμB1 σ true hAt
  refine ⟨σ, hmA, hmF, ?_, ?_, hfirm, ⟨by linarith, hsR2⟩, ⟨le_rfl, hsLH.le⟩, ?_, ?_⟩
  · intro b hb hi m
    cases hi
    · by_cases h : bstar < b
      · have hs : σ.σA b false = true := (hAf b hb).2 h
        rw [hs]
        cases m
        · exact (lowpos b hb h).le
        · exact le_rfl
      · have hs : σ.σA b false = false := by
          rw [← Bool.not_eq_true, hAf b hb]; exact h
        rw [hs]
        cases m
        · exact le_rfl
        · have h2 := dL b
          have : b * (hR - P.F P.sL) ≤ bstar * (hR - P.F P.sL) :=
            mul_le_mul_of_nonneg_right (not_lt.mp h) (by linarith)
          linarith
    · rw [hAt b hb]
      cases m
      · have h2 := dH b
        have := mul_nonneg hb.1 (by linarith : (0:ℝ) ≤ hR - P.F P.sL)
        have := mul_pos hRpos hΔH
        linarith
      · exact le_rfl
  · intro b hb heq
    by_contra hne
    rw [Bool.not_eq_false, hAf b hb] at hne
    have := lowpos b hb hne
    linarith
  · intro _
    exact (hbayes4 σ bstar hbI (hmA true) (hmA false) hAt hAf).symm
  · intro hmF'
    unfold bayesBelief msgProb sendProb at *
    simp only [Bool.false_eq_true, if_false, hrt1] at hmF' ⊢
    have hx : P.p * (1 - 1) + (1 - P.p) * (1 - recProb P σ false) ≠ 0 := ne_of_gt hmF'
    rw [eq_div_iff hx]; ring

end RepLiesProp1Aux

open RepLiesProp1Aux in
theorem solution (P : Primitives) (hP : P.Standing) (r : ℝ) (hr : 0 < r) :
    (∃ σ : Profile, IsEquilibrium P σ r) ∧
    (∀ σ σ' : Profile, IsEquilibrium P σ r → IsEquilibrium P σ' r →
      (∀ b ∈ Icc (0 : ℝ) 1, ∀ hi, σ.σA b hi = σ'.σA b hi) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, ∀ m, σ.σF x m = σ'.σF x m) ∧
      σ.sR = σ'.sR ∧ σ.sNR = σ'.sNR) ∧
    (∀ σ : Profile, IsEquilibrium P σ r → ∃ bstar ∈ Ioc (0 : ℝ) 1,
      (∀ b ∈ Icc (0 : ℝ) 1, σ.σA b true = true) ∧
      (∀ b ∈ Icc (0 : ℝ) 1, (σ.σA b false = true ↔ bstar < b)) ∧
      σ.sNR = P.sL ∧ (∀ x ∈ Icc (0 : ℝ) 1, (σ.σF x false = true ↔ x ≤ P.sL)) ∧
      σ.sR = P.sRof bstar ∧ (∀ x ∈ Icc (0 : ℝ) 1, (σ.σF x true = true ↔ x ≤ P.sRof bstar)) ∧
      (bstar = 1 ↔ P.Bbar ≤ P.L r) ∧ (bstar < 1 → P.lieGain bstar = P.L r)) := by
  refine ⟨exist P hP r hr, ?_, fun σ hσ => charac P hP r hr σ hσ⟩
  intro σ σ' hσ hσ'
  obtain ⟨hlgM, -, -, -⟩ := step_5_threshold P hP
  obtain ⟨b1, hb1, hAt1, hAf1, hN1, hFN1, hR1, hFR1, hi1, hl1⟩ := charac P hP r hr σ hσ
  obtain ⟨b2, hb2, hAt2, hAf2, hN2, hFN2, hR2, hFR2, hi2, hl2⟩ := charac P hP r hr σ' hσ'
  have hbb : b1 = b2 := by
    by_cases hB : P.Bbar ≤ P.L r
    · rw [hi1.2 hB, hi2.2 hB]
    · have h1 : b1 < 1 := lt_of_le_of_ne hb1.2 (fun h => hB (hi1.1 h))
      have h2 : b2 < 1 := lt_of_le_of_ne hb2.2 (fun h => hB (hi2.1 h))
      exact hlgM.injOn hb1 hb2 ((hl1 h1).trans (hl2 h2).symm)
  subst hbb
  refine ⟨?_, ?_, by rw [hR1, hR2], by rw [hN1, hN2]⟩
  · intro b hb hi
    cases hi
    · rw [Bool.eq_iff_iff, hAf1 b hb, hAf2 b hb]
    · rw [hAt1 b hb, hAt2 b hb]
  · intro x hx m
    cases m
    · rw [Bool.eq_iff_iff, hFN1 x hx, hFN2 x hx]
    · rw [Bool.eq_iff_iff, hFR1 x hx, hFR2 x hx]
