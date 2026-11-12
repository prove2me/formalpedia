-- Prove2me | solution 1 for PGDMap20261031.entropy_alternation_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-31T14:10:31.035122+00:00
-- url     : https://prove2.me/submissions/ea5d3978-28ae-421e-94dd-6e3d9d44025b

import Mathlib.Tactic
import Definitions.Def_PGDMap20261031_Entropy
import Theorems.Thm_PGDMap20261031_entropy_error_lub

open PGDMap20261031

private lemma curvature_pos (c t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    0 < powerCurvature c t := by
  unfold powerCurvature
  exact div_pos (add_pos (Real.rpow_pos_of_pos (by linarith [ht.1]) _)
    (Real.rpow_pos_of_pos (by linarith [ht.2]) _)) (by norm_num)

private lemma error_order (M : EntropyMixture) (c p d q t : ℝ)
    (hp : 0 < p) (hq : 0 < q) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    curvatureError M c p t ≤ curvatureError M d q t ↔
      p * powerCurvature c t ≤ q * powerCurvature d t := by
  have htden : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have hB : 0 < entropyCurvature M t := div_pos M.lambda_pos htden
  have hA : 0 ≤ mixtureCurvature M t := by
    unfold mixtureCurvature
    apply Finset.sum_nonneg
    intro j _
    apply div_nonneg (mul_nonneg (M.weight_pos j).le (M.a_pos j).le)
    nlinarith [M.a_pos j, M.a_lt_one j]
  have hu : 0 < p * powerCurvature c t := mul_pos hp (curvature_pos c t ht)
  have hv : 0 < q * powerCurvature d t := mul_pos hq (curvature_pos d t ht)
  unfold curvatureError
  rw [div_le_div_iff₀ (add_pos hu hB) (add_pos hv hB)]
  constructor
  · intro h
    by_contra hn
    have hprod := mul_pos (sub_pos.mpr (lt_of_not_ge hn)) (add_pos_of_nonneg_of_pos hA hB)
    nlinarith only [h, hprod]
  · intro h
    have hprod := mul_nonneg (sub_nonneg.mpr h) (add_pos_of_nonneg_of_pos hA hB).le
    nlinarith only [hprod]

private lemma cut_upper (a b p q : ℝ) (hb : 0 < b) (hp : 0 < p)
    (h : p * a ≤ q * b) : a / b ≤ q / p := by
  apply (div_le_div_iff₀ hb hp).2
  nlinarith only [h]

private lemma cut_lower (a b p q : ℝ) (hb : 0 < b) (hp : 0 < p)
    (h : q * b ≤ p * a) : q / p ≤ a / b := by
  apply (div_le_div_iff₀ hp hb).2
  nlinarith only [h]

private lemma monotone_no_alternation (R : ℝ → ℝ)
    (hmono : StrictMonoOn R (Set.Ico (0 : ℝ) 1))
    (t₁ t₂ t₃ s : ℝ) (h₁ : t₁ ∈ Set.Ico (0 : ℝ) 1)
    (h₂ : t₂ ∈ Set.Ico (0 : ℝ) 1) (h₃ : t₃ ∈ Set.Ico (0 : ℝ) 1)
    (h₁₂ : t₁ < t₂) (h₂₃ : t₂ < t₃)
    (horders : (R t₁ ≤ s ∧ s ≤ R t₂ ∧ R t₃ ≤ s) ∨
      (s ≤ R t₁ ∧ R t₂ ≤ s ∧ s ≤ R t₃)) : False := by
  rcases horders with ⟨_, h₂s, h₃s⟩ | ⟨h₁s, h₂s, _⟩
  · linarith [hmono h₂ h₃ h₂₃]
  · linarith [hmono h₁ h₂ h₁₂]

private lemma contact_identifies_pair (hcross : PowerSingleCrossingClaim)
    (c p d q t₁ t₂ t₃ : ℝ) (hc : validGeometry (c, p)) (hd : validGeometry (d, q))
    (h₁ : t₁ ∈ Set.Ico (0 : ℝ) 1) (h₂ : t₂ ∈ Set.Ico (0 : ℝ) 1)
    (h₃ : t₃ ∈ Set.Ico (0 : ℝ) 1) (h₁₂ : t₁ < t₂) (h₂₃ : t₂ < t₃)
    (horders :
      (q * powerCurvature d t₁ ≤ p * powerCurvature c t₁ ∧
       p * powerCurvature c t₂ ≤ q * powerCurvature d t₂ ∧
       q * powerCurvature d t₃ ≤ p * powerCurvature c t₃) ∨
      (p * powerCurvature c t₁ ≤ q * powerCurvature d t₁ ∧
       q * powerCurvature d t₂ ≤ p * powerCurvature c t₂ ∧
       p * powerCurvature c t₃ ≤ q * powerCurvature d t₃)) : d = c ∧ q = p := by
  have heqc : d = c := by
    rcases lt_trichotomy d c with hlt | heq | hgt
    · exfalso
      apply monotone_no_alternation (fun t => powerCurvature c t / powerCurvature d t)
        (hcross d c hd.1 hlt hc.2.1) t₁ t₂ t₃ (q / p) h₁ h₂ h₃ h₁₂ h₂₃
      rcases horders with ⟨hA, hB, hC⟩ | ⟨hA, hB, hC⟩
      · exact Or.inr ⟨cut_lower _ _ _ _ (curvature_pos d t₁ h₁) hc.2.2 hA,
          cut_upper _ _ _ _ (curvature_pos d t₂ h₂) hc.2.2 hB,
          cut_lower _ _ _ _ (curvature_pos d t₃ h₃) hc.2.2 hC⟩
      · exact Or.inl ⟨cut_upper _ _ _ _ (curvature_pos d t₁ h₁) hc.2.2 hA,
          cut_lower _ _ _ _ (curvature_pos d t₂ h₂) hc.2.2 hB,
          cut_upper _ _ _ _ (curvature_pos d t₃ h₃) hc.2.2 hC⟩
    · exact heq
    · exfalso
      apply monotone_no_alternation (fun t => powerCurvature d t / powerCurvature c t)
        (hcross c d hc.1 hgt hd.2.1) t₁ t₂ t₃ (p / q) h₁ h₂ h₃ h₁₂ h₂₃
      rcases horders with ⟨hA, hB, hC⟩ | ⟨hA, hB, hC⟩
      · exact Or.inl ⟨cut_upper _ _ _ _ (curvature_pos c t₁ h₁) hd.2.2 hA,
          cut_lower _ _ _ _ (curvature_pos c t₂ h₂) hd.2.2 hB,
          cut_upper _ _ _ _ (curvature_pos c t₃ h₃) hd.2.2 hC⟩
      · exact Or.inr ⟨cut_lower _ _ _ _ (curvature_pos c t₁ h₁) hd.2.2 hA,
          cut_upper _ _ _ _ (curvature_pos c t₂ h₂) hd.2.2 hB,
          cut_lower _ _ _ _ (curvature_pos c t₃ h₃) hd.2.2 hC⟩
  refine ⟨heqc, ?_⟩
  subst d
  rcases horders with ⟨hA, hB, _⟩ | ⟨hA, hB, _⟩
  · exact le_antisymm
      ((mul_le_mul_iff_of_pos_right (curvature_pos c t₁ h₁)).mp hA)
      ((mul_le_mul_iff_of_pos_right (curvature_pos c t₂ h₂)).mp hB)
  · exact le_antisymm
      ((mul_le_mul_iff_of_pos_right (curvature_pos c t₂ h₂)).mp hB)
      ((mul_le_mul_iff_of_pos_right (curvature_pos c t₁ h₁)).mp hA)

theorem solution : PowerSingleCrossingClaim → AlternationCertificateClaim := by
  intro hcross M c p r hc hr hbound halt
  obtain ⟨t₁, t₂, t₃, σ, ht₁, h₁₂, h₂₃, ht₃, hσ, he₁, he₂, he₃⟩ := halt
  have h₁ : t₁ ∈ Set.Ico (0 : ℝ) 1 := ⟨ht₁, lt_trans h₁₂ (lt_trans h₂₃ ht₃)⟩
  have h₂ : t₂ ∈ Set.Ico (0 : ℝ) 1 := ⟨(lt_of_le_of_lt ht₁ h₁₂).le, lt_trans h₂₃ ht₃⟩
  have h₃ : t₃ ∈ Set.Ico (0 : ℝ) 1 := ⟨(lt_of_le_of_lt h₂.1 h₂₃).le, ht₃⟩
  have hrho : contraction M c p = r := by
    apply le_antisymm
    · apply (entropy_error_lub M c p hc).2
      rintro v ⟨t, ht, rfl⟩
      exact hbound t ht
    · have hmem : |curvatureError M c p t₁| ≤ contraction M c p :=
        (entropy_error_lub M c p hc).1 ⟨t₁, h₁, rfl⟩
      rcases hσ with hσ | hσ
      · simpa [he₁, hσ, abs_of_pos hr] using hmem
      · simpa [he₁, hσ, abs_of_pos hr] using hmem
  have identify (u : ℝ × ℝ) (hu : validGeometry u) (hvalue : contraction M u.1 u.2 ≤ r) :
      u = (c, p) := by
    have hub (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
        -r ≤ curvatureError M u.1 u.2 t ∧ curvatureError M u.1 u.2 t ≤ r := by
      apply abs_le.mp
      exact le_trans ((entropy_error_lub M u.1 u.2 hu).1 ⟨t, ht, rfl⟩) hvalue
    have hu₁ := hub t₁ h₁
    have hu₂ := hub t₂ h₂
    have hu₃ := hub t₃ h₃
    have horders :
      (u.2 * powerCurvature u.1 t₁ ≤ p * powerCurvature c t₁ ∧
       p * powerCurvature c t₂ ≤ u.2 * powerCurvature u.1 t₂ ∧
       u.2 * powerCurvature u.1 t₃ ≤ p * powerCurvature c t₃) ∨
      (p * powerCurvature c t₁ ≤ u.2 * powerCurvature u.1 t₁ ∧
       u.2 * powerCurvature u.1 t₂ ≤ p * powerCurvature c t₂ ∧
       p * powerCurvature c t₃ ≤ u.2 * powerCurvature u.1 t₃) := by
      rcases hσ with hσ | hσ
      · left
        refine ⟨(error_order M _ _ _ _ _ hu.2.2 hc.2.2 h₁).mp ?_,
          (error_order M _ _ _ _ _ hc.2.2 hu.2.2 h₂).mp ?_,
          (error_order M _ _ _ _ _ hu.2.2 hc.2.2 h₃).mp ?_⟩ <;>
          nlinarith [he₁, he₂, he₃, hu₁.1, hu₁.2, hu₂.1, hu₂.2, hu₃.1, hu₃.2]
      · right
        refine ⟨(error_order M _ _ _ _ _ hc.2.2 hu.2.2 h₁).mp ?_,
          (error_order M _ _ _ _ _ hu.2.2 hc.2.2 h₂).mp ?_,
          (error_order M _ _ _ _ _ hc.2.2 hu.2.2 h₃).mp ?_⟩ <;>
          nlinarith [he₁, he₂, he₃, hu₁.1, hu₁.2, hu₂.1, hu₂.2, hu₃.1, hu₃.2]
    obtain ⟨huc, hup⟩ := contact_identifies_pair hcross c p u.1 u.2 t₁ t₂ t₃
      hc hu h₁ h₂ h₃ h₁₂ h₂₃ horders
    exact Prod.ext huc hup
  have hopt : IsGeometryOptimum M (c, p) := by
    refine ⟨hc, ?_⟩
    intro u hu
    rw [hrho]
    by_contra hn
    have hlt : contraction M u.1 u.2 < r := lt_of_not_ge hn
    have heq := identify u hu hlt.le
    subst u
    exact (not_lt_of_ge hrho.ge) hlt
  refine ⟨hopt, hrho, ?_⟩
  intro u hu
  apply identify u hu.1
  simpa only [hrho] using hu.2 (c, p) hc
