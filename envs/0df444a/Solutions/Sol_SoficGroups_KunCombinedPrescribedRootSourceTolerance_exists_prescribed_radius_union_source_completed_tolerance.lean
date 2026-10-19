-- Prove2me | solution 1 for SoficGroups.KunCombinedPrescribedRootSourceTolerance.exists_prescribed_radius_union_source_completed_tolerance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/e19cb05c-a269-47b9-bda5-98b9623854b7

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_exists_diverging_radius_with_vanishing_diagonal_error
import Theorems.Thm_SoficGroups_KunRootedWordPower_RootedIndicatorMarkovModel_IsRootedAtRadius_mono
import Theorems.Thm_SoficGroups_KunCombinedPrescribedRootSourceTolerance_eventually_scaled_tolerance_lt

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunCombinedPrescribedRootSourceTolerance
open Filter Topology
namespace SoficGroups.KunCombinedPrescribedRootSourceTolerance
theorem _root_.solution
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (hVpositive : ∀ n, 0 < Fintype.card (V n))
    (hV : Tendsto (fun n => Fintype.card (V n)) atTop atTop)
    (root : (n : ℕ) → ℕ → Finset (V n))
    (source : (n : ℕ) → Finset (V n))
    (hroot : ∀ r : ℕ,
      Tendsto
        (fun n => ((root n r).card : ℝ) / Fintype.card (V n))
        atTop (𝓝 0))
    (hsource : Tendsto
      (fun n => ((source n).card : ℝ) / Fintype.card (V n))
      atTop (𝓝 0))
    (δ : ℕ → ℝ)
    (hδpositive : ∀ j, 0 < δ j)
    (hδ : Tendsto δ atTop (𝓝 0))
    (R : ℕ → ℕ) (hR : ∀ j, j ≤ R j)
    (d : ℕ) (hd : 0 < d)
    (ell q : ℝ) (hell : 0 < ell) (hq : q < 1) :
    ∃ m rootError t : ℕ → ℕ,
      Tendsto m atTop atTop ∧
      Tendsto (fun n => R (m n)) atTop atTop ∧
      Tendsto (fun n => δ (m n)) atTop (𝓝 0) ∧
      Tendsto
        (fun n =>
          (((root n (R (m n)) ∪ source n).card : ℝ) /
            (δ (m n) * (Fintype.card (V n) : ℝ))))
        atTop (𝓝 0) ∧
      (∀ n,
        rootError n =
          Nat.ceil (δ (m n) * (Fintype.card (V n) : ℝ))) ∧
      (∀ n,
        δ (m n) ≤
          (rootError n : ℝ) / (Fintype.card (V n) : ℝ)) ∧
      Tendsto
        (fun n =>
          (rootError n : ℝ) / (Fintype.card (V n) : ℝ))
        atTop (𝓝 0) ∧
      (∀ n,
        t n =
          2 * d * (root n (R (m n)) ∪ source n).card +
            rootError n + 1) ∧
      (∀ n, 0 < t n) ∧
      (∀ n,
        2 * d * (root n (R (m n))).card ≤ t n) ∧
      (∀ n,
        2 * d * (source n).card ≤ t n) ∧
      (∀ n, rootError n ≤ t n) ∧
      Tendsto
        (fun n =>
          (t n : ℝ) / (Fintype.card (V n) : ℝ))
        atTop (𝓝 0) ∧
      (∀ n,
        ell * δ (m n) / (2 * (ell + 8 * (d : ℝ))) ≤
          ell * (t n : ℝ) /
            (2 * (ell + 8 * (d : ℝ)) *
              (Fintype.card (V n) : ℝ))) ∧
      (∀ᶠ n in atTop,
        (10 : ℝ) * (t n : ℝ) <
          ell * (Fintype.card (V n) : ℝ)) ∧
      (∀ᶠ n in atTop,
        (5 : ℝ) *
            (4 + ell *
              (216 / ((d : ℝ) * (1 - q) ^ 2) +
                1 / (d : ℝ))) * (t n : ℝ) ≤
          ell * (Fintype.card (V n) : ℝ)) := by
  classical
  let N : ℕ → ℕ := fun n => Fintype.card (V n)
  let B : (n : ℕ) → ℕ → Finset (V n) :=
    fun n j => root n (R j) ∪ source n
  have hNpositive (n : ℕ) : (0 : ℝ) < N n := by
    exact_mod_cast hVpositive n
  have hunion (j : ℕ) :
      Tendsto
        (fun n => ((B n j).card : ℝ) / (N n : ℝ))
        atTop (𝓝 0) := by
    have hsum : Tendsto
        (fun n =>
          ((root n (R j)).card : ℝ) / Fintype.card (V n) +
            ((source n).card : ℝ) / Fintype.card (V n))
        atTop (𝓝 0) := by
      simpa only [zero_add] using (hroot (R j)).add hsource
    refine squeeze_zero (fun n => by positivity) ?_ hsum
    intro n
    have hcard :
        ((B n j).card : ℝ) ≤
          ((root n (R j)).card : ℝ) +
            ((source n).card : ℝ) := by
      exact_mod_cast Finset.card_union_le (root n (R j)) (source n)
    calc
      ((B n j).card : ℝ) / (N n : ℝ) ≤
          (((root n (R j)).card : ℝ) +
            ((source n).card : ℝ)) / (N n : ℝ) :=
        div_le_div_of_nonneg_right hcard (hNpositive n).le
      _ = ((root n (R j)).card : ℝ) / Fintype.card (V n) +
            ((source n).card : ℝ) / Fintype.card (V n) := by
        dsimp [N]
        ring
  let e : ℕ → ℕ → ℝ := fun n j =>
    (((B n j).card : ℝ) / (N n : ℝ)) / δ j
  have hepositive (n j : ℕ) : 0 ≤ e n j := by
    dsimp [e]
    exact div_nonneg
      (div_nonneg (Nat.cast_nonneg _) (hNpositive n).le)
      (hδpositive j).le
  have hevanishes (j : ℕ) :
      Tendsto (fun n => e n j) atTop (𝓝 0) := by
    simpa [e] using (hunion j).div_const (δ j)
  obtain ⟨m, hm, herror⟩ :=
    SoficGroups.exists_diverging_radius_with_vanishing_diagonal_error
      e hepositive hevanishes
  have hδm : Tendsto (fun n => δ (m n)) atTop (𝓝 0) :=
    hδ.comp hm
  have hRm : Tendsto (fun n => R (m n)) atTop atTop :=
    tendsto_atTop_mono (fun n => hR (m n)) hm
  have hrelative : Tendsto
      (fun n =>
        ((B n (m n)).card : ℝ) /
          (δ (m n) * (N n : ℝ)))
      atTop (𝓝 0) := by
    convert herror using 1
    funext n
    dsimp [e]
    ring
  have hbadselected : Tendsto
      (fun n => ((B n (m n)).card : ℝ) / (N n : ℝ))
      atTop (𝓝 0) := by
    have hp := hrelative.mul hδm
    convert hp using 1
    · funext n
      have hne : δ (m n) ≠ 0 := (hδpositive (m n)).ne'
      field_simp
    · norm_num
  have honeover : Tendsto
      (fun n => (1 : ℝ) / (N n : ℝ))
      atTop (𝓝 0) :=
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hV
  let rootError : ℕ → ℕ :=
    fun n => Nat.ceil (δ (m n) * (N n : ℝ))
  have hrootlower (n : ℕ) :
      δ (m n) ≤ (rootError n : ℝ) / (N n : ℝ) := by
    apply (le_div_iff₀ (hNpositive n)).2
    exact Nat.le_ceil _
  have hrootupper (n : ℕ) :
      (rootError n : ℝ) / (N n : ℝ) ≤
        δ (m n) + 1 / (N n : ℝ) := by
    apply (div_le_iff₀ (hNpositive n)).2
    have hceil :=
      (Nat.ceil_lt_add_one
        (mul_nonneg (hδpositive (m n)).le
          (hNpositive n).le)).le
    have hone : (1 / (N n : ℝ)) * (N n : ℝ) = 1 := by
      field_simp [ne_of_gt (hNpositive n)]
    change (rootError n : ℝ) ≤ _
    dsimp [rootError] at hceil ⊢
    nlinarith
  have hrootlimit : Tendsto
      (fun n => (rootError n : ℝ) / (N n : ℝ))
      atTop (𝓝 0) := by
    have hupper : Tendsto
        (fun n => δ (m n) + 1 / (N n : ℝ))
        atTop (𝓝 0) := by
      simpa using hδm.add honeover
    exact squeeze_zero (fun n => by positivity) hrootupper hupper
  let t : ℕ → ℕ :=
    fun n => 2 * d * (B n (m n)).card + rootError n + 1
  have htpositive (n : ℕ) : 0 < t n := by
    dsimp [t]
    omega
  have hrootbudget (n : ℕ) :
      2 * d * (root n (R (m n))).card ≤ t n := by
    have hsub :
        root n (R (m n)) ⊆ B n (m n) := by
      dsimp [B]
      exact Finset.subset_union_left
    have hcard := Finset.card_le_card hsub
    have hmul :
        2 * d * (root n (R (m n))).card ≤
          2 * d * (B n (m n)).card :=
      Nat.mul_le_mul_left (2 * d) hcard
    dsimp [t]
    omega
  have hsourcebudget (n : ℕ) :
      2 * d * (source n).card ≤ t n := by
    have hsub : source n ⊆ B n (m n) := by
      dsimp [B]
      exact Finset.subset_union_right
    have hcard := Finset.card_le_card hsub
    have hmul :
        2 * d * (source n).card ≤
          2 * d * (B n (m n)).card :=
      Nat.mul_le_mul_left (2 * d) hcard
    dsimp [t]
    omega
  have hrooterrorbudget (n : ℕ) : rootError n ≤ t n := by
    dsimp [t]
    omega
  have htzero : Tendsto
      (fun n => (t n : ℝ) / (N n : ℝ))
      atTop (𝓝 0) := by
    have hscaled : Tendsto
        (fun n =>
          ((2 * d : ℕ) : ℝ) *
            (((B n (m n)).card : ℝ) / (N n : ℝ)))
        atTop (𝓝 0) := by
      simpa using hbadselected.const_mul ((2 * d : ℕ) : ℝ)
    have hsum := (hscaled.add hrootlimit).add honeover
    convert hsum using 1
    · funext n
      dsimp [t]
      push_cast
      ring
    · norm_num
  have hdreal : (0 : ℝ) < d := by
    exact_mod_cast hd
  have hden : 0 < (2 : ℝ) * (ell + 8 * (d : ℝ)) := by
    positivity
  have htarget (n : ℕ) :
      ell * δ (m n) / (2 * (ell + 8 * (d : ℝ))) ≤
        ell * (t n : ℝ) /
          (2 * (ell + 8 * (d : ℝ)) * (N n : ℝ)) := by
    have hratio : δ (m n) ≤ (t n : ℝ) / (N n : ℝ) := by
      calc
        δ (m n) ≤ (rootError n : ℝ) / (N n : ℝ) :=
          hrootlower n
        _ ≤ (t n : ℝ) / (N n : ℝ) := by
          apply div_le_div_of_nonneg_right
            (by exact_mod_cast hrooterrorbudget n)
            (hNpositive n).le
    calc
      ell * δ (m n) / (2 * (ell + 8 * (d : ℝ))) ≤
          ell * ((t n : ℝ) / (N n : ℝ)) /
            (2 * (ell + 8 * (d : ℝ))) := by
        apply div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hratio hell.le) hden.le
      _ = ell * (t n : ℝ) /
            (2 * (ell + 8 * (d : ℝ)) * (N n : ℝ)) := by
        field_simp [ne_of_gt (hNpositive n), ne_of_gt hden]
  have hten :
      ∀ᶠ n in atTop,
        (10 : ℝ) * (t n : ℝ) < ell * (N n : ℝ) :=
    eventually_scaled_tolerance_lt
      N t (fun n => hVpositive n) htzero
      10 ell (by norm_num) hell
  let c : ℝ :=
    5 * (4 + ell *
      (216 / ((d : ℝ) * (1 - q) ^ 2) + 1 / (d : ℝ)))
  have hdiff : 0 < 1 - q := sub_pos.mpr hq
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hspectral :
      ∀ᶠ n in atTop,
        c * (t n : ℝ) ≤ ell * (N n : ℝ) :=
    (eventually_scaled_tolerance_lt
      N t (fun n => hVpositive n) htzero c ell hc hell).mono
      fun _ h => h.le
  refine ⟨m, rootError, t, hm, hRm, hδm,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [B, N] using hrelative
  · intro n
    rfl
  · simpa only [N] using hrootlower
  · simpa only [N] using hrootlimit
  · intro n
    rfl
  · exact htpositive
  · exact hrootbudget
  · exact hsourcebudget
  · exact hrooterrorbudget
  · simpa only [N] using htzero
  · simpa only [N] using htarget
  · simpa only [N] using hten
  · simpa only [N, c] using hspectral
end SoficGroups.KunCombinedPrescribedRootSourceTolerance
