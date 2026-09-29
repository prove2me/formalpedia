-- Prove2me | solution 1 for Rudin.integrals_stable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T00:43:28.053872+00:00
-- url     : https://prove2.me/submissions/deba03ff-77ee-43fc-8901-e4ca0f4b7683

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes
import Theorems.Thm_Rudin_sSup_image_stable
import Theorems.Thm_Rudin_sInf_image_stable
import Theorems.Thm_Rudin_exists_partition
import Theorems.Thm_Rudin_upperSum_stable
import Theorems.Thm_Rudin_lowerSum_stable

open Rudin

theorem solution {a b : ℝ} (hab : a ≤ b) (α f g : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b)) {ε : ℝ} (hε : 0 ≤ ε)
    (hfg : ∀ x ∈ Set.Icc a b, |f x - g x| ≤ ε) :
    |upperIntegral a b f α - upperIntegral a b g α| ≤
        ε * (α b - α a) ∧
      |lowerIntegral a b f α - lowerIntegral a b g α| ≤
        ε * (α b - α a) := by
  have hspan : 0 ≤ α b - α a := by
    exact sub_nonneg.mpr (hα ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)
  let C : ℝ := ε * (α b - α a)
  have hC : 0 ≤ C := mul_nonneg hε hspan
  obtain ⟨P₀⟩ := Rudin.exists_partition hab
  constructor
  · have hstable : ∀ P : Partition a b,
        |upperSum f α P - upperSum g α P| ≤ C := by
      intro P
      exact Rudin.upperSum_stable hab α f g hα hε hfg P
    have h := Rudin.sInf_image_stable (Set.univ : Set (Partition a b))
      (show (Set.univ : Set (Partition a b)).Nonempty from
        ⟨P₀, Set.mem_univ _⟩)
      (fun P => upperSum f α P) (fun P => upperSum g α P) hC
      (fun P _ => hstable P)
    have hfset : (upperSum f α '' (Set.univ : Set (Partition a b))) =
        {y : ℝ | ∃ P : Partition a b, y = upperSum f α P} := by
      ext y
      simp [eq_comm]
    have hgset : (upperSum g α '' (Set.univ : Set (Partition a b))) =
        {y : ℝ | ∃ P : Partition a b, y = upperSum g α P} := by
      ext y
      simp [eq_comm]
    simpa only [upperIntegral, hfset, hgset, C] using h
  · have hstable : ∀ P : Partition a b,
        |lowerSum f α P - lowerSum g α P| ≤ C := by
      intro P
      exact Rudin.lowerSum_stable hab α f g hα hε hfg P
    have h := Rudin.sSup_image_stable (Set.univ : Set (Partition a b))
      (show (Set.univ : Set (Partition a b)).Nonempty from
        ⟨P₀, Set.mem_univ _⟩)
      (fun P => lowerSum f α P) (fun P => lowerSum g α P) hC
      (fun P _ => hstable P)
    have hfset : (lowerSum f α '' (Set.univ : Set (Partition a b))) =
        {y : ℝ | ∃ P : Partition a b, y = lowerSum f α P} := by
      ext y
      simp [eq_comm]
    have hgset : (lowerSum g α '' (Set.univ : Set (Partition a b))) =
        {y : ℝ | ∃ P : Partition a b, y = lowerSum g α P} := by
      ext y
      simp [eq_comm]
    simpa only [lowerIntegral, hfset, hgset, C] using h
