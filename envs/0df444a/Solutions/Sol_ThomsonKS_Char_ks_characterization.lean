-- Prove2me | solution 1 for ThomsonKS.Char.ks_characterization
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T12:28:16.594115+00:00
-- url     : https://prove2.me/submissions/643379ad-ca96-4e37-8ddb-dd5833709078

import Mathlib
import Definitions.Def_ThomsonKS_Char_Setting
import Theorems.Thm_ThomsonKS_Char_theorem_1
import Theorems.Thm_ThomsonKS_Char_theorem_3

open ThomsonKS.Char Filter Topology

lemma ks_goal_scale_mem {P : Finset ℕ} {S : Set (P → ℝ)} (hS : S ∈ DivProb P)
    {c : P → ℝ} (hc : ∀ i, 0 < c i) : scale c '' S ∈ DivProb P := by
  obtain ⟨hP, hnn, hcpt, hcvx, ⟨x0, hx0, hx0p⟩, hcomp⟩ := hS
  have hlin : IsLinearMap ℝ (scale c) :=
    ⟨fun x y => by funext i; simp [scale]; ring, fun r x => by funext i; simp [scale]; ring⟩
  have hcont : Continuous (scale c) :=
    continuous_pi fun i => continuous_const.mul (continuous_apply i)
  refine ⟨hP, ?_, hcpt.image hcont, hcvx.is_linear_image hlin, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ i
    exact mul_nonneg (hc i).le (hnn x hx i)
  · exact ⟨scale c x0, ⟨x0, hx0, rfl⟩, fun i => mul_pos (hc i) (hx0p i)⟩
  · rintro _ ⟨x, hx, rfl⟩ y hy hyx
    refine ⟨fun i => y i / c i, hcomp x hx _ ?_ ?_, ?_⟩
    · intro i; exact div_nonneg (hy i) (hc i).le
    · intro i
      have := hyx i
      simp only [scale] at this
      rw [div_le_iff₀ (hc i)]; linarith
    · funext i; simp [scale]; field_simp [(hc i).ne']

theorem solution (F : Solution) (hF : IsSolution F) :
    (WPO F ∧ An F ∧ SInv F ∧ Cont F ∧ Mon F) ↔
      ∀ P : Finset ℕ, ∀ S ∈ DivProb P, F P S = KS P S := by
  constructor
  · rintro ⟨hW, hA, hI, hC, hM⟩
    exact theorem_3 F hF hW hA hI hC hM
  · intro h
    obtain ⟨_, W1, A1, I1, C1, M1⟩ := theorem_1
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro P S hS y hy hlt
      rw [h P S hS] at hlt
      exact W1 P S hS y hy hlt
    · intro P P' γ S hS S' hS' hrel i
      rw [h P' S' hS', h P S hS]
      exact A1 P P' γ S hS S' hS' hrel i
    · intro P S hS c hc
      rw [h P _ (ks_goal_scale_mem hS hc), h P S hS]
      exact I1 P S hS c hc
    · intro P Sk S hS hSk ht
      have e : (fun k => F P (Sk k)) = fun k => KS P (Sk k) := funext fun k => h P (Sk k) (hSk k)
      rw [e, h P S hS]
      exact C1 P Sk S hS hSk ht
    · intro P Q hPQ S hS T hT hsl i
      rw [h Q T hT, h P S hS]
      exact M1 P Q hPQ S hS T hT hsl i
