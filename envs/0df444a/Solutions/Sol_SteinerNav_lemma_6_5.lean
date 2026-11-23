-- Prove2me | solution 1 for SteinerNav.lemma_6_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:04:13.853843+00:00
-- url     : https://prove2.me/submissions/8d1eb92c-05e2-4277-9a71-5034a7be2dd1

import Mathlib
import Definitions.Def_SteinerNav_IsSteinerNavigable
import Definitions.Def_SteinerNav_GreedyRun

open SteinerNav

namespace AuxLemma65

lemma step_dist_bound {d : ℕ} {α : ℝ} (hα : 1 < α) {P R : Finset (Pt d)}
    {E : Finset (Pt d × Pt d)} (hG : IsSteinerNavigable α P R E)
    {q tstar x : Pt d} (hx : x ∈ P ∪ R) (htstar : tstar ∈ P) (hxt : x ≠ tstar) :
    ∃ v, (x, v) ∈ E ∧ dist v q ≤ (dist x q + dist q tstar) / α + dist q tstar := by
  obtain ⟨v, hvE, hcov⟩ := hG.2.2 x hx tstar htstar hxt.symm
  refine ⟨v, hvE, ?_⟩
  unfold Covers at hcov
  have hα_pos : 0 < α := by linarith
  have htri1 : dist v q ≤ dist v tstar + dist tstar q := dist_triangle v tstar q
  have htri2 : dist x tstar ≤ dist x q + dist q tstar := dist_triangle x q tstar
  have hdiv : dist x tstar / α ≤ (dist x q + dist q tstar) / α :=
    div_le_div_of_nonneg_right htri2 (le_of_lt hα_pos)
  rw [dist_comm tstar q] at htri1
  linarith

lemma localMin_bound {d : ℕ} {α : ℝ} (hα : 1 < α) {P R : Finset (Pt d)}
    {E : Finset (Pt d × Pt d)} (hG : IsSteinerNavigable α P R E)
    {q tstar x : Pt d} (hx : x ∈ P ∪ R) (htstar : tstar ∈ P)
    (hloc : GreedyLocalMin E q x) :
    dist x q ≤ (α + 1) / (α - 1) * dist q tstar := by
  have hαm1 : 0 < α - 1 := by linarith
  have hα_pos : 0 < α := by linarith
  by_cases hxt : x = tstar
  · subst hxt
    rw [dist_comm x q]
    have hr : 0 ≤ dist q x := dist_nonneg
    have h1 : 1 ≤ (α + 1) / (α - 1) := by
      rw [one_le_div hαm1]
      linarith
    nlinarith
  · obtain ⟨v, hvE, hvq⟩ := step_dist_bound hα hG hx htstar hxt
    have hxv : dist x q ≤ dist v q := hloc v hvE
    have hineq : dist x q ≤ (dist x q + dist q tstar) / α + dist q tstar := le_trans hxv hvq
    have hmul : α * dist x q ≤ α * ((dist x q + dist q tstar) / α + dist q tstar) :=
      mul_le_mul_of_nonneg_left hineq (le_of_lt hα_pos)
    have hsimp : α * ((dist x q + dist q tstar) / α + dist q tstar) =
        dist x q + (α + 1) * dist q tstar := by
      field_simp
      ring
    rw [hsimp] at hmul
    have hsub : dist x q * (α - 1) ≤ (α + 1) * dist q tstar := by linarith
    have hdiv : dist x q ≤ ((α + 1) * dist q tstar) / (α - 1) :=
      (le_div_iff₀ hαm1).mpr hsub
    calc dist x q ≤ ((α + 1) * dist q tstar) / (α - 1) := hdiv
      _ = (α + 1) / (α - 1) * dist q tstar := by ring

end AuxLemma65

theorem solution {d : ℕ} (α : ℝ) (hα : 1 < α) (P R : Finset (Pt d)) (E : Finset (Pt d × Pt d))
    (hn : 2 ≤ P.card) (hG : IsSteinerNavigable α P R E) (q tstar : Pt d) (htstar : tstar ∈ P)
    (hnear : ∀ p ∈ P, dist q tstar ≤ dist q p) :
    (∀ x ∈ P ∪ R, GreedyLocalMin E q x → dist x q ≤ (α + 1) / (α - 1) * dist q tstar) ∧
      (NoSteinerToSteiner R P E → ∀ x ∈ P ∪ R, GreedyLocalMin E q x →
        (∃ y, GreedyReturns E P q x y) ∧
          ∀ y, GreedyReturns E P q x y →
            y ∈ P ∧ dist y q ≤ (α + 1) / (α - 1) * dist q tstar) := by
  have _ := hn
  have _ := hnear
  constructor
  · intro x hx hloc
    exact AuxLemma65.localMin_bound hα hG hx htstar hloc
  · intro hN x hx hloc
    have hx_bound : dist x q ≤ (α + 1) / (α - 1) * dist q tstar :=
      AuxLemma65.localMin_bound hα hG hx htstar hloc
    by_cases hxP : x ∈ P
    · refine ⟨⟨x, Or.inl ⟨hxP, rfl⟩⟩, ?_⟩
      rintro y (⟨_, rfl⟩ | ⟨hnxP, _⟩)
      · exact ⟨hxP, hx_bound⟩
      · exact absurd hxP hnxP
    · have hxR : x ∈ R := by
        rcases Finset.mem_union.mp hx with hP | hR
        · exact absurd hP hxP
        · exact hR
      have hxt : x ≠ tstar := by
        intro heq
        subst heq
        exact hxP htstar
      obtain ⟨v, hvE, hvq⟩ := AuxLemma65.step_dist_bound hα hG hx htstar hxt
      let outN : Finset (Pt d) := (E.filter fun e => e.1 = x).image Prod.snd
      have hv_mem : v ∈ outN :=
        Finset.mem_image.mpr ⟨(x, v), Finset.mem_filter.mpr ⟨hvE, rfl⟩, rfl⟩
      obtain ⟨y₀, hy₀_mem, hy₀_min⟩ := outN.exists_min_image (fun z => dist z q) ⟨v, hv_mem⟩
      obtain ⟨⟨x', y'⟩, hxy_filt, rfl⟩ := Finset.mem_image.mp hy₀_mem
      obtain ⟨hxyE, rfl⟩ := Finset.mem_filter.mp hxy_filt
      dsimp only at hy₀_min ⊢
      have hret₀ : GreedyReturns E P q x' y' := by
        refine Or.inr ⟨hxP, hxyE, ?_⟩
        intro z hzE
        exact hy₀_min z (Finset.mem_image.mpr ⟨(x', z), Finset.mem_filter.mpr ⟨hzE, rfl⟩, rfl⟩)
      refine ⟨⟨y', hret₀⟩, ?_⟩
      rintro y (⟨hxP', _⟩ | ⟨_, hyE, hy_min⟩)
      · exact absurd hxP' hxP
      · refine ⟨hN x' y hyE hxR, ?_⟩
        have hyv : dist y q ≤ dist v q := hy_min v hvE
        have hα_pos : 0 < α := by linarith
        have hαm1_ne : α - 1 ≠ 0 := by linarith
        have hα_ne : α ≠ 0 := by linarith
        have hstep2 : (dist x' q + dist q tstar) / α + dist q tstar ≤
            ((α + 1) / (α - 1) * dist q tstar + dist q tstar) / α + dist q tstar := by
          gcongr
        have hid : ((α + 1) / (α - 1) * dist q tstar + dist q tstar) / α + dist q tstar =
            (α + 1) / (α - 1) * dist q tstar := by
          field_simp
          ring
        linarith
