-- Prove2me | solution 1 for PlatformPrecommit.Commission.lemma_F_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:14:23.136586+00:00
-- url     : https://prove2.me/submissions/3df2fbb8-c96a-464f-bc8c-2bc351895576

import Mathlib
import Definitions.Def_PlatformPrecommit_Commission_Setting

set_option autoImplicit false
open PlatformPrecommit.Commission

theorem solution (M : Model) (hM : M.Standing)
    (α p : Fin 2 → ℝ) (hα : AdmissibleAlpha α)
    (hp : IsCSubNE M α p) (hpos : ∀ i, 0 < profC M α p i) :
    ∀ i, demand M p i = supply M (wageC α p) i := by
  obtain ⟨hΩ, hβ0, hβ1, hγ0, hγ1⟩ := hM
  intro i
  have hr : rival i ≠ i := by
    unfold rival
    split_ifs with h
    · subst h; decide
    · exact fun e => h e.symm
  -- positivity of prices and matching of every firm
  have hpp : ∀ k, 0 < p k ∧ 0 < matchC M α p k := by
    intro k
    have h := hpos k
    unfold profC at h
    have hm : 0 ≤ matchC M α p k := le_min (le_max_right _ _) (le_max_right _ _)
    have hk : 0 < 1 - α k := by linarith [(hα k).2]
    constructor
    · by_contra hn
      push_neg at hn
      have h1 : (1 - α k) * p k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk.le hn
      have h2 : (1 - α k) * p k * matchC M α p k ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1 hm
      linarith
    · by_contra hn
      push_neg at hn
      have h0 : matchC M α p k = 0 := le_antisymm hn hm
      rw [h0, mul_zero] at h
      exact lt_irrefl _ h
  have hdev : ∀ a, profC M α (Function.update p i a) i =
      (1 - α i) * a * min (max (M.Ω - a + M.γ * p (rival i)) 0)
        (max (α i * a - M.β * (α (rival i) * p (rival i))) 0) := by
    intro a
    have e1 : Function.update p i a i = a := by simp
    have e2 : Function.update p i a (rival i) = p (rival i) := by simp [hr]
    simp only [profC, matchC, demand, supply, wageC, e1, e2]
  have hbase : profC M α p i =
      (1 - α i) * p i * min (max (M.Ω - p i + M.γ * p (rival i)) 0)
        (max (α i * p i - M.β * (α (rival i) * p (rival i))) 0) := by
    simp only [profC, matchC, demand, supply, wageC]
  have hdemand : demand M p i = max (M.Ω - p i + M.γ * p (rival i)) 0 := rfl
  have hsupply : supply M (wageC α p) i =
      max (α i * p i - M.β * (α (rival i) * p (rival i))) 0 := rfl
  have hNE : ∀ a, (1 - α i) * a * min (max (M.Ω - a + M.γ * p (rival i)) 0)
        (max (α i * a - M.β * (α (rival i) * p (rival i))) 0)
      ≤ (1 - α i) * p i * min (max (M.Ω - p i + M.γ * p (rival i)) 0)
        (max (α i * p i - M.β * (α (rival i) * p (rival i))) 0) := by
    intro a
    rw [← hdev a, ← hbase]
    exact hp.2 i a trivial
  obtain ⟨hpi, hmi⟩ := hpp i
  obtain ⟨hpj, -⟩ := hpp (rival i)
  have hmi' : 0 < min (max (M.Ω - p i + M.γ * p (rival i)) 0)
      (max (α i * p i - M.β * (α (rival i) * p (rival i))) 0) := hmi
  rw [lt_min_iff] at hmi'
  obtain ⟨hD, hS⟩ := hmi'
  have hx1 : 0 < M.Ω - p i + M.γ * p (rival i) := by
    rcases lt_max_iff.mp hD with h | h
    · exact h
    · exact absurd h (lt_irrefl _)
  have hx2 : 0 < α i * p i - M.β * (α (rival i) * p (rival i)) := by
    rcases lt_max_iff.mp hS with h | h
    · exact h
    · exact absurd h (lt_irrefl _)
  rw [hdemand, hsupply, max_eq_left hx1.le, max_eq_left hx2.le]
  have hαi := hα i
  have hαj := hα (rival i)
  have hbp : 0 ≤ M.β * (α (rival i) * p (rival i)) :=
    mul_nonneg hβ0 (mul_nonneg hαj.1.le hpj.le)
  have hx2p : α i * p i - M.β * (α (rival i) * p (rival i)) < p i := by
    have := mul_pos (sub_pos.2 hαi.2) hpi
    linarith
  have hk : 0 < 1 - α i := by linarith [hαi.2]
  have hne1 : 1 + α i ≠ 0 := by linarith [hαi.1]
  have hα0 : 0 < α i := hαi.1
  set x1 := M.Ω - p i + M.γ * p (rival i) with hx1def
  set x2 := α i * p i - M.β * (α (rival i) * p (rival i)) with hx2def
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- x1 < x2 : demand binds, lower the price
    obtain ⟨ε, hεdef, hεpos⟩ : ∃ ε : ℝ, ε * (2 * (1 + α i)) = x2 - x1 ∧ 0 < ε :=
      ⟨(x2 - x1) / (2 * (1 + α i)), by field_simp,
        div_pos (by linarith) (by linarith)⟩
    have hεα : 0 < ε * α i := mul_pos hεpos hα0
    have hεsmall : ε < x2 - x1 := by linarith
    have h1 : M.Ω - (p i - ε) + M.γ * p (rival i) = x1 + ε := by rw [hx1def]; ring
    have h2 : α i * (p i - ε) - M.β * (α (rival i) * p (rival i)) = x2 - α i * ε := by
      rw [hx2def]; ring
    have hpos1 : 0 < x1 + ε := by linarith
    have hpos2 : x1 + ε < x2 - α i * ε := by linarith
    have hmax1 : max (M.Ω - (p i - ε) + M.γ * p (rival i)) 0 = x1 + ε := by
      rw [h1]; exact max_eq_left hpos1.le
    have hmax2 : max (α i * (p i - ε) - M.β * (α (rival i) * p (rival i))) 0 = x2 - α i * ε := by
      rw [h2]; exact max_eq_left (by linarith)
    have hmin : min (x1 + ε) (x2 - α i * ε) = x1 + ε := min_eq_left hpos2.le
    have hb : min (max x1 0) (max x2 0) = x1 := by
      rw [max_eq_left hx1.le, max_eq_left hx2.le]; exact min_eq_left hlt.le
    have hnash := hNE (p i - ε)
    rw [hmax1, hmax2, hmin, hb] at hnash
    have h3 : 0 < p i - x1 - ε := by linarith
    have h4 := mul_pos hεpos h3
    have key : p i * x1 < (p i - ε) * (x1 + ε) := by linarith
    have h5 := mul_lt_mul_of_pos_left key hk
    linarith
  · -- x1 > x2 : supply binds, raise the price
    obtain ⟨ε, hεdef, hεpos⟩ : ∃ ε : ℝ, ε * (2 * (1 + α i)) = x1 - x2 ∧ 0 < ε :=
      ⟨(x1 - x2) / (2 * (1 + α i)), by field_simp,
        div_pos (by linarith) (by linarith)⟩
    have hεα : 0 < ε * α i := mul_pos hεpos hα0
    have h1 : M.Ω - (p i + ε) + M.γ * p (rival i) = x1 - ε := by rw [hx1def]; ring
    have h2 : α i * (p i + ε) - M.β * (α (rival i) * p (rival i)) = x2 + α i * ε := by
      rw [hx2def]; ring
    have hpos2 : 0 < x2 + α i * ε := by linarith
    have hpos12 : x2 + α i * ε < x1 - ε := by linarith
    have hmax1 : max (M.Ω - (p i + ε) + M.γ * p (rival i)) 0 = x1 - ε := by
      rw [h1]; exact max_eq_left (by linarith)
    have hmax2 : max (α i * (p i + ε) - M.β * (α (rival i) * p (rival i))) 0 = x2 + α i * ε := by
      rw [h2]; exact max_eq_left hpos2.le
    have hmin : min (x1 - ε) (x2 + α i * ε) = x2 + α i * ε := min_eq_right hpos12.le
    have hb : min (max x1 0) (max x2 0) = x2 := by
      rw [max_eq_left hx1.le, max_eq_left hx2.le]; exact min_eq_right hgt.le
    have hnash := hNE (p i + ε)
    rw [hmax1, hmax2, hmin, hb] at hnash
    have h3 := mul_pos hpi hεα
    have h4 := mul_pos hεpos hx2
    have h5 := mul_pos hεα hεpos
    have key : p i * x2 < (p i + ε) * (x2 + α i * ε) := by linarith
    have h6 := mul_lt_mul_of_pos_left key hk
    linarith
