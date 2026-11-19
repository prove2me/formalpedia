-- Prove2me | solution 1 for QueueSignal.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @shuffle
-- created : 2026-11-18T06:16:00.920108+00:00
-- url     : https://prove2.me/submissions/3e534950-d4a6-4b3e-a088-7f9542480fd9

import Definitions.Def_QueueSignal_QueueModel
import Theorems.Thm_QueueSignal_unique_crossing
import Theorems.Thm_QueueSignal_credible_belief_cases
import Theorems.Thm_QueueSignal_pooling_R_iff
import Theorems.Thm_QueueSignal_pooling_C_iff
import Theorems.Thm_QueueSignal_separating_RC
import Theorems.Thm_QueueSignal_separating_CR
import Mathlib.Tactic.NormNum

open QueueSignal

private theorem payoff_independent_of_type (P : Params) (lam : ℝ)
    (t : QType) (s : Sig) (d : ℝ) : pay P lam t s d = pay P lam .H s d := by
  cases s <;> rfl

private theorem pooling_refinement (P : Params) (hP : P.Valid) (lam : ℝ)
    (on off : Sig) (hne : on ≠ off) (b : Sig → ℝ) (hb : b on = P.δ)
    (hSE : IsPureSE P.δ (pay P lam) (on, on) b) :
    IsPurePSE P.δ (pay P lam) (on, on) b ↔
      pay P lam .H off P.δ ≤ pay P lam .H on P.δ := by
  have hs : ¬ OnPath (on, on) off := by simpa [OnPath] using hne
  have heq (t : QType) : eqPay (pay P lam) (on, on) b t = pay P lam .H on P.δ := by
    have hsig : Profile.sig (on, on) t = on := by cases t <;> rfl
    rw [eqPay, hsig, hb, payoff_independent_of_type]
  constructor
  · intro h
    by_contra! hdev
    have hd (t : QType) : eqPay (pay P lam) (on, on) b t < pay P lam t off P.δ := by
      rw [heq, payoff_independent_of_type P lam t off P.δ]
      exact hdev
    have hc : IsCredible P.δ (pay P lam) (on, on) b off P.δ := by
      refine ⟨⟨.H, Or.inl (hd .H)⟩, fun _ => 1, ?_, ?_, ?_, ?_, ?_⟩
      · intro t ht
        rfl
      · intro t ht
        exact ⟨zero_le_one, le_rfl⟩
      · intro t ht _
        exact (ht (hd t)).elim
      · norm_num
      · simp [prior]
    exact h.2 off hs P.δ hc .H (hd .H)
  · intro h
    refine ⟨hSE, ?_⟩
    intro s hso γ hc t hdev
    have hso' : s = off := by
      cases on <;> cases off <;> cases s <;> simp_all [OnPath]
    subst s
    have hd (u : QType) : eqPay (pay P lam) (on, on) b u < pay P lam u off γ := by
      simpa only [heq, payoff_independent_of_type] using hdev
    have hγ := (credible_belief_cases P.δ hP.2.2.2.2.1 hP.2.2.2.2.2
      (pay P lam) (on, on) b off hs γ).1 hc hd
    exact (not_lt_of_ge h) (by simpa only [hγ, heq] using hd .H)

theorem solution (P : Params) (hP : P.Valid) :
    ∃ lhat : ℝ, (0 < lhat ∧ lamO P lhat P.δ = lamU P lhat P.δ) ∧
      (∀ lam : ℝ, 0 < lam → lamO P lam P.δ = lamU P lam P.δ → lam = lhat) ∧
      ∀ lam : ℝ, 0 < lam → lamO P lam 1 ≠ lamU P lam 0 → lamO P lam 0 ≠ lamU P lam 1 →
        ∀ σ : Profile,
          (lam < lhat →
            ((∃ b : Sig → ℝ, IsPurePSE P.δ (pay P lam) σ b) ↔ σ = (.C, .C))) ∧
          (lhat < lam →
            ((∃ b : Sig → ℝ, IsPurePSE P.δ (pay P lam) σ b) ↔ σ = (.R, .R))) := by
  have hδ0 := hP.2.2.2.2.1
  have hδ1 := hP.2.2.2.2.2
  obtain ⟨lhat, hlhat, heq, huniq, hbelow, habove⟩ :=
    unique_crossing P hP P.δ hδ0.le hδ1.le
  refine ⟨lhat, ⟨hlhat, heq⟩, huniq, ?_⟩
  intro lam hlam hneRC hneCR σ
  have hR : (∃ b : Sig → ℝ, IsPurePSE P.δ (pay P lam) (.R, .R) b) ↔
      lamU P lam P.δ ≤ lamO P lam P.δ := by
    obtain ⟨hprior, hpool⟩ := pooling_R_iff P hP lam hlam
    constructor
    · rintro ⟨b, hb⟩
      exact (pooling_refinement P hP lam .R .C (by decide) b (hprior b hb.1) hb.1).mp hb
    · intro h
      have hse := (hpool P.δ hδ0.le hδ1.le).mpr h
      exact ⟨beliefs P.δ P.δ,
        (pooling_refinement P hP lam .R .C (by decide) _ rfl hse).mpr h⟩
  have hC : (∃ b : Sig → ℝ, IsPurePSE P.δ (pay P lam) (.C, .C) b) ↔
      lamO P lam P.δ ≤ lamU P lam P.δ := by
    obtain ⟨hprior, hpool⟩ := pooling_C_iff P hP lam hlam
    constructor
    · rintro ⟨b, hb⟩
      exact (pooling_refinement P hP lam .C .R (by decide) b (hprior b hb.1) hb.1).mp hb
    · intro h
      have hse := (hpool P.δ hδ0.le hδ1.le).mpr h
      exact ⟨beliefs P.δ P.δ,
        (pooling_refinement P hP lam .C .R (by decide) _ rfl hse).mpr h⟩
  have hRC : ¬ (∃ b : Sig → ℝ, IsPurePSE P.δ (pay P lam) (.R, .C) b) := by
    rintro ⟨b, hb⟩
    exact hneRC ((separating_RC P hP lam hlam b).mp hb.1).2.2
  have hCR : ¬ (∃ b : Sig → ℝ, IsPurePSE P.δ (pay P lam) (.C, .R) b) := by
    rintro ⟨b, hb⟩
    exact hneCR ((separating_CR P hP lam hlam b).mp hb.1).2.2
  rcases σ with ⟨sH, sL⟩
  cases sH <;> cases sL
  · constructor
    · intro hlt
      simp [hR, (not_le_of_gt (hbelow lam hlam hlt))]
    · intro hlt
      simp [hR, (habove lam hlt).le]
  · simp [hRC]
  · simp [hCR]
  · constructor
    · intro hlt
      simp [hC, (hbelow lam hlam hlt).le]
    · intro hlt
      simp [hC, (not_le_of_gt (habove lam hlt))]
