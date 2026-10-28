-- Prove2me | solution 1 for RiskPremiaDMP.Equivalence.rp_to_artificial
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T05:42:12.017931+00:00
-- url     : https://prove2.me/submissions/2c0b8b4e-758c-4c83-b617-ec31c4be0ec7

import Mathlib
import Definitions.Def_RiskPremiaDMP_Equivalence_Model

open RiskPremiaDMP.Equivalence

lemma aff_d1 (S SQ : ℝ → ℝ → ℝ) (C a b k : ℝ)
    (hrel : ∀ y η, S y η = C * SQ (y + a) (b + k * η)) (y η : ℝ) :
    d1 S y η = C * d1 SQ (y + a) (b + k * η) := by
  unfold d1
  have : (fun y' => S y' η) = fun y' => C * (fun z => SQ z (b + k * η)) (y' + a) := by
    funext y'; exact hrel y' η
  rw [this, deriv_const_mul_field]
  exact congrArg _ (deriv_comp_add_const (fun z => SQ z (b + k * η)) a y)

lemma aff_d11 (S SQ : ℝ → ℝ → ℝ) (C a b k : ℝ)
    (hrel : ∀ y η, S y η = C * SQ (y + a) (b + k * η)) (y η : ℝ) :
    d11 S y η = C * d11 SQ (y + a) (b + k * η) := by
  have h1 : ∀ y', deriv (fun y'' => S y'' η) y' = C * d1 SQ (y' + a) (b + k * η) :=
    fun y' => aff_d1 S SQ C a b k hrel y' η
  unfold d11
  have : (fun y' => deriv (fun y'' => S y'' η) y')
      = fun y' => C * (fun z => d1 SQ z (b + k * η)) (y' + a) := by
    funext y'; exact h1 y'
  rw [this, deriv_const_mul_field]
  exact congrArg _ (deriv_comp_add_const (fun z => d1 SQ z (b + k * η)) a y)

lemma aff_d2 (S SQ : ℝ → ℝ → ℝ) (C a b k : ℝ)
    (hrel : ∀ y η, S y η = C * SQ (y + a) (b + k * η)) (y η : ℝ) :
    d2 S y η = C * k * d2 SQ (y + a) (b + k * η) := by
  unfold d2
  have : (fun η' => S y η') = fun η' => C * (fun z => SQ (y + a) (b + z)) (k * η') := by
    funext η'; exact hrel y η'
  rw [this, deriv_const_mul_field]
  have h := deriv_comp_mul_left (c := k) (fun z => SQ (y + a) (b + z)) η
  have h2 := deriv_comp_const_add (fun m' => SQ (y + a) m') b (k * η)
  simp only [smul_eq_mul] at h
  rw [show deriv (fun η' => (fun z => SQ (y + a) (b + z)) (k * η')) η = _ from h]
  rw [show deriv (fun z => SQ (y + a) (b + z)) (k * η) = _ from h2]
  ring

lemma aff_d22 (S SQ : ℝ → ℝ → ℝ) (C a b k : ℝ)
    (hrel : ∀ y η, S y η = C * SQ (y + a) (b + k * η)) (y η : ℝ) :
    d22 S y η = C * k ^ 2 * d22 SQ (y + a) (b + k * η) := by
  have h1 : ∀ η', deriv (fun η'' => S y η'') η' = C * k * d2 SQ (y + a) (b + k * η') :=
    fun η' => aff_d2 S SQ C a b k hrel y η'
  unfold d22
  have : (fun η' => deriv (fun η'' => S y η'') η')
      = fun η' => C * k * (fun z => d2 SQ (y + a) (b + z)) (k * η') := by
    funext η'; exact h1 η'
  rw [this, deriv_const_mul_field]
  have h := deriv_comp_mul_left (c := k) (fun z => d2 SQ (y + a) (b + z)) η
  have h2 := deriv_comp_const_add (fun m' => d2 SQ (y + a) m') b (k * η)
  simp only [smul_eq_mul] at h
  rw [show deriv (fun η' => (fun z => d2 SQ (y + a) (b + z)) (k * η')) η = _ from h]
  rw [show deriv (fun z => d2 SQ (y + a) (b + z)) (k * η) = _ from h2]
  unfold d2
  ring

lemma toMuQ_eq (P : RPParams) (η : ℝ) :
    toMuQ P η = P.σy * P.ηbar / P.κy + (-(P.σy / P.κy)) * η := by
  unfold toMuQ; ring

lemma genQ_eq (P : RPParams) (hκ : P.κy ≠ 0) (S SQ : ℝ → ℝ → ℝ) (C : ℝ)
    (hrel : ∀ y η, S y η = C * SQ (toYQ P y) (toMuQ P η)) (y η : ℝ) :
    genQ P.κy P.σy P.κη P.ηbar P.ση S y η
      = C * genP (artificial P).κy (artificial P).σy (artificial P).κμ (artificial P).σμ SQ
          (toYQ P y) (toMuQ P η) := by
  have hrel' : ∀ y η, S y η = C * SQ (y + shift P)
      (P.σy * P.ηbar / P.κy + (-(P.σy / P.κy)) * η) := by
    intro y η; rw [hrel, toYQ, toMuQ_eq]
  have e1 := aff_d1 S SQ C _ _ _ hrel' y η
  have e11 := aff_d11 S SQ C _ _ _ hrel' y η
  have e2 := aff_d2 S SQ C _ _ _ hrel' y η
  have e22 := aff_d22 S SQ C _ _ _ hrel' y η
  rw [← toMuQ_eq, ← toYQ] at e1 e11 e2 e22
  unfold genQ genP
  simp only [artificial]
  rw [e1, e11, e2, e22]
  unfold toYQ toMuQ shift
  field_simp
  ring

lemma toYQ_surj (P : RPParams) (Y : ℝ) : ∃ y, toYQ P y = Y := ⟨Y - shift P, by unfold toYQ; ring⟩

lemma toMuQ_surj (P : RPParams) (hκ : P.κy ≠ 0) (hσ : P.σy ≠ 0) (M : ℝ) :
    ∃ η, toMuQ P η = M :=
  ⟨P.ηbar - M * P.κy / P.σy, by unfold toMuQ; field_simp; ring⟩

lemma equiv_core (P : RPParams) (hP : P.Standing) (q : ℝ → ℝ)
    (S θ SQ θQ : ℝ → ℝ → ℝ)
    (h24a : ∀ y η : ℝ, SQ (toYQ P y) (toMuQ P η) = Real.exp (shift P) * S y η)
    (h24b : ∀ y η : ℝ, θQ (toYQ P y) (toMuQ P η) = θ y η) :
    IsEquilibriumRP P q S θ ↔ IsEquilibriumNoRP (artificial P) q SQ θQ := by
  have hκ : P.κy ≠ 0 := ne_of_gt hP.1
  have hσ : P.σy ≠ 0 := ne_of_gt hP.2.1
  have hea : 0 < Real.exp (shift P) := Real.exp_pos _
  have hrel : ∀ y η, S y η = Real.exp (-shift P) * SQ (toYQ P y) (toMuQ P η) := by
    intro y η
    rw [h24a, ← mul_assoc, ← Real.exp_add]; simp
  -- pointwise equivalence
  have pt : ∀ y η, ((P.rf + P.s) * S y η
        = Real.exp y - P.z - P.β * P.c / (1 - P.β) * θ y η
            + genQ P.κy P.σy P.κη P.ηbar P.ση S y η ∧
      P.c = (1 - P.β) * q (θ y η) * S y η) ↔
      ((artificial P).rf + (artificial P).s) * SQ (toYQ P y) (toMuQ P η)
        = Real.exp (toYQ P y) - (artificial P).z
          - (artificial P).β * (artificial P).c / (1 - (artificial P).β) * θQ (toYQ P y) (toMuQ P η)
          + genP (artificial P).κy (artificial P).σy (artificial P).κμ (artificial P).σμ SQ
              (toYQ P y) (toMuQ P η) ∧
        (artificial P).c = (1 - (artificial P).β) * q (θQ (toYQ P y) (toMuQ P η))
            * SQ (toYQ P y) (toMuQ P η) := by
    intro y η
    have g := genQ_eq P hκ S SQ _ hrel y η
    have hg : genP (artificial P).κy (artificial P).σy (artificial P).κμ (artificial P).σμ SQ
        (toYQ P y) (toMuQ P η) = Real.exp (shift P) * genQ P.κy P.σy P.κη P.ηbar P.ση S y η := by
      rw [g, ← mul_assoc, ← Real.exp_add]; simp
    have hY : Real.exp (toYQ P y) = Real.exp (shift P) * Real.exp y := by
      unfold toYQ; rw [add_comm, Real.exp_add]
    rw [hg, h24a, h24b, hY]
    simp only [artificial]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linear_combination Real.exp (shift P) * h1,
             by linear_combination Real.exp (shift P) * h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨mul_left_cancel₀ hea.ne' ?_, mul_left_cancel₀ hea.ne' ?_⟩
      · linear_combination h1
      · linear_combination h2
  constructor
  · rintro ⟨hcd, hE⟩
    refine ⟨?_, ?_⟩
    · have hA : ContDiff ℝ 2 (fun p : ℝ × ℝ => (p.1 - shift P, P.ηbar - p.2 * P.κy / P.σy)) := by
        fun_prop
      have : Function.uncurry SQ = fun p : ℝ × ℝ => Real.exp (shift P) *
          Function.uncurry S (p.1 - shift P, P.ηbar - p.2 * P.κy / P.σy) := by
        funext p
        obtain ⟨y, hy⟩ := toYQ_surj P p.1
        obtain ⟨η, hη⟩ := toMuQ_surj P hκ hσ p.2
        have e1 : p.1 - shift P = y := by rw [← hy]; unfold toYQ; ring
        have e2 : P.ηbar - p.2 * P.κy / P.σy = η := by
          rw [← hη]; unfold toMuQ; field_simp; ring
        rw [e1, e2, Function.uncurry_apply_pair]
        have := h24a y η
        rw [hy, hη] at this
        exact this
      rw [this]
      exact contDiff_const.mul (hcd.comp hA)
    · intro Y M
      obtain ⟨y, rfl⟩ := toYQ_surj P Y
      obtain ⟨η, rfl⟩ := toMuQ_surj P hκ hσ M
      exact (pt y η).1 (hE y η)
  · rintro ⟨hcd, hE⟩
    refine ⟨?_, fun y η => (pt y η).2 (hE _ _)⟩
    have hA : ContDiff ℝ 2 (fun p : ℝ × ℝ => (p.1 + shift P, P.σy * (P.ηbar - p.2) / P.κy)) := by
      fun_prop
    have : Function.uncurry S = fun p : ℝ × ℝ => Real.exp (-shift P) *
        Function.uncurry SQ (p.1 + shift P, P.σy * (P.ηbar - p.2) / P.κy) := by
      funext p
      exact hrel p.1 p.2
    rw [this]
    exact contDiff_const.mul (hcd.comp hA)

theorem solution (P : RPParams) (hP : P.Standing) (q : ℝ → ℝ)
    (S θ SQ θQ : ℝ → ℝ → ℝ)
    (h24a : ∀ y η : ℝ, SQ (toYQ P y) (toMuQ P η) = Real.exp (shift P) * S y η)
    (h24b : ∀ y η : ℝ, θQ (toYQ P y) (toMuQ P η) = θ y η)
    (h19 : IsEquilibriumRP P q S θ) :
    IsEquilibriumNoRP (artificial P) q SQ θQ :=
  (equiv_core P hP q S θ SQ θQ h24a h24b).1 h19
