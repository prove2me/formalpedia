-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.model_pi_positive_simplex
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:47:42.383432+00:00
-- url     : https://prove2.me/submissions/824f7986-5dfb-4646-9f80-c9aeb949e6e0

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Mathlib
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

private lemma potts_pi_real (q : ℕ) (β : ℝ) (i : Fin q)
    (hq : (q:ℝ) ≠ 0) (ht : (q:ℝ) - 1 + β ≠ 0) :
    Model.pi (.potts q) β i = (q:ℝ)⁻¹ := by
  unfold Model.pi Model.P
  change (∑ j : Fin q, ((1:ℝ) + if i = j then β - 1 else 0) /
      ((q:ℝ) * ((q:ℝ) - 1 + β))) = (q:ℝ)⁻¹
  rw [← Finset.sum_div]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hs : (∑ j : Fin q, if i = j then β - 1 else 0) = β - 1 := by simp
  rw [hs]
  field_simp
  ring

theorem solution (m : Model) (hm : m.Valid) (t : ℝ) (ht : m.PosParam t) :
    (∀ a, 0 < m.pi t a) ∧ m.pi t ∈ stdSimplex ℝ m.Spin := by
  cases m with
  | hardcore =>
    change 0 < t ∧ t < 1/2 at ht
    have h0 : Model.pi .hardcore t (0 : Fin 2) = 1-t := by
      simp [Model.pi, Model.Spin, Model.P, Fin.sum_univ_two] <;> ring
    have h1 : Model.pi .hardcore t (1 : Fin 2) = t := by
      simp [Model.pi, Model.Spin, Model.P, Fin.sum_univ_two] <;> ring
    constructor
    · intro a
      fin_cases a <;> simp [h0,h1] <;> linarith
    · change (∀ a : Fin 2, 0 ≤ Model.pi .hardcore t a) ∧
        (∑ a : Fin 2, Model.pi .hardcore t a) = 1
      constructor
      · intro a
        fin_cases a <;> simp [h0,h1] <;> linarith
      · rw [Fin.sum_univ_two,h0,h1]
        ring
  | potts q =>
    change 2 ≤ q at hm
    change 0 < t ∧ t < 1 at ht
    have hq : (2:ℝ) ≤ q := by exact_mod_cast hm
    have hqn : (q:ℝ) ≠ 0 := by linarith
    have ht' : (q:ℝ)-1+t ≠ 0 := by linarith
    have hpi (i : Fin q) : Model.pi (.potts q) t i = (q:ℝ)⁻¹ := potts_pi_real q t i hqn ht'
    constructor
    · intro a
      change Fin q at a
      change 0 < Model.pi (.potts q) t a
      rw [hpi a]
      positivity
    · change (∀ a : Fin q, 0 ≤ Model.pi (.potts q) t a) ∧
        (∑ a : Fin q, Model.pi (.potts q) t a) = 1
      constructor
      · intro a
        rw [hpi]
        positivity
      · simp_rw [hpi]
        simp [hqn]
