-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.normalized_partition_positive
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:08:18.284636+00:00
-- url     : https://prove2.me/submissions/09ca9406-cf92-470e-869f-218f715ecaa7

import Theorems.Thm_ZeroFreeRRG_Hardcore_model_pi_positive_simplex
import Theorems.Thm_ZeroFreeRRG_Hardcore_model_edge_nonnegative
import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (hm : m.Valid) (t : ℝ) (ht : m.PosParam t)
    (d n : ℕ) (M : Matching n d) : 0 < normZ m t M := by
  classical
  have hπ : ∀ a, 0 < m.pi t a := (model_pi_positive_simplex m hm t ht).1
  have hP := model_edge_nonnegative m hm t ht
  have hM : ∀ a b, 0 ≤ m.M t a b := fun a b =>
    div_nonneg (hP a b) (mul_nonneg (hπ a).le (hπ b).le)
  have hdiag : ∃ a, 0 < m.P t a a := by
    cases m with
    | hardcore =>
      change 0 < t ∧ t < 1/2 at ht
      refine ⟨(0 : Fin 2),?_⟩
      simp [Model.P]
      linarith
    | potts q =>
      change 2 ≤ q at hm
      change 0 < t ∧ t < 1 at ht
      have hq : (2:ℝ) ≤ q := by exact_mod_cast hm
      have hq0 : 0 < (q:ℝ) := by linarith
      have hq1 : 0 < (q:ℝ)-1+t := by linarith
      refine ⟨⟨0,by omega⟩,?_⟩
      change 0 < ((1:ℝ)+(t-1))/((q:ℝ)*((q:ℝ)-1+t))
      apply div_pos _ (mul_pos hq0 hq1)
      linarith
  obtain ⟨a,ha⟩ := hdiag
  have haa : 0 < m.M t a a := div_pos ha (mul_pos (hπ a) (hπ a))
  have hw (σ : Fin n → m.Spin) : 0 ≤ weight m t M σ := by
    unfold weight
    exact mul_nonneg (Finset.prod_nonneg fun v hv => (hπ (σ v)).le)
      (Finset.prod_nonneg fun x hx => hM (σ x.1) (σ (M.1 x).1))
  have hconst : 0 < weight m t M (fun _ => a) := by
    unfold weight
    exact mul_pos (Finset.prod_pos fun v hv => hπ a) (Finset.prod_pos fun x hx => haa)
  unfold normZ
  apply Finset.sum_pos'
  · intro σ hσ
    exact hw σ
  · exact ⟨fun _ => a,Finset.mem_univ _,hconst⟩
