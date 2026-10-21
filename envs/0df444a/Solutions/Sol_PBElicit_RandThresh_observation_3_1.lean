-- Prove2me | solution 1 for PBElicit.RandThresh.observation_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T07:44:15.247351+00:00
-- url     : https://prove2.me/submissions/1d082c83-cfa0-4879-9d0e-8634825d12c6

import Mathlib
import Definitions.Def_PBElicit_RandThresh_Setting

open Classical PBElicit.RandThresh

/-! Helpers for Theorem 3.5. -/

noncomputable def pbMkRule {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A] {c : A → ℝ}
    {ι : Type*} [Fintype ι] (w t : ι → ℝ) (g : ι → (Fin n → Finset A) → Finset A)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (hg : ∀ i ρ, IsMaxFeasible c (g i ρ)) :
    ThresholdRule n A c where
  size := Fintype.card ι
  weight r := w ((Fintype.equivFin ι).symm r)
  thr r := t ((Fintype.equivFin ι).symm r)
  agg r := g ((Fintype.equivFin ι).symm r)
  weight_nonneg r := hw _
  weight_sum := by rw [← hs]; exact Equiv.sum_comp (Fintype.equivFin ι).symm w
  agg_mem r ρ := hg _ ρ

lemma pbMkRule_exp {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A] {c : A → ℝ}
    {ι : Type*} [Fintype ι] (w t : ι → ℝ) (g : ι → (Fin n → Finset A) → Finset A)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (hg : ∀ i ρ, IsMaxFeasible c (g i ρ))
    (v : Fin n → A → ℝ) :
    (pbMkRule w t g hw hs hg).expWelfare v = ∑ i, w i * sw v (g i (approvals v (t i))) := by
  unfold ThresholdRule.expWelfare pbMkRule
  exact Equiv.sum_comp (Fintype.equivFin ι).symm (fun i => w i * sw v (g i (approvals v (t i))))

lemma pb_exists_ext {A : Type*} [Fintype A] [DecidableEq A] (c : A → ℝ) (S : Finset A) :
    ∃ T : Finset A, (cost c S ≤ 1 → S ⊆ T) ∧ IsMaxFeasible c T := by
  have key : ∀ S : Finset A, cost c S ≤ 1 → ∃ T, S ⊆ T ∧ IsMaxFeasible c T := by
    intro S hS
    obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image
      ((Finset.univ : Finset (Finset A)).filter (fun T => S ⊆ T ∧ cost c T ≤ 1)) Finset.card
      ⟨S, by simp [hS]⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT hmax
    refine ⟨T, hT.1, hT.2, fun T' hT' => ?_⟩
    by_contra h
    push_neg at h
    have := hmax T' ⟨hT.1.trans hT'.le, h⟩
    exact absurd (Finset.card_lt_card hT') (not_lt.mpr this)
  by_cases h : cost c S ≤ 1
  · obtain ⟨T, h1, h2⟩ := key S h; exact ⟨T, fun _ => h1, h2⟩
  · obtain ⟨T, -, h2⟩ := key ∅ (by simp [cost]); exact ⟨T, fun h' => absurd h' h, h2⟩

noncomputable def pbExt {A : Type*} [Fintype A] [DecidableEq A] (c : A → ℝ) (S : Finset A) :
    Finset A :=
  Classical.choose (pb_exists_ext c S)

lemma pbExt_max {A : Type*} [Fintype A] [DecidableEq A] (c : A → ℝ) (S : Finset A) :
    IsMaxFeasible c (pbExt c S) := (Classical.choose_spec (pb_exists_ext c S)).2

lemma pbExt_sup {A : Type*} [Fintype A] [DecidableEq A] (c : A → ℝ) (S : Finset A)
    (h : cost c S ≤ 1) : S ⊆ pbExt c S := (Classical.choose_spec (pb_exists_ext c S)).1 h

lemma pb_sw_mono {n : ℕ} {A : Type*} (v : Fin n → A → ℝ) (hv : ∀ i a, 0 ≤ v i a)
    {S T : Finset A} (h : S ⊆ T) : sw v S ≤ sw v T :=
  Finset.sum_le_sum_of_subset_of_nonneg h
    (fun a _ _ => Finset.sum_nonneg (fun i _ => hv i a))

lemma pb_sw_nonneg {n : ℕ} {A : Type*} (v : Fin n → A → ℝ) (hv : ∀ i a, 0 ≤ v i a)
    (S : Finset A) : 0 ≤ sw v S :=
  Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun i _ => hv i a))

lemma pb_sw_ext {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A] (c : A → ℝ)
    (v : Fin n → A → ℝ) (hv : ∀ i a, 0 ≤ v i a) (S : Finset A) (h : cost c S ≤ 1) :
    sw v S ≤ sw v (pbExt c S) := pb_sw_mono v hv (pbExt_sup c S h)

theorem solution {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A] (c : A → ℝ)
    (hc : ∀ a, 0 ≤ c a ∧ c a ≤ 1) (hm : 1 ≤ Fintype.card A) :
    ∃ R : ThresholdRule n A c, (∀ r ρ ρ', R.agg r ρ = R.agg r ρ') ∧
      ∀ v : Fin n → A → ℝ, IsUtilityProfile v →
        ∀ T : Finset A, IsMaxFeasible c T →
          sw v T ≤ (Fintype.card A : ℝ) * R.expWelfare v := by
  set m : ℕ := Fintype.card A with hmdef
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  have hw : ∀ a : A, 0 ≤ (fun _ => 1 / (m:ℝ)) a := fun _ => by positivity
  have hs : ∑ a : A, (fun _ => 1 / (m:ℝ)) a = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← hmdef]; field_simp
  have hg : ∀ (a : A) (ρ : Fin n → Finset A), IsMaxFeasible c ((fun a _ => pbExt c {a}) a ρ) :=
    fun a _ => pbExt_max c {a}
  refine ⟨pbMkRule (fun _ => 1 / (m:ℝ)) (fun _ => 0) (fun a _ => pbExt c {a}) hw hs hg,
    fun r ρ ρ' => rfl, fun v hv T hT => ?_⟩
  rw [pbMkRule_exp]
  have hv0 := hv.1
  have hT : sw v T ≤ n := by
    calc sw v T ≤ sw v Finset.univ := pb_sw_mono v hv0 (Finset.subset_univ T)
      _ = n := by
        unfold sw; rw [Finset.sum_comm]; simp [hv.2]
  have hn : (n:ℝ) ≤ ∑ a : A, sw v (pbExt c {a}) := by
    have : (n:ℝ) = ∑ a : A, sw v {a} := by
      simp only [sw, Finset.sum_singleton]
      rw [Finset.sum_comm]
      simp [hv.2]
    rw [this]
    refine Finset.sum_le_sum (fun a _ => pb_sw_ext c v hv0 _ ?_)
    simp [cost, (hc a).2]
  rw [← Finset.mul_sum, ← mul_assoc, mul_one_div_cancel hmpos.ne', one_mul]
  linarith
