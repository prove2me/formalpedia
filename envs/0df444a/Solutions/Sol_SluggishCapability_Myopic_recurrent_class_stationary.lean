-- Prove2me | solution 1 for SluggishCapability.Myopic.recurrent_class_stationary
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T00:47:47.595029+00:00
-- url     : https://prove2.me/submissions/4f3b775c-c7f4-4006-935f-d5de4549bd18

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_SluggishCapability_Myopic_Setting
import Theorems.Thm_MarkovMixing_exists_stationary_pos

open MarkovMixing
open SluggishCapability.Myopic

namespace SlugRecAux

variable {X : Type*} [Fintype X] [DecidableEq X]

lemma pow_nonneg' (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y) :
    ∀ t : ℕ, ∀ x y, 0 ≤ (K ^ t) x y := by
  intro t
  induction t with
  | zero => intro x y; simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ t ih =>
    intro x y
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun w _ => mul_nonneg (ih x w) (hK w y)

lemma reaches_refl (K : Matrix X X ℝ) (x : X) : Reaches K x x :=
  ⟨0, by simp⟩

lemma reaches_of_pos (K : Matrix X X ℝ) {x y : X} (h : 0 < K x y) : Reaches K x y :=
  ⟨1, by simpa using h⟩

lemma reaches_trans (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y) {x y z : X}
    (h1 : Reaches K x y) (h2 : Reaches K y z) : Reaches K x z := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  refine ⟨a + b, ?_⟩
  rw [pow_add, Matrix.mul_apply]
  have hle : (K ^ a) x y * (K ^ b) y z ≤ ∑ w, (K ^ a) x w * (K ^ b) w z :=
    Finset.single_le_sum (f := fun w => (K ^ a) x w * (K ^ b) w z)
      (fun w _ => mul_nonneg (pow_nonneg' K hK a x w) (pow_nonneg' K hK b w z))
      (Finset.mem_univ y)
  exact lt_of_lt_of_le (mul_pos ha hb) hle

/-- Positive `t`-step probability out of a closed set stays in the set. -/
lemma closed_pow (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y) (C : X → Prop)
    (hC : ∀ y z, C y → 0 < K y z → C z) :
    ∀ t : ℕ, ∀ y z, C y → 0 < (K ^ t) y z → C z := by
  intro t
  induction t with
  | zero =>
    intro y z hy h
    simp only [pow_zero, Matrix.one_apply] at h
    split_ifs at h with hyz
    · exact hyz ▸ hy
    · norm_num at h
  | succ t ih =>
    intro y z hy h
    by_contra hz
    rw [pow_succ, Matrix.mul_apply] at h
    have : ∑ w, (K ^ t) y w * K w z ≤ 0 := by
      apply Finset.sum_nonpos
      intro w _
      rcases (pow_nonneg' K hK t y w).lt_or_eq with h1 | h1
      · rcases (hK w z).lt_or_eq with h2 | h2
        · exact absurd (hC w z (ih y w hy h1) h2) hz
        · rw [← h2]; simp
      · rw [← h1]; simp
    linarith

lemma sum_subtype_eq {p : X → Prop} [DecidablePred p] (g : X → ℝ)
    (hg : ∀ z, ¬ p z → g z = 0) : ∑ a : {z // p z}, g a = ∑ z, g z := by
  rw [← Fintype.sum_subtype_add_sum_subtype p g]
  have : ∑ a : {z // ¬ p z}, g a = 0 := Finset.sum_eq_zero fun a _ => hg a.1 a.2
  rw [this, add_zero]

end SlugRecAux

open SlugRecAux

theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    (K : Matrix X X ℝ) (hK : IsStochastic K) (x : X) (hx : IsRecurrentState K x) :
    ∃ ν : X → ℝ, IsStationary K ν ∧ 0 < ν x ∧ ∀ y, 0 < ν y → Reaches K x y := by
  classical
  have hK0 := hK.1
  let C : X → Prop := fun y => Reaches K x y
  have hC : ∀ y z, C y → 0 < K y z → C z := fun y z hy h =>
    reaches_trans K hK0 hy (reaches_of_pos K h)
  have hCt := closed_pow K hK0 C hC
  -- entries leaving `C` vanish
  have hzero : ∀ t : ℕ, ∀ y z, C y → ¬ C z → (K ^ t) y z = 0 := fun t y z hy hz =>
    le_antisymm (not_lt.mp fun h => hz (hCt t y z hy h)) (pow_nonneg' K hK0 t y z)
  let Y := {y // C y}
  let KC : Matrix Y Y ℝ := fun a b => K a.1 b.1
  have hpowC : ∀ t : ℕ, ∀ a b : Y, (KC ^ t) a b = (K ^ t) a.1 b.1 := by
    intro t
    induction t with
    | zero =>
      intro a b
      simp only [pow_zero, Matrix.one_apply]
      by_cases hab : a = b
      · subst hab; simp
      · rw [if_neg hab, if_neg (fun h => hab (Subtype.ext h))]
    | succ t ih =>
      intro a b
      rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
      simp_rw [ih]
      exact sum_subtype_eq (p := C) (fun z => (K ^ t) a.1 z * K z b.1)
        (fun z hz => by rw [hzero t a.1 z a.2 hz, zero_mul])
  have hKCst : IsStochastic KC := by
    refine ⟨fun a b => hK0 a.1 b.1, fun a => ?_⟩
    have := sum_subtype_eq (p := C) (fun z => K a.1 z)
      (fun z hz => by simpa using hzero 1 a.1 z a.2 hz)
    simpa [KC] using this.trans (hK.2 a.1)
  have hKCirr : MarkovMixing.Irreducible KC := by
    intro a b
    obtain ⟨t, ht⟩ := reaches_trans K hK0 (hx a.1 a.2) b.2
    exact ⟨t, by rw [hpowC]; exact ht⟩
  have : Nonempty Y := ⟨⟨x, reaches_refl K x⟩⟩
  obtain ⟨π, hπ, hπpos, -⟩ := exists_stationary_pos KC hKCst hKCirr
  let ν : X → ℝ := fun z => if h : C z then π ⟨z, h⟩ else 0
  have hνoff : ∀ z, ¬ C z → ν z = 0 := fun z hz => by simp [ν, hz]
  refine ⟨ν, ⟨⟨fun z => ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · by_cases hz : C z
    · simp only [ν, dif_pos hz]; exact (hπpos _).le
    · simp [ν, hz]
  · rw [← sum_subtype_eq (p := C) ν hνoff]
    have : ∀ a : Y, ν a.1 = π a := fun a => by simp [ν, a.2]
    simp_rw [this]
    exact hπ.1.2
  · funext z
    simp only [Matrix.vecMul, dotProduct]
    rw [← sum_subtype_eq (p := C) (fun w => ν w * K w z)
      (fun w hw => by rw [hνoff w hw, zero_mul])]
    have e1 : ∀ a : Y, ν a.1 = π a := fun a => by simp [ν, a.2]
    simp_rw [e1]
    by_cases hz : C z
    · have h2 := congrFun hπ.2 ⟨z, hz⟩
      simp only [Matrix.vecMul, dotProduct, KC] at h2
      rw [h2]; simp [ν, hz]
    · rw [hνoff z hz]
      exact Finset.sum_eq_zero fun a _ => by
        rw [show K a.1 z = 0 by simpa using hzero 1 a.1 z a.2 hz, mul_zero]
  · have hxC : C x := reaches_refl K x
    simp only [ν, dif_pos hxC]; exact hπpos _
  · intro y hy
    by_contra hc
    rw [hνoff y hc] at hy
    exact lt_irrefl _ hy
