-- Prove2me | solution 1 for ProactiveUpgrade.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:13:21.652544+00:00
-- url     : https://prove2.me/submissions/e10e6551-92bf-40e2-b42f-915c7e231efc

import Mathlib
import Definitions.Def_ProactiveUpgrade_Dir
import Definitions.Def_ProactiveUpgrade_Gen
import Definitions.Def_ProactiveUpgrade_AntiMultimodular

namespace Aux_ProactiveUpgrade_lemma_A_1
open ProactiveUpgrade

lemma uv_nonneg {n : ℕ} (i j : Fin n) : 0 ≤ unitVec i j := by
  unfold unitVec; rw [Pi.single_apply]; split_ifs <;> norm_num

lemma uv_self {n : ℕ} (i : Fin n) : unitVec i i = 1 := by
  unfold unitVec; exact Pi.single_eq_same _ _

lemma uv_ne {n : ℕ} {i j : Fin n} (h : j ≠ i) : unitVec i j = 0 := by
  unfold unitVec; exact Pi.single_eq_of_ne h _

lemma pred_ne {n : ℕ} (k : Fin n) (hk : 0 < k.val) : k ≠ predIdx k hk := by
  intro h
  have := congrArg Fin.val h
  simp [predIdx] at this
  omega

lemma d_self {n : ℕ} (k : Fin n) (hk : 0 < k.val) : Gen.vec (Gen.d k hk) k = -1 := by
  show unitVec (predIdx k hk) k - unitVec k k = -1
  rw [uv_self, uv_ne (pred_ne k hk)]; norm_num

lemma d_other {n : ℕ} (k : Fin n) (hk : 0 < k.val) (j : Fin n) (hj : j ≠ k) :
    0 ≤ Gen.vec (Gen.d k hk) j := by
  show 0 ≤ unitVec (predIdx k hk) j - unitVec k j
  rw [uv_ne hj]; simpa using uv_nonneg _ _

lemma pos_nonneg {n : ℕ} (h : 0 < n) (j : Fin n) : 0 ≤ Gen.vec (Gen.posLast h) j := by
  show 0 ≤ unitVec _ j
  exact uv_nonneg _ _

lemma neg_zero {n : ℕ} (h : 0 < n) : Gen.vec (Gen.negFirst h) ⟨0, h⟩ = -1 := by
  show -unitVec ⟨0, h⟩ ⟨0, h⟩ = -1
  rw [uv_self]

lemma neg_other {n : ℕ} (h : 0 < n) (j : Fin n) (hj : j ≠ ⟨0, h⟩) :
    Gen.vec (Gen.negFirst h) j = 0 := by
  show -unitVec ⟨0, h⟩ j = 0
  rw [uv_ne hj]; norm_num

lemma vec_inj {n : ℕ} (a b : Gen n) (h : Gen.vec a = Gen.vec b) : a = b := by
  have h' := fun j => congrFun h j
  cases a with
  | negFirst ha =>
    cases b with
    | negFirst hb => rfl
    | d k hk =>
      have e := h' k
      rw [neg_other ha k (fun hh => by rw [hh] at hk; exact absurd hk (lt_irrefl 0)), d_self] at e
      norm_num at e
    | posLast hb =>
      have e := h' ⟨0, ha⟩
      rw [neg_zero] at e
      have := pos_nonneg hb ⟨0, ha⟩
      linarith
  | d k hk =>
    cases b with
    | negFirst hb =>
      have e := h' k
      rw [neg_other hb k (fun hh => by rw [hh] at hk; exact absurd hk (lt_irrefl 0)), d_self] at e
      norm_num at e
    | d k' hk' =>
      by_cases hkk : k = k'
      · subst hkk; rfl
      · have e := h' k
        rw [d_self] at e
        have := d_other k' hk' k hkk
        linarith
    | posLast hb =>
      have e := h' k
      rw [d_self] at e
      have := pos_nonneg hb k
      linarith
  | posLast ha =>
    cases b with
    | negFirst hb =>
      have e := h' ⟨0, hb⟩
      rw [neg_zero] at e
      have := pos_nonneg ha ⟨0, hb⟩
      linarith
    | d k hk =>
      have e := h' k
      rw [d_self] at e
      have := pos_nonneg ha k
      linarith
    | posLast hb => rfl

end Aux_ProactiveUpgrade_lemma_A_1

open ProactiveUpgrade Aux_ProactiveUpgrade_lemma_A_1 in
theorem solution {n : ℕ} (f : (Fin n → ℕ) → ℝ) :
    AntiMultimodular f ↔
      ∀ (a b : Gen n), a ≠ b → ∀ x : Fin n → ℤ, EvalInQuad a.toDir b.toDir x →
        0 ≤ a.toDir.delta (b.toDir.delta (liftZ f)) x := by
  constructor
  · intro hA a b hab x hx
    have hne : Gen.vec a ≠ Gen.vec b := fun h => hab (vec_inj a b h)
    have key := hA (x + a.toDir.shift + b.toDir.shift) a.toDir.vec b.toDir.vec ⟨a, rfl⟩ ⟨b, rfl⟩
      hne hx.1 hx.2.1 hx.2.2.1 hx.2.2.2
    unfold Dir.delta
    have e1 : x + a.toDir.shift + a.toDir.vec + b.toDir.shift + b.toDir.vec
        = x + a.toDir.shift + b.toDir.shift + a.toDir.vec + b.toDir.vec := by abel
    have e2 : x + a.toDir.shift + a.toDir.vec + b.toDir.shift
        = x + a.toDir.shift + b.toDir.shift + a.toDir.vec := by abel
    rw [e1, e2]
    linarith
  · intro hB x a' b' ha' hb' hne hq0 hq1 hq2 hq3
    obtain ⟨a, rfl⟩ := ha'
    obtain ⟨b, rfl⟩ := hb'
    have hab : a ≠ b := fun h => hne (by rw [h])
    obtain ⟨x0, hx0⟩ : ∃ x0, x0 = x - a.toDir.shift - b.toDir.shift := ⟨_, rfl⟩
    have hx : x0 + a.toDir.shift + b.toDir.shift = x := by rw [hx0]; abel
    have key := hB a b hab x0 ⟨by rw [hx]; exact hq0, by rw [hx]; exact hq1,
      by rw [hx]; exact hq2, by rw [hx]; exact hq3⟩
    unfold Dir.delta at key
    have e1 : x0 + a.toDir.shift + a.toDir.vec + b.toDir.shift + b.toDir.vec
        = x + Gen.vec a + Gen.vec b := by rw [← hx]; unfold Gen.vec; abel
    have e2 : x0 + a.toDir.shift + a.toDir.vec + b.toDir.shift = x + Gen.vec a := by
      rw [← hx]; unfold Gen.vec; abel
    have e3 : x0 + a.toDir.shift + b.toDir.shift + b.toDir.vec = x + Gen.vec b := by
      show _ = x + b.toDir.vec
      rw [hx]
    rw [e1, e2, e3, hx] at key
    linarith
