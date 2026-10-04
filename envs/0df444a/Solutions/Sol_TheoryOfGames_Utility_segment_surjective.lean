-- Prove2me | solution 1 for TheoryOfGames.Utility.segment_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T00:59:32.489206+00:00
-- url     : https://prove2.me/submissions/3dc97316-6420-49df-9d3a-b79f5bdb5339

import Mathlib
import Definitions.Def_TheoryOfGames_Utility_UtilitySystem

set_option autoImplicit false

namespace P2M97ad6402

open TheoryOfGames.Utility

lemma gt_asymm {U : Type*} (S : UtilitySystem U) {a b : U} (h : S.gt a b) : ¬ S.gt b a := by
  rcases S.complete a b with ⟨_, h1, _⟩ | ⟨_, _, h2⟩ | ⟨_, _, h3⟩
  · exact absurd h h1
  · exact h2
  · exact absurd h h3

lemma mix_gt_snd {U : Type*} (S : UtilitySystem U) {v u : U} (h : S.gt v u) (b : OpenUnit) :
    S.gt (S.mix b v u) u := by
  rw [S.mix_comm]
  exact S.lt_mix_of_lt _ u v h

lemma mono {U : Type*} (S : UtilitySystem U) {v u : U} (h : S.gt v u) (a b : OpenUnit)
    (hab : (a : ℝ) < b) : S.gt (S.mix b v u) (S.mix a v u) := by
  have hb0 : (0 : ℝ) < b := b.2.1
  have hbne : (b : ℝ) ≠ 0 := hb0.ne'
  have hc : (a : ℝ) / b ∈ Set.Ioo (0 : ℝ) 1 := ⟨div_pos a.2.1 hb0, (div_lt_one hb0).2 hab⟩
  have he : a = OpenUnit.mul ⟨(a : ℝ) / b, hc⟩ b := by
    apply Subtype.ext
    change (a : ℝ) = (a : ℝ) / b * b
    rw [div_mul_cancel₀ _ hbne]
  rw [he, ← S.mix_mix]
  exact S.mix_lt_of_gt _ _ _ (mix_gt_snd S h b)

lemma cmb_eq {U : Type*} (S : UtilitySystem U) (α : OpenUnit) (u v : U) :
    S.cmb α u v = S.mix α v u := by
  unfold UtilitySystem.cmb
  rw [S.mix_comm]
  congr 1
  apply Subtype.ext
  simp [OpenUnit.oneSub]

theorem main {U : Type*} (S : UtilitySystem U) {u₀ v₀ : U}
    (h : S.lt u₀ v₀) :
    ∀ w : U, S.lt u₀ w → S.lt w v₀ → ∃ α : OpenUnit, S.cmb α u₀ v₀ = w := by
  intro w hw1 hw2
  unfold UtilitySystem.lt at h hw1 hw2
  -- A = {x | p x < w}, with p x = mix x v₀ u₀
  set A : Set ℝ := {x | ∃ hx : x ∈ Set.Ioo (0 : ℝ) 1, S.gt w (S.mix ⟨x, hx⟩ v₀ u₀)} with hA
  -- every element of A lies below any y with p y > w
  have below : ∀ x ∈ A, ∀ y : OpenUnit, S.gt (S.mix y v₀ u₀) w → x < (y : ℝ) := by
    rintro x ⟨hx, hxw⟩ y hy
    by_contra hcon
    rcases (not_lt.mp hcon).lt_or_eq with hlt | heq
    · have := mono S h y ⟨x, hx⟩ hlt
      exact gt_asymm S hxw (S.trans _ _ _ this hy)
    · have : (⟨x, hx⟩ : OpenUnit) = y := Subtype.ext heq.symm
      rw [this] at hxw
      exact gt_asymm S hxw hy
  obtain ⟨a, ha⟩ := S.exists_mix_lt u₀ v₀ w hw1 hw2
  rw [S.mix_comm] at ha
  have haA : ((OpenUnit.oneSub a : OpenUnit) : ℝ) ∈ A := ⟨(OpenUnit.oneSub a).2, ha⟩
  obtain ⟨b, hb⟩ := S.exists_mix_gt v₀ u₀ w hw2 hw1
  have hne : A.Nonempty := ⟨_, haA⟩
  have hbdd : BddAbove A := ⟨(b : ℝ), fun x hx => (below x hx b hb).le⟩
  set s := sSup A with hs
  have hs0 : 0 < s := lt_of_lt_of_le (OpenUnit.oneSub a).2.1 (le_csSup hbdd haA)
  have hs1 : s < 1 := lt_of_le_of_lt (csSup_le hne fun x hx => (below x hx b hb).le) b.2.2
  set σ : OpenUnit := ⟨s, hs0, hs1⟩ with hσ
  rcases S.complete (S.mix σ v₀ u₀) w with ⟨heq, -, -⟩ | ⟨hgt, -, -⟩ | ⟨hlt, -, -⟩
  · exact ⟨σ, by rw [cmb_eq]; exact heq⟩
  · exfalso
    obtain ⟨c, hc⟩ := S.exists_mix_gt (S.mix σ v₀ u₀) u₀ w hgt hw1
    rw [S.mix_mix] at hc
    have hle : s ≤ ((OpenUnit.mul c σ : OpenUnit) : ℝ) :=
      csSup_le hne fun x hx => (below x hx _ hc).le
    have hv : ((OpenUnit.mul c σ : OpenUnit) : ℝ) = (c : ℝ) * s := rfl
    rw [hv] at hle
    have hc1 : (c : ℝ) < 1 := c.2.2
    nlinarith
  · exfalso
    obtain ⟨c, hc⟩ := S.exists_mix_lt (S.mix σ v₀ u₀) v₀ w hlt hw2
    rw [S.mix_comm σ v₀ u₀, S.mix_mix,
      S.mix_comm (OpenUnit.mul c (OpenUnit.oneSub σ)) u₀ v₀] at hc
    have htA : (((OpenUnit.oneSub (OpenUnit.mul c (OpenUnit.oneSub σ))) : OpenUnit) : ℝ) ∈ A :=
      ⟨(OpenUnit.oneSub (OpenUnit.mul c (OpenUnit.oneSub σ))).2, hc⟩
    have hle := le_csSup hbdd htA
    have hv : (((OpenUnit.oneSub (OpenUnit.mul c (OpenUnit.oneSub σ))) : OpenUnit) : ℝ)
        = 1 - (c : ℝ) * (1 - s) := rfl
    rw [hv, ← hs] at hle
    have hc1 : (c : ℝ) < 1 := c.2.2
    have hc0 : (0 : ℝ) < c := c.2.1
    nlinarith

end P2M97ad6402

open TheoryOfGames.Utility in
theorem solution {U : Type*} (S : UtilitySystem U) {u₀ v₀ : U}
    (h : S.lt u₀ v₀) :
    ∀ w : U, S.lt u₀ w → S.lt w v₀ → ∃ α : OpenUnit, S.cmb α u₀ v₀ = w := by
  exact P2M97ad6402.main S h
