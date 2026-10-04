-- Prove2me | solution 1 for TheoryOfGames.Utility.intervalMap_unique
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:29:57.228986+00:00
-- url     : https://prove2.me/submissions/c675709e-29b6-491f-abf4-5e6e7da1f506

import Theorems.Thm_TheoryOfGames_Utility_segment_mono_injective
import Theorems.Thm_TheoryOfGames_Utility_segment_surjective
import Definitions.Def_TheoryOfGames_Utility_intervalMap

/-!
# (A:F): the interval function is characterized by (i), (ii) and either of the two
functional equations

For fixed `u₀ < v₀`, any map `f₁` on the utilities with `u₀ ≦ w ≦ v₀` that satisfies
`f₁(u₀) = 0`, `f₁(v₀) = 1`, and *either* (ii') `f₁((1−β)u₀ + βw) = β f₁(w)` (`w ≠ u₀`)
*or* (iii') `f₁((1−β)v₀ + βw) = 1 − β + β f₁(w)` (`w ≠ v₀`), coincides with the interval
function `f = f_{u₀,v₀}` of (A:D).

The point: evaluating the functional equation at the far endpoint pins `f₁` down on the whole
open segment. In case (ii'), take `w = v₀`:
$$f₁\big((1-\beta)u_0 + \beta v_0\big) = \beta\, f₁(v_0) = \beta = f\big((1-\beta)u_0 +
\beta v_0\big).$$
In case (iii'), take `w = u₀` and use `cmb β v₀ u₀ = cmb (1−β) u₀ v₀`:
$$f₁\big((1-\gamma)u_0 + \gamma v_0\big) = f₁\big(\mathrm{cmb}\ \gamma\ v_0\ u_0\big)
= 1 - \gamma + \gamma f₁(u_0) = 1-\gamma = \gamma',$$
with `γ' = 1 − γ`. Both endpoints match by (i), (ii), so `f₁ = f` on the closed interval
(the open part via surjectivity (A:C) and the defining property of `f`).
-/

open TheoryOfGames.Utility

namespace AFaux

variable {U : Type*} (S : UtilitySystem U)

/-- `oneSub` is an involution. -/
private lemma oneSub_oneSub (x : OpenUnit) : OpenUnit.oneSub (OpenUnit.oneSub x) = x := by
  ext1
  simp [OpenUnit.oneSub]

/-- The commutation axiom in `oneSub` form. -/
private lemma mix_comm' (x : OpenUnit) (u v : U) :
    S.mix (OpenUnit.oneSub x) u v = S.mix x v u := by
  rw [S.mix_comm, oneSub_oneSub]

/-- `gt` is irreflexive (from (3:A:a)). -/
private lemma gt_irrefl (v : U) : ¬ S.gt v v := by
  rcases S.complete v v with hc | hc | hc
  · exact hc.2.1
  · exact absurd rfl hc.2.1
  · exact absurd rfl hc.2.1

/-- If `cmb α u₀ v₀ = w` and `w ≠ u₀` then `f(w) = α` (injectivity (A:B)). -/
private lemma f_eq_of_cmb {u₀ v₀ : U} (h : S.lt u₀ v₀) (w : U) (α : OpenUnit)
    (hmem : S.cmb α u₀ v₀ = w) (hw₀ : w ≠ u₀) :
    intervalMap S u₀ v₀ w = (α : ℝ) := by
  obtain ⟨hbetw, hinj, hmono⟩ := segment_mono_injective S h
  have hwv : w ≠ v₀ := by
    intro hc
    rw [← hmem] at hc
    have hb := (hbetw α).2
    rw [hc] at hb
    exact gt_irrefl S v₀ hb
  have hex : ∃ a : OpenUnit, S.cmb a u₀ v₀ = w := ⟨α, hmem⟩
  have hopen : intervalMap S u₀ v₀ w = ((Classical.choose hex : OpenUnit) : ℝ) := by
    unfold intervalMap
    rw [if_neg hw₀, if_neg hwv, dif_pos hex]
  rw [hopen]
  have hsame : α = Classical.choose hex :=
    hinj (hmem.trans (Classical.choose_spec hex).symm)
  rw [hsame]

/-- The endpoint swap: `cmb β v₀ u₀ = cmb (1−β) u₀ v₀`. -/
private lemma cmb_swap (β : OpenUnit) (u₀ v₀ : U) :
    S.cmb β v₀ u₀ = S.cmb (OpenUnit.oneSub β) u₀ v₀ := by
  show S.mix (OpenUnit.oneSub β) v₀ u₀
      = S.mix (OpenUnit.oneSub (OpenUnit.oneSub β)) u₀ v₀
  rw [mix_comm' S β v₀ u₀, oneSub_oneSub]

end AFaux

open TheoryOfGames.Utility AFaux

theorem solution {U : Type*} (S : UtilitySystem U) {u₀ v₀ : U}
    (h : S.lt u₀ v₀) (f₁ : U → ℝ) (h0 : f₁ u₀ = 0) (h1 : f₁ v₀ = 1)
    (hf : (∀ (β : OpenUnit) (w : U), S.le u₀ w → S.le w v₀ → w ≠ u₀ →
            f₁ (S.cmb β u₀ w) = (β : ℝ) * f₁ w) ∨
          (∀ (β : OpenUnit) (w : U), S.le u₀ w → S.le w v₀ → w ≠ v₀ →
            f₁ (S.cmb β v₀ w) = 1 - (β : ℝ) + (β : ℝ) * f₁ w)) :
    ∀ w : U, S.le u₀ w → S.le w v₀ → f₁ w = intervalMap S u₀ v₀ w := by
  obtain ⟨hbetw, hinj, hmono⟩ := segment_mono_injective S h
  have hu₀v₀ : u₀ ≠ v₀ := by
    intro hc
    exact gt_irrefl S v₀ (hc ▸ h)
  intro w hw₀ hwv
  rcases hw₀ with heq | hwgt
  · -- w = u₀
    rw [← heq, h0]
    unfold intervalMap
    rw [if_pos rfl]
  rcases hwv with heq | hwlt
  · -- w = v₀
    rw [heq, h1]
    unfold intervalMap
    rw [if_neg (fun hc => hu₀v₀ hc.symm), if_pos rfl]
  · -- u₀ < w < v₀: write w = cmb α u₀ v₀
    obtain ⟨α, hα⟩ := segment_surjective S h w hwgt hwlt
    have hwne : w ≠ u₀ := by
      intro hc
      rw [hc] at hwgt
      exact gt_irrefl S u₀ hwgt
    rw [f_eq_of_cmb S h w α hα hwne, ← hα]
    rcases hf with hf2 | hf3
    · -- case (ii'): evaluate at v₀
      have := hf2 α v₀ (Or.inr h) (Or.inl rfl) (fun hc => hu₀v₀ hc.symm)
      rw [h1, mul_one] at this
      exact this
    · -- case (iii'): evaluate at u₀ via the endpoint swap
      have hswap : S.cmb (OpenUnit.oneSub α) v₀ u₀ = S.cmb α u₀ v₀ := by
        rw [cmb_swap S (OpenUnit.oneSub α) u₀ v₀, oneSub_oneSub]
      have := hf3 (OpenUnit.oneSub α) u₀ (Or.inl rfl) (Or.inr h)
        (fun hc => hu₀v₀ hc)
      rw [h0] at this
      rw [hswap] at this
      simp only [OpenUnit.oneSub] at this
      linarith
