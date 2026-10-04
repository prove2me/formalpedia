-- Prove2me | solution 1 for TheoryOfGames.Utility.intervalMap_properties
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:25:35.688877+00:00
-- url     : https://prove2.me/submissions/f0708aab-3039-49cf-825d-5f24c7bed7c7

import Theorems.Thm_TheoryOfGames_Utility_cmb_lt_cmb_of_lt
import Theorems.Thm_TheoryOfGames_Utility_segment_mono_injective
import Theorems.Thm_TheoryOfGames_Utility_segment_surjective
import Theorems.Thm_TheoryOfGames_Utility_cmb_self
import Definitions.Def_TheoryOfGames_Utility_intervalMap

/-!
# (A:E): the interval function is monotone and satisfies the two functional equations

For fixed `u₀ < v₀` write `f = f_{u₀,v₀}` for the interval map of (A:D): `f(u₀) = 0`,
`f(v₀) = 1`, and `f(w) = α` where `w = (1−α)u₀ + αv₀` (well defined by the injectivity (A:B)
and surjectivity (A:C) of the segment map). Then on `u₀ ≦ w ≦ v₀`:

* (i') `w < w'` implies `f(w) < f(w')`;
* (ii') `f((1−β)u₀ + βw) = β f(w)` for `0 < β < 1`, `w ≠ u₀`;
* (iii') `f((1−β)v₀ + βw) = 1 − β + β f(w)` for `0 < β < 1`, `w ≠ v₀`.

The heart is the mixture algebra with anchor `u₀` resp. `v₀`: with `w = cmb α u₀ v₀`,
```
  cmb β u₀ w = cmb (β·α) u₀ v₀,          cmb β v₀ w = cmb (1 − β·(1−α)) u₀ v₀,
```
which follow from the axioms (3:C:a) `mix_comm` and (3:C:b) `mix_mix`: commute the outer
mixture into "mixture-first" position, then absorb. Since both right-hand sides lie strictly
between `u₀` and `v₀` (A:B), the values of `f` on them read off by injectivity.
-/

open TheoryOfGames.Utility

namespace AEaux

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

/-- `gt` is asymmetric (from (3:A:a)). -/
private lemma gt_asymm (u v : U) (h : S.gt u v) : ¬ S.gt v u := by
  rcases S.complete u v with hc | hc | hc
  · exact absurd h hc.2.1
  · exact hc.2.2
  · exact absurd h hc.2.2

/-- `u₀ ≠ v₀` when `u₀ < v₀`. -/
private lemma ne_of_lt {u₀ v₀ : U} (h : S.lt u₀ v₀) : u₀ ≠ v₀ := by
  intro hc
  exact gt_irrefl S v₀ (hc ▸ h)

/-- The value of `f` at `u₀` is `0`. -/
private lemma f_u₀ {u₀ v₀ : U} (h : S.lt u₀ v₀) : intervalMap S u₀ v₀ u₀ = 0 := by
  unfold intervalMap
  rw [if_pos rfl]

/-- The value of `f` at `v₀` is `1`. -/
private lemma f_v₀ {u₀ v₀ : U} (h : S.lt u₀ v₀) : intervalMap S u₀ v₀ v₀ = 1 := by
  unfold intervalMap
  rw [if_neg (fun hc => ne_of_lt S h hc.symm), if_pos rfl]

/-- If `cmb α u₀ v₀ = w` and `w ≠ u₀` then `f(w) = α`: the value is independent of the
witness, by injectivity (A:B). -/
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

/-- The mixture algebra, anchored at `u₀`: `cmb β u₀ (cmb α u₀ v₀) = cmb (β·α) u₀ v₀`. -/
private lemma cmb_cmb_left (β α : OpenUnit) (u₀ v₀ : U) :
    S.cmb β u₀ (S.cmb α u₀ v₀) = S.cmb (OpenUnit.mul β α) u₀ v₀ := by
  show S.mix (OpenUnit.oneSub β) u₀ (S.mix (OpenUnit.oneSub α) u₀ v₀)
      = S.mix (OpenUnit.oneSub (OpenUnit.mul β α)) u₀ v₀
  rw [S.mix_comm (OpenUnit.oneSub α) u₀ v₀, oneSub_oneSub, mix_comm' S, S.mix_mix,
    mix_comm' S]

/-- The mixture algebra, anchored at `v₀`:
`cmb β v₀ (cmb α u₀ v₀) = cmb (1 − β·(1−α)) u₀ v₀`. -/
private lemma cmb_cmb_right (β α : OpenUnit) (u₀ v₀ : U) :
    S.cmb β v₀ (S.cmb α u₀ v₀)
      = S.cmb (OpenUnit.oneSub (OpenUnit.mul β (OpenUnit.oneSub α))) u₀ v₀ := by
  show S.mix (OpenUnit.oneSub β) v₀ (S.mix (OpenUnit.oneSub α) u₀ v₀)
      = S.mix (OpenUnit.oneSub (OpenUnit.oneSub (OpenUnit.mul β (OpenUnit.oneSub α)))) u₀ v₀
  rw [mix_comm' S, S.mix_mix, oneSub_oneSub]

end AEaux

open TheoryOfGames.Utility AEaux

theorem solution {U : Type*} (S : UtilitySystem U) {u₀ v₀ : U}
    (h : S.lt u₀ v₀) :
    (∀ w w' : U, S.le u₀ w → S.le w v₀ → S.le u₀ w' → S.le w' v₀ → S.lt w w' →
        intervalMap S u₀ v₀ w < intervalMap S u₀ v₀ w') ∧
      (∀ (β : OpenUnit) (w : U), S.le u₀ w → S.le w v₀ → w ≠ u₀ →
        intervalMap S u₀ v₀ (S.cmb β u₀ w) = (β : ℝ) * intervalMap S u₀ v₀ w) ∧
      ∀ (β : OpenUnit) (w : U), S.le u₀ w → S.le w v₀ → w ≠ v₀ →
        intervalMap S u₀ v₀ (S.cmb β v₀ w) = 1 - (β : ℝ) + (β : ℝ) * intervalMap S u₀ v₀ w := by
  obtain ⟨hbetw, hinj, hmono⟩ := segment_mono_injective S h
  constructor
  · -- (i') monotonicity
    intro w w' hw₀ hwv hw'₀ hw'v hlt
    rcases hw₀ with rfl | hwgt
    · -- w = u₀: f(w) = 0 and f(w') > 0
      rw [f_u₀ S h]
      rcases hw'v with rfl | hw'lt
      · rw [f_v₀ S h]
        norm_num
      · have hw'lt₀ : S.lt u₀ w' := by
          rcases hw'₀ with heq | hs
          · rw [← heq] at hlt
            exact absurd hlt (gt_irrefl S u₀)
          · exact hs
        obtain ⟨α', hα'⟩ := segment_surjective S h w' hw'lt₀ hw'lt
        rw [f_eq_of_cmb S h w' α' hα' (by
          intro hc
          rw [hc] at hw'lt₀
          exact gt_irrefl S u₀ hw'lt₀)]
        exact α'.2.1
    · -- u₀ < w
      have hwltv : S.lt w v₀ := by
        rcases hwv with heqW | hsW
        · rw [heqW] at hlt hwgt
          rcases hw'v with heq | hs
          · rw [← heq] at hlt
            exact absurd hlt (gt_irrefl S w')
          · exact absurd hlt (gt_asymm S v₀ w' hs)
        · exact hsW
      obtain ⟨α, hα⟩ := segment_surjective S h w hwgt hwltv
      have hwne : w ≠ u₀ := by
        intro hc
        rw [hc] at hwgt
        exact gt_irrefl S u₀ hwgt
      rcases hw'v with rfl | hw'lt
      · -- w' = v₀
        rw [f_v₀ S h, f_eq_of_cmb S h w α hα hwne]
        exact α.2.2
      · -- u₀ < w' < v₀
        have hw'lt₀ : S.lt u₀ w' := by
          rcases hw'₀ with heq | hs
          · rw [← heq] at hlt
            exact absurd hlt (gt_asymm S w u₀ hwgt)
          · exact hs
        obtain ⟨α', hα'⟩ := segment_surjective S h w' hw'lt₀ hw'lt
        have hw'ne : w' ≠ u₀ := by
          intro hc
          rw [hc] at hw'lt₀
          exact gt_irrefl S u₀ hw'lt₀
        rw [f_eq_of_cmb S h w α hα hwne, f_eq_of_cmb S h w' α' hα' hw'ne]
        rcases lt_trichotomy (α : ℝ) (α' : ℝ) with hl | heq | hg
        · exact hl
        · have hww' : w = w' := by
            rw [← hα, ← hα', Subtype.ext heq]
          rw [← hww'] at hlt
          exact absurd hlt (gt_irrefl S w)
        · have hmono' := hmono α' α hg
          rw [hα, hα'] at hmono'
          exact absurd hmono' (gt_asymm S w' w hlt)
  · constructor
    · -- (ii')
      intro β w hw₀ hwv hwu₀
      rcases hwv with heqW | hwstrict
      · -- w = v₀
        rw [heqW, f_v₀ S h]
        rw [f_eq_of_cmb S h (S.cmb β u₀ v₀) β rfl (by
          intro hc
          have hb := (hbetw β).1
          rw [hc] at hb
          exact gt_irrefl S u₀ hb)]
        simp
      · -- u₀ < w < v₀
        have hwlt₀ : S.lt u₀ w := by
          rcases hw₀ with heq | hs
          · exact absurd heq.symm hwu₀
          · exact hs
        obtain ⟨α, hα⟩ := segment_surjective S h w hwlt₀ hwstrict
        have hwne : w ≠ u₀ := by
          intro hc
          rw [hc] at hwlt₀
          exact gt_irrefl S u₀ hwlt₀
        rw [f_eq_of_cmb S h w α hα hwne]
        have halg := cmb_cmb_left S β α u₀ v₀
        rw [hα] at halg
        rw [halg, f_eq_of_cmb S h (S.cmb (OpenUnit.mul β α) u₀ v₀)
          (OpenUnit.mul β α) rfl (by
            intro hc
            have hb := (hbetw (OpenUnit.mul β α)).1
            rw [hc] at hb
            exact gt_irrefl S u₀ hb)]
        simp [OpenUnit.mul]
    · -- (iii')
      intro β w hw₀ hwv hwv₀
      rcases hw₀ with heqW | hwstrict
      · -- w = u₀
        have hconv : S.cmb β v₀ u₀ = S.cmb (OpenUnit.oneSub β) u₀ v₀ := by
          show S.mix (OpenUnit.oneSub β) v₀ u₀
              = S.mix (OpenUnit.oneSub (OpenUnit.oneSub β)) u₀ v₀
          rw [mix_comm' S β v₀ u₀, oneSub_oneSub]
        rw [← heqW, f_u₀ S h]
        rw [hconv, f_eq_of_cmb S h (S.cmb (OpenUnit.oneSub β) u₀ v₀)
          (OpenUnit.oneSub β) rfl (by
            intro hc
            have hb := (hbetw (OpenUnit.oneSub β)).1
            rw [hc] at hb
            exact gt_irrefl S u₀ hb)]
        simp [OpenUnit.oneSub]
      · -- u₀ < w < v₀
        have hwltv : S.lt w v₀ := by
          rcases hwv with heq | hs
          · exact absurd heq hwv₀
          · exact hs
        obtain ⟨α, hα⟩ := segment_surjective S h w hwstrict hwltv
        have hwne : w ≠ u₀ := by
          intro hc
          rw [hc] at hwstrict
          exact gt_irrefl S u₀ hwstrict
        rw [f_eq_of_cmb S h w α hα hwne]
        have halg := cmb_cmb_right S β α u₀ v₀
        rw [hα] at halg
        rw [halg, f_eq_of_cmb S h
          (S.cmb (OpenUnit.oneSub (OpenUnit.mul β (OpenUnit.oneSub α))) u₀ v₀)
          (OpenUnit.oneSub (OpenUnit.mul β (OpenUnit.oneSub α))) rfl (by
            intro hc
            have hb := (hbetw (OpenUnit.oneSub (OpenUnit.mul β (OpenUnit.oneSub α)))).1
            rw [hc] at hb
            exact gt_irrefl S u₀ hb)]
        simp [OpenUnit.oneSub, OpenUnit.mul]
        ring
