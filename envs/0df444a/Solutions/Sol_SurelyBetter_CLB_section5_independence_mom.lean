-- Prove2me | solution 1 for SurelyBetter.CLB.section5_independence_mom
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:04:26.178593+00:00
-- url     : https://prove2.me/submissions/dd5460c3-beb7-4f0c-ad11-364239743bb7

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_SurelyBetter_CLB_Model

open SurelyBetter.CLB

namespace IndependenceMOMAux

/-- Independence compares every pair of distinct mixture weights by the same endpoint order. -/
theorem compare_mix {S : Type*} (V : (S → ℝ) → ℝ) (G : Set (S → ℝ))
    (hG : Convex ℝ G) (hind : Independence V G)
    (f g : S → ℝ) (hf : f ∈ G) (hg : g ∈ G)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    (V (mix a f g) ≤ V (mix b f g) ↔ V g ≤ V f) ∧
    (V (mix b f g) ≤ V (mix a f g) ↔ V f ≤ V g) := by
  by_cases hd : b - a < 1
  · have hden : 0 < 1 - (b - a) := sub_pos.mpr hd
    have ht0 : 0 ≤ a / (1 - (b - a)) := div_nonneg ha (le_of_lt hden)
    have ht1 : a / (1 - (b - a)) ≤ 1 := (div_le_one hden).2 (by linarith)
    let h := mix (a / (1 - (b - a))) f g
    have hh : h ∈ G := hG hf hg ht0 (sub_nonneg.mpr ht1) (by ring)
    have hlo : mix (b - a) g h = mix a f g := by
      ext s
      dsimp [h, mix]
      field_simp
      ring
    have hhi : mix (b - a) f h = mix b f g := by
      ext s
      dsimp [h, mix]
      field_simp
      ring
    constructor
    · simpa only [hlo, hhi] using
        (hind f hf g hg h hh (b - a) ⟨sub_pos.mpr hab, le_of_lt hd⟩).symm
    · simpa only [hlo, hhi] using
        (hind g hg f hf h hh (b - a) ⟨sub_pos.mpr hab, le_of_lt hd⟩).symm
  · have ha0 : a = 0 := by linarith
    have hb1 : b = 1 := by linarith
    subst a b
    simp [mix]

end IndependenceMOMAux

theorem solution {S : Type*} [Fintype S] (V : (S → ℝ) → ℝ)
    (G : Set (S → ℝ)) (hG : Convex ℝ G) (hmon : StateMonotone V G) (hind : Independence V G) :
    MOMOn V G := by
  intro f hf f' hf' g hg hff' a ha b hb
  by_cases hab : a ≤ b
  · simpa only [inf_eq_left.mpr hab, sup_eq_right.mpr hab] using And.intro ha hb
  · have hba : b < a := lt_of_not_ge hab
    have hcmp := IndependenceMOMAux.compare_mix V G hG hind f g hf hg
      b a hb.1.1 hba ha.1.2
    have hcmp' := IndependenceMOMAux.compare_mix V G hG hind f' g hf' hg
      b a hb.1.1 hba ha.1.2
    have hgf : V g ≤ V f := hcmp.1.mp (ha.2 b hb.1)
    have hfg : V f' ≤ V g := hcmp'.2.mp (hb.2 a ha.1)
    have hmono : V f ≤ V f' := hmon f hf f' hf' hff'
    have hnew : b ∈ optMix V f g :=
      ⟨hb.1, fun c hc => (ha.2 c hc).trans (hcmp.2.mpr (hmono.trans hfg))⟩
    have hnew' : a ∈ optMix V f' g :=
      ⟨ha.1, fun c hc => (hb.2 c hc).trans (hcmp'.1.mpr (hgf.trans hmono))⟩
    simpa only [inf_eq_right.mpr hba.le, sup_eq_left.mpr hba.le] using And.intro hnew hnew'
