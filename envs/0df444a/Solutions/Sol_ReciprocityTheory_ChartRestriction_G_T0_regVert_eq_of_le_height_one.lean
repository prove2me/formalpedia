-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.regVert_eq_of_le_height_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:32:13.011431+00:00
-- url     : https://prove2.me/submissions/b624e55a-91f7-4a62-8fad-65122f72ddeb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegAVpt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegVert

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open IsLocalRing
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {A : Type*} [CommRing A] [IsDomain A] {Q P : Ideal A} [Q.IsPrime]
    [P.IsPrime] (hQ : Q ≠ ⊥) (hQP : Q ≤ P) (hP : P.height = 1) : Q = P := by
  by_contra hne
  have hlt : Q < P := lt_of_le_of_ne hQP hne
  have hbot : (⊥ : Ideal A) < Q := bot_lt_iff_ne_bot.mpr hQ
  have hQle : Q.height ≤ 1 := hP ▸ Ideal.height_mono hQP
  have hQfin : Q.height ≠ ⊤ := ne_top_of_le_ne_top (by simp) hQle
  haveI : Q.FiniteHeight := ⟨Or.inr hQfin⟩
  haveI : (⊥ : Ideal A).FiniteHeight := ⟨Or.inr (by simp)⟩
  have h1 : (⊥ : Ideal A).height + 1 ≤ Q.height := by
    first
    | exact ENat.add_one_le_of_lt (Ideal.height_strict_mono_of_isPrime hbot)
    | exact Order.add_one_le_of_lt (Ideal.height_strict_mono_of_isPrime hbot)
  have h2 : Q.height + 1 ≤ P.height := by
    first
    | exact ENat.add_one_le_of_lt (Ideal.height_strict_mono_of_isPrime hlt)
    | exact Order.add_one_le_of_lt (Ideal.height_strict_mono_of_isPrime hlt)
  rw [hP] at h2
  have h3 : (2 : ℕ∞) ≤ 1 := by
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ (⊥ : Ideal A).height + 1 + 1 := by gcongr; simp
      _ ≤ Q.height + 1 := by gcongr
      _ ≤ 1 := h2
  exact absurd h3 (by norm_num)
end ReciprocityTheory.ChartRestriction.G.T0
