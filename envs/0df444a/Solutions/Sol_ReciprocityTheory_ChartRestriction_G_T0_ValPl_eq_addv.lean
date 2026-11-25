-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValPl.eq_addv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:18:36.53891+00:00
-- url     : https://prove2.me/submissions/1cbda37c-70fa-4acf-9bfa-3bc8fd109dbc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_wt_add_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_addv_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.ValPl
open IsDedekindDomain WithZero IsLocalRing
variable {S L : Type*} [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] (v : HeightOneSpectrum S)
namespace ReciprocityTheory.ChartRestriction.G.T0.ValPl
theorem _root_.solution (w : AddValuation L (WithTop ℤ)) (hw : IsNormDiscrete w)
    (h0 : ∀ s : S, 0 ≤ w (algebraMap S L s))
    (hQ : ∀ s : S, 0 < w (algebraMap S L s) ↔ s ∈ v.asIdeal) : w = addv L v := by
  have hunit : ∀ d : S, d ∉ v.asIdeal → w (algebraMap S L d) = 0 := fun d hd =>
    le_antisymm (not_lt.1 (mt (hQ d).1 hd)) (h0 d)
  have hint : ∀ x : L, v.valuation L x ≤ 1 → 0 ≤ w x := by
    intro x hx
    obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (v := v) x hx
    have h := congrArg w hnd
    rw [AddValuation.map_mul, hunit d d.2, add_zero] at h
    rw [h]; exact h0 n
  have heq1 : ∀ x : L, x ≠ 0 → v.valuation L x = 1 → w x = 0 := by
    intro x hx h1
    have h2 : v.valuation L x⁻¹ = 1 := by rw [map_inv₀, h1, inv_one]
    have hs : w x + w x⁻¹ = 0 := by
      rw [← AddValuation.map_mul, mul_inv_cancel₀ hx, AddValuation.map_one]
    exact wt_add_eq_zero (hint x h1.le) (hint _ h2.le) hs
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  set p := algebraMap S L π with hp_def
  have hp : v.valuation L p = exp (-1 : ℤ) := by rw [hp_def, HeightOneSpectrum.valuation_of_algebraMap, hπ]
  have hp0 : p ≠ 0 := by
    intro h; rw [h, map_zero] at hp; exact exp_ne_zero hp.symm
  have hπQ : π ∈ v.asIdeal := by
    rw [← v.intValuation_lt_one_iff_mem, hπ, ← exp_zero, exp_lt_exp]; omega
  obtain ⟨a0, ha0⟩ : ∃ a0 : ℤ, w p = a0 := WithTop.ne_top_iff_exists.mp (hw.1 p hp0) |>.imp
    fun _ h => h.symm
  have hpinv : w p⁻¹ = ((-a0 : ℤ) : WithTop ℤ) := by
    have hs : w p + w p⁻¹ = 0 := by
      rw [← AddValuation.map_mul, mul_inv_cancel₀ hp0, AddValuation.map_one]
    have hne : w p⁻¹ ≠ ⊤ := hw.1 _ (inv_ne_zero hp0)
    obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [← hb] at hs ⊢
    rw [ha0] at hs
    have : a0 + b = 0 := by exact_mod_cast hs
    congr 1; omega
  have hzpow : ∀ n : ℤ, w (p ^ n) = ((n * a0 : ℤ) : WithTop ℤ) := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ n ih =>
      rw [zpow_add_one₀ hp0, AddValuation.map_mul, ih, ha0, ← WithTop.coe_add]; congr 1; ring
    | pred n ih =>
      rw [zpow_sub_one₀ hp0, AddValuation.map_mul, ih, hpinv, ← WithTop.coe_add]; congr 1; ring
  have hform : ∀ x : L, x ≠ 0 → w x = (((-log (v.valuation L x)) * a0 : ℤ) : WithTop ℤ) := by
    intro x hx
    have hvx : v.valuation L x ≠ 0 := by simpa using hx
    set k := log (v.valuation L x)
    have hy : v.valuation L (x * p ^ k) = 1 := by
      rw [map_mul, map_zpow₀, hp, ← exp_log hvx, ← exp_zsmul, ← exp_add]
      simp [k]
    have hy0 : x * p ^ k ≠ 0 := mul_ne_zero hx (zpow_ne_zero _ hp0)
    have h := heq1 _ hy0 hy
    rw [AddValuation.map_mul, hzpow] at h
    have hne : w x ≠ ⊤ := hw.1 x hx
    obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [← hb] at h ⊢
    have : b + k * a0 = 0 := by exact_mod_cast h
    congr 1; linarith
  have ha1 : a0 = 1 := by
    obtain ⟨z, hz⟩ := hw.2
    have hz0 : z ≠ 0 := by
      intro h; rw [h, AddValuation.map_zero] at hz; exact WithTop.top_ne_coe hz
    rw [hform z hz0] at hz
    have h1 : (-log (v.valuation L z)) * a0 = 1 := by exact_mod_cast hz
    have hpos : 0 < a0 := by
      have := (hQ π).mpr hπQ
      rw [← hp_def, ha0] at this; exact_mod_cast this
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' h1 with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  apply AddValuation.ext
  intro x
  by_cases hx : x = 0
  · subst hx; simp
  rw [hform x hx, addv_apply v hx, ha1, mul_one]
end ReciprocityTheory.ChartRestriction.G.T0.ValPl
