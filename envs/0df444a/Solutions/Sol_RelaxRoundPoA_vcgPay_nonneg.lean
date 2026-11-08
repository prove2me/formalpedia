-- Prove2me | solution 1 for RelaxRoundPoA.vcgPay_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:47:24.862212+00:00
-- url     : https://prove2.me/submissions/d4dde3e5-fff6-4902-bbe8-e157f032ff98

import Mathlib
import Definitions.Def_RelaxRoundPoA_Mechanism
import Definitions.Def_RelaxRoundPoA_IsProfile
import Definitions.Def_RelaxRoundPoA_ExpFinite
import Definitions.Def_RelaxRoundPoA_IsExactMaximizer
import Definitions.Def_RelaxRoundPoA_vcgPay

open MeasureTheory NNReal

open RelaxRoundPoA in
theorem solution {N : Type*} [Fintype N] [DecidableEq N] {Ω' : Type*} [MeasurableSpace Ω']
    (Val : N → Set (Ω' → ℝ≥0))
    (Feas : Set Ω') (M : Mechanism N Ω') (hfin : ExpFinite Val M)
    (hexact : IsExactMaximizer Val Feas M) (b : N → Ω' → ℝ≥0) (hb : IsProfile Val b) (i : N) :
    0 ≤ vcgPay M Feas b i := by
  have hae := hexact b hb
  obtain ⟨x0, hx0F, hx0⟩ := hae.exists
  have hbd : ∀ y ∈ Feas, ∑ j ∈ Finset.univ.erase i, (b j y : ℝ) ≤ ∑ j, (b j x0 : ℝ) := by
    intro y hy
    have h1 : ∑ j ∈ Finset.univ.erase i, (b j y : ℝ) ≤ ∑ j, (b j y : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun j _ _ => (b j y).2)
    have h2 : ((∑ j, b j y : ℝ≥0) : ℝ) ≤ ((∑ j, b j x0 : ℝ≥0) : ℝ) :=
      NNReal.coe_le_coe.mpr (hx0 y hy)
    push_cast at h2
    linarith
  have hBdd : BddAbove ((fun y => ∑ j ∈ Finset.univ.erase i, (b j y : ℝ)) '' Feas) := by
    refine ⟨∑ j, (b j x0 : ℝ), ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hbd y hy
  have hint : Integrable (fun x => ∑ j ∈ Finset.univ.erase i, (b j x : ℝ)) (M.outcome b) :=
    integrable_finset_sum _ (fun j _ => hfin b hb j (b j) (hb j))
  have hle : ∫ x, ∑ j ∈ Finset.univ.erase i, (b j x : ℝ) ∂(M.outcome b) ≤
      ∫ _x, sSup ((fun y => ∑ j ∈ Finset.univ.erase i, (b j y : ℝ)) '' Feas) ∂(M.outcome b) := by
    refine integral_mono_ae hint (integrable_const _) ?_
    filter_upwards [hae] with x hx
    exact le_csSup hBdd ⟨x, hx.1, rfl⟩
  rw [integral_const, probReal_univ, one_smul] at hle
  unfold vcgPay
  linarith
