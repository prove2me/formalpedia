-- Prove2me | solution 1 for RelaxRoundPoA.vcgPay_le_bid
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T02:28:00.169097+00:00
-- url     : https://prove2.me/submissions/949b7a29-9bb1-4eed-a503-cbb4cb609146

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
    vcgPay M Feas b i ≤ ∫ x, (b i x : ℝ) ∂(M.outcome b) := by
  have hint : ∀ j, Integrable (fun x => (b j x : ℝ)) (M.outcome b) :=
    fun j => hfin b hb j (b j) (hb j)
  have hsum_int : Integrable (fun x => ∑ j, (b j x : ℝ)) (M.outcome b) :=
    integrable_finsetSum _ (fun j _ => hint j)
  have herase_int : Integrable (fun x => ∑ j ∈ Finset.univ.erase i, (b j x : ℝ)) (M.outcome b) :=
    integrable_finsetSum _ (fun j _ => hint j)
  have hsplit : ∫ x, ∑ j, (b j x : ℝ) ∂(M.outcome b) =
      ∫ x, (b i x : ℝ) ∂(M.outcome b) +
        ∫ x, ∑ j ∈ Finset.univ.erase i, (b j x : ℝ) ∂(M.outcome b) := by
    rw [← integral_add (hint i) herase_int]
    congr 1
    funext x
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have hbound : ∀ y ∈ Feas, ∑ j ∈ Finset.univ.erase i, (b j y : ℝ) ≤
      ∫ x, ∑ j, (b j x : ℝ) ∂(M.outcome b) := by
    intro y hy
    have hae : ∀ᵐ x ∂(M.outcome b), (fun _ => ∑ j ∈ Finset.univ.erase i, (b j y : ℝ)) x ≤
        ∑ j, (b j x : ℝ) := by
      filter_upwards [hexact b hb] with x hx
      have h := hx.2 y hy
      have h' : ∑ j, (b j y : ℝ) ≤ ∑ j, (b j x : ℝ) := by
        rw [← NNReal.coe_sum, ← NNReal.coe_sum]
        exact_mod_cast h
      calc ∑ j ∈ Finset.univ.erase i, (b j y : ℝ) ≤ ∑ j, (b j y : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              (fun _ _ _ => NNReal.coe_nonneg _)
        _ ≤ ∑ j, (b j x : ℝ) := h'
    have := integral_mono_ae (integrable_const _) hsum_int hae
    simpa [integral_const] using this
  haveI : (ae (M.outcome b)).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero _)
  obtain ⟨x0, hx0⟩ := (hexact b hb).exists
  have hsup : sSup ((fun y => ∑ j ∈ Finset.univ.erase i, (b j y : ℝ)) '' Feas) ≤
      ∫ x, ∑ j, (b j x : ℝ) ∂(M.outcome b) := by
    apply csSup_le (Set.Nonempty.image _ ⟨x0, hx0.1⟩)
    rintro _ ⟨y, hy, rfl⟩
    exact hbound y hy
  unfold vcgPay
  linarith
