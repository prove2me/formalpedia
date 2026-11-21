-- Prove2me | solution 1 for RelaxRoundPoA.half_value_utility_ge
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:25:32.068833+00:00
-- url     : https://prove2.me/submissions/6d5013ee-523f-4c4a-ab6f-29fe6a3cbbae

import Mathlib
import Definitions.Def_RelaxRoundPoA_Mechanism
import Definitions.Def_RelaxRoundPoA_IsProfile
import Definitions.Def_RelaxRoundPoA_HalfClosed
import Definitions.Def_RelaxRoundPoA_utility
import Definitions.Def_RelaxRoundPoA_IsPayYourBid
import Definitions.Def_RelaxRoundPoA_ExpFinite
import Definitions.Def_RelaxRoundPoA_IsExactMaximizer

open MeasureTheory NNReal

namespace Aux_RelaxRoundPoA_half_value_utility_ge

open RelaxRoundPoA

theorem profile_update {N : Type*} [DecidableEq N] {Ω' : Type*} (Val : N → Set (Ω' → ℝ≥0))
    (b : N → Ω' → ℝ≥0) (hb : IsProfile Val b) (i : N) (w : Ω' → ℝ≥0) (hw : w ∈ Val i) :
    IsProfile Val (Function.update b i w) := by
  intro j
  rcases eq_or_ne j i with rfl | hj
  · rw [Function.update_self]
    exact hw
  · rw [Function.update_of_ne hj]
    exact hb j

theorem sum_update {N : Type*} [Fintype N] [DecidableEq N] {Ω' : Type*}
    (b : N → Ω' → ℝ≥0) (i : N) (w : Ω' → ℝ≥0) (y : Ω') :
    ∑ j, Function.update b i w j y = w y + ∑ j ∈ Finset.univ.erase i, b j y := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  congr 1
  · rw [Function.update_self]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_erase] at hj
    rw [Function.update_of_ne hj.1]

end Aux_RelaxRoundPoA_half_value_utility_ge

open RelaxRoundPoA Aux_RelaxRoundPoA_half_value_utility_ge in
theorem solution {N : Type*} [Fintype N] [DecidableEq N] {Ω' : Type*} [MeasurableSpace Ω']
    (Val : N → Set (Ω' → ℝ≥0))
    (Feas : Set Ω') (M : Mechanism N Ω') (hhalf : HalfClosed Val) (hpay : IsPayYourBid Val M)
    (hfin : ExpFinite Val M) (hexact : IsExactMaximizer Val Feas M)
    (b : N → Ω' → ℝ≥0) (hb : IsProfile Val b) (i : N) (v b'' : Ω' → ℝ≥0) (hv : v ∈ Val i)
    (hb'' : b'' ∈ Val i) :
    utility M i (Function.update b i b'') (fun x => v x / 2) ≤
      utility M i (Function.update b i (fun x => v x / 2)) v := by
  have hvh : (fun x => v x / 2) ∈ Val i := hhalf i v hv
  have hp1 : IsProfile Val (Function.update b i b'') := profile_update Val b hb i b'' hb''
  have hp2 : IsProfile Val (Function.update b i (fun x => v x / 2)) :=
    profile_update Val b hb i _ hvh
  have hpay1 := hpay _ hp1 i
  have hpay2 := hpay _ hp2 i
  rw [Function.update_self] at hpay1 hpay2
  have i1h : Integrable (fun x => ((v x / 2 : ℝ≥0) : ℝ)) (M.outcome (Function.update b i b'')) :=
    hfin _ hp1 i _ hvh
  have i1b : Integrable (fun x => ((b'' x : ℝ≥0) : ℝ)) (M.outcome (Function.update b i b'')) :=
    hfin _ hp1 i _ hb''
  have i2h : Integrable (fun x => ((v x / 2 : ℝ≥0) : ℝ))
      (M.outcome (Function.update b i (fun x => v x / 2))) := hfin _ hp2 i _ hvh
  have G1 := hexact _ hp1
  have G2 := hexact _ hp2
  have key : ∀ x x' : Ω',
      (x ∈ Feas ∧ ∀ y ∈ Feas, ∑ j, Function.update b i b'' j y ≤ ∑ j, Function.update b i b'' j x) →
      (x' ∈ Feas ∧ ∀ y ∈ Feas, ∑ j, Function.update b i (fun x => v x / 2) j y ≤
          ∑ j, Function.update b i (fun x => v x / 2) j x') →
      ((v x / 2 : ℝ≥0) : ℝ) - ((b'' x : ℝ≥0) : ℝ) ≤ ((v x' / 2 : ℝ≥0) : ℝ) := by
    rintro x x' ⟨hx, hmax⟩ ⟨hx', hmax'⟩
    have h1 := hmax x' hx'
    have h2 := hmax' x hx
    rw [sum_update, sum_update] at h1 h2
    have h3 := add_le_add h1 h2
    have h4 : (v x / 2 + b'' x') + (∑ j ∈ Finset.univ.erase i, b j x
          + ∑ j ∈ Finset.univ.erase i, b j x')
        ≤ (b'' x + v x' / 2) + (∑ j ∈ Finset.univ.erase i, b j x
          + ∑ j ∈ Finset.univ.erase i, b j x') := by
      calc (v x / 2 + b'' x') + (∑ j ∈ Finset.univ.erase i, b j x
            + ∑ j ∈ Finset.univ.erase i, b j x')
          = (b'' x' + ∑ j ∈ Finset.univ.erase i, b j x')
            + (v x / 2 + ∑ j ∈ Finset.univ.erase i, b j x) := by ring
        _ ≤ (b'' x + ∑ j ∈ Finset.univ.erase i, b j x)
            + (v x' / 2 + ∑ j ∈ Finset.univ.erase i, b j x') := h3
        _ = (b'' x + v x' / 2) + (∑ j ∈ Finset.univ.erase i, b j x
            + ∑ j ∈ Finset.univ.erase i, b j x') := by ring
    have h5 : v x / 2 + b'' x' ≤ b'' x + v x' / 2 := le_of_add_le_add_right h4
    have h6 : ((v x / 2 + b'' x' : ℝ≥0) : ℝ) ≤ ((b'' x + v x' / 2 : ℝ≥0) : ℝ) :=
      NNReal.coe_le_coe.mpr h5
    rw [NNReal.coe_add, NNReal.coe_add] at h6
    have h7 : (0 : ℝ) ≤ ((b'' x' : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    linarith
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ∫ x', ((v x' / 2 : ℝ≥0) : ℝ) ∂(M.outcome (Function.update b i (fun x => v x / 2))) := ⟨_, rfl⟩
  have hpt : ∀ᵐ x ∂(M.outcome (Function.update b i b'')), ((v x / 2 : ℝ≥0) : ℝ) - ((b'' x : ℝ≥0) : ℝ) ≤ C := by
    filter_upwards [G1] with x hx
    have hae : ∀ᵐ x' ∂(M.outcome (Function.update b i (fun x => v x / 2))), ((v x / 2 : ℝ≥0) : ℝ) - ((b'' x : ℝ≥0) : ℝ) ≤ ((v x' / 2 : ℝ≥0) : ℝ) := by
      filter_upwards [G2] with x' hx'
      exact key x x' hx hx'
    have hconst : ∫ _x', (((v x / 2 : ℝ≥0) : ℝ) - ((b'' x : ℝ≥0) : ℝ)) ∂(M.outcome (Function.update b i (fun x => v x / 2)))
        = ((v x / 2 : ℝ≥0) : ℝ) - ((b'' x : ℝ≥0) : ℝ) := by simp
    rw [hC, ← hconst]
    exact integral_mono_ae (integrable_const _) i2h hae
  have hL : ∫ x, ((v x / 2 : ℝ≥0) : ℝ) ∂(M.outcome (Function.update b i b'')) - ∫ x, ((b'' x : ℝ≥0) : ℝ) ∂(M.outcome (Function.update b i b'')) ≤ C := by
    rw [← integral_sub i1h i1b]
    have hconst : ∫ _x, C ∂(M.outcome (Function.update b i b'')) = C := by simp
    rw [← hconst]
    exact integral_mono_ae (i1h.sub i1b) (integrable_const _) hpt
  have hR : ∫ x, ((v x : ℝ≥0) : ℝ) ∂(M.outcome (Function.update b i (fun x => v x / 2))) = 2 * C := by
    rw [hC, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    push_cast
    ring
  have hpayC : M.expPay (Function.update b i (fun x => v x / 2)) i = C := by
    rw [hpay2, hC]
  show ∫ x, ((v x / 2 : ℝ≥0) : ℝ) ∂(M.outcome (Function.update b i b''))
        - M.expPay (Function.update b i b'') i ≤
      ∫ x, ((v x : ℝ≥0) : ℝ) ∂(M.outcome (Function.update b i (fun x => v x / 2)))
        - M.expPay (Function.update b i (fun x => v x / 2)) i
  rw [hpay1, hpayC, hR]
  linarith
