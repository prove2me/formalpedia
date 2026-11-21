-- Prove2me | solution 1 for RelaxRoundPoA.vcg_truthful
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:33:53.849258+00:00
-- url     : https://prove2.me/submissions/317981e9-62fc-4572-8046-3b9f6c4e6f5a

import Mathlib
import Definitions.Def_RelaxRoundPoA_Mechanism
import Definitions.Def_RelaxRoundPoA_IsProfile
import Definitions.Def_RelaxRoundPoA_utility
import Definitions.Def_RelaxRoundPoA_ExpFinite
import Definitions.Def_RelaxRoundPoA_IsExactMaximizer
import Definitions.Def_RelaxRoundPoA_vcgPay
import Definitions.Def_RelaxRoundPoA_vcgMech

open MeasureTheory NNReal

namespace Aux_RelaxRoundPoA_vcg_truthful

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

theorem sum_erase_update {N : Type*} [Fintype N] [DecidableEq N] {Ω' : Type*}
    (b : N → Ω' → ℝ≥0) (i : N) (w : Ω' → ℝ≥0) (y : Ω') :
    ∑ j ∈ Finset.univ.erase i, ((Function.update b i w j y : ℝ≥0) : ℝ)
      = ∑ j ∈ Finset.univ.erase i, ((b j y : ℝ≥0) : ℝ) := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

end Aux_RelaxRoundPoA_vcg_truthful

open RelaxRoundPoA Aux_RelaxRoundPoA_vcg_truthful in
theorem solution {N : Type*} [Fintype N] [DecidableEq N] {Ω' : Type*} [MeasurableSpace Ω']
    (Val : N → Set (Ω' → ℝ≥0))
    (Feas : Set Ω') (M : Mechanism N Ω') (hfin : ExpFinite Val M)
    (hexact : IsExactMaximizer Val Feas M) (b : N → Ω' → ℝ≥0) (hb : IsProfile Val b) (i : N)
    (w w'' : Ω' → ℝ≥0) (hw : w ∈ Val i) (hw'' : w'' ∈ Val i) :
    utility (vcgMech M Feas) i (Function.update b i w'') w ≤
      utility (vcgMech M Feas) i (Function.update b i w) w := by
  have hp1 : IsProfile Val (Function.update b i w'') := profile_update Val b hb i w'' hw''
  have hp2 : IsProfile Val (Function.update b i w) := profile_update Val b hb i w hw
  -- integrability of the welfare `w + B` under both outcome laws
  have hint : ∀ β, IsProfile Val β → (∀ j, j ≠ i → β j = b j) →
      Integrable (fun x => ((w x : ℝ≥0) : ℝ)) (M.outcome β) ∧
      Integrable (fun x => ∑ j ∈ Finset.univ.erase i, ((b j x : ℝ≥0) : ℝ)) (M.outcome β) := by
    intro β hβ hβb
    refine ⟨hfin β hβ i w hw, ?_⟩
    refine integrable_finsetSum _ (fun j hj => ?_)
    have := hfin β hβ j (b j) (hb j)
    exact this
  have hoth1 : ∀ j, j ≠ i → Function.update b i w'' j = b j :=
    fun j hj => Function.update_of_ne hj _ _
  have hoth2 : ∀ j, j ≠ i → Function.update b i w j = b j :=
    fun j hj => Function.update_of_ne hj _ _
  obtain ⟨Iw1, IB1⟩ := hint _ hp1 hoth1
  obtain ⟨Iw2, IB2⟩ := hint _ hp2 hoth2
  have G1 := hexact _ hp1
  have G2 := hexact _ hp2
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ∫ x', (((w x' : ℝ≥0) : ℝ)
      + ∑ j ∈ Finset.univ.erase i, ((b j x' : ℝ≥0) : ℝ)) ∂(M.outcome (Function.update b i w)) :=
    ⟨_, rfl⟩
  have key : ∀ x x' : Ω', x ∈ Feas →
      (x' ∈ Feas ∧ ∀ y ∈ Feas, ∑ j, Function.update b i w j y ≤ ∑ j, Function.update b i w j x') →
      ((w x : ℝ≥0) : ℝ) + ∑ j ∈ Finset.univ.erase i, ((b j x : ℝ≥0) : ℝ)
        ≤ ((w x' : ℝ≥0) : ℝ) + ∑ j ∈ Finset.univ.erase i, ((b j x' : ℝ≥0) : ℝ) := by
    rintro x x' hx ⟨_, hmax⟩
    have h1 := hmax x hx
    rw [sum_update, sum_update] at h1
    have h2 := NNReal.coe_le_coe.mpr h1
    push_cast at h2
    exact h2
  have hpt : ∀ᵐ x ∂(M.outcome (Function.update b i w'')),
      ((w x : ℝ≥0) : ℝ) + ∑ j ∈ Finset.univ.erase i, ((b j x : ℝ≥0) : ℝ) ≤ C := by
    filter_upwards [G1] with x hx
    have hae : ∀ᵐ x' ∂(M.outcome (Function.update b i w)),
        ((w x : ℝ≥0) : ℝ) + ∑ j ∈ Finset.univ.erase i, ((b j x : ℝ≥0) : ℝ)
          ≤ ((w x' : ℝ≥0) : ℝ) + ∑ j ∈ Finset.univ.erase i, ((b j x' : ℝ≥0) : ℝ) := by
      filter_upwards [G2] with x' hx'
      exact key x x' hx.1 hx'
    have hconst : ∫ _x', (((w x : ℝ≥0) : ℝ) + ∑ j ∈ Finset.univ.erase i, ((b j x : ℝ≥0) : ℝ))
          ∂(M.outcome (Function.update b i w))
        = ((w x : ℝ≥0) : ℝ) + ∑ j ∈ Finset.univ.erase i, ((b j x : ℝ≥0) : ℝ) := by simp
    rw [hC, ← hconst]
    exact integral_mono_ae (integrable_const _) (Iw2.add IB2) hae
  have hL : ∫ x, ((w x : ℝ≥0) : ℝ) ∂(M.outcome (Function.update b i w''))
      + ∫ x, ∑ j ∈ Finset.univ.erase i, ((b j x : ℝ≥0) : ℝ) ∂(M.outcome (Function.update b i w''))
      ≤ C := by
    rw [← integral_add Iw1 IB1]
    have hconst : ∫ _x, C ∂(M.outcome (Function.update b i w'')) = C := by simp
    rw [← hconst]
    exact integral_mono_ae (Iw1.add IB1) (integrable_const _) hpt
  have hR : ∫ x, ((w x : ℝ≥0) : ℝ) ∂(M.outcome (Function.update b i w))
      + ∫ x, ∑ j ∈ Finset.univ.erase i, ((b j x : ℝ≥0) : ℝ) ∂(M.outcome (Function.update b i w))
      = C := by
    rw [hC, integral_add Iw2 IB2]
  show ∫ x, ((w x : ℝ≥0) : ℝ) ∂(M.outcome (Function.update b i w''))
        - vcgPay M Feas (Function.update b i w'') i ≤
      ∫ x, ((w x : ℝ≥0) : ℝ) ∂(M.outcome (Function.update b i w))
        - vcgPay M Feas (Function.update b i w) i
  unfold vcgPay
  simp only [sum_erase_update]
  linarith
