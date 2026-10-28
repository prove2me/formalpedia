-- Prove2me | solution 1 for StochConvexProg.Duality.eq_4_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:52:45.179921+00:00
-- url     : https://prove2.me/submissions/d7516a13-0855-409c-87b1-aff20253b183

import Mathlib
import Definitions.Def_StochConvexProg_Duality_Problem
import Definitions.Def_StochConvexProg_Duality_Dual

open MeasureTheory

namespace Aux_StochConvexProg_Duality_eq_4_1

/-- Adding a real constant is an order automorphism of `EReal`. -/
noncomputable def addIso (c : ℝ) : EReal ≃o EReal where
  toFun e := (c : EReal) + e
  invFun e := ((-c : ℝ) : EReal) + e
  left_inv e := by
    show ((-c : ℝ) : EReal) + ((c : EReal) + e) = e
    rw [← add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, zero_add]
  right_inv e := by
    show (c : EReal) + (((-c : ℝ) : EReal) + e) = e
    rw [← add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, zero_add]
  map_rel_iff' := by
    intro a b
    show (c : EReal) + a ≤ (c : EReal) + b ↔ a ≤ b
    constructor
    · intro h
      have h2 := add_le_add (le_refl ((-c : ℝ) : EReal)) h
      rwa [← add_assoc, ← add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero,
        zero_add, zero_add] at h2
    · intro h
      exact add_le_add le_rfl h

theorem add_iInf {ι : Sort*} (c : ℝ) (f : ι → EReal) :
    (c : EReal) + ⨅ i, f i = ⨅ i, ((c : EReal) + f i) :=
  (addIso c).map_iInf f

theorem neg_iSup {ι : Sort*} (g : ι → EReal) : -(⨆ i, g i) = ⨅ i, -(g i) := by
  apply le_antisymm
  · exact le_iInf fun i => EReal.neg_le_neg_iff.mpr (le_iSup g i)
  · rw [EReal.le_neg]
    exact iSup_le fun i => EReal.le_neg.mpr (iInf_le (fun i => -(g i)) i)

end Aux_StochConvexProg_Duality_eq_4_1

open StochConvexProg.Duality Aux_StochConvexProg_Duality_eq_4_1 in
theorem solution {S : Type*} [MeasurableSpace S] {σ : Measure S}
    [IsProbabilityMeasure σ] {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂)
    (y : YSpace σ m₁ m₂) :
    pr.dualObj y = (⨅ u : USpace σ m₁ m₂, ((pairUY u y : ℝ) : EReal) + pr.phi u) ∧
      pr.dualObj y = -conjU pr.phi (-y) := by
  have h1 : pr.dualObj y = (⨅ u : USpace σ m₁ m₂, ((pairUY u y : ℝ) : EReal) + pr.phi u) := by
    unfold Problem.dualObj Problem.Lag Problem.phi
    rw [iInf_comm]
    congr 1
    funext u
    rw [add_iInf]
  refine ⟨h1, ?_⟩
  rw [h1]
  have hneg : ∀ u : USpace σ m₁ m₂, pairUY u (-y) = -pairUY u y := by
    intro u
    unfold pairUY
    have hint : ∫ s, u.2 s ⬝ᵥ (-y).2 s ∂σ = -∫ s, u.2 s ⬝ᵥ y.2 s ∂σ := by
      rw [← integral_neg]
      refine integral_congr_ae ?_
      have : ((-y).2 : S → Fin m₂ → ℝ) =ᵐ[σ] -(y.2 : S → Fin m₂ → ℝ) := by
        rw [Prod.snd_neg]
        exact Lp.coeFn_neg y.2
      filter_upwards [this] with s hs
      rw [hs, Pi.neg_apply, dotProduct_neg]
    rw [hint, Prod.fst_neg, dotProduct_neg]
    ring
  unfold conjU
  rw [neg_iSup]
  congr 1
  funext u
  rw [hneg, EReal.neg_sub (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)),
    EReal.coe_neg, neg_neg]
