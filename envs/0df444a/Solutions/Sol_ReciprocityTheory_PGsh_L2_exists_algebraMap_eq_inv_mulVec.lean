-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.exists_algebraMap_eq_inv_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:31:19.15971+00:00
-- url     : https://prove2.me/submissions/14bf40dc-ed17-4be4-b8f6-0b4beff33c67

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetLeOneOfEntriesIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (AA : HopfOrder (C := C) R N) (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C)
    (hβ : IsUnit β.det)
    (hAK : AA.carrier.map (resK (R := R) K) = Submodule.span R (Set.range fun j k => β k j))
    {h : K → C} (hh : h ∈ AA.carrier.map (resK (R := R) K)) (l : K) :
    ∃ r : R, algebraMap R C r = (β⁻¹ *ᵥ h) l := by
  rw [hAK] at hh
  induction hh using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨j, rfl⟩ := hg
    have e : β⁻¹ *ᵥ (fun k => β k j) = Pi.single j 1 := by
      ext l'
      have := congrFun (congrFun (Matrix.nonsing_inv_mul β hβ) l') j
      simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.one_apply, Pi.single_apply,
        eq_comm] using this
    rw [e]
    by_cases hl : l = j
    · exact ⟨1, by simp [hl]⟩
    · exact ⟨0, by simp [hl]⟩
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨r, hr⟩ := ha
    obtain ⟨s, hs⟩ := hb
    exact ⟨r + s, by simp [Matrix.mulVec_add, hr, hs]⟩
  | smul c a _ ha =>
    obtain ⟨r, hr⟩ := ha
    exact ⟨c * r, by rw [Matrix.mulVec_smul]; simp [hr, Algebra.smul_def]⟩
end ReciprocityTheory.PGsh.L2
