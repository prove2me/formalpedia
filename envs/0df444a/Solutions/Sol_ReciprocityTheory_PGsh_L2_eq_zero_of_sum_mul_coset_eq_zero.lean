-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.eq_zero_of_sum_mul_coset_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:57.287451+00:00
-- url     : https://prove2.me/submissions/b25942bd-fc2f-4604-8e37-0fdd387692ea

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsFamilyValuationDetEqOne
import Definitions.Def_ReciprocityTheory_DualLattices_MemMapAugmentationIdealComapPullbackQuotient
import Theorems.Thm_ReciprocityTheory_PGsh_L2_cosetCoordinates_expand


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
variable (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
  [DecidablePred (· ∈ K)] (β : Matrix K K C) (hβ : IsUnit β.det)
  (hAK : AA.carrier.map (resK (R := R) K) = Submodule.span R (Set.range fun j k => β k j))
  (f : K → N → C) (hf : ∀ j, f j ∈ AA.carrier) (hdet : ∀ x, v (h3mm K β f x).det = 1)
include hβ hdet
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (x : N) (c : K → C) (h : ∀ k : K, ∑ j, c j * f j (x + k) = 0) : c = 0 := by
  have hM : (h3mm K β f x).det ≠ 0 := by
    intro h0
    have := hdet x
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hw : β *ᵥ (c ᵥ* h3mm K β f x) = 0 := by
    funext k
    rw [Pi.zero_apply, ← h k]
    have e : ∀ j, f j (x + k) = ∑ l, β k l * h3mm K β f x j l := fun j => by
      rw [cosetCoordinates_expand K β hβ (f j) x k]
      rfl
    simp only [e]
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hw0 : c ᵥ* h3mm K β f x = 0 := by
    have := congrArg (β⁻¹ *ᵥ ·) hw
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul β hβ] using this
  by_contra hc
  exact hM (Matrix.exists_vecMul_eq_zero_iff.mp ⟨c, hc, hw0⟩)
end ReciprocityTheory.PGsh.L2
