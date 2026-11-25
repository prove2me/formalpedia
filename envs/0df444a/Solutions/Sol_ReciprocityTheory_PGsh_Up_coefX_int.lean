-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.coefX_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:06:49.7756+00:00
-- url     : https://prove2.me/submissions/7bef89ec-3c0e-4f4b-b747-c72dcf0a20e6

import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatement
import Definitions.Def_ReciprocityTheory_DualLattices_PowMemCarrier
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenCokerDet
import Definitions.Def_ReciprocityTheory_DualLattices_EigenLiftsFrobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (D : Lifts H U X) (hdet : (valM D).det ≠ 0)
    (hbasis : H.AA.carrier = Submodule.span R (Set.range fun (α : Nb p g) (y : Nb p g) =>
      ∏ j, (algebraMap R C (D.ε j) * D.u j y) ^ (α j).val))
    {f : Nb p g → C} (hf : f ∈ H.AA.carrier) :
    ∃ r : Nb p g → R, coefX D f = algebraMap R C ∘ r := by
  rw [hbasis] at hf
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hf
  refine ⟨r, ?_⟩
  have hfv : f = valM D *ᵥ (algebraMap R C ∘ r) := by
    rw [← hr]
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, valM, Matrix.of_apply,
      Function.comp_apply, monX, xL, Algebra.smul_def]
    exact Finset.sum_congr rfl fun α _ => mul_comm _ _
  rw [coefX, hfv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]
end ReciprocityTheory.PGsh.Up
