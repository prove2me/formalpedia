-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_trdeg_upperQuot_3c97414c0032
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:22:41.612975+00:00
-- url     : https://prove2.me/submissions/7b88a46e-e536-4881-b031-2f742ecb23b7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_uMat_diag_9ca96a409312
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_card_UIdx_b14733848e20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_isAlgebraic_uMat_d1e54cce0458

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
variable (F : Type) [Field F] (n : ℕ)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
theorem _root_.solution :
    Algebra.trdeg F (UpperQuot F n) = ((flagDim n + (n - 1) : ℕ) : Cardinal) := by
  set ι := Ideal.kerLiftAlg ((toUpper F n).comp (flagMinorMap F n))
  let _ : Algebra (UpperQuot F n) (MvPolynomial (UIdx n) F) := ι.toRingHom.toAlgebra
  have : IsScalarTower F (UpperQuot F n) (MvPolynomial (UIdx n) F) :=
    IsScalarTower.of_algebraMap_eq fun c => (ι.commutes c).symm
  have : FaithfulSMul F (UpperQuot F n) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap F (UpperQuot F n)).injective
  have : FaithfulSMul (UpperQuot F n) (MvPolynomial (UIdx n) F) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (Ideal.kerLiftAlg_injective _)
  have hX : ∀ u : UIdx n, IsAlgebraic (UpperQuot F n) (X u : MvPolynomial (UIdx n) F) := by
    rintro (⟨⟨r, c⟩, h⟩ | r)
    · have e : (X (Sum.inl ⟨(r, c), h⟩) : MvPolynomial (UIdx n) F) = uMat F n r c := by
        simp [uMat, h]
      rw [e]
      have hr : r.val < n - 1 := by
        have := c.2
        simp only [Fin.lt_def] at h
        omega
      exact isAlgebraic_uMat F n ⟨r.val, hr⟩ c (le_of_lt h)
    · have hr := r.2
      rw [← uMat_diag F r.val (by omega)]
      exact isAlgebraic_uMat F n r _ le_rfl
  have : Algebra.IsAlgebraic (UpperQuot F n) (MvPolynomial (UIdx n) F) := by
    have hall : ∀ x : MvPolynomial (UIdx n) F,
        x ∈ Subalgebra.algebraicClosure (UpperQuot F n) (MvPolynomial (UIdx n) F) := by
      intro x
      induction x using MvPolynomial.induction_on with
      | C a =>
        rw [← MvPolynomial.algebraMap_eq, IsScalarTower.algebraMap_apply F (UpperQuot F n)]
        exact isAlgebraic_algebraMap _
      | add p q hp hq => exact Subalgebra.add_mem _ hp hq
      | mul_X p u hp => exact Subalgebra.mul_mem _ hp (hX u)
    exact ⟨fun x => hall x⟩
  have h := trdeg_add_eq F (UpperQuot F n) (A := MvPolynomial (UIdx n) F)
  rw [trdeg_eq_zero (R := UpperQuot F n) (A := MvPolynomial (UIdx n) F), add_zero, MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype, card_UIdx,
    Cardinal.lift_natCast] at h
  exact h
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
