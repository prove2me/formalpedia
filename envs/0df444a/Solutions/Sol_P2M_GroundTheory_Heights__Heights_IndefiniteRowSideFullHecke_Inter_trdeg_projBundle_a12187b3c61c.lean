-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_trdeg_projBundle_a12187b3c61c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:41:02.619067+00:00
-- url     : https://prove2.me/submissions/a325e23e-1530-4621-8e4a-b395d80d4177

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_mul_transpose_eq_one_d14d1218bc3d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projBundleMap_rename_inlV_2f22a6c9fac6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_algebraMap_int_injective_bbfc0045ba62
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projBundleMap_X_inr_7730eace2592


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {K : Type} {ι : K → Type}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution (P : Ideal (MRing ι)) [P.IsPrime] (hPz : IsHorizontal P) {N1 n : ℕ}
    (B : Matrix (Fin n) (Fin N1) (FnField P)) (hB : LinearIndependent (FnField P) B) :
    Algebra.trdeg ℤ (MRing (PBlk ι N1) ⧸ projBundleIdeal P B) =
      Algebra.trdeg ℤ (MRing ι ⧸ P) + n := by
  classical
  set F := projBundleAlgHom P B
  have hker : RingHom.ker F = projBundleIdeal P B := rfl
  let e : (MRing (PBlk ι N1) ⧸ projBundleIdeal P B) ≃ₐ[ℤ] F.range :=
    AlgEquiv.ofRingEquiv (f := ((Ideal.quotientEquivAlgOfEq ℤ hker.symm).trans
      (Ideal.quotientKerEquivRange F)).toRingEquiv) fun x => Subtype.ext (by simp)
  rw [AlgEquiv.trdeg_eq (R := ℤ) (A := MRing (PBlk ι N1) ⧸ projBundleIdeal P B) (A' := F.range) e]
  set S := F.range
  have hmemS : ∀ g : MRing ι,
      (C (algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P g)) : MvPolynomial (Fin n) (FnField P)) ∈ S :=
    fun g => ⟨rename (inlV (ι₂ := fun _ : Unit => Fin N1)) g, projBundleMap_rename_inlV P B g⟩
  have hlin : ∀ j, (∑ a, C (B a j) * X a : MvPolynomial (Fin n) (FnField P)) ∈ S :=
    fun j => ⟨X ⟨Sum.inr (), j⟩, projBundleMap_X_inr P B () j⟩
  have halgS : ∀ x ∈ S, IsAlgebraic S x := fun x hx => isAlgebraic_algebraMap (⟨x, hx⟩ : S)
  have halgC : ∀ φ : FnField P, IsAlgebraic S (C φ : MvPolynomial (Fin n) (FnField P)) := by
    intro φ
    obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := MRing ι ⧸ P) φ
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
    have hs0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := FnField P) hs
    have hC0 : (C (algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P s)) :
        MvPolynomial (Fin n) (FnField P)) ≠ 0 := by
      rw [Ne, C_eq_zero]
      exact hs0
    refine IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hC0) (halgS _ (hmemS s)) ?_
    rw [← C_mul, mul_div_cancel₀ _ hs0]
    exact halgS _ (hmemS a)
  obtain ⟨D, hD⟩ := exists_mul_transpose_eq_one B hB
  have halgX : ∀ b, IsAlgebraic S (X b : MvPolynomial (Fin n) (FnField P)) := by
    intro b
    have h1 : ∀ a, ∑ j, D b j * B a j = if b = a then 1 else 0 := fun a => by
      have := congrFun (congrFun hD b) a
      simpa [Matrix.mul_apply, Matrix.one_apply] using this
    have hX : (X b : MvPolynomial (Fin n) (FnField P)) = ∑ j, C (D b j) * ∑ a, C (B a j) * X a := by
      simp_rw [Finset.mul_sum, ← mul_assoc, ← C_mul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, ← map_sum, h1]
      simp
    rw [hX]
    exact (Subalgebra.mem_algebraicClosure S _).1 (Subalgebra.sum_mem _ fun j _ =>
      Subalgebra.mul_mem _ ((Subalgebra.mem_algebraicClosure S _).2 (halgC _))
        ((Subalgebra.mem_algebraicClosure S _).2 (halgS _ (hlin j))))
  have hall : ∀ p : MvPolynomial (Fin n) (FnField P), p ∈ Subalgebra.algebraicClosure S _ := fun p =>
    MvPolynomial.induction_on p (fun φ => halgC φ) (fun _ _ hp hq => Subalgebra.add_mem _ hp hq)
      (fun _ b hp => Subalgebra.mul_mem _ hp (halgX b))
  have hAlg : Algebra.IsAlgebraic S (MvPolynomial (Fin n) (FnField P)) := ⟨fun p => hall p⟩

  have hA : Function.Injective (algebraMap ℤ (MRing ι ⧸ P)) := algebraMap_int_injective P hPz
  have hΦ : Function.Injective (algebraMap ℤ (FnField P)) := by
    rw [show algebraMap ℤ (FnField P) = (algebraMap (MRing ι ⧸ P) (FnField P)).comp (algebraMap ℤ _) from
      RingHom.ext_int _ _]
    exact (IsFractionRing.injective (MRing ι ⧸ P) (FnField P)).comp hA
  have hM : Function.Injective (algebraMap ℤ (MvPolynomial (Fin n) (FnField P))) := by
    rw [show algebraMap ℤ (MvPolynomial (Fin n) (FnField P)) = (C : FnField P →+* _).comp (algebraMap ℤ _) from
      RingHom.ext_int _ _]
    exact (C_injective _ _).comp hΦ
  have := (faithfulSMul_iff_algebraMap_injective ℤ (MRing ι ⧸ P)).2 hA
  have := (faithfulSMul_iff_algebraMap_injective (MRing ι ⧸ P) (FnField P)).2
    (IsFractionRing.injective (MRing ι ⧸ P) (FnField P))
  have := (faithfulSMul_iff_algebraMap_injective ℤ (FnField P)).2 hΦ
  have := (faithfulSMul_iff_algebraMap_injective (FnField P) (MvPolynomial (Fin n) (FnField P))).2
    (C_injective _ _)
  have := (faithfulSMul_iff_algebraMap_injective S (MvPolynomial (Fin n) (FnField P))).2 Subtype.val_injective
  have := (faithfulSMul_iff_algebraMap_injective ℤ S).2 fun a b h => hM (by
    rw [IsScalarTower.algebraMap_apply ℤ S (MvPolynomial (Fin n) (FnField P)) a,
      IsScalarTower.algebraMap_apply ℤ S (MvPolynomial (Fin n) (FnField P)) b, h])
  have : Algebra.IsAlgebraic (MRing ι ⧸ P) (FnField P) := IsLocalization.isAlgebraic _ (nonZeroDivisors _)
  have e1 := trdeg_add_eq ℤ S (A := MvPolynomial (Fin n) (FnField P))
  have e2 := trdeg_add_eq ℤ (FnField P) (A := MvPolynomial (Fin n) (FnField P))
  have e3 := trdeg_add_eq ℤ (MRing ι ⧸ P) (A := FnField P)
  rw [trdeg_eq_zero (R := S) (A := MvPolynomial (Fin n) (FnField P)), add_zero] at e1
  rw [trdeg_eq_zero (R := MRing ι ⧸ P) (A := FnField P), add_zero] at e3
  rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fin] at e2
  rw [e1, ← e2, e3]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
