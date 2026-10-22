-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P18.isCQ_of_weyl_dual_commutes
-- status  : ACCEPTED   (prove)
-- author  : @Imine
-- created : 2026-10-21T06:08:51.525196+00:00
-- url     : https://prove2.me/submissions/f9131df0-d0ac-4f83-ae81-618751e42e69

import Theorems.Thm_QAlgorithms_OperatorAlgebra_traceclass_weyl_annihilator
import Theorems.Thm_QAlgorithms_OperatorAlgebra_dual_commutator_coeff_traceclass
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P18
noncomputable section
set_option autoImplicit false
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
open QAlgorithms.Papers.Independent.Claimed50.P35 (ScaledWeylRepresentation InterleavedPhase tracePair)
open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff)
open QAlgorithms.Papers.Independent.Next46.P18 (DualChannel IsCQ)
attribute [local instance] Classical.propDecidable Classical.decEq

lemma coeff_injective {I : Type} (A B : Hilbert I →L[ℂ] Hilbert I)
    (h : operatorCoeff A = operatorCoeff B) : A = B := by
  classical
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro i
  apply ContinuousLinearMap.ext
  intro c
  change A (lp.single 2 i c) = B (lp.single 2 i c)
  have hc : (lp.single 2 i c : Hilbert I) = c • (lp.single 2 i (1 : ℂ) : Hilbert I) := by
    ext j
    simp [lp.single_apply, Pi.single_apply]
  rw [hc, map_smul, map_smul]
  congr 1
  ext k
  exact congrFun (congrFun h k) i


section TwoPass
variable {B Op Z : Type*} (F : B → Op) (g : Z → B) (comp : Op → Op → Op)

lemma two_pass_commute
    (hpair : ∀ z w : Z,
      comp (F (g z)) (F (g w)) = comp (F (g w)) (F (g z)))
    (hext : ∀ A : Op,
      (∀ z : Z, comp (F (g z)) A = comp A (F (g z))) →
      ∀ b : B, comp (F b) A = comp A (F b))
    (b c : B) :
    comp (F b) (F c) = comp (F c) (F b) := by
  have h₁ : ∀ z : Z, ∀ b : B,
      comp (F b) (F (g z)) = comp (F (g z)) (F b) := by
    intro z
    exact hext (F (g z)) (fun w => hpair w z)
  exact hext (F c) (fun z => (h₁ z c).symm) b

end TwoPass


theorem solution {I J : Type} [Countable I] [Countable J]
    [Nonempty I] [Nonempty J] {t : ℕ}
    (WB : ScaledWeylRepresentation J t 1) (Phi : DualChannel I J)
    (h : ∀ z w : InterleavedPhase t,
      (Phi.dual (WB.operator z)).comp (Phi.dual (WB.operator w)) =
      (Phi.dual (WB.operator w)).comp (Phi.dual (WB.operator z))) :
    IsCQ Phi := by
  have hext (A : Hilbert I →L[ℂ] Hilbert I)
      (hA : ∀ z : InterleavedPhase t,
        (Phi.dual (WB.operator z)).comp A = A.comp (Phi.dual (WB.operator z)))
      (B : Hilbert J →L[ℂ] Hilbert J) :
      (Phi.dual B).comp A = A.comp (Phi.dual B) := by
    apply sub_eq_zero.mp
    apply coeff_injective
    funext i j
    obtain ⟨Y, hY, hrepr⟩ :=
      QAlgorithms.OperatorAlgebra.dual_commutator_coeff_traceclass Phi A i j
    have hzero : Y = 0 := by
      apply QAlgorithms.OperatorAlgebra.traceclass_weyl_annihilator WB Y hY
      intro z
      rw [← hrepr (WB.operator z), hA z, sub_self]
      simp [operatorCoeff]
    rw [hrepr B, hzero]
    simp [tracePair, operatorCoeff]
  intro B C
  exact two_pass_commute (fun B => Phi.dual B) WB.operator
    (fun A D => A.comp D) h hext B C
