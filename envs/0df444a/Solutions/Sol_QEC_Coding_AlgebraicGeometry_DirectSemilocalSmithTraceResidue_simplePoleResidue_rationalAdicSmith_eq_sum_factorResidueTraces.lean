-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue.simplePoleResidue_rationalAdicSmith_eq_sum_factorResidueTraces
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:53:15.001313+00:00
-- url     : https://prove2.me/submissions/94eae04e-589c-454d-ac45-644a87947b3c

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSmithTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalCokernelTraceSum
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SmithDifferentialTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalSmithTraceResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_rationalAdicSmithLogarithmicDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSmithTraceResidue_directBaseResidueRationalAdicEquiv_quotientResidueEquiv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectSemilocalCokernelTraceSum_quotientResidueEquiv_primaryTorsionTrace_principalCokernel_eq_sum_factorResidueTrace
attribute [local simp] QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv_quotientResidueEquiv


section
namespace QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue
open scoped Polynomial RatFunc nonZeroDivisors BigOperators
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
open DirectFactorSmithTraceResidue
private theorem lmul_comp_lmul (t b : B k F) :
    (Algebra.lmul (R k) (B k F) t).comp
        (Algebra.lmul (R k) (B k F) b) =
      (Algebra.lmul (R k) (B k F) b).comp
        (Algebra.lmul (R k) (B k F) t) := by
  apply LinearMap.ext
  intro x
  change t * (b * x) = b * (t * x)
  ring
end QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue
open scoped Polynomial RatFunc nonZeroDivisors BigOperators
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue._p2m_local_instance_7f43513034_38
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue._p2m_local_instance_7f43513034_40
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue._p2m_local_instance_7f43513034_50
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue._p2m_local_instance_7f43513034_54
open DirectFactorSmithTraceResidue
namespace QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (J : Ideal (B k F))
    (hcop : IsCoprime
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) J)
    (t b : B k F)
    (hspan : Ideal.span ({t} : Set (B k F)) =
      (∏ P : (factors
        (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
          (P : Ideal (B k F))) * J)
    {n : ℕ}
    (source target : Module.Basis (Fin n) (R k) (B k F))
    (a : Fin n → R k) (ha : ∀ i, a i ≠ 0)
    (hdiag : LinearMap.toMatrix source target
      (Algebra.lmul (R k) (B k F) t) = Matrix.diagonal a) :
    Differential.simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (Differential.rationalAdicSmithLogarithmicDifferentialAtSimplePole p
          source target a ha (Algebra.lmul (R k) (B k F) b)) =
      directBaseResidueRationalAdicEquiv k p
        (∑ P : (factors
            (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
          Ideal.Factors.factorResidueTrace p.asIdeal P b) := by
  let depth : ℕ :=
    (∑ i, multiplicity p.asIdeal
      (Ideal.span ({a i} : Set (R k)))).succ
  have hdepth : ∀ i, multiplicity p.asIdeal
      (Ideal.span ({a i} : Set (R k))) ≤ depth := by
    intro i
    apply le_trans ?_ (Nat.le_succ _)
    exact Finset.single_le_sum
      (fun j _ => Nat.zero_le
        (multiplicity p.asIdeal (Ideal.span ({a j} : Set (R k)))))
      (Finset.mem_univ i)
  have hcomm := lmul_comp_lmul k F t b
  have hcokernel :
      cokernelEndomorphism
          (Algebra.lmul (R k) (B k F) t)
          (Algebra.lmul (R k) (B k F) b) hcomm =
        principalCokernelMul (R := R k) t b := by
    rfl
  have hrational :=
    Differential.simplePoleResidue_rationalAdicSmithLogarithmicDifferential
      p source target a ha
        (Algebra.lmul (R k) (B k F) t)
        (Algebra.lmul (R k) (B k F) b)
        hdiag hcomm depth hdepth
  have hprimary :=
    DirectSemilocalCokernelTraceSum.quotientResidueEquiv_primaryTorsionTrace_principalCokernel_eq_sum_factorResidueTrace
      k F p J hcop t b hspan depth (Nat.succ_pos _)
  calc
    Differential.simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (Differential.rationalAdicSmithLogarithmicDifferentialAtSimplePole p
          source target a ha (Algebra.lmul (R k) (B k F) b)) =
      GlobalPlace.rationalAdicIdealResidueEquiv p
        (primaryTorsionTrace p.asIdeal
          (cokernelEndomorphism
            (Algebra.lmul (R k) (B k F) t)
            (Algebra.lmul (R k) (B k F) b) hcomm) depth) := hrational
    _ = directBaseResidueRationalAdicEquiv k p
        (Ideal.Factors.quotientResidueEquiv p.asIdeal
          (primaryTorsionTrace p.asIdeal
            (principalCokernelMul (R := R k) t b) depth)) := by
      rw [hcokernel,
        directBaseResidueRationalAdicEquiv_quotientResidueEquiv]
    _ = _ := by rw [hprimary]
end QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue
