-- Prove2me | solution 1 for QEC.Semantics.clbtFourBlockGeneratorEstimate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:08:57.142018+00:00
-- url     : https://prove2.me/submissions/84ae0fab-6f06-40bd-95ef-9415cdd6191a

import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Theorems.Thm_QEC_Semantics_clbtGenerator_eq_sum_four_blocks
import Theorems.Thm_QEC_Semantics_clbtGeneratorBlockOne_bound
import Theorems.Thm_QEC_Semantics_clbtGeneratorBlockTwo_bound
import Theorems.Thm_QEC_Semantics_clbtGeneratorBlockThree_bound
import Theorems.Thm_QEC_Semantics_clbtGeneratorBlockFour_bound
import Theorems.Thm_QEC_Semantics_traceNorm_add_le

section
universe u v
namespace QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteQuantumSystem H]
private theorem traceNorm_four_sum_le_four_mul
    (A₁ A₂ A₃ A₄ : Operator H) (b : Real)
    (h₁ : traceNorm A₁ ≤ b) (h₂ : traceNorm A₂ ≤ b)
    (h₃ : traceNorm A₃ ≤ b) (h₄ : traceNorm A₄ ≤ b) :
    traceNorm (A₁ + A₂ + A₃ + A₄) ≤ 4 * b := by
  calc
    traceNorm (A₁ + A₂ + A₃ + A₄) ≤
        traceNorm (A₁ + A₂ + A₃) + traceNorm A₄ :=
      traceNorm_add_le _ _
    _ ≤ (traceNorm (A₁ + A₂) + traceNorm A₃) + traceNorm A₄ :=
      add_le_add (traceNorm_add_le (A₁ + A₂) A₃) (le_refl (traceNorm A₄))
    _ ≤ ((traceNorm A₁ + traceNorm A₂) + traceNorm A₃) + traceNorm A₄ :=
      add_le_add
        (add_le_add (traceNorm_add_le A₁ A₂) (le_refl (traceNorm A₃)))
        (le_refl (traceNorm A₄))
    _ ≤ b + b + b + b :=
      add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄
    _ = 4 * b := by ring
end
end QEC.Semantics
end

set_option autoImplicit false
universe u v
open QEC QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteQuantumSystem H]
namespace QEC.Semantics
theorem _root_.solution [Fintype ι] [Nontrivial H]
    (J : ι → Operator H) (O P : Operator H) (rho : DensityOperator H)
    (hprotected : JumpProtected J O P) (hO : O.IsSymmetric)
    (hP : IsStarProjection P) (hOP : Commute O P)
    (hOrho : Commute O rho.toOperator) (hPrho : Commute P rho.toOperator)
    (hstationary : lindbladDissipator J rho.toOperator = 0)
    (hOnorm : operatorNorm O ≤ 2) :
    traceNorm (lindbladDissipator J (O * rho.toOperator)) ≤
      8 * lindbladDissipatorNorm J * clbtGibbsTailMass P rho := by
  rw [clbtGenerator_eq_sum_four_blocks]
  calc
    traceNorm
        (clbtGeneratorBlockOne (lindbladDissipator J) O P rho.toOperator +
          clbtGeneratorBlockTwo (lindbladDissipator J) O P rho.toOperator +
          clbtGeneratorBlockThree (lindbladDissipator J) O P rho.toOperator +
          clbtGeneratorBlockFour (lindbladDissipator J) O P rho.toOperator) ≤
        4 * (2 * lindbladDissipatorNorm J * clbtGibbsTailMass P rho) :=
      traceNorm_four_sum_le_four_mul _ _ _ _ _
        (clbtGeneratorBlockOne_bound J O P rho hprotected hO hP hOP hPrho
          hstationary hOnorm)
        (clbtGeneratorBlockTwo_bound J O P rho hprotected hO hP hOP hOrho hPrho
          hstationary hOnorm)
        (clbtGeneratorBlockThree_bound J O P rho hO hP hOP hOrho hPrho hOnorm)
        (clbtGeneratorBlockFour_bound J O P rho hO hP hOP hOrho hPrho hOnorm)
    _ = 8 * lindbladDissipatorNorm J * clbtGibbsTailMass P rho := by ring
end QEC.Semantics
