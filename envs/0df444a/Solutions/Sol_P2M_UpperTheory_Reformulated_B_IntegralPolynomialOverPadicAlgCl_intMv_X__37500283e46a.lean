-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_IntegralPolynomialOverPadicAlgCl_intMv_X__37500283e46a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:00:13.313107+00:00
-- url     : https://prove2.me/submissions/3372f54c-cae4-4ce9-9e87-beb87592ce63

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralPolynomialFifth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.intMv_X
theorem _root_.solution.{u_1} :
    ∀ {p : Nat} [inst : Fact (Nat.Prime p)] {σ : Type u_1} (i : σ),
      @UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.IntegralMv σ p inst
        (@MvPowerSeries.X σ (@PadicComplex p inst)
          (@DivisionSemiring.toSemiring (@PadicComplex p inst)
            (@Semifield.toDivisionSemiring (@PadicComplex p inst)
              (@Field.toSemifield (@PadicComplex p inst)
                (@UniformSpace.Completion.instField (@PadicAlgCl p inst)
                  (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))
                  (@Valued.toUniformSpace (@PadicAlgCl p inst)
                    (@DivisionRing.toRing (@PadicAlgCl p inst)
                      (@Field.toDivisionRing (@PadicAlgCl p inst)
                        (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))))
                    NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))
                  (@Valued.isTopologicalDivisionRing (@PadicAlgCl p inst)
                    (@Field.toDivisionRing (@PadicAlgCl p inst)
                      (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst)))
                    NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))
                  (@NormedField.instCompletableTopField (@PadicAlgCl p inst) (@PadicAlgCl.normedField p inst))
                  (@Valued.toIsUniformAddGroup (@PadicAlgCl p inst)
                    (@DivisionRing.toRing (@PadicAlgCl p inst)
                      (@Field.toDivisionRing (@PadicAlgCl p inst)
                        (@AlgebraicClosure.instField (@Padic p inst) (@instFieldPadic p inst))))
                    NNReal NNReal.instLinearOrderedCommGroupWithZero (@PadicAlgCl.valued p inst))))))
          i) := by
  intro p inst σ i n
  classical
  change ‖(MvPowerSeries.coeff n (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) : ℂ_[p])‖ ≤ 1
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact norm_one.le
  · rw [norm_zero]
    exact zero_le_one
end UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl.intMv_X
