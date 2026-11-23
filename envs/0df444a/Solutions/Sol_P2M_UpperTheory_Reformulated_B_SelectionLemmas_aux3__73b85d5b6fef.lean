-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_SelectionLemmas_aux3__73b85d5b6fef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:37.364061+00:00
-- url     : https://prove2.me/submissions/05fae4c1-b80e-4530-acb8-aac448ae70ff

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SelectionLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.SelectionLemmas
theorem _root_.solution.{u_1, u_2, u_3} :
    ∀ {S : Type u_3} {K : Type u_2} {V : Type u_1} [inst : CommRing S] [inst_1 : Field K]
      [inst_2 :
        @Algebra S K (@CommRing.toCommSemiring S inst)
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))]
      [inst_3 : AddCommGroup V]
      [inst_4 :
        @_root_.Module K V (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
          (@AddCommGroup.toAddCommMonoid V inst_3)]
      [inst_5 :
        @_root_.Module S V (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
          (@AddCommGroup.toAddCommMonoid V inst_3)]
      [@IsScalarTower S K V
          (@Algebra.toSMul S K (@CommRing.toCommSemiring S inst)
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))) inst_2)
          (@SMulZeroClass.toSMul K V
            (@AddZero.toZero V
              (@AddZeroClass.toAddZero V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_3))))))
            (@DistribSMul.toSMulZeroClass K V
              (@AddMonoid.toAddZeroClass V
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_3))))
              (@DistribMulAction.toDistribSMul K V
                (@Semiring.toMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_3)))
                (@Module.toDistribMulAction K V
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                  (@AddCommGroup.toAddCommMonoid V inst_3) inst_4))))
          (@SMulZeroClass.toSMul S V
            (@AddZero.toZero V
              (@AddZeroClass.toAddZero V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_3))))))
            (@DistribSMul.toSMulZeroClass S V
              (@AddMonoid.toAddZeroClass V
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_3))))
              (@DistribMulAction.toDistribSMul S V
                (@Semiring.toMonoid S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst)))
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_3)))
                (@Module.toDistribMulAction S V (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
                  (@AddCommGroup.toAddCommMonoid V inst_3) inst_5))))],
      @LinearMap.CompatibleSMul V K (@AddCommGroup.toAddCommMonoid V inst_3)
        (@Semiring.toAddCommMonoid K
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
        S K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
        (@SMulZeroClass.toSMul S V
          (@AddZero.toZero V
            (@AddZeroClass.toAddZero V
              (@AddMonoid.toAddZeroClass V (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_3)))))
          (@DistribSMul.toSMulZeroClass S V
            (@AddMonoid.toAddZeroClass V (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_3)))
            (@DistribMulAction.toDistribSMul S V
              (@Semiring.toMonoid S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst)))
              (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_3))
              (@Module.toDistribMulAction S V (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
                (@AddCommGroup.toAddCommMonoid V inst_3) inst_5))))
        inst_4
        (@SMulZeroClass.toSMul S K
          (@AddZero.toZero K
            (@AddZeroClass.toAddZero K
              (@AddMonoid.toAddZeroClass K
                (@AddCommMonoid.toAddMonoid K
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))))))
          (@DistribSMul.toSMulZeroClass S K
            (@AddMonoid.toAddZeroClass K
              (@AddCommMonoid.toAddMonoid K
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))))
            (@DistribMulAction.toDistribSMul S K
              (@Semiring.toMonoid S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst)))
              (@AddCommMonoid.toAddMonoid K
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
              (@Module.toDistribMulAction S K (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                (@Algebra.toModule S K (@CommRing.toCommSemiring S inst)
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                  inst_2)))))
        (@Semiring.toModule K
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))) := by
  intros; infer_instance
end UpperTheory.Reformulated.B.SelectionLemmas
