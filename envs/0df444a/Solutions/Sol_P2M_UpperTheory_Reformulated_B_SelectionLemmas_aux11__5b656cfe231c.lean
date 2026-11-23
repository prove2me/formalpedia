-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_SelectionLemmas_aux11__5b656cfe231c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:29.137221+00:00
-- url     : https://prove2.me/submissions/8146dd21-60ae-4518-b600-d58906803a83

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
theorem _root_.solution.{u_1, u_2} :
    ∀ {R : Type u_1} [inst : CommRing R] {W : Type u_2} [inst_1 : AddCommGroup W]
      [inst_2 :
        @_root_.Module R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@AddCommGroup.toAddCommMonoid W inst_1)]
      (S :
        @Submonoid R
          (@MulZeroOneClass.toMulOneClass R
            (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
      (L :
        @Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@AddCommGroup.toAddCommMonoid W inst_1) inst_2),
      ∃ (s : R),
        And
          (@Membership.mem R
            (@Submonoid R
              (@MulZeroOneClass.toMulOneClass R
                (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
            (@SetLike.instMembership
              (@Submonoid R
                (@MulZeroOneClass.toMulOneClass R
                  (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
              R
              (@Submonoid.instSetLike R
                (@MulZeroOneClass.toMulOneClass R
                  (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))))
            S s)
          (@Membership.mem W
            (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
              (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
            (@SetLike.instMembership
              (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
              W
              (@Submodule.setLike R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                (@AddCommGroup.toAddCommMonoid W inst_1) inst_2))
            L
            (@HSMul.hSMul R W W
              (@instHSMul R W
                (@SMulZeroClass.toSMul R W
                  (@AddZero.toZero W
                    (@AddZeroClass.toAddZero W
                      (@AddMonoid.toAddZeroClass W
                        (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))))
                  (@DistribSMul.toSMulZeroClass R W
                    (@AddMonoid.toAddZeroClass W
                      (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))
                    (@DistribMulAction.toDistribSMul R W
                      (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                      (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1)))
                      (@Module.toDistribMulAction R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)))))
              s
              (@OfNat.ofNat W (nat_lit 0)
                (@Zero.toOfNat0 W
                  (@AddZero.toZero W
                    (@AddZeroClass.toAddZero W
                      (@AddMonoid.toAddZeroClass W
                        (@AddCommMonoid.toAddMonoid W (@AddCommGroup.toAddCommMonoid W inst_1))))))))) := by
  intro R _ W _ _ S L
  exact ⟨1, S.one_mem, by rw [smul_zero]; exact L.zero_mem⟩
end UpperTheory.Reformulated.B.SelectionLemmas
