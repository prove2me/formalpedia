-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Gub2.fg_Z1T
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:17:41.287667+00:00
-- url     : https://prove2.me/submissions/bbb1ece5-2302-4e46-a00b-78a4d2ba17e7

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementTor
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CompactQuotientSubmodule
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FgZ1T
import Theorems.Thm_UpperTheory_compact_quotient_submodule


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Gub2
theorem _root_.solution :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] {LL O V : Type} [inst_2 : Field LL] [inst_3 : CommRing O]
      [inst_4 :
        @Algebra O LL (@CommRing.toCommSemiring O inst_3)
          (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2)))]
      [inst_5 : AddCommGroup V]
      [inst_6 :
        @_root_.Module LL V
          (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2)))
          (@AddCommGroup.toAddCommMonoid V inst_5)]
      [inst_7 :
        @_root_.Module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
          (@AddCommGroup.toAddCommMonoid V inst_5)]
      [inst_8 :
        @IsScalarTower O LL V
          (@Algebra.toSMul O LL (@CommRing.toCommSemiring O inst_3)
            (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2))) inst_4)
          (@SMulZeroClass.toSMul LL V
            (@AddZero.toZero V
              (@AddZeroClass.toAddZero V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5))))))
            (@DistribSMul.toSMulZeroClass LL V
              (@AddMonoid.toAddZeroClass V
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5))))
              (@DistribMulAction.toDistribSMul LL V
                (@Semiring.toMonoid LL
                  (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2))))
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5)))
                (@Module.toDistribMulAction LL V
                  (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2)))
                  (@AddCommGroup.toAddCommMonoid V inst_5) inst_6))))
          (@SMulZeroClass.toSMul O V
            (@AddZero.toZero V
              (@AddZeroClass.toAddZero V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5))))))
            (@DistribSMul.toSMulZeroClass O V
              (@AddMonoid.toAddZeroClass V
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5))))
              (@DistribMulAction.toDistribSMul O V
                (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5)))
                (@Module.toDistribMulAction O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                  (@AddCommGroup.toAddCommMonoid V inst_5) inst_7))))]
      {ρ :
        @Representation LL G V
          (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2)))
          (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst)) (@AddCommGroup.toAddCommMonoid V inst_5) inst_6}
      [inst_9 : TopologicalSpace V]
      [inst_10 :
        @ContinuousAdd V inst_9
          (@AddCommMagma.toAdd V
            (@AddCommSemigroup.toAddCommMagma V
              (@AddCommMonoid.toAddCommSemigroup V (@AddCommGroup.toAddCommMonoid V inst_5))))]
      [inst_11 :
        @ContinuousConstSMul LL V inst_9
          (@SMulZeroClass.toSMul LL V
            (@AddZero.toZero V
              (@AddZeroClass.toAddZero V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5))))))
            (@DistribSMul.toSMulZeroClass LL V
              (@AddMonoid.toAddZeroClass V
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5))))
              (@DistribMulAction.toDistribSMul LL V
                (@Semiring.toMonoid LL
                  (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2))))
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5)))
                (@Module.toDistribMulAction LL V
                  (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2)))
                  (@AddCommGroup.toAddCommMonoid V inst_5) inst_6))))]
      [inst_12 : TopologicalSpace LL]
      [@ContinuousSMul LL V
          (@SMulZeroClass.toSMul LL V
            (@AddZero.toZero V
              (@AddZeroClass.toAddZero V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5))))))
            (@DistribSMul.toSMulZeroClass LL V
              (@AddMonoid.toAddZeroClass V
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5))))
              (@DistribMulAction.toDistribSMul LL V
                (@Semiring.toMonoid LL
                  (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2))))
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5)))
                (@Module.toDistribMulAction LL V
                  (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2)))
                  (@AddCommGroup.toAddCommMonoid V inst_5) inst_6))))
          inst_12 inst_9]
      [@IsTopologicalAddGroup V inst_9 (@AddCommGroup.toAddGroup V inst_5)] [@T2Space V inst_9]
      (L : @Formalism.WeaklyAdmissibleFiltrations.Lattice G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ) {ϖ : O},
      @Ne LL
          (@DFunLike.coe
            (@RingHom O LL (@Semiring.toNonAssocSemiring O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
              (@Semiring.toNonAssocSemiring LL
                (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2)))))
            O (fun (x : O) ↦ LL)
            (@RingHom.instFunLike O LL
              (@Semiring.toNonAssocSemiring O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
              (@Semiring.toNonAssocSemiring LL
                (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2)))))
            (@Algebra.algebraMap O LL (@CommRing.toCommSemiring O inst_3)
              (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2))) inst_4)
            ϖ)
          (@OfNat.ofNat LL (nat_lit 0)
            (@Zero.toOfNat0 LL
              (@MulZeroClass.toZero LL
                (@instMulZeroClassOfSemiring LL
                  (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2))))))) →
        (@Filter.HasBasis V Nat
            (@nhds V inst_9
              (@OfNat.ofNat V (nat_lit 0)
                (@Zero.toOfNat0 V
                  (@NegZeroClass.toZero V
                    (@SubNegZeroMonoid.toNegZeroClass V
                      (@SubtractionMonoid.toSubNegZeroMonoid V
                        (@SubtractionCommMonoid.toSubtractionMonoid V
                          (@AddCommGroup.toDivisionAddCommMonoid V inst_5))))))))
            (fun (x : Nat) ↦ True) fun (n : Nat) ↦
            @Set.image V V
              (fun (x : V) ↦
                @HSMul.hSMul O V V
                  (@instHSMul O V
                    (@SMulZeroClass.toSMul O V
                      (@AddZero.toZero V
                        (@AddZeroClass.toAddZero V
                          (@AddMonoid.toAddZeroClass V
                            (@SubNegMonoid.toAddMonoid V
                              (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5))))))
                      (@DistribSMul.toSMulZeroClass O V
                        (@AddMonoid.toAddZeroClass V
                          (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5))))
                        (@DistribMulAction.toDistribSMul O V
                          (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                          (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_5)))
                          (@Module.toDistribMulAction O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                            (@AddCommGroup.toAddCommMonoid V inst_5) inst_7)))))
                  (@HPow.hPow O Nat O
                    (@instHPow O Nat
                      (@NPow.toPow O
                        (@Monoid.toNPow O
                          (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))))))
                    ϖ n)
                  x)
              (@SetLike.coe
                (@Submodule O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                  (@AddCommGroup.toAddCommMonoid V inst_5) inst_7)
                V
                (@Submodule.setLike O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                  (@AddCommGroup.toAddCommMonoid V inst_5) inst_7)
                (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))) →
          @IsCompact LL inst_12
              (@Set.range LL O
                (@DFunLike.coe
                  (@RingHom O LL
                    (@Semiring.toNonAssocSemiring O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                    (@Semiring.toNonAssocSemiring LL
                      (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2)))))
                  O (fun (x : O) ↦ LL)
                  (@RingHom.instFunLike O LL
                    (@Semiring.toNonAssocSemiring O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                    (@Semiring.toNonAssocSemiring LL
                      (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2)))))
                  (@Algebra.algebraMap O LL (@CommRing.toCommSemiring O inst_3)
                    (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_2)))
                    inst_4))) →
            ∀
              (hI :
                @Formalism.WeaklyAdmissibleFiltrations.StableSub G inst LL inst_2 O inst_3 inst_4 V inst_5 inst_6 inst_7 inst_8 ρ L
                  (@HSMul.hSMul (@Ideal O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                    (@Submodule O (↥(@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                      (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                      (@Submodule.addCommMonoid O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                        (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                        (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                      (@Submodule.module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                        (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                        (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L)))
                    (@Submodule O (↥(@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                      (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                      (@Submodule.addCommMonoid O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                        (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                        (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                      (@Submodule.module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                        (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                        (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L)))
                    (@instHSMul (@Ideal O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                      (@Submodule O (↥(@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                        (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                        (@Submodule.addCommMonoid O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                          (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                          (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                        (@Submodule.module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                          (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                          (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L)))
                      (@Submodule.instSMul O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)) O
                        (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                        (@Semiring.toModule O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                        (↥(@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                        (@Submodule.addCommMonoid O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                          (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                          (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                        (@Submodule.module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                          (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                          (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                        (@Submodule.module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                          (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                          (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                        (@Submodule.isScalarTower' O O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                          (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                          (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L) O
                          (@instSMulOfMul O
                            (@Distrib.toMul O
                              (@instDistribOfSemiring O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))))
                          (@SMulZeroClass.toSMul O V
                            (@AddZero.toZero V
                              (@AddZeroClass.toAddZero V
                                (@AddMonoid.toAddZeroClass V
                                  (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_5)))))
                            (@DistribSMul.toSMulZeroClass O V
                              (@AddMonoid.toAddZeroClass V
                                (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_5)))
                              (@DistribMulAction.toDistribSMul O V
                                (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                                (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_5))
                                (@Module.toDistribMulAction O V
                                  (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                                  (@AddCommGroup.toAddCommMonoid V inst_5) inst_7))))
                          (@instSMulOfMul O
                            (@Distrib.toMul O
                              (@instDistribOfSemiring O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))))
                          (@SMulZeroClass.toSMul O V
                            (@AddZero.toZero V
                              (@AddZeroClass.toAddZero V
                                (@AddMonoid.toAddZeroClass V
                                  (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_5)))))
                            (@DistribSMul.toSMulZeroClass O V
                              (@AddMonoid.toAddZeroClass V
                                (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_5)))
                              (@DistribMulAction.toDistribSMul O V
                                (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                                (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_5))
                                (@Module.toDistribMulAction O V
                                  (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                                  (@AddCommGroup.toAddCommMonoid V inst_5) inst_7))))
                          (@SMulZeroClass.toSMul O O
                            (@AddZero.toZero O
                              (@AddZeroClass.toAddZero O
                                (@AddMonoid.toAddZeroClass O
                                  (@AddMonoidWithOne.toAddMonoid O
                                    (@AddCommMonoidWithOne.toAddMonoidWithOne O
                                      (@NonAssocSemiring.toAddCommMonoidWithOne O
                                        (@Semiring.toNonAssocSemiring O
                                          (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))))))))
                            (@DistribSMul.toSMulZeroClass O O
                              (@AddMonoid.toAddZeroClass O
                                (@AddMonoidWithOne.toAddMonoid O
                                  (@AddCommMonoidWithOne.toAddMonoidWithOne O
                                    (@NonAssocSemiring.toAddCommMonoidWithOne O
                                      (@Semiring.toNonAssocSemiring O
                                        (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))))))
                              (@DistribMulAction.toDistribSMul O O
                                (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                                (@AddMonoidWithOne.toAddMonoid O
                                  (@AddCommMonoidWithOne.toAddMonoidWithOne O
                                    (@NonAssocSemiring.toAddCommMonoidWithOne O
                                      (@Semiring.toNonAssocSemiring O
                                        (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))))))
                                (@Module.toDistribMulAction O O
                                  (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                                  (@Semiring.toAddCommMonoid O
                                    (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                                  (@Semiring.toModule O
                                    (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))))))
                          (@Submodule.module._proof_1 O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                            (@AddCommGroup.toAddCommMonoid V inst_5) inst_7)
                          (@IsScalarTower.left O V
                            (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                            (@DistribMulAction.toMulAction O V
                              (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                              (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_5))
                              (@Module.toDistribMulAction O V
                                (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                                (@AddCommGroup.toAddCommMonoid V inst_5) inst_7)))
                          (@Submodule.module._proof_1 O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                            (@AddCommGroup.toAddCommMonoid V inst_5) inst_7))))
                    (@Ideal.span O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                      (@Singleton.singleton O (Set O) (@Set.instSingletonSet O)
                        (@HPow.hPow O Nat O
                          (@instHPow O Nat
                            (@NPow.toPow O
                              (@Monoid.toNPow O
                                (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))))))
                          ϖ (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (@Top.top
                      (@Submodule O (↥(@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                        (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                        (@Submodule.addCommMonoid O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                          (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                          (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                        (@Submodule.module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                          (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                          (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L)))
                      (@Submodule.instTop O (↥(@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                        (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                        (@Submodule.addCommMonoid O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                          (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                          (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                        (@Submodule.module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                          (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                          (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L)))))),
              Finite
                  ↥(@Formalism.WeaklyAdmissibleFiltrations.quotientCocycles G inst LL inst_2 O inst_3 inst_4 V inst_5 inst_6 inst_7 inst_8 ρ inst_1 L
                      (@HSMul.hSMul (@Ideal O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                        (@Submodule O (↥(@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                          (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                          (@Submodule.addCommMonoid O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                            (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                            (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                          (@Submodule.module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                            (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                            (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L)))
                        (@Submodule O (↥(@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                          (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                          (@Submodule.addCommMonoid O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                            (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                            (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                          (@Submodule.module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                            (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                            (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L)))
                        (@instHSMul (@Ideal O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                          (@Submodule O (↥(@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                            (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                            (@Submodule.addCommMonoid O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                              (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                              (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                            (@Submodule.module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                              (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                              (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L)))
                          (@Submodule.instSMul O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)) O
                            (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                            (@Semiring.toModule O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                            (↥(@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                            (@Submodule.addCommMonoid O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                              (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                              (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                            (@Submodule.module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                              (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                              (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                            (@Submodule.module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                              (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                              (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                            (@Submodule.isScalarTower' O O V
                              (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                              (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                              (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L) O
                              (@instSMulOfMul O
                                (@Distrib.toMul O
                                  (@instDistribOfSemiring O
                                    (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))))
                              (@SMulZeroClass.toSMul O V
                                (@AddZero.toZero V
                                  (@AddZeroClass.toAddZero V
                                    (@AddMonoid.toAddZeroClass V
                                      (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_5)))))
                                (@DistribSMul.toSMulZeroClass O V
                                  (@AddMonoid.toAddZeroClass V
                                    (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_5)))
                                  (@DistribMulAction.toDistribSMul O V
                                    (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                                    (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_5))
                                    (@Module.toDistribMulAction O V
                                      (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                                      (@AddCommGroup.toAddCommMonoid V inst_5) inst_7))))
                              (@instSMulOfMul O
                                (@Distrib.toMul O
                                  (@instDistribOfSemiring O
                                    (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))))
                              (@SMulZeroClass.toSMul O V
                                (@AddZero.toZero V
                                  (@AddZeroClass.toAddZero V
                                    (@AddMonoid.toAddZeroClass V
                                      (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_5)))))
                                (@DistribSMul.toSMulZeroClass O V
                                  (@AddMonoid.toAddZeroClass V
                                    (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_5)))
                                  (@DistribMulAction.toDistribSMul O V
                                    (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                                    (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_5))
                                    (@Module.toDistribMulAction O V
                                      (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                                      (@AddCommGroup.toAddCommMonoid V inst_5) inst_7))))
                              (@SMulZeroClass.toSMul O O
                                (@AddZero.toZero O
                                  (@AddZeroClass.toAddZero O
                                    (@AddMonoid.toAddZeroClass O
                                      (@AddMonoidWithOne.toAddMonoid O
                                        (@AddCommMonoidWithOne.toAddMonoidWithOne O
                                          (@NonAssocSemiring.toAddCommMonoidWithOne O
                                            (@Semiring.toNonAssocSemiring O
                                              (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))))))))
                                (@DistribSMul.toSMulZeroClass O O
                                  (@AddMonoid.toAddZeroClass O
                                    (@AddMonoidWithOne.toAddMonoid O
                                      (@AddCommMonoidWithOne.toAddMonoidWithOne O
                                        (@NonAssocSemiring.toAddCommMonoidWithOne O
                                          (@Semiring.toNonAssocSemiring O
                                            (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))))))
                                  (@DistribMulAction.toDistribSMul O O
                                    (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                                    (@AddMonoidWithOne.toAddMonoid O
                                      (@AddCommMonoidWithOne.toAddMonoidWithOne O
                                        (@NonAssocSemiring.toAddCommMonoidWithOne O
                                          (@Semiring.toNonAssocSemiring O
                                            (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))))))
                                    (@Module.toDistribMulAction O O
                                      (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                                      (@Semiring.toAddCommMonoid O
                                        (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                                      (@Semiring.toModule O
                                        (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))))))
                              (@Submodule.module._proof_1 O V
                                (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                                (@AddCommGroup.toAddCommMonoid V inst_5) inst_7)
                              (@IsScalarTower.left O V
                                (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                                (@DistribMulAction.toMulAction O V
                                  (@Semiring.toMonoid O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3)))
                                  (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_5))
                                  (@Module.toDistribMulAction O V
                                    (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                                    (@AddCommGroup.toAddCommMonoid V inst_5) inst_7)))
                              (@Submodule.module._proof_1 O V
                                (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                                (@AddCommGroup.toAddCommMonoid V inst_5) inst_7))))
                        (@Ideal.span O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                          (@Singleton.singleton O (Set O) (@Set.instSingletonSet O)
                            (@HPow.hPow O Nat O
                              (@instHPow O Nat
                                (@NPow.toPow O
                                  (@Monoid.toNPow O
                                    (@Semiring.toMonoid O
                                      (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))))))
                              ϖ (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                        (@Top.top
                          (@Submodule O (↥(@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                            (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                            (@Submodule.addCommMonoid O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                              (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                              (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                            (@Submodule.module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                              (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                              (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L)))
                          (@Submodule.instTop O (↥(@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                            (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                            (@Submodule.addCommMonoid O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                              (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                              (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L))
                            (@Submodule.module O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                              (@AddCommGroup.toAddCommMonoid V inst_5) inst_7
                              (@Formalism.WeaklyAdmissibleFiltrations.Lattice.T G inst LL inst_2 O inst_3 V inst_5 inst_6 inst_7 ρ L)))))
                      hI) →
                @Submodule.FG O (G → V) (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                  (@Pi.addCommMonoid G (fun (a : G) ↦ V) fun (i : G) ↦ @AddCommGroup.toAddCommMonoid V inst_5)
                  (@Pi.Function.module G O V (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_3))
                    (@AddCommGroup.toAddCommMonoid V inst_5) inst_7)
                  (@Formalism.WeaklyAdmissibleFiltrations.latticeCocycles G inst LL inst_2 O inst_3 inst_4 V inst_5 inst_6 inst_7 inst_8 ρ inst_1 inst_9 inst_10
                    inst_11 L) := by
  intro G _ _ LL O V _ _ _ _ _ _ _ ρ _ _ _ _ _ _ _ L ϖ hϖ hb hc hI hfin
  have hmem : ∀ x : L.T, x ∈ (Ideal.span {ϖ ^ 1} • (⊤ : Submodule O L.T)) ↔
      ∃ y ∈ L.T, ϖ • y = (x : V) := by
    intro x
    rw [pow_one, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, -, rfl⟩
      exact ⟨y, y.2, rfl⟩
    · rintro ⟨y, hy, h⟩
      exact ⟨⟨y, hy⟩, trivial, Subtype.ext h⟩
  have hred : ∀ c : Formalism.WeaklyAdmissibleFiltrations.latticeCocycles L, Formalism.WeaklyAdmissibleFiltrations.redT L _ c ∈ Formalism.WeaklyAdmissibleFiltrations.quotientCocycles L _ hI := by
    intro c
    have hcont : Continuous (c : G → V) := c.2.1.1
    refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_, fun g h => ?_⟩
    · have h0 : Filter.Tendsto (fun y => (c : G → V) y - (c : G → V) g) (nhds g) (nhds 0) := by
        have := (hcont.sub (continuous_const (y := (c : G → V) g))).tendsto g
        rw [Pi.sub_apply, sub_self] at this
        exact this
      filter_upwards [h0 (hb.mem_of_mem (i := 1) trivial)] with y hy
      obtain ⟨v, hv, hvy⟩ := hy
      refine (Submodule.Quotient.eq _).2 ((hmem _).2 ⟨v, hv, ?_⟩)
      rw [← pow_one ϖ]
      exact hvy
    · have : Formalism.WeaklyAdmissibleFiltrations.evT L (g * h) c
          = Formalism.WeaklyAdmissibleFiltrations.evT L g c + Formalism.WeaklyAdmissibleFiltrations.actT L g (Formalism.WeaklyAdmissibleFiltrations.evT L h c) :=
        Subtype.ext (c.2.1.2 g h)
      change Submodule.mkQ _ (Formalism.WeaklyAdmissibleFiltrations.evT L (g * h) c) = _
      rw [this, map_add]
      rfl
  refine UpperTheory.compact_quotient_submodule (LL := LL) (Formalism.WeaklyAdmissibleFiltrations.latticeCocycles L) ϖ
    ((Formalism.WeaklyAdmissibleFiltrations.redT L _).codRestrict (Formalism.WeaklyAdmissibleFiltrations.quotientCocycles L _ hI) hred) hc ?_ ?_
  · intro U hU
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, hIf, t, ht, hsub⟩ := hU
    obtain ⟨n, -, hn⟩ := hb.mem_iff.1 ((Filter.biInter_mem hIf).2 fun i _ => ht i)
    refine ⟨n, fun z hz => hsub fun i hi => ?_⟩
    exact Set.mem_iInter₂.1 (hn ⟨z i, hz.2 i trivial, rfl⟩) i hi
  · intro z hz
    have hz' : ∀ g, ∃ y ∈ L.T, ϖ • y = (z : G → V) g := fun g =>
      (hmem (Formalism.WeaklyAdmissibleFiltrations.evT L g z)).1
        ((Submodule.Quotient.mk_eq_zero _).1 (congrFun (congrArg Subtype.val hz) g))
    refine ⟨(algebraMap O LL ϖ)⁻¹ • (z : G → V),
      ⟨(Formalism.WeaklyAdmissibleFiltrations.continuousCocycles ρ).smul_mem _ z.2.1, fun g _ => ?_⟩, ?_⟩
    · obtain ⟨y, hy, h⟩ := hz' g
      have : ((algebraMap O LL ϖ)⁻¹ • (z : G → V)) g = y := by
        rw [Pi.smul_apply, ← h, ← algebraMap_smul LL ϖ y, inv_smul_smul₀ hϖ]
      rw [this]
      exact hy
    · rw [← algebraMap_smul LL ϖ, smul_inv_smul₀ hϖ]
end UpperTheory.Reformulated.B.Gub2
