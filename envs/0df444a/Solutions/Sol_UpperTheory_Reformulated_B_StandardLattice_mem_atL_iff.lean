-- Prove2me | solution 1 for UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:43:21.139046+00:00
-- url     : https://prove2.me/submissions/94aa65c6-8616-4cd9-a293-8065cd8989cd

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StandardLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
attribute [local instance] UpperTheory.Reformulated.B.StandardLattice.rlAlgebra
namespace UpperTheory.Reformulated.B.StandardLattice
theorem _root_.solution :
    ∀ (l : Nat) [hl : Fact (Nat.Prime l)] (K : Type) [inst : Field K] [inst_1 : @NumberField K inst] {V : Type}
      [inst_2 : AddCommGroup V]
      [inst_3 :
        @_root_.Module K V (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          (@AddCommGroup.toAddCommMonoid V inst_2)]
      [inst_4 :
        @_root_.Module (@NumberField.RingOfIntegers K inst) V
          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst)))
          (@AddCommGroup.toAddCommMonoid V inst_2)]
      [@IsScalarTower (@NumberField.RingOfIntegers K inst) K V
          (@Algebra.toSMul (@NumberField.RingOfIntegers K inst) K
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@NumberField.RingOfIntegers.instAlgebra_1 K inst))
          (@SMulZeroClass.toSMul K V
            (@AddZero.toZero V
              (@AddZeroClass.toAddZero V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_2))))))
            (@DistribSMul.toSMulZeroClass K V
              (@AddMonoid.toAddZeroClass V
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_2))))
              (@DistribMulAction.toDistribSMul K V
                (@Semiring.toMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_2)))
                (@Module.toDistribMulAction K V
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@AddCommGroup.toAddCommMonoid V inst_2) inst_3))))
          (@SMulZeroClass.toSMul (@NumberField.RingOfIntegers K inst) V
            (@AddZero.toZero V
              (@AddZeroClass.toAddZero V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_2))))))
            (@DistribSMul.toSMulZeroClass (@NumberField.RingOfIntegers K inst) V
              (@AddMonoid.toAddZeroClass V
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_2))))
              (@DistribMulAction.toDistribSMul (@NumberField.RingOfIntegers K inst) V
                (@Semiring.toMonoid (@NumberField.RingOfIntegers K inst)
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst))))
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_2)))
                (@Module.toDistribMulAction (@NumberField.RingOfIntegers K inst) V
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst)))
                  (@AddCommGroup.toAddCommMonoid V inst_2) inst_4))))]
      {L :
        @Submodule (@NumberField.RingOfIntegers K inst) V
          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst)))
          (@AddCommGroup.toAddCommMonoid V inst_2) inst_4}
      {x : V},
      Iff
        (@Membership.mem V
          (@Submodule (@UpperTheory.Reformulated.B.StandardLattice.Rl l hl K inst) V
            (@OreLocalization.instSemiring (@NumberField.RingOfIntegers K inst)
              (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst)))
              (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)
              (@OreLocalization.oreSetComm (@NumberField.RingOfIntegers K inst)
                (@CommRing.toCommMonoid (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst))
                (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)))
            (@AddCommGroup.toAddCommMonoid V inst_2) (@UpperTheory.Reformulated.B.StandardLattice.rlModule l hl K inst inst_1 V inst_2 inst_3))
          (@SetLike.instMembership
            (@Submodule (@UpperTheory.Reformulated.B.StandardLattice.Rl l hl K inst) V
              (@OreLocalization.instSemiring (@NumberField.RingOfIntegers K inst)
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst)))
                (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)
                (@OreLocalization.oreSetComm (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommMonoid (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst))
                  (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)))
              (@AddCommGroup.toAddCommMonoid V inst_2) (@UpperTheory.Reformulated.B.StandardLattice.rlModule l hl K inst inst_1 V inst_2 inst_3))
            V
            (@Submodule.setLike (@UpperTheory.Reformulated.B.StandardLattice.Rl l hl K inst) V
              (@OreLocalization.instSemiring (@NumberField.RingOfIntegers K inst)
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst)))
                (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)
                (@OreLocalization.oreSetComm (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommMonoid (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst))
                  (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)))
              (@AddCommGroup.toAddCommMonoid V inst_2) (@UpperTheory.Reformulated.B.StandardLattice.rlModule l hl K inst inst_1 V inst_2 inst_3)))
          (@UpperTheory.Reformulated.B.StandardLattice.atL l hl K inst inst_1 V inst_2 inst_3 inst_4 L) x)
        (∃ (s : @NumberField.RingOfIntegers K inst),
          And
            (@Membership.mem (@NumberField.RingOfIntegers K inst)
              (@Submonoid (@NumberField.RingOfIntegers K inst)
                (@MulZeroOneClass.toMulOneClass (@NumberField.RingOfIntegers K inst)
                  (@instMulZeroOneClassOfSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                      (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                        (@NumberField.instCommRingRingOfIntegers K inst))))))
              (@SetLike.instMembership
                (@Submonoid (@NumberField.RingOfIntegers K inst)
                  (@MulZeroOneClass.toMulOneClass (@NumberField.RingOfIntegers K inst)
                    (@instMulZeroOneClassOfSemiring (@NumberField.RingOfIntegers K inst)
                      (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                        (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                          (@NumberField.instCommRingRingOfIntegers K inst))))))
                (@NumberField.RingOfIntegers K inst)
                (@Submonoid.instSetLike (@NumberField.RingOfIntegers K inst)
                  (@MulZeroOneClass.toMulOneClass (@NumberField.RingOfIntegers K inst)
                    (@instMulZeroOneClassOfSemiring (@NumberField.RingOfIntegers K inst)
                      (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                        (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                          (@NumberField.instCommRingRingOfIntegers K inst)))))))
              (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst) s)
            (@Membership.mem V
              (@Submodule (@NumberField.RingOfIntegers K inst) V
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst)))
                (@AddCommGroup.toAddCommMonoid V inst_2) inst_4)
              (@SetLike.instMembership
                (@Submodule (@NumberField.RingOfIntegers K inst) V
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst)))
                  (@AddCommGroup.toAddCommMonoid V inst_2) inst_4)
                V
                (@Submodule.setLike (@NumberField.RingOfIntegers K inst) V
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst)))
                  (@AddCommGroup.toAddCommMonoid V inst_2) inst_4))
              L
              (@HSMul.hSMul (@NumberField.RingOfIntegers K inst) V V
                (@instHSMul (@NumberField.RingOfIntegers K inst) V
                  (@SMulZeroClass.toSMul (@NumberField.RingOfIntegers K inst) V
                    (@AddZero.toZero V
                      (@AddZeroClass.toAddZero V
                        (@AddMonoid.toAddZeroClass V
                          (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_2))))))
                    (@DistribSMul.toSMulZeroClass (@NumberField.RingOfIntegers K inst) V
                      (@AddMonoid.toAddZeroClass V
                        (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_2))))
                      (@DistribMulAction.toDistribSMul (@NumberField.RingOfIntegers K inst) V
                        (@Semiring.toMonoid (@NumberField.RingOfIntegers K inst)
                          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                              (@NumberField.instCommRingRingOfIntegers K inst))))
                        (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_2)))
                        (@Module.toDistribMulAction (@NumberField.RingOfIntegers K inst) V
                          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                              (@NumberField.instCommRingRingOfIntegers K inst)))
                          (@AddCommGroup.toAddCommMonoid V inst_2) inst_4)))))
                s x))) := by
  intro l hl K inst inst_1 V inst_2 inst_3 inst_4 tower L x
  letI := UpperTheory.Reformulated.B.StandardLattice.rlModule l K V
  have hact : ∀ (r : NumberField.RingOfIntegers K) (v : V),
      (algebraMap (NumberField.RingOfIntegers K) (UpperTheory.Reformulated.B.StandardLattice.Rl l K) r) • v = r • v := by
    intro r v
    change UpperTheory.Reformulated.B.StandardLattice.rlToK l K (algebraMap _ _ r) • v = r • v
    unfold UpperTheory.Reformulated.B.StandardLattice.rlToK
    rw [IsLocalization.lift_eq, algebraMap_smul]
  haveI : IsScalarTower (NumberField.RingOfIntegers K) (UpperTheory.Reformulated.B.StandardLattice.Rl l K) V :=
    IsScalarTower.of_algebraMap_smul hact
  unfold UpperTheory.Reformulated.B.StandardLattice.atL
  rw [IsLocalization.mem_span_iff (UpperTheory.Reformulated.B.StandardLattice.Ml l K), Submodule.span_eq]
  constructor
  · rintro ⟨y, hy, z, rfl⟩
    refine ⟨z, z.2, ?_⟩
    rw [← hact, smul_smul, IsLocalization.mk'_spec', map_one, one_smul]
    exact hy
  · rintro ⟨s, hs, hx⟩
    refine ⟨s • x, hx, ⟨s, hs⟩, ?_⟩
    rw [← hact, smul_smul]
    have := IsLocalization.mk'_spec (UpperTheory.Reformulated.B.StandardLattice.Rl l K) (1 : NumberField.RingOfIntegers K)
      (⟨s, hs⟩ : UpperTheory.Reformulated.B.StandardLattice.Ml l K)
    rw [this, map_one, one_smul]
end UpperTheory.Reformulated.B.StandardLattice
