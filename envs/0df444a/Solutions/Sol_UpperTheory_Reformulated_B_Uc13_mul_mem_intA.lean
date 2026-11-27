-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Uc13.mul_mem_intA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:40:33.999+00:00
-- url     : https://prove2.me/submissions/edd970c8-c4e9-4e66-bd87-86c8f97675d5

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MulMemIntA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem UpperTheory.Reformulated.B.Uc13.intAf_mul (F : Type) [Field F] [NumberField F]
    {a b : UpperTheory.Reformulated.B.Uc13.Af F} (ha : a ∈ UpperTheory.Reformulated.B.Uc13.intAf F)
    (hb : b ∈ UpperTheory.Reformulated.B.Uc13.intAf F) : a * b ∈ UpperTheory.Reformulated.B.Uc13.intAf F := by
  intro v
  rw [map_mul]
  exact mul_mem (ha v) (hb v)
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Uc13
theorem _root_.solution :
    ∀ (F E : Type) [inst : Field F] [inst_1 : @NumberField F inst] [inst_2 : Field E] [@NumberField E inst_2]
      [inst_4 :
        @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))]
      {x y :
        @TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
          (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
            (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
          (@Semiring.toAddCommMonoid E
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
          (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
            (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
            (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
            (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst)
              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
          (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4)},
      @Membership.mem
          (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
            (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
            (@Semiring.toAddCommMonoid E
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
            (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
              (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
              (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
            (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
          (@AddSubgroup
            (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              E
              (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
              (@Semiring.toAddCommMonoid E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
              (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
              (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
            (@AddGroupWithOne.toAddGroup
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@Ring.toAddGroupWithOne
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@Algebra.TensorProduct.instRing F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommRing.toRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                  inst_4))))
          (@SetLike.instMembership
            (@AddSubgroup
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@AddGroupWithOne.toAddGroup
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@Ring.toAddGroupWithOne
                  (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))
                  (@Algebra.TensorProduct.instRing F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommRing.toRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))))
            (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              E
              (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
              (@Semiring.toAddCommMonoid E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
              (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
              (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
            (@AddSubgroup.instSetLike
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@AddGroupWithOne.toAddGroup
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@Ring.toAddGroupWithOne
                  (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))
                  (@Algebra.TensorProduct.instRing F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommRing.toRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4)))))
          (@UpperTheory.Reformulated.B.Uc13.intA F E inst inst_1 inst_2 inst_4) x →
        @Membership.mem
            (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              E
              (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
              (@Semiring.toAddCommMonoid E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
              (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
              (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
            (@AddSubgroup
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@AddGroupWithOne.toAddGroup
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@Ring.toAddGroupWithOne
                  (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))
                  (@Algebra.TensorProduct.instRing F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommRing.toRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))))
            (@SetLike.instMembership
              (@AddSubgroup
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@AddGroupWithOne.toAddGroup
                  (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))
                  (@Ring.toAddGroupWithOne
                    (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                      (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                            (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                      (@Semiring.toAddCommMonoid E
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                      (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                            (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                        (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                      (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                        inst_4))
                    (@Algebra.TensorProduct.instRing F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommRing.toRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))))
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@AddSubgroup.instSetLike
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@AddGroupWithOne.toAddGroup
                  (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))
                  (@Ring.toAddGroupWithOne
                    (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                      (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                            (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                      (@Semiring.toAddCommMonoid E
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                      (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                            (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                        (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                      (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                        inst_4))
                    (@Algebra.TensorProduct.instRing F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommRing.toRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4)))))
            (@UpperTheory.Reformulated.B.Uc13.intA F E inst inst_1 inst_2 inst_4) y →
          @Membership.mem
            (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              E
              (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
              (@Semiring.toAddCommMonoid E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
              (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
              (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
            (@AddSubgroup
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@AddGroupWithOne.toAddGroup
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@Ring.toAddGroupWithOne
                  (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))
                  (@Algebra.TensorProduct.instRing F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommRing.toRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))))
            (@SetLike.instMembership
              (@AddSubgroup
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@AddGroupWithOne.toAddGroup
                  (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))
                  (@Ring.toAddGroupWithOne
                    (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                      (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                            (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                      (@Semiring.toAddCommMonoid E
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                      (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                            (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                        (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                      (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                        inst_4))
                    (@Algebra.TensorProduct.instRing F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommRing.toRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))))
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@AddSubgroup.instSetLike
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@AddGroupWithOne.toAddGroup
                  (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                    (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4))
                  (@Ring.toAddGroupWithOne
                    (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                      (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                            (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                      (@Semiring.toAddCommMonoid E
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                      (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                            (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                        (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                      (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                        inst_4))
                    (@Algebra.TensorProduct.instRing F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommRing.toRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                      (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4)))))
            (@UpperTheory.Reformulated.B.Uc13.intA F E inst inst_1 inst_2 inst_4)
            (@HMul.hMul
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                  (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@instHMul
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semiring.toAddCommMonoid (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4))
                (@Algebra.TensorProduct.instMul F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) E
                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@CommRing.toNonUnitalCommRing (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                          (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))))
                  (@Algebra.toModule F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                      (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@Algebra.to_smulCommClass F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring
                      (@IsDedekindDomain.FiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                      (@CommRing.toCommSemiring
                        (@IsDedekindDomain.FiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@IsScalarTower.right F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring
                      (@IsDedekindDomain.FiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                      (@CommRing.toCommSemiring
                        (@IsDedekindDomain.FiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                        (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
                    (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring E
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing E
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing E
                        (@CommRing.toNonUnitalCommRing E (@Field.toCommRing E inst_2)))))
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4)
                  (@Algebra.to_smulCommClass F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4)
                  (@IsScalarTower.right F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    inst_4)))
              x y) := by
  intro F E _ _ _ _ _ x y hx hy
  unfold UpperTheory.Reformulated.B.Uc13.intA at *
  induction hx, hy using AddSubgroup.closure_induction₂ with
  | mem x y hx hy =>
    obtain ⟨a, ha, s, rfl⟩ := hx
    obtain ⟨b, hb, t, rfl⟩ := hy
    refine AddSubgroup.subset_closure
      ⟨a * b, UpperTheory.Reformulated.B.Uc13.intAf_mul F ha hb, s * t, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    rfl
  | zero_left x hx => rw [zero_mul]; exact zero_mem _
  | zero_right x hx => rw [mul_zero]; exact zero_mem _
  | add_left x y z hx hy hz h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | add_right y z x hy hz hx h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg_left x y hx hy h => rw [neg_mul]; exact neg_mem h
  | neg_right x y hx hy h => rw [mul_neg]; exact neg_mem h
end UpperTheory.Reformulated.B.Uc13
