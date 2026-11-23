-- Prove2me | solution 1 for UpperTheory.Reformulated.B.MapPowSub.map_pow_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:04.04638+00:00
-- url     : https://prove2.me/submissions/d967f519-a9ac-44de-89ed-9fe37a9c6888

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapPowSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.MapPowSub
theorem _root_.solution :
    ∀ {K : Type} [inst : Field K]
      {σ :
        @RingHom K Complex
          (@Semiring.toNonAssocSemiring K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)}
      {V E : Type} [inst_1 : AddCommGroup V]
      [inst_2 :
        @_root_.Module K V (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          (@AddCommGroup.toAddCommMonoid V inst_1)]
      [inst_3 : AddCommGroup E]
      [inst_4 : @_root_.Module Complex E Complex.instSemiring (@AddCommGroup.toAddCommMonoid E inst_3)]
      (f :
        @LinearMap K Complex (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          Complex.instSemiring σ V E (@AddCommGroup.toAddCommMonoid V inst_1) (@AddCommGroup.toAddCommMonoid E inst_3)
          inst_2 inst_4)
      (T :
        @Module.End K V (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          (@AddCommGroup.toAddCommMonoid V inst_1) inst_2)
      (S : @Module.End Complex E Complex.instSemiring (@AddCommGroup.toAddCommMonoid E inst_3) inst_4),
      (∀ (v : V),
          @Eq E
            (@DFunLike.coe
              (@LinearMap K Complex
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                Complex.instSemiring σ V E (@AddCommGroup.toAddCommMonoid V inst_1) (@AddCommGroup.toAddCommMonoid E inst_3)
                inst_2 inst_4)
              V (fun (x : V) ↦ E)
              (@LinearMap.instFunLike K Complex V E
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                Complex.instSemiring (@AddCommGroup.toAddCommMonoid V inst_1) (@AddCommGroup.toAddCommMonoid E inst_3)
                inst_2 inst_4 σ)
              f
              (@DFunLike.coe
                (@Module.End K V
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@AddCommGroup.toAddCommMonoid V inst_1) inst_2)
                V (fun (x : V) ↦ V)
                (@LinearMap.instFunLike K K V V
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@AddCommGroup.toAddCommMonoid V inst_1) (@AddCommGroup.toAddCommMonoid V inst_1) inst_2 inst_2
                  (@RingHom.id K
                    (@Semiring.toNonAssocSemiring K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
                T v))
            (@DFunLike.coe (@Module.End Complex E Complex.instSemiring (@AddCommGroup.toAddCommMonoid E inst_3) inst_4) E
              (fun (x : E) ↦ E)
              (@LinearMap.instFunLike Complex Complex E E Complex.instSemiring Complex.instSemiring
                (@AddCommGroup.toAddCommMonoid E inst_3) (@AddCommGroup.toAddCommMonoid E inst_3) inst_4 inst_4
                (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)))
              S
              (@DFunLike.coe
                (@LinearMap K Complex
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  Complex.instSemiring σ V E (@AddCommGroup.toAddCommMonoid V inst_1)
                  (@AddCommGroup.toAddCommMonoid E inst_3) inst_2 inst_4)
                V (fun (x : V) ↦ E)
                (@LinearMap.instFunLike K Complex V E
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  Complex.instSemiring (@AddCommGroup.toAddCommMonoid V inst_1) (@AddCommGroup.toAddCommMonoid E inst_3)
                  inst_2 inst_4 σ)
                f v))) →
        ∀ (a : K) (k : Nat) (v : V),
          @Eq E
            (@DFunLike.coe
              (@LinearMap K Complex
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                Complex.instSemiring σ V E (@AddCommGroup.toAddCommMonoid V inst_1) (@AddCommGroup.toAddCommMonoid E inst_3)
                inst_2 inst_4)
              V (fun (x : V) ↦ E)
              (@LinearMap.instFunLike K Complex V E
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                Complex.instSemiring (@AddCommGroup.toAddCommMonoid V inst_1) (@AddCommGroup.toAddCommMonoid E inst_3)
                inst_2 inst_4 σ)
              f
              (@DFunLike.coe
                (@Module.End K V
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@AddCommGroup.toAddCommMonoid V inst_1) inst_2)
                V (fun (x : V) ↦ V)
                (@LinearMap.instFunLike K K V V
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@AddCommGroup.toAddCommMonoid V inst_1) (@AddCommGroup.toAddCommMonoid V inst_1) inst_2 inst_2
                  (@RingHom.id K
                    (@Semiring.toNonAssocSemiring K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
                (@HPow.hPow
                  (@Module.End K V
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                    (@AddCommGroup.toAddCommMonoid V inst_1) inst_2)
                  Nat
                  (@Module.End K V
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                    (@AddCommGroup.toAddCommMonoid V inst_1) inst_2)
                  (@instHPow
                    (@Module.End K V
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                      (@AddCommGroup.toAddCommMonoid V inst_1) inst_2)
                    Nat
                    (@NPow.toPow
                      (@Module.End K V
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                        (@AddCommGroup.toAddCommMonoid V inst_1) inst_2)
                      (@Monoid.toNPow
                        (@Module.End K V
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                          (@AddCommGroup.toAddCommMonoid V inst_1) inst_2)
                        (@Module.End.instMonoid K V
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                          (@AddCommGroup.toAddCommMonoid V inst_1) inst_2))))
                  (@HSub.hSub
                    (@Module.End K V
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                      (@AddCommGroup.toAddCommMonoid V inst_1) inst_2)
                    (@Module.End K V
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                      (@AddCommGroup.toAddCommMonoid V inst_1) inst_2)
                    (@Module.End K V
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                      (@AddCommGroup.toAddCommMonoid V inst_1) inst_2)
                    (@instHSub
                      (@Module.End K V
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                        (@AddCommGroup.toAddCommMonoid V inst_1) inst_2)
                      (@LinearMap.instSub K K V V
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                        (@AddCommGroup.toAddCommMonoid V inst_1) inst_1 inst_2 inst_2
                        (@RingHom.id K
                          (@Semiring.toNonAssocSemiring K
                            (@DivisionSemiring.toSemiring K
                              (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))))
                    T
                    (@HSMul.hSMul K
                      (@Module.End K V
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                        (@AddCommGroup.toAddCommMonoid V inst_1) inst_2)
                      (@Module.End K V
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                        (@AddCommGroup.toAddCommMonoid V inst_1) inst_2)
                      (@instHSMul K
                        (@Module.End K V
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                          (@AddCommGroup.toAddCommMonoid V inst_1) inst_2)
                        (@LinearMap.instSMul K K K V V
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                          (@AddCommGroup.toAddCommMonoid V inst_1) (@AddCommGroup.toAddCommMonoid V inst_1) inst_2 inst_2
                          (@RingHom.id K
                            (@Semiring.toNonAssocSemiring K
                              (@DivisionSemiring.toSemiring K
                                (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                          (@DistribMulAction.toDistribSMul K V
                            (@Semiring.toMonoid K
                              (@DivisionSemiring.toSemiring K
                                (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                            (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_1)))
                            (@Module.toDistribMulAction K V
                              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                              (@AddCommGroup.toAddCommMonoid V inst_1) inst_2))
                          (@smulCommClass_self K V (@CommRing.toCommMonoid K (@Field.toCommRing K inst))
                            (@DistribMulAction.toMulAction K V
                              (@CommMonoid.toMonoid K (@CommRing.toCommMonoid K (@Field.toCommRing K inst)))
                              (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_1))
                              (@Module.toDistribMulAction K V
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                                (@AddCommGroup.toAddCommMonoid V inst_1) inst_2)))))
                      a
                      (@OfNat.ofNat
                        (@Module.End K V
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                          (@AddCommGroup.toAddCommMonoid V inst_1) inst_2)
                        (nat_lit 1)
                        (@One.toOfNat1
                          (@Module.End K V
                            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                            (@AddCommGroup.toAddCommMonoid V inst_1) inst_2)
                          (@Module.End.instOne K V
                            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                            (@AddCommGroup.toAddCommMonoid V inst_1) inst_2)))))
                  k)
                v))
            (@DFunLike.coe (@Module.End Complex E Complex.instSemiring (@AddCommGroup.toAddCommMonoid E inst_3) inst_4) E
              (fun (x : E) ↦ E)
              (@LinearMap.instFunLike Complex Complex E E Complex.instSemiring Complex.instSemiring
                (@AddCommGroup.toAddCommMonoid E inst_3) (@AddCommGroup.toAddCommMonoid E inst_3) inst_4 inst_4
                (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)))
              (@HPow.hPow (@Module.End Complex E Complex.instSemiring (@AddCommGroup.toAddCommMonoid E inst_3) inst_4) Nat
                (@Module.End Complex E Complex.instSemiring (@AddCommGroup.toAddCommMonoid E inst_3) inst_4)
                (@instHPow (@Module.End Complex E Complex.instSemiring (@AddCommGroup.toAddCommMonoid E inst_3) inst_4) Nat
                  (@NPow.toPow (@Module.End Complex E Complex.instSemiring (@AddCommGroup.toAddCommMonoid E inst_3) inst_4)
                    (@Monoid.toNPow
                      (@Module.End Complex E Complex.instSemiring (@AddCommGroup.toAddCommMonoid E inst_3) inst_4)
                      (@Module.End.instMonoid Complex E Complex.instSemiring (@AddCommGroup.toAddCommMonoid E inst_3)
                        inst_4))))
                (@HSub.hSub (@Module.End Complex E Complex.instSemiring (@AddCommGroup.toAddCommMonoid E inst_3) inst_4)
                  (@Module.End Complex E Complex.instSemiring (@AddCommGroup.toAddCommMonoid E inst_3) inst_4)
                  (@Module.End Complex E Complex.instSemiring (@AddCommGroup.toAddCommMonoid E inst_3) inst_4)
                  (@instHSub (@Module.End Complex E Complex.instSemiring (@AddCommGroup.toAddCommMonoid E inst_3) inst_4)
                    (@LinearMap.instSub Complex Complex E E Complex.instSemiring Complex.instSemiring
                      (@AddCommGroup.toAddCommMonoid E inst_3) inst_3 inst_4 inst_4
                      (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))))
                  S
                  (@HSMul.hSMul Complex
                    (@Module.End Complex E Complex.instSemiring (@AddCommGroup.toAddCommMonoid E inst_3) inst_4)
                    (@Module.End Complex E Complex.instSemiring (@AddCommGroup.toAddCommMonoid E inst_3) inst_4)
                    (@instHSMul Complex
                      (@Module.End Complex E Complex.instSemiring (@AddCommGroup.toAddCommMonoid E inst_3) inst_4)
                      (@LinearMap.instSMul Complex Complex Complex E E Complex.instSemiring Complex.instSemiring
                        (@AddCommGroup.toAddCommMonoid E inst_3) (@AddCommGroup.toAddCommMonoid E inst_3) inst_4 inst_4
                        (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))
                        (@DistribMulAction.toDistribSMul Complex E (@Semiring.toMonoid Complex Complex.instSemiring)
                          (@SubNegMonoid.toAddMonoid E (@AddGroup.toSubNegMonoid E (@AddCommGroup.toAddGroup E inst_3)))
                          (@Module.toDistribMulAction Complex E Complex.instSemiring
                            (@AddCommGroup.toAddCommMonoid E inst_3) inst_4))
                        (@smulCommClass_self Complex E (@CommRing.toCommMonoid Complex Complex.commRing)
                          (@DistribMulAction.toMulAction Complex E
                            (@CommMonoid.toMonoid Complex (@CommRing.toCommMonoid Complex Complex.commRing))
                            (@AddCommMonoid.toAddMonoid E (@AddCommGroup.toAddCommMonoid E inst_3))
                            (@Module.toDistribMulAction Complex E Complex.instSemiring
                              (@AddCommGroup.toAddCommMonoid E inst_3) inst_4)))))
                    (@DFunLike.coe
                      (@RingHom K Complex
                        (@Semiring.toNonAssocSemiring K
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                        (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))
                      K (fun (x : K) ↦ Complex)
                      (@RingHom.instFunLike K Complex
                        (@Semiring.toNonAssocSemiring K
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                        (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))
                      σ a)
                    (@OfNat.ofNat
                      (@Module.End Complex E Complex.instSemiring (@AddCommGroup.toAddCommMonoid E inst_3) inst_4)
                      (nat_lit 1)
                      (@One.toOfNat1
                        (@Module.End Complex E Complex.instSemiring (@AddCommGroup.toAddCommMonoid E inst_3) inst_4)
                        (@Module.End.instOne Complex E Complex.instSemiring (@AddCommGroup.toAddCommMonoid E inst_3)
                          inst_4)))))
                k)
              (@DFunLike.coe
                (@LinearMap K Complex
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  Complex.instSemiring σ V E (@AddCommGroup.toAddCommMonoid V inst_1)
                  (@AddCommGroup.toAddCommMonoid E inst_3) inst_2 inst_4)
                V (fun (x : V) ↦ E)
                (@LinearMap.instFunLike K Complex V E
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  Complex.instSemiring (@AddCommGroup.toAddCommMonoid V inst_1) (@AddCommGroup.toAddCommMonoid E inst_3)
                  inst_2 inst_4 σ)
                f v)) := by
  intro K _ σ V E _ _ _ _ f T S h a k
  have h1 : ∀ v : V, f ((T - a • (1 : Module.End K V)) v) = (S - σ a • (1 : Module.End ℂ E)) (f v) := by
    intro v
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, h, LinearMap.map_smulₛₗ]
  induction k with
  | zero => intro v; simp only [pow_zero, Module.End.one_apply]
  | succ n ih =>
    intro v
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h1]
end UpperTheory.Reformulated.B.MapPowSub
