-- Prove2me | solution 1 for UpperTheory.Reformulated.B.BorelApproximation.dcos_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:33:43.413957+00:00
-- url     : https://prove2.me/submissions/5429990a-5c69-4c04-85ea-4321dc6914b0

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BorelApproximation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.BorelApproximation
theorem _root_.solution :
    ∀ {E : Type} [inst : Field E] [inst_1 : @NumberField E inst]
      [@NumberField.IsCMField E inst (@NumberField.to_charZero E inst inst_1)] {m : Nat}
      {w : @UpperTheory.Reformulated.B.BorelApproximation.Pl E inst inst_1} (t k g : @UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 m w),
      @Membership.mem (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 m w)
          (@Subgroup (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 m w)
            (@Units.instGroup
              (Matrix (Fin m) (Fin m)
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                  (@NumberField.instCommRingRingOfIntegers E inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
              (@Semiring.toMonoid
                (Matrix (Fin m) (Fin m)
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                    (@NumberField.instCommRingRingOfIntegers E inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                (@Matrix.semiring (Fin m)
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                    (@NumberField.instCommRingRingOfIntegers E inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                  (@DivisionSemiring.toSemiring
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                      (@NumberField.instCommRingRingOfIntegers E inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                    (@Semifield.toDivisionSemiring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                        (@NumberField.instCommRingRingOfIntegers E inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                      (@Field.toSemifield
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                  (Fin.fintype m) (instDecidableEqFin m)))))
          (@SetLike.instMembership
            (@Subgroup (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 m w)
              (@Units.instGroup
                (Matrix (Fin m) (Fin m)
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                    (@NumberField.instCommRingRingOfIntegers E inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                (@Semiring.toMonoid
                  (Matrix (Fin m) (Fin m)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                      (@NumberField.instCommRingRingOfIntegers E inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                  (@Matrix.semiring (Fin m)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                      (@NumberField.instCommRingRingOfIntegers E inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                    (@DivisionSemiring.toSemiring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                        (@NumberField.instCommRingRingOfIntegers E inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                      (@Semifield.toDivisionSemiring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                        (@Field.toSemifield
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                    (Fin.fintype m) (instDecidableEqFin m)))))
            (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 m w)
            (@Subgroup.instSetLike (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 m w)
              (@Units.instGroup
                (Matrix (Fin m) (Fin m)
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                    (@NumberField.instCommRingRingOfIntegers E inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                (@Semiring.toMonoid
                  (Matrix (Fin m) (Fin m)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                      (@NumberField.instCommRingRingOfIntegers E inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                  (@Matrix.semiring (Fin m)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                      (@NumberField.instCommRingRingOfIntegers E inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                    (@DivisionSemiring.toSemiring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                        (@NumberField.instCommRingRingOfIntegers E inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                      (@Semifield.toDivisionSemiring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                        (@Field.toSemifield
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                    (Fin.fintype m) (instDecidableEqFin m))))))
          (@UpperTheory.Reformulated.B.BorelApproximation.iwGL E inst inst_1 m w) k →
        @Eq Complex
          (@UpperTheory.Reformulated.B.BorelApproximation.dcos E inst inst_1 m w t
            (@HMul.hMul (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 m w) (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 m w)
              (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 m w)
              (@instHMul (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 m w)
                (@Units.instMul
                  (Matrix (Fin m) (Fin m)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                      (@NumberField.instCommRingRingOfIntegers E inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                  (@Semiring.toMonoid
                    (Matrix (Fin m) (Fin m)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                        (@NumberField.instCommRingRingOfIntegers E inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                    (@Matrix.semiring (Fin m)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                        (@NumberField.instCommRingRingOfIntegers E inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                      (@DivisionSemiring.toSemiring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                        (@Semifield.toDivisionSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                          (@Field.toSemifield
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                      (Fin.fintype m) (instDecidableEqFin m)))))
              k g))
          (@UpperTheory.Reformulated.B.BorelApproximation.dcos E inst inst_1 m w t g) := by
  intro E _ _ _ m w t k g hk
  unfold UpperTheory.Reformulated.B.BorelApproximation.dcos
  refine congrArg (fun P : Prop => @ite ℂ P (Classical.propDecidable P) 1 0) (propext ⟨?_, ?_⟩)
  · rintro ⟨x, hx, z, hz, h⟩
    refine ⟨k⁻¹ * x, mul_mem (inv_mem hk) hx, z, hz, ?_⟩
    rw [mul_assoc k⁻¹, mul_assoc k⁻¹, ← h, inv_mul_cancel_left]
  · rintro ⟨x, hx, z, hz, h⟩
    refine ⟨k * x, mul_mem hk hx, z, hz, ?_⟩
    rw [h, mul_assoc k, mul_assoc k]
end UpperTheory.Reformulated.B.BorelApproximation
