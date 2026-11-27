-- Prove2me | solution 1 for UpperTheory.Reformulated.B.H23.dcos_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:33:06.415208+00:00
-- url     : https://prove2.me/submissions/c99eed77-043e-494a-b45f-4f30d07ff7d4

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ZeroContDiffOnSupported

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.H23
theorem _root_.solution :
    ∀ {E : Type} [inst : Field E] [inst_1 : @NumberField E inst]
      [@NumberField.IsCMField E inst (@NumberField.to_charZero E inst inst_1)] {m : Nat}
      {w : @UpperTheory.Reformulated.B.H23.Pl E inst inst_1} (t k g : @UpperTheory.Reformulated.B.H23.GLw E inst inst_1 m w),
      @Membership.mem (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 m w)
          (@Subgroup (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 m w)
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
            (@Subgroup (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 m w)
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
            (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 m w)
            (@Subgroup.instSetLike (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 m w)
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
          (@UpperTheory.Reformulated.B.H23.iwGL E inst inst_1 m w) k →
        @Eq Complex
          (@UpperTheory.Reformulated.B.H23.dcos E inst inst_1 m w t
            (@HMul.hMul (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 m w) (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 m w)
              (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 m w)
              (@instHMul (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 m w)
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
              g k))
          (@UpperTheory.Reformulated.B.H23.dcos E inst inst_1 m w t g) := by
  intro E _ _ _ m w t k g hk
  unfold UpperTheory.Reformulated.B.H23.dcos
  refine @if_congr _ _ _ (Classical.propDecidable _) (Classical.propDecidable _) _ _ _ _
    ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨x, hx, z, hz, h⟩
    exact ⟨x, hx, z * k⁻¹, Subgroup.mul_mem _ hz (Subgroup.inv_mem _ hk), by
      rw [← mul_assoc, ← h, mul_inv_cancel_right]⟩
  · rintro ⟨x, hx, z, hz, h⟩
    exact ⟨x, hx, z * k, Subgroup.mul_mem _ hz hk, by rw [h, mul_assoc (x * t)]⟩
end UpperTheory.Reformulated.B.H23
