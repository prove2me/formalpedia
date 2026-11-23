-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Re3.hloweq_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:47.832242+00:00
-- url     : https://prove2.me/submissions/64482bc3-8280-402e-beb2-7054880b863c

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ComplexNormedInstanceCompat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
attribute [local instance] UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ
private theorem UpperTheory.Reformulated.B.Re3.transfer_gen {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin n → Bool} {Λ : Fin n → ℝ} (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) (A : H →ₗ[ℂ] H)
    (hA : ∀ k ∈ UpperTheory.Reformulated.B.Re3.d21 ε, ∀ x : H, A (σ k x) = σ k (A x))
    {S : Submodule ℂ H} (hinj : ∀ w ∈ S, A w = 0 → w = 0)
    (hS : UpperTheory.Reformulated.B.Re3.IsKTypeOf ε σ Λ S) :
    UpperTheory.Reformulated.B.Re3.IsKTypeOf ε σ Λ (Submodule.map A S) := by
  obtain ⟨hfd, hst, hirr, ⟨v, hvS, hv0, hvw⟩, hdom⟩ := hS
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · rintro g hg _ ⟨w, hw, rfl⟩
    exact ⟨σ g w, hst g hg w hw, hA g hg w⟩
  · intro S' hS' hst'
    have hT : UpperTheory.Reformulated.B.Re3.IsKStableOn ε σ (S ⊓ Submodule.comap A S') := by
      intro g hg w hw
      refine ⟨hst g hg w hw.1, ?_⟩
      show A (σ g w) ∈ S'
      rw [hA g hg w]
      exact hst' g hg _ hw.2
    rcases hirr _ inf_le_left hT with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hS' hx
      have hw0 : w ∈ S ⊓ Submodule.comap A S' := ⟨hw, hx⟩
      rw [h, Submodule.mem_bot] at hw0
      simp [hw0]
    · right
      refine le_antisymm hS' ?_
      rintro _ ⟨w, hw, rfl⟩
      have hw1 : w ∈ S ⊓ Submodule.comap A S' := by rw [h]; exact hw
      exact hw1.2
  · refine ⟨A v, ⟨v, hvS, rfl⟩, fun h => hv0 (hinj v hvS h), ?_⟩
    intro θ hθ
    rw [← hA _ hθ, hvw θ hθ, map_smul]
  · rintro μ _ ⟨w, hw, rfl⟩ hw0 hwt
    refine hdom μ w hw (fun h => hw0 (by simp [h])) ?_
    intro θ hθ
    apply sub_eq_zero.mp
    apply hinj _ (S.sub_mem (hst _ hθ w hw) (S.smul_mem _ hw))
    rw [map_sub, map_smul, hA _ hθ, hwt θ hθ, sub_self]
end

set_option autoImplicit false
attribute [local instance] UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ
namespace UpperTheory.Reformulated.B.Re3
theorem _root_.solution :
    ∀ {n : Nat} {ε : Fin n → Bool} {Λ : Fin n → Real}
      (A :
        @LinearMap Complex Complex Complex.instSemiring Complex.instSemiring
          (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) (@UpperTheory.Reformulated.B.Re3.L2 n ε)
          (@UpperTheory.Reformulated.B.Re3.L2 n ε)
          (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
            (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
              (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
              (@OfNat.ofNat ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                  UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
              (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
          (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
            (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
              (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
              (@OfNat.ofNat ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                  UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
              (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
          (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
            (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
            (@OfNat.ofNat ENNReal (nat_lit 2)
              (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                (@AddMonoidWithOne.toNatCast ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
            (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
            (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
            (@Semiring.toModule Complex
              (@Ring.toSemiring Complex
                (@NormedRing.toRing Complex
                  (@CStarAlgebra.toNormedRing Complex
                    (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
            (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
              (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                  (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                    (@NormedCommRing.toSeminormedCommRing Complex
                      (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
              (@NonUnitalCStarAlgebra.toNormedSpace Complex
                (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                  (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
          (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
            (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
            (@OfNat.ofNat ENNReal (nat_lit 2)
              (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                (@AddMonoidWithOne.toNatCast ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
            (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
            (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
            (@Semiring.toModule Complex
              (@Ring.toSemiring Complex
                (@NormedRing.toRing Complex
                  (@CStarAlgebra.toNormedRing Complex
                    (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
            (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
              (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                  (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                    (@NormedCommRing.toSeminormedCommRing Complex
                      (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
              (@NonUnitalCStarAlgebra.toNormedSpace Complex
                (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                  (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))),
      (∀ (k : Matrix (Fin n) (Fin n) Complex),
          @Membership.mem (Matrix (Fin n) (Fin n) Complex) (Set (Matrix (Fin n) (Fin n) Complex))
              (@Set.instMembership (Matrix (Fin n) (Fin n) Complex)) (@UpperTheory.Reformulated.B.Re3.Kset n ε) k →
            ∀ (x : @UpperTheory.Reformulated.B.Re3.L2 n ε),
              @Eq (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                (@DFunLike.coe
                  (@LinearMap Complex Complex Complex.instSemiring Complex.instSemiring
                    (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))
                    (@UpperTheory.Reformulated.B.Re3.L2 n ε) (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                    (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                    (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                    (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                      (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                      (@OfNat.ofNat ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                          UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                      (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                      (@CStarAlgebra.toNormedRing Complex
                        (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                      (@Semiring.toModule Complex
                        (@Ring.toSemiring Complex
                          (@NormedRing.toRing Complex
                            (@CStarAlgebra.toNormedRing Complex
                              (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                      (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                            (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                              (@NormedCommRing.toSeminormedCommRing Complex
                                (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                        (@NonUnitalCStarAlgebra.toNormedSpace Complex
                          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                    (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                      (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                      (@OfNat.ofNat ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                          UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                      (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                      (@CStarAlgebra.toNormedRing Complex
                        (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                      (@Semiring.toModule Complex
                        (@Ring.toSemiring Complex
                          (@NormedRing.toRing Complex
                            (@CStarAlgebra.toNormedRing Complex
                              (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                      (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                            (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                              (@NormedCommRing.toSeminormedCommRing Complex
                                (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                        (@NonUnitalCStarAlgebra.toNormedSpace Complex
                          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex))))))
                  (@UpperTheory.Reformulated.B.Re3.L2 n ε) (fun (x : @UpperTheory.Reformulated.B.Re3.L2 n ε) ↦ @UpperTheory.Reformulated.B.Re3.L2 n ε)
                  (@LinearMap.instFunLike Complex Complex (@UpperTheory.Reformulated.B.Re3.L2 n ε) (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                    Complex.instSemiring Complex.instSemiring
                    (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                    (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                    (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                      (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                      (@OfNat.ofNat ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                          UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                      (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                      (@CStarAlgebra.toNormedRing Complex
                        (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                      (@Semiring.toModule Complex
                        (@Ring.toSemiring Complex
                          (@NormedRing.toRing Complex
                            (@CStarAlgebra.toNormedRing Complex
                              (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                      (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                            (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                              (@NormedCommRing.toSeminormedCommRing Complex
                                (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                        (@NonUnitalCStarAlgebra.toNormedSpace Complex
                          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                    (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                      (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                      (@OfNat.ofNat ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                          UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                      (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                      (@CStarAlgebra.toNormedRing Complex
                        (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                      (@Semiring.toModule Complex
                        (@Ring.toSemiring Complex
                          (@NormedRing.toRing Complex
                            (@CStarAlgebra.toNormedRing Complex
                              (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                      (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                            (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                              (@NormedCommRing.toSeminormedCommRing Complex
                                (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                        (@NonUnitalCStarAlgebra.toNormedSpace Complex
                          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                    (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)))
                  A
                  (@DFunLike.coe
                    (@ContinuousLinearMap Complex Complex Complex.instSemiring Complex.instSemiring
                      (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))
                      (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                          (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                            (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                              (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                                (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                                (@OfNat.ofNat ENNReal (nat_lit 2)
                                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                    (@AddMonoidWithOne.toNatCast ENNReal
                                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                    UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                                (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
                      (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                      (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                          (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                            (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                              (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                                (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                                (@OfNat.ofNat ENNReal (nat_lit 2)
                                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                    (@AddMonoidWithOne.toNatCast ENNReal
                                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                    UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                                (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
                      (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                      (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                        (@CStarAlgebra.toNormedRing Complex
                          (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                        (@Semiring.toModule Complex
                          (@Ring.toSemiring Complex
                            (@NormedRing.toRing Complex
                              (@CStarAlgebra.toNormedRing Complex
                                (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                        (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                              (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                                (@NormedCommRing.toSeminormedCommRing Complex
                                  (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                          (@NonUnitalCStarAlgebra.toNormedSpace Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                      (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                        (@CStarAlgebra.toNormedRing Complex
                          (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                        (@Semiring.toModule Complex
                          (@Ring.toSemiring Complex
                            (@NormedRing.toRing Complex
                              (@CStarAlgebra.toNormedRing Complex
                                (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                        (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                              (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                                (@NormedCommRing.toSeminormedCommRing Complex
                                  (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                          (@NonUnitalCStarAlgebra.toNormedSpace Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex))))))
                    (@UpperTheory.Reformulated.B.Re3.L2 n ε) (fun (x : @UpperTheory.Reformulated.B.Re3.L2 n ε) ↦ @UpperTheory.Reformulated.B.Re3.L2 n ε)
                    (@ContinuousLinearMap.funLike Complex Complex Complex.instSemiring Complex.instSemiring
                      (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))
                      (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                          (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                            (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                              (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                                (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                                (@OfNat.ofNat ENNReal (nat_lit 2)
                                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                    (@AddMonoidWithOne.toNatCast ENNReal
                                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                    UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                                (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
                      (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                      (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                          (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                            (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                              (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                                (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                                (@OfNat.ofNat ENNReal (nat_lit 2)
                                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                    (@AddMonoidWithOne.toNatCast ENNReal
                                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                    UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                                (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
                      (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                      (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                        (@CStarAlgebra.toNormedRing Complex
                          (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                        (@Semiring.toModule Complex
                          (@Ring.toSemiring Complex
                            (@NormedRing.toRing Complex
                              (@CStarAlgebra.toNormedRing Complex
                                (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                        (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                              (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                                (@NormedCommRing.toSeminormedCommRing Complex
                                  (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                          (@NonUnitalCStarAlgebra.toNormedSpace Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                      (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                        (@CStarAlgebra.toNormedRing Complex
                          (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                        (@Semiring.toModule Complex
                          (@Ring.toSemiring Complex
                            (@NormedRing.toRing Complex
                              (@CStarAlgebra.toNormedRing Complex
                                (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                        (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                              (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                                (@NormedCommRing.toSeminormedCommRing Complex
                                  (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                          (@NonUnitalCStarAlgebra.toNormedSpace Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex))))))
                    (@UpperTheory.Reformulated.B.Re3.rreg n ε k) x))
                (@DFunLike.coe
                  (@ContinuousLinearMap Complex Complex Complex.instSemiring Complex.instSemiring
                    (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))
                    (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                    (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                          (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                            (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                              (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                              (@OfNat.ofNat ENNReal (nat_lit 2)
                                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                  (@AddMonoidWithOne.toNatCast ENNReal
                                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                  UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                              (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
                    (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                    (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                    (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                          (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                            (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                              (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                              (@OfNat.ofNat ENNReal (nat_lit 2)
                                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                  (@AddMonoidWithOne.toNatCast ENNReal
                                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                  UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                              (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
                    (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                    (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                      (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                      (@OfNat.ofNat ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                          UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                      (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                      (@CStarAlgebra.toNormedRing Complex
                        (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                      (@Semiring.toModule Complex
                        (@Ring.toSemiring Complex
                          (@NormedRing.toRing Complex
                            (@CStarAlgebra.toNormedRing Complex
                              (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                      (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                            (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                              (@NormedCommRing.toSeminormedCommRing Complex
                                (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                        (@NonUnitalCStarAlgebra.toNormedSpace Complex
                          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                    (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                      (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                      (@OfNat.ofNat ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                          UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                      (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                      (@CStarAlgebra.toNormedRing Complex
                        (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                      (@Semiring.toModule Complex
                        (@Ring.toSemiring Complex
                          (@NormedRing.toRing Complex
                            (@CStarAlgebra.toNormedRing Complex
                              (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                      (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                            (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                              (@NormedCommRing.toSeminormedCommRing Complex
                                (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                        (@NonUnitalCStarAlgebra.toNormedSpace Complex
                          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex))))))
                  (@UpperTheory.Reformulated.B.Re3.L2 n ε) (fun (x : @UpperTheory.Reformulated.B.Re3.L2 n ε) ↦ @UpperTheory.Reformulated.B.Re3.L2 n ε)
                  (@ContinuousLinearMap.funLike Complex Complex Complex.instSemiring Complex.instSemiring
                    (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))
                    (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                    (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                          (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                            (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                              (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                              (@OfNat.ofNat ENNReal (nat_lit 2)
                                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                  (@AddMonoidWithOne.toNatCast ENNReal
                                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                  UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                              (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
                    (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                    (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                    (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                          (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                            (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                              (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                              (@OfNat.ofNat ENNReal (nat_lit 2)
                                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                  (@AddMonoidWithOne.toNatCast ENNReal
                                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                  UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                              (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
                    (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                    (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                      (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                      (@OfNat.ofNat ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                          UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                      (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                      (@CStarAlgebra.toNormedRing Complex
                        (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                      (@Semiring.toModule Complex
                        (@Ring.toSemiring Complex
                          (@NormedRing.toRing Complex
                            (@CStarAlgebra.toNormedRing Complex
                              (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                      (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                            (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                              (@NormedCommRing.toSeminormedCommRing Complex
                                (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                        (@NonUnitalCStarAlgebra.toNormedSpace Complex
                          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                    (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                      (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                      (@OfNat.ofNat ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                          UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                      (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                      (@CStarAlgebra.toNormedRing Complex
                        (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                      (@Semiring.toModule Complex
                        (@Ring.toSemiring Complex
                          (@NormedRing.toRing Complex
                            (@CStarAlgebra.toNormedRing Complex
                              (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                      (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                            (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                              (@NormedCommRing.toSeminormedCommRing Complex
                                (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                        (@NonUnitalCStarAlgebra.toNormedSpace Complex
                          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex))))))
                  (@UpperTheory.Reformulated.B.Re3.rreg n ε k)
                  (@DFunLike.coe
                    (@LinearMap Complex Complex Complex.instSemiring Complex.instSemiring
                      (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))
                      (@UpperTheory.Reformulated.B.Re3.L2 n ε) (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                      (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                      (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                        (@CStarAlgebra.toNormedRing Complex
                          (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                        (@Semiring.toModule Complex
                          (@Ring.toSemiring Complex
                            (@NormedRing.toRing Complex
                              (@CStarAlgebra.toNormedRing Complex
                                (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                        (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                              (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                                (@NormedCommRing.toSeminormedCommRing Complex
                                  (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                          (@NonUnitalCStarAlgebra.toNormedSpace Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                      (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                        (@CStarAlgebra.toNormedRing Complex
                          (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                        (@Semiring.toModule Complex
                          (@Ring.toSemiring Complex
                            (@NormedRing.toRing Complex
                              (@CStarAlgebra.toNormedRing Complex
                                (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                        (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                              (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                                (@NormedCommRing.toSeminormedCommRing Complex
                                  (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                          (@NonUnitalCStarAlgebra.toNormedSpace Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex))))))
                    (@UpperTheory.Reformulated.B.Re3.L2 n ε) (fun (x : @UpperTheory.Reformulated.B.Re3.L2 n ε) ↦ @UpperTheory.Reformulated.B.Re3.L2 n ε)
                    (@LinearMap.instFunLike Complex Complex (@UpperTheory.Reformulated.B.Re3.L2 n ε) (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      Complex.instSemiring Complex.instSemiring
                      (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                      (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                      (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                        (@CStarAlgebra.toNormedRing Complex
                          (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                        (@Semiring.toModule Complex
                          (@Ring.toSemiring Complex
                            (@NormedRing.toRing Complex
                              (@CStarAlgebra.toNormedRing Complex
                                (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                        (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                              (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                                (@NormedCommRing.toSeminormedCommRing Complex
                                  (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                          (@NonUnitalCStarAlgebra.toNormedSpace Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                      (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                        (@CStarAlgebra.toNormedRing Complex
                          (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                        (@Semiring.toModule Complex
                          (@Ring.toSemiring Complex
                            (@NormedRing.toRing Complex
                              (@CStarAlgebra.toNormedRing Complex
                                (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                        (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                              (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                                (@NormedCommRing.toSeminormedCommRing Complex
                                  (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                          (@NonUnitalCStarAlgebra.toNormedSpace Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                      (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)))
                    A x))) →
        ∀
          {S :
            @Submodule Complex (@UpperTheory.Reformulated.B.Re3.L2 n ε) Complex.instSemiring
              (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                  (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                  (@OfNat.ofNat ENNReal (nat_lit 2)
                    (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                      (@AddMonoidWithOne.toNatCast ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                      UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                  (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
              (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                (@OfNat.ofNat ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                    UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                (@Semiring.toModule Complex
                  (@Ring.toSemiring Complex
                    (@NormedRing.toRing Complex
                      (@CStarAlgebra.toNormedRing Complex
                        (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                        (@NormedCommRing.toSeminormedCommRing Complex
                          (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                  (@NonUnitalCStarAlgebra.toNormedSpace Complex
                    (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                      (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))},
          (∀ (w : @UpperTheory.Reformulated.B.Re3.L2 n ε),
              @Membership.mem (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                  (@Submodule Complex (@UpperTheory.Reformulated.B.Re3.L2 n ε) Complex.instSemiring
                    (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                    (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                      (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                      (@OfNat.ofNat ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                          UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                      (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                      (@CStarAlgebra.toNormedRing Complex
                        (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                      (@Semiring.toModule Complex
                        (@Ring.toSemiring Complex
                          (@NormedRing.toRing Complex
                            (@CStarAlgebra.toNormedRing Complex
                              (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                      (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                            (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                              (@NormedCommRing.toSeminormedCommRing Complex
                                (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                        (@NonUnitalCStarAlgebra.toNormedSpace Complex
                          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex))))))
                  (@SetLike.instMembership
                    (@Submodule Complex (@UpperTheory.Reformulated.B.Re3.L2 n ε) Complex.instSemiring
                      (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                      (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                        (@CStarAlgebra.toNormedRing Complex
                          (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                        (@Semiring.toModule Complex
                          (@Ring.toSemiring Complex
                            (@NormedRing.toRing Complex
                              (@CStarAlgebra.toNormedRing Complex
                                (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                        (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                              (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                                (@NormedCommRing.toSeminormedCommRing Complex
                                  (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                          (@NonUnitalCStarAlgebra.toNormedSpace Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex))))))
                    (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                    (@Submodule.setLike Complex (@UpperTheory.Reformulated.B.Re3.L2 n ε) Complex.instSemiring
                      (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                      (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                        (@CStarAlgebra.toNormedRing Complex
                          (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                        (@Semiring.toModule Complex
                          (@Ring.toSemiring Complex
                            (@NormedRing.toRing Complex
                              (@CStarAlgebra.toNormedRing Complex
                                (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                        (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                              (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                                (@NormedCommRing.toSeminormedCommRing Complex
                                  (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                          (@NonUnitalCStarAlgebra.toNormedSpace Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))))
                  S w →
                @Eq (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                    (@DFunLike.coe
                      (@LinearMap Complex Complex Complex.instSemiring Complex.instSemiring
                        (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))
                        (@UpperTheory.Reformulated.B.Re3.L2 n ε) (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                          (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                            (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                            (@OfNat.ofNat ENNReal (nat_lit 2)
                              (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                (@AddMonoidWithOne.toNatCast ENNReal
                                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                            (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                        (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                          (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                            (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                            (@OfNat.ofNat ENNReal (nat_lit 2)
                              (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                (@AddMonoidWithOne.toNatCast ENNReal
                                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                            (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                        (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                          (@CStarAlgebra.toNormedRing Complex
                            (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                          (@Semiring.toModule Complex
                            (@Ring.toSemiring Complex
                              (@NormedRing.toRing Complex
                                (@CStarAlgebra.toNormedRing Complex
                                  (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                          (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                            (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                              (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                                (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                                  (@NormedCommRing.toSeminormedCommRing Complex
                                    (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                            (@NonUnitalCStarAlgebra.toNormedSpace Complex
                              (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                                (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                        (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                          (@CStarAlgebra.toNormedRing Complex
                            (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                          (@Semiring.toModule Complex
                            (@Ring.toSemiring Complex
                              (@NormedRing.toRing Complex
                                (@CStarAlgebra.toNormedRing Complex
                                  (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                          (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                            (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                              (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                                (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                                  (@NormedCommRing.toSeminormedCommRing Complex
                                    (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                            (@NonUnitalCStarAlgebra.toNormedSpace Complex
                              (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                                (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex))))))
                      (@UpperTheory.Reformulated.B.Re3.L2 n ε) (fun (x : @UpperTheory.Reformulated.B.Re3.L2 n ε) ↦ @UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@LinearMap.instFunLike Complex Complex (@UpperTheory.Reformulated.B.Re3.L2 n ε) (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        Complex.instSemiring Complex.instSemiring
                        (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                          (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                            (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                            (@OfNat.ofNat ENNReal (nat_lit 2)
                              (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                (@AddMonoidWithOne.toNatCast ENNReal
                                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                            (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                        (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                          (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                            (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                            (@OfNat.ofNat ENNReal (nat_lit 2)
                              (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                (@AddMonoidWithOne.toNatCast ENNReal
                                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                            (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                        (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                          (@CStarAlgebra.toNormedRing Complex
                            (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                          (@Semiring.toModule Complex
                            (@Ring.toSemiring Complex
                              (@NormedRing.toRing Complex
                                (@CStarAlgebra.toNormedRing Complex
                                  (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                          (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                            (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                              (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                                (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                                  (@NormedCommRing.toSeminormedCommRing Complex
                                    (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                            (@NonUnitalCStarAlgebra.toNormedSpace Complex
                              (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                                (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                        (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                          (@CStarAlgebra.toNormedRing Complex
                            (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                          (@Semiring.toModule Complex
                            (@Ring.toSemiring Complex
                              (@NormedRing.toRing Complex
                                (@CStarAlgebra.toNormedRing Complex
                                  (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                          (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                            (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                              (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                                (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                                  (@NormedCommRing.toSeminormedCommRing Complex
                                    (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                            (@NonUnitalCStarAlgebra.toNormedSpace Complex
                              (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                                (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                        (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)))
                      A w)
                    (@OfNat.ofNat (@UpperTheory.Reformulated.B.Re3.L2 n ε) (nat_lit 0)
                      (@Zero.toOfNat0 (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@AddSubgroup.zero
                          (@MeasureTheory.AEEqFun (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                            (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                            (@UniformSpace.toTopologicalSpace Complex
                              (@PseudoMetricSpace.toUniformSpace Complex
                                (@SeminormedAddCommGroup.toPseudoMetricSpace Complex
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup))))
                            (@UpperTheory.Reformulated.B.Re3.muG n ε))
                          (@MeasureTheory.AEEqFun.instAddGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                            (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε) (@UpperTheory.Reformulated.B.Re3.muG n ε)
                            (@UniformSpace.toTopologicalSpace Complex
                              (@PseudoMetricSpace.toUniformSpace Complex
                                (@SeminormedAddCommGroup.toPseudoMetricSpace Complex
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup))))
                            (@AddCommGroup.toAddGroup Complex
                              (@NormedAddCommGroup.toAddCommGroup Complex Complex.instNormedAddCommGroup))
                            (@SeminormedAddCommGroup.toIsTopologicalAddGroup Complex
                              (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)))
                          (@MeasureTheory.Lp (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                            (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε) Complex.instNormedAddCommGroup
                            (@OfNat.ofNat ENNReal (nat_lit 2)
                              (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                (@AddMonoidWithOne.toNatCast ENNReal
                                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                            (@UpperTheory.Reformulated.B.Re3.muG n ε))))) →
                  @Eq (@UpperTheory.Reformulated.B.Re3.L2 n ε) w
                    (@OfNat.ofNat (@UpperTheory.Reformulated.B.Re3.L2 n ε) (nat_lit 0)
                      (@Zero.toOfNat0 (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@AddSubgroup.zero
                          (@MeasureTheory.AEEqFun (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                            (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                            (@UniformSpace.toTopologicalSpace Complex
                              (@PseudoMetricSpace.toUniformSpace Complex
                                (@SeminormedAddCommGroup.toPseudoMetricSpace Complex
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup))))
                            (@UpperTheory.Reformulated.B.Re3.muG n ε))
                          (@MeasureTheory.AEEqFun.instAddGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                            (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε) (@UpperTheory.Reformulated.B.Re3.muG n ε)
                            (@UniformSpace.toTopologicalSpace Complex
                              (@PseudoMetricSpace.toUniformSpace Complex
                                (@SeminormedAddCommGroup.toPseudoMetricSpace Complex
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup))))
                            (@AddCommGroup.toAddGroup Complex
                              (@NormedAddCommGroup.toAddCommGroup Complex Complex.instNormedAddCommGroup))
                            (@SeminormedAddCommGroup.toIsTopologicalAddGroup Complex
                              (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)))
                          (@MeasureTheory.Lp (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                            (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε) Complex.instNormedAddCommGroup
                            (@OfNat.ofNat ENNReal (nat_lit 2)
                              (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                (@AddMonoidWithOne.toNatCast ENNReal
                                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                            (@UpperTheory.Reformulated.B.Re3.muG n ε)))))) →
            @UpperTheory.Reformulated.B.Re3.IsKTypeOf n (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                  (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                  (@OfNat.ofNat ENNReal (nat_lit 2)
                    (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                      (@AddMonoidWithOne.toNatCast ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                      UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                  (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)
                (@MeasureTheory.L2.innerProductSpace (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex Complex.instRCLike
                  (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε) (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                  (@RCLike.innerProductSpace Complex Complex.instRCLike))
                ε (@UpperTheory.Reformulated.B.Re3.rreg n ε) Λ S →
              @UpperTheory.Reformulated.B.Re3.IsKTypeOf n (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                  (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                  (@OfNat.ofNat ENNReal (nat_lit 2)
                    (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                      (@AddMonoidWithOne.toNatCast ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                      UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                  (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)
                (@MeasureTheory.L2.innerProductSpace (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex Complex.instRCLike
                  (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε) (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                  (@RCLike.innerProductSpace Complex Complex.instRCLike))
                ε (@UpperTheory.Reformulated.B.Re3.rreg n ε) Λ
                (@Submodule.map Complex Complex (@UpperTheory.Reformulated.B.Re3.L2 n ε) (@UpperTheory.Reformulated.B.Re3.L2 n ε) Complex.instSemiring
                  Complex.instSemiring
                  (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                    (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                      (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                      (@OfNat.ofNat ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                          UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                      (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup))
                  (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                    (@NormedAddCommGroup.toAddCommGroup (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))
                  (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex
                    (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                    (@OfNat.ofNat ENNReal (nat_lit 2)
                      (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                        (@AddMonoidWithOne.toNatCast ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                        UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                    (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup
                    (@CStarAlgebra.toNormedRing Complex
                      (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                    (@Semiring.toModule Complex
                      (@Ring.toSemiring Complex
                        (@NormedRing.toRing Complex
                          (@CStarAlgebra.toNormedRing Complex
                            (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                    (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                      (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                          (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                            (@NormedCommRing.toSeminormedCommRing Complex
                              (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                      (@NonUnitalCStarAlgebra.toNormedSpace Complex
                        (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                          (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                  (@NormedSpace.toModule Complex (@UpperTheory.Reformulated.B.Re3.L2 n ε) Complex.instNormedField
                    (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                      (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal))
                    (@InnerProductSpace.toNormedSpace Complex (@UpperTheory.Reformulated.B.Re3.L2 n ε) Complex.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re3.L2 n ε)
                        (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex
                          (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
                          (@UpperTheory.Reformulated.B.Re3.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal))
                      (@MeasureTheory.L2.innerProductSpace (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex Complex Complex.instRCLike
                        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε) (@UpperTheory.Reformulated.B.Re3.muG n ε)
                        Complex.instNormedAddCommGroup (@RCLike.innerProductSpace Complex Complex.instRCLike))))
                  (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))
                  (@RingHomSurjective.ids Complex Complex.instSemiring) A S) := by
  intro n ε Λ A hA S hinj hS
  exact UpperTheory.Reformulated.B.Re3.transfer_gen (UpperTheory.Reformulated.B.Re3.rreg ε) A hA hinj hS
end UpperTheory.Reformulated.B.Re3
