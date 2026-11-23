-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Yzd4.lcsc_HA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:39.927211+00:00
-- url     : https://prove2.me/submissions/66413915-a81e-48fd-b468-36d9abc11ed5

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ConjInvariantCharacterMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
attribute [local instance] UpperTheory.Reformulated.B.Yzd4.instTopologicalSpaceHA
private theorem closed_UJ {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A) (hσ : Continuous σ)
    (J : Matrix n n A) :
    IsClosed ((UpperTheory.Reformulated.B.Yzd4.UJ σ J : Subgroup (Matrix.GeneralLinearGroup n A)) :
      Set (Matrix.GeneralLinearGroup n A)) := by
  have hv : Continuous (fun g : Matrix.GeneralLinearGroup n A => (g : Matrix n n A)) :=
    Units.continuous_val
  have hc : Continuous (fun g : Matrix.GeneralLinearGroup n A =>
      UpperTheory.Reformulated.B.Yzd4.cT σ (g : Matrix n n A) * J * (g : Matrix n n A)) := by
    simp only [UpperTheory.Reformulated.B.Yzd4.cT]
    exact ((hv.matrix_map hσ).matrix_transpose.matrix_mul continuous_const).matrix_mul hv
  exact isClosed_eq hc continuous_const
private theorem lcsc_GL {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A] {n : Type} [Fintype n]
    [DecidableEq n] :
    LocallyCompactSpace (Matrix.GeneralLinearGroup n A) ∧
      SecondCountableTopology (Matrix.GeneralLinearGroup n A) ∧
      T2Space (Matrix.GeneralLinearGroup n A) := by
  haveI : LocallyCompactSpace (Matrix n n A) := inferInstanceAs (LocallyCompactSpace (n → n → A))
  haveI : SecondCountableTopology (Matrix n n A) :=
    inferInstanceAs (SecondCountableTopology (n → n → A))
  haveI : SecondCountableTopology (Matrix n n A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  have he : Topology.IsClosedEmbedding (Units.embedProduct (Matrix n n A)) :=
    Units.isClosedEmbedding_embedProduct
  exact ⟨he.locallyCompactSpace, he.isEmbedding.secondCountableTopology, he.isEmbedding.t2Space⟩
private theorem lcsc_sub {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G)
    (hH : IsClosed (H : Set G)) [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] :
    LocallyCompactSpace H ∧ SecondCountableTopology H ∧ T2Space H :=
  ⟨hH.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    Topology.IsEmbedding.subtypeVal.secondCountableTopology, inferInstance⟩
private theorem props_of_free {R D : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [Ring D] [Algebra R D]
    {ι : Type} [Fintype ι] (B : Module.Basis ι R D) [Module.Finite R D] [TopologicalSpace D]
    [IsModuleTopology R D] :
    IsTopologicalRing D ∧ LocallyCompactSpace D ∧ SecondCountableTopology D ∧ T2Space D := by
  have hr := IsModuleTopology.isTopologicalRing R D
  haveI := IsModuleTopology.toContinuousAdd R D
  let e := B.equivFun
  have c1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have c2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : D ≃ₜ (ι → R) := { toEquiv := e.toEquiv, continuous_toFun := c1, continuous_invFun := c2 }
  exact ⟨hr, h.isClosedEmbedding.locallyCompactSpace, h.isEmbedding.secondCountableTopology,
    h.isEmbedding.t2Space⟩
private theorem tens_props (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    [TopologicalSpace (TensorProduct F R E)] [IsModuleTopology R (TensorProduct F R E)] :
    IsTopologicalRing (TensorProduct F R E) ∧ LocallyCompactSpace (TensorProduct F R E) ∧
      SecondCountableTopology (TensorProduct F R E) ∧ T2Space (TensorProduct F R E) :=
  props_of_free (Algebra.TensorProduct.basis R (Module.finBasis F E))
private theorem sigR_continuous {F E : Type} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [TopologicalSpace (TensorProduct F R E)]
    [IsModuleTopology R (TensorProduct F R E)] (σ : E →ₐ[F] E) :
    Continuous (UpperTheory.Reformulated.B.Yzd4.sigR R σ) := by
  haveI := IsModuleTopology.toContinuousAdd R (TensorProduct F R E)
  have h : (⇑(UpperTheory.Reformulated.B.Yzd4.sigR R σ) : TensorProduct F R E → TensorProduct F R E) =
      ⇑(LinearMap.baseChange R σ.toLinearMap) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [UpperTheory.Reformulated.B.Yzd4.sigR]
    | add a b ha hb => simp [map_add, ha, hb]
  rw [h]
  exact IsModuleTopology.continuous_of_linearMap _
end

set_option autoImplicit false
attribute [local instance] UpperTheory.Reformulated.B.Yzd4.instTopologicalSpaceHA
namespace UpperTheory.Reformulated.B.Yzd4
theorem _root_.solution :
    ∀ {F E : Type} [inst : Field F] [inst_1 : Field E]
      [inst_2 :
        @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))]
      [@FiniteDimensional F E (@Field.toDivisionRing F inst)
          (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_1)))
          (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))) inst_2)]
      (R : Type) [inst_4 : CommRing R]
      [inst_5 :
        @Algebra F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_4))]
      [inst_6 : TopologicalSpace R]
      [@IsTopologicalRing R inst_6
          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing R
            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing R (@CommRing.toNonUnitalCommRing R inst_4)))]
      [@LocallyCompactSpace R inst_6] [@SecondCountableTopology R inst_6] [@T2Space R inst_6]
      (σ :
        @AlgHom F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))) inst_2 inst_2)
      (M : Nat) (J : Matrix (Fin M) (Fin M) E),
      And
        (@LocallyCompactSpace (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_4 inst_5 σ M J)
          (@UpperTheory.Reformulated.B.Yzd4.instTopologicalSpaceHA F E inst inst_1 inst_2 R inst_4 inst_5 σ M J inst_6))
        (And
          (@SecondCountableTopology (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_4 inst_5 σ M J)
            (@UpperTheory.Reformulated.B.Yzd4.instTopologicalSpaceHA F E inst inst_1 inst_2 R inst_4 inst_5 σ M J inst_6))
          (@T2Space (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_4 inst_5 σ M J)
            (@UpperTheory.Reformulated.B.Yzd4.instTopologicalSpaceHA F E inst inst_1 inst_2 R inst_4 inst_5 σ M J inst_6))) := by
  intro F E _ _ _ _ R _ _ _ _ _ _ _ σ M J
  letI τ : TopologicalSpace (TensorProduct F R E) := UpperTheory.Reformulated.B.Yzd4.topTens R
  haveI hm : IsModuleTopology R (TensorProduct F R E) := ⟨rfl⟩
  obtain ⟨h1, h2, h3, h4⟩ := tens_props F E R
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  obtain ⟨g1, g2, g3⟩ := lcsc_GL (A := TensorProduct F R E) (n := Fin M)
  haveI := g1
  haveI := g2
  haveI := g3
  have hc := closed_UJ (UpperTheory.Reformulated.B.Yzd4.sigR R σ) (sigR_continuous R σ) (UpperTheory.Reformulated.B.Yzd4.JR R J)
  exact lcsc_sub _ hc
end UpperTheory.Reformulated.B.Yzd4
