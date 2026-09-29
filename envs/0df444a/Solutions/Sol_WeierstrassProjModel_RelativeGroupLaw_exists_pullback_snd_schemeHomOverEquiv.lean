-- Prove2me | solution 1 for WeierstrassProjModel.RelativeGroupLaw.exists_pullback_snd_schemeHomOverEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/2456d834-f454-533e-8a1c-0c7482af75c4

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_RelativeGroupLaw_exists_pullback_snd_schemeHomOverEquiv

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

universe u

set_option maxHeartbeats 8000000 in
theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (K : Type u) [CommRing K] [Algebra R K] :
    ∃ σ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R K))) f ≃
          SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
            (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      ∀ (G : WeierstrassProjModel.RelativeGroupLaw R f),
        ∃ G' : WeierstrassProjModel.RelativeGroupLaw K
            (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
          (∀ P Q, σ (G.mul (Spec.map (CommRingCat.ofHom (algebraMap R K))) P Q)
            = G'.mul (𝟙 _) (σ P) (σ Q))
          ∧ σ (G.one (Spec.map (CommRingCat.ofHom (algebraMap R K)))) = G'.one (𝟙 _) := by
  set tK := Spec.map (CommRingCat.ofHom (algebraMap R K)) with htK
  set pbs := pullback.snd f tK with hpbs

  let τ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)),
      SchemeHomOver t pbs ≃ SchemeHomOver (t ≫ tK) f := fun {T} t =>
    { toFun := fun Q => ⟨Q.1 ≫ pullback.fst f tK, by
        rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩
      invFun := fun P => ⟨pullback.lift P.1 t P.2, pullback.lift_snd _ _ _⟩
      left_inv := fun Q => Subtype.ext
        (pullback.hom_ext (pullback.lift_fst _ _ _)
          ((pullback.lift_snd _ _ _).trans Q.2.symm))
      right_inv := fun P => Subtype.ext (pullback.lift_fst _ _ _) }

  have τ_nat : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (t' : T' ⟶ Spec (CommRingCat.of K)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
      (Q : SchemeHomOver t pbs),
      τ t' (schemeHomOverComp ψ hψ Q)
        = schemeHomOverComp ψ (by rw [← Category.assoc, hψ]) (τ t Q) := by
    intro T T' t t' ψ hψ Q
    exact Subtype.ext (by simp only [τ, Equiv.coe_fn_mk, schemeHomOverComp_coe, Category.assoc])

  refine ⟨{ toFun := fun P => ⟨pullback.lift P.1 (𝟙 _)
              (P.2.trans (Category.id_comp tK).symm), pullback.lift_snd _ _ _⟩
            invFun := fun Q => ⟨Q.1 ≫ pullback.fst f tK, by
              rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2,
                Category.id_comp]⟩
            left_inv := fun P => Subtype.ext (pullback.lift_fst _ _ _)
            right_inv := fun Q => Subtype.ext
              (pullback.hom_ext (pullback.lift_fst _ _ _)
                ((pullback.lift_snd _ _ _).trans Q.2.symm)) }, ?_⟩
  intro G

  refine ⟨{ mul := fun {T} t P Q => (τ t).symm (G.mul (t ≫ tK) (τ t P) (τ t Q))
            one := fun {T} t => (τ t).symm (G.one (t ≫ tK))
            inv := fun {T} t P => (τ t).symm (G.inv (t ≫ tK) (τ t P))
            mul_assoc := fun {T} t x y z => by
              simp only [Equiv.apply_symm_apply]
              exact congrArg (τ t).symm (G.mul_assoc _ _ _ _)
            one_mul := fun {T} t x => by
              simp only [Equiv.apply_symm_apply]
              rw [G.one_mul]; exact (τ t).symm_apply_apply x
            mul_one := fun {T} t x => by
              simp only [Equiv.apply_symm_apply]
              rw [G.mul_one]; exact (τ t).symm_apply_apply x
            inv_mul_cancel := fun {T} t x => by
              simp only [Equiv.apply_symm_apply]
              rw [G.inv_mul_cancel]
            mul_natural := fun {T T'} t t' ψ hψ x y => by
              apply (τ t').injective
              simp only [Equiv.apply_symm_apply]
              rw [τ_nat t t' ψ hψ, τ_nat t t' ψ hψ, τ_nat t t' ψ hψ,
                ← G.mul_natural (t ≫ tK) (t' ≫ tK) ψ (by rw [← Category.assoc, hψ])
                  (τ t x) (τ t y)]
              simp only [Equiv.apply_symm_apply] }, ?_, ?_⟩
  ·
    intro P Q
    apply (τ (𝟙 _)).injective
    simp only [Equiv.apply_symm_apply, Equiv.coe_fn_mk]

    have hτσ : ∀ (X : SchemeHomOver tK f),
        τ (𝟙 _) ⟨pullback.lift X.1 (𝟙 _) (X.2.trans (Category.id_comp tK).symm),
            pullback.lift_snd _ _ _⟩
          = schemeHomOverComp (𝟙 _) rfl X := fun X =>
      Subtype.ext (by
        simp only [τ, Equiv.coe_fn_mk, schemeHomOverComp_coe, Category.id_comp]
        exact pullback.lift_fst _ _ _)
    rw [hτσ (G.mul tK P Q), hτσ P, hτσ Q]
    exact G.mul_natural tK (𝟙 _ ≫ tK) (𝟙 _) rfl P Q
  ·
    apply (τ (𝟙 _)).injective
    simp only [Equiv.apply_symm_apply, Equiv.coe_fn_mk]
    have hτσ₁ : τ (𝟙 _) ⟨pullback.lift (G.one tK).1 (𝟙 _)
            ((G.one tK).2.trans (Category.id_comp tK).symm), pullback.lift_snd _ _ _⟩
          = schemeHomOverComp (𝟙 _) rfl (G.one tK) :=
      Subtype.ext (by
        simp only [τ, Equiv.coe_fn_mk, schemeHomOverComp_coe, Category.id_comp]
        exact pullback.lift_fst _ _ _)
    rw [hτσ₁]
    exact G.one_natural tK (𝟙 _ ≫ tK) (𝟙 _) rfl

end S_WeierstrassProjModel_RelativeGroupLaw_exists_pullback_snd_schemeHomOverEquiv
end P2MW
export P2MW.S_WeierstrassProjModel_RelativeGroupLaw_exists_pullback_snd_schemeHomOverEquiv (solution)
