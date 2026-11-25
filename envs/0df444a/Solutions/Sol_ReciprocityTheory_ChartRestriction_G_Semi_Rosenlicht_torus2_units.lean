-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.torus2_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:47:22.425504+00:00
-- url     : https://prove2.me/submissions/45c35e1c-5272-4c3d-9a87-b10381d22256

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusIsCommMonObjSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsaRos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_isUnit_eq_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_torusGamma_chi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_torusGamma_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_torus2Gamma_bijective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_torus2Gamma_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_torus2Gamma_snd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj MonObj TensorProduct
open AddMonoidAlgebra
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
variable (K : Type u) [Field K] (X : Type u) [AddCommGroup X]
namespace ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
theorem _root_.solution [TwoUniqueSums X]
    {w : Γ((splitTorus (Spec (.of K)) X ⊗ splitTorus (Spec (.of K)) X).left, ⊤)} (hw : IsUnit w) :
    ∃ (c : Γ(Spec (.of K), ⊤)) (a b : X), IsUnit c ∧
      w = (fst (splitTorus (Spec (.of K)) X) (splitTorus (Spec (.of K)) X)).left.appTop.hom
          ((splitTorus (Spec (.of K)) X).hom.appTop.hom c * chi X a) *
        (snd (splitTorus (Spec (.of K)) X) (splitTorus (Spec (.of K)) X)).left.appTop.hom
          (chi X b) := by
  classical
  let L : (AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X) →ₐ[K] AddMonoidAlgebra K (X × X) :=
    Algebra.TensorProduct.lift (AddMonoidAlgebra.mapDomainAlgHom K K (AddMonoidHom.inl X X))
      (AddMonoidAlgebra.mapDomainAlgHom K K (AddMonoidHom.inr X X)) (fun _ _ => Commute.all _ _)
  let Mh : Multiplicative (X × X) →* (AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X) :=
    { toFun := fun z => single (Multiplicative.toAdd z).1 (1 : K) ⊗ₜ single (Multiplicative.toAdd z).2 (1 : K)
      map_one' := by
        simp only [toAdd_one, Prod.fst_zero, Prod.snd_zero]
        rw [← AddMonoidAlgebra.one_def, Algebra.TensorProduct.one_def]
      map_mul' := fun z z' => by
        simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, Algebra.TensorProduct.tmul_mul_tmul,
          AddMonoidAlgebra.single_mul_single, mul_one] }
  let M := AddMonoidAlgebra.lift K (AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X) (X × X) Mh
  have hML : M.comp L = AlgHom.id K _ := by
    ext x <;> simp [L, M, Mh, AddMonoidAlgebra.one_def]
  have hu : IsUnit ((torus2Gamma K X).hom w) := hw.map _
  obtain ⟨z, c, hc, hz⟩ := isUnit_eq_single (hu.map L)
  have htw : (torus2Gamma K X).hom w = c • (single z.1 (1 : K) ⊗ₜ single z.2 (1 : K)) := by
    have h1 : M (L ((torus2Gamma K X).hom w)) = (torus2Gamma K X).hom w := by
      rw [← AlgHom.comp_apply, hML]
      rfl
    rw [← h1, hz, AddMonoidAlgebra.lift_single]
    rfl
  refine ⟨(Scheme.ΓSpecIso (.of K)).inv.hom c, z.1, z.2, hc.map _, ?_⟩
  apply (torus2Gamma_bijective K X).1
  rw [htw, map_mul, torus2Gamma_fst, torus2Gamma_snd, map_mul, torusGamma_const, torusGamma_chi, torusGamma_chi,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, AddMonoidAlgebra.single_mul_single, zero_add, mul_one,
    TensorProduct.smul_tmul', AddMonoidAlgebra.smul_single', mul_one]
  congr 2
  simp
end ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
