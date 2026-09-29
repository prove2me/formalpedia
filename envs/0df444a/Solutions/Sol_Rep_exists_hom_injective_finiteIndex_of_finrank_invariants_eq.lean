-- Prove2me | solution 1 for Rep.exists_hom_injective_finiteIndex_of_finrank_invariants_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/93ce3589-b7ad-50dc-9d3b-e43cc2118681

import Mathlib
import Theorems.Thm_Rep_finrank_invariants_comp_eq_of_rat
import Theorems.Thm_Representation_exists_linearEquiv_of_finrank_invariants_eq
import Theorems.Thm_Rep_exists_hom_injective_finiteIndex_of_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_exists_hom_injective_finiteIndex_of_finrank_invariants_eq

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module"
open scoped Classical

namespace P2mS25LatticeMarks

open TensorProduct

variable {G : Type} [Group G]

noncomputable def ρc (L : Rep ℤ G) (g : G) : L →ₗ[ℤ] L := ((L.ρ g : L →ₗ[ℤ] L) : L →+ L).toIntLinearMap

@[scoped simp] lemma ρc_apply (L : Rep ℤ G) (g : G) (x : L) : ρc L g x = L.ρ g x := rfl

noncomputable def τQ (L : Rep ℤ G) : Representation ℚ G (ℚ ⊗[ℤ] L) where
  toFun g := (ρc L g).baseChange ℚ
  map_one' := by
    have : ρc L 1 = LinearMap.id := by ext x; simp [ρc_apply]
    rw [this, LinearMap.baseChange_id]; rfl
  map_mul' g h := by
    have : ρc L (g * h) = ρc L g ∘ₗ ρc L h := by ext x; simp [ρc_apply]
    rw [this, LinearMap.baseChange_comp]; rfl

lemma τQ_apply_tmul (L : Rep ℤ G) (g : G) (a : ℚ) (x : L) : τQ L g (a ⊗ₜ x) = a ⊗ₜ L.ρ g x := rfl

noncomputable def ι (L : Rep ℤ G) : L →+ ℚ ⊗[ℤ] L := (TensorProduct.mk ℤ ℚ L 1).toAddMonoidHom

@[scoped simp] lemma ι_apply (L : Rep ℤ G) (x : L) : ι L x = (1 : ℚ) ⊗ₜ x := rfl

lemma ι_injective (L : Rep ℤ G) [Module.Free ℤ L] : Function.Injective (ι L) := by
  have hinj : Function.Injective ((Algebra.linearMap ℤ ℚ).rTensor L) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (fun a b hab => (algebraMap ℤ ℚ).injective_int hab)
  intro x y hxy
  have : (Algebra.linearMap ℤ ℚ).rTensor L ((TensorProduct.lid ℤ L).symm x) =
      (Algebra.linearMap ℤ ℚ).rTensor L ((TensorProduct.lid ℤ L).symm y) := by
    simpa [LinearMap.rTensor_tmul] using hxy
  exact (TensorProduct.lid ℤ L).symm.injective (hinj this)

lemma ι_equivariant (L : Rep ℤ G) (g : G) (x : L) : ι L (L.ρ g x) = τQ L g (ι L x) := rfl

lemma ι_full (L : Rep ℤ G) : Submodule.span ℚ (Set.range (ι L)) = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a x =>
    have : a ⊗ₜ[ℤ] x = a • ((1 : ℚ) ⊗ₜ[ℤ] x) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ a (Submodule.subset_span ⟨x, rfl⟩)
  | add z w hz hw => exact Submodule.add_mem _ hz hw

end P2mS25LatticeMarks
p2m_reactivate "P2MW.S_Rep_exists_hom_injective_finiteIndex_of_finrank_invariants_eq.P2mS25LatticeMarks"

open scoped TensorProduct in
open P2mS25LatticeMarks in
theorem solution
    {G : Type} [Group G] [Finite G] [IsCyclic G]
    (L L' : Rep ℤ G) [Module.Finite ℤ L] [Module.Free ℤ L] [Module.Finite ℤ L'] [Module.Free ℤ L']
    (h : ∀ H : Subgroup G, Module.finrank ℤ (groupCohomology (Rep.res H.subtype L) 0) =
      Module.finrank ℤ (groupCohomology (Rep.res H.subtype L') 0)) :
    ∃ f : L ⟶ L', Function.Injective f.hom ∧ (f.hom : L →+ L').range.FiniteIndex := by
  haveI : Fintype G := Fintype.ofFinite G

  have hm : ∀ H : Subgroup G,
      Module.finrank ℚ (Representation.invariants ((τQ L).comp H.subtype)) =
        Module.finrank ℚ (Representation.invariants ((τQ L').comp H.subtype)) := fun H => by
    rw [Rep.finrank_invariants_comp_eq_of_rat (τQ L) (ι L) (ι_injective L) (ι_equivariant L) (ι_full L) H,
      Rep.finrank_invariants_comp_eq_of_rat (τQ L') (ι L') (ι_injective L') (ι_equivariant L') (ι_full L') H, h H]

  obtain ⟨e, he⟩ := Representation.exists_linearEquiv_of_finrank_invariants_eq (τQ L) (τQ L') hm

  exact Rep.exists_hom_injective_finiteIndex_of_rat (τQ L') (e.toLinearMap.toAddMonoidHom.comp (ι L))
    (e.injective.comp (ι_injective L))
    (fun g x => by
      show e (ι L (L.ρ g x)) = τQ L' g (e (ι L x))
      rw [ι_equivariant, he])
    (ι L') (ι_injective L') (ι_equivariant L')
    (by
      rw [AddMonoidHom.coe_comp, Set.range_comp]
      show Submodule.span ℚ (e.toLinearMap '' Set.range (ι L)) = ⊤
      rw [Submodule.span_image, ι_full, Submodule.map_top]
      exact LinearMap.range_eq_top.2 e.surjective)
    (ι_full L')

end S_Rep_exists_hom_injective_finiteIndex_of_finrank_invariants_eq
end P2MW
export P2MW.S_Rep_exists_hom_injective_finiteIndex_of_finrank_invariants_eq (solution)
