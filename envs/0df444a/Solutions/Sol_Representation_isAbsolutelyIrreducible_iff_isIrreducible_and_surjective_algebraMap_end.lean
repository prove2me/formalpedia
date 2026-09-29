-- Prove2me | solution 1 for Representation.isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/0b749ebb-1cb4-5753-8fdb-df5988c082ca

import Mathlib
import Definitions.Def_Deformations_MatrixRepresentation
import Definitions.Def_Representation_AbsolutelyIrreducible
import Theorems.Thm_Representation_span_range_eq_top_of_isAbsolutelyIrreducible_matrix
import Theorems.Thm_Matrix_exists_eq_smul_one_of_commute_of_span_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end

open Module LinearMap

universe u

section
open LinearMap
namespace Representation
p2m_export "Representation" "free asModule asModuleEquiv irreducible_iff_isSimpleModule_asModule asAlgebraHom IsIrreducible asAlgebraHom_single IntertwiningMap.equivLinearMapAsModule asAlgebraHom_single_one Equiv.conj_apply_self subrepresentation TensorProduct.lid asAlgebraHom_of Equiv.mk IntertwiningMap asModuleEquiv_map_smul asModuleEquiv_symm_map_rho Equiv baseChange IsAbsolutelyIrreducible IsAbsolutelyIrreducible.absolutelyIrreducible span_range_eq_top_of_isAbsolutelyIrreducible_matrix IsIrreducible.of_equiv"
p2m_open "Representation"

variable {R V G ι : Type*} [CommRing R] [AddCommMonoid V] [Module R V] [Module.Free R V]
  [Module.Finite R V] [Group G] [DecidableEq ι] [Fintype ι]

variable (ρ : Representation R G V) (𝓑 : Module.Basis ι R V)

omit [Module.Free R V] [Module.Finite R V] in
@[scoped simp]
lemma comp_def (g h : G) : ρ g ∘ₗ ρ h = ρ g * ρ h := rfl

noncomputable def gl_map_of_basis
  : G →* Matrix.GeneralLinearGroup ι R where
    toFun g := {
      val := LinearMap.toMatrix 𝓑 𝓑 (ρ g)
      inv := LinearMap.toMatrix 𝓑 𝓑 (ρ g⁻¹)
      val_inv := by rw [← toMatrix_comp, comp_def, ← map_mul]; simp
      inv_val := by rw [← toMatrix_comp, comp_def, ← map_mul]; simp
    }
    map_one' := by aesop
    map_mul' := by rintro x y; simp [LinearMap.toMatrix_mul]; norm_cast

section
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
set_option backward.isDefEq.respectTransparency false in

theorem nontrivial_of_isIrreducible (ρ : Representation k G V) [ρ.IsIrreducible] :
    Nontrivial V := by
  haveI : IsSimpleModule (MonoidAlgebra k G) ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  have : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra k G) ρ.asModule
  exact ρ.asModuleEquiv.symm.toEquiv.nontrivial
end

end Representation
p2m_reactivate "P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.Representation"

end
p2m_reactivate "P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.Representation"

section AbstractConverse

variable {k : Type*} [Field k] {G : Type*} [Monoid G]
variable {V : Type*} [AddCommGroup V] [Module k V]

namespace Representation p2m_export "Representation" "free asModule asModuleEquiv irreducible_iff_isSimpleModule_asModule asAlgebraHom IsIrreducible asAlgebraHom_single IntertwiningMap.equivLinearMapAsModule asAlgebraHom_single_one Equiv.conj_apply_self subrepresentation TensorProduct.lid asAlgebraHom_of Equiv.mk IntertwiningMap asModuleEquiv_map_smul asModuleEquiv_symm_map_rho Equiv baseChange IsAbsolutelyIrreducible IsAbsolutelyIrreducible.absolutelyIrreducible span_range_eq_top_of_isAbsolutelyIrreducible_matrix IsIrreducible.of_equiv" end Representation
p2m_open_scoped "Representation" in

theorem Representation.isIrreducible_of_span_range_eq_top
    (ρ : Representation k G V) [Nontrivial V]
    (hspan : Submodule.span k (Set.range ⇑ρ) = ⊤) : ρ.IsIrreducible := by

  have hstable : ∀ (W : Subrepresentation ρ) (f : Module.End k V) ⦃v : V⦄,
      v ∈ W.toSubmodule → f v ∈ W.toSubmodule := by
    intro W f
    have hf : f ∈ Submodule.span k (Set.range ⇑ρ) := hspan ▸ Submodule.mem_top
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact W.apply_mem_toSubmodule g
    | zero =>
      intro v _
      simp
    | add x y _ _ hx hy =>
      intro v hv
      simpa using W.toSubmodule.add_mem (hx hv) (hy hv)
    | smul a x _ hx =>
      intro v hv
      simpa using W.toSubmodule.smul_mem a (hx hv)

  haveI : Nontrivial (Subrepresentation ρ) :=
    ⟨⊥, ⊤, fun h => bot_ne_top (α := Submodule k V) (congrArg Subrepresentation.toSubmodule h)⟩

  refine IsSimpleOrder.of_forall_eq_top fun W hW => ?_
  apply Subrepresentation.toSubmodule_injective
  show W.toSubmodule = ⊤
  have hWbot : W.toSubmodule ≠ ⊥ := fun h =>
    hW (Subrepresentation.toSubmodule_injective (h.trans rfl))
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWbot
  rw [Submodule.eq_top_iff']
  intro v

  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hw0
  have hfw : (LinearMap.smulRight φ v) w = v := by
    rw [LinearMap.smulRight_apply, hφ, one_smul]
  exact hfw ▸ hstable W (LinearMap.smulRight φ v) hwW

end AbstractConverse
p2m_reactivate "P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.Representation"

section SpanAscent

variable {n : Type} [Fintype n] [DecidableEq n]

namespace Matrix p2m_export "Matrix" "ext mulVec_eq_sum add map_apply smul_single zero IsIrreducible map_single map_smul' GeneralLinearGroup.map scalar transpose_apply comp toLin'_one mulVecLin_apply rank smul matrix_eq_sum_single single GeneralLinearGroup one_apply smul_apply toLinearEquiv toLin'_apply' comp_apply of sum_apply inv toLin'_toMatrix' map toLin' one mul_apply module nonempty exists_eq_smul_one_of_commute_of_span_eq_top" end Matrix
p2m_open_scoped "Matrix" in

theorem Matrix.span_image_map_eq_top_of_span_eq_top
    {k : Type*} [Field k] {K : Type*} [Field K] (f : k →+* K)
    {S : Set (Matrix n n k)} (hS : Submodule.span k S = ⊤) :
    Submodule.span K ((fun X : Matrix n n k => X.map f) '' S) = ⊤ := by

  have key : ∀ X ∈ Submodule.span k S,
      X.map f ∈ Submodule.span K ((fun X : Matrix n n k => X.map f) '' S) := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      have h0 : (0 : Matrix n n k).map f = 0 := by
        ext i j; simp
      rw [h0]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have hadd : (x + y).map f = x.map f + y.map f := by
        ext i j; simp
      rw [hadd]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have hsmul : (a • x).map f = f a • x.map f := by
        ext i j
        simp [Matrix.map_apply, smul_eq_mul]
      rw [hsmul]; exact Submodule.smul_mem _ _ hx
  rw [eq_top_iff]
  rintro M -

  have hM : M = ∑ i, ∑ j, M i j • Matrix.single i j (1 : K) := by
    simp only [Matrix.smul_single, smul_eq_mul, mul_one]
    exact Matrix.matrix_eq_sum_single M
  rw [hM]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ ?_

  have hsingle : Matrix.single i j (1 : K) = (Matrix.single i j (1 : k)).map f := by
    rw [Matrix.map_single, map_one]
  rw [hsingle]
  exact key _ (hS ▸ Submodule.mem_top)

end SpanAscent
p2m_reactivate "P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.Representation"

namespace Deformation
p2m_export "Deformation" "matrixRepresentation matrixRepresentation_apply"
p2m_open "Deformation"

p2m_open "Matrix P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.Matrix"

variable {n : Type} [Fintype n] [DecidableEq n]
variable {G : Type u} [Group G]
variable {k : Type u} [Field k]

section
variable {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
set_option backward.isDefEq.respectTransparency false in
private theorem _root_.Representation.IsIrreducible.of_equiv {ρ : Representation k G V}
    {σ : Representation k G W} [Representation.IsIrreducible ρ] (Φ : ρ.Equiv σ) :
    Representation.IsIrreducible σ := by
  haveI : IsSimpleModule (MonoidAlgebra k G) ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  refine (Representation.irreducible_iff_isSimpleModule_asModule σ).mpr ?_
  exact IsSimpleModule.congr
    (LinearEquiv.ofBijective
      (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ Φ.toIntertwiningMap)
      Φ.toLinearEquiv.bijective).symm
p2m_alias "P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.Representation.IsIrreducible.of_equiv" "Representation.IsIrreducible.of_equiv"
end
p2m_reactivate "P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.Representation"

open scoped _root_.Representation _root_.P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.Representation in
set_option backward.isDefEq.respectTransparency false in

noncomputable def matrixRepresentationBaseChangeEquiv {K : Type u} [Field K] [Algebra k K]
    (ρ : G →* GL n k) :
    (Representation.baseChange K (matrixRepresentation ρ)).Equiv
      (matrixRepresentation ((Matrix.GeneralLinearGroup.map (n := n) (algebraMap k K)).comp ρ)) :=
  Representation.Equiv.mk (TensorProduct.piScalarRight k K K n) <| by
    intro g

    apply LinearMap.restrictScalars_injective k
    refine TensorProduct.ext' fun x v => ?_
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
      LinearEquiv.coe_coe]

    have l1 : Representation.baseChange K (matrixRepresentation ρ) g (x ⊗ₜ[k] v) =
        x ⊗ₜ[k] ((ρ g).val *ᵥ v) := by
      show LinearMap.baseChange K (matrixRepresentation ρ g) (x ⊗ₜ[k] v) = _
      rw [matrixRepresentation_apply, LinearMap.baseChange_tmul, Matrix.mulVecLin_apply]
    rw [l1]

    have l2 : ∀ w : n → k, TensorProduct.piScalarRight k K K n (x ⊗ₜ[k] w) =
        fun j => w j • x := fun w => by
      rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    rw [l2, l2, matrixRepresentation_apply]

    funext i
    show ((ρ g).val *ᵥ v) i • x = ((((Matrix.GeneralLinearGroup.map (n := n)
      (algebraMap k K)).comp ρ) g).val *ᵥ fun j => v j • x) i
    show ((ρ g).val *ᵥ v) i • x = (((ρ g).val.map (algebraMap k K)) *ᵥ fun j => v j • x) i
    simp only [Matrix.mulVec_eq_sum, Finset.sum_apply, Pi.smul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    rw [SemigroupAction.mul_smul, Algebra.smul_def]

theorem Burnside.isIrreducible_matrixRepresentation_of_span_eq_top [Nonempty n]
    (ρ : G →* GL n k)
    (hspan : Submodule.span k (Set.range fun g => (ρ g).val) = ⊤) :
    Representation.IsIrreducible (matrixRepresentation ρ) := by
  apply Representation.isIrreducible_of_span_range_eq_top

  have key : ∀ X ∈ Submodule.span k (Set.range fun g => (ρ g).val),
      Matrix.toLin' X ∈ Submodule.span k (Set.range ⇑(matrixRepresentation ρ)) := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      refine Submodule.subset_span ⟨g, ?_⟩
      rw [matrixRepresentation_apply, Matrix.toLin'_apply']
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [map_smul]
      exact Submodule.smul_mem _ _ hx
  rw [Submodule.eq_top_iff']
  intro f

  rw [← Matrix.toLin'_toMatrix' f]
  exact key _ (hspan ▸ Submodule.mem_top)

open scoped _root_.Representation _root_.P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.Representation in

theorem Burnside.isAbsolutelyIrreducible_of_span_eq_top [Nonempty n] (ρ : G →* GL n k)
    (hspan : Submodule.span k (Set.range fun g => (ρ g).val) = ⊤) :
    Representation.IsAbsolutelyIrreducible.{u} (matrixRepresentation ρ) := by
  constructor
  intro K _ _

  have hspanK : Submodule.span K (Set.range fun g =>
      (((Matrix.GeneralLinearGroup.map (n := n) (algebraMap k K)).comp ρ) g).val) = ⊤ := by
    rw [show (Set.range fun g =>
        (((Matrix.GeneralLinearGroup.map (n := n) (algebraMap k K)).comp ρ) g).val) =
        ((fun X : Matrix n n k => X.map (algebraMap k K)) ''
          Set.range fun g => (ρ g).val) by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext fun g => rfl)]
    exact Matrix.span_image_map_eq_top_of_span_eq_top (algebraMap k K) hspan

  haveI : Representation.IsIrreducible (matrixRepresentation
      ((Matrix.GeneralLinearGroup.map (n := n) (algebraMap k K)).comp ρ)) :=
    Burnside.isIrreducible_matrixRepresentation_of_span_eq_top _ hspanK

  exact Representation.IsIrreducible.of_equiv (matrixRepresentationBaseChangeEquiv ρ).symm

end Deformation
p2m_reactivate "P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.Representation"

section
open Module LinearMap
section Burnside

variable {k A V : Type*} [CommRing k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V]
  [Module A V] [IsScalarTower k A V]

namespace IsSimpleModule p2m_export "IsSimpleModule" "mk nontrivial algebraMap_end_bijective_of_isAlgClosed congr" end IsSimpleModule
p2m_open_scoped "IsSimpleModule" in

theorem IsSimpleModule.surjective_toModuleEnd_of_surjective_algebraMap_end
    [Module.Free k V] [Module.Finite k V] [IsSimpleModule A V]
    (hcomm : Function.Surjective (algebraMap k (Module.End A V))) :
    Function.Surjective (Module.toModuleEnd k V : A →+* Module.End k V) := by
  classical
  intro f₀

  have hsmul : ∀ (φ : Module.End A V) (v : V), f₀ (φ • v) = φ • (f₀ v) := by
    intro φ v
    obtain ⟨c, rfl⟩ := hcomm φ
    rw [Module.End.smul_def, Module.End.smul_def, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, map_smul]
  let F : Module.End (Module.End A V) V :=
    { toFun := f₀
      map_add' := f₀.map_add
      map_smul' := hsmul }

  let b := Module.Free.chooseBasis k V
  obtain ⟨a, ha⟩ := jacobson_density (R := A) (M := V) F (Finset.univ.image b)
  refine ⟨a, b.ext fun i ↦ ?_⟩
  have := ha (b i) (Finset.mem_image_of_mem b (Finset.mem_univ i))
  have h__af := this.symm
  simp at h__af ⊢
  exact h__af

end Burnside
p2m_reactivate "P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.Representation"
end
p2m_reactivate "P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.Representation"

namespace Representation
p2m_export "Representation" "free asModule asModuleEquiv irreducible_iff_isSimpleModule_asModule asAlgebraHom IsIrreducible asAlgebraHom_single IntertwiningMap.equivLinearMapAsModule asAlgebraHom_single_one Equiv.conj_apply_self subrepresentation TensorProduct.lid asAlgebraHom_of Equiv.mk IntertwiningMap asModuleEquiv_map_smul asModuleEquiv_symm_map_rho Equiv baseChange IsAbsolutelyIrreducible IsAbsolutelyIrreducible.absolutelyIrreducible span_range_eq_top_of_isAbsolutelyIrreducible_matrix IsIrreducible.of_equiv"
p2m_open "Representation"

section Dictionary

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

theorem range_asAlgebraHom_toLinearMap (ρ : Representation k G V) :
    LinearMap.range ρ.asAlgebraHom.toLinearMap = Submodule.span k (Set.range ⇑ρ) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨r, rfl⟩
    show ρ.asAlgebraHom r ∈ _
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | single g a =>
      rw [asAlgebraHom_single]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨g, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact ⟨MonoidAlgebra.single g 1, ρ.asAlgebraHom_single_one g⟩

theorem span_range_eq_top_iff_surjective_asAlgebraHom (ρ : Representation k G V) :
    Submodule.span k (Set.range ⇑ρ) = ⊤ ↔ Function.Surjective ρ.asAlgebraHom := by
  rw [← range_asAlgebraHom_toLinearMap]
  exact LinearMap.range_eq_top

end Dictionary
p2m_reactivate "P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.Representation"

end Representation
p2m_reactivate "P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.Representation"

namespace Representation
p2m_export "Representation" "free asModule asModuleEquiv irreducible_iff_isSimpleModule_asModule asAlgebraHom IsIrreducible asAlgebraHom_single IntertwiningMap.equivLinearMapAsModule asAlgebraHom_single_one Equiv.conj_apply_self subrepresentation TensorProduct.lid asAlgebraHom_of Equiv.mk IntertwiningMap asModuleEquiv_map_smul asModuleEquiv_symm_map_rho Equiv baseChange IsAbsolutelyIrreducible IsAbsolutelyIrreducible.absolutelyIrreducible span_range_eq_top_of_isAbsolutelyIrreducible_matrix IsIrreducible.of_equiv"
p2m_open "Representation"

section SingleFieldBurnside

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

set_option backward.isDefEq.respectTransparency false in

theorem span_range_eq_top_of_isIrreducible_of_surjective_algebraMap_end
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (hcomm : Function.Surjective
      (algebraMap k (Module.End (MonoidAlgebra k G) ρ.asModule))) :
    Submodule.span k (Set.range ⇑ρ) = ⊤ := by
  rw [span_range_eq_top_iff_surjective_asAlgebraHom]
  haveI : IsSimpleModule (MonoidAlgebra k G) ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance

  have hact := IsSimpleModule.surjective_toModuleEnd_of_surjective_algebraMap_end
    (k := k) (A := MonoidAlgebra k G) (V := ρ.asModule) hcomm

  intro f
  obtain ⟨r, hr⟩ := hact (ρ.asModuleEquiv.symm.toLinearMap ∘ₗ f ∘ₗ ρ.asModuleEquiv.toLinearMap)
  refine ⟨r, LinearMap.ext fun v ↦ ?_⟩

  have happ : (r • (ρ.asModuleEquiv.symm v) : ρ.asModule)
      = (ρ.asModuleEquiv.symm.toLinearMap ∘ₗ f ∘ₗ ρ.asModuleEquiv.toLinearMap)
          (ρ.asModuleEquiv.symm v) :=
    LinearMap.congr_fun hr (ρ.asModuleEquiv.symm v)

  have hdict : ρ.asAlgebraHom r v = ρ.asModuleEquiv (r • ρ.asModuleEquiv.symm v) := by
    rw [asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply]
  rw [hdict, happ]
  simp

end SingleFieldBurnside
p2m_reactivate "P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.Representation"

end Representation
p2m_reactivate "P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.Representation"

namespace Deformation
p2m_export "Deformation" "matrixRepresentation matrixRepresentation_apply"
p2m_open "Deformation"

p2m_open "Matrix P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.Matrix"

variable {n : Type} [Fintype n] [DecidableEq n]
variable {G : Type u} [Group G]
variable {k : Type u} [Field k]

theorem matrixRepresentation_span_range_eq_top_iff (φ : G →* GL n k) :
    Submodule.span k (Set.range ⇑(matrixRepresentation φ)) = ⊤ ↔
      Submodule.span k (Set.range fun g => (φ g).val) = ⊤ := by
  constructor
  · intro h

    have key : ∀ F ∈ Submodule.span k (Set.range ⇑(matrixRepresentation φ)),
        LinearMap.toMatrix' F ∈ Submodule.span k (Set.range fun g => (φ g).val) := by
      intro F hF
      induction hF using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g, rfl⟩ := hx
        refine Submodule.subset_span ⟨g, ?_⟩
        rw [matrixRepresentation_apply, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
    rw [eq_top_iff]
    rintro X -
    have hX := key (Matrix.toLin' X) (h ▸ Submodule.mem_top)
    rwa [LinearMap.toMatrix'_toLin'] at hX
  · intro h

    have key : ∀ X ∈ Submodule.span k (Set.range fun g => (φ g).val),
        Matrix.toLin' X ∈ Submodule.span k (Set.range ⇑(matrixRepresentation φ)) := by
      intro X hX
      induction hX using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g, rfl⟩ := hx
        refine Submodule.subset_span ⟨g, ?_⟩
        rw [matrixRepresentation_apply, Matrix.toLin'_apply']
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
    rw [eq_top_iff]
    rintro F -
    have hF := key (LinearMap.toMatrix' F) (h ▸ Submodule.mem_top)
    rwa [Matrix.toLin'_toMatrix'] at hF

theorem Burnside.span_matrix_eq_top_of_isIrreducible_of_surjective_algebraMap_end
    (φ : G →* GL n k) [Representation.IsIrreducible (matrixRepresentation φ)]
    (hcomm : Function.Surjective
      (algebraMap k (Module.End (MonoidAlgebra k G) (matrixRepresentation φ).asModule))) :
    Submodule.span k (Set.range fun g => (φ g).val) = ⊤ :=
  (matrixRepresentation_span_range_eq_top_iff φ).mp
    (Representation.span_range_eq_top_of_isIrreducible_of_surjective_algebraMap_end
      (matrixRepresentation φ) hcomm)

set_option backward.isDefEq.respectTransparency false in

theorem Burnside.surjective_algebraMap_end_of_span_eq_top (φ : G →* GL n k)
    (hspan : Submodule.span k (Set.range fun g => (φ g).val) = ⊤) :
    Function.Surjective
      (algebraMap k (Module.End (MonoidAlgebra k G) (matrixRepresentation φ).asModule)) := by
  classical
  set ρV := matrixRepresentation φ with hρV
  intro e

  set f : (n → k) →ₗ[k] (n → k) :=
    ρV.asModuleEquiv.toLinearMap ∘ₗ (LinearMap.restrictScalars k e) ∘ₗ
      ρV.asModuleEquiv.symm.toLinearMap with hf
  have hfapply : ∀ v : n → k, f v = ρV.asModuleEquiv (e (ρV.asModuleEquiv.symm v)) := by
    intro v
    simp only [hf, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.restrictScalars_apply]

  have hcommlin : ∀ g : G, f ∘ₗ ρV g = ρV g ∘ₗ f := by
    intro g
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply]
    rw [hfapply, hfapply, Representation.asModuleEquiv_symm_map_rho, map_smul,
      Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]

  have hmatval : ∀ g : G, LinearMap.toMatrix' (ρV g) = (φ g).val := by
    intro g
    rw [hρV, matrixRepresentation_apply, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  have hM : ∀ X ∈ (Set.range fun g => (φ g).val),
      X * LinearMap.toMatrix' f = LinearMap.toMatrix' f * X := by
    rintro X ⟨g, rfl⟩
    calc (φ g).val * LinearMap.toMatrix' f
        = LinearMap.toMatrix' (ρV g) * LinearMap.toMatrix' f := by rw [hmatval]
      _ = LinearMap.toMatrix' (ρV g ∘ₗ f) := (LinearMap.toMatrix'_comp _ _).symm
      _ = LinearMap.toMatrix' (f ∘ₗ ρV g) := by rw [hcommlin]
      _ = LinearMap.toMatrix' f * LinearMap.toMatrix' (ρV g) := LinearMap.toMatrix'_comp _ _
      _ = LinearMap.toMatrix' f * (φ g).val := by rw [hmatval]

  obtain ⟨a, ha⟩ := Matrix.exists_eq_smul_one_of_commute_of_span_eq_top hspan
    (LinearMap.toMatrix' f) hM
  refine ⟨a, ?_⟩

  have hfid : f = a • LinearMap.id := by
    have h1 : f = Matrix.toLin' (LinearMap.toMatrix' f) := (Matrix.toLin'_toMatrix' f).symm
    rw [h1, ha, map_smul, Matrix.toLin'_one]
  have he : ∀ x : ρV.asModule, e x = a • x := by
    intro x
    have h2 : f (ρV.asModuleEquiv x) = a • ρV.asModuleEquiv x := by
      rw [hfid]; rfl
    rw [hfapply, LinearEquiv.symm_apply_apply, ← map_smul] at h2
    exact ρV.asModuleEquiv.injective h2
  apply LinearMap.ext
  intro x
  rw [Module.algebraMap_end_apply]
  exact (he x).symm

theorem Burnside.surjective_algebraMap_end_of_isAbsolutelyIrreducible (φ : G →* GL n k)
    [Representation.IsAbsolutelyIrreducible.{u} (matrixRepresentation φ)] :
    Function.Surjective
      (algebraMap k (Module.End (MonoidAlgebra k G) (matrixRepresentation φ).asModule)) :=
  Burnside.surjective_algebraMap_end_of_span_eq_top φ (Representation.span_range_eq_top_of_isAbsolutelyIrreducible_matrix φ)

theorem Burnside.isAbsolutelyIrreducible_iff_span_eq_top [Nonempty n] (φ : G →* GL n k) :
    Representation.IsAbsolutelyIrreducible.{u} (matrixRepresentation φ) ↔
      Submodule.span k (Set.range fun g => (φ g).val) = ⊤ := by
  constructor
  · intro h
    haveI := h
    exact Representation.span_range_eq_top_of_isAbsolutelyIrreducible_matrix φ
  · intro h
    exact Burnside.isAbsolutelyIrreducible_of_span_eq_top φ h

namespace Burnside

private theorem _root_.Deformation.Burnside.port_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end
    [Nonempty n] (φ : G →* GL n k) :
    Representation.IsAbsolutelyIrreducible.{u} (matrixRepresentation φ) ↔
      (Representation.IsIrreducible (matrixRepresentation φ) ∧
        Function.Surjective
          (algebraMap k (Module.End (MonoidAlgebra k G) (matrixRepresentation φ).asModule))) := by
  constructor
  · intro h
    haveI := h
    have hspan := Representation.span_range_eq_top_of_isAbsolutelyIrreducible_matrix φ
    exact ⟨Burnside.isIrreducible_matrixRepresentation_of_span_eq_top φ hspan,
      Burnside.surjective_algebraMap_end_of_span_eq_top φ hspan⟩
  · rintro ⟨hirr, hcomm⟩
    haveI := hirr
    exact Burnside.isAbsolutelyIrreducible_of_span_eq_top φ
      (Burnside.span_matrix_eq_top_of_isIrreducible_of_surjective_algebraMap_end φ hcomm)

end Burnside
p2m_export "Deformation" "Burnside.port_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end"
end Deformation
p2m_reactivate "P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.Representation"

namespace Representation
p2m_export "Representation" "free asModule asModuleEquiv irreducible_iff_isSimpleModule_asModule asAlgebraHom IsIrreducible asAlgebraHom_single IntertwiningMap.equivLinearMapAsModule asAlgebraHom_single_one Equiv.conj_apply_self subrepresentation TensorProduct.lid asAlgebraHom_of Equiv.mk IntertwiningMap asModuleEquiv_map_smul asModuleEquiv_symm_map_rho Equiv baseChange IsAbsolutelyIrreducible IsAbsolutelyIrreducible.absolutelyIrreducible span_range_eq_top_of_isAbsolutelyIrreducible_matrix IsIrreducible.of_equiv"
p2m_open "Representation"

section Congr

variable {k G V W : Type*} [Field k] [Group G]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

private noncomputable def _root_.Representation.congr (ρ : Representation k G V) (e : V ≃ₗ[k] W) : Representation k G W where
  toFun g := e.toLinearMap ∘ₗ (ρ g) ∘ₗ e.symm.toLinearMap
  map_one' := by
    refine LinearMap.ext fun w => ?_
    simp only [map_one, LinearMap.comp_apply, LinearEquiv.coe_coe, Module.End.one_apply,
      LinearEquiv.apply_symm_apply]
  map_mul' g h := by
    refine LinearMap.ext fun w => ?_
    simp only [map_mul, LinearMap.comp_apply, LinearEquiv.coe_coe, Module.End.mul_apply,
      LinearEquiv.symm_apply_apply]

p2m_export "Representation" "congr"
@[scoped simp]
lemma congr_apply (ρ : Representation k G V) (e : V ≃ₗ[k] W) (g : G) (w : W) :
    ρ.congr e g w = e (ρ g (e.symm w)) := rfl

noncomputable def congrEquiv (ρ : Representation k G V) (e : V ≃ₗ[k] W) :
    ρ.Equiv (ρ.congr e) :=
  Representation.Equiv.mk e <| fun g => by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, congr_apply,
      LinearEquiv.symm_apply_apply]

end Congr
p2m_reactivate "P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.Representation"

section GlMapOfBasisVal

variable {k G V : Type*} [Field k] [Group G]
variable [AddCommGroup V] [Module k V]
variable {n : Type*} [Fintype n] [DecidableEq n]

@[scoped simp]
lemma gl_map_of_basis_val (ρ : Representation k G V) (b : Module.Basis n k V) (g : G) :
    (Representation.gl_map_of_basis ρ b g).val = LinearMap.toMatrix b b (ρ g) :=
  rfl

end GlMapOfBasisVal
p2m_reactivate "P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.Representation"

section BaseChangeEquiv

variable {k G V W : Type*} [Field k] [Group G]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

private noncomputable def _root_.Representation.baseChangeSelfEquiv (ρ : Representation k G V) :
    (Representation.baseChange k ρ).Equiv ρ :=
  Representation.Equiv.mk (_root_.TensorProduct.lid k V) <| fun g => by
    refine _root_.TensorProduct.ext' fun c v => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    show (_root_.TensorProduct.lid k V) (LinearMap.baseChange k (ρ g) (c ⊗ₜ[k] v))
      = ρ g ((_root_.TensorProduct.lid k V) (c ⊗ₜ[k] v))
    rw [LinearMap.baseChange_tmul, _root_.TensorProduct.lid_tmul, _root_.TensorProduct.lid_tmul,
      map_smul]

p2m_export "Representation" "baseChangeSelfEquiv"
namespace Equiv p2m_export "Representation.Equiv" "apply_symm_apply ext symm_apply_apply toIntertwiningMap toLinearEquiv conj_apply_self symm mk trans" end Equiv
namespace Equiv
p2m_open_scoped "Representation.Equiv" in

private noncomputable def _root_.Representation.Equiv.baseChange (K : Type*) [Field K] [Algebra k K]
    {ρ : Representation k G V} {σ : Representation k G W} (Φ : ρ.Equiv σ) :
    (Representation.baseChange K ρ).Equiv (Representation.baseChange K σ) :=
  Representation.Equiv.mk (Φ.toLinearEquiv.baseChange k K V W) <| fun g => by

    show (Φ.toLinearEquiv.toLinearMap.baseChange K) ∘ₗ LinearMap.baseChange K (ρ g)
      = LinearMap.baseChange K (σ g) ∘ₗ (Φ.toLinearEquiv.toLinearMap.baseChange K)
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    exact congrArg (LinearMap.baseChange K) (Φ.toIntertwiningMap.isIntertwining' g)

end Equiv
p2m_export "Representation" "Equiv.baseChange"
end BaseChangeEquiv
p2m_reactivate "P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.Representation"

end Representation
p2m_reactivate "P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.Representation"

namespace Representation
p2m_export "Representation" "free asModule asModuleEquiv irreducible_iff_isSimpleModule_asModule asAlgebraHom IsIrreducible asAlgebraHom_single IntertwiningMap.equivLinearMapAsModule asAlgebraHom_single_one Equiv.conj_apply_self subrepresentation TensorProduct.lid asAlgebraHom_of Equiv.mk IntertwiningMap asModuleEquiv_map_smul asModuleEquiv_symm_map_rho Equiv baseChange IsAbsolutelyIrreducible IsAbsolutelyIrreducible.absolutelyIrreducible span_range_eq_top_of_isAbsolutelyIrreducible_matrix IsIrreducible.of_equiv"
p2m_open "Representation"

section ClassTransport

variable {k G : Type u} [Field k] [Group G]
variable {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

namespace IsAbsolutelyIrreducible p2m_export "Representation.IsAbsolutelyIrreducible" "mk absolutelyIrreducible" end IsAbsolutelyIrreducible
namespace IsAbsolutelyIrreducible
p2m_open_scoped "Representation.IsAbsolutelyIrreducible" in

private theorem _root_.Representation.IsAbsolutelyIrreducible.of_equiv {ρ : Representation k G V} {σ : Representation k G W}
    [Representation.IsAbsolutelyIrreducible.{u} ρ] (Φ : ρ.Equiv σ) :
    Representation.IsAbsolutelyIrreducible.{u} σ := by
  refine ⟨fun K fK aK => ?_⟩
  haveI : Representation.IsIrreducible (Representation.baseChange K ρ) :=
    Representation.IsAbsolutelyIrreducible.absolutelyIrreducible K fK aK
  exact Representation.IsIrreducible.of_equiv (Representation.Equiv.baseChange K Φ)

end IsAbsolutelyIrreducible
p2m_export "Representation" "IsAbsolutelyIrreducible.of_equiv"
end ClassTransport
p2m_reactivate "P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.Representation"

section CommutantTransport

variable {k G V W : Type*} [Field k] [Group G]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

set_option backward.isDefEq.respectTransparency false in

theorem surjective_algebraMap_end_of_equiv {ρ : Representation k G V}
    {σ : Representation k G W} (Φ : ρ.Equiv σ)
    (h : Function.Surjective (algebraMap k (Module.End (MonoidAlgebra k G) ρ.asModule))) :
    Function.Surjective (algebraMap k (Module.End (MonoidAlgebra k G) σ.asModule)) := by

  set E : ρ.asModule ≃ₗ[MonoidAlgebra k G] σ.asModule :=
    LinearEquiv.ofBijective
      (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ Φ.toIntertwiningMap)
      Φ.toLinearEquiv.bijective with hE
  intro f

  obtain ⟨c, hc⟩ := h (E.symm.toLinearMap ∘ₗ f ∘ₗ E.toLinearMap)
  refine ⟨c, LinearMap.ext fun x => ?_⟩

  have h1 := LinearMap.congr_fun hc (E.symm x)
  simp only [Module.algebraMap_end_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] at h1

  have h2 : E (c • E.symm x) = c • x := by
    rw [← IsScalarTower.algebraMap_smul (MonoidAlgebra k G) c (E.symm x), map_smul,
      IsScalarTower.algebraMap_smul, LinearEquiv.apply_symm_apply]
  rw [Module.algebraMap_end_apply, ← h2, h1, LinearEquiv.apply_symm_apply]

theorem span_range_eq_top_of_equiv {ρ : Representation k G V} {σ : Representation k G W}
    (Φ : ρ.Equiv σ) (hspan : Submodule.span k (Set.range ⇑ρ) = ⊤) :
    Submodule.span k (Set.range ⇑σ) = ⊤ := by

  have hmap : Submodule.map Φ.toLinearEquiv.conj.toLinearMap
      (Submodule.span k (Set.range ⇑ρ)) = Submodule.span k (Set.range ⇑σ) := by
    rw [Submodule.map_span]
    refine congrArg (Submodule.span k) (Set.ext fun f => ?_)
    constructor
    · rintro ⟨-, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, (Representation.Equiv.conj_apply_self g Φ).symm⟩
    · rintro ⟨g, rfl⟩
      exact ⟨ρ g, ⟨g, rfl⟩, Representation.Equiv.conj_apply_self g Φ⟩
  rw [← hmap, hspan, Submodule.map_top, LinearMap.range_eq_top]
  exact Φ.toLinearEquiv.conj.surjective

end CommutantTransport
p2m_reactivate "P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.Representation"

end Representation
p2m_reactivate "P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.Representation"

namespace Representation
p2m_export "Representation" "free asModule asModuleEquiv irreducible_iff_isSimpleModule_asModule asAlgebraHom IsIrreducible asAlgebraHom_single IntertwiningMap.equivLinearMapAsModule asAlgebraHom_single_one Equiv.conj_apply_self subrepresentation TensorProduct.lid asAlgebraHom_of Equiv.mk IntertwiningMap asModuleEquiv_map_smul asModuleEquiv_symm_map_rho Equiv baseChange IsAbsolutelyIrreducible IsAbsolutelyIrreducible.absolutelyIrreducible span_range_eq_top_of_isAbsolutelyIrreducible_matrix IsIrreducible.of_equiv"
p2m_open "Representation"

section BasisTransport

variable {k G : Type u} [Field k] [Group G]
variable {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
variable {n : Type} [Fintype n] [DecidableEq n]

noncomputable def equivMatrixRepresentationOfBasis (ρ : Representation k G V)
    (b : Module.Basis n k V) :
    ρ.Equiv (Deformation.matrixRepresentation (Representation.gl_map_of_basis ρ b)) :=
  Representation.Equiv.mk b.equivFun <| fun g => by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [Deformation.matrixRepresentation_apply, Matrix.mulVecLin_apply,
      Representation.gl_map_of_basis_val, Module.Basis.equivFun_apply,
      Module.Basis.equivFun_apply]
    exact (LinearMap.toMatrix_mulVec_repr b b (ρ g) v).symm

end BasisTransport
p2m_reactivate "P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.Representation"

end Representation
p2m_reactivate "P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.Representation"

namespace Representation
p2m_export "Representation" "free asModule asModuleEquiv irreducible_iff_isSimpleModule_asModule asAlgebraHom IsIrreducible asAlgebraHom_single IntertwiningMap.equivLinearMapAsModule asAlgebraHom_single_one Equiv.conj_apply_self subrepresentation TensorProduct.lid asAlgebraHom_of Equiv.mk IntertwiningMap asModuleEquiv_map_smul asModuleEquiv_symm_map_rho Equiv baseChange IsAbsolutelyIrreducible IsAbsolutelyIrreducible.absolutelyIrreducible span_range_eq_top_of_isAbsolutelyIrreducible_matrix IsIrreducible.of_equiv"
p2m_open "Representation"

section Main

variable {k G V : Type u} [Field k] [Group G]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

private theorem _root_.Representation.port_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end
    (ρ : Representation k G V) :
    Representation.IsAbsolutelyIrreducible.{u} ρ ↔
      (Representation.IsIrreducible ρ ∧ Function.Surjective
        (algebraMap k (Module.End (MonoidAlgebra k G) ρ.asModule))) := by
  constructor
  · intro habs
    haveI := habs

    haveI : Representation.IsIrreducible (Representation.baseChange k ρ) :=
      Representation.IsAbsolutelyIrreducible.absolutelyIrreducible k _ _
    haveI hirr : Representation.IsIrreducible ρ :=
      Representation.IsIrreducible.of_equiv ρ.baseChangeSelfEquiv

    haveI : Nontrivial V := Representation.nontrivial_of_isIrreducible ρ
    haveI : Nonempty (Fin (Module.finrank k V)) := (Module.finBasis k V).index_nonempty

    obtain ⟨-, hcommM⟩ :=
      (Deformation.Burnside.port_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end
        (Representation.gl_map_of_basis ρ (Module.finBasis k V))).mp
        (Representation.IsAbsolutelyIrreducible.of_equiv
          (Representation.equivMatrixRepresentationOfBasis ρ (Module.finBasis k V)))

    exact ⟨hirr, Representation.surjective_algebraMap_end_of_equiv
      (Representation.equivMatrixRepresentationOfBasis ρ (Module.finBasis k V)).symm hcommM⟩
  · rintro ⟨hirr, hcomm⟩
    haveI := hirr

    haveI : Nontrivial V := Representation.nontrivial_of_isIrreducible ρ
    haveI : Nonempty (Fin (Module.finrank k V)) := (Module.finBasis k V).index_nonempty

    haveI hirrM : Representation.IsIrreducible
        (Deformation.matrixRepresentation
          (Representation.gl_map_of_basis ρ (Module.finBasis k V))) :=
      Representation.IsIrreducible.of_equiv
        (Representation.equivMatrixRepresentationOfBasis ρ (Module.finBasis k V))
    have hcommM := Representation.surjective_algebraMap_end_of_equiv
      (Representation.equivMatrixRepresentationOfBasis ρ (Module.finBasis k V)) hcomm

    haveI habsM :=
      (Deformation.Burnside.port_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end
        (Representation.gl_map_of_basis ρ (Module.finBasis k V))).mpr ⟨hirrM, hcommM⟩
    exact Representation.IsAbsolutelyIrreducible.of_equiv
      (Representation.equivMatrixRepresentationOfBasis ρ (Module.finBasis k V)).symm

p2m_export "Representation" "port_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end"
end Main
p2m_reactivate "P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.Representation"

end Representation
p2m_reactivate "P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.Representation"

theorem solution {k G V : Type u} [Field k]
  [Group G] [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) :
  Representation.IsAbsolutelyIrreducible.{u} ρ ↔
    ρ.IsIrreducible ∧ Function.Surjective (algebraMap k (Module.End (MonoidAlgebra k G) ρ.asModule)) :=
  Representation.port_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end ρ

end S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end
end P2MW
export P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end (solution)
