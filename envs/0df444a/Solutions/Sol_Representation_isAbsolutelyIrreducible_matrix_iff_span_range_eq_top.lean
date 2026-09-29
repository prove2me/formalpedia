-- Prove2me | solution 1 for Representation.isAbsolutelyIrreducible_matrix_iff_span_range_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/36336460-fae2-523f-878d-28648879146d

import Mathlib
import Definitions.Def_Deformations_MatrixRepresentation
import Definitions.Def_Representation_AbsolutelyIrreducible
import Theorems.Thm_Representation_span_range_eq_top_of_isAbsolutelyIrreducible_matrix
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_isAbsolutelyIrreducible_matrix_iff_span_range_eq_top

open Module LinearMap

universe u

section AbstractConverse

variable {k : Type*} [Field k] {G : Type*} [Monoid G]
variable {V : Type*} [AddCommGroup V] [Module k V]

namespace Representation p2m_export "Representation" "asModule irreducible_iff_isSimpleModule_asModule IsIrreducible IntertwiningMap.equivLinearMapAsModule subrepresentation Equiv.mk IntertwiningMap Equiv baseChange IsAbsolutelyIrreducible span_range_eq_top_of_isAbsolutelyIrreducible_matrix" end Representation
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

section SpanAscent

variable {n : Type} [Fintype n] [DecidableEq n]

namespace Matrix p2m_export "Matrix" "ext mulVec_eq_sum add map_apply smul_single zero IsIrreducible map_single GeneralLinearGroup.map transpose_apply comp mulVecLin_apply rank smul matrix_eq_sum_single single GeneralLinearGroup smul_apply toLinearEquiv toLin'_apply' comp_apply of sum_apply toLin'_toMatrix' map toLin' one" end Matrix
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

namespace Deformation
p2m_export "Deformation" "matrixRepresentation matrixRepresentation_apply"
p2m_open "Deformation"
namespace SolAux

p2m_open "Matrix P2MW.S_Representation_isAbsolutelyIrreducible_matrix_iff_span_range_eq_top.Matrix"

variable {n : Type} [Fintype n] [DecidableEq n]
variable {G : Type u} [Group G]
variable {k : Type u} [Field k]

section
variable {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
set_option backward.isDefEq.respectTransparency false in
theorem solAux_isIrreducible_of_equiv {ρ : Representation k G V}
    {σ : Representation k G W} [Representation.IsIrreducible ρ] (Φ : ρ.Equiv σ) :
    Representation.IsIrreducible σ := by
  haveI : IsSimpleModule (MonoidAlgebra k G) ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  refine (Representation.irreducible_iff_isSimpleModule_asModule σ).mpr ?_
  exact IsSimpleModule.congr
    (LinearEquiv.ofBijective
      (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ Φ.toIntertwiningMap)
      Φ.toLinearEquiv.bijective).symm
end

open scoped _root_.Representation _root_.P2MW.S_Representation_isAbsolutelyIrreducible_matrix_iff_span_range_eq_top.Representation in
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

end SolAux

p2m_open "Matrix P2MW.S_Representation_isAbsolutelyIrreducible_matrix_iff_span_range_eq_top.Matrix"

variable {n : Type} [Fintype n] [DecidableEq n]
variable {G : Type u} [Group G]
variable {k : Type u} [Field k]

theorem SolAux.isIrreducible_matrixRepresentation_of_span_eq_top [Nonempty n]
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

open scoped _root_.Representation _root_.P2MW.S_Representation_isAbsolutelyIrreducible_matrix_iff_span_range_eq_top.Representation in

theorem SolAux.isAbsolutelyIrreducible_of_span_eq_top [Nonempty n] (ρ : G →* GL n k)
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
    SolAux.isIrreducible_matrixRepresentation_of_span_eq_top _ hspanK

  exact SolAux.solAux_isIrreducible_of_equiv (SolAux.matrixRepresentationBaseChangeEquiv ρ).symm

end Deformation

universe v

theorem solution {n : Type} [Fintype n] [DecidableEq n] {G : Type u}
    [Group G] {k : Type u} [Field k] [Nonempty n] (φ : G →* GL n k) :
    Representation.IsAbsolutelyIrreducible.{u} (Deformation.matrixRepresentation φ) ↔
      Submodule.span k (Set.range fun g => (φ g).val) = ⊤ := by
  constructor
  · intro h
    haveI := h
    exact Representation.span_range_eq_top_of_isAbsolutelyIrreducible_matrix φ
  · intro h
    exact Deformation.SolAux.isAbsolutelyIrreducible_of_span_eq_top φ h

end S_Representation_isAbsolutelyIrreducible_matrix_iff_span_range_eq_top
end P2MW
export P2MW.S_Representation_isAbsolutelyIrreducible_matrix_iff_span_range_eq_top (solution)
