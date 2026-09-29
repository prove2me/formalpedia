-- Prove2me | solution 1 for Representation.span_range_baseChange_eq_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/9fce71dc-0021-5094-b7ea-f96be56acfb7

import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_span_range_baseChange_eq_top_iff

set_option autoImplicit false

open Module LinearMap
open scoped TensorProduct

namespace C6PortS10BNA2

section

variable {k K V : Type*} [Field k] [Field K] [Algebra k K] [AddCommGroup V] [Module k V]

private theorem apply_mem_of_mem_span {M N : Type*} [AddCommMonoid M] [Module k M]
    [AddCommMonoid N] [Module k N] [Module K N] [IsScalarTower k K N]
    (Φ : M →ₗ[k] N) (T : Submodule K N) {s : Set M} (hs : ∀ x ∈ s, Φ x ∈ T)
    {x : M} (hx : x ∈ Submodule.span k s) : Φ x ∈ T := by
  have h : Submodule.span k s ≤ (T.restrictScalars k).comap Φ :=
    Submodule.span_le.mpr fun y hy => hs y hy
  exact h hx

private theorem baseChange_mem_span_of_mem_span {G : Type*} (ρ : G → Module.End k V)
    {f : Module.End k V} (hf : f ∈ Submodule.span k (Set.range ρ)) :
    f.baseChange K ∈ Submodule.span K (Set.range fun g => (ρ g).baseChange K) := by
  refine apply_mem_of_mem_span (LinearMap.baseChangeHom k K V V) _ ?_ hf
  rintro _ ⟨g, rfl⟩
  exact Submodule.subset_span ⟨g, rfl⟩

variable [FiniteDimensional k V]

private theorem span_eq_top_of_span_baseChange_eq_top {G : Type*} (ρ : G → Module.End k V)
    (hK : Submodule.span K (Set.range fun g => (ρ g).baseChange K) = ⊤) :
    Submodule.span k (Set.range ρ) = ⊤ := by
  let S : Submodule k (Module.End k V) := Submodule.span k (Set.range ρ)
  let bS := Module.finBasis k S

  let T : Submodule K (Module.End K (K ⊗[k] V)) :=
    Submodule.span K (Set.range fun i => ((bS i : S) : Module.End k V).baseChange K)

  have hST : ∀ f ∈ S, f.baseChange K ∈ T := by
    intro f hf
    have hf' : f ∈ Submodule.span k (Set.range fun i => ((bS i : S) : Module.End k V)) := by
      have h := congrArg Subtype.val (bS.sum_repr ⟨f, hf⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h
      rw [← h]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    refine apply_mem_of_mem_span (LinearMap.baseChangeHom k K V V) T ?_ hf'
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩

  have hTtop : T = ⊤ := by
    refine eq_top_iff.mpr (hK ▸ Submodule.span_le.mpr ?_)
    rintro _ ⟨g, rfl⟩
    exact hST _ (Submodule.subset_span ⟨g, rfl⟩)

  have h1 : finrank K (Module.End K (K ⊗[k] V)) ≤ finrank k S := by
    have h := finrank_range_le_card (R := K) fun i => ((bS i : S) : Module.End k V).baseChange K
    rw [Fintype.card_fin] at h
    have hT' : finrank K T = finrank K (Module.End K (K ⊗[k] V)) := by rw [hTtop, finrank_top]
    exact hT' ▸ h
  have h2 : finrank K (Module.End K (K ⊗[k] V)) = finrank k (Module.End k V) := by
    rw [Module.finrank_linearMap, Module.finrank_linearMap, Module.finrank_baseChange]
  have h3 : finrank k S ≤ finrank k (Module.End k V) := Submodule.finrank_le S
  exact Submodule.eq_top_of_finrank_eq (le_antisymm h3 (h2 ▸ h1))

private noncomputable def elem {ι : Type*} (b : Basis ι k V) (i j : ι) : Module.End k V :=
  (b.coord j).smulRight (b i)

omit [FiniteDimensional k V] in
private theorem baseChange_elem_apply_basis {ι : Type*} [DecidableEq ι] (b : Basis ι k V)
    (i j l : ι) :
    (elem b i j).baseChange K (Algebra.TensorProduct.basis K b l) =
      if l = j then Algebra.TensorProduct.basis K b i else 0 := by
  rw [Algebra.TensorProduct.basis_apply, LinearMap.baseChange_tmul, elem, LinearMap.smulRight_apply,
    Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  split_ifs with h
  · rw [one_smul, Algebra.TensorProduct.basis_apply]
  · rw [zero_smul, TensorProduct.tmul_zero]

private theorem span_baseChange_eq_top_of_span_eq_top {G : Type*} (ρ : G → Module.End k V)
    (hk : Submodule.span k (Set.range ρ) = ⊤) :
    Submodule.span K (Set.range fun g => (ρ g).baseChange K) = ⊤ := by
  classical
  set T := Submodule.span K (Set.range fun g => (ρ g).baseChange K) with hT
  have hall : ∀ f : Module.End k V, f.baseChange K ∈ T := fun f =>
    baseChange_mem_span_of_mem_span ρ (hk ▸ Submodule.mem_top)
  let b := Module.finBasis k V
  let b' := Algebra.TensorProduct.basis K b
  refine eq_top_iff.mpr fun F _ => ?_

  have hF : F = ∑ l, ∑ i, b'.repr (F (b' l)) i • (elem b i l).baseChange K := by
    refine b'.ext fun m => ?_
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    rw [Finset.sum_eq_single m]
    · conv_lhs => rw [← b'.sum_repr (F (b' m))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [baseChange_elem_apply_basis, if_pos rfl]
    · intro l _ hlm
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [baseChange_elem_apply_basis, if_neg (Ne.symm hlm), smul_zero]
    · intro h; exact absurd (Finset.mem_univ m) h
  rw [hF]
  exact Submodule.sum_mem _ fun l _ => Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (hall _)

end

end C6PortS10BNA2

open C6PortS10BNA2 in
theorem solution
    {k K G V : Type*} [Field k] [Field K] [Algebra k K] [Monoid G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k G V) :
    Submodule.span K (Set.range fun g => (ρ g).baseChange K) = ⊤ ↔
      Submodule.span k (Set.range ⇑ρ) = ⊤ :=
  ⟨span_eq_top_of_span_baseChange_eq_top (K := K) ⇑ρ, span_baseChange_eq_top_of_span_eq_top (K := K) ⇑ρ⟩

end S_Representation_span_range_baseChange_eq_top_iff
end P2MW
export P2MW.S_Representation_span_range_baseChange_eq_top_iff (solution)
