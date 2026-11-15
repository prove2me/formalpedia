-- Prove2me | solution 1 for WatrousTQI.unital_qubit_is_mixed_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T15:34:56.139042+00:00
-- url     : https://prove2.me/submissions/9f89f9d6-32ed-4cdd-8e6f-9e98c9c40abd

import Theorems.Thm_Grunbaum2003_bounded_closed_convex_extreme_representation
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Convex.Combination
import Theorems.Thm_WatrousTQI_extreme_unital_qubit_is_unitary
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P11
import Theorems.Thm_WatrousTQI_unital_channels_compact_convex
import Mathlib.Analysis.RCLike.Basic
set_option autoImplicit false
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OwnMinkowski
lemma injective_image_extreme {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (f : V →ₗ[ℝ] W) (hf : Function.Injective f)
    (S : Set V) (x : V) : f x ∈ (f '' S).extremePoints ℝ ↔ x ∈ S.extremePoints ℝ := by
  constructor
  · intro h
    have hx : x ∈ S := by
      obtain ⟨y,hy,hxy⟩ := h.1
      exact hf hxy ▸ hy
    refine ⟨hx,?_⟩
    intro y hy z hz hseg
    apply hf
    apply h.2 ⟨y,hy,rfl⟩ ⟨z,hz,rfl⟩
    obtain ⟨a,b,ha,hb,hab,heq⟩ := hseg
    exact ⟨a,b,ha,hb,hab,by rw [← map_smul,← map_smul,← map_add,heq]⟩
  · intro h
    refine ⟨⟨x,h.1,rfl⟩,?_⟩
    rintro _ ⟨y,hy,rfl⟩ _ ⟨z,hz,rfl⟩ hseg
    apply congrArg f
    apply h.2 hy hz
    obtain ⟨a,b,ha,hb,hab,heq⟩ := hseg
    exact ⟨a,b,ha,hb,hab,hf (by rw [map_add,map_smul,map_smul];exact heq)⟩

lemma span_hull {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (S : Set E) (hS : IsCompact S) (hconv : Convex ℝ S)
    [FiniteDimensional ℝ (Submodule.span ℝ S)] :
    S ⊆ convexHull ℝ (S.extremePoints ℝ) := by
  classical
  intro x hx
  let W := Submodule.span ℝ S
  let K : Set W := {w | (w : E) ∈ S}
  have himage : W.subtype '' K = S := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩;exact hz
    · intro hy;exact ⟨⟨y,Submodule.subset_span hy⟩,hy,rfl⟩
  have hKcomp : IsCompact K := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    change IsCompact (W.subtype '' K)
    rw [himage]
    exact hS
  have hKconv : Convex ℝ K := hconv.linear_preimage W.subtype
  let e : W ≃ₗ[ℝ] (Fin (Module.finrank ℝ W) → ℝ) := (Module.finBasis ℝ W).equivFun
  let K' := e '' K
  have hK'comp : IsCompact K' := hKcomp.image e.toContinuousLinearEquiv.continuous
  have hK'conv : Convex ℝ K' := hKconv.linear_image e.toLinearMap
  have hw : (⟨x,Submodule.subset_span hx⟩ : W) ∈ K := hx
  have hy : e ⟨x,Submodule.subset_span hx⟩ ∈ K' := ⟨_,hw,rfl⟩
  have hrep : K' = convexHull ℝ (K'.extremePoints ℝ) :=
    Grunbaum2003.bounded_closed_convex_extreme_representation K' ⟨_,hy⟩
      hK'comp.isBounded hK'comp.isClosed hK'conv
  let g : (Fin (Module.finrank ℝ W) → ℝ) →ₗ[ℝ] E := W.subtype.comp e.symm.toLinearMap
  have hg : Function.Injective g := Subtype.val_injective.comp e.symm.injective
  have hgK : g '' K' = S := by
    rw [← himage]
    ext y
    constructor
    · rintro ⟨z,⟨w,hw,rfl⟩,rfl⟩
      exact ⟨w,hw,by simp [g]⟩
    · rintro ⟨w,hw,rfl⟩
      exact ⟨e w,⟨w,hw,rfl⟩,by simp [g]⟩
  have hge : g '' (K'.extremePoints ℝ) ⊆ S.extremePoints ℝ := by
    rintro _ ⟨z,hz,rfl⟩
    rw [← hgK]
    exact (injective_image_extreme g hg K' z).mpr hz
  have hmem : g (e ⟨x,Submodule.subset_span hx⟩) ∈
      g '' convexHull ℝ (K'.extremePoints ℝ) := ⟨_,hrep ▸ hy,rfl⟩
  have hconvimage : g '' convexHull ℝ (K'.extremePoints ℝ) = convexHull ℝ (g '' (K'.extremePoints ℝ)) :=
    g.toAffineMap.image_convexHull _
  rw [hconvimage] at hmem
  have := convexHull_mono hge hmem
  simpa [g] using this
end OwnMinkowski

noncomputable section
open scoped Matrix ComplexConjugate
set_option backward.isDefEq.respectTransparency false
open QAlgorithms

set_option autoImplicit false



theorem solution
    (Φ : QAlgorithms.Superop (Fin 2) (Fin 2))
    (hΦ : QAlgorithms.IsChannel Φ)
    (hu : Φ (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1) :
    QAlgorithms.Papers.Independent.Dependency50.P11.IsRandomUnitary Φ := by
  classical
  obtain ⟨hc,hconv,hfinite⟩ := WatrousTQI.unital_channels_compact_convex 2 (by decide)
  letI : FiniteDimensional ℝ (Submodule.span ℝ (WatrousTQI.unitalChannels 2)) := hfinite
  have hh : Φ ∈ convexHull ℝ ((WatrousTQI.unitalChannels 2).extremePoints ℝ) :=
    OwnMinkowski.span_hull _ hc hconv ⟨hΦ,hu⟩
  obtain ⟨ι,hι,w,z,hw,hs,hz,heq⟩ := mem_convexHull_iff_exists_fintype.mp hh
  letI : Fintype ι := hι
  have hunit (i : ι) : ∃ U : Matrix.unitaryGroup (Fin 2) ℂ,
      ∀ X, z i X = (U : Matrix (Fin 2) (Fin 2) ℂ) * X * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ :=
    WatrousTQI.extreme_unital_qubit_is_unitary (z i) (hz i)
  choose U hU using hunit
  have hw1 (i : ι) : w i ≤ 1 := by
    rw [← hs]
    exact Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ i)
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι,fun j => w (e j),fun j => U (e j),?_,?_,?_⟩
  · intro j;exact ⟨hw (e j),hw1 (e j)⟩
  · exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).trans hs
  · intro X
    have hX : Φ X = ∑ i : ι, (w i : ℂ) • (z i X) := by
      have hh := congrFun heq X
      ext o p
      have hentry := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℂ => B o p) hh
      simp only [Finset.sum_apply,Matrix.sum_apply,Pi.smul_apply,Matrix.smul_apply,
        RCLike.real_smul_eq_coe_mul,smul_eq_mul] at hentry
      simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
      exact hentry.symm
    rw [hX]
    calc
      _ = ∑ i : ι, (w i : ℂ) • ((U i : Matrix (Fin 2) (Fin 2) ℂ) * X * (U i : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hU i X]
      _ = _ := (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
