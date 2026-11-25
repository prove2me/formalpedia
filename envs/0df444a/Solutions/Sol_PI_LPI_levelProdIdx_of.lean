-- Prove2me | solution 1 for PI.LPI.levelProdIdx_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:47:33.69789+00:00
-- url     : https://prove2.me/submissions/0e8e0061-bd3c-4bbe-b03f-61555139ec0d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LevelProdIdx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_Development
import Theorems.Thm_PI_LPI_bc_mulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
namespace PI.LPI
open Formalism.UG
private theorem index_comap_ne_zero_lemma {G H : Type*} [Group G] [Group H] (f : G →* H)
    (K : Subgroup H) (hK : K.index ≠ 0) : (K.comap f).index ≠ 0 := by
  haveI : K.FiniteIndex := ⟨hK⟩
  have hr : ∀ a b : G, (QuotientGroup.leftRel (K.comap f)) a b →
      (QuotientGroup.leftRel K) (f a) (f b) := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    rw [Subgroup.mem_comap, map_mul, map_inv] at hab
    exact hab
  let g : G ⧸ K.comap f → H ⧸ K := Quotient.map' f hr
  have hinj : Function.Injective g := by
    intro q1 q2
    induction q1 using QuotientGroup.induction_on with
    | H a =>
    induction q2 using QuotientGroup.induction_on with
    | H b =>
    intro h
    have h1 : ((f a : H) : H ⧸ K) = ((f b : H) : H ⧸ K) := h
    rw [QuotientGroup.eq] at h1
    rw [QuotientGroup.eq, Subgroup.mem_comap, map_mul, map_inv]
    exact h1
  haveI : Finite (G ⧸ K.comap f) := Finite.of_injective g hinj
  exact Subgroup.index_ne_zero_of_finite
end PI.LPI
end
end

set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.LPI
open Formalism.UG
namespace PI.LPI
theorem _root_.solution (hD : PLDown) (hU : PLUp) (hL : PLLocal) : PI.LevelProdIdx := by
  unfold PI.LevelProdIdx
  intro F E _ _ _ _ _ n σ J Lb Uloc U hfin _ hUdef hle hfinite hidx
  have hsub : U ≤ levelAfL σ J Lb := by
    intro x hx
    have hx' := (hUdef x).1 hx
    refine ⟨hx'.1, ?_⟩
    intro y
    have hloc : ∀ v : HeightOneSpectrum (𝓞 F), (fun j => prV (E := E) v
        (((x : Matrix (Fin n) (Fin n) _) *ᵥ y) j)) =
        ((bc (prV (E := E) v) x : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
          (fun j => prV (E := E) v (y j)) := fun v => bc_mulVec (prV (E := E) v) x y
    have hxv : ∀ v : HeightOneSpectrum (𝓞 F), bc (prV (E := E) v) x ∈ levelVL σ J v Lb :=
      fun v => hle v (hx'.2 v)
    constructor
    · intro hy
      refine hU F E n Lb hfin _ fun v => ?_
      rw [hloc v]
      exact ((hxv v).2 _).1 (hD F E n Lb v y hy)
    · intro hy
      refine hU F E n Lb hfin _ fun v => ?_
      have h1 := hD F E n Lb v _ hy
      rw [hloc v] at h1
      exact ((hxv v).2 _).2 h1
  refine ⟨hsub, ?_⟩
  set S := {v | Uloc v ≠ levelVL σ J v Lb} with hS
  haveI : Finite S := hfinite.to_subtype
  let φ : ∀ v : HeightOneSpectrum (𝓞 F), (levelAfL σ J Lb) →* (levelVL σ J v Lb) := fun v =>
    ((bc (prV (E := E) v)).comp (levelAfL σ J Lb).subtype).codRestrict (levelVL σ J v Lb)
      (fun x => hL F E n σ J Lb hfin x.1 x.2 v)
  let K : S → Subgroup (levelAfL σ J Lb) := fun v =>
    ((Uloc v.1).subgroupOf (levelVL σ J v.1 Lb)).comap (φ v.1)
  have hK : ∀ v : S, (K v).FiniteIndex := by
    intro v
    exact ⟨index_comap_ne_zero_lemma (φ v.1) _ (hidx v.1)⟩
  have hle2 : (⨅ v : S, K v) ≤ U.subgroupOf (levelAfL σ J Lb) := by
    intro x hx
    rw [Subgroup.mem_iInf] at hx
    rw [Subgroup.mem_subgroupOf, hUdef]
    refine ⟨x.2.1, fun v => ?_⟩
    by_cases hv : v ∈ S
    · have h1 := hx ⟨v, hv⟩
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at h1
      exact h1
    · have h2 : Uloc v = levelVL σ J v Lb := by
        simpa [hS] using hv
      rw [h2]
      exact hL F E n σ J Lb hfin x.1 x.2 v
  haveI : (⨅ v : S, K v).FiniteIndex := Subgroup.finiteIndex_iInf hK
  haveI : (U.subgroupOf (levelAfL σ J Lb)).FiniteIndex := Subgroup.finiteIndex_of_le hle2
  exact Subgroup.FiniteIndex.index_ne_zero
end PI.LPI
