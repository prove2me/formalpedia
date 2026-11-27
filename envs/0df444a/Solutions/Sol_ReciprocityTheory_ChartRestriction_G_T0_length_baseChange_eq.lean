-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.length_baseChange_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:28:49.544875+00:00
-- url     : https://prove2.me/submissions/292d9807-c706-4b7a-88d1-186731f92131

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FlatLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
private theorem length_baseChange_of_isSimpleModule {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S]
    (hm : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S)
    (X : Type*) [AddCommGroup X] [Module R X] [hX : IsSimpleModule R X] :
    Module.length S (S ⊗[R] X) = Module.length R X := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hX
  have hIm : I.map (algebraMap R S) = IsLocalRing.maximalIdeal S := by
    rw [IsLocalRing.eq_maximalIdeal hI, hm]
  have e2 : (S ⊗[R] X) ≃ₗ[S] (S ⧸ IsLocalRing.maximalIdeal S) :=
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) e).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm.toLinearEquiv.trans
        (Submodule.quotEquivOfEq _ _ hIm))
  have : IsSimpleModule S (S ⧸ IsLocalRing.maximalIdeal S) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal S))
  have : IsSimpleModule S (S ⊗[R] X) := IsSimpleModule.congr e2
  rw [Module.length_eq_one, Module.length_eq_one]
private theorem length_baseChange_of_submodule_simple_quotient {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S] [Module.Flat R S]
    (hm : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S)
    {M : Type*} [AddCommGroup M] [Module R M] (N : Submodule R M) [IsSimpleModule R (M ⧸ N)]
    (ih : Module.length S (S ⊗[R] N) = Module.length R N) :
    Module.length S (S ⊗[R] M) = Module.length R M := by
  have hinj : Function.Injective (N.subtype.baseChange S) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ N.injective_subtype
  have hsurj : Function.Surjective (N.mkQ.baseChange S) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective S N.mkQ_surjective
  have hex : Function.Exact (N.subtype.baseChange S) (N.mkQ.baseChange S) := by
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact lTensor_exact S (LinearMap.exact_subtype_mkQ N) N.mkQ_surjective
  rw [Module.length_eq_add_of_exact _ _ hinj hsurj hex,
    Module.length_eq_add_of_exact _ _ N.injective_subtype N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N),
    ih, length_baseChange_of_isSimpleModule hm (M ⧸ N)]
private theorem length_baseChange_of_isFiniteLength {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S] [Module.Flat R S]
    (hm : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S)
    {M : Type*} [AddCommGroup M] [Module R M] (h : IsFiniteLength R M) :
    Module.length S (S ⊗[R] M) = Module.length R M := by
  induction h with
  | @of_subsingleton M' _ _ _ =>
    have : Subsingleton (S ⊗[R] M') := by
      have h0 : ∀ z : S ⊗[R] M', z = 0 := fun z => by
        induction z using TensorProduct.induction_on with
        | zero => rfl
        | tmul s m => rw [Subsingleton.elim m 0, TensorProduct.tmul_zero]
        | add x y hx hy => rw [hx, hy, add_zero]
      exact ⟨fun a b => by rw [h0 a, h0 b]⟩
    rw [Module.length_eq_zero, Module.length_eq_zero]
  | of_simple_quotient _ ih =>
    exact length_baseChange_of_submodule_simple_quotient hm _ ih
private theorem length_le_length_baseChange_of_faithfullyFlat {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] (Q : Type*) [AddCommGroup Q] [Module R Q] :
    Module.length R Q ≤ Module.length S (S ⊗[R] Q) := by
  have hmono : ∀ N N' : Submodule R Q, N ≤ N' →
      LinearMap.range (N.subtype.baseChange S) ≤ LinearMap.range (N'.subtype.baseChange S) := by
    intro N N' h x hx
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hx
    refine LinearMap.mem_range.mpr ⟨(Submodule.inclusion h).baseChange S z, ?_⟩
    rw [← Submodule.subtype_comp_inclusion _ _ h, LinearMap.baseChange_comp, LinearMap.comp_apply]
  have hrefl : ∀ N N' : Submodule R Q,
      LinearMap.range (N'.subtype.baseChange S) ≤ LinearMap.range (N.subtype.baseChange S) →
        N' ≤ N := by
    intro N N' h
    have hz : ∀ w : S ⊗[R] N, (N.mkQ.baseChange S) ((N.subtype.baseChange S) w) = 0 := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]
      | tmul s n =>
        have hn : N.mkQ (N.subtype n) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr n.2
        rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, hn, TensorProduct.tmul_zero]
      | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
    have h0 : (N.mkQ ∘ₗ N'.subtype).lTensor S = 0 := by
      refine LinearMap.ext fun z => ?_
      obtain ⟨w, hw⟩ :=
        LinearMap.mem_range.mp (h (LinearMap.mem_range_self (N'.subtype.baseChange S) z))
      have hb : ((N.mkQ ∘ₗ N'.subtype).baseChange S) z = 0 := by
        rw [LinearMap.baseChange_comp, LinearMap.comp_apply, ← hw, hz]
      rw [LinearMap.zero_apply]
      rwa [LinearMap.baseChange_eq_ltensor] at hb
    have hf : N.mkQ ∘ₗ N'.subtype = 0 :=
      (Module.FaithfullyFlat.zero_iff_lTensor_zero R S _).mpr h0
    intro x hx
    have hx0 := LinearMap.congr_fun hf ⟨x, hx⟩
    simpa using hx0
  have hsm : StrictMono (fun N : Submodule R Q => LinearMap.range (N.subtype.baseChange S)) :=
    fun N N' hlt => lt_of_le_of_ne (hmono N N' hlt.le)
      (fun heq => hlt.ne (le_antisymm hlt.le (hrefl N N' heq.ge)))
  have h1 : (Module.length R Q : WithBot ℕ∞) ≤ (Module.length S (S ⊗[R] Q) : WithBot ℕ∞) := by
    rw [Module.coe_length, Module.coe_length]
    exact Order.krullDim_le_of_strictMono _ hsm
  exact WithBot.coe_le_coe.mp h1
end ReciprocityTheory.ChartRestriction.G.T0
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] [Algebra R S] [Module.Flat R S] [IsLocalHom (algebraMap R S)]
    (hm : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S)
    (Q : Type*) [AddCommGroup Q] [Module R Q] :
    Module.length S (S ⊗[R] Q) = Module.length R Q := by
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hge := length_le_length_baseChange_of_faithfullyFlat (R := R) (S := S) Q
  by_cases hQ : Module.length R Q = ⊤
  · rw [hQ] at hge ⊢
    exact top_le_iff.mp hge
  · exact length_baseChange_of_isFiniteLength hm (Module.length_ne_top_iff.mp hQ)
end ReciprocityTheory.ChartRestriction.G.T0
