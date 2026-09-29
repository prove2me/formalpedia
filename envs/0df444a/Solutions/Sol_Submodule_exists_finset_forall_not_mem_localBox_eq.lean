-- Prove2me | solution 1 for Submodule.exists_finset_forall_not_mem_localBox_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/3eb73265-4565-5d89-a185-be61ac3bcefb

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox

import Theorems.Thm_Submodule_eventually_finiteAdeleEvalAt_mem_localBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_exists_finset_forall_not_mem_localBox_eq

set_option autoImplicit false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField

namespace LC2Body

variable {D : Type*} [Ring D] [Algebra ℚ D]

theorem mul_one_tmul_mem_localBox (Λ : Submodule ℤ D) (v : HeightOneSpectrum (𝓞 ℚ))
    {x : D ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v)
    {c : v.adicCompletion ℚ} (hc : c ∈ v.adicCompletionIntegers ℚ) :
    x * ((1 : D) ⊗ₜ[ℚ] c) ∈ Submodule.localBox Λ v := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨z, hz, c', hc', rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨z, hz, c' * c, mul_mem hc' hc, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | zero => rw [zero_mul]; exact (Submodule.localBox Λ v).zero_mem
  | add y z _ _ hy hz => rw [add_mul]; exact add_mem hy hz
  | neg y _ hy =>
    have := neg_mem hy
    exact (neg_mul y ((1 : D) ⊗ₜ[ℚ] c)).symm ▸ this

theorem tmul_one_mem_localBox_of_mem_span (Λ₁ : Submodule ℤ D) (s : Set D) (v : HeightOneSpectrum (𝓞 ℚ))
    (h : ∀ z ∈ s, (z ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) ∈ Submodule.localBox Λ₁ v)
    {z : D} (hz : z ∈ Submodule.span ℤ s) :
    (z ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) ∈ Submodule.localBox Λ₁ v := by
  induction hz using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => rw [TensorProduct.zero_tmul]; exact (Submodule.localBox Λ₁ v).zero_mem
  | add x y _ _ hx hy => rw [TensorProduct.add_tmul]; exact add_mem hx hy
  | smul n x _ hx =>
    rw [← Int.cast_smul_eq_zsmul ℚ n x, ← TensorProduct.smul_tmul', Int.cast_smul_eq_zsmul]
    exact AddSubgroup.zsmul_mem _ hx n

theorem localBox_le_of_forall_tmul_one_mem (Λ₁ Λ₂ : Submodule ℤ D) (s : Set D)
    (hs : Submodule.span ℤ s = Λ₂) (v : HeightOneSpectrum (𝓞 ℚ))
    (h : ∀ z ∈ s, (z ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) ∈ Submodule.localBox Λ₁ v) :
    Submodule.localBox Λ₂ v ≤ Submodule.localBox Λ₁ v := by
  refine (AddSubgroup.closure_le _).mpr ?_
  rintro x ⟨z, hz, c, hc, rfl⟩
  have hz' : z ∈ Submodule.span ℤ s := by rw [hs]; exact hz
  have := mul_one_tmul_mem_localBox Λ₁ v (tmul_one_mem_localBox_of_mem_span Λ₁ s v h hz') hc
  rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this

theorem exists_finset_forall_not_mem_localBox_le (Λ₁ Λ₂ : Submodule ℤ D)
    (hfg₁ : Λ₁.FG) (hsp₁ : Submodule.span ℚ (Λ₁ : Set D) = ⊤) (hfg₂ : Λ₂.FG) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 ℚ)), ∀ v ∉ S,
      Submodule.localBox Λ₂ v ≤ Submodule.localBox Λ₁ v := by
  classical
  obtain ⟨s, hs⟩ := hfg₂

  have hev : ∀ᶠ v in Filter.cofinite, ∀ z ∈ s,
      (z ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) ∈ Submodule.localBox Λ₁ v := by
    rw [Filter.eventually_all_finset]
    intro z _
    have := Submodule.eventually_finiteAdeleEvalAt_mem_localBox Λ₁ hfg₁ hsp₁
      (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ))
    refine this.mono fun v hv => ?_
    rwa [Submodule.finiteAdeleEvalAt_tmul, ← Submodule.finiteAdeleEvalAlgHom_apply, map_one] at hv
  rw [Filter.eventually_cofinite] at hev
  refine ⟨hev.toFinset, fun v hv => ?_⟩
  have hv' : ∀ z ∈ s, (z ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) ∈ Submodule.localBox Λ₁ v := by
    by_contra hcon
    exact hv (hev.mem_toFinset.mpr hcon)
  exact localBox_le_of_forall_tmul_one_mem Λ₁ Λ₂ (s : Set D) hs v (fun z hz => hv' z hz)

end LC2Body

open LC2Body in
theorem solution
    {D : Type*} [Ring D] [Algebra ℚ D]
    (Λ₁ Λ₂ : Submodule ℤ D) (hfg₁ : Λ₁.FG) (hsp₁ : Submodule.span ℚ (Λ₁ : Set D) = ⊤)
    (hfg₂ : Λ₂.FG) (hsp₂ : Submodule.span ℚ (Λ₂ : Set D) = ⊤) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 ℚ)), ∀ v ∉ S,
      Submodule.localBox Λ₁ v = Submodule.localBox Λ₂ v := by
  classical
  obtain ⟨S₁, h₁⟩ := exists_finset_forall_not_mem_localBox_le Λ₁ Λ₂ hfg₁ hsp₁ hfg₂
  obtain ⟨S₂, h₂⟩ := exists_finset_forall_not_mem_localBox_le Λ₂ Λ₁ hfg₂ hsp₂ hfg₁
  refine ⟨S₁ ∪ S₂, fun v hv => ?_⟩
  rw [Finset.mem_union, not_or] at hv
  exact le_antisymm (h₂ v hv.2) (h₁ v hv.1)

end S_Submodule_exists_finset_forall_not_mem_localBox_eq
end P2MW
export P2MW.S_Submodule_exists_finset_forall_not_mem_localBox_eq (solution)
