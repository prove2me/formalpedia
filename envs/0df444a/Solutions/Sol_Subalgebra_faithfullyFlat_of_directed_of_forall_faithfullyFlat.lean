-- Prove2me | solution 1 for Subalgebra.faithfullyFlat_of_directed_of_forall_faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/2af10990-dcea-582c-9bfd-8ddd4de9c33a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subalgebra_faithfullyFlat_of_directed_of_forall_faithfullyFlat

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped TensorProduct

universe u v w

set_option maxHeartbeats 4000000 in
theorem solution
    {k : Type u} [Field k] {H : Type v} [CommRing H] [Algebra k H] (K : Subalgebra k H)
    {ι : Type w} [Nonempty ι] (F : ι → Subalgebra k H) (hdir : Directed (· ≤ ·) F)
    (hle : ∀ i, F i ≤ K) (hcov : ∀ x ∈ K, ∃ i, x ∈ F i)
    (hff : ∀ i, Module.FaithfullyFlat ↥(F i) H) :
    Module.FaithfullyFlat ↥K H := by
  classical

  have hfin : ∀ (n : ℕ) (g : Fin n → ↥K), ∃ i, ∀ a, ((g a : ↥K) : H) ∈ F i := by
    intro n g
    choose j hj using fun a => hcov _ (g a).2
    obtain ⟨i, hi⟩ := hdir.finset_le (Finset.univ.image j)
    exact ⟨i, fun a => hi (j a) (Finset.mem_image_of_mem j (Finset.mem_univ a)) (hj a)⟩
  have hfin' : ∀ {α : Type _} [Fintype α] (g : α → ↥K), ∃ i, ∀ a, ((g a : ↥K) : H) ∈ F i := by
    intro α _ g
    obtain ⟨i, hi⟩ := hfin _ (g ∘ (Fintype.equivFin α).symm)
    exact ⟨i, fun a => by simpa using hi (Fintype.equivFin α a)⟩
  rw [Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top]
  refine ⟨?_, ?_⟩
  ·
    rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
    intro I hI
    obtain ⟨S, hS⟩ := hI
    let g : ↥S → ↥K := fun s => s.1
    have hgI : ∀ s : ↥S, g s ∈ I := fun s => hS ▸ Ideal.subset_span s.2
    obtain ⟨i, hi⟩ := hfin' g
    haveI := hff i

    have hsurj : ∀ z : ↥I ⊗[↥K] H, ∃ h : ↥S → H, z = ∑ s, (⟨g s, hgI s⟩ : ↥I) ⊗ₜ[↥K] h s := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp⟩
      | tmul m h =>
          have hm : (m : ↥K) ∈ Submodule.span ↥K (Set.range g) := by
            have hr : Set.range g = (↑S : Set ↥K) := by
              ext x; constructor
              · rintro ⟨s, rfl⟩; exact s.2
              · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
            rw [hr]
            show (m : ↥K) ∈ Ideal.span (↑S : Set ↥K)
            rw [hS]; exact m.2
          obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ↥K).mp hm
          refine ⟨fun s => c s • h, ?_⟩
          have hm' : m = ∑ s, c s • (⟨g s, hgI s⟩ : ↥I) := by
            apply Subtype.ext
            rw [← hc]
            simp
          rw [hm', TensorProduct.sum_tmul]
          exact Finset.sum_congr rfl fun s _ => by rw [TensorProduct.smul_tmul]
      | add z₁ z₂ h₁ h₂ =>
          obtain ⟨f₁, rfl⟩ := h₁
          obtain ⟨f₂, rfl⟩ := h₂
          refine ⟨f₁ + f₂, ?_⟩
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun s _ => by rw [Pi.add_apply, TensorProduct.tmul_add]
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨h, rfl⟩ := hsurj z

    have hrel : ∑ s, ((g s : ↥K) : H) * h s = 0 := by
      rw [map_sum] at hz
      simp [TensorProduct.lift.tmul] at hz
      exact hz

    let g' : ↥S → ↥(F i) := fun s => ⟨(g s : H), hi s⟩
    let J : Ideal ↥(F i) := Ideal.span (Set.range g')
    have hJ : J.FG := ⟨Finset.univ.image g', by simp [J]⟩
    have hinjJ := Module.Flat.iff_lift_lsmul_comp_subtype_injective.mp
      (inferInstance : Module.Flat ↥(F i) H) hJ
    let z' : ↥J ⊗[↥(F i)] H := ∑ s, (⟨g' s, Ideal.subset_span ⟨s, rfl⟩⟩ : ↥J) ⊗ₜ[↥(F i)] h s
    have hz' : z' = 0 := by
      apply hinjJ
      rw [map_zero, map_sum]
      simp [TensorProduct.lift.tmul] at hrel
      exact hrel

    have hJI : ∀ j : ↥(F i), j ∈ J → (Subalgebra.inclusion (hle i) j) ∈ I := by
      intro j hj
      induction hj using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨s, rfl⟩ := hx
          have : Subalgebra.inclusion (hle i) (g' s) = g s := Subtype.ext rfl
          rw [this]; exact hgI s
      | zero => rw [map_zero]; exact I.zero_mem
      | add x y _ _ hx hy => rw [map_add]; exact I.add_mem hx hy
      | smul r x _ hx => rw [smul_eq_mul, map_mul]; exact I.mul_mem_left _ hx

    let θ₀ : ↥J →+ H →+ ↥I ⊗[↥K] H :=
      { toFun := fun j =>
          { toFun := fun x => (⟨Subalgebra.inclusion (hle i) (j : ↥(F i)), hJI _ j.2⟩ : ↥I) ⊗ₜ[↥K] x
            map_zero' := by simp
            map_add' := fun x y => by simp [TensorProduct.tmul_add] }
        map_zero' := by
          ext x
          simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.zero_apply]
          have : (⟨Subalgebra.inclusion (hle i) ((0 : ↥J) : ↥(F i)), hJI _ (0 : ↥J).2⟩ : ↥I) = 0 :=
            Subtype.ext (map_zero _)
          rw [this, TensorProduct.zero_tmul]
        map_add' := fun j j' => by
          ext x
          simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.add_apply, ← TensorProduct.add_tmul]
          congr 1 }
    let θ : ↥J ⊗[↥(F i)] H →+ ↥I ⊗[↥K] H := TensorProduct.liftAddHom θ₀ (by
      intro r j x
      show (⟨Subalgebra.inclusion (hle i) ((r • j : ↥J) : ↥(F i)), _⟩ : ↥I) ⊗ₜ[↥K] x
        = (⟨Subalgebra.inclusion (hle i) (j : ↥(F i)), _⟩ : ↥I) ⊗ₜ[↥K] (r • x)
      have e1 : (⟨Subalgebra.inclusion (hle i) ((r • j : ↥J) : ↥(F i)), hJI _ (r • j).2⟩ : ↥I)
          = (Subalgebra.inclusion (hle i) r) • (⟨Subalgebra.inclusion (hle i) (j : ↥(F i)), hJI _ j.2⟩ : ↥I) := by
        apply Subtype.ext
        show Subalgebra.inclusion (hle i) (r * (j : ↥(F i))) = Subalgebra.inclusion (hle i) r * _
        exact map_mul _ _ _
      rw [e1, TensorProduct.smul_tmul]
      rfl)
    have hθ : ∀ s, θ ((⟨g' s, Ideal.subset_span ⟨s, rfl⟩⟩ : ↥J) ⊗ₜ[↥(F i)] h s)
        = (⟨g s, hgI s⟩ : ↥I) ⊗ₜ[↥K] h s := by
      intro s
      rw [TensorProduct.liftAddHom_tmul]
      show (⟨Subalgebra.inclusion (hle i) (g' s), _⟩ : ↥I) ⊗ₜ[↥K] h s = _
      congr 1
    calc (∑ s, (⟨g s, hgI s⟩ : ↥I) ⊗ₜ[↥K] h s) = θ z' := by
          rw [map_sum]; exact Finset.sum_congr rfl fun s _ => (hθ s).symm
      _ = 0 := by rw [hz', map_zero]
  ·
    intro I hI1
    have h1 : (1 : H) ∈ I.map (algebraMap ↥K H) := by
      have : (1 : H) ∈ I • (⊤ : Submodule ↥K H) := by rw [hI1]; exact Submodule.mem_top
      rw [Ideal.smul_top_eq_map] at this
      exact this

    obtain ⟨n, x, m₀, hsum⟩ := Submodule.mem_span_set'.mp h1
    have hm₀ : ∀ t, ∃ m ∈ I, (m₀ t : H) = algebraMap ↥K H m := fun t => by
      obtain ⟨m, hm, hmt⟩ := (m₀ t).2
      exact ⟨m, hm, hmt.symm⟩
    choose m hmI hm using hm₀
    obtain ⟨i, hi⟩ := hfin n m
    haveI := hff i
    let m' : Fin n → ↥(F i) := fun t => ⟨(m t : H), hi t⟩
    let J : Ideal ↥(F i) := Ideal.span (Set.range m')

    have hJ1 : J • (⊤ : Submodule ↥(F i) H) = ⊤ := by
      rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff, Ideal.eq_top_iff_one, ← hsum]
      refine Ideal.sum_mem _ fun t _ => ?_
      rw [smul_eq_mul]
      refine Ideal.mul_mem_left _ _ ?_
      rw [hm t]
      have : algebraMap ↥K H (m t) = algebraMap ↥(F i) H (m' t) := rfl
      rw [this]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨t, rfl⟩)
    have hJ : J = ⊤ := ((Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top _ _).mp (hff i)).2 J hJ1

    have h1J : (1 : ↥(F i)) ∈ J := by rw [hJ]; trivial
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp h1J
    rw [Ideal.eq_top_iff_one]
    have : (1 : ↥K) = ∑ t, Subalgebra.inclusion (hle i) (c t) * m t := by
      apply Subtype.ext
      have := congrArg (fun y : ↥(F i) => (y : H)) hc
      simp only [Subalgebra.coe_one] at this
      rw [Subalgebra.coe_one, ← this]
      simp [m']
    rw [this]
    exact I.sum_mem fun t _ => I.mul_mem_left _ (hmI t)

end S_Subalgebra_faithfullyFlat_of_directed_of_forall_faithfullyFlat
end P2MW
export P2MW.S_Subalgebra_faithfullyFlat_of_directed_of_forall_faithfullyFlat (solution)
