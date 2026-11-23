-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.lift_khw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:26.893626+00:00
-- url     : https://prove2.me/submissions/dbc70ac5-7d15-4482-9091-6918c44f815c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KUnitB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hU : IsKUnitary ε A) {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    {B : Fin n → Fin n → Module.End ℂ Y} (f : X →ₗ[ℂ] Y)
    (hf : ∀ a b, ε a = ε b → ∀ x, f (A a b x) = B a b (f x)) {S : Submodule ℂ X}
    (hfd : FiniteDimensional ℂ S) (hS : IsKStableSub ε A S) {x₀ : X} (hx₀ : x₀ ∈ S)
    {μ : Fin n → ℝ} (hy : IsKHWVec ε B μ (f x₀)) :
    ∃ x ∈ S, (∀ z ∈ S, f z = 0 → inner ℂ z x = 0) ∧ IsKHWVec ε A μ x ∧ f x = f x₀ := by
  classical
  haveI := hfd
  obtain ⟨K, hK⟩ : ∃ K : Submodule ℂ X, ∀ z, z ∈ K ↔ z ∈ S ∧ f z = 0 :=
    ⟨S ⊓ LinearMap.ker f, fun z => by simp⟩
  have hKS : K ≤ S := fun z hz => ((hK z).1 hz).1
  haveI : FiniteDimensional ℂ K := Submodule.finiteDimensional_of_le hKS
  obtain ⟨y, hyK, x, hxo, hsum⟩ := K.exists_add_mem_mem_orthogonal x₀
  have hyS := (hK y).1 hyK
  have hxS : x ∈ S := by
    have e : x = x₀ - y := by rw [hsum]; abel
    rw [e]
    exact S.sub_mem hx₀ hyS.1
  have hfx : f x = f x₀ := by
    rw [hsum, map_add, hyS.2, zero_add]
  have hperp : ∀ z ∈ K, inner ℂ z x = 0 := fun z hz => (Submodule.mem_orthogonal K x).1 hxo z hz
  have hKst : ∀ a b, ε a = ε b → ∀ z ∈ K, A a b z ∈ K := by
    intro a b hab z hz
    obtain ⟨hzS, hfz⟩ := (hK z).1 hz
    exact (hK _).2 ⟨hS a b hab z hzS, by rw [hf a b hab, hfz, map_zero]⟩
  have key : ∀ d, d ∈ S → f d = 0 → (∀ z ∈ K, inner ℂ z d = 0) → d = 0 := by
    intro d hdS hfd0 hdo
    exact inner_self_eq_zero.mp (hdo d ((hK d).2 ⟨hdS, hfd0⟩))
  refine ⟨x, hxS, fun z hz hfz => hperp z ((hK z).2 ⟨hz, hfz⟩),
    ⟨fun a => ?_, fun a b hab he => ?_⟩, hfx⟩
  · apply sub_eq_zero.mp
    apply key
    · exact S.sub_mem (hS a a rfl x hxS) (S.smul_mem _ hxS)
    · rw [map_sub, map_smul, hf a a rfl, hfx, hy.1 a, sub_self]
    · intro z hz
      rw [inner_sub_right, inner_smul_right, ← hU a a rfl, hperp _ (hKst a a rfl z hz),
        hperp z hz, mul_zero, sub_zero]
  · apply key
    · exact hS a b he x hxS
    · rw [hf a b he, hfx, hy.2 a b hab he]
    · intro z hz
      rw [← hU b a he.symm, hperp _ (hKst b a he.symm z hz)]
end ReciprocityTheory.ChartRestriction.DS
