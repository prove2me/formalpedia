-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.quotientMap_bijective_of_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:27:28.326812+00:00
-- url     : https://prove2.me/submissions/bd673ec5-34da-4374-9479-b0f7db5e3c65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCurveAlg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_one_sub_pow_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (h : A) (K : Ideal A) (hK : h - 1 ∈ K)
    (hB : ∀ b : B, ∃ m : ℕ, ∃ a : A, algebraMap A B (h ^ m) * b = algebraMap A B a)
    (hinj : Function.Injective (algebraMap A B)) :
    Function.Bijective (Ideal.quotientMap (K.map (algebraMap A B)) (algebraMap A B)
      Ideal.le_comap_map) := by

  have key : ∀ x ∈ K.map (algebraMap A B), ∃ M : ℕ, ∃ k ∈ K, algebraMap A B (h ^ M) * x = algebraMap A B k := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      exact ⟨0, k, hk, by simp⟩
    | zero => exact ⟨0, 0, K.zero_mem, by simp⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨M₁, k₁, hk₁, e₁⟩ := ihx
      obtain ⟨M₂, k₂, hk₂, e₂⟩ := ihy
      refine ⟨M₁ + M₂, h ^ M₂ * k₁ + h ^ M₁ * k₂,
        K.add_mem (K.mul_mem_left _ hk₁) (K.mul_mem_left _ hk₂), ?_⟩
      rw [map_add, map_mul, map_mul, ← e₁, ← e₂, pow_add, map_mul]
      ring
    | smul b x _ ih =>
      obtain ⟨M, k, hk, e⟩ := ih
      obtain ⟨m, a, hb⟩ := hB b
      refine ⟨M + m, a * k, K.mul_mem_left _ hk, ?_⟩
      rw [smul_eq_mul, map_mul, ← hb, ← e, pow_add, map_mul]
      ring
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at hz
    rw [Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨M, k, hk, e⟩ := key _ hz
    rw [← map_mul] at e
    have hM : h ^ M * a ∈ K := hinj e ▸ hk
    have h1 : (1 - h ^ M) * a ∈ K := K.mul_mem_right _ (one_sub_pow_mem h K hK M)
    have : a = h ^ M * a + (1 - h ^ M) * a := by ring
    rw [this]; exact K.add_mem hM h1
  · intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨m, a, hb⟩ := hB b
    refine ⟨Ideal.Quotient.mk K a, ?_⟩
    rw [Ideal.quotientMap_mk, ← hb, Ideal.Quotient.eq]
    have hmem : algebraMap A B (1 - h ^ m) ∈ K.map (algebraMap A B) :=
      Ideal.mem_map_of_mem _ (one_sub_pow_mem h K hK m)
    have : algebraMap A B (h ^ m) * b - b = -(algebraMap A B (1 - h ^ m) * b) := by
      rw [map_sub, map_one]; ring
    rw [this]
    exact Submodule.neg_mem _ (Ideal.mul_mem_right _ _ hmem)
end ReciprocityTheory.ChartRestriction.G.I2
