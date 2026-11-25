-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.gauss_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:36:20.15192+00:00
-- url     : https://prove2.me/submissions/5ec983a7-f403-48df-a190-922b3c173cb0

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValExists
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_unit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.MultiplicativeHeights
open MvPolynomial
private theorem gaussValuation_of_mem_valuationSubring {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (t : σ → U) (V : ValuationSubring U) (ht : ∀ s, t s ∈ V)
    (hind : letI := residueAlgebra V (algebraMap Ω U)
      AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
        (fun s => IsLocalRing.residue V ⟨t s, ht s⟩))
    (p : MvPolynomial σ Ω) (hp : p ≠ 0) :
    ∃ α₀ ∈ p.support, (∀ α ∈ p.support, V.valuation (algebraMap Ω U (p.coeff α)) ≤
        V.valuation (algebraMap Ω U (p.coeff α₀))) ∧
      V.valuation (aeval t p) = V.valuation (algebraMap Ω U (p.coeff α₀)) := by
  have hne : p.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.2 fun h => hp (MvPolynomial.support_eq_empty.1 h)
  obtain ⟨α₀, hα₀, hmax⟩ := Finset.exists_max_image p.support
    (fun α => V.valuation (algebraMap Ω U (p.coeff α))) hne
  refine ⟨α₀, hα₀, hmax, ?_⟩
  have hc0 : p.coeff α₀ ≠ 0 := MvPolynomial.mem_support_iff.1 hα₀
  have hv0 : V.valuation (algebraMap Ω U (p.coeff α₀)) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]
    exact (map_ne_zero _).2 hc0
  obtain ⟨q, hqdef⟩ : ∃ q : MvPolynomial σ Ω, q = MvPolynomial.C (p.coeff α₀)⁻¹ * p := ⟨_, rfl⟩
  have hqcoeff : ∀ α, q.coeff α = (p.coeff α₀)⁻¹ * p.coeff α := by
    intro α
    rw [hqdef]
    exact MvPolynomial.coeff_C_mul _ _ _
  have hqc : ∀ α, q.coeff α ∈ V.comap (algebraMap Ω U) := by
    intro α
    rw [hqcoeff, ValuationSubring.mem_comap]
    apply (V.valuation_le_one_iff _).1
    simp only [map_mul, map_inv₀]
    by_cases hα : α ∈ p.support
    · have hle : V.valuation (algebraMap Ω U (p.coeff α)) ≤
          V.valuation (algebraMap Ω U (p.coeff α₀)) := hmax α hα
      calc (V.valuation (algebraMap Ω U (p.coeff α₀)))⁻¹ * V.valuation (algebraMap Ω U (p.coeff α))
          ≤ (V.valuation (algebraMap Ω U (p.coeff α₀)))⁻¹ *
              V.valuation (algebraMap Ω U (p.coeff α₀)) := by
            exact mul_le_mul_of_nonneg_left hle zero_le'
        _ = 1 := inv_mul_cancel₀ hv0
    · have h0 : p.coeff α = 0 := by simpa [MvPolynomial.mem_support_iff] using hα
      rw [h0]
      simp
  have hα₀' : (q.coeff α₀)⁻¹ ∈ V.comap (algebraMap Ω U) := by
    rw [hqcoeff, inv_mul_cancel₀ hc0, inv_one]
    exact one_mem _
  have h0' : q.coeff α₀ ≠ 0 := by
    rw [hqcoeff, inv_mul_cancel₀ hc0]
    exact one_ne_zero
  have h1 := gauss_unit t V ht hind q hqc α₀ hα₀' h0'
  have hq : aeval t q = algebraMap Ω U (p.coeff α₀)⁻¹ * aeval t p := by
    rw [hqdef, map_mul, MvPolynomial.aeval_C]
  rw [hq] at h1
  simp only [map_mul, map_inv₀] at h1
  calc V.valuation (aeval t p)
      = V.valuation (algebraMap Ω U (p.coeff α₀)) *
          ((V.valuation (algebraMap Ω U (p.coeff α₀)))⁻¹ * V.valuation (aeval t p)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hv0, one_mul]
    _ = V.valuation (algebraMap Ω U (p.coeff α₀)) := by rw [h1, mul_one]
end ReciprocityTheory.MultiplicativeHeights
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (t : σ → U) (V : ValuationSubring U) (ht : ∀ s, t s ∈ V)
    (hind : letI := residueAlgebra V (algebraMap Ω U)
      AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
        (fun s => IsLocalRing.residue V ⟨t s, ht s⟩))
    (p : MvPolynomial σ Ω) :
    V.valuation (aeval t p) = p.support.sup fun α => V.valuation (algebraMap Ω U (p.coeff α)) := by
  by_cases hp : p = 0
  · subst hp
    rw [map_zero, MvPolynomial.support_zero, Finset.sup_empty]
    exact V.valuation.map_zero
  · obtain ⟨α₀, hα₀, hmax, hv⟩ := gaussValuation_of_mem_valuationSubring t V ht hind p hp
    rw [hv]
    exact le_antisymm
      (Finset.le_sup (f := fun α => V.valuation (algebraMap Ω U (p.coeff α))) hα₀)
      (Finset.sup_le hmax)
end ReciprocityTheory.MultiplicativeHeights
