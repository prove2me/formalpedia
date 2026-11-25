-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockTrdeg_algebraicIndependent_forgotten_1e622b88ee59
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:45:34.647415+00:00
-- url     : https://prove2.me/submissions/02b58495-92bb-4c57-a1a1-201277d018d0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsBlockTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PBlockTrdeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockTrdeg_exists_nat_mul_mem_range_finset_287ad278de3d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockTrdeg_isHomogeneous_forgetWeight_72c1617be2ea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockTrdeg_isWeightedHomogeneous_rename_3526478ad33d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockTrdeg_isWeightedHomogeneous_forgetMonomial_49694bee7116

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 Algebra Cardinal
open GroundTheory.Heights₂.Heights.BlockTrdeg
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open scoped Classical
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}
  {L : Type} [Field L] [Algebra ℚ L] {φ : MRing ι' →+* L}
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.BlockTrdeg
theorem _root_.solution (hv : ∀ p, (v p).1 = κ p.1) (hP : IsMultiHomogIdeal P')
    (hprime : P'.IsPrime) (hker : RingHom.ker φ = P') (i : ∀ k : Forgotten κ, ι' k.1)
    (hi : ∀ k, (X ⟨k.1, i k⟩ : MRing ι') ∉ P') (S : Subalgebra ℚ L)
    (hS : S ≤ adjoin ℚ (Set.range fun p : Σ k, ι k ↦ φ (X (v p)))) :
    AlgebraicIndependent S (fun k : Forgotten κ ↦ φ (X ⟨k.1, i k⟩)) := by
  rw [algebraicIndependent_iff]
  intro p hp
  set ψ : MvPolynomial (Σ k, ι k) ℤ →+* L := φ.comp (rename v).toRingHom with hψ
  have hA : adjoin ℚ (Set.range fun p : Σ k, ι k ↦ φ (X (v p))) = adjoin ℚ (Set.range fun p ↦ ψ (X p)) := by
    simp [ψ]
  obtain ⟨N, hN, hNs⟩ := exists_nat_mul_mem_range_finset ψ (p.support.image fun a ↦ ((coeff a p : S) : L)) (by
    intro y hy
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hy
    rw [← hA]
    exact hS (coeff a p).2)
  choose g hg using fun a : p.support ↦ RingHom.mem_range.mp (hNs _ (Finset.mem_image_of_mem _ a.2))
  set H : MRing ι' := ∑ a : p.support, rename v (g a) * forgetMonomial κ i a.1 with hHdef
  have hH : H ∈ P' := by
    rw [← hker, RingHom.mem_ker]
    have e1 : φ H = (N : L) * aeval (fun k : Forgotten κ ↦ φ (X ⟨k.1, i k⟩)) p := by
      rw [hHdef, map_sum, aeval_def, eval₂_eq', Finset.mul_sum, ← Finset.sum_coe_sort p.support]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [map_mul, show φ (rename v (g a)) = ψ (g a) from rfl, hg a, forgetMonomial, map_prod]
      simp only [map_pow, mul_assoc]
      rfl
    rw [e1, hp, mul_zero]
  refine MvPolynomial.ext _ _ fun a ↦ ?_
  rw [coeff_zero]
  by_cases ha : a ∈ p.support
  swap
  · exact notMem_support_iff.mp ha
  have hhom : ∀ b : p.support, IsWeightedHomogeneous (forgetWeight κ)
      (rename v (g b) * forgetMonomial κ i b.1) ⇑b.1 := by
    intro b
    have := (isWeightedHomogeneous_rename κ (fun p ↦ ⟨p.1, (hv p).symm⟩) (g b)).mul
      (isWeightedHomogeneous_forgetMonomial κ i b.1)
    rwa [zero_add] at this
  have hcomp := weightedHomogeneousComponent_mem_of_mem ℤ (forgetWeight κ)
    (isHomogeneous_forgetWeight κ hP) hH (⇑a)
  have e2 : weightedHomogeneousComponent (forgetWeight κ) (⇑a) H =
      rename v (g ⟨a, ha⟩) * forgetMonomial κ i a := by
    rw [hHdef, map_sum, Finset.sum_eq_single ⟨a, ha⟩]
    · exact (hhom ⟨a, ha⟩).weightedHomogeneousComponent_same
    · intro b _ hb
      exact (hhom b).weightedHomogeneousComponent_ne _
        (fun h ↦ hb (Subtype.ext (DFunLike.coe_injective h).symm))
    · simp
  rw [e2] at hcomp
  rcases hprime.mem_or_mem hcomp with h1 | h1
  · rw [← hker, RingHom.mem_ker] at h1
    have h2 : (N : L) * ((coeff a p : S) : L) = 0 := by
      rw [← hg ⟨a, ha⟩]
      exact h1
    have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
    have h3 := (mul_eq_zero.mp h2).resolve_left (Nat.cast_ne_zero.mpr hN)
    exact_mod_cast h3
  · exfalso
    have := hprime
    rw [forgetMonomial] at h1
    obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h1
    exact hi k (hprime.mem_of_pow_mem _ hk)
end GroundTheory.Heights₂.Heights.BlockTrdeg
