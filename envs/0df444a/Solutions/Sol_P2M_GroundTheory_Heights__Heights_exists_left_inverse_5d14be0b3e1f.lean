-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_left_inverse_5d14be0b3e1f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:31:58.31258+00:00
-- url     : https://prove2.me/submissions/e25f0566-88fc-40e1-bd89-e357c6e65dce

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_int_comb_c953859cc094
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sum_single_mul_a1dd377cfae2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sum_latticePoint_978f926e6c9b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable {r N : ℕ}
open Classical
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {F : HermLattice K (r + 1)} {φ : Fin (N + 1) → Fin (r + 1) → K}
    (hφ : IsDualBasis F.lattice φ) (σ : K →+* ℂ) (j₀ : Fin (r + 1)) :
    ∃ R : Fin (N + 1) → ℂ, ∀ (τ : K →+* ℂ) (j : Fin (r + 1)),
      ∑ b, R b * τ (φ b j) = if τ = σ ∧ j = j₀ then 1 else 0 := by
  let row : Fin (N + 1) → ((K →+* ℂ) × Fin (r + 1)) → ℂ := fun b p ↦ p.1 (φ b p.2)
  have htop : Submodule.span ℂ (Set.range row) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hle⟩ :=
      (Submodule.span ℂ (Set.range row)).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hne)
    apply hf0
    have hrow : ∀ b, f (row b) = 0 := fun b ↦ hle (Submodule.subset_span ⟨b, rfl⟩)
    let g : (K →+* ℂ) × Fin (r + 1) → ℂ := fun p ↦ f (Pi.single p 1)
    have hf : ∀ x, f x = ∑ p, g p * x p := by
      intro x
      conv_lhs => rw [← Finset.univ_sum_single x]
      rw [map_sum]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [show (Pi.single p (x p) : (K →+* ℂ) × Fin (r + 1) → ℂ) =
          x p • Pi.single p (1 : ℂ) by
        funext q; by_cases hq : q = p <;> simp [hq],
        map_smul, smul_eq_mul, mul_comm]
    have hzero : ∀ b, ∑ τ : K →+* ℂ, latticePoint φ τ (fun j ↦ g (τ, j)) () b = 0 := by
      intro b
      rw [← hrow b, hf, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun τ _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [row]
      ring
    have hv : ∀ v : Fin (r + 1) → K, ∑ τ : K →+* ℂ, ∑ j, τ (v j) * g (τ, j) = 0 := by
      intro v
      obtain ⟨D, hD, c, hc⟩ := exists_int_comb hφ v
      have h1 : ∑ b, (c b : ℂ) * ∑ τ : K →+* ℂ, latticePoint φ τ (fun j ↦ g (τ, j)) () b =
          D * ∑ τ : K →+* ℂ, ∑ j, τ (v j) * g (τ, j) := by
        calc ∑ b, (c b : ℂ) * ∑ τ : K →+* ℂ, latticePoint φ τ (fun j ↦ g (τ, j)) () b
            = ∑ τ : K →+* ℂ, ∑ b, (c b : ℂ) * latticePoint φ τ (fun j ↦ g (τ, j)) () b := by
              simp_rw [Finset.mul_sum]
              exact Finset.sum_comm
          _ = ∑ τ : K →+* ℂ, (D : ℂ) * ∑ j, τ (v j) * g (τ, j) :=
              Finset.sum_congr rfl fun τ _ ↦ sum_latticePoint τ _ hc
          _ = _ := (Finset.mul_sum _ _ _).symm
      simp only [hzero, mul_zero, Finset.sum_const_zero] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_left (Int.cast_ne_zero.mpr hD)
    have hind : LinearIndependent ℂ (fun τ : K →+* ℂ ↦ ((τ : K →* ℂ) : K → ℂ)) :=
      (linearIndependent_monoidHom K ℂ).comp (fun τ : K →+* ℂ ↦ (τ : K →* ℂ))
        (fun τ τ' h ↦ RingHom.ext fun a ↦ DFunLike.congr_fun h a)
    have hg : ∀ p, g p = 0 := by
      rintro ⟨τ, j⟩
      refine Fintype.linearIndependent_iff.mp hind (fun τ ↦ g (τ, j)) ?_ τ
      funext a
      have h := hv (Pi.single j a)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← h]
      refine Finset.sum_congr rfl fun τ _ ↦ ?_
      rw [sum_single_mul τ (fun j ↦ g (τ, j)) j a, mul_comm]
      rfl
    refine LinearMap.ext fun x ↦ ?_
    rw [hf]
    simp [hg]
  have hmem : (Pi.single (σ, j₀) 1 : (K →+* ℂ) × Fin (r + 1) → ℂ) ∈ Submodule.span ℂ (Set.range row) :=
    htop ▸ Submodule.mem_top
  obtain ⟨R, hR⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  refine ⟨R, fun τ j ↦ ?_⟩
  have h := congrFun hR (τ, j)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, row] at h
  rw [h, Pi.single_apply]
  exact if_congr (Iff.of_eq (Prod.mk.injEq _ _ _ _)) rfl rfl
end GroundTheory.Heights₂.Heights
