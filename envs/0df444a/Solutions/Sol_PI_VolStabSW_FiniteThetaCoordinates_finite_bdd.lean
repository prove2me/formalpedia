-- Prove2me | solution 1 for PI.VolStabSW.FiniteThetaCoordinates.finite_bdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:11:10.401602+00:00
-- url     : https://prove2.me/submissions/cabf724c-a5c7-4c6d-91ca-3b8e7bd5a0af

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FinTheta
import Theorems.Thm_PI_VolStabSW_FiniteThetaCoordinates_norm_emb_le_one_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.FiniteThetaCoordinates
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct
variable {F : Type} [Field F] [NumberField F]
namespace PI.VolStabSW.FiniteThetaCoordinates
theorem _root_.solution (S : Finset (HeightOneSpectrum (𝓞 F))) (C : HeightOneSpectrum (𝓞 F) → ℝ)
    (Ci : InfinitePlace F → ℝ) :
    {x : F | (∀ v, ‖FinitePlace.embedding v x‖ ≤ C v) ∧
      (∀ v ∉ S, ‖FinitePlace.embedding v x‖ ≤ 1) ∧ ∀ w : InfinitePlace F, w x ≤ Ci w}.Finite := by
  classical
  set N : ℕ := ∏ v ∈ S, Ideal.absNorm v.asIdeal with hN
  have hNint : ∀ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v (N : F)‖ ≤ 1 := by
    intro v
    have := FinitePlace.norm_le_one F v (N : 𝓞 F)
    simpa using this
  have hNlt : ∀ v ∈ S, ‖FinitePlace.embedding v (N : F)‖ < 1 := by
    intro v hv
    have hmem : (N : 𝓞 F) ∈ v.asIdeal := by
      rw [hN, ← Finset.mul_prod_erase S (fun v => Ideal.absNorm v.asIdeal) hv, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem v.asIdeal)
    have := (FinitePlace.norm_lt_one_iff_mem F v (N : 𝓞 F)).2 hmem
    simpa using this
  have hN0 : (N : F) ≠ 0 := by
    rw [Nat.cast_ne_zero, hN, Finset.prod_ne_zero_iff]
    intro v _
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have hk : ∀ v ∈ S, ∃ k : ℕ, ‖FinitePlace.embedding v (N : F)‖ ^ k * max (C v) 1 ≤ 1 := by
    intro v hv
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (one_div_pos.2 (lt_of_lt_of_le zero_lt_one
      (le_max_right (C v) 1))) (hNlt v hv)
    exact ⟨k, ((lt_div_iff₀ (lt_of_lt_of_le zero_lt_one (le_max_right (C v) 1))).1 hk).le⟩
  choose! kv hkv using hk
  set K := S.sup kv
  set D : F := (N : F) ^ K
  have hD0 : D ≠ 0 := pow_ne_zero _ hN0
  set Bi : ℝ := ∑ w : InfinitePlace F, w D * max (Ci w) 0
  refine ((Embeddings.finite_of_norm_le F ℂ Bi).preimage
    (mul_right_injective₀ hD0).injOn).subset ?_
  rintro x ⟨hC, hS, hI⟩
  refine ⟨?_, fun φ => ?_⟩
  · have hle : ∀ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v (D * x)‖ ≤ 1 := by
      intro v
      rw [map_mul, map_pow, norm_mul, norm_pow]
      by_cases hv : v ∈ S
      · calc ‖FinitePlace.embedding v (N : F)‖ ^ K * ‖FinitePlace.embedding v x‖
            ≤ ‖FinitePlace.embedding v (N : F)‖ ^ kv v * max (C v) 1 :=
              mul_le_mul (pow_le_pow_of_le_one (norm_nonneg _) (hNint v) (Finset.le_sup hv))
                ((hC v).trans (le_max_left _ _)) (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
          _ ≤ 1 := hkv v hv
      · exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (hNint v)) (norm_nonneg _) (hS v hv)
    obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F (D * x)
      (fun v => (norm_emb_le_one_iff v _).1 (hle v))
    show IsIntegral ℤ (D * x)
    rw [← hy]
    exact RingOfIntegers.isIntegral_coe y
  · rw [map_mul, norm_mul, ← InfinitePlace.apply, ← InfinitePlace.apply]
    calc InfinitePlace.mk φ D * InfinitePlace.mk φ x
        ≤ InfinitePlace.mk φ D * max (Ci (InfinitePlace.mk φ)) 0 :=
          mul_le_mul_of_nonneg_left ((hI _).trans (le_max_left _ _)) (apply_nonneg _ _)
      _ ≤ Bi := Finset.single_le_sum (f := fun w : InfinitePlace F => w D * max (Ci w) 0)
          (fun w _ => mul_nonneg (apply_nonneg _ _) (le_max_right _ _)) (Finset.mem_univ _)
end PI.VolStabSW.FiniteThetaCoordinates
