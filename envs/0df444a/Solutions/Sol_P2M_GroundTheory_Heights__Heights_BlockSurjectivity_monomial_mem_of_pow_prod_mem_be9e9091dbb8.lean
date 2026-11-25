-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockSurjectivity_monomial_mem_of_pow_prod_mem_be9e9091dbb8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:36:35.846685+00:00
-- url     : https://prove2.me/submissions/dd7b470d-309e-4840-8c09-1f2a9c2d0b4c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousSepBlock
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_weight_coordDeg_apply_695929babdd5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_mem_offMonos_089e7d3164ba

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
open MvPolynomial Module
noncomputable section
open GroundTheory.Heights₂.Heights.BlockSurjectivity
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.BlockSurjectivity
theorem _root_.solution {J : Ideal (MvPolynomial (Coord n) ℂ)} {k₀ : ι} {N : ℕ}
    (hJN : ∀ c : (k : ι) → Fin (n k + 1),
      (∏ k ∈ Finset.univ.erase k₀, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℂ)) ^ N ∈ J) :
    ∀ μ ∈ offMonos n k₀ (Fintype.card (Coord n) * N), (monomial μ 1 : MvPolynomial (Coord n) ℂ) ∈ J := by
  classical
  intro μ hμ
  rw [mem_offMonos] at hμ
  have hbig : ∀ k, ∃ i : Fin (n k + 1), k ≠ k₀ → N ≤ μ ⟨k, i⟩ := by
    intro k
    by_cases hk : k = k₀
    · exact ⟨0, fun h ↦ (h hk).elim⟩
    · by_contra hcon
      push Not at hcon
      have hsum : ∑ i, μ ⟨k, i⟩ = Fintype.card (Coord n) * N := by
        rw [← weight_coordDeg_apply, hμ, offDeg, Function.update_of_ne hk]
      have hlt : ∑ i, μ ⟨k, i⟩ < ∑ _i : Fin (n k + 1), N :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ ↦ (hcon i).2
      have hcard : n k + 1 ≤ Fintype.card (Coord n) := by
        rw [Fintype.card_sigma]
        simp only [Fintype.card_fin]
        exact Finset.single_le_sum (f := fun k ↦ n k + 1) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ k)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlt
      rw [hsum] at hlt
      exact absurd hlt (not_lt.mpr (Nat.mul_le_mul_right N hcard))
  choose c hc using hbig
  have hinj : Set.InjOn (fun k ↦ (⟨k, c k⟩ : Coord n)) (Finset.univ.erase k₀) :=
    fun a _ b _ h ↦ congrArg Sigma.fst h
  have hdvd : (∏ k ∈ Finset.univ.erase k₀, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℂ)) ^ N ∣
      monomial μ 1 := by
    rw [← Finset.prod_pow]
    calc ∏ k ∈ Finset.univ.erase k₀, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℂ) ^ N
        ∣ ∏ k ∈ Finset.univ.erase k₀, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℂ) ^ μ ⟨k, c k⟩ :=
          Finset.prod_dvd_prod_of_dvd _ _ fun k hk ↦
            pow_dvd_pow _ (hc k (Finset.ne_of_mem_erase hk))
      _ = ∏ v ∈ (Finset.univ.erase k₀).image (fun k ↦ (⟨k, c k⟩ : Coord n)),
            (X v : MvPolynomial (Coord n) ℂ) ^ μ v := by
          rw [Finset.prod_image hinj]
      _ ∣ ∏ v, (X v : MvPolynomial (Coord n) ℂ) ^ μ v :=
          Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)
      _ = monomial μ 1 := by
          rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  obtain ⟨r, hr⟩ := hdvd
  rw [hr]
  exact J.mul_mem_right _ (hJN c)
end GroundTheory.Heights₂.Heights.BlockSurjectivity
