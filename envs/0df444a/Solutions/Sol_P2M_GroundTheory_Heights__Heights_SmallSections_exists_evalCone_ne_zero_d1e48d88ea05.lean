-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SmallSections_exists_evalCone_ne_zero_d1e48d88ea05
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:55.853204+00:00
-- url     : https://prove2.me/submissions/0f7520af-420d-445c-b3b8-af58b5fad1fb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousAeval
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_mkF_X_ne_zero_5ca902d68882
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_isLive_of_mem_points_f34985632ea7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_exists_mul_pow_eq_mkF_840b0bae13e0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_chartMonomial_fd0871b69c38


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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SmallSections
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.SmallSections
theorem _root_.solution {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ} (hg : D.IsFormSystem d g)
    {z : Cone n ℂ} (hz : z ∈ P.points ℂ) {c : (k : ι) → Fin (n k + 1)} (hzc : ∀ k, z k (c k) ≠ 0) :
    ∃ j, evalCone z (g c j) ≠ 0 := by
  have hc : P.IsLive c := isLive_of_mem_points hz hzc
  by_contra hall
  simp only [not_exists, not_not] at hall
  obtain ⟨u, hu, hsum⟩ := D.generating c hc
  have hex : ∀ j, ∃ (N : ℕ) (E : MvPolynomial (Coord n) ℤ),
      u j * P.mkF (chartMonomial c 1) ^ N = P.mkF E := fun j ↦ exists_mul_pow_eq_mkF hc (hu j)
  choose N E hE using hex
  obtain ⟨S, hSdef⟩ : ∃ S, S = ∑ j, N j := ⟨_, rfl⟩
  have hcp : P.chartPow c D.deg ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (mkF_X_ne_zero hc k)
  have hxu : ∑ j, u j * D.elt j = P.chartPow c D.deg := by
    have h := congrArg (· * P.chartPow c D.deg) hsum
    simp only [Finset.sum_mul, one_mul] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [mul_assoc, div_mul_cancel₀ _ hcp]
  let R : MvPolynomial (Coord n) ℤ := ∏ k, X ⟨k, c k⟩ ^ ((d k : ℤ) + D.deg k).toNat
  have hR : P.mkF R = P.mkF (chartMonomial c d) * P.chartPow c D.deg := by
    simp only [R, chartMonomial, ArithVariety.chartPow, map_prod, map_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [← zpow_natCast, Int.toNat_of_nonneg (hg.nonneg k), zpow_add₀ (mkF_X_ne_zero hc k), zpow_natCast]
  have hterm : ∀ j, P.mkF (E j * chartMonomial c 1 ^ (S - N j) * g c j) =
      P.mkF (chartMonomial c 1) ^ S * P.mkF (chartMonomial c d) * (u j * D.elt j) := by
    intro j
    have hS : N j ≤ S := hSdef ▸ Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    rw [map_mul, map_mul, map_pow, ← hE j, hg.value c hc j]
    conv_rhs => rw [← Nat.add_sub_cancel' hS, pow_add]
    ring
  have hmem : chartMonomial c 1 ^ S * R - ∑ j, E j * chartMonomial c 1 ^ (S - N j) * g c j ∈ P.ideal := by
    rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_pow, hR, map_sum]
    simp only [hterm]
    rw [← Finset.mul_sum, hxu]
    ring
  have h0 := hz.2 _ hmem
  have hall' : ∀ j, eval₂ (Int.castRingHom ℂ) (fun v : Coord n ↦ z v.1 v.2) (g c j) = 0 := hall
  simp only [evalCone, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_sum, hall', mul_zero,
    Finset.sum_const_zero, sub_zero] at h0
  have hM : evalCone z (chartMonomial c 1) ≠ 0 := by
    rw [evalCone_chartMonomial]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hzc k)
  have hRz : evalCone z R ≠ 0 := by
    simp only [R, evalCone, eval₂_prod, eval₂_pow, eval₂_X]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hzc k)
  exact mul_ne_zero (pow_ne_zero S hM) hRz h0
end GroundTheory.Heights₂.Heights.SmallSections
