-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointLine_proof_60a02c7c6efe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:07:01.862554+00:00
-- url     : https://prove2.me/submissions/a1690792-28b7-44e5-a8a5-bffb60638f3e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointLine_exists_ne_zero_98697fadef41
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointLine_smul_mem_zeroSet_ab37cf5939d2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointLine_pairing_dvd_of_vanish_9f2009f89a61
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointLine_irreducible_pairing_1c55fbb0a974
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointLine_eq_smul_of_associated_bbcd2cbe6ce3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointLine_chowForm_vanish_aa54c6828c1b

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
open PointLine
namespace GroundTheory.Heights₂.Heights
namespace PointLine
theorem _root_.solution : PointLine.Statement := by
  classical
  intro n W g hW hg
  have := hW.isPrime
  set V : Set (Fin n → ℂ) := {x | ∀ q ∈ W, eval x q = 0} with hV
  have hNS : ∀ q, q ∈ W ↔ ∀ x ∈ V, eval x q = 0 := by
    intro q
    rw [← SetLike.ext_iff.mp (MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := ℂ) W) q,
      mem_vanishingIdeal_iff]
    have hae : ∀ (x : Fin n → ℂ) (p : MvPolynomial (Fin n) ℂ), aeval x p = eval x p := fun _ _ => rfl
    simp only [mem_zeroLocus_iff, hae, hV, Set.mem_ofPred_eq]
  have hcone : ∀ x ∈ V, ∀ t : ℂ, t • x ∈ V := fun x hx t => smul_mem_zeroSet hW.isHomog hx t
  have hdvd : ∀ x ∈ V, x ≠ 0 → pairing x ∣ g := fun x hx hx0 =>
    pairing_dvd_of_vanish hx0 g (chowForm_vanish hg hx0 hx)
  have hrel : ∀ S : Set (Fin n → ℂ), vanishingIdeal ℂ S ≤ W → ∃ y ∈ S, y ≠ 0 := by
    intro S hS
    by_contra h
    push Not at h
    obtain ⟨j, hj⟩ := hW.isRelevant
    refine hj (hS ?_)
    rw [mem_vanishingIdeal_iff]
    intro x hx
    simp [h x hx]
  obtain ⟨y₀, hy₀, hy₀0⟩ := hrel V (fun q hq => (hNS q).mpr fun x hx => by
    simpa using (mem_vanishingIdeal_iff.mp hq) x hx)
  let T := (UniqueFactorizationMonoid.factors g).toFinset
  let S : MvPolynomial (Fin 1 × Fin n) ℂ → Set (Fin n → ℂ) :=
    fun p => {x | x ∈ V ∧ (x = 0 ∨ Associated (pairing x) p)}
  have hcover : ∏ p ∈ T, vanishingIdeal ℂ (S p) ≤ W := by
    intro q hq
    rw [hNS]
    intro x hx
    obtain ⟨p, hpT, hxp⟩ : ∃ p ∈ T, x ∈ S p := by
      by_cases hx0 : x = 0
      · obtain ⟨p, hp, -⟩ := UniqueFactorizationMonoid.exists_mem_factors_of_dvd hg.1
          (irreducible_pairing hy₀0) (hdvd y₀ hy₀ hy₀0)
        exact ⟨p, Multiset.mem_toFinset.mpr hp, hx, Or.inl hx0⟩
      · obtain ⟨p, hp, hxp⟩ := UniqueFactorizationMonoid.exists_mem_factors_of_dvd hg.1
          (irreducible_pairing hx0) (hdvd x hx hx0)
        exact ⟨p, Multiset.mem_toFinset.mpr hp, hx, Or.inr hxp⟩
    have hq' : q ∈ vanishingIdeal ℂ (S p) := (Ideal.prod_le_inf.trans (Finset.inf_le hpT)) hq
    simpa using (mem_vanishingIdeal_iff.mp hq') x hxp
  obtain ⟨p, -, hpW⟩ := (Ideal.IsPrime.prod_le hW.isPrime).mp hcover
  obtain ⟨y, ⟨hyV, hyp⟩, hy0⟩ := hrel (S p) hpW
  have hyp' : Associated (pairing y) p := hyp.resolve_left hy0
  have hline : ∀ q, q ∈ W ↔ ∀ t : ℂ, eval (t • y) q = 0 := by
    intro q
    refine ⟨fun hq t => hcone y hyV t q hq, fun hq => hpW ?_⟩
    rw [mem_vanishingIdeal_iff]
    rintro x ⟨-, hx⟩
    rcases hx with rfl | hx
    · simpa using hq 0
    · obtain ⟨t, rfl⟩ := eq_smul_of_associated (hyp'.trans hx.symm)
      simpa using hq t
  refine ⟨y, hy0, fun x => ⟨fun hx => ?_, ?_⟩, hline⟩
  · obtain ⟨a, ha⟩ := exists_ne_zero hy0
    refine ⟨x a / y a, funext fun b => ?_⟩
    have hmem : C (y a) * X b - C (y b) * X a ∈ W := (hline _).mpr fun t => by
      simp only [map_sub, map_mul, eval_C, eval_X, Pi.smul_apply, smul_eq_mul]
      ring
    have h := hx _ hmem
    simp only [map_sub, map_mul, eval_C, eval_X] at h
    rw [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination h
  · rintro ⟨t, rfl⟩
    exact hcone y hyV t
end PointLine
end GroundTheory.Heights₂.Heights
