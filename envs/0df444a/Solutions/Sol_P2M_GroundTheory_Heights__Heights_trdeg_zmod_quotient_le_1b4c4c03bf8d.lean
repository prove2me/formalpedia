-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_trdeg_zmod_quotient_le_1b4c4c03bf8d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:40:40.507796+00:00
-- url     : https://prove2.me/submissions/e71574fd-f085-4716-8645-bb14292ecca8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IntDimTrdeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Algebra Cardinal MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {B : Type} [CommRing B] [IsDomain B] [Algebra ℤ B]
    (hinj : Function.Injective (algebraMap ℤ B)) (p : ℕ) [Fact p.Prime] (Q : Ideal B) [Q.IsPrime]
    [CharP (B ⧸ Q) p] :
    letI := ZMod.algebra (B ⧸ Q) p
    trdeg (ZMod p) (B ⧸ Q) ≤ trdeg ℤ B := by
  let := ZMod.algebra (B ⧸ Q) p
  have : FaithfulSMul (ZMod p) (B ⧸ Q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap (ZMod p) (B ⧸ Q)).injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis (ZMod p) (B ⧸ Q)
  rw [← hs.cardinalMk_eq_trdeg]
  let y : s → B := fun i => Function.surjInv Ideal.Quotient.mk_surjective (i : B ⧸ Q)
  have hy : (fun i => Ideal.Quotient.mkₐ ℤ Q (y i)) = ((↑) : s → B ⧸ Q) :=
    funext fun i => Function.surjInv_eq Ideal.Quotient.mk_surjective _
  have hp0 : (p : B) ≠ 0 := by
    intro h
    have : algebraMap ℤ B (p : ℤ) = algebraMap ℤ B 0 := by simpa using h
    exact (Nat.Prime.ne_zero (Fact.out : p.Prime)) (by exact_mod_cast hinj this)

  have hred : ∀ P : MvPolynomial s ℤ, aeval y P = 0 →
      MvPolynomial.map (algebraMap ℤ (ZMod p)) P = 0 := by
    intro P hP
    apply hs.1
    have hc : (algebraMap (ZMod p) (B ⧸ Q)).comp (algebraMap ℤ (ZMod p)) = algebraMap ℤ (B ⧸ Q) :=
      RingHom.ext_int _ _
    rw [map_zero, aeval_def, eval₂_map, hc, ← aeval_def, ← hy, ← comp_aeval_apply, hP, map_zero]
  have key : ∀ n : ℕ, ∀ P : MvPolynomial s ℤ, aeval y P = 0 →
      ∀ m, P.coeff m ≠ 0 → (P.coeff m).natAbs ≤ n → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro P hP m hm hn
      have hdvd : C (p : ℤ) ∣ P := by
        rw [C_dvd_iff_dvd_coeff]
        intro i
        have := congrArg (MvPolynomial.coeff i) (hred P hP)
        rw [coeff_map, coeff_zero, algebraMap_int_eq, eq_intCast,
          ZMod.intCast_zmod_eq_zero_iff_dvd] at this
        exact this
      obtain ⟨P', rfl⟩ := hdvd
      have hP' : aeval y P' = 0 := by
        rw [map_mul, aeval_C] at hP
        rcases mul_eq_zero.mp hP with h | h
        · exact absurd (by simpa using h) hp0
        · exact h
      rw [coeff_C_mul] at hm hn
      have hm' : P'.coeff m ≠ 0 := right_ne_zero_of_mul hm
      have hlt : (P'.coeff m).natAbs < n := by
        rw [Int.natAbs_mul] at hn
        have h2 : 2 ≤ ((p : ℤ)).natAbs := by
          simpa using (Fact.out : p.Prime).two_le
        have h1 : 0 < (P'.coeff m).natAbs := Int.natAbs_pos.mpr hm'
        nlinarith
      exact ih _ hlt P' hP' m hm' le_rfl
  refine AlgebraicIndependent.cardinalMk_le_trdeg (R := ℤ) (x := y) ?_
  rw [algebraicIndependent_iff]
  intro P hP
  by_contra hne
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hne
  exact key _ P hP m hm le_rfl
end GroundTheory.Heights₂.Heights
