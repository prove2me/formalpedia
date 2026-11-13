-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.CharacterDegreeCore.G0_nonvanishing_dichotomy_core
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:01:09.173033+00:00
-- url     : https://prove2.me/submissions/83a5256d-df1c-4967-8f96-6b6c38df1535

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Algebra/GaloisRationalInteger.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean
--   OddOrder/Peterfalvi/S15_CaseBEndgameSupply/AnalyticRelayer.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEngines
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Theorems.Thm_OddOrder_Peterfalvi_S15_lambda_tau1_apply_eq_of_not_mem_H_sat_core

-- ===== OddOrder/Algebra/GaloisRationalInteger.lean =====
namespace OddOrder.Algebra

open Polynomial IntermediateField

open OddOrder.RepresentationTheory in
/-- **Virtual-character values are algebraic integers** (general form, `OddOrder.Algebra` copy of
the `S05` leaf lemma): each irreducible character value is a sum of roots of unity
(`character_isIntegral`), and `IsIntegral ℤ` is closed under the `ℤ`-span operations. -/
theorem isIntegral_apply_of_mem_ZIrr {G : Type*} [Group G] [Finite G]
    {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) (g : G) :
    IsIntegral ℤ (φ g) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨V, _, _, _, ρ, hchar⟩ := IsIrreducibleCharacter.isCharacter hx
      rw [show x g = ρ.character g from congrFun hchar g]
      exact character_isIntegral ρ g
  | zero => rw [ClassFunction.zero_apply]; exact isIntegral_zero
  | add a b _ _ ha hb => rw [ClassFunction.add_apply]; exact ha.add hb
  | smul n a _ ha =>
      rw [ClassFunction.zsmul_apply, zsmul_eq_mul]
      exact (isIntegral_algebraMap (x := n)).mul ha

end OddOrder.Algebra

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

section CountingLayer

open OddOrder.GroupTheory

/-- Membership in the generic set `G₀`, unfolded: nonidentity and in neither saturation. -/
theorem Hypothesis.mem_G0_iff (hyp : Hypothesis (G := G)) (x : G) :
    x ∈ hyp.G0 ↔ x ≠ 1 ∧ x ∉ conjClassSet (sharpSubgroup hyp.H)
      ∧ x ∉ conjClassSet (sharpSubgroup hyp.Q) := by
  change x ∈ sharpSubgroup (⊤ : Subgroup G) \ _ ↔ _
  simp only [sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe,
    Subgroup.mem_top, true_and, Set.mem_union, not_or]

end CountingLayer

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CaseBEndgameSupply/AnalyticRelayer.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

section

/-- **Peterfalvi (13.9.a), Core form**: on `G₀`, `λ^{τ₁}` and `η₁₀` do not
vanish simultaneously.  The proof uses the Core/cluster off-`H^#` formula, the regular
value formula, and the four-corner grid relation; no monolithic character-degree carrier
is involved. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp) :
    ∀ x ∈ hyp.G0Finset, core.tau1S lam.lambda x ≠ 0 ∨ hyp.eta10 x ≠ 0 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  intro x hxF
  have hxG0 : x ∈ hyp.G0 := (Set.Finite.mem_toFinset _).mp hxF
  obtain ⟨hx1, hxH, hxQ⟩ := (hyp.mem_G0_iff x).mp hxG0
  by_cases hreg : x ∈ OddOrder.GroupTheory.conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G)))
  · right
    obtain ⟨w, hwmem, g, hg⟩ := OddOrder.GroupTheory.mem_conjClassSet.mp hreg
    obtain ⟨hwW, hwnot⟩ := hwmem
    have hconjval : hyp.eta10 x = hyp.eta10 w := by
      rw [← hg]
      exact (OddOrder.RepresentationTheory.ClassFunction.of_isConj hyp.eta10
        (isConj_iff.mpr ⟨g, rfl⟩)).symm
    have hval : hyp.eta10 w =
        hyp.omega ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩ ⟨w, hwW⟩ := by
      rw [show hyp.eta10 = hyp.eta ⟨1, hyp.q_prime.one_lt⟩
        ⟨0, hyp.p_prime.pos⟩ from rfl, hyp.eta_eq_tau_omega]
      exact hyp.tau3_apply_of_regular _ _ hwW hwnot
    rw [hconjval, hval]
    intro h0
    have hmul := hyp.omega_mul ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩
      ⟨w, hwW⟩ ⟨w, hwW⟩⁻¹
    rw [mul_inv_cancel, hyp.omega_apply_one, h0, zero_mul] at hmul
    exact one_ne_zero hmul
  · by_contra hboth
    push Not at hboth
    obtain ⟨hl0, he0⟩ := hboth
    obtain ⟨δ, hδ, hlam⟩ :=
      lambda_tau1_apply_eq_of_not_mem_H_sat_core hG core lam hxH
    have hδ0 : (δ : ℂ) ≠ 0 := by
      rcases hδ with rfl | rfl <;> norm_num
    have hsum0 : ∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ x = 0 := by
      have h := hlam.symm.trans hl0
      exact (mul_eq_zero.mp h).resolve_left hδ0
    have he10 : hyp.tau3 (hyp.omega ⟨1, hyp.q_prime.one_lt⟩
        ⟨0, hyp.p_prime.pos⟩) x = 0 := by
      rw [← hyp.eta_eq_tau_omega]
      exact he0
    have hrow := hyp.eta_row_vanish_of_one_zero x he10
    have hcol1ne : (⟨1, hyp.p_prime.one_lt⟩ : Fin hyp.p) ≠
        ⟨0, hyp.p_prime.pos⟩ := by
      intro h
      exact absurd (congrArg Fin.val h) one_ne_zero
    have hfc : ∀ i : Fin hyp.q, i ≠ ⟨0, hyp.q_prime.pos⟩ →
        hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ x
          = hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hyp.p_prime.one_lt⟩ x - 1 := by
      intro i hi
      have h4 := hyp.eta_fourcorner_vanish i ⟨1, hyp.p_prime.one_lt⟩ hi hcol1ne x hreg
      rw [hrow i hi] at h4
      rw [hyp.eta_eq_tau_omega, hyp.eta_eq_tau_omega]
      linear_combination h4
    have hsplit : (0 : ℂ) =
        (hyp.q : ℂ) * hyp.eta ⟨0, hyp.q_prime.pos⟩
          ⟨1, hyp.p_prime.one_lt⟩ x - ((hyp.q : ℂ) - 1) := by
      have hqpos : 0 < hyp.q := hyp.q_prime.pos
      have hcard : (Finset.univ.erase (⟨0, hqpos⟩ : Fin hyp.q)).card = hyp.q - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          Fintype.card_fin]
      calc (0 : ℂ) = ∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ x :=
            hsum0.symm
        _ = hyp.eta ⟨0, hqpos⟩ ⟨1, hyp.p_prime.one_lt⟩ x
            + ∑ i ∈ Finset.univ.erase (⟨0, hqpos⟩ : Fin hyp.q),
                hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ x :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm
        _ = hyp.eta ⟨0, hqpos⟩ ⟨1, hyp.p_prime.one_lt⟩ x
            + ∑ _i ∈ Finset.univ.erase (⟨0, hqpos⟩ : Fin hyp.q),
                (hyp.eta ⟨0, hqpos⟩ ⟨1, hyp.p_prime.one_lt⟩ x - 1) := by
          congr 1
          exact Finset.sum_congr rfl (fun i hi => hfc i (Finset.ne_of_mem_erase hi))
        _ = hyp.eta ⟨0, hqpos⟩ ⟨1, hyp.p_prime.one_lt⟩ x
            + ((hyp.q - 1 : ℕ) : ℂ)
              * (hyp.eta ⟨0, hqpos⟩ ⟨1, hyp.p_prime.one_lt⟩ x - 1) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
        _ = (hyp.q : ℂ) * hyp.eta ⟨0, hqpos⟩ ⟨1, hyp.p_prime.one_lt⟩ x
            - ((hyp.q : ℂ) - 1) := by
          have h1 : ((hyp.q - 1 : ℕ) : ℂ) = (hyp.q : ℂ) - 1 := by
            rw [Nat.cast_sub hyp.q_prime.one_lt.le, Nat.cast_one]
          rw [h1]
          ring
    have hZ : hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hyp.p_prime.one_lt⟩ ∈ ZIrr G := by
      rw [hyp.eta_eq_tau_omega]
      exact hyp.tau3_mem_ZIrr _ (hyp.omega_mem_ZIrr _ _)
    have hint := OddOrder.Algebra.isIntegral_apply_of_mem_ZIrr hZ x
    have hcast : (((hyp.q : ℤ) - 1 : ℤ) : ℂ) =
        ((hyp.q : ℤ) : ℂ) *
          hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hyp.p_prime.one_lt⟩ x := by
      push_cast
      linear_combination hsplit
    have hdvd := OddOrder.RepresentationTheory.int_dvd_of_intCast_eq_mul_isIntegral
      (by exact_mod_cast hyp.q_prime.pos.ne' : (hyp.q : ℤ) ≠ 0) hint hcast
    have hone : (hyp.q : ℤ) ∣ 1 := by
      have h2 : (hyp.q : ℤ) ∣ (hyp.q : ℤ) - ((hyp.q : ℤ) - 1) :=
        dvd_sub dvd_rfl hdvd
      simpa using h2
    have := Int.le_of_dvd one_pos hone
    have := hyp.q_prime.one_lt
    omega

end

end OddOrder.Peterfalvi.S15
