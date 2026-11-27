-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_ConeVarNumerator_proof_f5ccf64c0518
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:54:27.66879+00:00
-- url     : https://prove2.me/submissions/7397a7c5-1e13-40e3-ad14-88ef6f5a2ddb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConeVarNumerator
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PConeVarNumerator
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_mul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_degZeroLoc_algebraMap_cone_coe_8ba24d60fc2f


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 200000
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace ConeVarNumerator
theorem _root_.solution (hDZ : DegZeroLocQuot.Statement.{u}) :
    ConeVarNumerator.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW v _
  have := hP.isPrime
  have := hW.isPrime
  intro p
  have hne : ∀ g : MRing ι F, g ∉ W →
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P g) ≠ 0 := by
    intro g hg
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h' => hg (hPW h')
  have h𝒲 : ∀ W' ∈ ({W} : Set (Ideal (MRing ι F))), W'.IsPrime := by
    intro W' hW'
    rw [Set.mem_singleton_iff.mp hW']
    infer_instance

  have step : ∀ D : Finset (K →₀ ℕ), ∃ (b : K → ℕ) (g : MRing ι F) (hn : (K →₀ ℕ) → MRing ι F),
      IsMultiHomog g b ∧ g ∉ W ∧ (∀ d, IsMultiHomog (hn d) b) ∧ (∀ d, d ∉ D → hn d = 0) ∧
      ∀ d ∈ D, ((p.coeff d : degZeroLoc P {W}) : FractionRing (MRing ι F ⧸ P)) =
        algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (hn d)) /
          algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) := by
    intro D
    induction D using Finset.induction_on with
    | empty =>
      refine ⟨0, 1, fun _ => 0, isWeightedHomogeneous_one F _, fun h1 => ?_,
        fun _ => isWeightedHomogeneous_zero F _ _, fun _ _ => rfl, fun d hd => absurd hd (Finset.notMem_empty d)⟩
      exact Ideal.IsPrime.ne_top inferInstance ((Ideal.eq_top_iff_one W).mpr h1)
    | insert d₀ D hd₀ ih =>
      obtain ⟨b, g, hn, hg, hgW, hh, h0, hD⟩ := ih
      obtain ⟨b', f', g', hf', hg', -, hg'W, he⟩ := hDZ F K ι P {W} h𝒲 _ (p.coeff d₀).2
      have hg'W' : g' ∉ W := hg'W W rfl
      refine ⟨b + b', g * g', fun d => if d = d₀ then g * f' else hn d * g',
        IsWeightedHomogeneous.mul hg hg', fun hm => ?_, fun d => ?_, fun d hd => ?_, fun d hd => ?_⟩
      · exact (Ideal.IsPrime.mem_or_mem inferInstance hm).elim hgW hg'W'
      · dsimp only
        split_ifs
        · exact IsWeightedHomogeneous.mul hg hf'
        · exact IsWeightedHomogeneous.mul (hh d) hg'
      · rw [Finset.mem_insert, not_or] at hd
        dsimp only
        rw [if_neg hd.1, h0 d hd.2, zero_mul]
      · rcases Finset.mem_insert.mp hd with rfl | hd
        · dsimp only
          rw [if_pos rfl, he]
          simp only [map_mul]
          rw [mul_div_mul_left _ _ (hne g hgW)]
        · have hdd : d ≠ d₀ := fun e => hd₀ (e ▸ hd)
          dsimp only
          rw [if_neg hdd, hD d hd]
          simp only [map_mul]
          rw [mul_div_mul_right _ _ (hne g' hg'W')]
  obtain ⟨b, g, hn, hg, hgW, hh, h0, hD⟩ := step p.support
  refine ⟨b, g, hn, hg, hgW, hh, fun d => ?_, ?_⟩
  · by_cases hd : d ∈ p.support
    · exact hD d hd
    · rw [notMem_support_iff.mp hd, h0 d hd]
      simp

  have hφ : ∀ x : MvPolynomial K (degZeroLoc P {W}),
      ((coneVarMap P W hPW v x : coneLocal P W hPW) : FractionRing (MRing ι F ⧸ P)) =
        eval₂ (degZeroLoc P {W}).val.toRingHom (fun k => algebraMap (MRing ι F ⧸ P)
          (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (X ⟨k, v k⟩))) x := by
    intro x
    induction x using MvPolynomial.induction_on with
    | C a =>
      rw [coneVarMap, aeval_C, degZeroLoc.algebraMap_cone_coe, eval₂_C]
      rfl
    | add x y hx hy =>
      rw [map_add (coneVarMap P W hPW v) x y, Subalgebra.coe_add, hx, hy, eval₂_add]
    | mul_X x k hx =>
      rw [map_mul, Subalgebra.coe_mul, hx, eval₂_mul, eval₂_X, coneVarMap, aeval_X]
      rfl
  rw [hφ, eval₂_eq']
  simp only [map_sum, map_mul, map_prod, map_pow, Finset.sum_div]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [mul_div_right_comm, ← hD d hd]
  rfl
end ConeVarNumerator
end GroundTheory.Heights₂.Heights.FieldNumbers
