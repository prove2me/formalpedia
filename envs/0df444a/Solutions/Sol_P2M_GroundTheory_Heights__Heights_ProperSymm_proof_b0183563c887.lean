-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProperSymm_proof_b0183563c887
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:26.739796+00:00
-- url     : https://prove2.me/submissions/94c89308-d735-4e6f-9593-cd7bfc213664

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProperSymm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_localMult_ne_zero_of_mem_minimalPrimes_0d5be1cc02d3

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
open MvPolynomial Ideal
namespace GroundTheory.Heights₂.Heights
namespace ProperSymm
theorem _root_.solution : ProperSymm.Statement := by
  intro n W u u' hW hu hu' hadm W'' hW'' hlu
  classical
  have hval := Finsupp.mem_support_iff.mp hW''
  simp only [divCycle, fundCycle, Finsupp.onFinset_apply] at hval
  have hrel : W'' ∈ relComps (W ⊔ span {linForm u'}) := by
    by_contra h
    exact hval (if_neg h)
  obtain ⟨hmin'', hrel''⟩ := hrel
  have : W''.IsPrime := hmin''.1.1
  have hle : W ⊔ span {linForm u} ≤ W'' :=
    sup_le (le_sup_left.trans hmin''.1.2) ((span_singleton_le_iff_mem _).mpr hlu)
  obtain ⟨W', hW', hW'le⟩ := Ideal.exists_minimalPrimes_le hle
  have hrel' : IsRelevant W' := by
    obtain ⟨j, hj⟩ := hrel''
    exact ⟨j, fun h => hj (hW'le h)⟩
  have hsupp : W' ∈ (divCycle W u).support := by
    rw [Finsupp.mem_support_iff]
    simp only [divCycle, fundCycle, Finsupp.onFinset_apply]
    rw [if_pos ⟨hW', hrel'⟩]
    exact localMult_ne_zero_of_mem_minimalPrimes hW'
  have hu'W' : linForm u' ∉ W' := hadm W' hsupp
  have : W'.IsPrime := hW'.1.1
  have : W.IsPrime := hW.isPrime
  have hWW' : W ≤ W' := le_sup_left.trans hW'.1.2
  have huW' : linForm u ∈ W' := hW'.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hu'W'' : linForm u' ∈ W'' :=
    hmin''.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  let f := Ideal.Quotient.mk W
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker f = W := Ideal.mk_ker
  have : (W'.map f).IsPrime := Ideal.map_isPrime_of_surjective hf (by rw [hker]; exact hWW')
  have : (W''.map f).IsPrime :=
    Ideal.map_isPrime_of_surjective hf (by rw [hker]; exact hWW'.trans hW'le)
  have : IsDomain (MvPolynomial (Fin n) ℂ ⧸ W) := Ideal.Quotient.isDomain W
  have : (⊥ : Ideal (MvPolynomial (Fin n) ℂ ⧸ W)).IsPrime := Ideal.isPrime_bot
  have h0 : (⊥ : Ideal (MvPolynomial (Fin n) ℂ ⧸ W)) < W'.map f := by
    refine bot_lt_iff_ne_bot.mpr fun h => hu ?_
    have hm := Ideal.mem_map_of_mem f huW'
    rw [h, Ideal.mem_bot] at hm
    exact Ideal.Quotient.eq_zero_iff_mem.mp hm
  have h1 : W'.map f < W''.map f := by
    refine lt_of_le_of_ne (Ideal.map_mono hW'le) fun h => hu'W' ?_
    have hm := Ideal.mem_map_of_mem f hu'W''
    rw [← h, ← Ideal.mem_comap, Ideal.comap_map_of_surjective' f hf, hker,
      sup_eq_left.mpr hWW'] at hm
    exact hm
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime h0
  have e2 := Ideal.height_add_one_le_of_lt_of_isPrime h1
  have e3 : (W''.map f).height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hmin''
  rw [Ideal.height_bot, zero_add] at e1
  have h2 : (2 : ℕ∞) ≤ 1 :=
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ (W'.map f).height + 1 := by gcongr
      _ ≤ (W''.map f).height := e2
      _ ≤ 1 := e3
  exact absurd h2 (by norm_num)
end ProperSymm
end GroundTheory.Heights₂.Heights
