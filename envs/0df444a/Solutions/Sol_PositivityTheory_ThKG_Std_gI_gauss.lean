-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.gI_gauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:22:49.094473+00:00
-- url     : https://prove2.me/submissions/9a132b4c-2052-42e6-8acc-fc73205127c6

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_ContinuousCut
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_IntIndPow
import Theorems.Thm_PositivityTheory_ThKG_Std_dl_of_ne
import Theorems.Thm_PositivityTheory_ThKG_Std_val_pow_lt
import Theorems.Thm_PositivityTheory_ThKG_Std_dl_add
import Theorems.Thm_PositivityTheory_ThKG_Std_res_eq_iff
import Theorems.Thm_PositivityTheory_ThKG_Std_int_cosets
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_PositivityTheory_ThKG_Std_IsPsi_triv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf



set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Matrix MeasureTheory ValuativeRel Topology GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open scoped Pointwise
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Std
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ}
variable [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k] {m : Measure k} {ψ : AddChar k ℂ}
open Classical
namespace PositivityTheory.ThKG.Std
theorem _root_.solution (hm : IsVol m) (hψ : IsPsi ψ) (hϖ : IsUnif ϖ) (hc : 1 ≤ c) (hν : CondLE ϖ c ν) [Fintype (Res k c)ˣ] :
    gI m ψ ν (((ϖ : k) ^ c)⁻¹) = ((resCard k : ℂ) ^ c)⁻¹ * ∑ y : (Res k c)ˣ,
      if h : ((Quotient.out y.1 : 𝒪[k]) : k) = 0 then 0 else
        (((ν (Units.mk0 _ h))⁻¹ : ℂˣ) : ℂ) * ψ (((Quotient.out y.1 : 𝒪[k]) : k) / ϖ ^ c) := by
  have h0 : 0 < valuation k ((ϖ : k) ^ c) := zero_lt_iff.2 (by simp)
  rw [gI, int_cosets hm hϖ c _ (fun x hx => by rw [dl_of_ne fun h => hx h.le, zero_mul]) fun x t ht => by
    rw [dl_add hϖ hc hν x ht, mul_add, AddChar.map_add_eq_mul, hψ.triv (x := _ * t), mul_one]
    rwa [map_mul, map_inv₀, inv_mul_le_iff₀ h0, mul_one]]
  congr 1
  have hu : ∀ y : Res k c, IsUnit y ↔ valuation k ((Quotient.out y : 𝒪[k]) : k) = 1 := fun y => by
    constructor
    · rintro ⟨u, rfl⟩
      have h1 : (Ideal.Quotient.mk _ ((Quotient.out u.1 : 𝒪[k]) * Quotient.out (u⁻¹).1) : Res k c) = Ideal.Quotient.mk _ 1 := by
        rw [map_mul, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out, Units.mul_inv, map_one]
      have h2 := ((res_eq_iff hϖ c _ _).1 h1).trans_lt (val_pow_lt hϖ hc)
      have h3 := (valuation k).map_one_add_of_lt h2
      simp only [OneMemClass.coe_one, add_sub_cancel, MulMemClass.coe_mul, map_mul] at h3
      refine le_antisymm (Quotient.out u.1 : 𝒪[k]).2 ?_
      rw [← h3]
      exact mul_le_of_le_one_right' (Quotient.out (u⁻¹).1 : 𝒪[k]).2
    · intro h
      have : IsUnit (Quotient.out y : 𝒪[k]) := by
        by_contra h'
        exact absurd h (ne_of_lt (Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 h'))
      simpa only [Ideal.Quotient.mk_out] using this.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c))
  symm
  rw [← finsum_eq_sum_of_fintype, ← finsum_mem_univ, finsum_mem_eq_of_bijOn (s := Set.univ) (t := {y | IsUnit y})
    (g := fun y : Res k c => dl ν ((Quotient.out y : 𝒪[k]) : k) * ψ (((ϖ : k) ^ c)⁻¹ * (Quotient.out y : 𝒪[k]))) Units.val
    ⟨fun u _ => u.isUnit, fun _ _ _ _ => Units.ext, fun y ⟨u, hu⟩ => ⟨u, trivial, hu⟩⟩]
  · rw [finsum_mem_def]
    congr 1
    funext y
    by_cases hy : y ∈ {y : Res k c | IsUnit y}
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, dl_of_ne fun h => hy ((hu y).2 h), zero_mul]
  · intro u _
    have h1 := (hu u.1).1 u.isUnit
    have h2 : ((Quotient.out u.1 : 𝒪[k]) : k) ≠ 0 := by intro h; simp [h] at h1
    rw [dif_neg h2, dl, dif_pos ⟨h2, h1⟩, div_eq_inv_mul]
end PositivityTheory.ThKG.Std
