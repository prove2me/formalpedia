-- Prove2me | solution 1 for OnlinePrimalDual.AdAuctions.dual_near_feasible
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:07:51.697587+00:00
-- url     : https://prove2.me/submissions/d29644a0-f6c9-4354-b669-6f468ddd830a

import Mathlib
import Definitions.Def_OnlinePrimalDual_AdAuctions_AdAuctionsInstance
import Definitions.Def_OnlinePrimalDual_AdAuctions_cParam
import Definitions.Def_OnlinePrimalDual_AdAuctions_buyerX
import Definitions.Def_OnlinePrimalDual_AdAuctions_revenue

namespace OnlinePrimalDual.AdAuctions

lemma aux_dnf_c_gt_one {I M : Type*} [Fintype I] [Fintype M]
    (inst : AdAuctionsInstance I M) : 1 < cParam inst := by
  unfold cParam
  apply Real.one_lt_rpow
  · linarith [inst.hRmax_pos]
  · exact one_div_pos.mpr inst.hRmax_pos

lemma aux_dnf_bern {I M : Type*} [Fintype I] [Fintype M]
    (inst : AdAuctionsInstance I M) (t : ℝ) (ht0 : 0 ≤ t) (htR : t ≤ inst.Rmax) :
    cParam inst ^ t ≤ 1 + t := by
  have hR := inst.hRmax_pos
  unfold cParam
  rw [← Real.rpow_mul (by linarith)]
  have h1 : 0 ≤ 1 / inst.Rmax * t := by positivity
  have h2 : 1 / inst.Rmax * t ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one hR]; exact htR
  have := rpow_one_add_le_one_add_mul_self (s := inst.Rmax) (by linarith) h1 h2
  calc (1 + inst.Rmax) ^ (1 / inst.Rmax * t) ≤ 1 + 1 / inst.Rmax * t * inst.Rmax := this
    _ = 1 + t := by field_simp

lemma aux_dnf_fold {I M : Type*} [Fintype I] [Fintype M]
    (inst : AdAuctionsInstance I M) (i : I) (l : List ℝ)
    (hl : ∀ bd ∈ l, 0 ≤ bd ∧ bd ≤ inst.Rmax * inst.B i) (x S : ℝ)
    (hx : x ≥ (1 / (cParam inst - 1)) * (cParam inst ^ (S / inst.B i) - 1)) :
    l.foldl (fun x bd => x * (1 + bd / inst.B i) + bd / ((cParam inst - 1) * inst.B i)) x ≥
      (1 / (cParam inst - 1)) * (cParam inst ^ ((S + l.sum) / inst.B i) - 1) := by
  induction l generalizing x S with
  | nil => simpa using hx
  | cons b l ih =>
    simp only [List.foldl_cons, List.sum_cons]
    have hb := hl b (by simp)
    have hl' : ∀ bd ∈ l, 0 ≤ bd ∧ bd ≤ inst.Rmax * inst.B i :=
      fun bd h => hl bd (List.mem_cons_of_mem _ h)
    rw [show S + (b + l.sum) = (S + b) + l.sum by ring]
    apply ih hl'
    have hB := inst.hB_pos i
    have hc := aux_dnf_c_gt_one inst
    have hc1 : 0 < cParam inst - 1 := by linarith
    set c := cParam inst with hcdef
    set B := inst.B i
    set t := b / B with htdef
    have ht0 : 0 ≤ t := div_nonneg hb.1 hB.le
    have htR : t ≤ inst.Rmax := by
      rw [htdef, div_le_iff₀ hB]; exact hb.2
    have hbern : c ^ t ≤ 1 + t := aux_dnf_bern inst t ht0 htR
    have hsplit : c ^ ((S + b) / B) = c ^ (S / B) * c ^ t := by
      rw [← Real.rpow_add (by linarith)]; congr 1; rw [htdef]; ring
    have hpos : 0 ≤ c ^ (S / B) := Real.rpow_nonneg (by linarith) _
    have hbB : b / ((c - 1) * B) = t / (c - 1) := by
      rw [htdef, div_div, mul_comm B]
    rw [hsplit, hbB]
    have hmono : x * (1 + t) ≥ (1 / (c - 1)) * (c ^ (S / B) - 1) * (1 + t) :=
      mul_le_mul_of_nonneg_right hx (by linarith)
    have key : (1 / (c - 1)) * (c ^ (S / B) - 1) * (1 + t) + t / (c - 1) =
        (1 / (c - 1)) * (c ^ (S / B) * (1 + t) - 1) := by
      field_simp; ring
    have key2 : (1 / (c - 1)) * (c ^ (S / B) * c ^ t - 1) ≤
        (1 / (c - 1)) * (c ^ (S / B) * (1 + t) - 1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have := mul_le_mul_of_nonneg_left hbern hpos
      linarith
    linarith

end OnlinePrimalDual.AdAuctions

open OnlinePrimalDual.AdAuctions

theorem solution {I M : Type*} [Fintype I] [Fintype M]
    (inst : AdAuctionsInstance I M) (wonBids : I → List ℝ)
    (hbids_valid : ∀ i, ∀ bd ∈ wonBids i, 0 ≤ bd ∧ bd ≤ inst.Rmax * inst.B i) :
    ∀ i : I, buyerX inst i (wonBids i) ≥
      (1 / (cParam inst - 1)) * (cParam inst ^ (revenue inst wonBids i / inst.B i) - 1) := by
  intro i
  have h := aux_dnf_fold inst i (wonBids i) (hbids_valid i) 0 0 (by simp)
  simpa [buyerX, revenue] using h
