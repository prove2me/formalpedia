-- Prove2me | solution 1 for RevenueOrdered.UDPmin.uniform_pricing_log_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T04:23:20.039331+00:00
-- url     : https://prove2.me/submissions/ce0dfe88-152d-4789-86e6-d60fc69c8a98

import Mathlib
import Definitions.Def_RevenueOrdered_UDPmin_Reduction
import Theorems.Thm_RevenueOrdered_UDPmin_udpmin_reduction
import Theorems.Thm_RevenueOrdered_UDPmin_revenue_ordered_ratio_bound

open scoped BigOperators
open RevenueOrdered.UDPmin
local notation "IsRegular" => RevenueOrdered.UDPmin.IsRegular
set_option maxHeartbeats 1000000

variable {X M : Type*} [Fintype X] [DecidableEq X] [Fintype M] [Nonempty M]

private lemma up_pay_le (I : Instance X M) (p : X → ℝ) (i : M) : payment I p i ≤ I.v i := by
  unfold payment
  split_ifs with hb hp
  · exact hp
  · exact (I.v_pos i).le
  · exact (I.v_pos i).le

private lemma up_uniform_ge (I : Instance X M) (q : ℝ) (hq : 0 < q) :
    revenue I (fun _ => q) ≤ uniformRevenue I := by
  have hb : BddAbove (Set.range (fun z : {q : ℝ // 0 < q} => revenue I (fun _ => z.val))) := by
    refine ⟨∑ i, I.v i, ?_⟩
    rintro _ ⟨z,rfl⟩
    exact Finset.sum_le_sum (fun i _ => up_pay_le I _ i)
  exact le_ciSup hb ⟨q,hq⟩

private lemma up_vm (I : Instance X M) : 0 < vMin I ∧ vMin I ≤ vMax I := by
  classical
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset M)) Finset.univ_nonempty I.v
  constructor
  · change 0 < Finset.univ.inf' Finset.univ_nonempty I.v
    rw [he]
    exact I.v_pos i
  · change Finset.univ.inf' Finset.univ_nonempty I.v ≤ Finset.univ.sup' Finset.univ_nonempty I.v
    rw [he]
    exact Finset.le_sup' I.v (Finset.mem_univ i)

private lemma up_r_bounds [Nonempty X] (I : Instance X M)
    [Nonempty (RedProd I)] :
    rMax (redRev I) ≤ (Fintype.card M : ℝ)*vMax I ∧
      (Fintype.card M : ℝ)*vMin I ≤ rMin (redRev I) := by
  classical
  have hm : 0 ≤ (Fintype.card M : ℝ) := Nat.cast_nonneg _
  have hu (y : RedProd I) : redRev I y ≤ (Fintype.card M : ℝ)*vMax I := by
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp y.2.property
    dsimp [redRev]
    rw [← he]
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' I.v (Finset.mem_univ i)) hm
  have hl (y : RedProd I) : (Fintype.card M : ℝ)*vMin I ≤ redRev I y := by
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp y.2.property
    dsimp [redRev]
    rw [← he]
    exact mul_le_mul_of_nonneg_left (Finset.inf'_le I.v (Finset.mem_univ i)) hm
  constructor
  · apply Finset.max'_le
    intro t ht
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ht
    exact hu y
  · apply Finset.le_min'
    intro t ht
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ht
    exact hl y

private lemma up_root_nonempty [Nonempty X] (I : Instance X M)
    (hp : IsRegular (redP I)) (hr : ∀ y : RedProd I, 0 < redRev I y)
    (heq : RevenueOrdered.Ratio.opt (redP I) (redRev I) = optUDP I)
    (hthreshold : ∀ y : RedProd I, ∃ i : M, RevenueOrdered.Tightness.rev (redP I) (redRev I)
      (thresholdSet (redRev I) (redRev I y)) = revenue I (fun _ => I.v i))
    (hratio : ∀ [Nonempty (RedProd I)],
      RevenueOrdered.Ratio.opt (redP I) (redRev I) ≤ ratioSum (redRev I)*ro (redP I) (redRev I) ∧
      ratioSum (redRev I) ≤ 1+Real.log (rMax (redRev I)/rMin (redRev I))) :
    optUDP I ≤ (1+Real.log (vMax I/vMin I))*uniformRevenue I := by
  classical
  let i0 : M := Classical.arbitrary M
  let y0 : RedProd I := ⟨Classical.arbitrary X, ⟨I.v i0, Finset.mem_image.mpr ⟨i0, Finset.mem_univ i0, rfl⟩⟩⟩
  letI : Nonempty (RedProd I) := ⟨y0⟩
  have hro : ro (redP I) (redRev I) ≤ uniformRevenue I := by
    unfold ro
    apply Finset.sup'_le
    intro t ht
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨i,he⟩ := hthreshold y
    rw [he]
    exact up_uniform_ge I _ (I.v_pos i)
  have hro0 : 0 ≤ ro (redP I) (redRev I) := by
    have hn : 0 ≤ RevenueOrdered.Tightness.rev (redP I) (redRev I)
        (thresholdSet (redRev I) (redRev I y0)) :=
      Finset.sum_nonneg (fun y _ => mul_nonneg (hp.nonneg y _) (hr y).le)
    apply hn.trans
    unfold ro
    exact Finset.le_sup' (fun t => RevenueOrdered.Tightness.rev (redP I) (redRev I)
      (thresholdSet (redRev I) t)) (Finset.mem_image.mpr ⟨y0, Finset.mem_univ y0, rfl⟩)
  have hm : 0 < (Fintype.card M : ℝ) := by exact_mod_cast Fintype.card_pos
  have hv := up_vm I
  have hb := up_r_bounds I
  have hmin : 0 < rMin (redRev I) := (mul_pos hm hv.1).trans_le hb.2
  have hmax : 0 < rMax (redRev I) := by
    have hne : (revValues (redRev I)).Nonempty := Finset.univ_nonempty.image _
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp (Finset.max'_mem (revValues (redRev I)) hne)
    change redRev I y = rMax (redRev I) at he
    rw [← he]
    exact hr y
  have hdiv : rMax (redRev I)/rMin (redRev I) ≤ vMax I/vMin I := by
    calc
      _ ≤ ((Fintype.card M : ℝ)*vMax I)/((Fintype.card M : ℝ)*vMin I) :=
        div_le_div₀ (mul_nonneg hm.le (hv.1.trans_le hv.2).le) hb.1 (mul_pos hm hv.1) hb.2
      _ = _ := by field_simp [ne_of_gt hm]
  have hlog := Real.log_le_log (div_pos hmax hmin) hdiv
  have hL : 0 ≤ 1+Real.log (vMax I/vMin I) := by
    have hh : 1 ≤ vMax I/vMin I := (le_div_iff₀ hv.1).mpr (by simpa using hv.2)
    have := Real.log_nonneg hh
    linarith
  have hh := hratio
  rw [← heq]
  calc
    _ ≤ ratioSum (redRev I)*ro (redP I) (redRev I) := hh.1
    _ ≤ (1+Real.log (vMax I/vMin I))*ro (redP I) (redRev I) :=
      mul_le_mul_of_nonneg_right (by linarith [hh.2]) hro0
    _ ≤ _ := mul_le_mul_of_nonneg_left hro hL

private lemma up_root_empty [IsEmpty X] (I : Instance X M) :
    optUDP I ≤ (1+Real.log (vMax I/vMin I))*uniformRevenue I := by
  classical
  have hB (i : M) : I.B i = ∅ := Finset.eq_empty_of_isEmpty _
  have hrev (p : X → ℝ) : revenue I p = 0 := by simp [revenue, payment, hB]
  letI : Nonempty {p : X → ℝ // ∀ x, 0 < p x} := ⟨⟨fun _ => 1, by simp⟩⟩
  letI : Nonempty {q : ℝ // 0 < q} := ⟨⟨1, by norm_num⟩⟩
  simp [optUDP, uniformRevenue, hrev]


theorem solution {X M : Type*} [Fintype X] [Fintype M] [Nonempty M]
    (I : Instance X M) :
    optUDP I ≤ (1 + Real.log (vMax I / vMin I)) * uniformRevenue I := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · letI := hX
    exact up_root_empty I
  · letI := hX
    have h := RevenueOrdered.UDPmin.udpmin_reduction I
    apply up_root_nonempty I h.1 h.2.1 h.2.2.1 h.2.2.2.2
    intro inst
    exact RevenueOrdered.UDPmin.revenue_ordered_ratio_bound (redP I) h.1 (redRev I) h.2.1
#print axioms solution
