-- Prove2me | solution 1 for SennottDP.BOR.bor_of_cav
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T02:11:36.590648+00:00
-- url     : https://prove2.me/submissions/37e9a45e-1e13-4a33-92d6-ecd49b8a5f87

import Mathlib
import Definitions.Def_SennottDP_BOR_Assumptions

open scoped ENNReal NNReal
open Filter Topology


namespace SennottDP.BOR

open Classical

noncomputable def kerG {S : Type} [Countable S] {Act : Type} {M : SennottDP.Discounted.MDC S Act}
    (d : RandStationaryPolicy M) (G : Set S) (k j : S) : ℝ≥0∞ :=
  if j ∈ G then 0 else ∑' a, d.dist k a * M.P k a j

noncomputable def pw {S : Type} (p : S → S → ℝ≥0∞) : ℕ → S → S → ℝ≥0∞
  | 0, i, j => if i = j then 1 else 0
  | t+1, i, j => ∑' k, pw p t i k * p k j

noncomputable def cst {S : Type} [Countable S] {Act : Type} {M : SennottDP.Discounted.MDC S Act}
    (d : RandStationaryPolicy M) (k : S) : ℝ≥0∞ :=
  ∑ a ∈ M.A k, d.dist k a * (M.C k a : ℝ≥0∞)

lemma key_mc {S : Type} [Countable S] {Act : Type} {M : SennottDP.Discounted.MDC S Act}
    (d : RandStationaryPolicy M) (G : Set S) : ∀ (t : ℕ) (i : S) (g : S → ℝ≥0∞),
    (∑' s : Fin (t+1) → S, ∑' as : Fin t → Act,
      if (∀ k : Fin (t+1), 1 ≤ k.val → s k ∉ G) then
        histProb d.toPolicy i t s as * g (s (Fin.last t)) else 0)
    = ∑' j, pw (kerG d G) t i j * g j := by
  intro t
  induction t with
  | zero =>
    intro i g
    rw [← (Equiv.funUnique (Fin 1) S).symm.tsum_eq]
    simp [histProb, pw]
  | succ t ih =>
    intro i g
    have hpt : ∀ (x : S) (s' : Fin (t+1) → S) (a : Act) (as' : Fin t → Act),
        (if (∀ k : Fin (t+2), 1 ≤ k.val → (Fin.snoc s' x : Fin (t+2) → S) k ∉ G) then
          histProb d.toPolicy i (t+1) (Fin.snoc s' x) (Fin.snoc as' a) *
            g ((Fin.snoc s' x : Fin (t+2) → S) (Fin.last (t+1))) else 0)
        = if (∀ k : Fin (t+1), 1 ≤ k.val → s' k ∉ G) then
            histProb d.toPolicy i t s' as' *
              (if x ∈ G then 0 else d.dist (s' (Fin.last t)) a * M.P (s' (Fin.last t)) a x * g x)
          else 0 := by
      intro x s' a as'
      have hc : (∀ k : Fin (t+2), 1 ≤ k.val → (Fin.snoc s' x : Fin (t+2) → S) k ∉ G) ↔
          ((∀ k : Fin (t+1), 1 ≤ k.val → s' k ∉ G) ∧ x ∉ G) := by
        constructor
        · intro h
          refine ⟨fun k hk => ?_, ?_⟩
          · have := h (Fin.castSucc k) (by simpa using hk)
            simpa using this
          · have := h (Fin.last (t+1)) (by simp)
            simpa using this
        · rintro ⟨h1, h2⟩ k hk
          induction k using Fin.lastCases with
          | last => simpa using h2
          | cast k => simpa using h1 k (by simpa using hk)
      rw [if_congr hc rfl rfl]
      simp only [histProb, Fin.init_snoc, Fin.snoc_last, Fin.snoc_castSucc,
        RandStationaryPolicy.toPolicy]
      by_cases h1 : (∀ k : Fin (t+1), 1 ≤ k.val → s' k ∉ G) <;> by_cases h2 : x ∈ G <;>
        simp [h1, h2, mul_assoc]
    calc (∑' s : Fin (t+2) → S, ∑' as : Fin (t+1) → Act,
          if (∀ k : Fin (t+2), 1 ≤ k.val → s k ∉ G) then
            histProb d.toPolicy i (t+1) s as * g (s (Fin.last (t+1))) else 0)
        = ∑' x : S, ∑' s' : Fin (t+1) → S, ∑' a : Act, ∑' as' : Fin t → Act,
            if (∀ k : Fin (t+1), 1 ≤ k.val → s' k ∉ G) then
              histProb d.toPolicy i t s' as' *
                (if x ∈ G then 0 else d.dist (s' (Fin.last t)) a * M.P (s' (Fin.last t)) a x * g x)
            else 0 := by
          rw [← (Fin.snocEquiv (fun _ => S)).tsum_eq, ENNReal.tsum_prod']
          refine tsum_congr (fun x => tsum_congr (fun s' => ?_))
          rw [← (Fin.snocEquiv (fun _ => Act)).tsum_eq, ENNReal.tsum_prod']
          refine tsum_congr (fun a => tsum_congr (fun as' => ?_))
          exact hpt x s' a as'
      _ = ∑' s' : Fin (t+1) → S, ∑' as' : Fin t → Act,
            if (∀ k : Fin (t+1), 1 ≤ k.val → s' k ∉ G) then
              histProb d.toPolicy i t s' as' *
                (fun k => ∑' x, kerG d G k x * g x) (s' (Fin.last t))
            else 0 := by
          rw [ENNReal.tsum_comm]
          refine tsum_congr (fun s' => ?_)
          conv_lhs => enter [1, x]; rw [ENNReal.tsum_comm]
          rw [ENNReal.tsum_comm]
          refine tsum_congr (fun as' => ?_)
          split_ifs with h1
          · simp only [kerG]
            rw [← ENNReal.tsum_mul_left]
            refine tsum_congr (fun x => ?_)
            split_ifs with h2
            · simp
            · rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
          · simp
      _ = ∑' j, pw (kerG d G) (t+1) i j * g j := by
          refine (ih i (fun k => ∑' x, kerG d G k x * g x)).trans ?_
          simp only [pw]
          simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
          rw [ENNReal.tsum_comm]
          refine tsum_congr (fun k => tsum_congr (fun x => ?_))
          ring


section
variable {S : Type} [Countable S] {Act : Type} {M : SennottDP.Discounted.MDC S Act}

lemma expCost_eq_mc (d : RandStationaryPolicy M) (i : S) (t : ℕ) :
    expCost d.toPolicy i t = ∑' j, pw (kerG d ∅) t i j * cst d j := by
  rw [← key_mc d ∅ t i (cst d)]
  simp only [Set.mem_empty_iff_false, not_false_eq_true, implies_true, if_true]
  rfl

lemma passageCost_eq_mc (d : RandStationaryPolicy M) (i : S) (G : Set S) :
    passageCost d.toPolicy i G = ∑' t, ∑' j, pw (kerG d G) t i j * cst d j := by
  unfold passageCost
  refine tsum_congr (fun t => ?_)
  rw [← key_mc d G t i (cst d)]
  rfl

lemma kerG_split (d : RandStationaryPolicy M) (z k j : S) :
    kerG d ∅ k j = kerG d {z} k j + (if j = z then kerG d ∅ k z else 0) := by
  unfold kerG
  by_cases h : j = z
  · subst h; simp
  · simp [h]

lemma kerG_sum_le (d : RandStationaryPolicy M) (k : S) : ∑' j, kerG d ∅ k j ≤ 1 := by
  simp only [kerG, Set.mem_empty_iff_false, if_false]
  rw [ENNReal.tsum_comm]
  calc ∑' a, ∑' j, d.dist k a * M.P k a j = ∑' a, d.dist k a * ∑' j, M.P k a j := by
        simp_rw [ENNReal.tsum_mul_left]
    _ = ∑ a ∈ M.A k, d.dist k a * ∑' j, M.P k a j := by
        rw [tsum_eq_sum]
        intro a ha; simp [d.dist_supp k a ha]
    _ = ∑ a ∈ M.A k, d.dist k a := by
        refine Finset.sum_congr rfl (fun a ha => ?_)
        rw [M.P_sum k a ha, mul_one]
    _ = 1 := d.dist_sum k
    _ ≤ 1 := le_rfl

lemma pw_sum_le (d : RandStationaryPolicy M) : ∀ t i, ∑' j, pw (kerG d ∅) t i j ≤ 1 := by
  intro t
  induction t with
  | zero => intro i; simp [pw]
  | succ t ih =>
    intro i
    simp only [pw]
    rw [ENNReal.tsum_comm]
    calc ∑' k, ∑' j, pw (kerG d ∅) t i k * kerG d ∅ k j
        = ∑' k, pw (kerG d ∅) t i k * ∑' j, kerG d ∅ k j := by simp_rw [ENNReal.tsum_mul_left]
      _ ≤ ∑' k, pw (kerG d ∅) t i k * 1 := by
          gcongr with k; exact kerG_sum_le d k
      _ ≤ 1 := by simpa using ih i

lemma pw_le_one (d : RandStationaryPolicy M) (t : ℕ) (i j : S) : pw (kerG d ∅) t i j ≤ 1 :=
  le_trans (ENNReal.le_tsum j) (pw_sum_le d t i)

lemma pw_decomp (d : RandStationaryPolicy M) (z : S) : ∀ t i j,
    pw (kerG d ∅) t i j = pw (kerG d {z}) t i j +
      ∑ s ∈ Finset.range t, pw (kerG d ∅) (s+1) i z * pw (kerG d {z}) (t - 1 - s) z j := by
  intro t
  induction t with
  | zero => intro i j; simp [pw]
  | succ t ih =>
    intro i j
    have e1 : pw (kerG d ∅) (t+1) i j = ∑' k, pw (kerG d ∅) t i k * kerG d {z} k j +
        (if j = z then pw (kerG d ∅) (t+1) i z else 0) := by
      simp only [pw]
      simp_rw [kerG_split d z _ j, mul_add]
      rw [ENNReal.tsum_add]
      congr 1
      by_cases h : j = z
      · subst h; simp
      · simp [h]
    rw [e1]
    simp_rw [ih]
    simp_rw [add_mul, Finset.sum_mul]
    rw [ENNReal.tsum_add, Finset.sum_range_succ, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    have e2 : ∀ s ∈ Finset.range t, ∑' k, pw (kerG d ∅) (s+1) i z * pw (kerG d {z}) (t - 1 - s) z k
        * kerG d {z} k j = pw (kerG d ∅) (s+1) i z * pw (kerG d {z}) (t + 1 - 1 - s) z j := by
      intro s hs
      have hs' : t + 1 - 1 - s = (t - 1 - s) + 1 := by
        have := Finset.mem_range.1 hs; omega
      rw [hs']
      simp only [pw]
      rw [← ENNReal.tsum_mul_left]
      refine tsum_congr (fun k => ?_); ring
    rw [Finset.sum_congr rfl e2]
    have e3 : (if j = z then pw (kerG d ∅) (t+1) i z else 0) =
        pw (kerG d ∅) (t+1) i z * pw (kerG d {z}) (t + 1 - 1 - t) z j := by
      simp only [Nat.add_sub_cancel, Nat.sub_self, pw]
      by_cases h : z = j
      · subst h; simp
      · simp [h, Ne.symm h]
    rw [e3]
    simp only [pw]
    ring

lemma expCost_le_mc (d : RandStationaryPolicy M) (z i : S) (t : ℕ) :
    expCost d.toPolicy i t ≤ (∑' j, pw (kerG d {z}) t i j * cst d j) + passageCost d.toPolicy z {z} := by
  rw [expCost_eq_mc]
  simp_rw [pw_decomp d z t i, add_mul, Finset.sum_mul]
  rw [ENNReal.tsum_add, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  gcongr
  rw [passageCost_eq_mc]
  calc ∑ s ∈ Finset.range t, ∑' j, pw (kerG d ∅) (s+1) i z * pw (kerG d {z}) (t - 1 - s) z j * cst d j
      ≤ ∑ s ∈ Finset.range t, ∑' j, pw (kerG d {z}) (t - 1 - s) z j * cst d j := by
        gcongr with s hs j
        exact mul_le_of_le_one_left (zero_le) (pw_le_one d _ _ _)
    _ = ∑ u ∈ Finset.range t, ∑' j, pw (kerG d {z}) u z j * cst d j := by
        exact Finset.sum_range_reflect (fun u => ∑' j, pw (kerG d {z}) u z j * cst d j) t
    _ ≤ ∑' u, ∑' j, pw (kerG d {z}) u z j * cst d j := ENNReal.sum_le_tsum _

lemma expCost_z_le (d : RandStationaryPolicy M) (z : S) (t : ℕ) :
    expCost d.toPolicy z t ≤ 2 * passageCost d.toPolicy z {z} := by
  refine (expCost_le_mc d z z t).trans ?_
  rw [two_mul]
  gcongr
  rw [passageCost_eq_mc]
  exact ENNReal.le_tsum (f := fun t => ∑' j, pw (kerG d {z}) t z j * cst d j) t

lemma avgCost_z_le (d : RandStationaryPolicy M) (z : S) :
    avgCost d.toPolicy z ≤ 2 * passageCost d.toPolicy z {z} := by
  unfold avgCost
  refine limsup_le_of_le (by isBoundedDefault) (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  apply ENNReal.div_le_of_le_mul
  unfold horizonCost
  calc ∑ t ∈ Finset.range n, expCost d.toPolicy z t ≤ ∑ t ∈ Finset.range n, 2 * passageCost d.toPolicy z {z} :=
        Finset.sum_le_sum (fun t _ => expCost_z_le d z t)
    _ = 2 * passageCost d.toPolicy z {z} * n := by simp [mul_comm]

end


lemma lowCost_finite_core {S Act : Type} [Countable S] (M : SennottDP.Discounted.MDC S Act) (z : S)
    (d : RandStationaryPolicy M) (hd : IsZStandard d.toPolicy z)
    (hD : ∀ U : ℝ, 0 < U → (lowCostSet M (ENNReal.ofReal U)).Finite) :
    (lowCostSet M (avgCost d.toPolicy z + ENNReal.ofReal 1)).Finite := by
  have hfin : avgCost d.toPolicy z ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) (hd z).2.ne) (avgCost_z_le d z)
  have h1 : avgCost d.toPolicy z + ENNReal.ofReal 1 =
      ENNReal.ofReal ((avgCost d.toPolicy z).toReal + 1) := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one, ENNReal.ofReal_toReal hfin]
  rw [h1]
  exact hD _ (by positivity)

theorem bor_of_cav_core {S Act : Type} [Countable S] (M : SennottDP.Discounted.MDC S Act) (z : S)
    (d : RandStationaryPolicy M) (hCAV : CAVAssumptions M z d) :
    ∃ ε : ℝ, BORAssumptions M z d ε :=
  ⟨1, hCAV.1, ⟨one_pos, lowCost_finite_core M z d hCAV.1 hCAV.2.1⟩,
    fun i hi => hCAV.2.2 i hi.2⟩

theorem cav_of_irreducible_standard_core {S Act : Type} [Countable S] (M : SennottDP.Discounted.MDC S Act) (z : S)
    (d : RandStationaryPolicy M) (hd : IsZStandard d.toPolicy z)
    (hR : recClass M d z = Set.univ)
    (hD : ∀ U : ℝ, 0 < U → (lowCostSet M (ENNReal.ofReal U)).Finite) :
    CAVAssumptions M z d ∧ ∃ ε : ℝ, BORAssumptions M z d ε := by
  have hC : CAVAssumptions M z d := ⟨hd, hD, fun i hi => absurd (hR ▸ Set.mem_univ i) hi⟩
  exact ⟨hC, bor_of_cav_core M z d hC⟩

end SennottDP.BOR

open SennottDP.BOR


theorem solution {S Act : Type} [Countable S] (M : SennottDP.Discounted.MDC S Act) (z : S)
    (d : RandStationaryPolicy M) (hCAV : CAVAssumptions M z d) :
    ∃ ε : ℝ, BORAssumptions M z d ε := by
  exact bor_of_cav_core M z d hCAV
