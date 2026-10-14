-- Prove2me | solution 1 for SennottDP.BOR.sen_of_monotone_value
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T02:24:14.554983+00:00
-- url     : https://prove2.me/submissions/b63e49ed-5453-4461-88af-7577c7f035b7

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


section shift
variable {S : Type} [Countable S] {Act : Type} {M : SennottDP.Discounted.MDC S Act}

noncomputable def shDist (d : RandStationaryPolicy M) (θs : S → SennottDP.Discounted.Policy M) :
    (n : ℕ) → (Fin (n+1) → S) → (Fin n → Act) → Act → ℝ≥0∞
  | 0, s, _, a => d.dist (s 0) a
  | n+1, s, as, a => (θs (s 1)).dist n (Fin.tail s) (Fin.tail as) a

noncomputable def shPol (d : RandStationaryPolicy M) (θs : S → SennottDP.Discounted.Policy M) :
    SennottDP.Discounted.Policy M where
  dist := shDist d θs
  dist_supp n s as a ha := by
    cases n with
    | zero => exact d.dist_supp _ a (by simpa using ha)
    | succ n =>
      apply (θs (s 1)).dist_supp
      simpa [Fin.tail, Fin.succ_last] using ha
  dist_sum n s as := by
    cases n with
    | zero => simpa [shDist] using d.dist_sum (s 0)
    | succ n =>
      have := (θs (s 1)).dist_sum n (Fin.tail s) (Fin.tail as)
      simpa [Fin.tail, Fin.succ_last, shDist] using this

lemma histProb_ne_zero {θ : SennottDP.Discounted.Policy M} {i : S} :
    ∀ n (s : Fin (n+1) → S) (as : Fin n → Act), s 0 ≠ i → histProb θ i n s as = 0 := by
  intro n
  induction n with
  | zero => intro s as h; simp [histProb, h]
  | succ n ih =>
    intro s as h
    simp only [histProb]
    rw [ih (Fin.init s) (Fin.init as) (by simpa [Fin.init] using h)]
    simp

lemma histProb_shPol (d : RandStationaryPolicy M) (θs : S → SennottDP.Discounted.Policy M) (i : S) :
    ∀ n (s : Fin (n+2) → S) (as : Fin (n+1) → Act),
    histProb (shPol d θs) i (n+1) s as =
      (if s 0 = i then 1 else 0) * d.dist (s 0) (as 0) * M.P (s 0) (as 0) (s 1) *
        histProb (θs (s 1)) (s 1) n (Fin.tail s) (Fin.tail as) := by
  intro n
  induction n with
  | zero =>
    intro s as
    by_cases h : s 0 = i
    · have h' : Fin.init s 0 = i := by simpa [Fin.init] using h
      simp [histProb, shPol, shDist, Fin.tail, h']
      simp [Fin.init, h]
    · rw [histProb_ne_zero _ s as h]; simp [h]
  | succ n ih =>
    intro s as
    by_cases h : s 0 = i
    · have h' : Fin.init s 0 = i := by simpa [Fin.init] using h
      rw [histProb, ih (Fin.init s) (Fin.init as), if_pos h', if_pos h]
      conv_rhs => rw [histProb]
      simp only [shPol, shDist, Fin.tail_init_eq_init_tail, one_mul]
      have e1 : Fin.init s 0 = s 0 := rfl
      have e2 : Fin.init s 1 = s 1 := rfl
      have e3 : Fin.init as 0 = as 0 := rfl
      have e4 : Fin.tail as (Fin.last n) = as (Fin.last (n+1)) := by simp [Fin.tail, Fin.succ_last]
      have e5 : Fin.tail s (Fin.last n).castSucc = s (Fin.last (n+1)).castSucc := by
        simp [Fin.tail, Fin.succ_castSucc, Fin.succ_last]
      have e6 : Fin.tail s (Fin.last (n+1)) = s (Fin.last (n+1+1)) := by simp [Fin.tail, Fin.succ_last]
      have e7 : Fin.init (Fin.init s) = Fin.init (Fin.init s) := rfl
      rw [e1, e2, e3, e4, e5, e6]
      ring
    · rw [histProb_ne_zero _ s as h, if_neg h]
      simp


lemma stepCost_shPol (d : RandStationaryPolicy M) (θs : S → SennottDP.Discounted.Policy M) (n : ℕ)
    (s : Fin (n+2) → S) (as : Fin (n+1) → Act) :
    stepCost (shPol d θs) (n+1) s as = stepCost (θs (s 1)) n (Fin.tail s) (Fin.tail as) := by
  unfold stepCost
  have : Fin.tail s (Fin.last n) = s (Fin.last (n+1)) := by simp [Fin.tail, Fin.succ_last]
  rw [this]; rfl

lemma expCost_shPol_zero (d : RandStationaryPolicy M) (θs : S → SennottDP.Discounted.Policy M) (i : S) :
    expCost (shPol d θs) i 0 = cst d i := by
  unfold expCost
  rw [← (Equiv.funUnique (Fin 1) S).symm.tsum_eq]
  rw [tsum_eq_single i]
  · simp [histProb, stepCost, shPol, shDist, cst]
  · intro b hb; simp [histProb, hb]

lemma tsum_diag {n : ℕ} {F : S → (Fin (n+1) → S) → ℝ≥0∞} (hF : ∀ j s', s' 0 ≠ j → F j s' = 0) :
    ∑' s', F (s' 0) s' = ∑' j, ∑' s', F j s' := by
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun s' => ?_)
  rw [tsum_eq_single (s' 0)]
  intro j hj; exact hF j s' (Ne.symm hj)

lemma expCost_shPol_succ (d : RandStationaryPolicy M) (θs : S → SennottDP.Discounted.Policy M) (i : S)
    (n : ℕ) : expCost (shPol d θs) i (n+1) = ∑' j, kerG d ∅ i j * expCost (θs j) j n := by
  unfold expCost
  rw [← (Fin.consEquiv (fun _ => S)).tsum_eq, ENNReal.tsum_prod']
  rw [tsum_eq_single i]
  · have e : ∀ s' : Fin (n+1) → S, (∑' as : Fin (n+1) → Act,
        histProb (shPol d θs) i (n+1) ((Fin.consEquiv (fun _ => S)) (i, s')) as *
          stepCost (shPol d θs) (n+1) ((Fin.consEquiv (fun _ => S)) (i, s')) as)
        = ∑' a, ∑' as' : Fin n → Act, d.dist i a * M.P i a (s' 0) *
            (histProb (θs (s' 0)) (s' 0) n s' as' * stepCost (θs (s' 0)) n s' as') := by
      intro s'
      rw [← (Fin.consEquiv (fun _ => Act)).tsum_eq, ENNReal.tsum_prod']
      refine tsum_congr (fun a => tsum_congr (fun as' => ?_))
      change histProb (shPol d θs) i (n+1) (Fin.cons i s') (Fin.cons a as') *
        stepCost (shPol d θs) (n+1) (Fin.cons i s') (Fin.cons a as') = _
      simp only [histProb_shPol, stepCost_shPol, Fin.tail_cons, Fin.cons_zero,
        Fin.cons_one, if_true, one_mul]
      ring
    simp_rw [e]
    rw [tsum_diag (F := fun j s' => ∑' a, ∑' as' : Fin n → Act, d.dist i a * M.P i a j *
            (histProb (θs j) j n s' as' * stepCost (θs j) n s' as'))]
    · refine tsum_congr (fun j => ?_)
      simp only [kerG, Set.mem_empty_iff_false, if_false]
      rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_right]
      refine tsum_congr (fun a => ?_)
      rw [← ENNReal.tsum_mul_left]
      refine tsum_congr (fun s' => ?_)
      rw [← ENNReal.tsum_mul_left]
    · intro j s' hj
      simp [histProb_ne_zero _ s' _ hj]
  · intro x hx
    refine ENNReal.tsum_eq_zero.2 (fun s' => ENNReal.tsum_eq_zero.2 (fun as => ?_))
    rw [histProb_ne_zero _ _ _ (by simpa using hx)]
    simp


lemma ennreal_tsum_succ (f : ℕ → ℝ≥0∞) : ∑' t, f t = f 0 + ∑' t, f (t+1) :=
  tsum_eq_zero_add' ENNReal.summable

lemma discCost_shPol (d : RandStationaryPolicy M) (θs : S → SennottDP.Discounted.Policy M) (α : ℝ)
    (i : S) : discCost (shPol d θs) α i =
      cst d i + ENNReal.ofReal α * ∑' j, kerG d ∅ i j * discCost (θs j) α j := by
  unfold discCost
  rw [ennreal_tsum_succ (fun t => ENNReal.ofReal α ^ t * expCost (shPol d θs) i t)]
  simp only [pow_zero, one_mul, expCost_shPol_zero, expCost_shPol_succ]
  congr 1
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun j => tsum_congr (fun n => ?_))
  ring

lemma valueFn_bellman (d : RandStationaryPolicy M) (α : ℝ) (hα1 : α ≤ 1) (i : S) :
    valueFn M α i ≤ cst d i + ENNReal.ofReal α * ∑' j, kerG d ∅ i j * valueFn M α j := by
  refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
  have hθ : ∀ j, ∃ θ : SennottDP.Discounted.Policy M, discCost θ α j ≤ valueFn M α j + ε := by
    intro j
    by_cases hV : valueFn M α j = ⊤
    · exact ⟨d.toPolicy, by rw [hV]; simp⟩
    · have : valueFn M α j < valueFn M α j + ε :=
        ENNReal.lt_add_right hV (by exact_mod_cast hε.ne')
      obtain ⟨θ, hθ⟩ := iInf_lt_iff.1 this
      exact ⟨θ, hθ.le⟩
  choose θs hθs using hθ
  have hr : ENNReal.ofReal α ≤ 1 := ENNReal.ofReal_le_one.2 hα1
  calc valueFn M α i ≤ discCost (shPol d θs) α i := iInf_le _ _
    _ = cst d i + ENNReal.ofReal α * ∑' j, kerG d ∅ i j * discCost (θs j) α j :=
        discCost_shPol d θs α i
    _ ≤ cst d i + ENNReal.ofReal α * ∑' j, kerG d ∅ i j * (valueFn M α j + ε) := by
        gcongr with j; exact hθs j
    _ ≤ cst d i + ENNReal.ofReal α * ∑' j, kerG d ∅ i j * valueFn M α j + ε := by
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, mul_add, add_assoc]
        gcongr
        calc ENNReal.ofReal α * ∑' j, kerG d ∅ i j * (ε : ℝ≥0∞)
            = ENNReal.ofReal α * ((∑' j, kerG d ∅ i j) * ε) := by rw [ENNReal.tsum_mul_right]
          _ ≤ 1 * (1 * ε) := by gcongr; exact kerG_sum_le d i
          _ = ε := by simp

lemma pw_mono (d : RandStationaryPolicy M) (z : S) :
    ∀ n i j, pw (kerG d {z}) n i j ≤ pw (kerG d ∅) n i j := by
  intro n
  induction n with
  | zero => intro i j; simp [pw]
  | succ n ih =>
    intro i j
    simp only [pw]
    gcongr with k
    · exact ih i k
    · rw [kerG_split d z k j]; exact le_self_add

lemma pw_add (p : S → S → ℝ≥0∞) (n : ℕ) : ∀ u i k,
    pw p (n+u) i k = ∑' j, pw p n i j * pw p u j k := by
  intro u
  induction u with
  | zero =>
    intro i k
    simp only [pw, Nat.add_zero]
    rw [tsum_eq_single k]
    · simp
    · intro j hj; simp [hj]
  | succ u ih =>
    intro i k
    rw [← Nat.add_assoc]
    simp only [pw]
    simp_rw [ih, ENNReal.tsum_mul_right.symm, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr (fun j => tsum_congr (fun l => ?_))
    ring

lemma sum_kerG_split (d : RandStationaryPolicy M) (z k : S) (V : S → ℝ≥0∞) :
    ∑' j, kerG d ∅ k j * V j = ∑' j, kerG d {z} k j * V j + kerG d ∅ k z * V z := by
  have e : ∀ j, kerG d ∅ k j * V j =
      kerG d {z} k j * V j + (if j = z then kerG d ∅ k z else 0) * V j := by
    intro j; rw [kerG_split d z k j, add_mul]
  rw [tsum_congr e, ENNReal.tsum_add]
  congr 1
  rw [tsum_eq_single z]
  · simp
  · intro j hj; simp [hj]

lemma pw_succ_sum (q : S → S → ℝ≥0∞) (n : ℕ) (i : S) (V : S → ℝ≥0∞) :
    ∑' j, pw q n i j * ∑' k, q j k * V k = ∑' k, pw q (n+1) i k * V k := by
  simp only [pw]
  simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun k => tsum_congr (fun j => ?_))
  ring

lemma iterate_bound (d : RandStationaryPolicy M) (z : S) (V : S → ℝ≥0∞) (r : ℝ≥0∞)
    (hB : ∀ k, V k ≤ cst d k + r * ∑' j, kerG d ∅ k j * V j) : ∀ n i,
    V i ≤ (∑ t ∈ Finset.range n, r^t * ∑' j, pw (kerG d {z}) t i j * cst d j) +
      (∑ t ∈ Finset.range n, r^(t+1) * ∑' j, pw (kerG d {z}) t i j * kerG d ∅ j z) * V z +
      r^n * ∑' j, pw (kerG d {z}) n i j * V j := by
  intro n
  induction n with
  | zero =>
    intro i
    simp only [Finset.range_zero, Finset.sum_empty, zero_mul, zero_add, pow_zero, one_mul, pw]
    rw [tsum_eq_single i]
    · simp
    · intro j hj; simp [Ne.symm hj]
  | succ n ih =>
    intro i
    refine (ih i).trans ?_
    have h1 : ∑' j, pw (kerG d {z}) n i j * V j ≤
        ∑' j, pw (kerG d {z}) n i j * cst d j +
          r * ∑' k, pw (kerG d {z}) (n+1) i k * V k +
          r * (∑' j, pw (kerG d {z}) n i j * kerG d ∅ j z) * V z := by
      calc ∑' j, pw (kerG d {z}) n i j * V j
          ≤ ∑' j, pw (kerG d {z}) n i j * (cst d j + r * (∑' k, kerG d {z} j k * V k +
              kerG d ∅ j z * V z)) := by
            gcongr with j
            rw [← sum_kerG_split]; exact hB j
        _ = _ := by
          have e : ∀ j, pw (kerG d {z}) n i j * (cst d j + r * (∑' k, kerG d {z} j k * V k +
              kerG d ∅ j z * V z)) = pw (kerG d {z}) n i j * cst d j +
              r * (pw (kerG d {z}) n i j * ∑' k, kerG d {z} j k * V k) +
              (r * V z) * (pw (kerG d {z}) n i j * kerG d ∅ j z) := by intro j; ring
          rw [tsum_congr e, ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_left,
            ENNReal.tsum_mul_left, pw_succ_sum]
          ring
    calc _ ≤ (∑ t ∈ Finset.range n, r^t * ∑' j, pw (kerG d {z}) t i j * cst d j) +
          (∑ t ∈ Finset.range n, r^(t+1) * ∑' j, pw (kerG d {z}) t i j * kerG d ∅ j z) * V z +
          r^n * (∑' j, pw (kerG d {z}) n i j * cst d j +
            r * ∑' k, pw (kerG d {z}) (n+1) i k * V k +
            r * (∑' j, pw (kerG d {z}) n i j * kerG d ∅ j z) * V z) := by gcongr
      _ = _ := by
          rw [Finset.sum_range_succ, Finset.sum_range_succ]
          ring


lemma hit_bound (d : RandStationaryPolicy M) (z i : S) : ∀ n,
    (∑ t ∈ Finset.range n, ∑' j, pw (kerG d {z}) t i j * kerG d ∅ j z) +
      ∑' j, pw (kerG d {z}) n i j ≤ 1 := by
  intro n
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_add, pw]
    rw [tsum_eq_single i]
    · simp
    · intro j hj; simp [Ne.symm hj]
  | succ n ih =>
    refine le_trans ?_ ih
    rw [Finset.sum_range_succ, add_assoc]
    gcongr
    have e1 : ∑' k, pw (kerG d {z}) (n+1) i k =
        ∑' j, pw (kerG d {z}) n i j * ∑' k, kerG d {z} j k := by
      have := pw_succ_sum (kerG d {z}) n i (fun _ => 1)
      simpa using this.symm
    rw [e1, ← ENNReal.tsum_add]
    calc ∑' j, (pw (kerG d {z}) n i j * kerG d ∅ j z + pw (kerG d {z}) n i j * ∑' k, kerG d {z} j k)
        = ∑' j, pw (kerG d {z}) n i j * ∑' k, kerG d ∅ j k := by
          refine tsum_congr (fun j => ?_)
          have := sum_kerG_split d z j (fun _ => 1)
          simp only [mul_one] at this
          rw [this]; ring
      _ ≤ ∑' j, pw (kerG d {z}) n i j * 1 := by gcongr with j; exact kerG_sum_le d j
      _ = ∑' j, pw (kerG d {z}) n i j := by simp

lemma valueFn_le_passage (d : RandStationaryPolicy M) (z : S) (hd : IsZStandard d.toPolicy z)
    (α : ℝ) (hα1 : α < 1) (i : S) :
    valueFn M α i ≤ passageCost d.toPolicy i {z} + valueFn M α z := by
  have hr1 : ENNReal.ofReal α < 1 := ENNReal.ofReal_lt_one.2 hα1
  have hB := iterate_bound d z (valueFn M α) (ENNReal.ofReal α)
    (fun k => valueFn_bellman d α hα1.le k)
  set r := ENNReal.ofReal α with hr_def
  set V := valueFn M α with hV_def
  set f : ℕ → ℝ≥0∞ := fun t => r^t * expCost d.toPolicy i t with hf_def
  have hf : ∑' t, f t ≠ ⊤ := by
    have hK := (hd z).2
    have hle : ∑' t, f t ≤ ∑' t, ((∑' j, pw (kerG d {z}) t i j * cst d j) +
          passageCost d.toPolicy z {z} * r^t) := by
      refine ENNReal.tsum_le_tsum (fun t => ?_)
      calc r^t * expCost d.toPolicy i t
          ≤ r^t * ((∑' j, pw (kerG d {z}) t i j * cst d j) + passageCost d.toPolicy z {z}) := by
            gcongr; exact expCost_le_mc d z i t
        _ ≤ _ := by
            rw [mul_add]
            exact add_le_add (mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le hr1.le))
              (le_of_eq (mul_comm _ _))
    have heq : ∑' t, ((∑' j, pw (kerG d {z}) t i j * cst d j) +
          passageCost d.toPolicy z {z} * r^t) =
        passageCost d.toPolicy i {z} + passageCost d.toPolicy z {z} * (1 - r)⁻¹ := by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ← passageCost_eq_mc d i {z}]
    refine ne_top_of_le_ne_top ?_ (hle.trans heq.le)
    refine ENNReal.add_ne_top.2 ⟨(hd i).2.ne, ENNReal.mul_ne_top hK.ne ?_⟩
    exact ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr1).ne'
  have hn : ∀ n, V i ≤ passageCost d.toPolicy i {z} + V z + ∑' u, f (u + n) := by
    intro n
    refine (hB n i).trans ?_
    gcongr ?_ + ?_ + ?_
    · calc ∑ t ∈ Finset.range n, r^t * ∑' j, pw (kerG d {z}) t i j * cst d j
          ≤ ∑ t ∈ Finset.range n, ∑' j, pw (kerG d {z}) t i j * cst d j :=
            Finset.sum_le_sum (fun t _ => mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le hr1.le))
        _ ≤ ∑' t, ∑' j, pw (kerG d {z}) t i j * cst d j := ENNReal.sum_le_tsum _
        _ = _ := (passageCost_eq_mc d i {z}).symm
    · refine mul_le_of_le_one_left zero_le ?_
      calc ∑ t ∈ Finset.range n, r^(t+1) * ∑' j, pw (kerG d {z}) t i j * kerG d ∅ j z
          ≤ ∑ t ∈ Finset.range n, ∑' j, pw (kerG d {z}) t i j * kerG d ∅ j z :=
            Finset.sum_le_sum (fun t _ => mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le hr1.le))
        _ ≤ _ := le_self_add
        _ ≤ 1 := hit_bound d z i n
    · calc r^n * ∑' j, pw (kerG d {z}) n i j * V j
          ≤ r^n * ∑' j, pw (kerG d ∅) n i j *
              ∑' u, r^u * ∑' k, pw (kerG d ∅) u j k * cst d k := by
            gcongr with j
            · exact pw_mono d z n i j
            · calc V j ≤ discCost d.toPolicy α j := iInf_le _ _
                _ = _ := by unfold discCost; simp_rw [expCost_eq_mc]; rfl
        _ = ∑' u, f (u + n) := by
            simp only [hf_def, expCost_eq_mc]
            simp_rw [add_comm _ n, pw_add, pow_add]
            simp_rw [ENNReal.tsum_mul_right.symm, ← ENNReal.tsum_mul_left]
            rw [ENNReal.tsum_comm]
            refine tsum_congr (fun u => ?_)
            rw [ENNReal.tsum_comm]
            refine tsum_congr (fun k => tsum_congr (fun j => ?_))
            ring
  have hlim : Tendsto (fun n => passageCost d.toPolicy i {z} + V z + ∑' u, f (u + n)) atTop
      (𝓝 (passageCost d.toPolicy i {z} + V z)) := by
    simpa using (tendsto_const_nhds (x := passageCost d.toPolicy i {z} + V z)).add
      (ENNReal.tendsto_sum_nat_add f hf)
  exact ge_of_tendsto' hlim hn

end shift


lemma valueFn_z_le {S Act : Type} [Countable S] {M : SennottDP.Discounted.MDC S Act}
    (d : RandStationaryPolicy M) (z : S) (α : ℝ) :
    valueFn M α z ≤ 2 * passageCost d.toPolicy z {z} * (1 - ENNReal.ofReal α)⁻¹ := by
  refine (iInf_le _ d.toPolicy).trans ?_
  unfold discCost
  calc ∑' t, ENNReal.ofReal α ^ t * expCost d.toPolicy z t
      ≤ ∑' t, ENNReal.ofReal α ^ t * (2 * passageCost d.toPolicy z {z}) :=
        ENNReal.tsum_le_tsum (fun t => by gcongr; exact expCost_z_le d z t)
    _ = _ := by rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, mul_comm]

lemma one_sub_ofReal' {α : ℝ} (hα0 : 0 < α) : 1 - ENNReal.ofReal α = ENNReal.ofReal (1 - α) := by
  rw [ENNReal.ofReal_sub 1 hα0.le, ENNReal.ofReal_one]

lemma valueFn_z_ne_top {S Act : Type} [Countable S] {M : SennottDP.Discounted.MDC S Act}
    (d : RandStationaryPolicy M) (z : S) (hd : IsZStandard d.toPolicy z) (α : ℝ) (hα0 : 0 < α)
    (hα1 : α < 1) : valueFn M α z ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (valueFn_z_le d z α)
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (hd z).2.ne) ?_
  rw [one_sub_ofReal' hα0]
  exact ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (by linarith)).ne'

lemma sen1_of_standard {S Act : Type} [Countable S] {M : SennottDP.Discounted.MDC S Act}
    (d : RandStationaryPolicy M) (z : S) (hd : IsZStandard d.toPolicy z) : SEN1 M z := by
  have hK : 2 * passageCost d.toPolicy z {z} ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) (hd z).2.ne
  refine ⟨(2 * passageCost d.toPolicy z {z}).toNNReal, fun α hα0 hα1 => ?_⟩
  rw [ENNReal.coe_toNNReal hK]
  calc ENNReal.ofReal (1 - α) * valueFn M α z
      ≤ ENNReal.ofReal (1 - α) * (2 * passageCost d.toPolicy z {z} * (1 - ENNReal.ofReal α)⁻¹) := by
        gcongr; exact valueFn_z_le d z α
    _ = 2 * passageCost d.toPolicy z {z} := by
        rw [one_sub_ofReal' hα0, mul_comm, mul_assoc,
          ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 (by linarith)).ne' ENNReal.ofReal_ne_top,
          mul_one]

lemma relValue_le_std {S Act : Type} [Countable S] {M : SennottDP.Discounted.MDC S Act}
    (d : RandStationaryPolicy M) (z : S) (hd : IsZStandard d.toPolicy z) (α : ℝ) (hα1 : α < 1)
    (i : S) : relValue M z α i ≤ ((passageCost d.toPolicy i {z}).toReal : EReal) := by
  unfold relValue
  by_cases hz : valueFn M α z = ⊤
  · rw [hz]; simp [EReal.sub_top]
  have h := valueFn_le_passage d z hd α hα1 i
  have hc := (hd i).2.ne
  have hi : valueFn M α i ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hc, hz⟩) h
  rw [← EReal.coe_ennreal_toReal hi, ← EReal.coe_ennreal_toReal hz, ← EReal.coe_sub,
    EReal.coe_le_coe_iff]
  have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hc, hz⟩) h
  rw [ENNReal.toReal_add hc hz] at this
  linarith

theorem sen12_of_standard_core {S Act : Type} [Countable S] (M : SennottDP.Discounted.MDC S Act) (z : S)
    (hd : ∃ d : RandStationaryPolicy M, IsZStandard d.toPolicy z) :
    SEN1 M z ∧ ∃ Mf : S → ℝ, SEN2 M z Mf := by
  obtain ⟨d, hd⟩ := hd
  exact ⟨sen1_of_standard d z hd, fun i => (passageCost d.toPolicy i {z}).toReal,
    fun i => ENNReal.toReal_nonneg, fun α _ hα1 i => relValue_le_std d z hd α hα1 i⟩

lemma ereal_sub_nonneg' {a b : ℝ≥0∞} (hb : b ≠ ⊤) (h : b ≤ a) : (0 : EReal) ≤ (a : EReal) - b := by
  by_cases ha : a = ⊤
  · rw [ha, ← EReal.coe_ennreal_toReal hb]; simp
  · rw [← EReal.coe_ennreal_toReal ha, ← EReal.coe_ennreal_toReal hb, ← EReal.coe_sub]
    exact_mod_cast sub_nonneg.2 (ENNReal.toReal_mono ha h)

theorem sen_of_monotone_value_core {Act : Type} (M : SennottDP.Discounted.MDC ℕ Act)
    (hmono : ∀ α : ℝ, 0 < α → α < 1 → Monotone (valueFn M α))
    (hd : ∃ d : RandStationaryPolicy M, IsZStandard d.toPolicy 0) :
    SEN M 0 ∧ ∀ h : ℕ → ℝ, IsLimitFunction M 0 h → (∀ i, 0 ≤ h i) ∧ Monotone h := by
  obtain ⟨d, hd'⟩ := hd
  have hnn : ∀ α : ℝ, 0 < α → α < 1 → ∀ i, (0 : EReal) ≤ relValue M 0 α i := fun α h0 h1 i =>
    ereal_sub_nonneg' (valueFn_z_ne_top d 0 hd' α h0 h1) (hmono α h0 h1 (Nat.zero_le i))
  have hmo : ∀ α : ℝ, 0 < α → α < 1 → Monotone (relValue M 0 α) := fun α h0 h1 i j hij =>
    EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.2 (hmono α h0 h1 hij)) le_rfl
  obtain ⟨_, Mf, hMf⟩ := sen12_of_standard_core M 0 ⟨d, hd'⟩
  refine ⟨⟨Mf, 0, sen1_of_standard d 0 hd', hMf, le_rfl, fun α h0 h1 i => by simpa using hnn α h0 h1 i⟩,
    fun h hh => ?_⟩
  obtain ⟨β, hβ, _, hlim⟩ := hh.2
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · have : (0 : EReal) ≤ (h i : EReal) :=
      ge_of_tendsto' (hlim i) (fun n => hnn (β n) (hβ n).1 (hβ n).2 i)
    exact_mod_cast this
  · have : (h i : EReal) ≤ (h j : EReal) :=
      le_of_tendsto_of_tendsto' (hlim i) (hlim j) (fun n => hmo (β n) (hβ n).1 (hβ n).2 hij)
    exact_mod_cast this

end SennottDP.BOR

open SennottDP.BOR


theorem solution {Act : Type} (M : SennottDP.Discounted.MDC ℕ Act)
    (hmono : ∀ α : ℝ, 0 < α → α < 1 → Monotone (valueFn M α))
    (hd : ∃ d : RandStationaryPolicy M, IsZStandard d.toPolicy 0) :
    SEN M 0 ∧ ∀ h : ℕ → ℝ, IsLimitFunction M 0 h → (∀ i, 0 ≤ h i) ∧ Monotone h := by
  exact sen_of_monotone_value_core M hmono hd
