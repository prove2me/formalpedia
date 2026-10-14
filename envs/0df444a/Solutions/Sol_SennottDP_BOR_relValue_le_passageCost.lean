-- Prove2me | solution 1 for SennottDP.BOR.relValue_le_passageCost
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T02:32:35.026905+00:00
-- url     : https://prove2.me/submissions/1ff0cebc-3be4-4a9d-8924-f074bfafcf2b

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


section concat
variable {S : Type} [Countable S] {Act : Type} {M : SennottDP.Discounted.MDC S Act}

noncomputable def pol0 (θ : SennottDP.Discounted.Policy M) (i : S) (a : Act) : ℝ≥0∞ :=
  θ.dist 0 (fun _ => i) Fin.elim0 a

lemma cons_last' {n : ℕ} {β : Type} (x : β) (s : Fin (n+1) → β) :
    (Fin.cons x s : Fin (n+2) → β) (Fin.last (n+1)) = s (Fin.last n) := by
  rw [← Fin.succ_last, Fin.cons_succ]

noncomputable def cont (θ : SennottDP.Discounted.Policy M) (i : S) (a : Act) :
    SennottDP.Discounted.Policy M where
  dist m s as b := θ.dist (m+1) (Fin.cons i s) (Fin.cons a as) b
  dist_supp m s as b hb := θ.dist_supp _ _ _ b (by rw [cons_last']; exact hb)
  dist_sum m s as := by
    have := θ.dist_sum (m+1) (Fin.cons i s) (Fin.cons a as)
    rwa [cons_last'] at this

lemma pol0_supp (θ : SennottDP.Discounted.Policy M) (i : S) (a : Act) (ha : a ∉ M.A i) :
    pol0 θ i a = 0 := θ.dist_supp 0 _ _ a ha

lemma pol0_sum (θ : SennottDP.Discounted.Policy M) (i : S) : ∑ a ∈ M.A i, pol0 θ i a = 1 :=
  θ.dist_sum 0 (fun _ => i) Fin.elim0

lemma init_one {β : Type} (s : Fin 2 → β) : (Fin.init s : Fin 1 → β) = fun _ => s 0 := by
  funext k; rw [Fin.fin_one_eq_zero k]; rfl

lemma histProb_cont (θ : SennottDP.Discounted.Policy M) (i : S) :
    ∀ n (s : Fin (n+2) → S) (as : Fin (n+1) → Act),
    histProb θ i (n+1) s as =
      (if s 0 = i then 1 else 0) * pol0 θ (s 0) (as 0) * M.P (s 0) (as 0) (s 1) *
        histProb (cont θ (s 0) (as 0)) (s 1) n (Fin.tail s) (Fin.tail as) := by
  intro n
  induction n with
  | zero =>
    intro s as
    by_cases h : s 0 = i
    · have h' : Fin.init s 0 = i := by simpa [Fin.init] using h
      have ea : (Fin.init as : Fin 0 → Act) = Fin.elim0 := Subsingleton.elim _ _
      simp only [histProb, h', if_true, h, one_mul, Fin.tail, pol0]
      rw [init_one, ea]
      simp
      rw [h]
    · rw [histProb_ne_zero _ s as h]; simp [h]
  | succ n ih =>
    intro s as
    by_cases h : s 0 = i
    · have h' : Fin.init s 0 = i := by simpa [Fin.init] using h
      rw [histProb, ih (Fin.init s) (Fin.init as), if_pos h', if_pos h]
      conv_rhs => rw [histProb]
      have e1 : Fin.init s 0 = s 0 := rfl
      have e2 : Fin.init s 1 = s 1 := rfl
      have e3 : Fin.init as 0 = as 0 := rfl
      have e4 : Fin.tail as (Fin.last n) = as (Fin.last (n+1)) := by simp [Fin.tail, Fin.succ_last]
      have e5 : Fin.tail s (Fin.last n).castSucc = s (Fin.last (n+1)).castSucc := by
        simp [Fin.tail, Fin.succ_castSucc, Fin.succ_last]
      have e6 : Fin.tail s (Fin.last (n+1)) = s (Fin.last (n+1+1)) := by simp [Fin.tail, Fin.succ_last]
      have e7 : θ.dist (n+1) (Fin.init s) (Fin.init as) (as (Fin.last (n+1))) =
          (cont θ (s 0) (as 0)).dist n (Fin.init (Fin.tail s)) (Fin.init (Fin.tail as))
            (as (Fin.last (n+1))) := by
        simp only [cont]
        rw [← Fin.tail_init_eq_init_tail, ← Fin.tail_init_eq_init_tail, ← e1, ← e3,
          Fin.cons_self_tail, Fin.cons_self_tail]
      rw [e7, e1, e2, e3, e4, e5, e6, Fin.tail_init_eq_init_tail, Fin.tail_init_eq_init_tail]
      ring
    · rw [histProb_ne_zero _ s as h, if_neg h]
      simp


lemma gen_succ (θ : SennottDP.Discounted.Policy M) (i : S) (n : ℕ)
    (F : S → Act → (Fin (n+1) → S) → (Fin n → Act) → ℝ≥0∞) :
    ∑' s : Fin (n+2) → S, ∑' as : Fin (n+1) → Act,
      histProb θ i (n+1) s as * F (s 0) (as 0) (Fin.tail s) (Fin.tail as) =
    ∑' a, pol0 θ i a * ∑' j, M.P i a j * ∑' s' : Fin (n+1) → S, ∑' as' : Fin n → Act,
      histProb (cont θ i a) j n s' as' * F i a s' as' := by
  rw [← (Fin.consEquiv (fun _ => S)).tsum_eq, ENNReal.tsum_prod']
  rw [tsum_eq_single i]
  · have e : ∀ s' : Fin (n+1) → S, (∑' as : Fin (n+1) → Act,
        histProb θ i (n+1) ((Fin.consEquiv (fun _ => S)) (i, s')) as *
          F (((Fin.consEquiv (fun _ => S)) (i, s')) 0) (as 0)
            (Fin.tail ((Fin.consEquiv (fun _ => S)) (i, s'))) (Fin.tail as))
        = ∑' a, ∑' as' : Fin n → Act, pol0 θ i a * M.P i a (s' 0) *
            (histProb (cont θ i a) (s' 0) n s' as' * F i a s' as') := by
      intro s'
      rw [← (Fin.consEquiv (fun _ => Act)).tsum_eq, ENNReal.tsum_prod']
      refine tsum_congr (fun a => tsum_congr (fun as' => ?_))
      change histProb θ i (n+1) (Fin.cons i s') (Fin.cons a as') *
        F ((Fin.cons i s' : Fin (n+2) → S) 0) ((Fin.cons a as' : Fin (n+1) → Act) 0)
          (Fin.tail (Fin.cons i s' : Fin (n+2) → S)) (Fin.tail (Fin.cons a as' : Fin (n+1) → Act)) = _
      simp only [histProb_cont, Fin.tail_cons, Fin.cons_zero, Fin.cons_one, if_true, one_mul]
      ring
    simp_rw [e]
    rw [tsum_diag (F := fun j s' => ∑' a, ∑' as' : Fin n → Act, pol0 θ i a * M.P i a j *
            (histProb (cont θ i a) j n s' as' * F i a s' as'))]
    · conv_lhs => enter [1, j]; rw [ENNReal.tsum_comm]
      rw [ENNReal.tsum_comm]
      refine tsum_congr (fun a => ?_)
      simp_rw [← ENNReal.tsum_mul_left]
      refine tsum_congr (fun j => tsum_congr (fun s' => tsum_congr (fun as' => ?_)))
      ring
    · intro j s' hj
      simp [histProb_ne_zero _ s' _ hj]
  · intro x hx
    refine ENNReal.tsum_eq_zero.2 (fun s' => ENNReal.tsum_eq_zero.2 (fun as => ?_))
    rw [histProb_ne_zero _ _ _ (by simpa using hx)]
    simp

lemma stepCost_cont (θ : SennottDP.Discounted.Policy M) (n : ℕ) (s : Fin (n+2) → S)
    (as : Fin (n+1) → Act) :
    stepCost θ (n+1) s as = stepCost (cont θ (s 0) (as 0)) n (Fin.tail s) (Fin.tail as) := by
  unfold stepCost
  have : Fin.tail s (Fin.last n) = s (Fin.last (n+1)) := by simp [Fin.tail, Fin.succ_last]
  rw [this]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [cont]
  rw [Fin.cons_self_tail, Fin.cons_self_tail]

lemma expCost_zero_gen (θ : SennottDP.Discounted.Policy M) (i : S) :
    expCost θ i 0 = ∑ a ∈ M.A i, pol0 θ i a * (M.C i a : ℝ≥0∞) := by
  unfold expCost
  rw [← (Equiv.funUnique (Fin 1) S).symm.tsum_eq]
  rw [tsum_eq_single i]
  · simp only [histProb, stepCost, pol0]
    have ea : ∀ as : Fin 0 → Act, as = Fin.elim0 := fun as => Subsingleton.elim _ _
    simp [ea]
    rfl
  · intro b hb; simp [histProb, hb]

lemma expCost_succ_gen (θ : SennottDP.Discounted.Policy M) (i : S) (n : ℕ) :
    expCost θ i (n+1) = ∑' a, pol0 θ i a * ∑' j, M.P i a j * expCost (cont θ i a) j n := by
  unfold expCost
  have := gen_succ θ i n (fun x a s' as' => stepCost (cont θ x a) n s' as')
  rw [← this]
  simp_rw [stepCost_cont]

noncomputable def pcT (z : S) (θ : SennottDP.Discounted.Policy M) (i : S) (t : ℕ) : ℝ≥0∞ :=
  ∑' s : Fin (t + 1) → S, ∑' as : Fin t → Act,
    if (∀ k : Fin (t + 1), 1 ≤ k.val → s k ∉ ({z} : Set S)) then histProb θ i t s as * stepCost θ t s as
    else 0

lemma passageCost_eq_pcT (z : S) (θ : SennottDP.Discounted.Policy M) (i : S) :
    passageCost θ i {z} = ∑' t, pcT z θ i t := rfl

lemma pcT_zero (z : S) (θ : SennottDP.Discounted.Policy M) (i : S) :
    pcT z θ i 0 = expCost θ i 0 := by
  unfold pcT expCost
  refine tsum_congr (fun s => tsum_congr (fun as => ?_))
  rw [if_pos]
  intro k hk; exact absurd hk (by have := k.2; omega)

lemma pcT_succ (z : S) (θ : SennottDP.Discounted.Policy M) (i : S) (n : ℕ) :
    pcT z θ i (n+1) = ∑' a, pol0 θ i a * ∑' j, (if j = z then 0 else
      M.P i a j * pcT z (cont θ i a) j n) := by
  unfold pcT
  have := gen_succ θ i n (fun x a s' as' =>
    if (s' 0 ≠ z ∧ ∀ k : Fin (n + 1), 1 ≤ k.val → s' k ∉ ({z} : Set S)) then
      stepCost (cont θ x a) n s' as' else 0)
  have e : ∀ (s : Fin (n+2) → S) (as : Fin (n+1) → Act),
      (if (∀ k : Fin (n + 2), 1 ≤ k.val → s k ∉ ({z} : Set S)) then
        histProb θ i (n+1) s as * stepCost θ (n+1) s as else 0) =
      histProb θ i (n+1) s as * (if (Fin.tail s 0 ≠ z ∧ ∀ k : Fin (n + 1), 1 ≤ k.val →
        Fin.tail s k ∉ ({z} : Set S)) then
          stepCost (cont θ (s 0) (as 0)) n (Fin.tail s) (Fin.tail as) else 0) := by
    intro s as
    have hc : (∀ k : Fin (n + 2), 1 ≤ k.val → s k ∉ ({z} : Set S)) ↔
        (Fin.tail s 0 ≠ z ∧ ∀ k : Fin (n + 1), 1 ≤ k.val → Fin.tail s k ∉ ({z} : Set S)) := by
      constructor
      · intro h
        refine ⟨?_, fun k _ => ?_⟩
        · have := h 1 (by simp); simpa [Fin.tail] using this
        · have := h k.succ (by simp); simpa [Fin.tail] using this
      · rintro ⟨h1, h2⟩ k hk
        induction k using Fin.cases with
        | zero => simp at hk
        | succ k =>
          by_cases hk0 : k.val = 0
          · have : k = 0 := Fin.ext hk0
            subst this; simpa [Fin.tail] using h1
          · have := h2 k (by omega); simpa [Fin.tail] using this
    by_cases h : (∀ k : Fin (n + 2), 1 ≤ k.val → s k ∉ ({z} : Set S))
    · rw [if_pos h, if_pos (hc.1 h), stepCost_cont]
    · rw [if_neg h, if_neg (fun h' => h (hc.2 h')), mul_zero]
  simp_rw [e]
  rw [this]
  refine tsum_congr (fun a => ?_)
  congr 1
  refine tsum_congr (fun j => ?_)
  by_cases hj : j = z
  · rw [if_pos hj]
    refine mul_eq_zero_of_right _ (ENNReal.tsum_eq_zero.2 (fun s' => ENNReal.tsum_eq_zero.2 (fun as' => ?_)))
    by_cases h0 : s' 0 = j
    · rw [if_neg (by rw [h0, hj]; simp)]; simp
    · rw [histProb_ne_zero _ _ _ h0]; simp
  · rw [if_neg hj]
    congr 1
    refine tsum_congr (fun s' => tsum_congr (fun as' => ?_))
    by_cases h0 : s' 0 = j
    · by_cases hc : (∀ k : Fin (n + 1), 1 ≤ k.val → s' k ∉ ({z} : Set S))
      · rw [if_pos ⟨by rw [h0]; exact hj, hc⟩, if_pos hc]
      · rw [if_neg (fun h' => hc h'.2), if_neg hc, mul_zero]
    · rw [histProb_ne_zero _ _ _ h0]; simp


lemma pol_ext {θ₁ θ₂ : SennottDP.Discounted.Policy M} (h : θ₁.dist = θ₂.dist) : θ₁ = θ₂ := by
  cases θ₁; cases θ₂; simp only at h; subst h; rfl

noncomputable def cdist (θ' : SennottDP.Discounted.Policy M) (z : S) : (n : ℕ) →
    SennottDP.Discounted.Policy M → (Fin (n+1) → S) → (Fin n → Act) → Act → ℝ≥0∞
  | 0, θ, s, as, a => if s 0 = z then θ'.dist 0 s as a else θ.dist 0 s as a
  | n+1, θ, s, as, a => if s 0 = z then θ'.dist (n+1) s as a else
      cdist θ' z n (cont θ (s 0) (as 0)) (Fin.tail s) (Fin.tail as) a

lemma cdist_supp (θ' : SennottDP.Discounted.Policy M) (z : S) : ∀ n θ s as a,
    a ∉ M.A (s (Fin.last n)) → cdist θ' z n θ s as a = 0 := by
  intro n
  induction n with
  | zero =>
    intro θ s as a ha
    simp only [cdist]
    split_ifs
    · exact θ'.dist_supp _ _ _ _ ha
    · exact θ.dist_supp _ _ _ _ ha
  | succ n ih =>
    intro θ s as a ha
    simp only [cdist]
    split_ifs
    · exact θ'.dist_supp _ _ _ _ ha
    · apply ih
      simpa [Fin.tail, Fin.succ_last] using ha

lemma cdist_sum (θ' : SennottDP.Discounted.Policy M) (z : S) : ∀ n θ s as,
    ∑ a ∈ M.A (s (Fin.last n)), cdist θ' z n θ s as a = 1 := by
  intro n
  induction n with
  | zero =>
    intro θ s as
    simp only [cdist]
    split_ifs
    · exact θ'.dist_sum _ _ _
    · exact θ.dist_sum _ _ _
  | succ n ih =>
    intro θ s as
    simp only [cdist]
    split_ifs
    · exact θ'.dist_sum _ _ _
    · have := ih (cont θ (s 0) (as 0)) (Fin.tail s) (Fin.tail as)
      simpa [Fin.tail, Fin.succ_last] using this

noncomputable def concat0 (θ' : SennottDP.Discounted.Policy M) (z : S)
    (θ : SennottDP.Discounted.Policy M) : SennottDP.Discounted.Policy M where
  dist n s as a := cdist θ' z n θ s as a
  dist_supp n s as a ha := cdist_supp θ' z n θ s as a ha
  dist_sum n s as := cdist_sum θ' z n θ s as

noncomputable def c1dist (θ' : SennottDP.Discounted.Policy M) (z : S) (θ : SennottDP.Discounted.Policy M) :
    (n : ℕ) → (Fin (n+1) → S) → (Fin n → Act) → Act → ℝ≥0∞
  | 0, s, as, a => θ.dist 0 s as a
  | n+1, s, as, a => cdist θ' z n (cont θ (s 0) (as 0)) (Fin.tail s) (Fin.tail as) a

noncomputable def concat1 (θ' : SennottDP.Discounted.Policy M) (z : S)
    (θ : SennottDP.Discounted.Policy M) : SennottDP.Discounted.Policy M where
  dist n s as a := c1dist θ' z θ n s as a
  dist_supp n s as a ha := by
    cases n with
    | zero => exact θ.dist_supp _ _ _ _ ha
    | succ n => exact cdist_supp θ' z n _ _ _ a (by simpa [Fin.tail, Fin.succ_last] using ha)
  dist_sum n s as := by
    cases n with
    | zero => exact θ.dist_sum _ _ _
    | succ n =>
      have := cdist_sum θ' z n (cont θ (s 0) (as 0)) (Fin.tail s) (Fin.tail as)
      simpa [Fin.tail, Fin.succ_last, c1dist] using this

lemma concat0_pol0 (θ' : SennottDP.Discounted.Policy M) (z : S) (θ : SennottDP.Discounted.Policy M)
    (i : S) (hi : i ≠ z) (a : Act) : pol0 (concat0 θ' z θ) i a = pol0 θ i a := by
  simp [pol0, concat0, cdist, hi]

lemma concat0_cont (θ' : SennottDP.Discounted.Policy M) (z : S) (θ : SennottDP.Discounted.Policy M)
    (i : S) (hi : i ≠ z) (a : Act) : cont (concat0 θ' z θ) i a = concat0 θ' z (cont θ i a) := by
  apply pol_ext
  funext m s as b
  simp [cont, concat0, cdist, hi]

lemma concat1_pol0 (θ' : SennottDP.Discounted.Policy M) (z : S) (θ : SennottDP.Discounted.Policy M)
    (i : S) (a : Act) : pol0 (concat1 θ' z θ) i a = pol0 θ i a := rfl

lemma concat1_cont (θ' : SennottDP.Discounted.Policy M) (z : S) (θ : SennottDP.Discounted.Policy M)
    (i : S) (a : Act) : cont (concat1 θ' z θ) i a = concat0 θ' z (cont θ i a) := by
  apply pol_ext
  funext m s as b
  simp [cont, concat0, concat1, c1dist]

lemma histProb_congr {θ₁ θ₂ : SennottDP.Discounted.Policy M} {z : S}
    (h : ∀ n s as, s 0 = z → θ₁.dist n s as = θ₂.dist n s as) :
    ∀ n s as, histProb θ₁ z n s as = histProb θ₂ z n s as := by
  intro n
  induction n with
  | zero => intro s as; rfl
  | succ n ih =>
    intro s as
    by_cases h0 : s 0 = z
    · simp only [histProb]
      rw [ih, h n _ _ (by simpa [Fin.init] using h0)]
    · rw [histProb_ne_zero _ _ _ h0, histProb_ne_zero _ _ _ h0]

lemma expCost_congr {θ₁ θ₂ : SennottDP.Discounted.Policy M} {z : S}
    (h : ∀ n s as, s 0 = z → θ₁.dist n s as = θ₂.dist n s as) (t : ℕ) :
    expCost θ₁ z t = expCost θ₂ z t := by
  unfold expCost
  refine tsum_congr (fun s => tsum_congr (fun as => ?_))
  by_cases h0 : s 0 = z
  · rw [histProb_congr h]
    unfold stepCost
    rw [h t s as h0]
  · rw [histProb_ne_zero _ _ _ h0, histProb_ne_zero _ _ _ h0]; simp

lemma concat0_at_z (θ' : SennottDP.Discounted.Policy M) (z : S) (θ : SennottDP.Discounted.Policy M)
    (t : ℕ) : expCost (concat0 θ' z θ) z t = expCost θ' z t := by
  apply expCost_congr
  intro n s as h0
  funext a
  cases n with
  | zero => simp [concat0, cdist, h0]
  | succ n => simp [concat0, cdist, h0]


lemma fsum_tsum {ι β : Type*} (s : Finset ι) (f : ι → β → ℝ≥0∞) :
    ∑ i ∈ s, ∑' b, f i b = ∑' b, ∑ i ∈ s, f i b :=
  (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm

lemma pol0_P_sum (θ : SennottDP.Discounted.Policy M) (i : S) :
    ∑' a, pol0 θ i a * ∑' j, M.P i a j = 1 := by
  rw [tsum_eq_sum (s := M.A i)]
  · rw [← pol0_sum θ i]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [M.P_sum i a ha, mul_one]
  · intro a ha; simp [pol0_supp θ i a ha]

lemma step_bound (θ' : SennottDP.Discounted.Policy M) (z : S) (α : ℝ) (hα : α ≤ 1) (N : ℕ)
    (IH : ∀ θ j, ∑ t ∈ Finset.range N, ENNReal.ofReal α ^ t * expCost (concat0 θ' z θ) j t ≤
      (if j = z then 0 else ∑ t ∈ Finset.range N, pcT z θ j t) + discCost θ' α z)
    (η θ : SennottDP.Discounted.Policy M) (i : S) (h0 : ∀ a, pol0 η i a = pol0 θ i a)
    (hc : ∀ a, cont η i a = concat0 θ' z (cont θ i a)) :
    ∑ t ∈ Finset.range (N+1), ENNReal.ofReal α ^ t * expCost η i t ≤
      ∑ t ∈ Finset.range (N+1), pcT z θ i t + discCost θ' α z := by
  set r := ENNReal.ofReal α with hr
  have hr1 : r ≤ 1 := ENNReal.ofReal_le_one.2 hα
  set V' := discCost θ' α z
  have e0 : expCost η i 0 = pcT z θ i 0 := by
    rw [pcT_zero, expCost_zero_gen, expCost_zero_gen]
    simp_rw [h0]
  have e1 : ∑ t ∈ Finset.range N, r^(t+1) * expCost η i (t+1) =
      r * ∑' a, pol0 θ i a * ∑' j, M.P i a j *
        ∑ t ∈ Finset.range N, r^t * expCost (concat0 θ' z (cont θ i a)) j t := by
    simp_rw [expCost_succ_gen, h0, hc]
    simp_rw [Finset.mul_sum, ← ENNReal.tsum_mul_left, fsum_tsum]
    refine tsum_congr (fun a => tsum_congr (fun j => ?_))
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    ring
  have e2 : ∑ t ∈ Finset.range N, pcT z θ i (t+1) =
      ∑' a, pol0 θ i a * ∑' j, (if j = z then 0 else
        M.P i a j * ∑ t ∈ Finset.range N, pcT z (cont θ i a) j t) := by
    simp_rw [pcT_succ]
    rw [fsum_tsum]
    refine tsum_congr (fun a => ?_)
    rw [← Finset.mul_sum, fsum_tsum]
    congr 1
    refine tsum_congr (fun j => ?_)
    split_ifs
    · simp
    · rw [Finset.mul_sum]
  rw [Finset.sum_range_succ', Finset.sum_range_succ', e1, e2, pow_zero, one_mul, e0]
  calc r * ∑' a, pol0 θ i a * ∑' j, M.P i a j *
        ∑ t ∈ Finset.range N, r^t * expCost (concat0 θ' z (cont θ i a)) j t + pcT z θ i 0
      ≤ ∑' a, pol0 θ i a * ∑' j, M.P i a j *
        ((if j = z then 0 else ∑ t ∈ Finset.range N, pcT z (cont θ i a) j t) + V') + pcT z θ i 0 := by
        gcongr ?_ + _
        refine (mul_le_of_le_one_left zero_le hr1).trans ?_
        gcongr with a j
        exact IH (cont θ i a) j
    _ = ∑' a, pol0 θ i a * ∑' j, (if j = z then 0 else
          M.P i a j * ∑ t ∈ Finset.range N, pcT z (cont θ i a) j t) +
        V' * ∑' a, pol0 θ i a * ∑' j, M.P i a j + pcT z θ i 0 := by
        congr 1
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
        refine tsum_congr (fun a => ?_)
        simp_rw [← ENNReal.tsum_mul_left]
        rw [← ENNReal.tsum_add]
        refine tsum_congr (fun j => ?_)
        split_ifs <;> ring
    _ ≤ _ := by
        rw [pol0_P_sum, mul_one]
        apply le_of_eq; ring

lemma claim0 (θ' : SennottDP.Discounted.Policy M) (z : S) (α : ℝ) (hα : α ≤ 1) : ∀ N θ j,
    ∑ t ∈ Finset.range N, ENNReal.ofReal α ^ t * expCost (concat0 θ' z θ) j t ≤
      (if j = z then 0 else ∑ t ∈ Finset.range N, pcT z θ j t) + discCost θ' α z := by
  intro N
  induction N with
  | zero => intro θ j; simp
  | succ N ih =>
    intro θ j
    by_cases hj : j = z
    · subst hj
      rw [if_pos rfl, zero_add]
      simp_rw [concat0_at_z]
      exact ENNReal.sum_le_tsum (f := fun t => ENNReal.ofReal α ^ t * expCost θ' j t) _
    · rw [if_neg hj]
      exact step_bound θ' z α hα N ih (concat0 θ' z θ) θ j (concat0_pol0 θ' z θ j hj)
        (concat0_cont θ' z θ j hj)

lemma concat1_bound (θ' : SennottDP.Discounted.Policy M) (z : S) (α : ℝ) (hα : α ≤ 1)
    (θ : SennottDP.Discounted.Policy M) (i : S) :
    discCost (concat1 θ' z θ) α i ≤ passageCost θ i {z} + discCost θ' α z := by
  unfold discCost
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le (fun N => ?_)
  calc ∑ t ∈ Finset.range N, ENNReal.ofReal α ^ t * expCost (concat1 θ' z θ) i t
      ≤ ∑ t ∈ Finset.range (N+1), ENNReal.ofReal α ^ t * expCost (concat1 θ' z θ) i t :=
        Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (Nat.le_succ N))
    _ ≤ ∑ t ∈ Finset.range (N+1), pcT z θ i t + discCost θ' α z :=
        step_bound θ' z α hα N (claim0 θ' z α hα N) (concat1 θ' z θ) θ i
          (fun a => concat1_pol0 θ' z θ i a) (fun a => concat1_cont θ' z θ i a)
    _ ≤ _ := add_le_add (by rw [passageCost_eq_pcT]; exact ENNReal.sum_le_tsum _) le_rfl

lemma valueFn_le_passage_gen (z : S) (α : ℝ) (hα : α ≤ 1) (θ : SennottDP.Discounted.Policy M)
    (i : S) : valueFn M α i ≤ passageCost θ i {z} + valueFn M α z := by
  unfold valueFn
  rw [ENNReal.add_iInf]
  exact le_iInf (fun θ' => (iInf_le _ (concat1 θ' z θ)).trans (concat1_bound θ' z α hα θ i))

end concat


lemma ereal_sub_le' {a b c : ℝ≥0∞} (hb : b ≠ ⊤) (hc : c ≠ ⊤) (h : a ≤ c + b) :
    (a : EReal) - b ≤ c := by
  have ha : a ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hc, hb⟩) h
  rw [← EReal.coe_ennreal_toReal ha, ← EReal.coe_ennreal_toReal hb, ← EReal.coe_ennreal_toReal hc,
    ← EReal.coe_sub, EReal.coe_le_coe_iff]
  have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hc, hb⟩) h
  rw [ENNReal.toReal_add hc hb] at this
  linarith

theorem relValue_le_passageCost_core {S Act : Type} [Countable S] [DecidableEq S]
    (M : SennottDP.Discounted.MDC S Act) (z : S) :
    (∀ α : ℝ, 0 < α → α < 1 → valueFn M α z < ⊤ →
      ∀ i, i ≠ z → ∀ θ : SennottDP.Discounted.Policy M, InRStar θ i {z} →
        relValue M z α i ≤ ((passageCost θ i {z} : ℝ≥0∞) : EReal)) ∧
    ((∀ α : ℝ, 0 < α → α < 1 → valueFn M α z < ⊤) →
      ∀ θ : S → SennottDP.Discounted.Policy M, (∀ i, i ≠ z → InRStar (θ i) i {z}) →
        SEN2 M z (fun i => if i = z then 0 else (passageCost (θ i) i {z}).toReal)) := by
  have P1 : ∀ α : ℝ, 0 < α → α < 1 → valueFn M α z < ⊤ →
      ∀ i, i ≠ z → ∀ θ : SennottDP.Discounted.Policy M, InRStar θ i {z} →
        relValue M z α i ≤ ((passageCost θ i {z} : ℝ≥0∞) : EReal) := by
    intro α _ h1 hz i _ θ hθ
    exact ereal_sub_le' hz.ne hθ.2.ne (valueFn_le_passage_gen z α h1.le θ i)
  refine ⟨P1, fun hfin θ hθ => ⟨fun i => ?_, fun α h0 h1 i => ?_⟩⟩
  · beta_reduce
    split_ifs
    · exact le_rfl
    · exact ENNReal.toReal_nonneg
  · beta_reduce
    by_cases hi : i = z
    · rw [if_pos hi]
      subst hi
      unfold relValue
      rw [← EReal.coe_ennreal_toReal (hfin α h0 h1).ne, ← EReal.coe_sub, sub_self]
    · rw [if_neg hi, EReal.coe_ennreal_toReal ((hθ i hi).2.ne)]
      exact P1 α h0 h1 (hfin α h0 h1) i hi (θ i) (hθ i hi)

end SennottDP.BOR

open SennottDP.BOR


theorem solution {S Act : Type} [Countable S] [DecidableEq S] (M : SennottDP.Discounted.MDC S Act) (z : S) :
    (∀ α : ℝ, 0 < α → α < 1 → valueFn M α z < ⊤ →
      ∀ i, i ≠ z → ∀ θ : SennottDP.Discounted.Policy M, InRStar θ i {z} →
        relValue M z α i ≤ ((passageCost θ i {z} : ℝ≥0∞) : EReal)) ∧
    ((∀ α : ℝ, 0 < α → α < 1 → valueFn M α z < ⊤) →
      ∀ θ : S → SennottDP.Discounted.Policy M, (∀ i, i ≠ z → InRStar (θ i) i {z}) →
        SEN2 M z (fun i => if i = z then 0 else (passageCost (θ i) i {z}).toReal)) := by
  exact relValue_le_passageCost_core M z
