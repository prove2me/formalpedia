-- Prove2me | solution 1 for QAlgorithms.DeWolf.ldc_decoder_normalForm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T03:16:26.690849+00:00
-- url     : https://prove2.me/submissions/115a1385-05b7-4dfc-b756-6aebd836b885

import Definitions.Def_QAlgorithms_Defs_Information

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open QAlgorithms
open scoped ENNReal

private def sgn (b : Bool) : ℝ := if b then -1 else 1

private def psign {N : ℕ} (t : Finset (Fin N)) (y : Fin N → Bool) : ℝ :=
  ∏ j ∈ t, sgn (y j)

private lemma sgn_sq (b : Bool) : sgn b * sgn b = 1 := by cases b <;> norm_num [sgn]

private lemma sgn_parity {N : ℕ} (t : Finset (Fin N)) (y : Fin N → Bool) :
    sgn (decide (Odd (t.filter fun j => y j = true).card)) = psign t y := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [psign, sgn]
  | @insert j t hj ih =>
    cases h : y j
    · simpa [Finset.filter_insert, h, hj, psign, sgn] using ih
    · have hj' : j ∉ t.filter (fun k => y k = true) := fun h => hj (Finset.mem_filter.mp h).1
      simp only [Finset.filter_insert, h, ↓reduceIte, Finset.card_insert_of_notMem hj']
      change sgn (decide (Odd ((t.filter fun k => y k = true).card + 1))) =
        psign (insert j t) y
      rw [show psign (insert j t) y = sgn (y j) * psign t y by simp [psign, hj], ← ih]
      by_cases ho : Odd (t.filter fun k => y k = true).card <;>
        simp [Nat.odd_add_one, ho, sgn, h]

private lemma sgn_xor (a b : Bool) : sgn (xor a b) = sgn a * sgn b := by
  cases a <;> cases b <;> norm_num [sgn]

private lemma sum_sign {n : ℕ} (f g : (Fin n → Bool) → Bool) :
    ∑ x, sgn (f x) * sgn (g x) =
      2 * ((Finset.univ.filter fun x => f x = g x).card : ℝ) - (2 : ℝ)^n := by
  have h (x : Fin n → Bool) : sgn (f x) * sgn (g x) =
      2 * (if f x = g x then (1 : ℝ) else 0) - 1 := by
    cases f x <;> cases g x <;> norm_num [sgn]
  simp_rw [h]
  simp [Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_filter, mul_comm]

private def flipSet {N : ℕ} (t : Finset (Fin N)) (j : Fin N) : Finset (Fin N) :=
  if j ∈ t then t.erase j else insert j t

private lemma flipSet_card {N : ℕ} (t : Finset (Fin N)) (j : Fin N) :
    (flipSet t j).card ≤ t.card + 1 := by
  unfold flipSet
  split_ifs with h
  · exact (Finset.card_erase_le).trans (Nat.le_succ _)
  · simp [Finset.card_insert_of_notMem h]

private lemma psign_flip {N : ℕ} (t : Finset (Fin N)) (j : Fin N) (y : Fin N → Bool) :
    psign (flipSet t j) y = psign t y * sgn (y j) := by
  classical
  unfold flipSet
  split_ifs with h
  · have ht := Finset.mul_prod_erase t (fun k => sgn (y k)) h
    dsimp [psign]
    rw [← ht]
    cases hy : y j <;> norm_num [sgn, hy]

  · simp [psign, Finset.prod_insert, h, mul_comm]

private lemma flipSet_disjoint {N : ℕ} {t U : Finset (Fin N)} {j : Fin N}
    (ht : Disjoint t U) (hj : j ∉ U) : Disjoint (flipSet t j) U := by
  unfold flipSet
  split_ifs
  · exact ht.mono_left (Finset.erase_subset _ _)
  · simpa using Finset.disjoint_insert_left.mpr ⟨hj, ht⟩

private def treeSign {N : ℕ} : ℕ → DecisionTree (Fin N) Bool Bool → (Fin N → Bool) → ℝ
  | _, .leaf b, _ => sgn b
  | 0, .node _ _, _ => 1
  | q+1, .node j k, y => treeSign q (k (y j)) y

private lemma treeSign_eval {N q : ℕ} (t : DecisionTree (Fin N) Bool Bool)
    (y : Fin N → Bool) (h : t.queries y ≤ q) : treeSign q t y = sgn (t.eval y) := by
  induction q generalizing t with
  | zero => cases t with
    | leaf b => rfl
    | node j k => simp [DecisionTree.queries] at h
  | succ q ih => cases t with
    | leaf b => rfl
    | node j k =>
      simp only [treeSign, DecisionTree.eval]
      exact ih _ (by simp only [DecisionTree.queries] at h; omega)

private def eraseWord {N : ℕ} (U : Finset (Fin N)) (y : Fin N → Bool) : Fin N → Bool :=
  fun j => if j ∈ U then false else y j

private lemma tree_corr_bound {n N Q : ℕ} (C : (Fin n → Bool) → (Fin N → Bool))
    (i : Fin n) (U : Finset (Fin N)) (B : ℝ) (hB : 0 < B)
    (hpar : ∀ t : Finset (Fin N), t.card ≤ Q → Disjoint t U →
      |∑ x, sgn (x i) * psign t (C x)| < B) :
    ∀ q (t : DecisionTree (Fin N) Bool Bool) (v : Finset (Fin N)),
      v.card + q ≤ Q → Disjoint v U →
      |∑ x, sgn (x i) * psign v (C x) * treeSign q t (eraseWord U (C x))| < 2^q * B := by
  intro q
  induction q with
  | zero =>
    intro t v hv hd
    have hp := hpar v (by omega) hd
    cases t with
    | leaf b => cases b <;> simpa [treeSign, sgn, Finset.sum_neg_distrib] using hp
    | node j k => simpa [treeSign] using hp
  | succ q ih =>
    intro t v hv hd
    have hh : (2 : ℝ)^q * B < 2^(q+1) * B := by
      rw [pow_succ]
      nlinarith [show 0 < (2 : ℝ)^q * B by positivity]
    cases t with
    | leaf b =>
      have hp := hpar v (by omega) hd
      have hpow : (1 : ℝ) ≤ 2^(q+1) := one_le_pow₀ (by norm_num)
      have hp' : |∑ x, sgn (x i) * psign v (C x)| < 2^(q+1)*B :=
        hp.trans_le (by nlinarith)
      cases b <;> simpa [treeSign, sgn, Finset.sum_neg_distrib] using hp'
    | node j k =>
      by_cases hj : j ∈ U
      · have hb := ih (k false) v (by omega) hd
        apply lt_trans _ hh
        simpa [treeSign, eraseWord, hj] using hb
      · have hv' : (flipSet v j).card + q ≤ Q := (Nat.add_le_add_right (flipSet_card v j) q).trans (by omega)
        have hd' := flipSet_disjoint hd hj
        have h0 := ih (k false) v (by omega) hd
        have h1 := ih (k true) v (by omega) hd
        have h2 := ih (k false) (flipSet v j) hv' hd'
        have h3 := ih (k true) (flipSet v j) hv' hd'
        have hexp (x : Fin n → Bool) :
            sgn (x i) * psign v (C x) * treeSign (q+1) (.node j k) (eraseWord U (C x)) =
            (sgn (x i) * psign v (C x) * treeSign q (k false) (eraseWord U (C x)) +
             sgn (x i) * psign v (C x) * treeSign q (k true) (eraseWord U (C x)) +
             sgn (x i) * psign (flipSet v j) (C x) * treeSign q (k false) (eraseWord U (C x)) -
             sgn (x i) * psign (flipSet v j) (C x) * treeSign q (k true) (eraseWord U (C x))) / 2 := by
          rw [psign_flip]
          cases hx : C x j <;> simp [treeSign, eraseWord, hj, hx, sgn] <;> ring
        simp_rw [hexp]
        rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.sum_add_distrib, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have hb := abs_add_le
          ((∑ x, sgn (x i) * psign v (C x) * treeSign q (k false) (eraseWord U (C x))) +
           (∑ x, sgn (x i) * psign v (C x) * treeSign q (k true) (eraseWord U (C x))) +
           (∑ x, sgn (x i) * psign (flipSet v j) (C x) * treeSign q (k false) (eraseWord U (C x))))
          (-(∑ x, sgn (x i) * psign (flipSet v j) (C x) * treeSign q (k true) (eraseWord U (C x))))
        simp only [abs_neg, ← sub_eq_add_neg] at hb
        have ha := abs_add_le
          ((∑ x, sgn (x i) * psign v (C x) * treeSign q (k false) (eraseWord U (C x))) +
           (∑ x, sgn (x i) * psign v (C x) * treeSign q (k true) (eraseWord U (C x))))
          (∑ x, sgn (x i) * psign (flipSet v j) (C x) * treeSign q (k false) (eraseWord U (C x)))
        have hc := abs_add_le
          (∑ x, sgn (x i) * psign v (C x) * treeSign q (k false) (eraseWord U (C x)))
          (∑ x, sgn (x i) * psign v (C x) * treeSign q (k true) (eraseWord U (C x)))
        rw [pow_succ]
        linarith

private lemma pmf_sum_real {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a, (p a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a)]
  simpa [tsum_fintype] using congrArg ENNReal.toReal p.tsum_coe

private lemma pmf_map_real {α : Type*} [Fintype α] (p : PMF α)
    (f : α → Bool) (b : Bool) :
    ((p.map f) b).toReal = ∑ a, (p a).toReal * (if f a = b then 1 else 0) := by
  classical
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro a _
    by_cases h : f a = b
    · simp [h]
    · simp [h, Ne.symm h]
  · intro a _
    split_ifs <;> simp [p.apply_ne_top]

private lemma good_tree {n N q : ℕ} {δ ε : ℝ}
    {C : (Fin n → Bool) → (Fin N → Bool)} (hC : IsLDC q δ ε C)
    (i : Fin n) (U : Finset (Fin N)) (hU : (U.card : ℝ) ≤ δ * N) :
    ∃ t : DecisionTree (Fin N) Bool Bool, t.MakesAtMost q ∧
      2 * ε * (2 : ℝ)^n ≤ ∑ x, sgn (x i) * sgn (t.eval (eraseWord U (C x))) := by
  classical
  obtain ⟨R, hRq, hR⟩ := hC i
  let F := fun t : DecisionTree (Fin N) Bool Bool =>
    fun x : Fin n → Bool => t.eval (eraseWord U (C x))
  let p := R.map F
  let K : ℝ := (1/2 + ε) * 2^n
  have hprob (x : Fin n → Bool) :
      1/2 + ε ≤ ∑ f, (p f).toReal * (if f x = x i then 1 else 0) := by
    have hd : hammingDist (C x) (eraseWord U (C x)) ≤ U.card := by
      apply Finset.card_le_card
      intro j hj
      simp only [hammingDist, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      by_contra h
      exact hj (by simp [eraseWord, h])
    have hdr : (hammingDist (C x) (eraseWord U (C x)) : ℝ) ≤ U.card := by exact_mod_cast hd
    have he := hR x (eraseWord U (C x)) (hdr.trans hU)
    have hm : p.map (fun f => f x) = R.map (fun t => t.eval (eraseWord U (C x))) := by
      change (R.map F).map (fun f => f x) = _
      rw [PMF.map_comp]
      rfl
    rw [← pmf_map_real, hm]
    exact he
  have hsum : K ≤ ∑ f, (p f).toReal *
      ((Finset.univ.filter fun x : Fin n → Bool => f x = x i).card : ℝ) := by
    have hb := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (Fin n → Bool))) => hprob x)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at hb
    have hs : (∑ x : Fin n → Bool, ∑ f, (p f).toReal * (if f x = x i then 1 else 0)) =
        ∑ f, (p f).toReal * ((Finset.univ.filter fun x : Fin n → Bool => f x = x i).card : ℝ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro f _
      rw [← Finset.mul_sum]
      congr 1
      simp [← Finset.sum_filter]
    rw [hs] at hb
    simpa [K, mul_comm] using hb

  have hg : ∃ f ∈ p.support,
      K ≤ ((Finset.univ.filter fun x : Fin n → Bool => f x = x i).card : ℝ) := by
    by_contra hh
    push Not at hh
    have hle (f : (Fin n → Bool) → Bool) (_ : f ∈ Finset.univ) :
        (p f).toReal * ((Finset.univ.filter fun x => f x = x i).card : ℝ) ≤
        (p f).toReal * K := by
      by_cases hf : f ∈ p.support
      · exact mul_le_mul_of_nonneg_left (hh f hf).le ENNReal.toReal_nonneg
      · have hz : p f = 0 := by simpa [PMF.mem_support_iff] using hf
        simp [hz]
    have hlt : (∑ f, (p f).toReal *
        ((Finset.univ.filter fun x => f x = x i).card : ℝ)) < ∑ f, (p f).toReal * K := by
      apply Finset.sum_lt_sum hle
      obtain ⟨f, hf⟩ := p.support_nonempty
      refine ⟨f, Finset.mem_univ _, mul_lt_mul_of_pos_left (hh f hf) ?_⟩
      exact ENNReal.toReal_pos ((p.mem_support_iff f).mp hf) (p.apply_ne_top f)
    rw [← Finset.sum_mul, pmf_sum_real, one_mul] at hlt
    linarith
  obtain ⟨f, hf, hfg⟩ := hg
  obtain ⟨t, ht, htf⟩ := (PMF.mem_support_map_iff F R f).mp hf
  refine ⟨t, hRq t ht, ?_⟩
  have heq : (fun x => t.eval (eraseWord U (C x))) = f := htf
  have heqp (x : Fin n → Bool) : t.eval (eraseWord U (C x)) = f x := congrFun heq x
  simp_rw [heqp]
  rw [sum_sign]
  have hc : ((Finset.univ.filter fun x : Fin n → Bool => x i = f x).card : ℝ) =
      ((Finset.univ.filter fun x : Fin n → Bool => f x = x i).card : ℝ) := by
    congr 2
    ext x
    simp [eq_comm]
  rw [hc]
  dsimp [K] at hfg
  nlinarith

private lemma parity_avoiding {n N q : ℕ} {δ ε : ℝ}
    {C : (Fin n → Bool) → (Fin N → Bool)} (hε : 0 < ε) (hC : IsLDC q δ ε C)
    (i : Fin n) (U : Finset (Fin N)) (hU : (U.card : ℝ) ≤ δ * N) :
    ∃ t : Finset (Fin N), t.card ≤ q ∧ Disjoint t U ∧ ∃ a : Bool,
      1/2 + ε/(2:ℝ)^q ≤
        ((Finset.univ.filter fun x : Fin n → Bool =>
          x i = xor a (decide (Odd (t.filter fun j => C x j = true).card))).card : ℝ) / (2:ℝ)^n := by
  classical
  by_contra hh
  push Not at hh
  let B : ℝ := 2 * ε * (2:ℝ)^n / (2:ℝ)^q
  have hB : 0 < B := by dsimp [B]; positivity
  have hpar (v : Finset (Fin N)) (hv : v.card ≤ q) (hd : Disjoint v U) :
      |∑ x, sgn (x i) * psign v (C x)| < B := by
    have h0 := hh v hv hd false
    have h1 := hh v hv hd true
    have e0 := sum_sign (fun x : Fin n → Bool => x i)
      (fun x => xor false (decide (Odd (v.filter fun j => C x j = true).card)))
    have e1 := sum_sign (fun x : Fin n → Bool => x i)
      (fun x => xor true (decide (Odd (v.filter fun j => C x j = true).card)))
    simp_rw [sgn_xor, sgn_parity] at e0 e1
    simp only [sgn, Bool.false_eq_true, ↓reduceIte, one_mul] at e0
    simp only [sgn, ↓reduceIte, neg_one_mul, mul_neg, Finset.sum_neg_distrib] at e1
    have hn : (0:ℝ) < 2^n := by positivity
    rw [div_lt_iff₀ hn] at h0 h1
    have hform : (1/2 + ε/(2:ℝ)^q)*(2:ℝ)^n = (2:ℝ)^n/2 + B/2 := by
      dsimp [B]
      ring
    rw [hform] at h0 h1
    apply abs_lt.mpr
    dsimp only [sgn]
    constructor <;> linarith [e0, e1]

  obtain ⟨t, ht, hc⟩ := good_tree hC i U hU
  have hb := tree_corr_bound C i U B hB hpar q t ∅ (by simp) (by simp)
  have heq (x : Fin n → Bool) : treeSign q t (eraseWord U (C x)) =
      sgn (t.eval (eraseWord U (C x))) := treeSign_eval t _ (ht _)
  simp only [psign, Finset.prod_empty, mul_one] at hb
  simp_rw [heq] at hb
  have hval : (2:ℝ)^q * B = 2 * ε * (2:ℝ)^n := by dsimp [B]; field_simp
  rw [hval] at hb
  linarith [le_abs_self (∑ x, sgn (x i) * sgn (t.eval (eraseWord U (C x))))]

private lemma balanced {n : ℕ} (i : Fin n) (b : Bool) :
    ((Finset.univ.filter fun x : Fin n → Bool => x i = b).card : ℝ) /
      (2:ℝ)^n = 1/2 := by
  classical
  let R := {j : Fin n // j ≠ i} → Bool
  have hsum : (∑ x : Fin n → Bool, if x i = b then (1:ℝ) else 0) = Fintype.card R := by
    rw [← (Equiv.funSplitAt i Bool).symm.sum_comp]
    simp only [Equiv.funSplitAt, Equiv.piSplitAt, Equiv.coe_fn_mk, dif_pos rfl]
    rw [Fintype.sum_prod_type]
    cases b <;> simp [R]
  have hc : (2:ℝ)^n = 2 * Fintype.card R := by
    have h := Fintype.card_congr (Equiv.funSplitAt i Bool)
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Fintype.card_prod] at h
    dsimp [R]
    simp only [Fintype.card_fun, Fintype.card_bool]
    exact_mod_cast h
  have hcount : ((Finset.univ.filter fun x : Fin n → Bool => x i = b).card : ℝ) =
      Fintype.card R := by
    simpa only [← Finset.sum_boole, Finset.sum_ite_irrel] using hsum
  rw [hcount]
  have hpos : (0:ℝ) < 2^n := by positivity
  rw [div_eq_iff hpos.ne']
  linarith


private lemma correlated_nonempty {n N : ℕ} (i : Fin n)
    (C : (Fin n → Bool) → (Fin N → Bool)) (κ : ℝ) (hκ : 0 < κ)
    (t : Finset (Fin N)) (a : Bool)
    (h : 1/2 + κ ≤ ((Finset.univ.filter fun x : Fin n → Bool =>
      x i = xor a (decide (Odd (t.filter fun j => C x j = true).card))).card : ℝ) /
        (2:ℝ)^n) : t.Nonempty := by
  classical
  by_contra ht
  have he : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
  have hb := balanced i a
  have h' : 1/2 + κ ≤ ((Finset.univ.filter fun x : Fin n → Bool => x i = a).card : ℝ) /
      (2:ℝ)^n := by simpa [he] using h
  rw [hb] at h'
  linarith

private lemma eps_bound {n N q : ℕ} {δ ε : ℝ}
    {C : (Fin n → Bool) → (Fin N → Bool)} (hδ : 0 ≤ δ) (hC : IsLDC q δ ε C)
    (i : Fin n) : ε ≤ 1/2 := by
  obtain ⟨R, _, hR⟩ := hC i
  let x : Fin n → Bool := fun _ => false
  have h := hR x (C x) (by simp; positivity)
  have hp : successProb R (C x) (x i) ≤ 1 := by
    unfold successProb
    have hp := ENNReal.toReal_mono (show (1:ℝ≥0∞) ≠ ⊤ by simp)
      ((R.map (fun t => t.eval (C x))).coe_le_one (x i))
    simpa using hp
  linarith

private lemma matching_family {n N q : ℕ} {δ ε : ℝ}
    {C : (Fin n → Bool) → (Fin N → Bool)} (hδ : 0 < δ) (hε : 0 < ε)
    (hC : IsLDC q δ ε C) (i : Fin n) (hq : 0 < q) :
    ∃ M : Finset (Finset (Fin N)),
      (M : Set (Finset (Fin N))).PairwiseDisjoint id ∧
      (∀ t ∈ M, t.card ≤ q) ∧
      δ * ε * (N : ℝ) / (q : ℝ)^2 ≤ (M.card : ℝ) ∧
      ∃ a : Finset (Fin N) → Bool, ∀ t ∈ M,
        1/2 + ε/(2:ℝ)^q ≤
          ((Finset.univ.filter fun x : Fin n → Bool =>
            x i = xor (a t) (decide (Odd (t.filter fun j => C x j = true).card))).card : ℝ) / (2:ℝ)^n := by
  classical
  let Good (t : Finset (Fin N)) : Prop := t.card ≤ q ∧ ∃ a : Bool,
    1/2 + ε/(2:ℝ)^q ≤
      ((Finset.univ.filter fun x : Fin n → Bool =>
        x i = xor a (decide (Odd (t.filter fun j => C x j = true).card))).card : ℝ) / (2:ℝ)^n
  let F : Finset (Finset (Finset (Fin N))) := Finset.univ.filter fun M =>
    (M : Set (Finset (Fin N))).PairwiseDisjoint id ∧ ∀ t ∈ M, Good t
  have he : ∅ ∈ F := by simp [F, Set.pairwiseDisjoint_empty]
  obtain ⟨M, hM, hmax⟩ := F.exists_max_image Finset.card ⟨∅, he⟩
  obtain ⟨hdis, hgood⟩ := (Finset.mem_filter.mp hM).2
  let U : Finset (Fin N) := M.biUnion id
  have hU : δ * N < (U.card : ℝ) := by
    by_contra hh
    obtain ⟨t, htq, htd, a, ha⟩ := parity_avoiding hε hC i U (le_of_not_gt hh)
    have htne := correlated_nonempty i C (ε/(2:ℝ)^q) (by positivity) t a ha
    have hsub (v : Finset (Fin N)) (hv : v ∈ M) : v ⊆ U :=
      fun j hj => Finset.mem_biUnion.mpr ⟨v, hv, hj⟩
    have htn : t ∉ M := by
      intro ht
      have hdself : Disjoint t t := htd.mono_right (hsub t ht)
      have hz : t = ∅ := by simpa using hdself
      exact htne.ne_empty hz
    have hins : insert t M ∈ F := by
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rw [Finset.coe_insert]
        exact Set.pairwiseDisjoint_insert.mpr ⟨hdis, fun v hv _ => htd.mono_right (hsub v hv)⟩
      · intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact ⟨htq, a, ha⟩
        · exact hgood v hv
    have hb := hmax _ hins
    rw [Finset.card_insert_of_notMem htn] at hb
    omega
  have hUc : U.card ≤ M.card * q :=
    Finset.card_biUnion_le_card_mul M id q (fun t ht => (hgood t ht).1)
  have hqr : (0:ℝ) < q := by exact_mod_cast hq
  have hεq : ε ≤ (q:ℝ) := by
    have he := eps_bound hδ.le hC i
    have h1 : (1:ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hUcR : (U.card : ℝ) ≤ (M.card : ℝ) * (q:ℝ) := by exact_mod_cast hUc
  have hcount : δ * ε * (N:ℝ) / (q:ℝ)^2 ≤ (M.card:ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos hqr)).mpr
    have hδN : 0 ≤ δ * (N:ℝ) := by positivity
    have hprod := mul_le_mul_of_nonneg_left hεq hδN
    have hh := mul_le_mul_of_nonneg_right (hU.le.trans hUcR) hqr.le
    nlinarith
  refine ⟨M, hdis, fun t ht => (hgood t ht).1, hcount, ?_⟩
  have hchoice : ∀ t ∈ M, ∃ a : Bool,
      1/2 + ε/(2:ℝ)^q ≤
        ((Finset.univ.filter fun x : Fin n → Bool =>
          x i = xor a (decide (Odd (t.filter fun j => C x j = true).card))).card : ℝ) / (2:ℝ)^n :=
    fun t ht => (hgood t ht).2
  choose a ha using hchoice
  refine ⟨fun t => if ht : t ∈ M then a t ht else false, ?_⟩
  intro t ht
  simpa only [dif_pos ht] using ha t ht

theorem solution :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧
      ∀ (n N q : ℕ) (δ ε : ℝ) (C : (Fin n → Bool) → (Fin N → Bool)),
        0 < δ → 0 < ε → IsLDC q δ ε C →
        ∀ i : Fin n, ∃ M : Finset (Finset (Fin N)),
          (M : Set (Finset (Fin N))).PairwiseDisjoint id ∧
          (∀ t ∈ M, t.card ≤ q) ∧
          c₁ * (δ * ε * (N : ℝ) / (q : ℝ) ^ 2) ≤ (M.card : ℝ) ∧
          ∃ a : Finset (Fin N) → Bool, ∀ t ∈ M,
            1 / 2 + c₂ * (ε / (2 : ℝ) ^ q) ≤
              ((Finset.univ.filter fun x : Fin n → Bool =>
                  x i = xor (a t) (decide (Odd (t.filter fun j => C x j = true).card))).card : ℝ) /
                (2 : ℝ) ^ n  := by
  classical
  refine ⟨1, by norm_num, 1, by norm_num, ?_⟩
  intro n N q δ ε C hδ hε hC i
  by_cases hq : q = 0
  · subst q
    refine ⟨∅, by simp, by simp, ?_, fun _ => false, by simp⟩
    simp
  · simpa only [one_mul] using matching_family hδ hε hC i (Nat.pos_of_ne_zero hq)
