-- Prove2me | solution 1 for ProxGapTight.lemma_3_5_syndromes
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:48:59.472192+00:00
-- url     : https://prove2.me/submissions/7e0736f6-ba51-4ccb-9164-1b195d3ec846

import Mathlib
import Definitions.Def_ProxGapTight_incVec

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Polynomial



namespace ProxGapTight.Dev.Syn

variable {F : Type} [Field F]

/-- Newton-type identity from `P' = ∑_w P/(X-w)`. -/
lemma newton_coeff (W : Finset F) (u : ℕ) :
    (derivative (∏ w ∈ W, (X - C w))).coeff u
      = ∑ w ∈ W, ∑ i ∈ Finset.Icc (u+1) W.card,
          w ^ (i - (u+1)) * (∏ w ∈ W, (X - C w)).coeff i := by
  classical
  set P : F[X] := ∏ w ∈ W, (X - C w) with hP
  have hnd : P.natDegree = W.card := natDegree_finsetProd_X_sub_C_eq_card W id
  have hroot : ∀ w ∈ W, P.IsRoot w := by
    intro w hw
    rw [hP, IsRoot, eval_prod]
    exact Finset.prod_eq_zero hw (by simp)
  have hq : ∀ w ∈ W, ∏ j ∈ W.erase w, (X - C j) = P /ₘ (X - C w) := by
    intro w hw
    apply mul_left_cancel₀ (X_sub_C_ne_zero w)
    rw [mul_divByMonic_eq_iff_isRoot.mpr (hroot w hw), hP]
    exact Finset.mul_prod_erase W (fun j => X - C j) hw
  rw [hP, derivative_prod_finset, finsetSum_coeff]
  refine Finset.sum_congr rfl fun w hw => ?_
  simp only [derivative_sub, derivative_X, derivative_C, sub_zero, mul_one]
  rw [hq w hw, coeff_divByMonic_X_sub_C, hnd]


/-- Power sum. -/
def psum (W : Finset F) (r : ℕ) : F := ∑ w ∈ W, w ^ r

section PS

variable (p a : ℕ) [Fact p.Prime] [CharP F p]

lemma Qcast_zero (Q : ℕ) (hQ : Q = p ^ a) (ha : 1 ≤ a) (j : ℕ) (hj : 1 ≤ j) :
    ((Q ^ j : ℕ) : F) = 0 := by
  have hp : ((p : ℕ) : F) = 0 := CharP.cast_eq_zero F p
  have : Q ^ j = p * (p ^ (a * j - 1) ) := by
    rw [hQ, ← pow_mul, ← pow_succ' ]
    congr 1
    have : 1 ≤ a * j := Nat.mul_pos ha hj
    omega
  rw [this]; push_cast; rw [hp, zero_mul]

lemma two_le_Q (Q : ℕ) (hQ : Q = p ^ a) (ha : 1 ≤ a) : 2 ≤ Q := by
  have h2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  rw [hQ]
  calc 2 ≤ p := h2
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ a := Nat.pow_le_pow_right (by omega) ha


end PS

section PS2

variable {p a : ℕ} [Fact p.Prime] [CharP F p]

/-- Hypotheses bundle for power sums. -/
lemma Dprime (Q : ℕ) (hQ : Q = p ^ a) (ha : 1 ≤ a) (k : ℕ) (W : Finset F) (c : ℕ → F)
    (hcard : W.card = Q ^ (k + 2))
    (hP : ∏ w ∈ W, (X - C w) = ∑ i ∈ Finset.range (k + 3), C (c i) * X ^ (Q ^ i))
    (u : ℕ) :
    ∑ j ∈ Finset.range (k + 3), (if u + 1 ≤ Q ^ j then c j * psum W (Q ^ j - (u + 1)) else 0)
      = if u = 0 then c 0 else 0 := by
  classical
  have hQ2 := two_le_Q p a Q hQ ha
  have hder : derivative (∏ w ∈ W, (X - C w)) = C (c 0) := by
    rw [hP, derivative_sum, Finset.sum_range_succ']
    have : ∀ j ∈ Finset.range (k + 2), derivative (C (c (j + 1)) * X ^ (Q ^ (j + 1))) = 0 := by
      intro j _
      rw [derivative_C_mul_X_pow]
      have := Qcast_zero (F := F) p a Q hQ ha (j + 1) (by omega)
      simp [this]
    rw [Finset.sum_eq_zero this]
    simp
  have h1 := newton_coeff W u
  rw [hder, coeff_C, hcard] at h1
  refine Eq.trans ?_ h1.symm
  have hQle : ∀ j ∈ Finset.range (k + 3), Q ^ j ≤ Q ^ (k + 2) := fun j hj =>
    Nat.pow_le_pow_right (by omega) (by simpa [Nat.lt_succ_iff] using hj)
  rw [Finset.sum_comm]
  have : ∀ i ∈ Finset.Icc (u + 1) (Q ^ (k + 2)),
      ∑ w ∈ W, w ^ (i - (u + 1)) * (∏ w ∈ W, (X - C w)).coeff i
        = ∑ j ∈ Finset.range (k + 3), (if i = Q ^ j then c j * psum W (i - (u + 1)) else 0) := by
    intro i _
    rw [← Finset.sum_mul, hP, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp [psum, mul_comm]
  rw [Finset.sum_congr rfl this, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.sum_ite_eq']
  by_cases h : u + 1 ≤ Q ^ j
  · rw [if_pos h, if_pos (Finset.mem_Icc.mpr ⟨h, hQle j hj⟩)]
  · rw [if_neg h, if_neg]
    simp [h]


/-- Free recurrence from `P(w) = 0`. -/
lemma recur (Q : ℕ) (k : ℕ) (W : Finset F) (c : ℕ → F) (hc : c (k + 2) = 1)
    (hP : ∏ w ∈ W, (X - C w) = ∑ i ∈ Finset.range (k + 3), C (c i) * X ^ (Q ^ i))
    (s : ℕ) :
    psum W (s + Q ^ (k + 2)) = - ∑ j ∈ Finset.range (k + 2), c j * psum W (s + Q ^ j) := by
  have h0 : ∀ w ∈ W, w ^ s * ∑ i ∈ Finset.range (k + 3), c i * w ^ (Q ^ i) = 0 := by
    intro w hw
    have : (∏ w ∈ W, (X - C w)).eval w = 0 := by
      rw [eval_prod]; exact Finset.prod_eq_zero hw (by simp)
    rw [hP] at this
    simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X] at this
    rw [this, mul_zero]
  have h1 : ∑ w ∈ W, w ^ s * ∑ i ∈ Finset.range (k + 3), c i * w ^ (Q ^ i) = 0 :=
    Finset.sum_eq_zero h0
  simp only [Finset.mul_sum] at h1
  rw [Finset.sum_comm, Finset.sum_range_succ, hc] at h1
  have h2 : ∀ j, ∑ w ∈ W, w ^ s * (c j * w ^ (Q ^ j)) = c j * psum W (s + Q ^ j) := by
    intro j
    simp only [psum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [pow_add]; ring
  simp only [h2, one_mul] at h1
  have h3 : ∑ w ∈ W, w ^ s * w ^ (Q ^ (k + 2)) = psum W (s + Q ^ (k + 2)) := by
    simp only [psum]; refine Finset.sum_congr rfl fun w _ => ?_; exact (pow_add w s (Q ^ (k + 2))).symm
  rw [h3] at h1
  linear_combination h1


lemma psum_low (Q : ℕ) (hQ : Q = p ^ a) (ha : 1 ≤ a) (k : ℕ) (W : Finset F) (c : ℕ → F)
    (hcard : W.card = Q ^ (k + 2)) (hc : c (k + 2) = 1)
    (hP : ∏ w ∈ W, (X - C w) = ∑ i ∈ Finset.range (k + 3), C (c i) * X ^ (Q ^ i)) :
    ∀ r, r + 2 ≤ Q ^ (k + 2) → psum W r = 0 := by
  have hQ2 := two_le_Q p a Q hQ ha
  have hp0 : psum W 0 = 0 := by
    have := Qcast_zero (F := F) p a Q hQ ha (k + 2) (by omega)
    simp [psum, hcard, this]
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · exact hp0
    have hD := Dprime Q hQ ha k W c hcard hP (Q ^ (k + 2) - 1 - r)
    rw [if_neg (by omega)] at hD
    rw [Finset.sum_range_succ] at hD
    have hN : Q ^ (k + 2) - 1 - r + 1 ≤ Q ^ (k + 2) := by omega
    rw [if_pos hN, hc, one_mul,
      show Q ^ (k + 2) - (Q ^ (k + 2) - 1 - r + 1) = r by omega] at hD
    have hz : ∑ j ∈ Finset.range (k + 2),
        (if Q ^ (k + 2) - 1 - r + 1 ≤ Q ^ j
          then c j * psum W (Q ^ j - (Q ^ (k + 2) - 1 - r + 1)) else 0) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      split_ifs with h
      · have hlt : Q ^ j < Q ^ (k + 2) :=
          Nat.pow_lt_pow_right hQ2 (by simpa using hj)
        rw [ih _ (by omega) (by omega), mul_zero]
      · rfl
    rw [hz, zero_add] at hD
    exact hD


lemma power_sums (Q : ℕ) (hQ : Q = p ^ a) (ha : 1 ≤ a) (k : ℕ) (W : Finset F) (c : ℕ → F)
    (hcard : W.card = Q ^ (k + 2)) (hc : c (k + 2) = 1)
    (hP : ∏ w ∈ W, (X - C w) = ∑ i ∈ Finset.range (k + 3), C (c i) * X ^ (Q ^ i)) :
    psum W (Q ^ (k + 2) - 1) = c 0 ∧
    psum W (2 * Q ^ (k + 2) - Q ^ (k + 1) - 1) = -(c 0 * c (k + 1)) ∧
    psum W (2 * Q ^ (k + 2) - Q ^ k - 1) = -(c 0 * c k) := by
  have hQ2 := two_le_Q p a Q hQ ha
  have hlow := psum_low (F := F) (p := p) (a := a) Q hQ ha k W c hcard hc hP
  have hrec := recur (F := F) Q k W c hc hP
  have hpow : ∀ j, j < k + 2 → Q ^ j < Q ^ (k + 2) := fun j hj =>
    Nat.pow_lt_pow_right hQ2 hj
  have hmono : ∀ j j', j < j' → Q ^ j < Q ^ j' := fun j j' h => Nat.pow_lt_pow_right hQ2 h
  obtain ⟨t, ht⟩ : ∃ t, t = Q ^ k := ⟨_, rfl⟩
  have hA : Q ^ (k + 1) = Q * t := by rw [ht, pow_succ, mul_comm]
  have hN : Q ^ (k + 2) = Q * (Q * t) := by rw [← hA, pow_succ, mul_comm]
  have ht1 : 1 ≤ t := by rw [ht]; exact Nat.one_le_pow _ _ (by omega)
  obtain ⟨q, hq⟩ : ∃ q, Q = q + 2 := ⟨Q - 2, by omega⟩
  have hkey : 2 * (Q * t) + 1 ≤ Q ^ (k + 2) + t := by
    rw [hN, hq]; nlinarith [Nat.zero_le (t * q), Nat.zero_le (t * q * q)]
  have hA2 : 2 * t ≤ Q * t := by nlinarith
  have hA3 : Q * t + 2 ≤ Q ^ (k + 2) := by rw [hN, hq]; nlinarith [Nat.zero_le (t * q), Nat.zero_le (t * q * q)]
  have h0 : psum W (Q ^ (k + 2) - 1) = c 0 := by
    have hD := Dprime Q hQ ha k W c hcard hP 0
    rw [if_pos rfl, Finset.sum_range_succ] at hD
    have hz : ∑ j ∈ Finset.range (k + 2),
        (if 0 + 1 ≤ Q ^ j then c j * psum W (Q ^ j - (0 + 1)) else 0) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      split_ifs with h
      · have := hpow j (by simpa using hj)
        rw [hlow _ (by omega), mul_zero]
      · rfl
    rw [hz, zero_add, if_pos (Nat.one_le_pow _ _ (by omega)), hc, one_mul] at hD
    simpa using hD
  refine ⟨h0, ?_, ?_⟩
  · rw [show 2 * Q ^ (k + 2) - Q ^ (k + 1) - 1 = (Q ^ (k + 2) - Q ^ (k + 1) - 1) + Q ^ (k + 2) by omega,
      hrec, Finset.sum_range_succ]
    have hz : ∑ j ∈ Finset.range (k + 1), c j * psum W ((Q ^ (k + 2) - Q ^ (k + 1) - 1) + Q ^ j) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have := hmono j (k + 1) (by simpa using hj)
      rw [hlow _ (by omega), mul_zero]
    rw [hz, zero_add, show (Q ^ (k + 2) - Q ^ (k + 1) - 1) + Q ^ (k + 1) = Q ^ (k + 2) - 1 by omega, h0]
    ring
  · rw [show 2 * Q ^ (k + 2) - Q ^ k - 1 = (Q ^ (k + 2) - Q ^ k - 1) + Q ^ (k + 2) by omega,
      hrec, Finset.sum_range_succ, Finset.sum_range_succ]
    have hz : ∑ j ∈ Finset.range k, c j * psum W ((Q ^ (k + 2) - Q ^ k - 1) + Q ^ j) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have := hmono j k (by simpa using hj)
      rw [hlow _ (by omega), mul_zero]
    have hlast : psum W ((Q ^ (k + 2) - Q ^ k - 1) + Q ^ (k + 1)) = 0 := by
      rw [show (Q ^ (k + 2) - Q ^ k - 1) + Q ^ (k + 1) = (Q ^ (k + 1) - Q ^ k - 1) + Q ^ (k + 2) by omega,
        hrec]
      refine neg_eq_zero.mpr (Finset.sum_eq_zero fun j hj => ?_)
      have := Nat.pow_le_pow_right (show 0 < Q by omega) (show j ≤ k + 1 by simpa [Nat.lt_succ_iff] using hj)
      rw [hlow _ (by omega), mul_zero]
    rw [hz, zero_add, hlast, mul_zero, add_zero,
      show (Q ^ (k + 2) - Q ^ k - 1) + Q ^ k = Q ^ (k + 2) - 1 by omega, h0]
    ring

end PS2

end ProxGapTight.Dev.Syn



namespace ProxGapTight.Dev.Syn

section Sub

open Classical

variable {F : Type} [Field F] [Fintype F]
variable {K : Type} [Field K] [Fintype K] [Algebra K F]

/-- Subspace polynomial `∏_{x ∈ U} (X - x)`. -/
noncomputable def sp (U : Submodule K F) : F[X] :=
  ∏ x ∈ Finset.univ.filter (fun x => x ∈ U), (X - C x)

lemma sp_monic (U : Submodule K F) : (sp U).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

lemma sp_natDegree (U : Submodule K F) :
    (sp U).natDegree = Fintype.card K ^ Module.finrank K U := by
  unfold sp
  have h := natDegree_finsetProd_X_sub_C_eq_card (Finset.univ.filter (fun x => x ∈ U)) (fun x : F => x)
  rw [h]
  rw [← Module.card_eq_pow_finrank (K := K) (V := U), Fintype.card_subtype]

lemma sp_eval_eq_zero_iff (U : Submodule K F) (x : F) : (sp U).eval x = 0 ↔ x ∈ U := by
  unfold sp
  rw [eval_prod, Finset.prod_eq_zero_iff]
  simp [sub_eq_zero, eq_comm]

variable (p a : ℕ) [Fact p.Prime] [CharP F p]

lemma frobQ_add (Q : ℕ) (hQ : Q = p ^ a) (i : ℕ) (x y : F) :
    (x + y) ^ (Q ^ i) = x ^ (Q ^ i) + y ^ (Q ^ i) := by
  have : Q ^ i = p ^ (a * i) := by rw [hQ, pow_mul]
  rw [this]
  exact add_pow_char_pow x y p (a * i)

lemma frobQ_alg (Q : ℕ) (hKQ : Fintype.card K = Q) (i : ℕ) (c : K) :
    (algebraMap K F c) ^ (Q ^ i) = algebraMap K F c := by
  rw [← map_pow, ← hKQ, FiniteField.pow_card_pow]


lemma eval_qsum_add (Q : ℕ) (hQ : Q = p ^ a) (hKQ : Fintype.card K = Q) (m : ℕ) (c : ℕ → F)
    (u b : F) (t : K) :
    (∑ i ∈ Finset.range m, C (c i) * X ^ (Q ^ i)).eval (u + algebraMap K F t * b)
      = (∑ i ∈ Finset.range m, C (c i) * X ^ (Q ^ i)).eval u
        + algebraMap K F t * (∑ i ∈ Finset.range m, C (c i) * X ^ (Q ^ i)).eval b := by
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [frobQ_add p a Q hQ i, mul_pow, frobQ_alg (F := F) Q hKQ i t]
  ring

lemma qsum_pow (Q : ℕ) (hQ : Q = p ^ a) (m : ℕ) (c : ℕ → F) :
    (∑ i ∈ Finset.range m, C (c i) * X ^ (Q ^ i)) ^ Q
      = ∑ i ∈ Finset.range m, C (c i ^ Q) * X ^ (Q ^ (i + 1)) := by
  have hc : CharP F[X] p := inferInstance
  rw [hQ, sum_pow_char_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow, ← C_pow, ← pow_mul, ← hQ, pow_succ]


lemma sp_struct (Q : ℕ) (hQ : Q = p ^ a) (ha : 1 ≤ a) (hKQ : Fintype.card K = Q)
    (V : Subfield F) (hV : ∀ x : K, algebraMap K F x ∈ V) :
    ∀ (n : ℕ) (U : Submodule K F), Module.finrank K U = n → (∀ x ∈ U, x ∈ V) →
    ∃ c : ℕ → F, (∀ i, c i ∈ V) ∧ c n = 1 ∧
      sp U = ∑ i ∈ Finset.range (n + 1), C (c i) * X ^ (Q ^ i) := by
  have hQ2 : 2 ≤ Q := by
    have h2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    rw [hQ]
    calc 2 ≤ p := h2
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ a := Nat.pow_le_pow_right (by omega) ha
  intro n
  induction n with
  | zero =>
    intro U hU _
    have hU0 : U = ⊥ := Submodule.finrank_eq_zero.mp hU
    refine ⟨fun i => if i = 0 then 1 else 0, fun i => ?_, by simp, ?_⟩
    · show (if i = 0 then (1 : F) else 0) ∈ V
      split_ifs
      · exact V.one_mem
      · exact V.zero_mem
    · have : Finset.univ.filter (fun x : F => x ∈ U) = {0} := by
        ext x; simp [hU0]
      simp [sp, this]
  | succ n ih =>
    intro U hU hUV
    have hpos : 0 < Module.finrank K U := by omega
    haveI : Nontrivial U := Module.finrank_pos_iff.mp hpos
    obtain ⟨b', hb'⟩ := exists_ne (0 : U)
    obtain ⟨C', hC⟩ := Submodule.exists_isCompl (Submodule.span K {b'})
    have hfin := Submodule.finrank_add_eq_of_isCompl hC
    rw [finrank_span_singleton hb', hU] at hfin
    have hC'fin : Module.finrank K C' = n := by omega
    set U' : Submodule K F := C'.map U.subtype with hU'
    have hU'fin : Module.finrank K U' = n := by
      rw [hU', Submodule.finrank_map_subtype_eq, hC'fin]
    have hU'U : ∀ x ∈ U', x ∈ U := by
      intro x hx
      obtain ⟨y, _, rfl⟩ := hx
      exact y.2
    obtain ⟨c, hcV, hcn, hsp⟩ := ih U' hU'fin (fun x hx => hUV x (hU'U x hx))
    set b : F := (b' : F) with hb
    have hbU : b ∈ U := b'.2
    have hdecomp : ∀ x ∈ U, ∃ u ∈ U', ∃ t : K, x = u + algebraMap K F t * b := by
      intro x hx
      have hx' : (⟨x, hx⟩ : U) ∈ Submodule.span K {b'} ⊔ C' := by
        rw [hC.sup_eq_top]; trivial
      obtain ⟨l, hl, y, hy, hly⟩ := Submodule.mem_sup.mp hx'
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hl
      refine ⟨(y : F), ⟨y, hy, rfl⟩, t, ?_⟩
      have := congrArg (fun z : U => (z : F)) hly
      simp only [Submodule.coe_add, Submodule.coe_smul] at this
      rw [Algebra.smul_def] at this
      rw [← this, hb]; ring
    set P' := sp U' with hP'
    set z : F := P'.eval b with hz
    have hzV : z ∈ V := by
      rw [hz, hsp]
      simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
      refine V.sum_mem fun i _ => V.mul_mem (hcV i) ?_
      exact V.pow_mem (hUV b hbU) _
    set R : F[X] := P' ^ Q - C (z ^ (Q - 1)) * P' with hR
    have hP'mon : P'.Monic := sp_monic U'
    have hP'deg : P'.natDegree = Q ^ n := by
      rw [hP', sp_natDegree, hU'fin, hKQ]
    have hpowdeg : (P' ^ Q).natDegree = Q ^ (n + 1) := by
      rw [hP'mon.natDegree_pow, hP'deg, ← pow_succ']
    have hQn : Q ^ n < Q ^ (n + 1) := Nat.pow_lt_pow_right hQ2 (by omega)
    have hlt : (C (z ^ (Q - 1)) * P').natDegree < (P' ^ Q).natDegree := by
      calc (C (z ^ (Q - 1)) * P').natDegree ≤ P'.natDegree := natDegree_C_mul_le _ _
        _ = Q ^ n := hP'deg
        _ < Q ^ (n + 1) := hQn
        _ = _ := hpowdeg.symm
    have hRmon : R.Monic := (hP'mon.pow Q).sub_of_left (degree_lt_degree hlt)
    have hRdeg : R.natDegree = Q ^ (n + 1) := by
      rw [hR, natDegree_sub_eq_left_of_natDegree_lt hlt, hpowdeg]
    have hroot : ∀ x ∈ U, R.eval x = 0 := by
      intro x hx
      obtain ⟨u, hu, t, rfl⟩ := hdecomp x hx
      have h1 : P'.eval (u + algebraMap K F t * b) = algebraMap K F t * z := by
        rw [hsp] at hz ⊢
        rw [eval_qsum_add p a Q hQ hKQ, ← hsp, (sp_eval_eq_zero_iff U' u).mpr hu, zero_add]
      rw [hR, eval_sub, eval_pow, eval_mul, eval_C, h1, mul_pow]
      have h2 := frobQ_alg (F := F) Q hKQ 1 t
      rw [pow_one] at h2
      rw [h2]
      have h3 : z ^ (Q - 1) * z = z ^ Q := pow_sub_one_mul (by omega) z
      rw [← h3]; ring
    have hdvd : sp U ∣ R := by
      have hR0 : R ≠ 0 := hRmon.ne_zero
      have hle : (Finset.univ.filter (fun x : F => x ∈ U)).val ≤ R.roots := by
        rw [Multiset.le_iff_subset (Finset.nodup _)]
        intro x hx
        rw [Finset.mem_val, Finset.mem_filter] at hx
        exact (mem_roots hR0).mpr (hroot x hx.2)
      refine (Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hle)).trans ?_
      exact prod_multiset_X_sub_C_dvd R
    have hspR : sp U = R := by
      refine (eq_of_monic_of_dvd_of_natDegree_le (sp_monic U) hRmon hdvd ?_).symm
      rw [sp_natDegree, hU, hKQ, hRdeg]
    -- coefficients
    refine ⟨fun i => (if i = 0 then 0 else c (i - 1) ^ Q) - z ^ (Q - 1) * (if i ≤ n then c i else 0),
      fun i => ?_, ?_, ?_⟩
    · show ((if i = 0 then 0 else c (i - 1) ^ Q) - z ^ (Q - 1) * (if i ≤ n then c i else 0)) ∈ V
      refine V.sub_mem ?_ (V.mul_mem (V.pow_mem hzV _) ?_)
      · split_ifs
        · exact V.zero_mem
        · exact V.pow_mem (hcV _) _
      · split_ifs
        · exact hcV _
        · exact V.zero_mem
    · simp [hcn]
    · rw [hspR, hR, hsp, qsum_pow p a Q hQ, Finset.mul_sum]
      simp only [sub_mul, C_sub, Finset.sum_sub_distrib]
      rw [Finset.sum_range_succ' (fun i => (C (if i = 0 then 0 else c (i - 1) ^ Q)) * X ^ Q ^ i)]
      rw [Finset.sum_range_succ (fun x => C (z ^ (Q - 1) * if x ≤ n then c x else 0) * X ^ Q ^ x)]
      simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, if_true, C_0, zero_mul,
        add_zero, Nat.not_succ_le_self, mul_zero]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      have : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
      rw [if_pos this, C_mul, mul_assoc]


lemma card_filter_mem (U : Submodule K F) :
    (Finset.univ.filter (fun x : F => x ∈ U)).card = Fintype.card K ^ Module.finrank K U := by
  rw [← Module.card_eq_pow_finrank (K := K) (V := U), Fintype.card_subtype]

lemma coeff_one_sp_ne_zero (U : Submodule K F) : (sp U).coeff 1 ≠ 0 := by
  have h0 : (0 : F) ∈ Finset.univ.filter (fun x : F => x ∈ U) := by simp
  have : sp U = X * ∏ x ∈ (Finset.univ.filter (fun x : F => x ∈ U)).erase 0, (X - C x) := by
    unfold sp
    rw [← Finset.mul_prod_erase _ _ h0]
    simp
  rw [this, coeff_X_mul, coeff_zero_eq_eval_zero, eval_prod]
  refine Finset.prod_ne_zero_iff.mpr fun x hx => ?_
  have := (Finset.mem_erase.mp hx).1
  simpa [sub_eq_zero] using this

lemma coeff_of_repr (Q : ℕ) (hQ2 : 2 ≤ Q) (n : ℕ) (c : ℕ → F) (P : F[X])
    (hP : P = ∑ i ∈ Finset.range (n + 1), C (c i) * X ^ (Q ^ i)) (i : ℕ) (hi : i ≤ n) :
    P.coeff (Q ^ i) = c i := by
  rw [hP, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [if_neg]
    intro h
    exact hj (Nat.pow_right_injective hQ2 h).symm
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h


lemma sp_inj (Q : ℕ) (hQ : Q = p ^ a) (ha : 1 ≤ a) (hKQ : Fintype.card K = Q)
    (V : Subfield F) (hV : ∀ x : K, algebraMap K F x ∈ V)
    (Vm : Submodule K F) (hVm : ∀ x, x ∈ Vm ↔ x ∈ V) (k : ℕ) (hVfin : Module.finrank K Vm = k + 4)
    (U U' : Submodule K F) (hU : Module.finrank K U = k + 2) (hU' : Module.finrank K U' = k + 2)
    (hUV : ∀ x ∈ U, x ∈ V) (hUV' : ∀ x ∈ U', x ∈ V)
    (h1 : (sp U).coeff (Q ^ (k + 1)) = (sp U').coeff (Q ^ (k + 1)))
    (h0 : (sp U).coeff (Q ^ k) = (sp U').coeff (Q ^ k)) : U = U' := by
  have hQ2 : 2 ≤ Q := by
    have h2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    rw [hQ]
    calc 2 ≤ p := h2
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ a := Nat.pow_le_pow_right (by omega) ha
  obtain ⟨c, _, hcn, hc⟩ := sp_struct p a Q hQ ha hKQ V hV (k + 2) U hU hUV
  obtain ⟨c', _, hcn', hc'⟩ := sp_struct p a Q hQ ha hKQ V hV (k + 2) U' hU' hUV'
  have e1 : c (k + 1) = c' (k + 1) := by
    rw [← coeff_of_repr Q hQ2 (k + 2) c _ hc (k + 1) (by omega),
      ← coeff_of_repr Q hQ2 (k + 2) c' _ hc' (k + 1) (by omega)]; exact h1
  have e0 : c k = c' k := by
    rw [← coeff_of_repr Q hQ2 (k + 2) c _ hc k (by omega),
      ← coeff_of_repr Q hQ2 (k + 2) c' _ hc' k (by omega)]; exact h0
  have hD : sp U - sp U' = ∑ i ∈ Finset.range k, C (c i - c' i) * X ^ (Q ^ i) := by
    rw [hc, hc', ← Finset.sum_sub_distrib]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, hcn, hcn', e1, e0]
    simp [C_sub, sub_mul]
  have hdeg : (sp U - sp U').natDegree < Q ^ k := by
    rw [hD]
    have hQk : 1 ≤ Q ^ k := Nat.one_le_pow _ _ (by omega)
    have : (∑ i ∈ Finset.range k, C (c i - c' i) * X ^ (Q ^ i)).natDegree ≤ Q ^ k - 1 := by
      refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
      refine (natDegree_C_mul_X_pow_le _ _).trans ?_
      have := Nat.pow_lt_pow_right hQ2 (Finset.mem_range.mp hi)
      omega
    omega
  have hinf : k ≤ Module.finrank K (U ⊓ U' : Submodule K F) := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq U U'
    have h2 : Module.finrank K (U ⊔ U' : Submodule K F) ≤ Module.finrank K Vm := by
      refine Submodule.finrank_mono ?_
      intro x hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
      exact (hVm _).mpr (V.add_mem (hUV y hy) (hUV' z hz))
    omega
  have hzero : sp U - sp U' = 0 := by
    by_contra hne
    have hsub : (Finset.univ.filter (fun x : F => x ∈ (U ⊓ U' : Submodule K F))).val
        ⊆ (sp U - sp U').roots := by
      intro x hx
      rw [Finset.mem_val, Finset.mem_filter] at hx
      rw [mem_roots hne, IsRoot, eval_sub, (sp_eval_eq_zero_iff U x).mpr hx.2.1,
        (sp_eval_eq_zero_iff U' x).mpr hx.2.2, sub_self]
    have := card_le_degree_of_subset_roots hsub
    rw [card_filter_mem, hKQ] at this
    have h3 : Q ^ k ≤ Q ^ Module.finrank K (U ⊓ U' : Submodule K F) :=
      Nat.pow_le_pow_right (by omega) hinf
    omega
  have hspeq : sp U = sp U' := sub_eq_zero.mp hzero
  ext x
  rw [← sp_eval_eq_zero_iff U, ← sp_eval_eq_zero_iff U', hspeq]

end Sub
end ProxGapTight.Dev.Syn



namespace ProxGapTight.Dev.Syn


section Lines

open Classical

variable {F : Type} [Field F] [Fintype F]
variable {K : Type} [Field K] [Fintype K] [Algebra K F]

lemma line_eq_span {m : ℕ} (ℓ : Lines K m) (v : Fin m → K) (hv : v ∈ ℓ.1) (hv0 : v ≠ 0) :
    ℓ.1 = Submodule.span K {v} := by
  symm
  refine Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem v ℓ.1).mpr hv) ?_
  rw [finrank_span_singleton hv0, ℓ.2]

lemma line_sum {m : ℕ} (e' : (Fin m → K) →ₗ[K] F) (he' : Function.Injective e')
    (v : Lines K m → (Fin m → K)) (hv : ∀ ℓ, v ℓ ∈ ℓ.1 ∧ v ℓ ≠ 0)
    (Q : ℕ) (hKQ : Fintype.card K = Q) (hQF : (Q : F) = 0)
    (W : Submodule K (Fin m → K)) (d : ℕ) (hd1 : 1 ≤ d) (hd : (Q - 1) ∣ d) :
    ∑ ℓ ∈ Finset.univ.filter (fun ℓ : Lines K m => ℓ.1 ≤ W), (e' (v ℓ)) ^ d
      = - psum (Finset.univ.filter (fun x : F => x ∈ W.map e')) d := by
  set Lfin := Finset.univ.filter (fun ℓ : Lines K m => ℓ.1 ≤ W) with hLfin
  set Kun := Finset.univ.filter (fun c : K => c ≠ 0) with hKun
  set Wfin := Finset.univ.filter (fun x : Fin m → K => x ∈ W) with hWfin
  have hpow : ∀ c : K, c ≠ 0 → (algebraMap K F c) ^ d = 1 := by
    intro c hc
    obtain ⟨j, hj⟩ := hd
    have := FiniteField.pow_card_sub_one_eq_one c hc
    rw [hKQ] at this
    rw [hj, pow_mul, ← map_pow, this]
    simp
  have h1 : psum (Finset.univ.filter (fun y : F => y ∈ W.map e')) d
      = ∑ x ∈ Wfin, (e' x) ^ d := by
    have : Finset.univ.filter (fun y : F => y ∈ W.map e') = Wfin.image e' := by
      ext y; simp [Submodule.mem_map, hWfin]
    rw [psum, this, Finset.sum_image (fun a _ b _ h => he' h)]
  have h0mem : (0 : Fin m → K) ∈ Wfin := by simp [hWfin]
  have h2 : ∑ x ∈ Wfin, (e' x) ^ d = ∑ x ∈ Wfin.erase 0, (e' x) ^ d := by
    rw [← Finset.add_sum_erase _ _ h0mem]
    simp [zero_pow (show d ≠ 0 by omega)]
  have h3 : ∑ p ∈ Lfin ×ˢ Kun, (e' (p.2 • v p.1)) ^ d = ∑ x ∈ Wfin.erase 0, (e' x) ^ d := by
    refine Finset.sum_bij (fun p _ => p.2 • v p.1) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_product, hLfin, hKun, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [Finset.mem_erase, hWfin, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨smul_ne_zero hp.2 (hv p.1).2, W.smul_mem _ (hp.1 (hv p.1).1)⟩
    · intro p hp q hq hpq
      simp only [Finset.mem_product, hLfin, hKun, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
      have hℓ : p.1 = q.1 := by
        have hp1 := line_eq_span p.1 _ (hv p.1).1 (hv p.1).2
        have hq1 := line_eq_span q.1 _ (hv q.1).1 (hv q.1).2
        have hle : p.1.1 ≤ q.1.1 := by
          rw [hp1, Submodule.span_singleton_le_iff_mem]
          have : v p.1 = p.2⁻¹ • (q.2 • v q.1) := by
            rw [← hpq, smul_smul, inv_mul_cancel₀ hp.2, one_smul]
          rw [this, hq1]
          exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
        have heq := Submodule.eq_of_le_of_finrank_eq hle (by rw [p.1.2, q.1.2])
        exact Subtype.ext heq
      have hvv : v p.1 = v q.1 := by rw [hℓ]
      rw [hvv] at hpq
      have : p.2 = q.2 := by
        have := (smul_left_injective K (hv q.1).2) hpq
        exact this
      exact Prod.ext hℓ this
    · intro x hx
      simp only [Finset.mem_erase, hWfin, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨hx0, hxW⟩ := hx
      let ℓ : Lines K m := ⟨Submodule.span K {x}, finrank_span_singleton hx0⟩
      have hℓW : ℓ.1 ≤ W := (Submodule.span_singleton_le_iff_mem x W).mpr hxW
      have hvℓ : v ℓ ∈ Submodule.span K {x} := (hv ℓ).1
      obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hvℓ
      have ht0 : t ≠ 0 := by
        rintro rfl
        exact (hv ℓ).2 (by rw [← ht, zero_smul])
      refine ⟨(ℓ, t⁻¹), ?_, ?_⟩
      · simp only [Finset.mem_product, hLfin, hKun, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hℓW, inv_ne_zero ht0⟩
      · simp only
        rw [← ht, smul_smul, inv_mul_cancel₀ ht0, one_smul]
    · intro p hp; rfl
  have h4 : ∑ p ∈ Lfin ×ˢ Kun, (e' (p.2 • v p.1)) ^ d
      = ∑ p ∈ Lfin ×ˢ Kun, (e' (v p.1)) ^ d := by
    refine Finset.sum_congr rfl fun p hp => ?_
    simp only [Finset.mem_product, hKun, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [map_smul, Algebra.smul_def, mul_pow, hpow _ hp.2, one_mul]
  have hcard : Kun.card = Q - 1 := by
    rw [hKun, Finset.filter_ne' , Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp [hKQ]
  have h5 : ∑ p ∈ Lfin ×ˢ Kun, (e' (v p.1)) ^ d
      = ((Q - 1 : ℕ) : F) * ∑ ℓ ∈ Lfin, (e' (v ℓ)) ^ d := by
    rw [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    show ∑ y ∈ Kun, e' (v ℓ) ^ d = _
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
  have hQ1 : ((Q - 1 : ℕ) : F) = -1 := by
    have hQpos : 1 ≤ Q := by rw [← hKQ]; exact Fintype.card_pos
    rw [Nat.cast_sub hQpos, hQF]; simp
  rw [h1, h2, ← h3, h4, h5, hQ1]
  ring

end Lines
end ProxGapTight.Dev.Syn



namespace ProxGapTight.Dev.Syn

open Classical

lemma charP_of_card {L : Type} [Field L] [Fintype L] (p n : ℕ) [Fact p.Prime]
    (h : Fintype.card L = p ^ n) : CharP L p := by
  obtain ⟨n', hp', hc⟩ := FiniteField.card L (ringChar L)
  have hr : ringChar L = p := by
    have hdvd : ringChar L ∣ p ^ n := by
      rw [← h, hc]; exact dvd_pow_self _ n'.ne_zero
    exact (Nat.prime_dvd_prime_iff_eq hp' Fact.out).mp (hp'.dvd_of_dvd_pow hdvd)
  rw [← hr]; exact ringChar.charP L

lemma finrank_zmod_of_card (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L]
    (n : ℕ) (h : Fintype.card L = p ^ n) :
    Module.finrank (ZMod p) L = n := by
  have := FiniteField.pow_finrank_eq_card p L
  rw [h] at this
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le this

lemma exists_setup (p a m : ℕ) [Fact p.Prime] (ha : 1 ≤ a) (hm : 1 ≤ m)
    (K : Type) [Field K] [Fintype K] (hK : Fintype.card K = p ^ a)
    (F : Type) [Field F] [Fintype F] (hF : Fintype.card F = (p ^ a) ^ (2 * m)) :
    ∃ (ι : K →+* F) (V : Subfield F), (∀ x : K, ι x ∈ V) ∧
      (Finset.univ.filter (fun x : F => x ∈ V)).card = (p ^ a) ^ m := by
  have hF' : Fintype.card F = p ^ (a * (2 * m)) := by rw [hF, ← pow_mul]
  haveI hcK := charP_of_card (L := K) p a hK
  haveI hcF := charP_of_card (L := F) p _ hF'
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  have hfK := finrank_zmod_of_card p K a hK
  have hfF := finrank_zmod_of_card p F _ hF'
  have ham : a * m ≠ 0 := by positivity
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod p) (K := K) (L := F)
    (by rw [hfK, hfF]; exact Dvd.intro (2 * m) rfl)
  obtain ⟨g⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod p)
    (K := GaloisField p (a * m)) (L := F)
    (by rw [GaloisField.finrank p ham, hfF]; exact ⟨2, by ring⟩)
  letI : Fintype (GaloisField p (a * m)) := Fintype.ofFinite _
  have hLcard : Fintype.card (GaloisField p (a * m)) = (p ^ a) ^ m := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p _ ham, pow_mul]
  have hQ2 : 2 ≤ p ^ a := by
    have h2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    calc 2 ≤ p := h2
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ a := Nat.pow_le_pow_right (by omega) ha
  have hQm : 2 ≤ (p ^ a) ^ m := by
    calc 2 ≤ p ^ a := hQ2
      _ = (p ^ a) ^ 1 := (pow_one _).symm
      _ ≤ (p ^ a) ^ m := Nat.pow_le_pow_right (by omega) hm
  let Vfin : Finset F := Finset.univ.image g
  have hVcard : Vfin.card = (p ^ a) ^ m := by
    have hinj : Function.Injective g := RingHom.injective g.toRingHom
    show (Finset.univ.image g).card = _
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, hLcard]
  let S : Finset F := Finset.univ.filter (fun x : F => x ^ ((p ^ a) ^ m) = x)
  have hsub : Vfin ⊆ S := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← map_pow, ← hLcard, FiniteField.pow_card]
  have hS : S.card ≤ (p ^ a) ^ m := by
    have hR : (X ^ ((p ^ a) ^ m) - X : F[X]) ≠ 0 := by
      intro h
      have := congrArg natDegree h
      rw [natDegree_sub_eq_left_of_natDegree_lt (by rw [natDegree_X, natDegree_X_pow]; omega)] at this
      rw [natDegree_X_pow, natDegree_zero] at this
      omega
    have hsub2 : S.val ⊆ (X ^ ((p ^ a) ^ m) - X : F[X]).roots := by
      intro x hx
      rw [Finset.mem_val] at hx
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [mem_roots hR]
      simp [hx]
    have := card_le_degree_of_subset_roots hsub2
    rw [natDegree_sub_eq_left_of_natDegree_lt (by rw [natDegree_X, natDegree_X_pow]; omega)] at this
    simpa using this
  have hVS : Vfin = S := Finset.eq_of_subset_of_card_le hsub (by omega)
  refine ⟨f.toRingHom, g.toRingHom.fieldRange, fun x => ?_, ?_⟩
  · have : f.toRingHom x ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      show (f x) ^ ((p ^ a) ^ m) = f x
      rw [← map_pow, ← hK, FiniteField.pow_card_pow]
    rw [← hVS] at this
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp this
    exact ⟨y, hy⟩
  · have : Finset.univ.filter (fun x : F => x ∈ g.toRingHom.fieldRange) = Vfin := by
      ext x
      simp [Vfin, RingHom.mem_fieldRange]
    rw [this, hVcard]

end ProxGapTight.Dev.Syn

namespace ProxGapTight.Dev.Syn

section Main

open Classical

variable {F : Type} [Field F] [Fintype F]
variable {K : Type} [Field K] [Fintype K] [Algebra K F]

lemma syn_data (p a : ℕ) [Fact p.Prime] [CharP F p] (Q : ℕ) (hQ : Q = p ^ a) (ha : 1 ≤ a)
    (hKQ : Fintype.card K = Q) (V : Subfield F) (hV : ∀ x : K, algebraMap K F x ∈ V)
    (k : ℕ) (U : Submodule K F) (hU : Module.finrank K U = k + 2) (hUV : ∀ x ∈ U, x ∈ V) :
    psum (Finset.univ.filter (fun x : F => x ∈ U)) (Q ^ (k + 2) - 1) = (sp U).coeff 1 ∧
    psum (Finset.univ.filter (fun x : F => x ∈ U)) (2 * Q ^ (k + 2) - Q ^ (k + 1) - 1)
      = -((sp U).coeff 1 * (sp U).coeff (Q ^ (k + 1))) ∧
    psum (Finset.univ.filter (fun x : F => x ∈ U)) (2 * Q ^ (k + 2) - Q ^ k - 1)
      = -((sp U).coeff 1 * (sp U).coeff (Q ^ k)) ∧
    (sp U).coeff (Q ^ (k + 1)) ∈ V ∧ (sp U).coeff (Q ^ k) ∈ V ∧ (sp U).coeff 1 ≠ 0 := by
  have hQ2 := two_le_Q p a Q hQ ha
  obtain ⟨c, hcV, hcn, hc⟩ := sp_struct p a Q hQ ha hKQ V hV (k + 2) U hU hUV
  have hcard : (Finset.univ.filter (fun x : F => x ∈ U)).card = Q ^ (k + 2) := by
    rw [card_filter_mem, hKQ, hU]
  have hc' : ∏ w ∈ Finset.univ.filter (fun x : F => x ∈ U), (X - C w)
      = ∑ i ∈ Finset.range (k + 3), C (c i) * X ^ (Q ^ i) := hc
  obtain ⟨h0, h1, h2⟩ := power_sums Q hQ ha k _ c hcard hcn hc'
  have e0 : (sp U).coeff 1 = c 0 := by
    have := coeff_of_repr Q hQ2 (k + 2) c _ hc 0 (by omega)
    rwa [pow_zero] at this
  have e1 : (sp U).coeff (Q ^ (k + 1)) = c (k + 1) :=
    coeff_of_repr Q hQ2 (k + 2) c _ hc (k + 1) (by omega)
  have e2 : (sp U).coeff (Q ^ k) = c k := coeff_of_repr Q hQ2 (k + 2) c _ hc k (by omega)
  refine ⟨by rw [e0, h0], by rw [e0, e1, h1], by rw [e0, e2, h2], by rw [e1]; exact hcV _,
    by rw [e2]; exact hcV _, coeff_one_sp_ne_zero U⟩

end Main

end ProxGapTight.Dev.Syn

namespace ProxGapTight.Dev.Syn

open Classical

theorem main_aux (p a m : ℕ) [Fact p.Prime] (hm : 4 ≤ m)
    (K : Type) [Field K] [Fintype K] (hK : Fintype.card K = p ^ a)
    (F : Type) [Field F] [Fintype F] (hF : Fintype.card F = (p ^ a) ^ (2 * m)) :
    ∃ Ψ₀ : (Lines K m → F) →ₗ[F] (Fin 2 → F),
      (∀ W : Codim2 K m, Ψ₀ (incVec F W) ≠ 0) ∧
      (∀ W W' : Codim2 K m, W ≠ W' →
        LinearIndependent F ![Ψ₀ (incVec F W), Ψ₀ (incVec F W')]) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
  have ha : 1 ≤ a := by
    by_contra h
    have h0 : a = 0 := by omega
    have := Fintype.one_lt_card (α := K)
    rw [hK, h0] at this
    simp at this
  have hF' : Fintype.card F = p ^ (a * (2 * (k + 4))) := by rw [hF, ← pow_mul]
  haveI hcF : CharP F p := charP_of_card p _ hF'
  obtain ⟨ι, V, hιV, hVcard⟩ := exists_setup p a (k + 4) ha (by omega) K hK F hF
  letI : Algebra K F := ι.toAlgebra
  have hιV' : ∀ x : K, algebraMap K F x ∈ V := hιV
  have hQ2 : 2 ≤ p ^ a := two_le_Q p a (p ^ a) rfl ha
  let Vm : Submodule K F :=
    { carrier := {x | x ∈ V}
      add_mem' := fun hx hy => V.add_mem hx hy
      zero_mem' := V.zero_mem
      smul_mem' := fun c x hx => by
        rw [Algebra.smul_def]; exact V.mul_mem (hιV' c) hx }
  have hVm : ∀ x, x ∈ Vm ↔ x ∈ V := fun _ => Iff.rfl
  have hVfin : Module.finrank K Vm = k + 4 := by
    have h1 : Fintype.card Vm = (p ^ a) ^ (k + 4) := by
      rw [Fintype.card_subtype]; exact hVcard
    have h2 := Module.card_eq_pow_finrank (K := K) (V := Vm)
    rw [h1, hK] at h2
    exact (Nat.pow_right_injective hQ2 h2).symm
  obtain ⟨β, hβ⟩ : ∃ β : F, β ∉ V := by
    by_contra h
    push Not at h
    have : Finset.univ.filter (fun x : F => x ∈ V) = Finset.univ :=
      Finset.filter_true_of_mem (fun x _ => h x)
    rw [this, Finset.card_univ, hF] at hVcard
    have h3 := Nat.pow_right_injective hQ2 (hVcard : (p ^ a) ^ (2 * (k + 4)) = (p ^ a) ^ (k + 4))
    omega
  let e : (Fin (k + 4) → K) ≃ₗ[K] Vm :=
    LinearEquiv.ofFinrankEq _ _ (by rw [Module.finrank_fin_fun, hVfin])
  let e' : (Fin (k + 4) → K) →ₗ[K] F := Vm.subtype ∘ₗ (e : (Fin (k + 4) → K) →ₗ[K] Vm)
  have he' : Function.Injective e' := Subtype.val_injective.comp e.injective
  have hve' : ∀ x, e' x ∈ V := fun x => (e x).2
  have hv : ∀ ℓ : Lines K (k + 4), ∃ x : Fin (k + 4) → K, x ∈ ℓ.1 ∧ x ≠ 0 := by
    intro ℓ
    refine Submodule.exists_mem_ne_zero_of_ne_bot ?_
    intro h
    have := ℓ.2
    rw [h, finrank_bot] at this
    omega
  choose v hv1 using hv
  set Q := p ^ a with hQdef
  have hKQ : Fintype.card K = Q := hK
  have hQF : (Q : F) = 0 := by
    have := Qcast_zero (F := F) p a Q hQdef ha 1 le_rfl
    simpa using this
  have hdiv : ∀ j, (Q - 1) ∣ Q ^ j - 1 := fun j => Nat.sub_one_dvd_pow_sub_one Q j
  have hN2 : 2 ≤ Q ^ (k + 2) :=
    calc 2 ≤ Q := hQ2
      _ = Q ^ 1 := (pow_one Q).symm
      _ ≤ Q ^ (k + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hA : Q ^ (k + 1) < Q ^ (k + 2) := Nat.pow_lt_pow_right hQ2 (by omega)
  have hT : Q ^ k < Q ^ (k + 2) := Nat.pow_lt_pow_right hQ2 (by omega)
  have hA1 : 1 ≤ Q ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
  have hT1 : 1 ≤ Q ^ k := Nat.one_le_pow _ _ (by omega)
  have hd0 : (Q - 1) ∣ Q ^ (k + 2) - 1 := hdiv _
  have hd1 : (Q - 1) ∣ 2 * Q ^ (k + 2) - Q ^ (k + 1) - 1 := by
    have : 2 * Q ^ (k + 2) - Q ^ (k + 1) - 1
        = (Q ^ (k + 2) - 1) + ((Q ^ (k + 2) - 1) - (Q ^ (k + 1) - 1)) := by omega
    rw [this]; exact dvd_add (hdiv _) (Nat.dvd_sub (hdiv _) (hdiv _))
  have hd2 : (Q - 1) ∣ 2 * Q ^ (k + 2) - Q ^ k - 1 := by
    have : 2 * Q ^ (k + 2) - Q ^ k - 1
        = (Q ^ (k + 2) - 1) + ((Q ^ (k + 2) - 1) - (Q ^ k - 1)) := by omega
    rw [this]; exact dvd_add (hdiv _) (Nat.dvd_sub (hdiv _) (hdiv _))
  let s : Lines K (k + 4) → (Fin 2 → F) := fun ℓ =>
    ![(e' (v ℓ)) ^ (Q ^ (k + 2) - 1),
      (e' (v ℓ)) ^ (2 * Q ^ (k + 2) - Q ^ (k + 1) - 1)
        + β * (e' (v ℓ)) ^ (2 * Q ^ (k + 2) - Q ^ k - 1)]
  let Ψ : (Lines K (k + 4) → F) →ₗ[F] (Fin 2 → F) :=
    { toFun := fun f => ∑ ℓ, f ℓ • s ℓ
      map_add' := by intro f g; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intro c f; simp [Finset.smul_sum, smul_smul] }
  have hkey : ∀ (W : Codim2 K (k + 4)) (g : Lines K (k + 4) → F),
      ∑ ℓ, incVec F W ℓ * g ℓ
        = ∑ ℓ ∈ Finset.univ.filter (fun ℓ : Lines K (k + 4) => ℓ.1 ≤ W.1), g ℓ := by
    intro W g
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    unfold incVec
    split_ifs <;> simp
  have hΨ : ∀ W : Codim2 K (k + 4), Ψ (incVec F W) =
      (sp (W.1.map e')).coeff 1 • ![(-1 : F),
        (sp (W.1.map e')).coeff (Q ^ (k + 1)) + β * (sp (W.1.map e')).coeff (Q ^ k)] := by
    intro W
    have hfin : Module.finrank K (W.1.map e') = k + 2 := by
      rw [← (Submodule.equivMapOfInjective e' he' W.1).finrank_eq]
      have := W.2; omega
    have hsubV : ∀ x ∈ W.1.map e', x ∈ V := by
      intro x hx; obtain ⟨y, _, rfl⟩ := hx; exact hve' y
    obtain ⟨h0, h1, h2, -, -, -⟩ := syn_data p a Q hQdef ha hKQ V hιV' k _ hfin hsubV
    have s0 := line_sum e' he' v (fun ℓ => hv1 ℓ) Q hKQ hQF W.1 (Q ^ (k + 2) - 1) (by omega) hd0
    have s1 := line_sum e' he' v (fun ℓ => hv1 ℓ) Q hKQ hQF W.1
      (2 * Q ^ (k + 2) - Q ^ (k + 1) - 1) (by omega) hd1
    have s2 := line_sum e' he' v (fun ℓ => hv1 ℓ) Q hKQ hQF W.1
      (2 * Q ^ (k + 2) - Q ^ k - 1) (by omega) hd2
    rw [h0] at s0
    rw [h1] at s1
    rw [h2] at s2
    have c0 : Ψ (incVec F W) 0 = ∑ ℓ, incVec F W ℓ * (e' (v ℓ)) ^ (Q ^ (k + 2) - 1) := by
      simp [Ψ, s, Finset.sum_apply]
    have c1 : Ψ (incVec F W) 1 = ∑ ℓ, incVec F W ℓ * ((e' (v ℓ)) ^ (2 * Q ^ (k + 2) - Q ^ (k + 1) - 1)
        + β * (e' (v ℓ)) ^ (2 * Q ^ (k + 2) - Q ^ k - 1)) := by
      simp [Ψ, s, Finset.sum_apply]
    funext i
    fin_cases i
    · show Ψ (incVec F W) 0 = _
      rw [c0, hkey, s0]
      simp
    · show Ψ (incVec F W) 1 = _
      rw [c1, hkey, Finset.sum_add_distrib, ← Finset.mul_sum, s1, s2]
      simp
      ring
  have hfinW : ∀ W : Codim2 K (k + 4), Module.finrank K (W.1.map e') = k + 2 := by
    intro W
    rw [← (Submodule.equivMapOfInjective e' he' W.1).finrank_eq]
    have := W.2; omega
  have hsubW : ∀ W : Codim2 K (k + 4), ∀ x ∈ W.1.map e', x ∈ V := by
    intro W x hx; obtain ⟨y, _, rfl⟩ := hx; exact hve' y
  have hdat := fun W : Codim2 K (k + 4) =>
    syn_data p a Q hQdef ha hKQ V hιV' k (W.1.map e') (hfinW W) (hsubW W)
  refine ⟨Ψ, ?_, ?_⟩
  · intro W h
    have h0 := congrFun h 0
    rw [hΨ W] at h0
    obtain ⟨-, -, -, -, -, hne⟩ := hdat W
    apply hne
    simpa using h0
  · intro W W' hne
    rw [hΨ W, hΨ W']
    obtain ⟨-, -, -, hA1V, hA2V, ha0⟩ := hdat W
    obtain ⟨-, -, -, hA1V', hA2V', ha0'⟩ := hdat W'
    have hT : (sp (W.1.map e')).coeff (Q ^ (k + 1)) + β * (sp (W.1.map e')).coeff (Q ^ k)
        ≠ (sp (W'.1.map e')).coeff (Q ^ (k + 1)) + β * (sp (W'.1.map e')).coeff (Q ^ k) := by
      intro hTT
      apply hne
      have hA2 : (sp (W.1.map e')).coeff (Q ^ k) = (sp (W'.1.map e')).coeff (Q ^ k) := by
        by_contra hneq
        have hsub : (sp (W.1.map e')).coeff (Q ^ k) - (sp (W'.1.map e')).coeff (Q ^ k) ≠ 0 :=
          sub_ne_zero.mpr hneq
        apply hβ
        have : β = ((sp (W'.1.map e')).coeff (Q ^ (k + 1)) - (sp (W.1.map e')).coeff (Q ^ (k + 1)))
            / ((sp (W.1.map e')).coeff (Q ^ k) - (sp (W'.1.map e')).coeff (Q ^ k)) := by
          field_simp
          linear_combination hTT
        rw [this]
        exact V.div_mem (V.sub_mem hA1V' hA1V) (V.sub_mem hA2V hA2V')
      have hA1 : (sp (W.1.map e')).coeff (Q ^ (k + 1)) = (sp (W'.1.map e')).coeff (Q ^ (k + 1)) := by
        rw [hA2] at hTT
        exact add_right_cancel hTT
      have := sp_inj p a Q hQdef ha hKQ V hιV' Vm hVm k hVfin (W.1.map e') (W'.1.map e')
        (hfinW W) (hfinW W') (hsubW W) (hsubW W') hA1 hA2
      exact Subtype.ext (Submodule.map_injective_of_injective he' this)
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have c0 := congrFun hst 0
    have c1 := congrFun hst 1
    simp at c0 c1
    have ht : t * (sp (W'.1.map e')).coeff 1 *
        (((sp (W'.1.map e')).coeff (Q ^ (k + 1)) + β * (sp (W'.1.map e')).coeff (Q ^ k))
        - ((sp (W.1.map e')).coeff (Q ^ (k + 1)) + β * (sp (W.1.map e')).coeff (Q ^ k))) = 0 := by
      linear_combination c1 + ((sp (W.1.map e')).coeff (Q ^ (k + 1))
        + β * (sp (W.1.map e')).coeff (Q ^ k)) * c0
    have hsub : ((sp (W'.1.map e')).coeff (Q ^ (k + 1)) + β * (sp (W'.1.map e')).coeff (Q ^ k))
        - ((sp (W.1.map e')).coeff (Q ^ (k + 1)) + β * (sp (W.1.map e')).coeff (Q ^ k)) ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm hT)
    have ht0 : t = 0 := by
      rcases mul_eq_zero.mp ht with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact h
        · exact absurd h ha0'
      · exact absurd h hsub
    refine ⟨?_, ht0⟩
    subst ht0
    have : s * (sp (W.1.map e')).coeff 1 = 0 := by linear_combination -c0
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h ha0

end ProxGapTight.Dev.Syn

namespace ProxGapTight

theorem chk_lemma_3_5_syndromes (p a m : ℕ) [Fact p.Prime] (hm : 4 ≤ m)
    (K : Type) [Field K] [Fintype K] (hK : Fintype.card K = p ^ a)
    (F : Type) [Field F] [Fintype F] (hF : Fintype.card F = (p ^ a) ^ (2 * m)) :
    ∃ Ψ₀ : (Lines K m → F) →ₗ[F] (Fin 2 → F),
      (∀ W : Codim2 K m, Ψ₀ (incVec F W) ≠ 0) ∧
      (∀ W W' : Codim2 K m, W ≠ W' →
        LinearIndependent F ![Ψ₀ (incVec F W), Ψ₀ (incVec F W')]) :=
  Dev.Syn.main_aux p a m hm K hK F hF

end ProxGapTight
end

theorem solution : type_of% @ProxGapTight.chk_lemma_3_5_syndromes := @ProxGapTight.chk_lemma_3_5_syndromes
