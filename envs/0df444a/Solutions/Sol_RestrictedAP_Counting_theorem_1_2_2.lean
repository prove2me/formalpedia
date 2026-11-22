-- Prove2me | solution 2 for RestrictedAP.Counting.theorem_1_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-22T22:50:05.076295+00:00
-- url     : https://prove2.me/submissions/ea1cb3cb-4c3e-4b7e-9682-210b9a273915
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_MuP
import Definitions.Def_RestrictedAP_Counting_SomewhatRestricted3APCount
import Theorems.Thm_RestrictedAP_Counting_claim_5_14_monotone
import Theorems.Thm_RestrictedAP_Counting_lemma_5_27
import Theorems.Thm_RestrictedAP_Counting_remark_1_2_no_embedding

section
open Classical
set_option autoImplicit false

namespace RestrictedAP.Counting.Dev.DirectT12

variable (p : ℕ) [NeZero p]

/-- The one-coordinate somewhat restricted 3-AP map. -/
def ap3 : ZMod p × Fin 3 → ZMod p × ZMod p × ZMod p :=
  fun xa => (xa.1, xa.1 + ((xa.2 : ℕ) : ZMod p), xa.1 + 2 * ((xa.2 : ℕ) : ZMod p))

/-- For `p ≥ 3`, the pair `(x,a)` is recoverable from `(x,x+a,x+2a)`. -/
theorem ap3_injective (hp : 3 ≤ p) : Function.Injective (ap3 p) := by
  rintro ⟨x, a⟩ ⟨y, b⟩ h
  have hxy : x = y := congrArg Prod.fst h
  have h2 : x + ((a : ℕ) : ZMod p) = y + ((b : ℕ) : ZMod p) :=
    congrArg (fun t => t.2.1) h
  rw [hxy] at h2
  have habcast : ((a : ℕ) : ZMod p) = ((b : ℕ) : ZMod p) := add_left_cancel h2
  have ha : (a : ℕ) < p := a.isLt.trans_le hp
  have hb : (b : ℕ) < p := b.isLt.trans_le hp
  have hval := congrArg ZMod.val habcast
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hval
  have hab : a = b := Fin.ext hval
  cases hxy
  cases hab
  rfl

theorem fiber_card_le_one (hp : 3 ≤ p) (t : ZMod p × ZMod p × ZMod p) :
    (Finset.univ.filter (fun s : ZMod p × Fin 3 => ap3 p s = t)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro s hs u hu
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs hu
  exact ap3_injective p hp (hs.trans hu.symm)

/-- Every atom of `muP p` has weight exactly `1/(3p)`. -/
theorem muP_atom_value (hp : 3 ≤ p) (t : ZMod p × ZMod p × ZMod p)
    (ht : muP p t ≠ 0) : muP p t = 1 / (3 * (p : ℝ)) := by
  have hc : (Finset.univ.filter (fun s : ZMod p × Fin 3 => ap3 p s = t)).card ≠ 0 := by
    intro hc
    apply ht
    unfold muP
    change ((Finset.univ.filter (fun s : ZMod p × Fin 3 => ap3 p s = t)).card : ℝ) /
      (3 * (p : ℝ)) = 0
    simp [hc]
  have hc1 : (Finset.univ.filter (fun s : ZMod p × Fin 3 => ap3 p s = t)).card = 1 :=
    Nat.le_antisymm (fiber_card_le_one p hp t) (Nat.one_le_iff_ne_zero.mpr hc)
  unfold muP
  change ((Finset.univ.filter (fun s : ZMod p × Fin 3 => ap3 p s = t)).card : ℝ) /
    (3 * (p : ℝ)) = _
  rw [hc1]
  norm_num

theorem diag_ne_zero (x : ZMod p) : muP p (x, x, x) ≠ 0 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  unfold muP
  simp only [ne_eq, div_eq_zero_iff, Nat.cast_eq_zero, not_or]
  refine ⟨?_, by positivity⟩
  have hc : 0 < (Finset.univ.filter (fun xa : ZMod p × Fin 3 =>
      (xa.1, xa.1 + ((xa.2 : ℕ) : ZMod p), xa.1 + 2 * ((xa.2 : ℕ) : ZMod p)) =
        (x, x, x))).card :=
    Finset.card_pos.mpr ⟨(x, 0), by simp⟩
  exact_mod_cast hc.ne'

theorem muP_minAtom (hp : 3 ≤ p) : IsMinAtom (muP p) (1 / (3 * (p : ℝ))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  refine ⟨by positivity, ?_, ?_⟩
  · intro t ht
    rw [muP_atom_value p hp t ht]
  · exact ⟨(0, 0, 0), muP_atom_value p hp (0, 0, 0) (diag_ne_zero p 0)⟩

theorem muP_eq (t : ZMod p × ZMod p × ZMod p) :
    muP p t = (1 / (3 * (p : ℝ))) * ∑ s : ZMod p × Fin 3, if ap3 p s = t then 1 else 0 := by
  unfold muP
  rw [Finset.card_filter]
  push_cast
  rw [div_eq_mul_inv, mul_comm, one_div]
  rfl

theorem tensor_eq (n : ℕ) (t : Fin n → ZMod p × ZMod p × ZMod p) :
    tensorPow (muP p) n t = (1 / (3 * (p : ℝ))) ^ n *
      ∑ s : Fin n → ZMod p × Fin 3, if (fun i => ap3 p (s i)) = t then 1 else 0 := by
  unfold tensorPow
  simp_rw [muP_eq]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  have := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (ZMod p × Fin 3)))
    (fun i s => if ap3 p s = t i then (1 : ℝ) else 0)
  rw [Fintype.piFinset_univ] at this
  rw [this]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.prod_boole]
  simp only [funext_iff, Finset.mem_univ, forall_true_left]

/-- The tensor law of the coordinatewise 3-APs is exactly the counting probability in Theorem 1.2. -/
theorem triple_eq (n : ℕ) (A : Finset (Fin n → ZMod p)) :
    tripleProb (muP p) n A = somewhatRestricted3APProb p n A := by
  unfold tripleProb somewhatRestricted3APProb somewhatRestricted3APCount
  simp_rw [tensor_eq]
  set c : ℝ := (1 / (3 * (p : ℝ))) ^ n with hc
  have h1 : ∀ t : Fin n → ZMod p × ZMod p × ZMod p,
      (if ((fun i => (t i).1) ∈ A ∧ (fun i => (t i).2.1) ∈ A ∧ (fun i => (t i).2.2) ∈ A) then
        c * ∑ s : Fin n → ZMod p × Fin 3, (if (fun i => ap3 p (s i)) = t then (1 : ℝ) else 0) else 0) =
      c * ∑ s : Fin n → ZMod p × Fin 3, (if (fun i => ap3 p (s i)) = t then
        (if ((fun i => (t i).1) ∈ A ∧ (fun i => (t i).2.1) ∈ A ∧ (fun i => (t i).2.2) ∈ A)
          then (1 : ℝ) else 0) else 0) := by
    intro t
    by_cases h : ((fun i => (t i).1) ∈ A ∧ (fun i => (t i).2.1) ∈ A ∧ (fun i => (t i).2.2) ∈ A)
    · simp [h]
    · simp [h]
  simp_rw [h1]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  have h2 : (c : ℝ) = 1 / ((p : ℝ) ^ n * (3 : ℝ) ^ n) := by
    rw [hc, ← mul_pow, one_div, one_div, mul_comm, inv_pow]
  rw [h2, one_div, div_eq_mul_inv, mul_comm, Finset.card_filter]
  congr 1
  push_cast
  refine Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow _ _ _) _ _ (fun s => ?_)
  have e0 : (fun i => (ap3 p (s i)).1) = (Equiv.arrowProdEquivProdArrow _ _ _ s).1 := rfl
  have e1 : (fun i => (ap3 p (s i)).2.1) =
      (Equiv.arrowProdEquivProdArrow _ _ _ s).1 + castDiff (Equiv.arrowProdEquivProdArrow _ _ _ s).2 := by
    funext i; simp [ap3, castDiff, Equiv.arrowProdEquivProdArrow]
  have e2 : (fun i => (ap3 p (s i)).2.2) =
      (Equiv.arrowProdEquivProdArrow _ _ _ s).1 + 2 • castDiff (Equiv.arrowProdEquivProdArrow _ _ _ s).2 := by
    funext i; simp [ap3, castDiff, Equiv.arrowProdEquivProdArrow]
  rw [e0, e1, e2]

theorem sum_shift (c a : ZMod p) : ∑ x : ZMod p, (if x + c = a then (1 : ℝ) else 0) = 1 := by
  simp_rw [← eq_sub_iff_add_eq]
  simp

theorem marg_eq (i : Fin 3) : marginal (muP p) i = fun _ => 1 / (p : ℝ) := by
  funext a
  unfold marginal
  simp_rw [muP_eq]
  have h1 : ∀ t : ZMod p × ZMod p × ZMod p,
      (if coord3 i t = a then (1 / (3 * (p : ℝ))) * ∑ s : ZMod p × Fin 3, (if ap3 p s = t then (1:ℝ) else 0)
        else 0) =
      (1 / (3 * (p : ℝ))) * ∑ s : ZMod p × Fin 3, (if ap3 p s = t then
        (if coord3 i t = a then (1:ℝ) else 0) else 0) := by
    intro t
    by_cases h : coord3 i t = a <;> simp [h]
  simp_rw [h1]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hcount : ∑ s : ZMod p × Fin 3, (if coord3 i (ap3 p s) = a then (1 : ℝ) else 0) = 3 := by
    rw [Fintype.sum_prod_type_right]
    have : ∀ k : Fin 3, ∑ x : ZMod p, (if coord3 i (ap3 p (x, k)) = a then (1 : ℝ) else 0) = 1 := by
      intro k
      fin_cases i
      · show ∑ x : ZMod p, (if coord3 (0 : Fin 3) (ap3 p (x, k)) = a then (1 : ℝ) else 0) = 1
        have e : ∀ x : ZMod p, coord3 (0 : Fin 3) (ap3 p (x, k)) = x := fun x => by simp [coord3, ap3]
        simp_rw [e]; simp
      · show ∑ x : ZMod p, (if coord3 (1 : Fin 3) (ap3 p (x, k)) = a then (1 : ℝ) else 0) = 1
        have e : ∀ x : ZMod p, coord3 (1 : Fin 3) (ap3 p (x, k)) = x + ((k : ℕ) : ZMod p) :=
          fun x => by simp [coord3, ap3]
        simp_rw [e]; exact sum_shift p _ a
      · show ∑ x : ZMod p, (if coord3 (2 : Fin 3) (ap3 p (x, k)) = a then (1 : ℝ) else 0) = 1
        have e : ∀ x : ZMod p, coord3 (2 : Fin 3) (ap3 p (x, k)) = x + 2 * ((k : ℕ) : ZMod p) :=
          fun x => by simp [coord3, ap3]
        simp_rw [e]; exact sum_shift p _ a
    simp [this]
  rw [hcount]
  field_simp

theorem muP_isDist : IsDist (muP p) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  refine ⟨fun t => ?_, ?_⟩
  · unfold muP; positivity
  · simp_rw [muP_eq]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp_rw [Finset.sum_ite_eq]
    simp
    field_simp

end RestrictedAP.Counting.Dev.DirectT12

namespace RestrictedAP.Counting.Dev.DirectR14
open RestrictedAP.Counting

/-- The real-valued indicator function of `A ⊆ Σ^n`. -/
noncomputable def ind {Sig : Type} [DecidableEq Sig] {n : ℕ} (A : Finset (Fin n → Sig)) :
    (Fin n → Sig) → ℝ := fun x => if x ∈ A then 1 else 0

theorem ind_01 {Sig : Type} [DecidableEq Sig] {n : ℕ} (A : Finset (Fin n → Sig))
    (x : Fin n → Sig) : ind A x = 0 ∨ ind A x = 1 := by
  unfold ind; split_ifs <;> simp

theorem tripleProb_eq_Delta1 {Sig : Type} [Fintype Sig] [DecidableEq Sig]
    (μ : Sig × Sig × Sig → ℝ) (n : ℕ) (A : Finset (Fin n → Sig)) :
    tripleProb μ n A = Delta1 μ (ind A) := by
  unfold tripleProb Delta1 ind
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h1 : (fun i => (t i).1) ∈ A <;> by_cases h2 : (fun i => (t i).2.1) ∈ A <;>
    by_cases h3 : (fun i => (t i).2.2) ∈ A <;> simp [h1, h2, h3]

theorem expect_ind {Sig : Type} [Fintype Sig] [DecidableEq Sig] (ν : Sig → ℝ) (n : ℕ)
    (A : Finset (Fin n → Sig)) :
    expect (tensorPow ν n) (ind A) = ∑ x ∈ A, tensorPow ν n x := by
  unfold expect ind
  simp [mul_ite, Finset.sum_ite_mem]

theorem tensorPow_nonneg {Ω : Type} (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (n : ℕ)
    (t : Fin n → Ω) : 0 ≤ tensorPow μ n t :=
  Finset.prod_nonneg fun i _ => hμ (t i)

theorem Delta1_nonneg {Sig : Type} [Fintype Sig] {n : ℕ} (μ : Sig × Sig × Sig → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (g : (Fin n → Sig) → ℝ) (hg : ∀ x, g x = 0 ∨ g x = 1) :
    0 ≤ Delta1 μ g := by
  have hg0 : ∀ x, 0 ≤ g x := fun x => by rcases hg x with h | h <;> simp [h]
  unfold Delta1
  exact Finset.sum_nonneg fun t _ => mul_nonneg (tensorPow_nonneg μ hμ n t)
    (mul_nonneg (mul_nonneg (hg0 _) (hg0 _)) (hg0 _))

/-- The numerical comparison used after Claim 5.14. -/
theorem final_bound (s α α₀ d B : ℝ) (hs : 0 < s) (hα : 0 < α) (hsα₀ : s ≤ α₀) (hα₀ : α₀ ≤ 1)
    (hd : α ≤ d) (hB : 0 ≤ B) (k : ℕ) :
    s ^ (2 * B / (α * s ^ k)) ≤ α₀ ^ (2 * B / (d * α₀ ^ k)) := by
  have hs1 : s ≤ 1 := hsα₀.trans hα₀
  have hα₀pos : 0 < α₀ := hs.trans_le hsα₀
  have hsk : 0 < s ^ k := pow_pos hs k
  have hsk' : s ^ k ≤ α₀ ^ k := pow_le_pow_left₀ hs.le hsα₀ k
  have hden : α * s ^ k ≤ d * α₀ ^ k := mul_le_mul hd hsk' hsk.le (hα.le.trans hd)
  have hX : 2 * B / (d * α₀ ^ k) ≤ 2 * B / (α * s ^ k) :=
    div_le_div_of_nonneg_left (by linarith) (mul_pos hα hsk) hden
  have hX0 : 0 ≤ 2 * B / (d * α₀ ^ k) :=
    div_nonneg (by linarith) (mul_nonneg (hα.le.trans hd) (pow_nonneg hα₀pos.le k))
  calc s ^ (2 * B / (α * s ^ k)) ≤ s ^ (2 * B / (d * α₀ ^ k)) :=
        Real.rpow_le_rpow_of_exponent_ge hs hs1 hX
    _ ≤ α₀ ^ (2 * B / (d * α₀ ^ k)) := Real.rpow_le_rpow hs.le hsα₀ hX0

end RestrictedAP.Counting.Dev.DirectR14

namespace RestrictedAP.Counting

/-- Direct reduction of Theorem 1.2 to the fixed-distribution Lemma 5.27. -/
theorem chk_direct_theorem_1_2 (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (α : ℝ) (hα : 0 < α) :
    ∃ β : ℝ, 0 < β ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ A : Finset (Fin n → ZMod p), α * (p : ℝ) ^ n ≤ (A.card : ℝ) →
        β ≤ somewhatRestricted3APProb p n A := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  let α₀ : ℝ := 1 / (3 * (p : ℝ))
  have hα₀ : 0 < α₀ := by dsimp [α₀]; positivity
  have hα₀1 : α₀ ≤ 1 := by
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
    dsimp [α₀]
    exact (div_le_one (by positivity)).mpr (by nlinarith)
  have hmin : IsMinAtom (muP p) α₀ := Dev.DirectT12.muP_minAtom p hp
  obtain ⟨B, c, hc, H⟩ := lemma_5_27 p α₀ α hα₀ hα
  refine ⟨α₀ ^ (2 * (B : ℝ) / (α * α₀ ^ B)) * α₀ ^ (B + 1) * c,
    mul_pos (mul_pos (Real.rpow_pos_of_pos hα₀ _) (pow_pos hα₀ _)) hc, 0, ?_⟩
  intro n _hn A hA
  have hdense : α ≤ ∑ x ∈ A, tensorPow (fun _ : ZMod p => 1 / (p : ℝ)) n x := by
    have hsum : ∑ x ∈ A, tensorPow (fun _ : ZMod p => 1 / (p : ℝ)) n x =
        A.card * (1 / (p : ℝ)) ^ n := by simp [tensorPow]
    rw [hsum]
    have hpn : (0 : ℝ) < (p : ℝ) ^ n := by positivity
    rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpn]
    exact hA
  rw [← Dev.DirectR14.expect_ind] at hdense
  let δ' : ℕ → ℝ → ℝ := fun _ η => if α ≤ η then α₀ ^ (B + 1) * c else 0
  have hyp : ∀ (η : ℝ) (g : (Fin n → ZMod p) → ℝ), (∀ x, g x = 0 ∨ g x = 1) →
      Resilient (fun _ : ZMod p => 1 / (p : ℝ)) B (1 / 2) g →
      η ≤ expect (tensorPow (fun _ : ZMod p => 1 / (p : ℝ)) n) g → δ' B η ≤ Delta1 (muP p) g := by
    intro η g hg hres hη
    simp only [δ']
    split_ifs with h
    · exact H (ZMod p) (by rw [ZMod.card]) (muP p) (fun _ => 1 / (p : ℝ))
        (Dev.DirectT12.muP_isDist p) (fun i => Dev.DirectT12.marg_eq p i)
        (Dev.DirectT12.diag_ne_zero p) (remark_1_2_no_embedding p hp) hmin
        n B le_rfl g hg hres (h.trans hη)
    · exact Dev.DirectR14.Delta1_nonneg (muP p) (Dev.DirectT12.muP_isDist p).1 g hg
  have hmain := claim_5_14_monotone (ZMod p) (muP p) (fun _ => 1 / (p : ℝ))
    (Dev.DirectT12.muP_isDist p) (fun i => Dev.DirectT12.marg_eq p i)
    (Dev.DirectT12.diag_ne_zero p) (remark_1_2_no_embedding p hp) α₀ hmin n B δ' hyp
    (Dev.DirectR14.ind A) (Dev.DirectR14.ind_01 A) (hα.trans_le hdense)
  have hδ' : δ' B (expect (tensorPow (fun _ : ZMod p => 1 / (p : ℝ)) n)
      (Dev.DirectR14.ind A)) = α₀ ^ (B + 1) * c := by
    simp only [δ', if_pos hdense]
  rw [hδ'] at hmain
  rw [← Dev.DirectT12.triple_eq, Dev.DirectR14.tripleProb_eq_Delta1]
  refine le_trans ?_ hmain
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (Dev.DirectR14.final_bound α₀ α α₀ _ B hα₀ hα le_rfl hα₀1 hdense (Nat.cast_nonneg B) B)
    (mul_nonneg (pow_nonneg hα₀.le _) hc.le)

end RestrictedAP.Counting
end

theorem solution : type_of% @RestrictedAP.Counting.chk_direct_theorem_1_2 :=
  @RestrictedAP.Counting.chk_direct_theorem_1_2
