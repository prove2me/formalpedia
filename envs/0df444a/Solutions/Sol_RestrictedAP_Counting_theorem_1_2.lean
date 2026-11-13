-- Prove2me | solution 1 for RestrictedAP.Counting.theorem_1_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:16:52.232196+00:00
-- url     : https://prove2.me/submissions/78eb754b-0485-4166-9992-1f3e4316fd61
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_MuP
import Definitions.Def_RestrictedAP_Counting_SomewhatRestricted3APCount
import Theorems.Thm_RestrictedAP_Counting_theorem_1_4
import Theorems.Thm_RestrictedAP_Counting_remark_1_2_no_embedding

section
namespace RestrictedAP.Counting.Dev.R12

theorem mem_supp (p : ℕ) [NeZero p] (x : ZMod p) (a : Fin 3) :
    (x, x + ((a : ℕ) : ZMod p), x + 2 * ((a : ℕ) : ZMod p)) ∈ supp (muP p) := by
  unfold supp muP
  simp only [Set.mem_setOf_eq, ne_eq, div_eq_zero_iff, not_or]
  refine ⟨?_, ?_⟩
  · have : 0 < (Finset.univ.filter (fun xa : ZMod p × Fin 3 =>
        (xa.1, xa.1 + ((xa.2 : ℕ) : ZMod p), xa.1 + 2 * ((xa.2 : ℕ) : ZMod p)) =
          (x, x + ((a : ℕ) : ZMod p), x + 2 * ((a : ℕ) : ZMod p)))).card :=
      Finset.card_pos.mpr ⟨(x, a), by simp⟩
    exact_mod_cast this.ne'
  · have : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
    positivity

end RestrictedAP.Counting.Dev.R12
end

section
open Classical

namespace RestrictedAP.Counting.Dev.T12

variable (p : ℕ) [NeZero p]

/-- the 3-AP map -/
def ap3 : ZMod p × Fin 3 → ZMod p × ZMod p × ZMod p :=
  fun xa => (xa.1, xa.1 + ((xa.2 : ℕ) : ZMod p), xa.1 + 2 * ((xa.2 : ℕ) : ZMod p))

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

end RestrictedAP.Counting.Dev.T12

namespace RestrictedAP.Counting.Dev.T12

theorem muP_isDist (p : ℕ) [NeZero p] : IsDist (muP p) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  refine ⟨fun t => ?_, ?_⟩
  · unfold muP; positivity
  · simp_rw [muP_eq]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp_rw [Finset.sum_ite_eq]
    simp
    field_simp

theorem nu_isDist (p : ℕ) [NeZero p] : IsDist (fun _ : ZMod p => 1 / (p : ℝ)) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  refine ⟨fun t => ?_, ?_⟩
  · positivity
  · simp

theorem muP_atoms (p : ℕ) [NeZero p] : AtomsAtLeast (muP p) (1 / (3 * (p : ℝ))) := by
  intro t ht
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  unfold muP at ht ⊢
  have hc : (Finset.univ.filter (fun xa : ZMod p × Fin 3 =>
      (xa.1, xa.1 + ((xa.2 : ℕ) : ZMod p), xa.1 + 2 * ((xa.2 : ℕ) : ZMod p)) = t)).card ≠ 0 := by
    intro h; apply ht; simp [h]
  have h1 : (1 : ℝ) ≤ (Finset.univ.filter (fun xa : ZMod p × Fin 3 =>
      (xa.1, xa.1 + ((xa.2 : ℕ) : ZMod p), xa.1 + 2 * ((xa.2 : ℕ) : ZMod p)) = t)).card := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hc
  exact div_le_div_of_nonneg_right h1 (by positivity)

end RestrictedAP.Counting.Dev.T12
end

section
open Classical

namespace RestrictedAP.Counting

theorem chk_theorem_1_2 (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (α : ℝ) (hα : 0 < α) :
    ∃ β : ℝ, 0 < β ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ A : Finset (Fin n → ZMod p), α * (p : ℝ) ^ n ≤ (A.card : ℝ) →
        β ≤ somewhatRestricted3APProb p n A := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  obtain ⟨β, hβ, H⟩ := theorem_1_4 p (1 / (3 * (p : ℝ))) α (by positivity) hα
  refine ⟨β, hβ, ?_⟩
  have h := H (ZMod p) (by rw [ZMod.card]) (muP p) (fun _ => 1 / (p : ℝ))
    (Dev.T12.muP_isDist p) (Dev.T12.nu_isDist p) (fun i => Dev.T12.marg_eq p i)
    (fun x => by
      have := Dev.R12.mem_supp p x 0
      simpa [supp] using this)
    (Dev.T12.muP_atoms p) (remark_1_2_no_embedding p hp)
  obtain ⟨n₀, hn₀⟩ := h
  refine ⟨n₀, fun n hn A hA => ?_⟩
  rw [← Dev.T12.triple_eq]
  apply hn₀ n hn A
  have : ∑ x ∈ A, tensorPow (fun _ : ZMod p => 1 / (p : ℝ)) n x = A.card * (1 / (p : ℝ)) ^ n := by
    simp [tensorPow]
  rw [this]
  have hpn : (0 : ℝ) < (p : ℝ) ^ n := by positivity
  rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpn]
  exact hA

end RestrictedAP.Counting
end
theorem solution : type_of% @RestrictedAP.Counting.chk_theorem_1_2 := @RestrictedAP.Counting.chk_theorem_1_2
