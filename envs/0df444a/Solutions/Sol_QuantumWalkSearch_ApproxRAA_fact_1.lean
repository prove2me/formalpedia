-- Prove2me | solution 1 for QuantumWalkSearch.ApproxRAA.fact_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T23:42:01.336792+00:00
-- url     : https://prove2.me/submissions/be1f1d67-f79e-4915-b34d-c880f60a3b0c

import Mathlib
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Setting
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Circuit

open Matrix

namespace Aux_QWS

open QuantumWalkSearch.ApproxRAA

/-! ### Generic facts about `act` -/

section Gen

variable {ι : Type*} [Fintype ι]

lemma act_apply (A : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) (p : ι) :
    act A v p = ∑ q, A p q * v q := rfl

lemma act_mul (A B : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    act (A * B) v = act A (act B v) := by
  ext p
  simp only [act_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun q _ => by ring

lemma act_add (A B : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    act (A + B) v = act A v + act B v := by
  ext p
  simp only [act_apply, PiLp.add_apply, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

lemma act_sub_mat (A B : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    act (A - B) v = act A v - act B v := by
  ext p
  simp only [act_apply, PiLp.sub_apply, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma act_one [DecidableEq ι] (v : EuclideanSpace ℂ ι) : act (1 : Matrix ι ι ℂ) v = v := by
  ext p
  rw [act_apply, Finset.sum_eq_single p]
  · rw [Matrix.one_apply_eq, one_mul]
  · intro q _ hq
    rw [Matrix.one_apply_ne (Ne.symm hq), zero_mul]
  · intro h; exact absurd (Finset.mem_univ p) h

lemma act_vadd (A : Matrix ι ι ℂ) (v w : EuclideanSpace ℂ ι) :
    act A (v + w) = act A v + act A w := by
  ext p
  simp only [act_apply, PiLp.add_apply, mul_add, Finset.sum_add_distrib]

lemma act_vsub (A : Matrix ι ι ℂ) (v w : EuclideanSpace ℂ ι) :
    act A (v - w) = act A v - act A w := by
  ext p
  simp only [act_apply, PiLp.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma act_smul (A : Matrix ι ι ℂ) (c : ℂ) (v : EuclideanSpace ℂ ι) :
    act A (c • v) = c • act A v := by
  ext p
  simp only [act_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by ring

lemma inner_act (A : Matrix ι ι ℂ) (x y : EuclideanSpace ℂ ι) :
    inner ℂ (act A x) y = inner ℂ x (act Aᴴ y) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Pi.star_apply]
  simp only [act_apply, star_sum, star_mul', Matrix.conjTranspose_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma norm_act_unitary [DecidableEq ι] {U : Matrix ι ι ℂ}
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (v : EuclideanSpace ℂ ι) : ‖act U v‖ = ‖v‖ := by
  have h1 : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hU
  have h2 : inner ℂ (act U v) (act U v) = inner ℂ v v := by
    rw [inner_act, ← act_mul, h1, act_one]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h2
  have h3 : ‖act U v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast h2
  rw [← Real.sqrt_sq (norm_nonneg (act U v)), h3, Real.sqrt_sq (norm_nonneg v)]

lemma ct_unitary [DecidableEq ι] {U : Matrix ι ι ℂ}
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) : Uᴴ ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  have h := Matrix.mem_unitaryGroup_iff'.mp hU
  rw [Matrix.star_eq_conjTranspose] at h
  exact h

lemma act_refState [DecidableEq ι] (φ w : EuclideanSpace ℂ ι) :
    act (refState φ) w = (2 * inner ℂ φ w) • φ - w := by
  ext p
  have key : act (refState φ) w p =
      (((2 : ℂ) • Matrix.vecMulVec φ.ofLp (star φ.ofLp)) *ᵥ w.ofLp) p - w p := by
    show (refState φ *ᵥ w.ofLp) p = _
    rw [refState, Matrix.sub_mulVec, Matrix.one_mulVec] <;> rfl
  rw [key, PiLp.sub_apply, PiLp.smul_apply, EuclideanSpace.inner_eq_star_dotProduct, smul_eq_mul]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun q _ => by ring

lemma le_of_sq_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  rw [← Real.sqrt_sq ha, ← Real.sqrt_sq hb]; exact Real.sqrt_le_sqrt h

lemma eq_of_sq_eq' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) : a = b := by
  rw [← Real.sqrt_sq ha, h, Real.sqrt_sq hb]

lemma mul_star_self' (a : ℂ) : a * star a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, starRingEnd_apply]

end Gen

/-! ### Projections on `X × ρ` -/

section Proj

variable {X : Type*} [Fintype X] [DecidableEq X] {ρ : Type*} [Fintype ρ] [DecidableEq ρ]

lemma PM_apply (M : Finset X) (v : EuclideanSpace ℂ (X × ρ)) (p : X × ρ) :
    act (markedProj M) v p = if p.1 ∈ M then v p else 0 := by
  show (markedProj M *ᵥ v.ofLp) p = _
  rw [markedProj, Matrix.mulVec_diagonal]
  by_cases h : p.1 ∈ M <;> simp [h]

lemma PU_apply (M : Finset X) (v : EuclideanSpace ℂ (X × ρ)) (p : X × ρ) :
    act (unmarkedProj M) v p = if p.1 ∈ M then 0 else v p := by
  show (unmarkedProj M *ᵥ v.ofLp) p = _
  rw [unmarkedProj, Matrix.mulVec_diagonal]
  by_cases h : p.1 ∈ M <;> simp [h]

lemma F_apply (M : Finset X) (v : EuclideanSpace ℂ (X × ρ)) (p : X × ρ) :
    act (flipMarked M) v p = if p.1 ∈ M then - v p else v p := by
  show (flipMarked M *ᵥ v.ofLp) p = _
  rw [flipMarked, Matrix.mulVec_diagonal]
  by_cases h : p.1 ∈ M <;> simp [h]

noncomputable def sMU (M : Finset X) (α β : ℂ) (v : EuclideanSpace ℂ (X × ρ)) :
    EuclideanSpace ℂ (X × ρ) :=
  WithLp.toLp 2 (fun p => if p.1 ∈ M then α * v p else β * v p)

lemma sMU_apply (M : Finset X) (α β : ℂ) (v : EuclideanSpace ℂ (X × ρ)) (p : X × ρ) :
    sMU M α β v p = if p.1 ∈ M then α * v p else β * v p := rfl

lemma norm_sq_sMU (M : Finset X) (α β : ℂ) (v : EuclideanSpace ℂ (X × ρ)) :
    ‖sMU M α β v‖ ^ 2 = ‖α‖ ^ 2 * ‖act (markedProj M) v‖ ^ 2 +
      ‖β‖ ^ 2 * ‖act (unmarkedProj M) v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [sMU_apply, PM_apply, PU_apply]
  by_cases h : p.1 ∈ M <;> simp [h, norm_mul, mul_pow]

lemma sMU_one_one (M : Finset X) (v : EuclideanSpace ℂ (X × ρ)) : sMU M 1 1 v = v := by
  ext p; rw [sMU_apply]; split_ifs <;> simp

lemma F_eq_sMU (M : Finset X) (v : EuclideanSpace ℂ (X × ρ)) :
    act (flipMarked M) v = sMU M (-1) 1 v := by
  ext p; rw [sMU_apply, F_apply]; split_ifs <;> simp

lemma norm_sq_split (M : Finset X) (v : EuclideanSpace ℂ (X × ρ)) :
    ‖v‖ ^ 2 = ‖act (markedProj M) v‖ ^ 2 + ‖act (unmarkedProj M) v‖ ^ 2 := by
  have h := norm_sq_sMU M 1 1 v
  rw [sMU_one_one] at h
  rw [h]; simp

lemma norm_F (M : Finset X) (v : EuclideanSpace ℂ (X × ρ)) :
    ‖act (flipMarked M) v‖ = ‖v‖ := by
  apply eq_of_sq_eq' (norm_nonneg _) (norm_nonneg _)
  rw [F_eq_sMU, norm_sq_sMU, norm_sq_split M v]; simp

lemma norm_PM_le (M : Finset X) (v : EuclideanSpace ℂ (X × ρ)) :
    ‖act (markedProj M) v‖ ≤ ‖v‖ := by
  apply le_of_sq_le' (norm_nonneg _) (norm_nonneg _)
  rw [norm_sq_split M v]; nlinarith [sq_nonneg ‖act (unmarkedProj M) v‖]

lemma norm_PU_le (M : Finset X) (v : EuclideanSpace ℂ (X × ρ)) :
    ‖act (unmarkedProj M) v‖ ≤ ‖v‖ := by
  apply le_of_sq_le' (norm_nonneg _) (norm_nonneg _)
  rw [norm_sq_split M v]; nlinarith [sq_nonneg ‖act (markedProj M) v‖]

lemma inner_F (M : Finset X) (v : EuclideanSpace ℂ (X × ρ)) :
    inner ℂ v (act (flipMarked M) v) =
      ((‖act (unmarkedProj M) v‖ ^ 2 - ‖act (markedProj M) v‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq, ← Finset.sum_sub_distrib, Complex.ofReal_sum]
  simp only [dotProduct, Pi.star_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [F_apply, PM_apply, PU_apply]
  by_cases h : p.1 ∈ M
  · rw [if_pos h, if_pos h, if_pos h, neg_mul, mul_star_self']
    push_cast; simp
  · rw [if_neg h, if_neg h, if_neg h, mul_star_self']
    push_cast; simp

end Proj

/-! ### The circuit -/

section Circ

variable {X : Type*} [Fintype X] [DecidableEq X] {κ : ℕ → Type*} [∀ i, Fintype (κ i)]
  [∀ i, DecidableEq (κ i)]

lemma sum_agree {β : Type*} [AddCommMonoid β] {T : ℕ} (ii : Fin T) (b : Regs κ T)
    (f : Regs κ T → β) :
    (∑ a : Regs κ T, if (∀ j : Fin T, j ≠ ii → b j = a j) then f a else 0) =
      ∑ k : κ (ii.val + 1), f (Function.update b ii k) := by
  rw [← Finset.sum_filter]
  have hset : (Finset.univ.filter fun a : Regs κ T => ∀ j : Fin T, j ≠ ii → b j = a j) =
      Finset.univ.image (fun k : κ (ii.val + 1) => Function.update b ii k) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      refine ⟨a ii, ?_⟩
      funext j
      by_cases hj : j = ii
      · subst hj; exact Function.update_self _ _ _
      · rw [Function.update_of_ne hj]; exact h j hj
    · rintro ⟨k, rfl⟩ j hj
      exact (Function.update_of_ne hj _ _).symm
  rw [hset, Finset.sum_image]
  intro k _ k' _ h
  exact Function.update_injective b ii h

lemma sum_agree' {β : Type*} [AddCommMonoid β] {T : ℕ} (ii : Fin T) (b : Regs κ T)
    (f : Regs κ T → β) :
    (∑ a : Regs κ T, if (∀ j : Fin T, j ≠ ii → a j = b j) then f a else 0) =
      ∑ k : κ (ii.val + 1), f (Function.update b ii k) := by
  rw [← Finset.sum_filter]
  have hset : (Finset.univ.filter fun a : Regs κ T => ∀ j : Fin T, j ≠ ii → a j = b j) =
      Finset.univ.image (fun k : κ (ii.val + 1) => Function.update b ii k) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      refine ⟨a ii, ?_⟩
      funext j
      by_cases hj : j = ii
      · subst hj; exact Function.update_self _ _ _
      · rw [Function.update_of_ne hj]; exact (h j hj).symm
    · rintro ⟨k, rfl⟩ j hj
      exact Function.update_of_ne hj _ _
  rw [hset, Finset.sum_image]
  intro k _ k' _ h
  exact Function.update_injective b ii h

lemma sum_agree3 {β : Type*} [AddCommMonoid β] {T : ℕ} (ii : Fin T) (b : Regs κ T)
    (f : X × X × Regs κ T → β) :
    (∑ r : X × X × Regs κ T, if (∀ j : Fin T, j ≠ ii → b j = r.2.2 j) then f r else 0) =
      ∑ w : X × X × κ (ii.val + 1), f (w.1, w.2.1, Function.update b ii w.2.2) := by
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  exact sum_agree ii b (fun a => f (x, y, a))

lemma sum_agree3' {β : Type*} [AddCommMonoid β] {T : ℕ} (ii : Fin T) (b : Regs κ T)
    (f : X × X × Regs κ T → β) :
    (∑ r : X × X × Regs κ T, if (∀ j : Fin T, j ≠ ii → r.2.2 j = b j) then f r else 0) =
      ∑ w : X × X × κ (ii.val + 1), f (w.1, w.2.1, Function.update b ii w.2.2) := by
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  exact sum_agree' ii b (fun a => f (x, y, a))

lemma bad_iff_of_agree {T : ℕ} (z : ∀ i, κ i) (ii : Fin T) {a b : Regs κ T}
    (h : ∀ j : Fin T, j ≠ ii → a j = b j) :
    (∃ j : Fin T, j < ii ∧ a j ≠ z (j.val + 1)) ↔ (∃ j : Fin T, j < ii ∧ b j ≠ z (j.val + 1)) := by
  constructor
  · rintro ⟨j, hj, hne⟩; exact ⟨j, hj, by rw [← h j (ne_of_lt hj)]; exact hne⟩
  · rintro ⟨j, hj, hne⟩; exact ⟨j, hj, by rw [h j (ne_of_lt hj)]; exact hne⟩

lemma cR_apply (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (T : ℕ)
    (ii : Fin T) (p q : X × X × Regs κ T) :
    controlledR z R T ii p q =
      if (∃ j : Fin T, j < ii ∧ q.2.2 j ≠ z (j.val + 1)) then (if p = q then -1 else 0)
      else if (∀ j : Fin T, j ≠ ii → p.2.2 j = q.2.2 j) then
        R (ii.val + 1) (p.1, p.2.1, p.2.2 ii) (q.1, q.2.1, q.2.2 ii) else 0 := rfl

lemma cR_unitary (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (T : ℕ)
    (ii : Fin T) (hU : R (ii.val + 1) ∈ Matrix.unitaryGroup (X × X × κ (ii.val + 1)) ℂ) :
    controlledR z R T ii ∈ Matrix.unitaryGroup (X × X × Regs κ T) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have hRR : (R (ii.val + 1))ᴴ * R (ii.val + 1) = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hU
  ext p q
  rw [Matrix.mul_apply]
  simp only [Matrix.star_apply]
  by_cases hq : ∃ j : Fin T, j < ii ∧ q.2.2 j ≠ z (j.val + 1)
  · rw [Finset.sum_eq_single q]
    · rw [cR_apply z R T ii q q, if_pos hq, if_pos rfl]
      by_cases hp : ∃ j : Fin T, j < ii ∧ p.2.2 j ≠ z (j.val + 1)
      · rw [cR_apply z R T ii q p, if_pos hp]
        by_cases hpq : p = q
        · subst hpq; simp
        · rw [if_neg (Ne.symm hpq), Matrix.one_apply_ne hpq]; simp
      · rw [cR_apply z R T ii q p, if_neg hp]
        have hpq : p ≠ q := by rintro rfl; exact hp hq
        have hag : ¬ (∀ j : Fin T, j ≠ ii → q.2.2 j = p.2.2 j) :=
          fun h => hp ((bad_iff_of_agree z ii h).mp hq)
        rw [if_neg hag, Matrix.one_apply_ne hpq]; simp
    · intro r _ hr
      rw [cR_apply z R T ii r q, if_pos hq, if_neg hr, mul_zero]
    · intro h; exact absurd (Finset.mem_univ q) h
  · by_cases hp : ∃ j : Fin T, j < ii ∧ p.2.2 j ≠ z (j.val + 1)
    · rw [Finset.sum_eq_single p]
      · rw [cR_apply z R T ii p p, if_pos hp, if_pos rfl, cR_apply z R T ii p q, if_neg hq]
        have hpq : p ≠ q := by rintro rfl; exact hq hp
        have hag : ¬ (∀ j : Fin T, j ≠ ii → p.2.2 j = q.2.2 j) :=
          fun h => hq ((bad_iff_of_agree z ii h).mp hp)
        rw [if_neg hag, Matrix.one_apply_ne hpq]; simp
      · intro r _ hr
        rw [cR_apply z R T ii r p, if_pos hp, if_neg hr, star_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ p) h
    · have hterm : ∀ r : X × X × Regs κ T,
          star (controlledR z R T ii r p) * controlledR z R T ii r q =
          if (∀ j : Fin T, j ≠ ii → r.2.2 j = p.2.2 j) ∧
              (∀ j : Fin T, j ≠ ii → r.2.2 j = q.2.2 j) then
            star (R (ii.val + 1) (r.1, r.2.1, r.2.2 ii) (p.1, p.2.1, p.2.2 ii)) *
              R (ii.val + 1) (r.1, r.2.1, r.2.2 ii) (q.1, q.2.1, q.2.2 ii) else 0 := by
        intro r
        rw [cR_apply z R T ii r p, cR_apply z R T ii r q, if_neg hp, if_neg hq]
        by_cases h1 : ∀ j : Fin T, j ≠ ii → r.2.2 j = p.2.2 j
        · by_cases h2 : ∀ j : Fin T, j ≠ ii → r.2.2 j = q.2.2 j
          · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]
          · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 h.2), mul_zero]
        · rw [if_neg h1, if_neg (show ¬ ((∀ j : Fin T, j ≠ ii → r.2.2 j = p.2.2 j) ∧
            (∀ j : Fin T, j ≠ ii → r.2.2 j = q.2.2 j)) from fun h => h1 h.1), star_zero, zero_mul]
      by_cases hag : ∀ j : Fin T, j ≠ ii → p.2.2 j = q.2.2 j
      · have hterm2 : ∀ r : X × X × Regs κ T,
            (if (∀ j : Fin T, j ≠ ii → r.2.2 j = p.2.2 j) ∧
                (∀ j : Fin T, j ≠ ii → r.2.2 j = q.2.2 j) then
              star (R (ii.val + 1) (r.1, r.2.1, r.2.2 ii) (p.1, p.2.1, p.2.2 ii)) *
                R (ii.val + 1) (r.1, r.2.1, r.2.2 ii) (q.1, q.2.1, q.2.2 ii) else 0) =
            if (∀ j : Fin T, j ≠ ii → r.2.2 j = q.2.2 j) then
              star (R (ii.val + 1) (r.1, r.2.1, r.2.2 ii) (p.1, p.2.1, p.2.2 ii)) *
                R (ii.val + 1) (r.1, r.2.1, r.2.2 ii) (q.1, q.2.1, q.2.2 ii) else 0 := by
          intro r
          by_cases h2 : ∀ j : Fin T, j ≠ ii → r.2.2 j = q.2.2 j
          · rw [if_pos h2, if_pos ⟨fun j hj => (h2 j hj).trans (hag j hj).symm, h2⟩]
          · rw [if_neg h2, if_neg (fun h => h2 h.2)]
        rw [Finset.sum_congr rfl (fun r _ => (hterm r).trans (hterm2 r)), sum_agree3' ii q.2.2]
        simp only [Function.update_self, Prod.mk.eta]
        have hR1 := congrFun (congrFun hRR (p.1, p.2.1, p.2.2 ii)) (q.1, q.2.1, q.2.2 ii)
        rw [Matrix.mul_apply] at hR1
        simp only [Matrix.conjTranspose_apply] at hR1
        refine hR1.trans ?_
        by_cases hpq : p = q
        · subst hpq; simp
        · have hne : (p.1, p.2.1, p.2.2 ii) ≠ (q.1, q.2.1, q.2.2 ii) := by
            intro h
            apply hpq
            simp only [Prod.mk.injEq] at h
            obtain ⟨h1, h2, h3⟩ := h
            have h4 : p.2.2 = q.2.2 := by
              funext j
              by_cases hj : j = ii
              · subst hj; exact h3
              · exact hag j hj
            exact Prod.ext h1 (Prod.ext h2 h4)
          rw [Matrix.one_apply_ne hne, Matrix.one_apply_ne hpq]
      · have hpq : p ≠ q := by rintro rfl; exact hag (fun j _ => rfl)
        rw [Matrix.one_apply_ne hpq]
        refine Finset.sum_eq_zero fun r _ => ?_
        rw [hterm r, if_neg (fun h => hag (fun j hj => (h.1 j hj).symm.trans (h.2 j hj)))]

lemma flip_unitary {T : ℕ} (M : Finset X) :
    flipMarked (X := X) (ρ := X × Regs κ T) M ∈ Matrix.unitaryGroup (X × X × Regs κ T) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext p q
  rw [Matrix.mul_apply, Finset.sum_eq_single p]
  · rw [Matrix.star_apply]
    by_cases hpq : p = q
    · subst hpq
      simp only [flipMarked, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      split_ifs <;> simp
    · rw [Matrix.one_apply_ne hpq]
      simp only [flipMarked, Matrix.diagonal_apply_ne _ hpq, mul_zero]
  · intro r _ hr
    rw [Matrix.star_apply]
    simp only [flipMarked, Matrix.diagonal_apply_ne _ hr, star_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ p) h

lemma A_zero (M : Finset X) (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ)
    (T : ℕ) : approxRAA M z R T 0 = 1 := by
  rw [approxRAA]

lemma A_succ_lt (M : Finset X) (z : ∀ i, κ i)
    (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (T n : ℕ) (h : n < T) :
    approxRAA M z R T (n + 1) = approxRAA M z R T n * controlledR z R T ⟨n, h⟩ *
      (approxRAA M z R T n)ᴴ * flipMarked M * approxRAA M z R T n := by
  rw [approxRAA, dif_pos h]

lemma A_succ_ge (M : Finset X) (z : ∀ i, κ i)
    (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (T n : ℕ) (h : ¬ n < T) :
    approxRAA M z R T (n + 1) = approxRAA M z R T n := by
  rw [approxRAA, dif_neg h]

lemma A_unitary (M : Finset X) (z : ∀ i, κ i)
    (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (T : ℕ)
    (hR : ∀ i, 1 ≤ i → R i ∈ Matrix.unitaryGroup (X × X × κ i) ℂ) :
    ∀ n, approxRAA M z R T n ∈ Matrix.unitaryGroup (X × X × Regs κ T) ℂ
  | 0 => by rw [A_zero]; exact one_mem _
  | n + 1 => by
    by_cases h : n < T
    · rw [A_succ_lt M z R T n h]
      have hA := A_unitary M z R T hR n
      exact mul_mem (mul_mem (mul_mem (mul_mem hA (cR_unitary z R T ⟨n, h⟩
        (hR (n + 1) (by omega)))) (ct_unitary hA)) (flip_unitary M)) hA
    · rw [A_succ_ge M z R T n h]; exact A_unitary M z R T hR n

/-! Locality: the first `n` steps only touch the registers `j < n`. -/

def Loc {T : ℕ} (n : ℕ) (A : Matrix (X × X × Regs κ T) (X × X × Regs κ T) ℂ) : Prop :=
  ∀ p q : X × X × Regs κ T, A p q ≠ 0 → ∀ j : Fin T, n ≤ j.val → p.2.2 j = q.2.2 j

lemma Loc_mul {T n : ℕ} {A B : Matrix (X × X × Regs κ T) (X × X × Regs κ T) ℂ}
    (hA : Loc n A) (hB : Loc n B) : Loc n (A * B) := by
  intro p q h j hj
  rw [Matrix.mul_apply] at h
  obtain ⟨r, _, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact (hA p r (left_ne_zero_of_mul hr) j hj).trans (hB r q (right_ne_zero_of_mul hr) j hj)

lemma Loc_ct {T n : ℕ} {A : Matrix (X × X × Regs κ T) (X × X × Regs κ T) ℂ}
    (hA : Loc n A) : Loc n Aᴴ := by
  intro p q h j hj
  rw [Matrix.conjTranspose_apply] at h
  exact (hA q p (star_ne_zero.mp h) j hj).symm

lemma Loc_one {T n : ℕ} : Loc (X := X) (κ := κ) (T := T) n 1 := by
  intro p q h j _
  by_cases hpq : p = q
  · rw [hpq]
  · exact absurd (Matrix.one_apply_ne hpq) h

lemma Loc_flip {T n : ℕ} (M : Finset X) :
    Loc (κ := κ) (T := T) n (flipMarked (X := X) (ρ := X × Regs κ T) M) := by
  intro p q h j _
  by_cases hpq : p = q
  · rw [hpq]
  · exact absurd (by unfold flipMarked; exact Matrix.diagonal_apply_ne _ hpq) h

lemma Loc_mono {T n m : ℕ} (hnm : n ≤ m)
    {A : Matrix (X × X × Regs κ T) (X × X × Regs κ T) ℂ} (hA : Loc n A) : Loc m A :=
  fun p q h j hj => hA p q h j (le_trans hnm hj)

lemma Loc_cR (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (T : ℕ)
    (ii : Fin T) : Loc (ii.val + 1) (controlledR z R T ii) := by
  intro p q h j hj
  rw [cR_apply] at h
  by_cases hq : ∃ j : Fin T, j < ii ∧ q.2.2 j ≠ z (j.val + 1)
  · rw [if_pos hq] at h
    by_cases hpq : p = q
    · rw [hpq]
    · rw [if_neg hpq] at h; exact absurd rfl h
  · rw [if_neg hq] at h
    by_cases hag : ∀ j : Fin T, j ≠ ii → p.2.2 j = q.2.2 j
    · exact hag j (fun hji => by rw [hji] at hj; omega)
    · rw [if_neg hag] at h; exact absurd rfl h

lemma Loc_A (M : Finset X) (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ)
    (T : ℕ) : ∀ n : ℕ, Loc n (approxRAA M z R T n)
  | 0 => by rw [A_zero]; exact Loc_one
  | n + 1 => by
    by_cases h : n < T
    · rw [A_succ_lt M z R T n h]
      have hA := Loc_mono (Nat.le_succ n) (Loc_A M z R T n)
      exact Loc_mul (Loc_mul (Loc_mul (Loc_mul hA (Loc_cR z R T ⟨n, h⟩)) (Loc_ct hA))
        (Loc_flip M)) hA
    · rw [A_succ_ge M z R T n h]; exact Loc_mono (Nat.le_succ n) (Loc_A M z R T n)

def Supp {T : ℕ} (z : ∀ i, κ i) (n : ℕ) (v : EuclideanSpace ℂ (X × X × Regs κ T)) : Prop :=
  ∀ p : X × X × Regs κ T, (∃ j : Fin T, n ≤ j.val ∧ p.2.2 j ≠ z (j.val + 1)) → v p = 0

lemma Supp_act {T n : ℕ} {z : ∀ i, κ i}
    {A : Matrix (X × X × Regs κ T) (X × X × Regs κ T) ℂ} (hA : Loc n A)
    {v : EuclideanSpace ℂ (X × X × Regs κ T)} (hv : Supp z n v) : Supp z n (act A v) := by
  rintro p ⟨j, hj, hne⟩
  rw [act_apply]
  refine Finset.sum_eq_zero fun q _ => ?_
  by_cases hq : A p q = 0
  · rw [hq, zero_mul]
  · rw [hv q ⟨j, hj, by rw [← hA p q hq j hj]; exact hne⟩, mul_zero]

lemma Supp_mono {T n m : ℕ} {z : ∀ i, κ i} (hnm : n ≤ m)
    {v : EuclideanSpace ℂ (X × X × Regs κ T)} (hv : Supp z n v) : Supp z m v := by
  rintro p ⟨j, hj, hne⟩
  exact hv p ⟨j, le_trans hnm hj, hne⟩

lemma Supp_init {T : ℕ} (z : ∀ i, κ i) (piState : EuclideanSpace ℂ (X × X)) :
    Supp z 0 (initState z T piState) := by
  rintro p ⟨j, _, hne⟩
  show (if p.2.2 = zeroRegs z T then piState (p.1, p.2.1) else 0) = 0
  rw [if_neg]
  intro h; apply hne; exact congrFun h j

lemma norm_tensorZero {ρ : Type*} [Fintype ρ] [DecidableEq ρ] (c : ρ)
    (ψ : EuclideanSpace ℂ (X × X)) : ‖tensorZero c ψ‖ = ‖ψ‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single c]
  · show ‖(if c = c then ψ (a, b) else 0)‖ ^ 2 = _
    rw [if_pos rfl]
  · intro k _ hk
    show ‖(if k = c then ψ (a, b) else 0)‖ ^ 2 = 0
    rw [if_neg hk]; simp
  · intro h; exact absurd (Finset.mem_univ c) h

lemma act_cR_bad {T : ℕ} (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ)
    (ii : Fin T) (v : EuclideanSpace ℂ (X × X × Regs κ T)) (p : X × X × Regs κ T)
    (hp : ∃ j : Fin T, j < ii ∧ p.2.2 j ≠ z (j.val + 1)) :
    act (controlledR z R T ii) v p = - v p := by
  rw [act_apply, Finset.sum_eq_single p]
  · rw [cR_apply, if_pos hp, if_pos rfl, neg_one_mul]
  · intro q _ hq
    rw [cR_apply]
    by_cases hqb : ∃ j : Fin T, j < ii ∧ q.2.2 j ≠ z (j.val + 1)
    · rw [if_pos hqb, if_neg (Ne.symm hq), zero_mul]
    · rw [if_neg hqb, if_neg (fun h => hqb ((bad_iff_of_agree z ii h).mp hp)), zero_mul]
  · intro h; exact absurd (Finset.mem_univ p) h

lemma act_cR_good {T : ℕ} (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ)
    (ii : Fin T) (v : EuclideanSpace ℂ (X × X × Regs κ T)) (p : X × X × Regs κ T)
    (hp : ¬ ∃ j : Fin T, j < ii ∧ p.2.2 j ≠ z (j.val + 1)) :
    act (controlledR z R T ii) v p = ∑ w : X × X × κ (ii.val + 1),
      R (ii.val + 1) (p.1, p.2.1, p.2.2 ii) w * v (w.1, w.2.1, Function.update p.2.2 ii w.2.2) := by
  rw [act_apply]
  have hterm : ∀ q : X × X × Regs κ T, controlledR z R T ii p q * v q =
      if (∀ j : Fin T, j ≠ ii → p.2.2 j = q.2.2 j) then
        R (ii.val + 1) (p.1, p.2.1, p.2.2 ii) (q.1, q.2.1, q.2.2 ii) * v q else 0 := by
    intro q
    rw [cR_apply]
    by_cases hqb : ∃ j : Fin T, j < ii ∧ q.2.2 j ≠ z (j.val + 1)
    · have hpq : p ≠ q := by rintro rfl; exact hp hqb
      rw [if_pos hqb, if_neg hpq, zero_mul,
        if_neg (fun h => hp ((bad_iff_of_agree z ii h).mpr hqb))]
    · rw [if_neg hqb, ite_mul, zero_mul]
  rw [Finset.sum_congr rfl (fun q _ => hterm q), sum_agree3 ii p.2.2]
  simp only [Function.update_self, Prod.mk.eta]

lemma upd_zero_iff {T : ℕ} (z : ∀ i, κ i) (ii : Fin T) (k : κ (ii.val + 1)) :
    Function.update (zeroRegs z T) ii k = zeroRegs z T ↔ k = z (ii.val + 1) :=
  Function.update_eq_self_iff

lemma upd_of_clean {T : ℕ} (z : ∀ i, κ i) (ii : Fin T) (b : Regs κ T)
    (hcl : ∀ j : Fin T, j ≠ ii → zeroRegs z T j = b j) (k : κ (ii.val + 1)) :
    Function.update b ii k = Function.update (zeroRegs z T) ii k := by
  funext j
  by_cases hj : j = ii
  · subst hj; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hj, Function.update_of_ne hj]; exact (hcl j hj).symm

lemma cR_fixes {T : ℕ} (piState : EuclideanSpace ℂ (X × X)) (z : ∀ i, κ i)
    (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (γ : ℝ)
    (hR : ApproxReflections piState z R γ) (ii : Fin T) :
    act (controlledR z R T ii) (initState z T piState) = initState z T piState := by
  have hfix := hR.fixes (ii.val + 1) (by omega)
  ext p
  by_cases hpb : ∃ j : Fin T, j < ii ∧ p.2.2 j ≠ z (j.val + 1)
  · rw [act_cR_bad z R ii _ p hpb]
    obtain ⟨j, _, hne⟩ := hpb
    rw [Supp_init z piState p ⟨j, Nat.zero_le _, hne⟩, neg_zero]
  · rw [act_cR_good z R ii _ p hpb]
    by_cases hcl : ∀ j : Fin T, j ≠ ii → zeroRegs z T j = p.2.2 j
    · have hfp := congrArg (fun v : EuclideanSpace ℂ (X × X × κ (ii.val + 1)) =>
        v (p.1, p.2.1, p.2.2 ii)) hfix
      simp only [act_apply] at hfp
      have hterm : ∀ w : X × X × κ (ii.val + 1),
          initState z T piState (w.1, w.2.1, Function.update p.2.2 ii w.2.2) =
            tensorZero (z (ii.val + 1)) piState w := by
        intro w
        show (if Function.update p.2.2 ii w.2.2 = zeroRegs z T then piState (w.1, w.2.1) else 0)
          = (if w.2.2 = z (ii.val + 1) then piState (w.1, w.2.1) else 0)
        rw [upd_of_clean z ii p.2.2 hcl w.2.2]
        by_cases hk : w.2.2 = z (ii.val + 1)
        · rw [if_pos hk, if_pos ((upd_zero_iff z ii _).mpr hk)]
        · rw [if_neg hk, if_neg (fun h => hk ((upd_zero_iff z ii _).mp h))]
      have hsum : ∑ w : X × X × κ (ii.val + 1), R (ii.val + 1) (p.1, p.2.1, p.2.2 ii) w *
          initState z T piState (w.1, w.2.1, Function.update p.2.2 ii w.2.2) =
          ∑ w : X × X × κ (ii.val + 1), R (ii.val + 1) (p.1, p.2.1, p.2.2 ii) w *
            tensorZero (z (ii.val + 1)) piState w :=
        Finset.sum_congr rfl fun w _ => by rw [hterm w]
      rw [hsum, hfp]
      show (if p.2.2 ii = z (ii.val + 1) then piState (p.1, p.2.1) else 0) =
        (if p.2.2 = zeroRegs z T then piState (p.1, p.2.1) else 0)
      have hiff : p.2.2 ii = z (ii.val + 1) ↔ p.2.2 = zeroRegs z T := by
        constructor
        · intro h
          funext j
          by_cases hj : j = ii
          · subst hj; exact h
          · exact (hcl j hj).symm
        · intro h; exact congrFun h ii
      by_cases h : p.2.2 = zeroRegs z T
      · rw [if_pos h, if_pos (hiff.mpr h)]
      · rw [if_neg h, if_neg (fun h' => h (hiff.mp h'))]
    · obtain ⟨j, hj, hne⟩ : ∃ j : Fin T, j ≠ ii ∧ p.2.2 j ≠ z (j.val + 1) := by
        by_contra hcon
        push_neg at hcon
        exact hcl (fun j hj => (hcon j hj).symm)
      rw [Supp_init z piState p ⟨j, Nat.zero_le _, hne⟩]
      refine Finset.sum_eq_zero fun w _ => ?_
      rw [Supp_init z piState (w.1, w.2.1, Function.update p.2.2 ii w.2.2) ⟨j, Nat.zero_le _, by
        show Function.update p.2.2 ii w.2.2 j ≠ z (j.val + 1)
        rw [Function.update_of_ne hj]; exact hne⟩, mul_zero]

lemma cR_plus_one_bound {T : ℕ} (piState : EuclideanSpace ℂ (X × X)) (z : ∀ i, κ i)
    (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (γ : ℝ) (hγ : 0 < γ)
    (hR : ApproxReflections piState z R γ) (ii : Fin T)
    (x : EuclideanSpace ℂ (X × X × Regs κ T))
    (hx : Supp z ii.val x) (hπx : inner ℂ (initState z T piState) x = 0) :
    ‖act (controlledR z R T ii + 1) x‖ ≤ beta γ (ii.val + 1) * ‖x‖ := by
  set ψ : EuclideanSpace ℂ (X × X) := WithLp.toLp 2 (fun ab => x (ab.1, ab.2, zeroRegs z T))
    with hψ
  have hinner : inner ℂ piState ψ = 0 := by
    rw [← hπx, EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, Pi.star_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_eq_single (zeroRegs z T)]
    · show x (a, b, zeroRegs z T) * star (piState (a, b)) =
        x (a, b, zeroRegs z T) * star (if zeroRegs z T = zeroRegs z T then piState (a, b) else 0)
      rw [if_pos rfl]
    · intro r _ hr
      show x (a, b, r) * star (if r = zeroRegs z T then piState (a, b) else 0) = 0
      rw [if_neg hr, star_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have htz : ∀ a b : X, ∀ k : κ (ii.val + 1),
      x (a, b, Function.update (zeroRegs z T) ii k) = tensorZero (z (ii.val + 1)) ψ (a, b, k) := by
    intro a b k
    show _ = if k = z (ii.val + 1) then x (a, b, zeroRegs z T) else 0
    by_cases hk : k = z (ii.val + 1)
    · rw [if_pos hk, (upd_zero_iff z ii k).mpr hk]
    · rw [if_neg hk]
      apply hx
      exact ⟨ii, le_refl _, by
        show Function.update (zeroRegs z T) ii k ii ≠ z (ii.val + 1)
        rw [Function.update_self]; exact hk⟩
  have hy : ∀ p : X × X × Regs κ T, act (controlledR z R T ii + 1) x p =
      if (∀ j : Fin T, j ≠ ii → zeroRegs z T j = p.2.2 j) then
        act (R (ii.val + 1) + 1) (tensorZero (z (ii.val + 1)) ψ) (p.1, p.2.1, p.2.2 ii)
      else 0 := by
    intro p
    rw [act_add, act_one, PiLp.add_apply]
    by_cases hpb : ∃ j : Fin T, j < ii ∧ p.2.2 j ≠ z (j.val + 1)
    · rw [act_cR_bad z R ii x p hpb, neg_add_cancel, if_neg]
      intro h
      obtain ⟨j, hj, hne⟩ := hpb
      exact hne (h j (ne_of_lt hj)).symm
    · rw [act_cR_good z R ii x p hpb]
      by_cases hcl : ∀ j : Fin T, j ≠ ii → zeroRegs z T j = p.2.2 j
      · rw [if_pos hcl, act_add, act_one, PiLp.add_apply, act_apply]
        have hp_eq : x p = tensorZero (z (ii.val + 1)) ψ (p.1, p.2.1, p.2.2 ii) := by
          (rw [← htz, ← upd_of_clean z ii p.2.2 hcl, Function.update_eq_self]) <;> rfl
        rw [hp_eq]
        congr 1
        refine Finset.sum_congr rfl fun w _ => ?_
        (rw [upd_of_clean z ii p.2.2 hcl, htz]) <;> rfl
      · rw [if_neg hcl]
        obtain ⟨j, hj, hne⟩ : ∃ j : Fin T, j ≠ ii ∧ p.2.2 j ≠ z (j.val + 1) := by
          by_contra hcon
          push_neg at hcon
          exact hcl (fun j hj => (hcon j hj).symm)
        have hij : ii.val ≤ j.val := by
          have h1 : ¬ j < ii := fun hlt => hpb ⟨j, hlt, hne⟩
          rw [Fin.lt_def] at h1
          omega
        rw [hx p ⟨j, hij, hne⟩, add_zero]
        refine Finset.sum_eq_zero fun w _ => ?_
        rw [hx (w.1, w.2.1, Function.update p.2.2 ii w.2.2) ⟨j, hij, by
          show Function.update p.2.2 ii w.2.2 j ≠ z (j.val + 1)
          rw [Function.update_of_ne hj]; exact hne⟩, mul_zero]
  have hnorm_y : ‖act (controlledR z R T ii + 1) x‖ =
      ‖act (R (ii.val + 1) + 1) (tensorZero (z (ii.val + 1)) ψ)‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    have h1 : ∀ p : X × X × Regs κ T, ‖act (controlledR z R T ii + 1) x p‖ ^ 2 =
        if (∀ j : Fin T, j ≠ ii → zeroRegs z T j = p.2.2 j) then
          ‖act (R (ii.val + 1) + 1) (tensorZero (z (ii.val + 1)) ψ) (p.1, p.2.1, p.2.2 ii)‖ ^ 2
        else 0 := by
      intro p; rw [hy p]; split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun p _ => h1 p), sum_agree3 ii (zeroRegs z T)]
    simp only [Function.update_self, Prod.mk.eta]
  have hψx : ‖ψ‖ ≤ ‖x‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    simp only [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
    exact Finset.single_le_sum (f := fun r => ‖x (a, b, r)‖ ^ 2) (fun r _ => sq_nonneg _)
      (Finset.mem_univ (zeroRegs z T))
  have hb := hR.approx (ii.val + 1) (by omega) ψ hinner
  have hβ : 0 ≤ beta γ (ii.val + 1) := by
    unfold beta
    exact div_nonneg (mul_nonneg (by positivity) hγ.le) (by positivity)
  calc ‖act (controlledR z R T ii + 1) x‖
      = ‖act (R (ii.val + 1) + 1) (tensorZero (z (ii.val + 1)) ψ)‖ := hnorm_y
    _ ≤ beta γ (ii.val + 1) * ‖ψ‖ := hb
    _ ≤ beta γ (ii.val + 1) * ‖x‖ := mul_le_mul_of_nonneg_left hψx hβ

lemma norm_init {T : ℕ} (z : ∀ i, κ i) (piState : EuclideanSpace ℂ (X × X)) :
    ‖initState z T piState‖ = ‖piState‖ := norm_tensorZero _ _

lemma fact1_core (M : Finset X) (piState : EuclideanSpace ℂ (X × X)) (hπ : ‖piState‖ = 1)
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (γ : ℝ) (hγ : 0 < γ)
    (hR : ApproxReflections piState z R γ) (T : ℕ) (ii : Fin T) :
    act (errOp M z R piState T ii) (phi M z R piState T ii.val) = 0 ∧
    ∀ v : EuclideanSpace ℂ (X × X × Regs κ T),
      (∀ p : X × X × Regs κ T, (∃ j : Fin T, ii ≤ j ∧ p.2.2 j ≠ z (j.val + 1)) → v p = 0) →
      inner ℂ (phi M z R piState T ii.val) v = 0 →
      ‖act (errOp M z R piState T ii) v‖ ≤ beta γ (ii.val + 1) * ‖v‖ := by
  have hAu := A_unitary M z R T hR.unitary ii.val
  have hA1 : (approxRAA M z R T ii.val)ᴴ * approxRAA M z R T ii.val = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hAu
  have hA2 : approxRAA M z R T ii.val * (approxRAA M z R T ii.val)ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp hAu
  have hφ1 : ‖phi M z R piState T ii.val‖ = 1 := by
    unfold phi; rw [norm_act_unitary hAu, norm_init, hπ]
  constructor
  · have h1 : act (reflStep M z R T ii) (phi M z R piState T ii.val) =
        phi M z R piState T ii.val := by
      unfold reflStep phi
      rw [act_mul, act_mul, ← act_mul (approxRAA M z R T ii.val)ᴴ, hA1, act_one,
        cR_fixes piState z R γ hR ii]
    have h2 : act (refState (phi M z R piState T ii.val)) (phi M z R piState T ii.val) =
        phi M z R piState T ii.val := by
      rw [act_refState, inner_self_eq_norm_sq_to_K, hφ1]
      ext p
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      push_cast; ring
    rw [errOp, act_sub_mat, h1, h2, sub_self]
  · intro v hv hinner
    have hvS : Supp z ii.val v := fun p ⟨j, hj, hne⟩ => hv p ⟨j, Fin.le_def.mpr hj, hne⟩
    have hx : act (approxRAA M z R T ii.val) (act (approxRAA M z R T ii.val)ᴴ v) = v := by
      rw [← act_mul, hA2, act_one]
    have herr : act (errOp M z R piState T ii) v = act (approxRAA M z R T ii.val)
        (act (controlledR z R T ii + 1) (act (approxRAA M z R T ii.val)ᴴ v)) := by
      rw [errOp, reflStep, act_sub_mat, act_refState, hinner, mul_zero, zero_smul, zero_sub,
        sub_neg_eq_add, act_mul, act_mul, act_add, act_one, act_vadd, hx]
    rw [herr, norm_act_unitary hAu]
    have hS' : Supp z ii.val (act (approxRAA M z R T ii.val)ᴴ v) :=
      Supp_act (Loc_ct (Loc_A M z R T ii.val)) hvS
    have hI : inner ℂ (initState z T piState) (act (approxRAA M z R T ii.val)ᴴ v) = 0 := by
      rw [← inner_act]; exact hinner
    have hb := cR_plus_one_bound piState z R γ hγ hR ii _ hS' hI
    rw [norm_act_unitary (ct_unitary hAu)] at hb
    exact hb

end Circ

end Aux_QWS

open QuantumWalkSearch.ApproxRAA in
theorem solution {X : Type*} [Fintype X] [DecidableEq X] {κ : ℕ → Type*}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (M : Finset X) (piState : EuclideanSpace ℂ (X × X)) (hπ : ‖piState‖ = 1)
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (γ : ℝ) (hγ : 0 < γ)
    (hR : ApproxReflections piState z R γ) (T : ℕ) (ii : Fin T) :
    act (errOp M z R piState T ii) (phi M z R piState T ii.val) = 0 ∧
    ∀ v : EuclideanSpace ℂ (X × X × Regs κ T),
      (∀ p : X × X × Regs κ T, (∃ j : Fin T, ii ≤ j ∧ p.2.2 j ≠ z (j.val + 1)) → v p = 0) →
      inner ℂ (phi M z R piState T ii.val) v = 0 →
      ‖act (errOp M z R piState T ii) v‖ ≤ beta γ (ii.val + 1) * ‖v‖ :=
  Aux_QWS.fact1_core M piState hπ z R γ hγ hR T ii
