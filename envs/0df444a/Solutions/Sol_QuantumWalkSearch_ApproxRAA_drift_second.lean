-- Prove2me | solution 1 for QuantumWalkSearch.ApproxRAA.drift_second
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T00:22:52.216771+00:00
-- url     : https://prove2.me/submissions/02184508-d16c-4a52-bcb1-ead6a9cbad4f

import Mathlib
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Setting
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Circuit
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Tolerant

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

namespace Aux_QWS

open QuantumWalkSearch.ApproxRAA

/-! ### One step of the amplitude recursion -/

section Amp

variable {X : Type*} [Fintype X] [DecidableEq X] {κ : ℕ → Type*} [∀ i, Fintype (κ i)]
  [∀ i, DecidableEq (κ i)]

noncomputable def sA (M : Finset X) (z : ∀ i, κ i)
    (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (piState : EuclideanSpace ℂ (X × X))
    (T n : ℕ) : ℝ :=
  ‖act (markedProj M) (phi M z R piState T n)‖

noncomputable def errV (M : Finset X) (z : ∀ i, κ i)
    (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (piState : EuclideanSpace ℂ (X × X))
    (T k : ℕ) (hk : k < T) : EuclideanSpace ℂ (X × X × Regs κ T) :=
  act (errOp M z R piState T ⟨k, hk⟩) (act (flipMarked M) (phi M z R piState T k))

lemma phi_zero (M : Finset X) (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ)
    (piState : EuclideanSpace ℂ (X × X)) (T : ℕ) :
    phi M z R piState T 0 = initState z T piState := by
  unfold phi; rw [A_zero, act_one]

lemma phi_norm (M : Finset X) (piState : EuclideanSpace ℂ (X × X)) (hπ : ‖piState‖ = 1)
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (γ : ℝ)
    (hR : ApproxReflections piState z R γ) (T n : ℕ) : ‖phi M z R piState T n‖ = 1 := by
  unfold phi; rw [norm_act_unitary (A_unitary M z R T hR.unitary n), norm_init, hπ]

lemma phi_Supp (M : Finset X) (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ)
    (piState : EuclideanSpace ℂ (X × X)) (T n : ℕ) : Supp z n (phi M z R piState T n) :=
  Supp_act (Loc_A M z R T n) (Supp_mono (Nat.zero_le n) (Supp_init z piState))

lemma sA_nonneg (M : Finset X) (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ)
    (piState : EuclideanSpace ℂ (X × X)) (T n : ℕ) : 0 ≤ sA M z R piState T n := norm_nonneg _

lemma sA_le_one (M : Finset X) (piState : EuclideanSpace ℂ (X × X)) (hπ : ‖piState‖ = 1)
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (γ : ℝ)
    (hR : ApproxReflections piState z R γ) (T n : ℕ) : sA M z R piState T n ≤ 1 :=
  (norm_PM_le M _).trans (le_of_eq (phi_norm M piState hπ z R γ hR T n))

lemma PU_phi_sq (M : Finset X) (piState : EuclideanSpace ℂ (X × X)) (hπ : ‖piState‖ = 1)
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (γ : ℝ)
    (hR : ApproxReflections piState z R γ) (T n : ℕ) :
    ‖act (unmarkedProj M) (phi M z R piState T n)‖ ^ 2 = 1 - sA M z R piState T n ^ 2 := by
  have h := norm_sq_split M (phi M z R piState T n)
  rw [phi_norm M piState hπ z R γ hR T n, one_pow] at h
  have h2 : sA M z R piState T n = ‖act (markedProj M) (phi M z R piState T n)‖ := rfl
  rw [h2]; linarith

lemma PU_phi_norm (M : Finset X) (piState : EuclideanSpace ℂ (X × X)) (hπ : ‖piState‖ = 1)
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (γ : ℝ)
    (hR : ApproxReflections piState z R γ) (T n : ℕ) :
    ‖act (unmarkedProj M) (phi M z R piState T n)‖ = Real.sqrt (1 - sA M z R piState T n ^ 2) := by
  rw [← PU_phi_sq M piState hπ z R γ hR T n, Real.sqrt_sq (norm_nonneg _)]

lemma errOp_eq (M : Finset X) (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ)
    (piState : EuclideanSpace ℂ (X × X)) (T k : ℕ) (hk : k < T) :
    errOp M z R piState T ⟨k, hk⟩ = reflStep M z R T ⟨k, hk⟩ - refState (phi M z R piState T k) :=
  rfl

lemma phi_succ (M : Finset X) (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ)
    (piState : EuclideanSpace ℂ (X × X)) (T k : ℕ) (hk : k < T) :
    phi M z R piState T (k + 1) =
      act (refState (phi M z R piState T k)) (act (flipMarked M) (phi M z R piState T k)) +
        errV M z R piState T k hk := by
  have h1 : phi M z R piState T (k + 1) =
      act (reflStep M z R T ⟨k, hk⟩) (act (flipMarked M) (phi M z R piState T k)) := by
    unfold phi reflStep
    rw [A_succ_lt M z R T k hk]
    simp only [act_mul] <;> rfl
  rw [h1]
  unfold errV
  rw [errOp_eq, act_sub_mat]
  abel

lemma inner_F_phi (M : Finset X) (piState : EuclideanSpace ℂ (X × X)) (hπ : ‖piState‖ = 1)
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (γ : ℝ)
    (hR : ApproxReflections piState z R γ) (T k : ℕ) :
    inner ℂ (phi M z R piState T k) (act (flipMarked M) (phi M z R piState T k)) =
      ((1 - 2 * sA M z R piState T k ^ 2 : ℝ) : ℂ) := by
  rw [inner_F, PU_phi_sq M piState hπ z R γ hR T k]
  have h2 : sA M z R piState T k = ‖act (markedProj M) (phi M z R piState T k)‖ := rfl
  rw [← h2]
  congr 1
  ring

lemma phi_succ_decomp (M : Finset X) (piState : EuclideanSpace ℂ (X × X)) (hπ : ‖piState‖ = 1)
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (γ : ℝ)
    (hR : ApproxReflections piState z R γ) (T k : ℕ) (hk : k < T) :
    phi M z R piState T (k + 1) =
      (2 * ((1 - 2 * sA M z R piState T k ^ 2 : ℝ) : ℂ)) • phi M z R piState T k -
        act (flipMarked M) (phi M z R piState T k) + errV M z R piState T k hk := by
  rw [phi_succ M z R piState T k hk, act_refState, inner_F_phi M piState hπ z R γ hR T k]

lemma PM_succ (M : Finset X) (piState : EuclideanSpace ℂ (X × X)) (hπ : ‖piState‖ = 1)
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (γ : ℝ)
    (hR : ApproxReflections piState z R γ) (T k : ℕ) (hk : k < T) :
    act (markedProj M) (phi M z R piState T (k + 1)) =
      ((3 - 4 * sA M z R piState T k ^ 2 : ℝ) : ℂ) • act (markedProj M) (phi M z R piState T k) +
        act (markedProj M) (errV M z R piState T k hk) := by
  rw [phi_succ_decomp M piState hπ z R γ hR T k hk]
  ext p
  simp only [PM_apply, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, F_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring

lemma PU_succ (M : Finset X) (piState : EuclideanSpace ℂ (X × X)) (hπ : ‖piState‖ = 1)
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (γ : ℝ)
    (hR : ApproxReflections piState z R γ) (T k : ℕ) (hk : k < T) :
    act (unmarkedProj M) (phi M z R piState T (k + 1)) =
      (1 - 4 * sA M z R piState T k ^ 2 : ℝ) • act (unmarkedProj M) (phi M z R piState T k) +
        act (unmarkedProj M) (errV M z R piState T k hk) := by
  rw [phi_succ_decomp M piState hπ z R γ hR T k hk]
  ext p
  simp only [PU_apply, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, F_apply, smul_eq_mul,
    Complex.real_smul]
  split_ifs <;> push_cast <;> ring

lemma errV_bound (M : Finset X) (piState : EuclideanSpace ℂ (X × X)) (hπ : ‖piState‖ = 1)
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (γ : ℝ) (hγ : 0 < γ)
    (hR : ApproxReflections piState z R γ) (T k : ℕ) (hk : k < T) :
    ‖errV M z R piState T k hk‖ ≤ beta γ (k + 1) *
      (2 * sA M z R piState T k * Real.sqrt (1 - sA M z R piState T k ^ 2)) := by
  set φ := phi M z R piState T k with hφ
  set s := sA M z R piState T k with hs
  have hsφ : ‖act (markedProj M) φ‖ = s := rfl
  have hφ1 : ‖φ‖ = 1 := phi_norm M piState hπ z R γ hR T k
  have hPU : ‖act (unmarkedProj M) φ‖ ^ 2 = 1 - s ^ 2 := PU_phi_sq M piState hπ z R γ hR T k
  have hs0 : 0 ≤ s := norm_nonneg _
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ((1 - 2 * s ^ 2 : ℝ) : ℂ) := ⟨_, rfl⟩
  have hw : act (flipMarked M) φ =
      sMU M ((-2 + 2 * s ^ 2 : ℝ) : ℂ) ((2 * s ^ 2 : ℝ) : ℂ) φ + c • φ := by
    ext p
    rw [PiLp.add_apply, PiLp.smul_apply, sMU_apply, F_apply, smul_eq_mul, hc]
    split_ifs <;> push_cast <;> ring
  obtain ⟨hE0, hE⟩ := fact1_core M piState hπ z R γ hγ hR T ⟨k, hk⟩
  have hE0' : act (errOp M z R piState T ⟨k, hk⟩) φ = 0 := hE0
  have hErr : errV M z R piState T k hk = act (errOp M z R piState T ⟨k, hk⟩)
      (sMU M ((-2 + 2 * s ^ 2 : ℝ) : ℂ) ((2 * s ^ 2 : ℝ) : ℂ) φ) := by
    show act (errOp M z R piState T ⟨k, hk⟩) (act (flipMarked M) φ) = _
    rw [hw, act_vadd, act_smul, hE0', smul_zero, add_zero]
  have hφS : Supp z k φ := phi_Supp M z R piState T k
  have hsupp : ∀ p : X × X × Regs κ T,
      (∃ j : Fin T, (⟨k, hk⟩ : Fin T) ≤ j ∧ p.2.2 j ≠ z (j.val + 1)) →
      sMU M ((-2 + 2 * s ^ 2 : ℝ) : ℂ) ((2 * s ^ 2 : ℝ) : ℂ) φ p = 0 := by
    rintro p ⟨j, hj, hne⟩
    rw [sMU_apply, hφS p ⟨j, Fin.le_def.mp hj, hne⟩]; simp
  have hwdef : sMU M ((-2 + 2 * s ^ 2 : ℝ) : ℂ) ((2 * s ^ 2 : ℝ) : ℂ) φ =
      act (flipMarked M) φ - c • φ := by
    rw [hw, add_sub_cancel_right]
  have hFc : inner ℂ φ (act (flipMarked M) φ) = c := by
    rw [hc]; exact inner_F_phi M piState hπ z R γ hR T k
  have horth : inner ℂ φ (sMU M ((-2 + 2 * s ^ 2 : ℝ) : ℂ) ((2 * s ^ 2 : ℝ) : ℂ) φ) = 0 := by
    rw [hwdef, inner_sub_right, inner_smul_right, hFc, inner_self_eq_norm_sq_to_K, hφ1]; simp
  have h1s : 0 ≤ 1 - s ^ 2 := by rw [← hPU]; positivity
  have hw_norm : ‖sMU M ((-2 + 2 * s ^ 2 : ℝ) : ℂ) ((2 * s ^ 2 : ℝ) : ℂ) φ‖ =
      2 * s * Real.sqrt (1 - s ^ 2) := by
    apply eq_of_sq_eq' (norm_nonneg _)
      (mul_nonneg (mul_nonneg (by norm_num) hs0) (Real.sqrt_nonneg _))
    rw [norm_sq_sMU, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      sq_abs, sq_abs, hsφ, hPU]
    simp only [mul_pow]
    rw [Real.sq_sqrt h1s]
    ring
  rw [hErr]
  calc _ ≤ beta γ ((⟨k, hk⟩ : Fin T).val + 1) *
        ‖sMU M ((-2 + 2 * s ^ 2 : ℝ) : ℂ) ((2 * s ^ 2 : ℝ) : ℂ) φ‖ := hE _ hsupp horth
    _ = beta γ (k + 1) * (2 * s * Real.sqrt (1 - s ^ 2)) := by (rw [hw_norm]) <;> rfl

lemma amp_bound (M : Finset X) (piState : EuclideanSpace ℂ (X × X)) (hπ : ‖piState‖ = 1)
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (γ : ℝ) (hγ : 0 < γ)
    (hR : ApproxReflections piState z R γ) (T k : ℕ) (hk : k < T) :
    |sA M z R piState T (k + 1) - |3 - 4 * sA M z R piState T k ^ 2| * sA M z R piState T k| ≤
      beta γ (k + 1) *
        (2 * sA M z R piState T k * Real.sqrt (1 - sA M z R piState T k ^ 2)) := by
  have h1 : sA M z R piState T (k + 1) =
      ‖((3 - 4 * sA M z R piState T k ^ 2 : ℝ) : ℂ) • act (markedProj M) (phi M z R piState T k) +
        act (markedProj M) (errV M z R piState T k hk)‖ := by
    show ‖act (markedProj M) (phi M z R piState T (k + 1))‖ = _
    rw [PM_succ M piState hπ z R γ hR T k hk]
  have h2 : ‖((3 - 4 * sA M z R piState T k ^ 2 : ℝ) : ℂ) •
      act (markedProj M) (phi M z R piState T k)‖ =
      |3 - 4 * sA M z R piState T k ^ 2| * sA M z R piState T k := by
    (rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]) <;> rfl
  rw [h1, ← h2]
  calc _ ≤ ‖((3 - 4 * sA M z R piState T k ^ 2 : ℝ) : ℂ) •
          act (markedProj M) (phi M z R piState T k) +
        act (markedProj M) (errV M z R piState T k hk) -
        ((3 - 4 * sA M z R piState T k ^ 2 : ℝ) : ℂ) •
          act (markedProj M) (phi M z R piState T k)‖ := abs_norm_sub_norm_le _ _
    _ = ‖act (markedProj M) (errV M z R piState T k hk)‖ := by rw [add_sub_cancel_left]
    _ ≤ ‖errV M z R piState T k hk‖ := norm_PM_le M _
    _ ≤ _ := errV_bound M piState hπ z R γ hγ hR T k hk

lemma sA_zero (M : Finset X) (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ)
    (piState : EuclideanSpace ℂ (X × X)) (T : ℕ) :
    sA M z R piState T 0 = ‖act (markedProj M) piState‖ := by
  show ‖act (markedProj M) (phi M z R piState T 0)‖ = _
  rw [phi_zero]
  have h : act (markedProj M) (initState z T piState) =
      tensorZero (zeroRegs z T) (act (markedProj M) piState) := by
    ext p
    rw [PM_apply]
    show _ = if p.2.2 = zeroRegs z T then act (markedProj M) piState (p.1, p.2.1) else 0
    rw [PM_apply]
    show (if p.1 ∈ M then (if p.2.2 = zeroRegs z T then piState (p.1, p.2.1) else 0) else 0) = _
    by_cases h1 : p.1 ∈ M <;> by_cases h2 : p.2.2 = zeroRegs z T <;> simp [h1, h2]
  rw [h, norm_tensorZero]

end Amp

end Aux_QWS

namespace Aux_QWS

open QuantumWalkSearch.ApproxRAA

/-! ### Real-variable estimates -/

section Real

lemma beta_nonneg (γ : ℝ) (hγ : 0 ≤ γ) (i : ℕ) : 0 ≤ beta γ i := by
  unfold beta
  exact div_nonneg (mul_nonneg (by positivity) hγ) (by positivity)

lemma S_le (γ : ℝ) (hγ : 0 ≤ γ) (n : ℕ) :
    4 * Real.pi * ∑ k ∈ Finset.range n, beta γ (k + 1) ≤ 3 * γ := by
  have hz : ∑ k ∈ Finset.range n, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2 ≤ Real.pi ^ 2 / 6 := by
    have h := sum_le_hasSum (Finset.range (n + 1)) (fun i _ => by positivity) hasSum_zeta_two
    rw [Finset.sum_range_succ'] at h
    have h0 : (1 : ℝ) / ((0 : ℕ) : ℝ) ^ 2 = 0 := by simp
    rw [h0, add_zero] at h
    exact h
  have hS : ∑ k ∈ Finset.range n, beta γ (k + 1) =
      18 / (4 * Real.pi ^ 3) * γ * ∑ k ∈ Finset.range n, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold beta
    ring
  rw [hS]
  have hpi := Real.pi_pos
  have hc : 0 ≤ 18 / (4 * Real.pi ^ 3) * γ := mul_nonneg (by positivity) hγ
  calc 4 * Real.pi * (18 / (4 * Real.pi ^ 3) * γ *
        ∑ k ∈ Finset.range n, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2)
      ≤ 4 * Real.pi * (18 / (4 * Real.pi ^ 3) * γ * (Real.pi ^ 2 / 6)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz hc) (by positivity)
    _ = 3 * γ := by field_simp; ring

lemma D_bound (s : ℕ → ℝ) (bt : ℕ → ℝ) (θ0 : ℝ) (N : ℕ)
    (hθ0 : 0 ≤ θ0) (h0 : s 0 = Real.sin θ0) (hs0 : ∀ n, 0 ≤ s n)
    (hrec : ∀ n, n < N → |s (n + 1) - |3 - 4 * s n ^ 2| * s n| ≤
      bt (n + 1) * (2 * s n * Real.sqrt (1 - s n ^ 2)))
    (hbt : ∀ k, 0 ≤ bt k) (hS : ∀ n, ∑ k ∈ Finset.range n, bt (k + 1) ≤ 1 / 2) :
    ∀ n, n ≤ N → (3 : ℝ) ^ n * θ0 < Real.pi / 4 →
      |s n - Real.sin ((3 : ℝ) ^ n * θ0)| ≤ (3 : ℝ) ^ n * θ0 * ∑ k ∈ Finset.range n, bt (k + 1) := by
  intro n
  induction n with
  | zero => intro _ _; simp [h0]
  | succ n ih =>
    intro hn ha
    obtain ⟨a, ha_def⟩ : ∃ a, a = (3 : ℝ) ^ n * θ0 := ⟨_, rfl⟩
    have h3 : (3 : ℝ) ^ (n + 1) * θ0 = 3 * a := by rw [ha_def]; ring
    rw [h3] at ha ⊢
    have ha0 : 0 ≤ a := by rw [ha_def]; exact mul_nonneg (pow_nonneg (by norm_num) n) hθ0
    have ha12 : a < Real.pi / 12 := by linarith
    have hIH := ih (by omega) (by rw [← ha_def]; linarith [Real.pi_pos])
    rw [← ha_def] at hIH
    obtain ⟨S, hS_def⟩ : ∃ S, S = ∑ k ∈ Finset.range n, bt (k + 1) := ⟨_, rfl⟩
    rw [← hS_def] at hIH
    rw [Finset.sum_range_succ, ← hS_def]
    have hS0 : 0 ≤ S := by rw [hS_def]; exact Finset.sum_nonneg fun k _ => hbt (k + 1)
    have hS1 : S ≤ 1 / 2 := by rw [hS_def]; exact hS n
    have hb0 := hbt (n + 1)
    obtain ⟨u, hu_def⟩ : ∃ u, u = Real.sin a := ⟨_, rfl⟩
    rw [← hu_def] at hIH
    have hu0 : 0 ≤ u := by
      rw [hu_def]; exact Real.sin_nonneg_of_nonneg_of_le_pi ha0 (by linarith [Real.pi_pos])
    have hua : u ≤ a := by rw [hu_def]; exact Real.sin_le ha0
    have hsn := hs0 n
    obtain ⟨hD1, hD2⟩ := abs_le.mp hIH
    have hpi : Real.pi < 3.15 := Real.pi_lt_d2
    have hs_up : s n ≤ a * (1 + S) := by nlinarith
    have hs_small : s n ≤ 2 / 5 := by nlinarith [mul_le_mul_of_nonneg_left hS1 ha0]
    have hu_small : u ≤ 2 / 5 := by linarith
    have hpos : 0 ≤ 3 - 4 * s n ^ 2 := by
      nlinarith [mul_le_mul hs_small hs_small hsn (by norm_num)]
    have hrn := hrec n (by omega)
    rw [abs_of_nonneg hpos] at hrn
    have hsq : Real.sqrt (1 - s n ^ 2) ≤ 1 := by
      calc Real.sqrt (1 - s n ^ 2) ≤ Real.sqrt 1 :=
            Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (s n)])
        _ = 1 := Real.sqrt_one
    have herr : bt (n + 1) * (2 * s n * Real.sqrt (1 - s n ^ 2)) ≤ 2 * bt (n + 1) * s n := by
      have h1 : s n * Real.sqrt (1 - s n ^ 2) ≤ s n := mul_le_of_le_one_right hsn hsq
      nlinarith [mul_le_mul_of_nonneg_left h1 hb0]
    rw [Real.sin_three_mul, ← hu_def]
    have hfac : (3 - 4 * s n ^ 2) * s n - (3 * u - 4 * u ^ 3) =
        (s n - u) * (3 - 4 * (s n ^ 2 + s n * u + u ^ 2)) := by ring
    have hQ0 : 0 ≤ s n ^ 2 + s n * u + u ^ 2 := by
      nlinarith [mul_nonneg hsn hu0, sq_nonneg (s n), sq_nonneg u]
    have hQ1 : s n ^ 2 + s n * u + u ^ 2 ≤ 3 / 2 := by
      nlinarith [mul_le_mul hs_small hu_small hu0 (by norm_num),
        mul_le_mul hs_small hs_small hsn (by norm_num), mul_le_mul hu_small hu_small hu0 (by norm_num)]
    have hf : |(3 - 4 * s n ^ 2) * s n - (3 * u - 4 * u ^ 3)| ≤ 3 * |s n - u| := by
      rw [hfac, abs_mul]
      have h1 : |3 - 4 * (s n ^ 2 + s n * u + u ^ 2)| ≤ 3 := abs_le.mpr ⟨by linarith, by linarith⟩
      calc |s n - u| * |3 - 4 * (s n ^ 2 + s n * u + u ^ 2)| ≤ |s n - u| * 3 :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = 3 * |s n - u| := mul_comm _ _
    have htri := abs_sub_le (s (n + 1)) ((3 - 4 * s n ^ 2) * s n) (3 * u - 4 * u ^ 3)
    have hbs : bt (n + 1) * s n ≤ bt (n + 1) * (a * (1 + S)) := mul_le_mul_of_nonneg_left hs_up hb0
    have hfin : 0 ≤ bt (n + 1) * a * (1 - 2 * S) := mul_nonneg (mul_nonneg hb0 ha0) (by linarith)
    nlinarith

lemma firsthit_lt (θ0 : ℝ) (hθ0 : 0 ≤ θ0) (t : ℕ) (ht : IsFirstHit θ0 t) :
    ∀ n, n < t → (3 : ℝ) ^ n * θ0 < Real.pi / 4 := by
  intro n hn
  by_contra hcon
  push_neg at hcon
  have hnot := ht.2 n hn
  have hgt : 3 * Real.pi / 4 < (3 : ℝ) ^ n * θ0 := by
    by_contra h2; push_neg at h2; exact hnot ⟨hcon, h2⟩
  have hmono : (3 : ℝ) ^ n * θ0 ≤ (3 : ℝ) ^ t * θ0 :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn.le) hθ0
  have := ht.1.2
  linarith

lemma sin_ge_of_mem (x : ℝ) (h1 : Real.pi / 4 ≤ x) (h2 : x ≤ 3 * Real.pi / 4) :
    Real.sqrt 2 / 2 ≤ Real.sin x := by
  rw [← Real.sin_pi_div_four]
  by_cases hx : x ≤ Real.pi / 2
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hx h1
  · rw [← Real.sin_pi_sub x]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith)
      (by linarith)

end Real

/-! ### The drift of the amplitude along the recursion -/

section Drift

variable {X : Type*} [Fintype X] [DecidableEq X] {κ : ℕ → Type*} [∀ i, Fintype (κ i)]
  [∀ i, DecidableEq (κ i)]

lemma theta_facts (M : Finset X) (piState : EuclideanSpace ℂ (X × X)) (hπ : ‖piState‖ = 1)
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (T : ℕ) :
    0 ≤ Real.arcsin (Real.sqrt (markedWeight M piState)) ∧
    Real.sin (Real.arcsin (Real.sqrt (markedWeight M piState))) = sA M z R piState T 0 := by
  have hPMπ1 : ‖act (markedProj M) piState‖ ≤ 1 := (norm_PM_le M piState).trans hπ.le
  have hmw : Real.sqrt (markedWeight M piState) = ‖act (markedProj M) piState‖ := by
    unfold markedWeight; exact Real.sqrt_sq (norm_nonneg _)
  refine ⟨Real.arcsin_nonneg.mpr (Real.sqrt_nonneg _), ?_⟩
  rw [hmw, sA_zero, Real.sin_arcsin (by linarith [norm_nonneg (act (markedProj M) piState)])
    hPMπ1]

/-- The angle-error bound along the recursion, valid while `3^n θ₀ < π/4`. -/
lemma D_phi (M : Finset X) (piState : EuclideanSpace ℂ (X × X)) (hπ : ‖piState‖ = 1)
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (γ : ℝ) (hγ : 0 < γ)
    (hγ1 : γ ≤ 1) (hR : ApproxReflections piState z R γ) (T : ℕ) :
    ∀ n, n ≤ T → (3 : ℝ) ^ n * Real.arcsin (Real.sqrt (markedWeight M piState)) < Real.pi / 4 →
      |sA M z R piState T n - Real.sin ((3 : ℝ) ^ n *
          Real.arcsin (Real.sqrt (markedWeight M piState)))| ≤
        (3 : ℝ) ^ n * Real.arcsin (Real.sqrt (markedWeight M piState)) *
          ∑ k ∈ Finset.range n, beta γ (k + 1) := by
  obtain ⟨hθ0, hsin0⟩ := theta_facts M piState hπ z R T
  have hβ0 : ∀ k, 0 ≤ beta γ k := fun k => beta_nonneg γ hγ.le k
  have hShalf : ∀ n, ∑ k ∈ Finset.range n, beta γ (k + 1) ≤ 1 / 2 := by
    intro n
    have h := S_le γ hγ.le n
    have h0 : 0 ≤ ∑ k ∈ Finset.range n, beta γ (k + 1) := Finset.sum_nonneg fun k _ => hβ0 (k + 1)
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr Real.pi_gt_three.le)]
  exact D_bound (fun n => sA M z R piState T n) (fun k => beta γ k) _ T hθ0 hsin0.symm
    (fun n => sA_nonneg M z R piState T n)
    (fun n hn => amp_bound M piState hπ z R γ hγ hR T n hn) hβ0 hShalf

end Drift

end Aux_QWS

namespace Aux_QWS

open QuantumWalkSearch.ApproxRAA

/-! ### Normalisation estimates and the Tolerant-RAA drift -/

section Norml

variable {ι : Type*} [Fintype ι]

lemma norm_normalize_sub (a b : EuclideanSpace ℂ ι) (hb : b ≠ 0) :
    ‖QuantumWalkSearch.ApproxRAA.normalize a - QuantumWalkSearch.ApproxRAA.normalize b‖ ≤
      2 * ‖a - b‖ / ‖b‖ := by
  unfold QuantumWalkSearch.ApproxRAA.normalize
  have hnb : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have h1 : ‖a‖⁻¹ • a - ‖b‖⁻¹ • b = (‖a‖⁻¹ - ‖b‖⁻¹) • a + ‖b‖⁻¹ • (a - b) := by
    rw [sub_smul, smul_sub]; abel
  rw [h1]
  have h2 : ‖(‖a‖⁻¹ - ‖b‖⁻¹) • a‖ ≤ ‖a - b‖ / ‖b‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    by_cases ha : a = 0
    · rw [ha, norm_zero, mul_zero]; positivity
    · have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
      have e : |‖a‖⁻¹ - ‖b‖⁻¹| * ‖a‖ = |‖b‖ - ‖a‖| / ‖b‖ := by
        rw [inv_sub_inv hna.ne' hnb.ne', abs_div, abs_of_pos (mul_pos hna hnb),
          div_mul_eq_mul_div, mul_comm ‖a‖ ‖b‖, mul_div_mul_right _ _ hna.ne']
      rw [e]
      apply div_le_div_of_nonneg_right _ hnb.le
      rw [norm_sub_rev]
      exact abs_norm_sub_norm_le b a
  have h3 : ‖‖b‖⁻¹ • (a - b)‖ = ‖a - b‖ / ‖b‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnb), inv_mul_eq_div]
  calc _ ≤ ‖(‖a‖⁻¹ - ‖b‖⁻¹) • a‖ + ‖‖b‖⁻¹ • (a - b)‖ := norm_add_le _ _
    _ ≤ ‖a - b‖ / ‖b‖ + ‖a - b‖ / ‖b‖ := by rw [h3]; linarith
    _ = 2 * ‖a - b‖ / ‖b‖ := by ring

lemma normalize_smul_pos (r : ℝ) (hr : 0 < r) (v : EuclideanSpace ℂ ι) :
    QuantumWalkSearch.ApproxRAA.normalize (r • v) = QuantumWalkSearch.ApproxRAA.normalize v := by
  unfold QuantumWalkSearch.ApproxRAA.normalize
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, smul_smul, mul_inv, mul_right_comm,
    inv_mul_cancel₀ hr.ne', one_mul]

end Norml

section NPU

variable {X : Type*} [Fintype X] [DecidableEq X] {ρ : Type*} [Fintype ρ] [DecidableEq ρ]

lemma normalize_PU_sub (M : Finset X) (v : EuclideanSpace ℂ (X × ρ)) (hv : ‖v‖ = 1)
    (hc : 0 < ‖act (unmarkedProj M) v‖) :
    ‖QuantumWalkSearch.ApproxRAA.normalize (act (unmarkedProj M) v) - v‖ ≤
      Real.arcsin ‖act (markedProj M) v‖ := by
  have hsplit := norm_sq_split M v
  rw [hv, one_pow] at hsplit
  have heq : QuantumWalkSearch.ApproxRAA.normalize (act (unmarkedProj M) v) - v =
      sMU M (-1) ((‖act (unmarkedProj M) v‖⁻¹ - 1 : ℝ) : ℂ) v := by
    ext p
    rw [PiLp.sub_apply]
    show ((‖act (unmarkedProj M) v‖⁻¹ : ℝ) • act (unmarkedProj M) v) p - v p = _
    rw [PiLp.smul_apply, PU_apply, sMU_apply, Complex.real_smul]
    split_ifs <;> push_cast <;> ring
  have hθ : Real.cos (Real.arcsin ‖act (markedProj M) v‖) = ‖act (unmarkedProj M) v‖ := by
    rw [Real.cos_arcsin,
      show 1 - ‖act (markedProj M) v‖ ^ 2 = ‖act (unmarkedProj M) v‖ ^ 2 by linarith]
    exact Real.sqrt_sq (norm_nonneg _)
  have hcos := Real.one_sub_sq_div_two_le_cos (x := Real.arcsin ‖act (markedProj M) v‖)
  rw [hθ] at hcos
  rw [heq]
  apply le_of_sq_le' (norm_nonneg _) (Real.arcsin_nonneg.mpr (norm_nonneg _))
  rw [norm_sq_sMU, Complex.norm_real, Real.norm_eq_abs, sq_abs, norm_neg, norm_one, one_pow,
    one_mul]
  have e1 : (‖act (unmarkedProj M) v‖⁻¹ - 1) * ‖act (unmarkedProj M) v‖ =
      1 - ‖act (unmarkedProj M) v‖ := by
    rw [sub_mul, inv_mul_cancel₀ hc.ne', one_mul]
  have e2 : (‖act (unmarkedProj M) v‖⁻¹ - 1) ^ 2 * ‖act (unmarkedProj M) v‖ ^ 2 =
      (1 - ‖act (unmarkedProj M) v‖) ^ 2 := by
    rw [← e1]; ring
  rw [e2]
  nlinarith

end NPU

section Drift2

variable {X : Type*} [Fintype X] [DecidableEq X] {κ : ℕ → Type*} [∀ i, Fintype (κ i)]
  [∀ i, DecidableEq (κ i)]

lemma small_facts (M : Finset X) (piState : EuclideanSpace ℂ (X × X)) (hπ : ‖piState‖ = 1)
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (γ : ℝ) (hγ : 0 < γ)
    (hγ' : γ ≤ 1 / 40) (hR : ApproxReflections piState z R γ) (t : ℕ)
    (ht : IsFirstHit (Real.arcsin (Real.sqrt (markedWeight M piState))) t) (T n : ℕ)
    (hnT : n ≤ T) (hnt : n < t) :
    sA M z R piState T n ≤ 0.72 ∧
    (n + 1 < t → sA M z R piState T n < 1 / 2 ∧
      sA M z R piState T n ≤ 2 * ((3 : ℝ) ^ n * Real.arcsin (Real.sqrt (markedWeight M piState)))) := by
  obtain ⟨hθ0, _⟩ := theta_facts M piState hπ z R T
  have ha4 := firsthit_lt _ hθ0 t ht n hnt
  have hD := D_phi M piState hπ z R γ hγ (by linarith) hR T n hnT ha4
  have ha4' : n + 1 < t → 3 * ((3 : ℝ) ^ n * Real.arcsin (Real.sqrt (markedWeight M piState))) <
      Real.pi / 4 := by
    intro h
    have h' := firsthit_lt _ hθ0 t ht (n + 1) h
    rw [pow_succ] at h'
    linarith
  have hS := S_le γ hγ.le n
  have hS0 : 0 ≤ ∑ k ∈ Finset.range n, beta γ (k + 1) :=
    Finset.sum_nonneg fun k _ => beta_nonneg γ hγ.le (k + 1)
  have ha0 : 0 ≤ (3 : ℝ) ^ n * Real.arcsin (Real.sqrt (markedWeight M piState)) :=
    mul_nonneg (pow_nonneg (by norm_num) n) hθ0
  have hu_lt : Real.sin ((3 : ℝ) ^ n * Real.arcsin (Real.sqrt (markedWeight M piState))) <
      Real.sqrt 2 / 2 := by
    rw [← Real.sin_pi_div_four]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]) ha4
  have hu_le := Real.sin_le ha0
  clear ht
  generalize sA M z R piState T n = s at hD ⊢
  generalize Real.sin ((3 : ℝ) ^ n * Real.arcsin (Real.sqrt (markedWeight M piState))) = u
    at hD hu_lt hu_le
  generalize (3 : ℝ) ^ n * Real.arcsin (Real.sqrt (markedWeight M piState)) = a
    at hD ha4 ha4' ha0 hu_le ⊢
  generalize ∑ k ∈ Finset.range n, beta γ (k + 1) = S at hD hS hS0
  have hSs : S ≤ 1 / 160 := by
    have := mul_nonneg hS0 (sub_nonneg.mpr Real.pi_gt_three.le)
    nlinarith
  have hr2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hr2up : Real.sqrt 2 < 1.4143 := by nlinarith [Real.sqrt_nonneg 2]
  have hpi := Real.pi_lt_d2
  obtain ⟨_, hD2⟩ := abs_le.mp hD
  have haS : a * S ≤ a * (1 / 160) := mul_le_mul_of_nonneg_left hSs ha0
  constructor
  · linarith
  · intro hn1
    have h3 := ha4' hn1
    constructor
    · linarith
    · linarith

lemma cos_ge (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 0.72) : 2 / 3 ≤ Real.sqrt (1 - s ^ 2) := by
  rw [Real.le_sqrt' (by norm_num)]
  have := mul_le_mul hs hs hs0 (by norm_num)
  nlinarith

lemma driftfirst_main (M : Finset X) (piState : EuclideanSpace ℂ (X × X)) (hπ : ‖piState‖ = 1)
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ ≤ 1 / 40) (hR : ApproxReflections piState z R γ) (t : ℕ)
    (ht : IsFirstHit (Real.arcsin (Real.sqrt (markedWeight M piState))) t) (T : ℕ) (htT : t ≤ T)
    (i : ℕ) (hi : 1 ≤ i) (hit : i < t) :
    ‖leftover M z R piState T i - muPerp M z R piState T i‖ ≤
        2 * ‖tolState M z R piState T i - phi M z R piState T i‖ /
          Real.cos (markedAngle M (phi M z R piState T i)) ∧
      2 * ‖tolState M z R piState T i - phi M z R piState T i‖ /
          Real.cos (markedAngle M (phi M z R piState T i)) ≤
        3 * ‖tolState M z R piState T i - phi M z R piState T i‖ := by
  obtain ⟨hsle, -⟩ := small_facts M piState hπ z R γ hγ hγ' hR t ht T i (by omega) hit
  have hc23 := cos_ge _ (sA_nonneg M z R piState T i) hsle
  have hcos : Real.cos (markedAngle M (phi M z R piState T i)) =
      Real.sqrt (1 - sA M z R piState T i ^ 2) := Real.cos_arcsin _
  have hPU := PU_phi_norm M piState hπ z R γ hR T i
  rw [hcos]
  have hcpos : 0 < Real.sqrt (1 - sA M z R piState T i ^ 2) := by linarith
  have hb : act (unmarkedProj M) (phi M z R piState T i) ≠ 0 := by
    intro h; rw [h, norm_zero] at hPU; linarith
  have hδ0 := norm_nonneg (tolState M z R piState T i - phi M z R piState T i)
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have hlo : leftover M z R piState T (i' + 1) = QuantumWalkSearch.ApproxRAA.normalize
      (act (unmarkedProj M) (tolState M z R piState T (i' + 1))) := rfl
  have hmu : muPerp M z R piState T (i' + 1) = QuantumWalkSearch.ApproxRAA.normalize
      (act (unmarkedProj M) (phi M z R piState T (i' + 1))) := rfl
  have hnorm := norm_normalize_sub (act (unmarkedProj M) (tolState M z R piState T (i' + 1)))
    (act (unmarkedProj M) (phi M z R piState T (i' + 1))) hb
  have hab : ‖act (unmarkedProj M) (tolState M z R piState T (i' + 1)) -
      act (unmarkedProj M) (phi M z R piState T (i' + 1))‖ ≤
      ‖tolState M z R piState T (i' + 1) - phi M z R piState T (i' + 1)‖ := by
    rw [← act_vsub]; exact norm_PU_le M _
  rw [hPU] at hnorm
  constructor
  · rw [hlo, hmu]
    exact hnorm.trans (div_le_div_of_nonneg_right (by linarith) hcpos.le)
  · rw [div_le_iff₀ hcpos]
    have := mul_le_mul_of_nonneg_left hc23 hδ0
    linarith

lemma driftsecond_main (M : Finset X) (piState : EuclideanSpace ℂ (X × X)) (hπ : ‖piState‖ = 1)
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ ≤ 1 / 40) (hR : ApproxReflections piState z R γ) (t : ℕ)
    (ht : IsFirstHit (Real.arcsin (Real.sqrt (markedWeight M piState))) t) (T : ℕ)
    (k : Fin T) (hkt : k.val + 1 < t) :
    ‖muPerp M z R piState T (k.val + 1) - muPerp M z R piState T k.val‖ ≤
        2 * ‖act (errOp M z R piState T k) (act (flipMarked M) (phi M z R piState T k.val))‖ /
          Real.cos (markedAngle M (phi M z R piState T (k.val + 1))) ∧
      2 * ‖act (errOp M z R piState T k) (act (flipMarked M) (phi M z R piState T k.val))‖ /
          Real.cos (markedAngle M (phi M z R piState T (k.val + 1))) ≤
        12 * beta γ (k.val + 1) *
          ((3 : ℝ) ^ k.val * Real.arcsin (Real.sqrt (markedWeight M piState))) := by
  have hk := k.isLt
  obtain ⟨-, hsmall⟩ := small_facts M piState hπ z R γ hγ hγ' hR t ht T k.val (by omega) (by omega)
  obtain ⟨hk12, hk2a⟩ := hsmall hkt
  obtain ⟨hk1le, -⟩ := small_facts M piState hπ z R γ hγ hγ' hR t ht T (k.val + 1) (by omega) hkt
  have hPUs := PU_succ M piState hπ z R γ hR T k.val hk
  have hErr : act (errOp M z R piState T k) (act (flipMarked M) (phi M z R piState T k.val)) =
      errV M z R piState T k.val hk := rfl
  rw [hErr]
  have hcos1 : Real.cos (markedAngle M (phi M z R piState T (k.val + 1))) =
      Real.sqrt (1 - sA M z R piState T (k.val + 1) ^ 2) := Real.cos_arcsin _
  rw [hcos1]
  have hPU1 := PU_phi_norm M piState hπ z R γ hR T (k.val + 1)
  have hc23 := cos_ge _ (sA_nonneg M z R piState T (k.val + 1)) hk1le
  have hcpos : 0 < Real.sqrt (1 - sA M z R piState T (k.val + 1) ^ 2) := by linarith
  have ha : act (unmarkedProj M) (phi M z R piState T (k.val + 1)) ≠ 0 := by
    intro h; rw [h, norm_zero] at hPU1; linarith
  have hs0 := sA_nonneg M z R piState T k.val
  have hr : 0 < 1 - 4 * sA M z R piState T k.val ^ 2 := by
    have := mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ 1 / 2 - sA M z R piState T k.val)
    nlinarith
  have hmu_k : muPerp M z R piState T k.val = QuantumWalkSearch.ApproxRAA.normalize
      ((1 - 4 * sA M z R piState T k.val ^ 2) • act (unmarkedProj M) (phi M z R piState T k.val)) := by
    (rw [normalize_smul_pos _ hr]) <;> rfl
  have hmu_k1 : muPerp M z R piState T (k.val + 1) = QuantumWalkSearch.ApproxRAA.normalize
      (act (unmarkedProj M) (phi M z R piState T (k.val + 1))) := rfl
  have hnorm := norm_normalize_sub
    ((1 - 4 * sA M z R piState T k.val ^ 2) • act (unmarkedProj M) (phi M z R piState T k.val))
    (act (unmarkedProj M) (phi M z R piState T (k.val + 1))) ha
  have hdiff : ‖(1 - 4 * sA M z R piState T k.val ^ 2) •
      act (unmarkedProj M) (phi M z R piState T k.val) -
      act (unmarkedProj M) (phi M z R piState T (k.val + 1))‖ =
      ‖act (unmarkedProj M) (errV M z R piState T k.val hk)‖ := by
    rw [hPUs, sub_add_cancel_left, norm_neg]
  rw [hdiff, hPU1] at hnorm
  have hPUe := norm_PU_le M (errV M z R piState T k.val hk)
  have hE := errV_bound M piState hπ z R γ hγ hR T k.val hk
  constructor
  · rw [hmu_k1, hmu_k, norm_sub_rev]
    exact hnorm.trans (div_le_div_of_nonneg_right (by linarith) hcpos.le)
  · rw [div_le_iff₀ hcpos]
    have hβ := beta_nonneg γ hγ.le (k.val + 1)
    have ha0 : 0 ≤ (3 : ℝ) ^ k.val * Real.arcsin (Real.sqrt (markedWeight M piState)) :=
      mul_nonneg (pow_nonneg (by norm_num) _)
        (Real.arcsin_nonneg.mpr (Real.sqrt_nonneg _))
    have hsq : Real.sqrt (1 - sA M z R piState T k.val ^ 2) ≤ 1 := by
      calc Real.sqrt (1 - sA M z R piState T k.val ^ 2) ≤ Real.sqrt 1 :=
            Real.sqrt_le_sqrt (by linarith [sq_nonneg (sA M z R piState T k.val)])
        _ = 1 := Real.sqrt_one
    have e1 : beta γ (k.val + 1) * (2 * sA M z R piState T k.val *
        Real.sqrt (1 - sA M z R piState T k.val ^ 2)) ≤
        beta γ (k.val + 1) * (2 * sA M z R piState T k.val) := by
      apply mul_le_mul_of_nonneg_left _ hβ
      have := mul_le_mul_of_nonneg_left hsq (by linarith : (0 : ℝ) ≤ 2 * sA M z R piState T k.val)
      linarith
    have e2 : beta γ (k.val + 1) * sA M z R piState T k.val ≤
        beta γ (k.val + 1) * (2 * ((3 : ℝ) ^ k.val *
          Real.arcsin (Real.sqrt (markedWeight M piState)))) :=
      mul_le_mul_of_nonneg_left hk2a hβ
    have hβa := mul_nonneg hβ ha0
    have e3 : 12 * beta γ (k.val + 1) * ((3 : ℝ) ^ k.val *
        Real.arcsin (Real.sqrt (markedWeight M piState))) * (2 / 3) ≤
        12 * beta γ (k.val + 1) * ((3 : ℝ) ^ k.val *
          Real.arcsin (Real.sqrt (markedWeight M piState))) *
          Real.sqrt (1 - sA M z R piState T (k.val + 1) ^ 2) :=
      mul_le_mul_of_nonneg_left hc23 (by linarith)
    linarith

lemma tol_zero (M : Finset X) (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ)
    (piState : EuclideanSpace ℂ (X × X)) (T : ℕ) :
    tolState M z R piState T 0 = phi M z R piState T 0 := by
  show act (approxRAA M z R T 0) (leftover M z R piState T 0) = _
  (rw [A_zero, act_one, phi_zero]) <;> rfl

lemma tol_succ (M : Finset X) (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ)
    (piState : EuclideanSpace ℂ (X × X)) (γ : ℝ) (hR : ApproxReflections piState z R γ)
    (T n : ℕ) :
    ‖tolState M z R piState T (n + 1) - phi M z R piState T (n + 1)‖ =
      ‖leftover M z R piState T n - phi M z R piState T 0‖ := by
  show ‖act (approxRAA M z R T (n + 1)) (leftover M z R piState T n) -
    act (approxRAA M z R T (n + 1)) (initState z T piState)‖ = _
  rw [← act_vsub, norm_act_unitary (A_unitary M z R T hR.unitary (n + 1)), phi_zero]

lemma mu_tele (M : Finset X) (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ)
    (piState : EuclideanSpace ℂ (X × X)) (T : ℕ) : ∀ n : ℕ,
    ‖muPerp M z R piState T n - muPerp M z R piState T 0‖ ≤
      ∑ k ∈ Finset.range n, ‖muPerp M z R piState T (k + 1) - muPerp M z R piState T k‖
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ]
    have ih := mu_tele M z R piState T n
    have h := norm_sub_le_norm_sub_add_norm_sub (muPerp M z R piState T (n + 1))
      (muPerp M z R piState T n) (muPerp M z R piState T 0)
    linarith

lemma theta_eq (M : Finset X) (piState : EuclideanSpace ℂ (X × X))
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (T : ℕ) :
    Real.arcsin (Real.sqrt (markedWeight M piState)) = Real.arcsin (sA M z R piState T 0) := by
  have hmw : Real.sqrt (markedWeight M piState) = ‖act (markedProj M) piState‖ := by
    unfold markedWeight; exact Real.sqrt_sq (norm_nonneg _)
  rw [hmw, sA_zero]

lemma drifttotal_main (M : Finset X) (piState : EuclideanSpace ℂ (X × X)) (hπ : ‖piState‖ = 1)
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ ≤ 1 / 40) (hR : ApproxReflections piState z R γ) (t : ℕ)
    (ht : IsFirstHit (Real.arcsin (Real.sqrt (markedWeight M piState))) t) (T : ℕ)
    (htT : t ≤ T) :
    ‖tolState M z R piState T t - phi M z R piState T t‖ ≤ Real.pi / 8 + 9 * γ / 8 := by
  rcases Nat.eq_zero_or_pos t with h0t | htpos
  · subst h0t
    rw [tol_zero, sub_self, norm_zero]
    have := Real.pi_pos
    linarith
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  obtain ⟨hθ0, -⟩ := theta_facts M piState hπ z R T
  have hfirst := firsthit_lt _ hθ0 (m + 1) ht
  have hβ0 : ∀ k, 0 ≤ beta γ k := fun k => beta_nonneg γ hγ.le k
  -- the bound on `‖μ₀ - φ₀‖`
  obtain ⟨hs0le, -⟩ := small_facts M piState hπ z R γ hγ hγ' hR (m + 1) ht T 0 (by omega) (by omega)
  have hmu0 : ‖muPerp M z R piState T 0 - phi M z R piState T 0‖ ≤
      Real.arcsin (Real.sqrt (markedWeight M piState)) := by
    rw [theta_eq M piState z R T]
    have hPU0 := PU_phi_norm M piState hπ z R γ hR T 0
    have hc0 : 0 < ‖act (unmarkedProj M) (phi M z R piState T 0)‖ := by
      rw [hPU0]
      have := cos_ge _ (sA_nonneg M z R piState T 0) hs0le
      linarith
    exact normalize_PU_sub M _ (phi_norm M piState hπ z R γ hR T 0) hc0
  -- the drift of `μ`
  have hdr : ∀ k, k + 1 < m + 1 → ‖muPerp M z R piState T (k + 1) - muPerp M z R piState T k‖ ≤
      12 * beta γ (k + 1) * ((3 : ℝ) ^ k * Real.arcsin (Real.sqrt (markedWeight M piState))) := by
    intro k hk
    have h := driftsecond_main M piState hπ z R γ hγ hγ' hR (m + 1) ht T ⟨k, by omega⟩ hk
    exact h.1.trans h.2
  -- the main induction
  have key : ∀ n, n ≤ m →
      ‖leftover M z R piState T n - phi M z R piState T 0‖ +
        (Real.arcsin (Real.sqrt (markedWeight M piState)) + ∑ k ∈ Finset.range n,
          12 * beta γ (k + 1) * ((3 : ℝ) ^ k * Real.arcsin (Real.sqrt (markedWeight M piState)))) / 2
        ≤ (3 : ℝ) ^ n * Real.arcsin (Real.sqrt (markedWeight M piState)) *
          (1 / 2 + 6 * ∑ k ∈ Finset.range n, beta γ (k + 1)) := by
    intro n
    induction n with
    | zero =>
      intro _
      have h0 : leftover M z R piState T 0 = phi M z R piState T 0 := by
        (rw [phi_zero]) <;> rfl
      rw [h0, sub_self, norm_zero]
      simp only [Finset.sum_range_zero, pow_zero, one_mul, add_zero, zero_add, mul_zero]
      linarith
    | succ n ih =>
      intro hn
      have ihn := ih (by omega)
      have hfst := driftfirst_main M piState hπ z R γ hγ hγ' hR (m + 1) ht T htT (n + 1)
        (by omega) (by omega)
      have hlm : ‖leftover M z R piState T (n + 1) - muPerp M z R piState T (n + 1)‖ ≤
          3 * ‖leftover M z R piState T n - phi M z R piState T 0‖ := by
        rw [← tol_succ M z R piState γ hR T n]; exact hfst.1.trans hfst.2
      have htel := mu_tele M z R piState T (n + 1)
      have hsum : ∑ k ∈ Finset.range (n + 1),
          ‖muPerp M z R piState T (k + 1) - muPerp M z R piState T k‖ ≤
          ∑ k ∈ Finset.range (n + 1), 12 * beta γ (k + 1) *
            ((3 : ℝ) ^ k * Real.arcsin (Real.sqrt (markedWeight M piState))) :=
        Finset.sum_le_sum fun k hk => hdr k (by rw [Finset.mem_range] at hk; omega)
      have htri1 := norm_sub_le_norm_sub_add_norm_sub (leftover M z R piState T (n + 1))
        (muPerp M z R piState T (n + 1)) (phi M z R piState T 0)
      have htri2 := norm_sub_le_norm_sub_add_norm_sub (muPerp M z R piState T (n + 1))
        (muPerp M z R piState T 0) (phi M z R piState T 0)
      have hMs : ∑ k ∈ Finset.range (n + 1), 12 * beta γ (k + 1) *
            ((3 : ℝ) ^ k * Real.arcsin (Real.sqrt (markedWeight M piState))) =
          ∑ k ∈ Finset.range n, 12 * beta γ (k + 1) *
            ((3 : ℝ) ^ k * Real.arcsin (Real.sqrt (markedWeight M piState))) +
          12 * beta γ (n + 1) * ((3 : ℝ) ^ n * Real.arcsin (Real.sqrt (markedWeight M piState))) :=
        Finset.sum_range_succ _ _
      have hSs : ∑ k ∈ Finset.range (n + 1), beta γ (k + 1) =
          ∑ k ∈ Finset.range n, beta γ (k + 1) + beta γ (n + 1) := Finset.sum_range_succ _ _
      rw [hMs] at hsum
      rw [hMs, hSs]
      have h3 : (3 : ℝ) ^ (n + 1) * Real.arcsin (Real.sqrt (markedWeight M piState)) =
          3 * ((3 : ℝ) ^ n * Real.arcsin (Real.sqrt (markedWeight M piState))) := by ring
      rw [h3]
      linarith
  have hfin := key m le_rfl
  rw [tol_succ M z R piState γ hR T m]
  have ham := hfirst m (by omega)
  have hS := S_le γ hγ.le m
  have hS0 : 0 ≤ ∑ k ∈ Finset.range m, beta γ (k + 1) :=
    Finset.sum_nonneg fun k _ => hβ0 (k + 1)
  have hM0 : 0 ≤ ∑ k ∈ Finset.range m,
      12 * beta γ (k + 1) * ((3 : ℝ) ^ k * Real.arcsin (Real.sqrt (markedWeight M piState))) :=
    Finset.sum_nonneg fun k _ => mul_nonneg (mul_nonneg (by norm_num) (hβ0 (k + 1)))
      (mul_nonneg (pow_nonneg (by norm_num) k) hθ0)
  have ha0 : 0 ≤ (3 : ℝ) ^ m * Real.arcsin (Real.sqrt (markedWeight M piState)) :=
    mul_nonneg (pow_nonneg (by norm_num) m) hθ0
  have e1 := mul_le_mul_of_nonneg_right ham.le
    (by linarith : (0 : ℝ) ≤ 1 / 2 + 6 * ∑ k ∈ Finset.range m, beta γ (k + 1))
  have hpi := Real.pi_pos
  linarith

end Drift2

end Aux_QWS

open QuantumWalkSearch.ApproxRAA in
theorem solution {X : Type*} [Fintype X] [DecidableEq X] {κ : ℕ → Type*}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (M : Finset X) (piState : EuclideanSpace ℂ (X × X)) (hπ : ‖piState‖ = 1)
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ ≤ 1 / 40) (hR : ApproxReflections piState z R γ) (t : ℕ)
    (ht : IsFirstHit (Real.arcsin (Real.sqrt (markedWeight M piState))) t) (T : ℕ)
    (k : Fin T) (hkt : k.val + 1 < t) :
    ‖muPerp M z R piState T (k.val + 1) - muPerp M z R piState T k.val‖ ≤
        2 * ‖act (errOp M z R piState T k) (act (flipMarked M) (phi M z R piState T k.val))‖ /
          Real.cos (markedAngle M (phi M z R piState T (k.val + 1))) ∧
      2 * ‖act (errOp M z R piState T k) (act (flipMarked M) (phi M z R piState T k.val))‖ /
          Real.cos (markedAngle M (phi M z R piState T (k.val + 1))) ≤
        12 * beta γ (k.val + 1) *
          ((3 : ℝ) ^ k.val * Real.arcsin (Real.sqrt (markedWeight M piState))) :=
  Aux_QWS.driftsecond_main M piState hπ z R γ hγ hγ' hR t ht T k hkt
