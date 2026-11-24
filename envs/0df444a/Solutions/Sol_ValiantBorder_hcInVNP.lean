-- Prove2me | solution 1 for ValiantBorder.hcInVNP
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:00:05.933633+00:00
-- url     : https://prove2.me/submissions/04b47916-6703-4bed-b737-8858b574b765

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Definitions.Def_VP_VNP_all_fields

/-! Adapted from Claude (Anthropic), *VP ≠ VNP over every field*.
The verifier, its correctness and size proofs, and the circuit combinators are from
`vp-vnp/Nc/Hc/Vnp.lean`, `vp-vnp/Nc/Final/CClasses.lean`, and `vp-vnp/Paper/Fields.lean`,
revision 11b6c7e3c927df2658f513b6b68ea7f8929c62c5 of `anthropics/formal-math` (Apache-2.0).
This port uses Prove2Me's `Statement.Computes`, `Statement.hc` and `Statement.VNP` directly. -/

namespace Statement
open Finset MvPolynomial

private noncomputable def hcSum {n : ℕ} {R : Type*} [CommSemiring R] (M : Fin n → Fin n → R) : R := by
  classical
  exact ∑ σ : Equiv.Perm (Fin n) with σ.IsCycleOn Set.univ, ∏ i, M i (σ i)

variable {F : Type*} [CommSemiring F]
noncomputable def bits {X : Type*} {m : ℕ} (q : MvPolynomial (X ⊕ Fin m) F) (e : Fin m → Bool) :
    MvPolynomial X F :=
  MvPolynomial.aeval (Sum.elim MvPolynomial.X fun i => if e i then 1 else 0) q

section
variable {X : Type}

theorem Computes.mono {p : MvPolynomial X F} {s t : ℕ} (h : Computes p s) (hst : s ≤ t) : Computes p t := by
  obtain ⟨l, hl, a, ha, rfl⟩ := h
  refine ⟨fun k => if k < s then l k else MvPolynomial.C 0, fun k hk => ?_, a, by omega, if_pos ha⟩
  by_cases h : k < s
  · have e : ∀ i < k, (if i < s then l i else MvPolynomial.C 0) = l i := fun i hi => if_pos (by omega)
    rcases hl k h with ⟨i, h1⟩ | ⟨c, h1⟩ | ⟨i, hi, j, hj, h1⟩ | ⟨i, hi, j, hj, h1⟩
    · exact Or.inl ⟨i, by simp only [h, if_true, h1]⟩
    · exact Or.inr (Or.inl ⟨c, by simp only [h, if_true, h1]⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, by
        simp only [h, if_true, h1, show i < s by omega, show j < s by omega]⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨i, hi, j, hj, by
        simp only [h, if_true, h1, show i < s by omega, show j < s by omega]⟩))
  · exact Or.inr (Or.inl ⟨0, by simp only [h, if_false]⟩)

theorem Computes.join {p q r : MvPolynomial X F} {s t : ℕ} (hp : Computes p s) (hq : Computes q t)
    (hr : r = p + q ∨ r = p * q) : Computes r (s + t + 1) := by
  obtain ⟨l, hl, a, ha, rfl⟩ := hp
  obtain ⟨l', hl', b, hb, rfl⟩ := hq
  let L : ℕ → MvPolynomial X F := fun k => if k < s then l k else if k < s + t then l' (k - s) else r
  have L1 : ∀ k < s, L k = l k := fun k hk => if_pos hk
  have L2 : ∀ k < t, L (s + k) = l' k := fun k hk => by
    simp only [L]
    rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
  have L3 : L (s + t) = r := by
    simp only [L]
    rw [if_neg (by omega), if_neg (by omega)]
  refine ⟨L, fun k hk => ?_, s + t, by omega, L3⟩
  rcases lt_or_ge k s with h | h
  · rw [L1 k h]
    rcases hl k h with e | e | ⟨i, hi, j, hj, e⟩ | ⟨i, hi, j, hj, e⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, by rw [L1 i (by omega), L1 j (by omega), e]⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨i, hi, j, hj, by rw [L1 i (by omega), L1 j (by omega), e]⟩))
  · rcases lt_or_ge k (s + t) with h' | h'
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
      have hk' : k < t := by omega
      rw [L2 k hk']
      rcases hl' k hk' with e | e | ⟨i, hi, j, hj, e⟩ | ⟨i, hi, j, hj, e⟩
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inl ⟨s + i, by omega, s + j, by omega, by
          rw [L2 i (by omega), L2 j (by omega), e]⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨s + i, by omega, s + j, by omega, by
          rw [L2 i (by omega), L2 j (by omega), e]⟩))
    · obtain rfl : k = s + t := by omega
      rw [L3]
      rcases hr with hr | hr
      · exact Or.inr (Or.inr (Or.inl ⟨a, by omega, s + b, by omega, by rw [L1 a ha, L2 b hb, hr]⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨a, by omega, s + b, by omega, by rw [L1 a ha, L2 b hb, hr]⟩))

/-- The polynomial has circuits with s gates and degree at most d. -/
def CSize (p : MvPolynomial X F) (s d : ℕ) : Prop := Computes p s ∧ p.totalDegree ≤ d

namespace CSize

theorem mono {p : MvPolynomial X F} {s d s' d' : ℕ} (h : CSize p s d) (hs : s ≤ s') (hd : d ≤ d') :
    CSize p s' d' := ⟨h.1.mono hs, h.2.trans hd⟩

theorem var (x : X) : CSize (MvPolynomial.X x : MvPolynomial X F) 1 1 := by
  refine ⟨⟨fun _ => MvPolynomial.X x, fun _ _ => Or.inl ⟨x, rfl⟩, 0, by omega, rfl⟩, ?_⟩
  refine (MvPolynomial.totalDegree_monomial_le (R := F) (Finsupp.single x 1) 1).trans ?_
  rw [Finsupp.sum_single_index rfl]
  exact le_rfl

theorem const (a : F) : CSize (MvPolynomial.C a : MvPolynomial X F) 1 0 := by
  refine ⟨⟨fun _ => MvPolynomial.C a, fun _ _ => Or.inr (Or.inl ⟨a, rfl⟩), 0, by omega, rfl⟩, ?_⟩
  rw [MvPolynomial.totalDegree_C]

theorem add {p q : MvPolynomial X F} {s d t : ℕ} (hp : CSize p s d) (hq : CSize q t d) :
    CSize (p + q) (s + t + 1) d :=
  ⟨hp.1.join hq.1 (Or.inl rfl), (MvPolynomial.totalDegree_add p q).trans (max_le hp.2 hq.2)⟩

theorem mul {p q : MvPolynomial X F} {s d t e : ℕ} (hp : CSize p s d) (hq : CSize q t e) :
    CSize (p * q) (s + t + 1) (d + e) :=
  ⟨hp.1.join hq.1 (Or.inr rfl), (MvPolynomial.totalDegree_mul p q).trans (add_le_add hp.2 hq.2)⟩

theorem sum {ι : Type*} (A : Finset ι) {f : ι → MvPolynomial X F} {s d : ℕ} (h : ∀ i ∈ A, CSize (f i) s d) :
    CSize (∑ i ∈ A, f i) (A.card * (s + 1) + 1) d := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    have := (const (X := X) (0 : F)).mono (s' := 1) (d' := d) le_rfl (Nat.zero_le _)
    rw [map_zero] at this
    simpa using this
  | insert i A hi ih =>
    rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
    refine ((h i (Finset.mem_insert_self i A)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))).mono ?_ le_rfl
    ring_nf
    omega

theorem prod {ι : Type*} (A : Finset ι) {f : ι → MvPolynomial X F} {s d : ℕ} (h : ∀ i ∈ A, CSize (f i) s d) :
    CSize (∏ i ∈ A, f i) (A.card * (s + 1) + 1) (A.card * d) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    have := const (X := X) (1 : F)
    rw [map_one] at this
    simpa using this
  | insert i A hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    refine ((h i (Finset.mem_insert_self i A)).mul
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))).mono ?_ ?_
    · ring_nf
      omega
    · ring_nf
      omega

end CSize

end

section
variable {X : Type*}
theorem bits_add {m : ℕ} (p q : MvPolynomial (X ⊕ Fin m) F) (e : Fin m → Bool) :
    bits (p + q) e = bits p e + bits q e := map_add _ _ _

theorem bits_mul {m : ℕ} (p q : MvPolynomial (X ⊕ Fin m) F) (e : Fin m → Bool) :
    bits (p * q) e = bits p e * bits q e := map_mul _ _ _

theorem bits_sum {m : ℕ} {ι : Type*} (A : Finset ι) (f : ι → MvPolynomial (X ⊕ Fin m) F) (e : Fin m → Bool) :
    bits (∑ i ∈ A, f i) e = ∑ i ∈ A, bits (f i) e := map_sum _ _ _

theorem bits_prod {m : ℕ} {ι : Type*} (A : Finset ι) (f : ι → MvPolynomial (X ⊕ Fin m) F) (e : Fin m → Bool) :
    bits (∏ i ∈ A, f i) e = ∏ i ∈ A, bits (f i) e := map_prod _ _ _

theorem bits_C {m : ℕ} (a : F) (e : Fin m → Bool) :
    bits (MvPolynomial.C a : MvPolynomial (X ⊕ Fin m) F) e = MvPolynomial.C a := by
  rw [bits, MvPolynomial.aeval_C]
  rfl

theorem bits_inl {m : ℕ} (x : X) (e : Fin m → Bool) :
    bits (MvPolynomial.X (Sum.inl x) : MvPolynomial (X ⊕ Fin m) F) e = MvPolynomial.X x := by
  simp [bits]

theorem bits_inr {m : ℕ} (i : Fin m) (e : Fin m → Bool) :
    bits (MvPolynomial.X (Sum.inr i) : MvPolynomial (X ⊕ Fin m) F) e = if e i then 1 else 0 := by
  simp [bits]

end

namespace Hc

variable {k : ℕ}

/-- The cycle that visits the vertices in the order π. -/
def cycleOf (π : Equiv.Perm (Fin (k + 1))) : Equiv.Perm (Fin (k + 1)) := π * finRotate (k + 1) * π⁻¹

theorem cycleOf_apply (π : Equiv.Perm (Fin (k + 1))) (i : Fin (k + 1)) :
    cycleOf π (π i) = π (finRotate (k + 1) i) := by
  simp [cycleOf]

theorem cycleOf_pow (π : Equiv.Perm (Fin (k + 1))) {i : ℕ} (hi : i < k + 1) :
    (cycleOf π ^ i) (π 0) = π ⟨i, hi⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega), cycleOf_apply, finRotate_apply]
    congr 1
    ext
    rw [Fin.val_add_one_of_lt (by simp [Fin.lt_def]; omega)]

theorem cycleOf_isCycleOn (π : Equiv.Perm (Fin (k + 1))) : (cycleOf π).IsCycleOn Set.univ := by
  refine ⟨Set.bijOn_univ.2 (Equiv.bijective _), fun u _ v _ => ?_⟩
  have key : ∀ v, (cycleOf π).SameCycle (π 0) v := by
    intro v
    obtain ⟨i, rfl⟩ := π.surjective v
    exact ⟨(i : ℕ), by rw [zpow_natCast, cycleOf_pow π i.2]⟩
  exact (key u).symm.trans (key v)

/-- Every cycle through all vertices visits them in exactly one
order that begins with the first vertex. -/
theorem sum_cycles_eq_sum_orders {R : Type*} [CommSemiring R]
    (M : Fin (k + 1) → Fin (k + 1) → R) :
    hcSum M = ∑ π : Equiv.Perm (Fin (k + 1)) with π 0 = 0, ∏ i, M (π i) (π (finRotate (k + 1) i)) := by
  classical
  unfold hcSum
  symm
  refine Finset.sum_bij (fun π _ => cycleOf π) (fun π _ => mem_filter.2 ⟨mem_univ _, cycleOf_isCycleOn π⟩) ?_ ?_ ?_
  · intro π hπ π' hπ' e
    refine Equiv.ext fun i => ?_
    have h := cycleOf_pow π i.2
    have h' := cycleOf_pow π' i.2
    rw [(mem_filter.1 hπ).2] at h
    rw [(mem_filter.1 hπ').2, ← e, h] at h'
    exact h'
  · intro σ hσ
    have hc : σ.IsCycleOn (↑(Finset.univ : Finset (Fin (k + 1))) : Set (Fin (k + 1))) := by
      rw [Finset.coe_univ]
      exact (mem_filter.1 hσ).2
    have hsur : Function.Surjective fun i : Fin (k + 1) => (σ ^ (i : ℕ)) 0 := by
      intro v
      obtain ⟨i, hi, e⟩ := hc.exists_pow_eq (mem_univ (0 : Fin (k + 1))) (mem_univ v)
      rw [Finset.card_univ, Fintype.card_fin] at hi
      exact ⟨⟨i, hi⟩, e⟩
    let π := Equiv.ofBijective _ (Finite.surjective_iff_bijective.1 hsur)
    refine ⟨π, mem_filter.2 ⟨mem_univ _, rfl⟩, Equiv.ext fun v => ?_⟩
    obtain ⟨i, rfl⟩ := π.surjective v
    rw [cycleOf_apply]
    change (σ ^ (finRotate (k + 1) i : ℕ)) 0 = σ ((σ ^ (i : ℕ)) 0)
    rw [← Equiv.Perm.mul_apply, ← pow_succ', finRotate_apply, Fin.val_add_one]
    split_ifs with h
    · rw [h, Fin.val_last]
      have := hc.pow_card_apply (mem_univ (0 : Fin (k + 1)))
      rw [Finset.card_univ, Fintype.card_fin] at this
      rw [this, pow_zero]
      rfl
    · rfl
  · intro π _
    rw [← Equiv.prod_comp π (fun u => M u (cycleOf π u))]
    exact Finset.prod_congr rfl fun i _ => by rw [cycleOf_apply]

variable (F : Type*) [Field F] (n : ℕ)

/-- The bit "position i holds vertex u". -/
noncomputable def pos (i u : Fin n) : MvPolynomial ((Fin n × Fin n) ⊕ Fin (n * n)) F :=
  MvPolynomial.X (Sum.inr (finProdFinEquiv (i, u)))

/-- The pairs of bits that exclude each other: two of one position or two of one vertex. -/
def clash : Finset ((Fin n × Fin n) × (Fin n × Fin n)) :=
  Finset.univ.filter fun p => p.1 ≠ p.2 ∧ (p.1.1 = p.2.1 ∨ p.1.2 = p.2.2)

/-- The test that the bits are a bijection between positions and vertices. -/
noncomputable def orderTest : MvPolynomial ((Fin n × Fin n) ⊕ Fin (n * n)) F :=
  (∏ p ∈ clash n, (C 1 + C (-1) * (pos F n p.1.1 p.1.2 * pos F n p.2.1 p.2.2))) * ∏ i, ∑ u, pos F n i u

/-- The edges between consecutive positions. -/
noncomputable def orderEdges : MvPolynomial ((Fin n × Fin n) ⊕ Fin (n * n)) F :=
  ∏ i, ∑ p : Fin n × Fin n, pos F n i p.1 * pos F n (finRotate n i) p.2 * MvPolynomial.X (Sum.inl p)

/-- The witness: the test, the first vertex at the first position, and the edges. -/
noncomputable def hcWit : MvPolynomial ((Fin n × Fin n) ⊕ Fin (n * n)) F :=
  if h : 0 < n then orderTest F n * pos F n ⟨0, h⟩ ⟨0, h⟩ * orderEdges F n else C 1

/-- The table of bits of an order. -/
def orderBits (π : Equiv.Perm (Fin n)) : Fin (n * n) → Bool :=
  fun q => decide (π (finProdFinEquiv.symm q).1 = (finProdFinEquiv.symm q).2)

theorem orderBits_injective : Function.Injective (orderBits n) := by
  intro π π' e
  refine Equiv.ext fun i => ?_
  have := congrFun e (finProdFinEquiv (i, π i))
  simp only [orderBits, Equiv.symm_apply_apply, decide_true] at this
  exact (of_decide_eq_true this.symm).symm

theorem bits_pos_order (π : Equiv.Perm (Fin n)) (i u : Fin n) :
    bits (pos F n i u) (orderBits n π) = if π i = u then 1 else 0 := by
  simp [pos, bits_inr, orderBits]

theorem bits_orderTest_order (π : Equiv.Perm (Fin n)) : bits (orderTest F n) (orderBits n π) = 1 := by
  simp only [orderTest, bits_mul, bits_prod, bits_sum, bits_add, bits_C, bits_pos_order]
  rw [Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro i _
    simp
  · intro p hp
    obtain ⟨hne, h⟩ := (mem_filter.1 hp).2
    have : ¬ (π p.1.1 = p.1.2 ∧ π p.2.1 = p.2.2) := by
      rintro ⟨h1, h2⟩
      refine hne (Prod.ext ?_ ?_) <;> rcases h with e | e
      · exact e
      · exact π.injective (h1.trans (e.trans h2.symm))
      · exact h1.symm.trans ((congrArg π e).trans h2)
      · exact e
    split_ifs with h1 h2 <;> simp_all

/-- A table of bits passes the test only if it is the table of a bijection
between the positions and the vertices. -/
theorem exists_order_of_test_ne_zero (e : Fin (n * n) → Bool) (h : bits (orderTest F n) e ≠ 0) :
    ∃ π, orderBits n π = e := by
  simp only [orderTest, bits_mul, bits_prod, bits_sum, bits_add, bits_C, pos, bits_inr] at h
  have h1 : ∀ p ∈ clash n, ¬ (e (finProdFinEquiv p.1) = true ∧ e (finProdFinEquiv p.2) = true) := by
    rintro p hp ⟨a, b⟩
    refine h (mul_eq_zero_of_left (Finset.prod_eq_zero hp ?_) _)
    rw [if_pos a, if_pos b, mul_one, mul_one, ← map_add, add_neg_cancel, map_zero]
  have h2 : ∀ i, ∃ u, e (finProdFinEquiv (i, u)) = true := by
    intro i
    by_contra hc
    push Not at hc
    refine h (mul_eq_zero_of_right _ (Finset.prod_eq_zero (mem_univ i) (Finset.sum_eq_zero fun u _ => ?_)))
    exact if_neg (hc u)
  choose f hf using h2
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    exact h1 ((i, f i), (j, f j)) (mem_filter.2 ⟨mem_univ _, fun q => hne (Prod.mk.inj q).1, Or.inr hij⟩) ⟨hf i, hf j⟩
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), funext fun q => ?_⟩
  obtain ⟨⟨i, u⟩, rfl⟩ := finProdFinEquiv.surjective q
  rw [Bool.eq_iff_iff]
  simp only [orderBits, Equiv.symm_apply_apply, decide_eq_true_iff, Equiv.ofBijective_apply]
  constructor
  · rintro rfl
    exact hf i
  · intro hu
    by_contra hne
    exact h1 ((i, f i), (i, u)) (mem_filter.2 ⟨mem_univ _, fun q => hne (Prod.mk.inj q).2, Or.inl rfl⟩) ⟨hf i, hu⟩

theorem bits_orderEdges_order (π : Equiv.Perm (Fin n)) :
    bits (orderEdges F n) (orderBits n π) = ∏ i, MvPolynomial.X (π i, π (finRotate n i)) := by
  simp only [orderEdges, bits_prod, bits_sum, bits_mul, bits_pos_order, bits_inl]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (π i, π (finRotate n i))]
  · simp
  · intro p _ hp
    by_cases h1 : π i = p.1
    · rw [if_pos h1, if_neg (fun h2 => hp (Prod.ext h1.symm h2.symm)), one_mul, zero_mul]
    · rw [if_neg h1, zero_mul, zero_mul]
  · exact fun h => absurd (mem_univ _) h

/-- The Hamiltonian cycle polynomial is the sum of the witness over all tables of
bits. -/
theorem genHC_eq_sum_wit : hc F n = ∑ e : Fin (n * n) → Bool, bits (hcWit F n) e := by
  classical
  rcases n with _ | k
  · have : IsEmpty (Fin (0 * 0)) := ⟨fun i => absurd i.isLt (by simp)⟩
    have : Unique (Fin (0 * 0) → Bool) := Pi.uniqueOfIsEmpty _
    rw [Fintype.sum_unique, hcWit, dif_neg (lt_irrefl 0), bits_C, C_1, hc,
      Finset.sum_eq_single_of_mem 1 (mem_filter.2 ⟨mem_univ _, Set.bijOn_univ.2 (Equiv.bijective _),
        fun i => i.elim0⟩) fun σ _ hne => absurd (Equiv.ext fun i => i.elim0) hne]
    simp
  · have hsum : ∀ g : MvPolynomial ((Fin (k + 1) × Fin (k + 1)) ⊕ Fin ((k + 1) * (k + 1))) F,
        ∑ e, bits (orderTest F (k + 1) * g) e = ∑ π, bits g (orderBits (k + 1) π) := by
      intro g
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (orderBits (k + 1))))]
      · rw [Finset.sum_image (orderBits_injective (k + 1)).injOn]
        exact Finset.sum_congr rfl fun π _ => by rw [bits_mul, bits_orderTest_order, one_mul]
      · intro e _ he
        rw [bits_mul, mul_eq_zero_of_left]
        by_contra h
        obtain ⟨π, hπ⟩ := exists_order_of_test_ne_zero F (k + 1) e h
        exact he (mem_image.2 ⟨π, mem_univ _, hπ⟩)
    rw [hcWit, dif_pos k.succ_pos]
    simp only [mul_assoc]
    rw [hsum]
    simp only [bits_mul, bits_pos_order, bits_orderEdges_order, ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter]
    refine Eq.trans ?_ (sum_cycles_eq_sum_orders fun a b => (MvPolynomial.X (a, b) : MvPolynomial _ F))
    unfold hc hcSum
    rfl

theorem csize_pos (i u : Fin n) : CSize (pos F n i u) 1 1 := CSize.var _

/-- The witness has polynomial size and degree. -/
theorem csize_hcWit : CSize (hcWit F n) (40 * (n + 1) ^ 4) (40 * (n + 1) ^ 4) := by
  unfold hcWit
  split_ifs with h
  · have hclash : (clash n).card ≤ n ^ 4 := by
      refine (Finset.card_le_univ _).trans (le_of_eq ?_)
      simp only [Fintype.card_prod, Fintype.card_fin]
      ring
    have h1 := CSize.prod (clash n) (f := fun p => C 1 + C (-1) * (pos F n p.1.1 p.1.2 * pos F n p.2.1 p.2.2))
      (s := 7) (d := 2) fun p _ =>
        ((CSize.const 1).mono (s' := 1) (d' := 2) le_rfl (by norm_num)).add
          (((CSize.const (-1)).mul ((csize_pos F n _ _).mul (csize_pos F n _ _))).mono (s' := 5) le_rfl le_rfl)
    have h2 := CSize.prod Finset.univ (f := fun i => ∑ u, pos F n i u) fun i _ =>
      CSize.sum Finset.univ fun u _ => csize_pos F n i u
    have h3 := CSize.prod Finset.univ
      (f := fun i => ∑ p : Fin n × Fin n, pos F n i p.1 * pos F n (finRotate n i) p.2 * MvPolynomial.X (Sum.inl p))
      fun i _ => CSize.sum Finset.univ fun p _ =>
        ((csize_pos F n i p.1).mul (csize_pos F n (finRotate n i) p.2)).mul (CSize.var (Sum.inl p))
    refine (((h1.mul h2).mul (csize_pos F n _ _)).mul h3).mono ?_ ?_
    all_goals
      simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
      nlinarith [hclash, Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 2)]
  · exact (CSize.const 1).mono (by nlinarith [Nat.one_le_pow 4 (n + 1) n.succ_pos]) (Nat.zero_le _)

/-- A polynomial bound in the form of the definition of VP. -/
theorem quartic_bound {C : ℕ} (hC : 700 ≤ C) : 40 * (n + 1) ^ 4 ≤ n ^ C + C := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> exact le_trans (le_trans (by norm_num) hC) (Nat.le_add_left C _)
  · have h3 : n + 1 ≤ n ^ 2 := by nlinarith
    calc 40 * (n + 1) ^ 4 ≤ 2 ^ 6 * (n ^ 2) ^ 4 := Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left h3 4)
      _ ≤ n ^ 6 * (n ^ 2) ^ 4 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h 6)
      _ = n ^ 14 := by rw [← pow_mul, ← pow_add]
      _ ≤ n ^ C := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ _ := Nat.le_add_right _ _

end Hc

end Statement

open Statement
universe u


theorem solution (F : Type u) [Field F] :
    ({ vars := fun n => Fin n × Fin n, poly := hc F } : Statement.Family F) ∈ VNP F := by
  refine ⟨fun n => n * n, Hc.hcWit F, ⟨700, fun n => ?_⟩, Hc.genHC_eq_sum_wit F⟩
  have hb := Hc.quartic_bound n (C := 700) le_rfl
  obtain ⟨h1, h2⟩ := Hc.csize_hcWit F n
  refine ⟨le_trans ?_ hb, h2.trans hb, h1.mono hb⟩
  show Fintype.card ((Fin n × Fin n) ⊕ Fin (n * n)) ≤ _
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  nlinarith [Nat.zero_le (n ^ 4), Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 2)]

