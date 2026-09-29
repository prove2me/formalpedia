-- Prove2me | solution 1 for Valued.exists_forall_v_sub_eq_one_and_v_det_eq_one_of_v_sub_sum_div_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/2efa98f2-e966-531f-a0a2-9bc33b6b9a3c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Valued_exists_forall_v_sub_eq_one_and_v_det_eq_one_of_v_sub_sum_div_lt_one

set_option autoImplicit false

open Polynomial

namespace Valued
p2m_export "Valued" "mk v integer"
namespace GenericUnimodular
p2m_open "Valued"

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "𝓋" => (Valued.v : Valuation K Γ₀)

lemma v_natCast_le_one (n : ℕ) : 𝓋 (n : K) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    exact (Valuation.map_add _ _ _).trans (max_le ih (by simp))

lemma v_intCast_le_one (n : ℤ) : 𝓋 (n : K) ≤ 1 := by
  cases n with
  | ofNat n => simpa using v_natCast_le_one (K := K) n
  | negSucc n =>
    rw [Int.cast_negSucc, Valuation.map_neg]
    exact_mod_cast v_natCast_le_one (K := K) (n + 1)

lemma v_sub_le_one {x y : K} (hx : 𝓋 x ≤ 1) (hy : 𝓋 y ≤ 1) : 𝓋 (x - y) ≤ 1 :=
  (Valuation.map_sub _ x y).trans (max_le hx hy)

lemma v_sub_eq_of_lt {x y : K} (h : 𝓋 x < 𝓋 y) : 𝓋 (x - y) = 𝓋 y := by
  rw [Valuation.map_sub_swap, sub_eq_add_neg]
  exact Valuation.map_add_eq_of_lt_left _ (by simpa using h)

lemma ne_zero_of_v_eq_one {x : K} (h : 𝓋 x = 1) : x ≠ 0 := by
  rintro rfl; simp at h

lemma exists_forall_v_sub_eq_one [IsAlgClosed K] (F : Finset K) (hF : ∀ f ∈ F, 𝓋 f ≤ 1) :
    ∃ x : K, 𝓋 x ≤ 1 ∧ ∀ f ∈ F, 𝓋 (x - f) = 1 := by
  classical

  set F' : Finset K := insert 0 F with hF'def
  have hF' : ∀ f ∈ F', 𝓋 f ≤ 1 := by
    intro f hf
    rcases Finset.mem_insert.1 hf with rfl | hf
    · simp
    · exact hF f hf
  have h0 : (0 : K) ∈ F' := Finset.mem_insert_self _ _

  set q : K[X] := (∏ f ∈ F', (X - C f)) - C 1 with hqdef
  have hdegprod : (∏ f ∈ F', (X - C f)).natDegree = F'.card := by
    rw [natDegree_prod_of_monic _ _ (fun f _ => monic_X_sub_C f)]
    simp
  have hcard : 0 < F'.card := Finset.card_pos.2 ⟨0, h0⟩
  have hqdeg : q.natDegree = F'.card := by
    rw [hqdef, natDegree_sub_C, hdegprod]
  have hq0 : q ≠ 0 := ne_zero_of_natDegree_gt (n := 0) (by omega)
  have hqdeg' : q.degree ≠ 0 := by
    rw [degree_eq_natDegree hq0]
    exact_mod_cast (by omega : q.natDegree ≠ 0)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root q hqdeg'
  have hprod : ∏ f ∈ F', (x - f) = 1 := by
    have h := hx
    rw [IsRoot, hqdef, eval_sub, eval_C, eval_prod] at h
    simp only [eval_sub, eval_X, eval_C] at h
    exact sub_eq_zero.1 h
  have hvprod : ∏ f ∈ F', 𝓋 (x - f) = 1 := by
    rw [← map_prod 𝓋, hprod, map_one]

  have hxint : 𝓋 x ≤ 1 := by
    by_contra hx1
    push_neg at hx1
    have hge : ∀ f ∈ F', 1 ≤ 𝓋 (x - f) := by
      intro f hf
      have : 𝓋 (x - f) = 𝓋 x := by
        rw [sub_eq_add_neg]
        exact Valuation.map_add_eq_of_lt_left _ (by simpa using (hF' f hf).trans_lt hx1)
      rw [this]; exact hx1.le
    have h1 : 𝓋 (x - 0) * ∏ f ∈ F'.erase 0, 𝓋 (x - f) = 1 := by
      rw [Finset.mul_prod_erase _ (fun f => 𝓋 (x - f)) h0, hvprod]
    have h2 : 1 ≤ ∏ f ∈ F'.erase 0, 𝓋 (x - f) :=
      Finset.one_le_prod' (fun f hf => hge f (Finset.mem_of_mem_erase hf))
    have h3 : 𝓋 x ≤ 1 := by
      calc 𝓋 x = 𝓋 (x - 0) * 1 := by simp
        _ ≤ 𝓋 (x - 0) * ∏ f ∈ F'.erase 0, 𝓋 (x - f) := mul_le_mul_right h2 _
        _ = 1 := h1
    exact absurd h3 (not_le.2 hx1)
  have hle : ∀ f ∈ F', 𝓋 (x - f) ≤ 1 := fun f hf => v_sub_le_one hxint (hF' f hf)
  have hall := (Finset.prod_eq_one_iff_of_le_one' hle).1 hvprod
  exact ⟨x, hxint, fun f hf => hall f (Finset.mem_insert_of_mem hf)⟩

lemma exists_forall_one_le_v_sub [IsAlgClosed K] (F : Finset K) :
    ∃ x : K, 𝓋 x ≤ 1 ∧ (∀ f ∈ F, 𝓋 f ≤ 1 → 𝓋 (x - f) = 1) ∧ ∀ f ∈ F, 1 ≤ 𝓋 (x - f) := by
  classical
  obtain ⟨x, hx, hxf⟩ := exists_forall_v_sub_eq_one (F.filter fun f => 𝓋 f ≤ 1)
    (fun f hf => (Finset.mem_filter.1 hf).2)
  refine ⟨x, hx, fun f hf hf1 => hxf f (Finset.mem_filter.2 ⟨hf, hf1⟩), fun f hf => ?_⟩
  by_cases hf1 : 𝓋 f ≤ 1
  · exact (hxf f (Finset.mem_filter.2 ⟨hf, hf1⟩)).ge
  · push_neg at hf1
    rw [v_sub_eq_of_lt (hx.trans_lt hf1)]
    exact hf1.le

section det

variable {n : Type} [Fintype n] [DecidableEq n]

def resIdeal : Ideal (𝓋).integer where
  carrier := {x | 𝓋 (x : K) < 1}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Subring.coe_add] at *
    exact Valuation.map_add_lt _ ha hb
  zero_mem' := by simp
  smul_mem' c {x} hx := by
    simp only [Set.mem_setOf_eq, smul_eq_mul, Subring.coe_mul, Valuation.map_mul] at *
    have hc : 𝓋 (c : K) ≤ 1 := (Valuation.mem_integer_iff _ _).1 c.2
    calc 𝓋 (c : K) * 𝓋 (x : K) ≤ 1 * 𝓋 (x : K) := mul_le_mul_left hc _
      _ = 𝓋 (x : K) := one_mul _
      _ < 1 := hx

def liftMat (M : Matrix n n K) (hM : ∀ i j, 𝓋 (M i j) ≤ 1) : Matrix n n (𝓋).integer :=
  Matrix.of fun i j => ⟨M i j, (Valuation.mem_integer_iff _ _).2 (hM i j)⟩

lemma subtype_mapMatrix_liftMat (M : Matrix n n K) (hM : ∀ i j, 𝓋 (M i j) ≤ 1) :
    ((𝓋).integer.subtype).mapMatrix (liftMat M hM) = M := by
  ext i j; rfl

lemma det_eq_coe_det_liftMat (M : Matrix n n K) (hM : ∀ i j, 𝓋 (M i j) ≤ 1) :
    M.det = ((liftMat M hM).det : K) := by
  have h := RingHom.map_det ((𝓋).integer.subtype) (liftMat M hM)
  rw [subtype_mapMatrix_liftMat] at h
  exact h.symm

lemma v_det_le_one (M : Matrix n n K) (hM : ∀ i j, 𝓋 (M i j) ≤ 1) : 𝓋 M.det ≤ 1 := by
  rw [det_eq_coe_det_liftMat M hM]
  exact (Valuation.mem_integer_iff _ _).1 (liftMat M hM).det.2

lemma v_det_sub_det_lt_one (M N : Matrix n n K) (hN : ∀ i j, 𝓋 (N i j) ≤ 1)
    (h : ∀ i j, 𝓋 (M i j - N i j) < 1) : 𝓋 (M.det - N.det) < 1 := by
  have hM : ∀ i j, 𝓋 (M i j) ≤ 1 := by
    intro i j
    have : M i j = N i j + (M i j - N i j) := by ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le (hN i j) (h i j).le)
  set π := Ideal.Quotient.mk (resIdeal (K := K)) with hπ
  have hent : π.mapMatrix (liftMat M hM) = π.mapMatrix (liftMat N hN) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    exact (Ideal.Quotient.eq).2 (h i j)
  have hdet : π (liftMat M hM).det = π (liftMat N hN).det := by
    rw [RingHom.map_det, RingHom.map_det, hent]
  have hmem := (Ideal.Quotient.eq).1 hdet
  rw [det_eq_coe_det_liftMat M hM, det_eq_coe_det_liftMat N hN]
  exact hmem

lemma v_det_eq_one_of_forall_v_sub_lt_one (M N : Matrix n n K) (hN : ∀ i j, 𝓋 (N i j) ≤ 1)
    (hNdet : 𝓋 N.det = 1) (h : ∀ i j, 𝓋 (M i j - N i j) < 1) : 𝓋 M.det = 1 := by
  have hlt := v_det_sub_det_lt_one M N hN h
  have : M.det = N.det + (M.det - N.det) := by ring
  rw [this, Valuation.map_add_eq_of_lt_left _ (by rwa [hNdet]), hNdet]

end det

section cleared

variable {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ}

def L (t : ι → K) (a : ι) (x : K) : K := ∏ a' ∈ Finset.univ.erase a, (x - t a')

def N (t : ι → K) (m : Fin r → Fin r → ι → ℤ) (b : Fin r → K) : Matrix (Fin r) (Fin r) K :=
  Matrix.of fun i j => ∑ a, (m i j a : K) * L t a (b i)

lemma L_apply_ne (t : ι → K) {a a' : ι} (h : a ≠ a') : L t a (t a') = 0 := by
  unfold L
  exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨h.symm, Finset.mem_univ _⟩) (sub_self _)

lemma v_L_le_one (t : ι → K) (ht : ∀ a, 𝓋 (t a) ≤ 1) (a : ι) {x : K} (hx : 𝓋 x ≤ 1) :
    𝓋 (L t a x) ≤ 1 := by
  unfold L
  rw [map_prod 𝓋]
  exact Finset.prod_le_one' (fun a' _ => v_sub_le_one hx (ht a'))

lemma v_L_apply_self (t : ι → K) (ht : ∀ a, 𝓋 (t a) ≤ 1)
    (htsep : ∀ a a' : ι, a ≠ a' → 1 ≤ 𝓋 (t a - t a')) (a : ι) : 𝓋 (L t a (t a)) = 1 := by
  unfold L
  rw [map_prod 𝓋]
  refine Finset.prod_eq_one (fun a' ha' => ?_)
  have hne : a ≠ a' := fun h => (Finset.mem_erase.1 ha').1 h.symm
  exact le_antisymm (v_sub_le_one (ht a) (ht a')) (htsep a a' hne)

lemma L_mul_sub (t : ι → K) (a : ι) (x : K) : L t a x * (x - t a) = ∏ a', (x - t a') := by
  unfold L
  exact Finset.prod_erase_mul _ (fun a' => x - t a') (Finset.mem_univ a)

lemma v_N_le_one (t : ι → K) (ht : ∀ a, 𝓋 (t a) ≤ 1) (m : Fin r → Fin r → ι → ℤ) {b : Fin r → K}
    (hb : ∀ i, 𝓋 (b i) ≤ 1) (i j : Fin r) : 𝓋 (N t m b i j) ≤ 1 := by
  unfold N
  simp only [Matrix.of_apply]
  refine Valuation.map_sum_le _ (fun a _ => ?_)
  rw [Valuation.map_mul]
  exact mul_le_one' (v_intCast_le_one _) (v_L_le_one t ht a (hb i))

lemma N_apply_poles (t : ι → K) (m : Fin r → Fin r → ι → ℤ) (a₀ : Fin r → ι) (i j : Fin r) :
    N t m (fun i => t (a₀ i)) i j = L t (a₀ i) (t (a₀ i)) * (m i j (a₀ i) : K) := by
  unfold N
  simp only [Matrix.of_apply]
  rw [Finset.sum_eq_single (a₀ i)]
  · ring
  · intro a _ ha
    rw [L_apply_ne t ha, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma v_det_N_poles (t : ι → K) (ht : ∀ a, 𝓋 (t a) ≤ 1)
    (htsep : ∀ a a' : ι, a ≠ a' → 1 ≤ 𝓋 (t a - t a')) (m : Fin r → Fin r → ι → ℤ) (a₀ : Fin r → ι)
    (hdet : 𝓋 (Matrix.of (fun i j : Fin r => ((m i j (a₀ i) : ℤ) : K))).det = 1) :
    𝓋 (N t m (fun i => t (a₀ i))).det = 1 := by
  have hN : N t m (fun i => t (a₀ i)) =
      Matrix.of (fun i j => L t (a₀ i) (t (a₀ i)) * (Matrix.of (fun i j : Fin r => ((m i j (a₀ i) : ℤ) : K))) i j) := by
    ext i j
    rw [N_apply_poles]
    simp
  rw [hN, Matrix.det_mul_column, Valuation.map_mul, map_prod 𝓋, hdet, mul_one]
  exact Finset.prod_eq_one (fun i _ => v_L_apply_self t ht htsep (a₀ i))

lemma partialFraction_eq (t : ι → K) (m : Fin r → Fin r → ι → ℤ) {b : Fin r → K}
    (hb : ∀ i a, b i - t a ≠ 0) (i j : Fin r) :
    ∑ a, (m i j a : K) / (b i - t a) = (∏ a, (b i - t a))⁻¹ * N t m b i j := by
  unfold N
  simp only [Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hP : (∏ a', (b i - t a')) ≠ 0 := Finset.prod_ne_zero_iff.2 (fun a' _ => hb i a')
  have hL := L_mul_sub t a (b i)
  have hbt : b i - t a ≠ 0 := hb i a
  have hLne : L t a (b i) ≠ 0 := fun h0 => hP (by rw [← hL, h0, zero_mul])
  rw [← hL, mul_inv, div_eq_mul_inv]
  calc (m i j a : K) * (b i - t a)⁻¹ = (m i j a : K) * (b i - t a)⁻¹ * ((L t a (b i))⁻¹ * L t a (b i)) := by
        rw [inv_mul_cancel₀ hLne, mul_one]
    _ = (L t a (b i))⁻¹ * (b i - t a)⁻¹ * ((m i j a : K) * L t a (b i)) := by ring

lemma v_det_partialFraction (t : ι → K) (m : Fin r → Fin r → ι → ℤ) {b : Fin r → K}
    (hb : ∀ i a, 𝓋 (b i - t a) = 1) :
    𝓋 (Matrix.of (fun i j : Fin r => ∑ a, (m i j a : K) / (b i - t a))).det = 𝓋 (N t m b).det := by
  have hb0 : ∀ i a, b i - t a ≠ 0 := fun i a => ne_zero_of_v_eq_one (hb i a)
  have hM : Matrix.of (fun i j : Fin r => ∑ a, (m i j a : K) / (b i - t a)) =
      Matrix.of (fun i j => (∏ a, (b i - t a))⁻¹ * N t m b i j) := by
    ext i j
    simp only [Matrix.of_apply]
    exact partialFraction_eq t m hb0 i j
  rw [hM, Matrix.det_mul_column, Valuation.map_mul, map_prod 𝓋]
  have : ∏ i : Fin r, 𝓋 ((∏ a, (b i - t a))⁻¹) = 1 := by
    refine Finset.prod_eq_one (fun i _ => ?_)
    rw [Valuation.map_inv, map_prod 𝓋, Finset.prod_eq_one (fun a _ => hb i a), inv_one]
  rw [this, one_mul]

noncomputable def Q (t : ι → K) (m : Fin r → Fin r → ι → ℤ) (b : Fin r → K) (i : Fin r) : Matrix (Fin r) (Fin r) K[X] :=
  Matrix.of fun k j => if k = i then ∑ a, (C (m i j a : K)) * ∏ a' ∈ Finset.univ.erase a, (X - C (t a'))
    else C (N t m b k j)

lemma eval_mapMatrix_Q (t : ι → K) (m : Fin r → Fin r → ι → ℤ) (b : Fin r → K) (i : Fin r) (x : K) :
    (evalRingHom x).mapMatrix (Q t m b i) = N t m (Function.update b i x) := by
  ext k j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Q, Matrix.of_apply]
  by_cases hk : k = i
  · subst hk
    simp only [if_true, coe_evalRingHom, eval_finset_sum, eval_mul, eval_C, eval_prod, eval_sub, eval_X, N,
      Matrix.of_apply, Function.update_self, L]
  · simp only [hk, if_false, coe_evalRingHom, eval_C, N, Matrix.of_apply, Function.update_of_ne hk]

lemma det_N_update_eq_eval (t : ι → K) (m : Fin r → Fin r → ι → ℤ) (b : Fin r → K) (i : Fin r) (x : K) :
    (N t m (Function.update b i x)).det = eval x (Q t m b i).det := by
  rw [← coe_evalRingHom, RingHom.map_det, eval_mapMatrix_Q]

end cleared

lemma exists_v_eval_eq_one_avoiding [IsAlgClosed K] (p : K[X]) (x₀ : K) (hx₀ : 𝓋 x₀ ≤ 1)
    (hp : 𝓋 (eval x₀ p) = 1) (hint : ∀ x, 𝓋 x ≤ 1 → 𝓋 (eval x p) ≤ 1) (F : Finset K) :
    ∃ x : K, 𝓋 x ≤ 1 ∧ (∀ f ∈ F, 1 ≤ 𝓋 (x - f)) ∧ 𝓋 (eval x p) = 1 := by
  classical
  have hp0 : p ≠ 0 := by
    rintro rfl; simp at hp

  have hsplit := (IsAlgClosed.splits p).eq_prod_roots
  have heval : ∀ x : K, eval x p = p.leadingCoeff * (p.roots.map fun α => x - α).prod := by
    intro x
    conv_lhs => rw [hsplit]
    rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    congr 1
    refine congr_arg _ (Multiset.map_congr rfl (fun α _ => ?_))
    simp
  have hveval : ∀ x : K, 𝓋 (eval x p) = 𝓋 p.leadingCoeff * (p.roots.map fun α => 𝓋 (x - α)).prod := by
    intro x
    rw [heval, Valuation.map_mul, map_multiset_prod 𝓋, Multiset.map_map]
    rfl

  obtain ⟨x, hx, hx1, hxF⟩ := exists_forall_one_le_v_sub (K := K) (F ∪ p.roots.toFinset)
  refine ⟨x, hx, fun f hf => hxF f (Finset.mem_union_left _ hf), ?_⟩
  refine le_antisymm (hint x hx) ?_
  rw [← hp, hveval, hveval]
  refine mul_le_mul_right (Multiset.prod_map_le_prod_map _ _ (fun α hα => ?_)) _
  have hαF : α ∈ F ∪ p.roots.toFinset := Finset.mem_union_right _ (Multiset.mem_toFinset.2 hα)
  by_cases hα1 : 𝓋 α ≤ 1
  · rw [hx1 α hαF hα1]
    exact v_sub_le_one hx₀ hα1
  · push_neg at hα1
    rw [v_sub_eq_of_lt (hx₀.trans_lt hα1), v_sub_eq_of_lt (hx.trans_lt hα1)]

lemma exists_points [IsAlgClosed K] {ι : Type} [Fintype ι] [DecidableEq ι] (t : ι → K)
    (ht : ∀ a, 𝓋 (t a) ≤ 1) (htsep : ∀ a a' : ι, a ≠ a' → 1 ≤ 𝓋 (t a - t a'))
    {r : ℕ} (m : Fin r → Fin r → ι → ℤ) (a₀ : Fin r → ι)
    (hdet : 𝓋 (Matrix.of (fun i j : Fin r => ((m i j (a₀ i) : ℤ) : K))).det = 1)
    (S : Fin r → Finset K) (A : Finset (Fin r)) :
    ∃ b : Fin r → K, (∀ i, 𝓋 (b i) ≤ 1) ∧ 𝓋 (N t m b).det = 1 ∧
      ∀ i ∈ A, (∀ a, 1 ≤ 𝓋 (b i - t a)) ∧ ∀ s ∈ S i, 1 ≤ 𝓋 (b i - s) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    exact ⟨fun i => t (a₀ i), fun i => ht (a₀ i), v_det_N_poles t ht htsep m a₀ hdet, fun i hi => absurd hi (by simp)⟩
  | insert i A hiA ih =>
    obtain ⟨b, hb, hbdet, hgood⟩ := ih

    set p : K[X] := (Q t m b i).det with hpdef
    have hp : 𝓋 (eval (b i) p) = 1 := by
      rw [hpdef, ← det_N_update_eq_eval, Function.update_eq_self]; exact hbdet
    have hint : ∀ x, 𝓋 x ≤ 1 → 𝓋 (eval x p) ≤ 1 := by
      intro x hx
      rw [hpdef, ← det_N_update_eq_eval]
      refine v_det_le_one _ (fun k j => v_N_le_one t ht m (fun k => ?_) k j)
      by_cases hk : k = i
      · subst hk; simpa using hx
      · rw [Function.update_of_ne hk]; exact hb k
    obtain ⟨x, hx, hxF, hxp⟩ :=
      exists_v_eval_eq_one_avoiding p (b i) (hb i) hp hint (Finset.univ.image t ∪ S i)
    refine ⟨Function.update b i x, fun k => ?_, ?_, fun k hk => ?_⟩
    · by_cases hk : k = i
      · subst hk; simpa using hx
      · rw [Function.update_of_ne hk]; exact hb k
    · rw [det_N_update_eq_eval, ← hpdef]; exact hxp
    · rcases Finset.mem_insert.1 hk with rfl | hk
      · refine ⟨fun a => ?_, fun s hs => ?_⟩
        · rw [Function.update_self]
          exact hxF _ (Finset.mem_union_left _ (Finset.mem_image_of_mem t (Finset.mem_univ a)))
        · rw [Function.update_self]
          exact hxF _ (Finset.mem_union_right _ hs)
      · have hki : k ≠ i := fun h => hiA (h ▸ hk)
        rw [Function.update_of_ne hki]
        exact hgood k hk

end Valued.GenericUnimodular

open Valued.GenericUnimodular in

theorem solution
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    {ι : Type} [Fintype ι] (t : ι → K)
    (ht : ∀ a : ι, Valued.v (t a) ≤ 1) (htsep : ∀ a a' : ι, a ≠ a' → 1 ≤ Valued.v (t a - t a'))
    {r : ℕ} (m : Fin r → Fin r → ι → ℤ) (a₀ : Fin r → ι)
    (hdet : Valued.v (Matrix.of (fun i j : Fin r => ((m i j (a₀ i) : ℤ) : K))).det = 1)
    (S : Fin r → Finset K) :
    ∃ b : Fin r → K,
      (∀ i, Valued.v (b i) ≤ 1) ∧
      (∀ i a, Valued.v (b i - t a) = 1) ∧
      (∀ i, ∀ s ∈ S i, 1 ≤ Valued.v (b i - s)) ∧
      ∀ d : Matrix (Fin r) (Fin r) K,
        (∀ i j, Valued.v (d i j - ∑ a, (m i j a : K) / (b i - t a)) < 1) →
        Valued.v d.det = 1 := by
  classical
  obtain ⟨b, hb, hbdet, hgood⟩ := exists_points t ht htsep m a₀ hdet S Finset.univ
  have hbt : ∀ i a, Valued.v (b i - t a) = 1 := fun i a =>
    le_antisymm (v_sub_le_one (hb i) (ht a)) ((hgood i (Finset.mem_univ i)).1 a)
  refine ⟨b, hb, hbt, fun i s hs => (hgood i (Finset.mem_univ i)).2 s hs, fun d hd => ?_⟩
  have hDint : ∀ i j, Valued.v (∑ a, (m i j a : K) / (b i - t a)) ≤ 1 := by
    intro i j
    refine Valuation.map_sum_le _ (fun a _ => ?_)
    rw [Valuation.map_div, hbt i a, div_one]
    exact v_intCast_le_one _
  have hDdet : Valued.v (Matrix.of (fun i j : Fin r => ∑ a, (m i j a : K) / (b i - t a))).det = 1 := by
    rw [v_det_partialFraction t m hbt]; exact hbdet
  exact v_det_eq_one_of_forall_v_sub_lt_one d _ (fun i j => by simpa using hDint i j) hDdet
    (fun i j => by simpa using hd i j)

end S_Valued_exists_forall_v_sub_eq_one_and_v_det_eq_one_of_v_sub_sum_div_lt_one
end P2MW
export P2MW.S_Valued_exists_forall_v_sub_eq_one_and_v_det_eq_one_of_v_sub_sum_div_lt_one (solution)
