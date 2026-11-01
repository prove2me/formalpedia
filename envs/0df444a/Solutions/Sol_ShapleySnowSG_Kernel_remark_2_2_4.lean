-- Prove2me | solution 1 for ShapleySnowSG.Kernel.remark_2_2_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T22:00:08.795675+00:00
-- url     : https://prove2.me/submissions/b4fcb220-090a-4747-b847-0dcd1e3f510d

import Mathlib
import Definitions.Def_ShapleySnowSG_Kernel_MatrixGame
import Theorems.Thm_MatousekLP_ZeroSum_minimax_equality

namespace SSKAux
open ShapleySnowSG.Kernel

lemma val_le {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) (x : ι → ℝ) (y : κ → ℝ)
    (w w' : ℝ) (hx : x ∈ stdSimplex ℝ ι) (hy : y ∈ stdSimplex ℝ κ)
    (h1 : ∀ j, w ≤ ∑ i, x i * A i j) (h2 : ∀ i, ∑ j, A i j * y j ≤ w') : w ≤ w' := by
  calc w = ∑ j, y j * w := by rw [← Finset.sum_mul, hy.2, one_mul]
    _ ≤ ∑ j, y j * ∑ i, x i * A i j :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h1 j) (hy.1 j)
    _ = ∑ i, x i * ∑ j, A i j * y j := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ i, x i * w' := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h2 i) (hx.1 i)
    _ = w' := by rw [← Finset.sum_mul, hx.2, one_mul]

lemma isMatVal_unique {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) (w w' : ℝ)
    (h : IsMatVal A w) (h' : IsMatVal A w') : w = w' := by
  obtain ⟨x, hx, y, hy, hxA, hAy⟩ := h
  obtain ⟨x', hx', y', hy', hxA', hAy'⟩ := h'
  exact le_antisymm (val_le A x y' w w' hx hy' hxA hAy') (val_le A x' y w' w hx' hy hxA' hAy)

lemma val_lip {ι κ : Type*} [Fintype ι] [Fintype κ] (A B : Matrix ι κ ℝ) (a b ε : ℝ)
    (hA : IsMatVal A a) (hB : IsMatVal B b) (h : ∀ i j, A i j ≤ B i j + ε) : a ≤ b + ε := by
  obtain ⟨x, hx, _, _, hxA, _⟩ := hA
  obtain ⟨_, _, y, hy, _, hBy⟩ := hB
  refine val_le A x y a (b + ε) hx hy hxA fun i => ?_
  calc ∑ j, A i j * y j ≤ ∑ j, (B i j + ε) * y j :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (h i j) (hy.1 j)
    _ = ∑ j, B i j * y j + ε := by
        simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hy.2, mul_one]
    _ ≤ b + ε := by linarith [hBy i]

lemma val_abs_le {ι κ : Type*} [Fintype ι] [Fintype κ] (A B : Matrix ι κ ℝ) (a b ε : ℝ)
    (hA : IsMatVal A a) (hB : IsMatVal B b) (h : ∀ i j, |A i j - B i j| ≤ ε) : |a - b| ≤ ε := by
  rw [abs_le]
  constructor
  · have := val_lip B A b a ε hB hA (fun i j => by have := h i j; rw [abs_le] at this; linarith)
    linarith
  · have := val_lip A B a b ε hA hB (fun i j => by have := h i j; rw [abs_le] at this; linarith)
    linarith

end SSKAux

open Matrix

namespace SSKAux
open ShapleySnowSG.Kernel

lemma exists_val_fin {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (M : Matrix (Fin m) (Fin n) ℝ) :
    ∃ w, IsMatVal M w := by
  obtain ⟨v, ⟨⟨x, hx, hxv⟩, _⟩, ⟨⟨y, hy, hyv⟩, _⟩⟩ := MatousekLP.ZeroSum.minimax_equality hm hn M
  refine ⟨v, x, hx, y, hy, fun j => ?_, fun i => ?_⟩
  · have hc : Continuous fun y' : Fin n → ℝ => MatousekLP.ZeroSum.payoff M x y' :=
      continuous_const.dotProduct (continuous_const.matrix_mulVec continuous_id)
    have hbdd := ((isCompact_stdSimplex ℝ (Fin n)).image hc).bddBelow
    have := csInf_le hbdd ⟨Pi.single j 1, single_mem_stdSimplex ℝ j, rfl⟩
    rw [← hxv]
    refine this.trans (le_of_eq ?_)
    simp only [MatousekLP.ZeroSum.payoff, mulVec_single_one, dotProduct, col_apply]
  · have hc : Continuous fun x' : Fin m → ℝ => MatousekLP.ZeroSum.payoff M x' y :=
      continuous_id.dotProduct continuous_const
    have hbdd := ((isCompact_stdSimplex ℝ (Fin m)).image hc).bddAbove
    have := le_csSup hbdd ⟨Pi.single i 1, single_mem_stdSimplex ℝ i, rfl⟩
    rw [← hyv]
    refine (le_of_eq ?_).trans this
    simp [MatousekLP.ZeroSum.payoff, Pi.single_apply, mulVec, dotProduct]

lemma exists_val {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (A : Matrix ι κ ℝ) : ∃ w, IsMatVal A w := by
  classical
  let e1 := Fintype.equivFin ι
  let e2 := Fintype.equivFin κ
  obtain ⟨w, x, hx, y, hy, h1, h2⟩ := exists_val_fin (Fintype.card_pos (α := ι))
    (Fintype.card_pos (α := κ)) (A.submatrix e1.symm e2.symm)
  refine ⟨w, x ∘ e1, ⟨fun i => hx.1 _, ?_⟩, y ∘ e2, ⟨fun j => hy.1 _, ?_⟩, fun j => ?_, fun i => ?_⟩
  · rw [← hx.2]; exact Equiv.sum_comp e1 x
  · rw [← hy.2]; exact Equiv.sum_comp e2 y
  · have := h1 (e2 j)
    rw [← Equiv.sum_comp e1] at this
    simpa using this
  · have := h2 (e1 i)
    rw [← Equiv.sum_comp e2] at this
    simpa using this

end SSKAux

namespace SSKAux
open ShapleySnowSG.Kernel

lemma sign_cancel (d a b σ : ℝ) (ha : 0 ≤ d * a) (hb : 0 ≤ -d * b) (hσa : 0 < σ * a)
    (hσb : 0 < σ * b) : d = 0 := by
  have hab : 0 < a * b := by
    have h3 : 0 < (σ * a) * (σ * b) := mul_pos hσa hσb
    have h4 : (σ * a) * (σ * b) = σ ^ 2 * (a * b) := by ring
    rw [h4] at h3
    exact pos_of_mul_pos_right h3 (sq_nonneg σ)
  have h5 : 0 ≤ (d * a) * (-d * b) := mul_nonneg ha hb
  have h6 : (d * a) * (-d * b) = -(d ^ 2 * (a * b)) := by ring
  rw [h6] at h5
  have h7 : d ^ 2 ≤ 0 := by
    by_contra h
    push Not at h
    linarith [mul_pos h hab]
  nlinarith [sq_nonneg d]

/-- Existence for entries of `B` all positive. -/
lemma exists_root_pos {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (A B : Matrix ι κ ℝ) (hB : ∀ i j, 0 < B i j) : ∃ w : ℝ, IsMatVal (A - w • B) 0 := by
  have hex : ∀ w : ℝ, ∃ u, IsMatVal (A - w • B) u := fun w => exists_val _
  choose φ hφ using hex
  set c := ∑ i, ∑ j, |A i j| with hc
  set Bm := ∑ i, ∑ j, |B i j| with hBm
  have hAle : ∀ i j, |A i j| ≤ c := fun i j =>
    (Finset.single_le_sum (f := fun j => |A i j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, |A i j|)
        (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i))
  have hBle : ∀ i j, |B i j| ≤ Bm := fun i j =>
    (Finset.single_le_sum (f := fun j => |B i j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, |B i j|)
        (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i))
  have hBm0 : 0 ≤ Bm := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  obtain ⟨⟨i1, j1⟩, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (ι × κ))
    (fun p => B p.1 p.2) Finset.univ_nonempty
  set β := B i1 j1 with hβ
  have hβ0 : 0 < β := hB i1 j1
  have hβle : ∀ i j, β ≤ B i j := fun i j => hmin ⟨i, j⟩ (Finset.mem_univ _)
  -- continuity of φ
  have hlip : ∀ w w', |φ w - φ w'| ≤ |w - w'| * Bm := by
    intro w w'
    refine val_abs_le _ _ _ _ _ (hφ w) (hφ w') fun i j => ?_
    have : (A - w • B) i j - (A - w' • B) i j = (w' - w) * B i j := by
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
    rw [this, abs_mul, abs_sub_comm]
    exact mul_le_mul_of_nonneg_left (hBle i j) (abs_nonneg _)
  have hcont : Continuous φ := by
    refine Metric.continuous_iff.mpr fun w ε hε => ⟨ε / (Bm + 1), by positivity, fun w' hw' => ?_⟩
    rw [Real.dist_eq] at hw' ⊢
    calc |φ w' - φ w| ≤ |w' - w| * Bm := hlip w' w
      _ ≤ ε / (Bm + 1) * Bm := mul_le_mul_of_nonneg_right hw'.le hBm0
      _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith
  -- upper bound: φ w ≤ c - w β for w ≥ 0
  have hup : ∀ w, 0 ≤ w → φ w ≤ c - w * β := by
    intro w hw
    obtain ⟨x, hx, _, _, h1, _⟩ := hφ w
    have := h1 j1
    have hsum : ∑ i, x i * (A - w • B) i j1 ≤ c - w * β := by
      have : ∀ i, x i * (A - w • B) i j1 ≤ x i * (c - w * β) := fun i => by
        refine mul_le_mul_of_nonneg_left ?_ (hx.1 i)
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
        have h1 := (le_abs_self (A i j1)).trans (hAle i j1)
        have h2 := mul_le_mul_of_nonneg_left (hβle i j1) hw
        linarith
      refine (Finset.sum_le_sum fun i _ => this i).trans (le_of_eq ?_)
      rw [← Finset.sum_mul, hx.2, one_mul]
    linarith
  have hlow : ∀ w, w ≤ 0 → -c - w * β ≤ φ w := by
    intro w hw
    obtain ⟨_, _, y, hy, _, h2⟩ := hφ w
    have := h2 i1
    have hsum : -c - w * β ≤ ∑ j, (A - w • B) i1 j * y j := by
      have : ∀ j, (-c - w * β) * y j ≤ (A - w • B) i1 j * y j := fun j => by
        refine mul_le_mul_of_nonneg_right ?_ (hy.1 j)
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
        have h1 := (neg_abs_le (A i1 j)).trans' (neg_le_neg (hAle i1 j))
        have h2 := mul_le_mul_of_nonpos_left (hβle i1 j) hw
        linarith
      refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun j _ => this j)
      rw [← Finset.mul_sum, hy.2, mul_one]
    linarith
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  set w1 := (c + 1) / β
  set w0 := -((c + 1) / β)
  have hw1 : 0 ≤ w1 := by positivity
  have hw0 : w0 ≤ 0 := by
    have : 0 ≤ (c + 1) / β := by positivity
    simp only [w0]; linarith
  have hφ1 : φ w1 < 0 := by
    have := hup w1 hw1
    have e : w1 * β = c + 1 := by simp only [w1]; field_simp
    linarith
  have hφ0 : 0 < φ w0 := by
    have := hlow w0 hw0
    have e : w0 * β = -(c + 1) := by simp only [w0]; field_simp
    linarith
  have hle : w0 ≤ w1 := by linarith
  obtain ⟨w, _, hw⟩ := intermediate_value_Icc' hle hcont.continuousOn ⟨hφ1.le, hφ0.le⟩
  exact ⟨w, by rw [← hw]; exact hφ w⟩

end SSKAux

open ShapleySnowSG.Kernel in
theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (A B : Matrix ι κ ℝ) (hB : (∀ i j, 0 < B i j) ∨ (∀ i j, B i j < 0)) :
    ∃! w : ℝ, IsMatVal (A - w • B) 0 := by
  obtain ⟨σ, hσ, hex⟩ : ∃ σ : ℝ, (∀ i j, 0 < σ * B i j) ∧ ∃ w : ℝ, IsMatVal (A - w • B) 0 := by
    rcases hB with h | h
    · exact ⟨1, fun i j => by simpa using h i j, SSKAux.exists_root_pos A B h⟩
    · obtain ⟨w, hw⟩ := SSKAux.exists_root_pos A (-B) (fun i j => by simpa using h i j)
      refine ⟨-1, fun i j => by simpa using h i j, -w, ?_⟩
      have : A - -w • B = A - w • -B := by rw [neg_smul, smul_neg]
      rw [this]; exact hw
  obtain ⟨w, hw⟩ := hex
  refine ⟨w, hw, fun w' hw' => ?_⟩
  obtain ⟨x, hx, y, hy, h1, h2⟩ := hw
  obtain ⟨x', hx', y', hy', h1', h2'⟩ := hw'
  -- x (A - wB) y' ≥ 0 and x (A - w'B) y' ≤ 0
  have hpos : ∀ u v : ι → ℝ, ∀ t : κ → ℝ, u ∈ stdSimplex ℝ ι → t ∈ stdSimplex ℝ κ →
      0 < σ * (u ⬝ᵥ (B *ᵥ t)) := by
    intro u _ t hu ht
    have hu1 : ∃ a, 0 < u a := by
      by_contra h; push Not at h
      have : ∑ a, u a = 0 := Finset.sum_eq_zero fun a _ => le_antisymm (h a) (hu.1 a)
      rw [hu.2] at this; exact one_ne_zero this
    have ht1 : ∃ b, 0 < t b := by
      by_contra h; push Not at h
      have : ∑ a, t a = 0 := Finset.sum_eq_zero fun a _ => le_antisymm (h a) (ht.1 a)
      rw [ht.2] at this; exact one_ne_zero this
    obtain ⟨a0, ha0⟩ := hu1
    obtain ⟨b0, hb0⟩ := ht1
    have : σ * (u ⬝ᵥ (B *ᵥ t)) = ∑ a, ∑ b, u a * t b * (σ * B a b) := by
      simp only [dotProduct, mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [this]
    refine Finset.sum_pos' (fun a _ => Finset.sum_nonneg fun b _ =>
      mul_nonneg (mul_nonneg (hu.1 a) (ht.1 b)) (hσ a b).le) ⟨a0, Finset.mem_univ _, ?_⟩
    exact Finset.sum_pos' (fun b _ => mul_nonneg (mul_nonneg (hu.1 a0) (ht.1 b)) (hσ a0 b).le)
      ⟨b0, Finset.mem_univ _, mul_pos (mul_pos ha0 hb0) (hσ a0 b0)⟩
  have key : ∀ (w w' : ℝ) (x : ι → ℝ) (y' : κ → ℝ), x ∈ stdSimplex ℝ ι → y' ∈ stdSimplex ℝ κ →
      (∀ j, 0 ≤ ∑ i, x i * (A - w • B) i j) → (∀ i, ∑ j, (A - w' • B) i j * y' j ≤ 0) →
      0 ≤ (w' - w) * (x ⬝ᵥ (B *ᵥ y')) := by
    intro w w' x y' hx hy' h1 h2
    have e1 : 0 ≤ x ⬝ᵥ ((A - w • B) *ᵥ y') := by
      rw [dotProduct_mulVec]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (h1 j) (hy'.1 j)
    have e2 : x ⬝ᵥ ((A - w' • B) *ᵥ y') ≤ 0 :=
      Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hx.1 i) (h2 i)
    have e3 : x ⬝ᵥ ((A - w • B) *ᵥ y') - x ⬝ᵥ ((A - w' • B) *ᵥ y') =
        (w' - w) * (x ⬝ᵥ (B *ᵥ y')) := by
      rw [← dotProduct_sub, ← sub_mulVec]
      have : A - w • B - (A - w' • B) = (w' - w) • B := by rw [sub_smul]; abel
      rw [this, smul_mulVec, dotProduct_smul, smul_eq_mul]
    linarith
  have k1 := key w w' x y' hx hy' h1 h2'
  have k2 := key w' w x' y hx' hy h1' h2
  have hd := SSKAux.sign_cancel (w' - w) _ _ σ k1 (by have : -(w' - w) = w - w' := by ring
                                                      rw [this]; exact k2)
    (hpos x x y' hx hy') (hpos x' x' y hx' hy)
  linarith
