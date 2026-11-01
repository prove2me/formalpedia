-- Prove2me | solution 1 for ShapleySnowSG.Kernel.shapley_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T21:58:32.386556+00:00
-- url     : https://prove2.me/submissions/24394a51-cdc0-46e6-ba0a-398557153c31

import Mathlib
import Definitions.Def_ShapleySnowSG_Kernel_StochasticGame
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

lemma localGame_diff {n : ℕ} {I J : Fin n → Type*} (g : ∀ k, I k → J k → ℝ)
    (q : ∀ k, I k → J k → Fin n → ℝ) (hq0 : ∀ k i j l, 0 ≤ q k i j l)
    (hq1 : ∀ k i j, ∑ l, q k i j l = 1) (lam : ℝ) (hlam1 : lam ≤ 1) (z zb : Fin n → ℝ)
    (k : Fin n) (i : I k) (j : J k) :
    |localGame g q lam z k i j - localGame g q lam zb k i j| ≤ (1 - lam) * ‖z - zb‖ := by
  simp only [localGame, Matrix.of_apply]
  have : lam * g k i j + (1 - lam) * ∑ l, q k i j l * z l -
      (lam * g k i j + (1 - lam) * ∑ l, q k i j l * zb l) =
      (1 - lam) * ∑ l, q k i j l * (z l - zb l) := by
    simp only [mul_sub, Finset.sum_sub_distrib]; ring
  rw [this, abs_mul, abs_of_nonneg (by linarith)]
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  calc |∑ l, q k i j l * (z l - zb l)|
      ≤ ∑ l, |q k i j l * (z l - zb l)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, q k i j l * ‖z - zb‖ := by
      refine Finset.sum_le_sum fun l _ => ?_
      rw [abs_mul, abs_of_nonneg (hq0 _ _ _ _)]
      refine mul_le_mul_of_nonneg_left ?_ (hq0 _ _ _ _)
      have := norm_le_pi_norm (z - zb) l
      rwa [Real.norm_eq_abs, Pi.sub_apply] at this
    _ = ‖z - zb‖ := by rw [← Finset.sum_mul, hq1, one_mul]

end SSKAux

open ShapleySnowSG.Kernel in
theorem solution {n : ℕ} (hn : 0 < n) {I J : Fin n → Type*} [∀ k, Fintype (I k)] [∀ k, Fintype (J k)]
    [∀ k, Nonempty (I k)] [∀ k, Nonempty (J k)]
    (g : ∀ k, I k → J k → ℝ) (q : ∀ k, I k → J k → Fin n → ℝ)
    (hq0 : ∀ k i j l, 0 ≤ q k i j l) (hq1 : ∀ k i j, ∑ l, q k i j l = 1)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    (∀ (z : Fin n → ℝ) (k : Fin n), ∃! w : ℝ, IsMatVal (localGame g q lam z k) w) ∧
    (∃! v : Fin n → ℝ, IsShapleyFixed g q lam v) ∧
    (∀ z zb w wb : Fin n → ℝ, (∀ k, IsMatVal (localGame g q lam z k) (w k)) →
      (∀ k, IsMatVal (localGame g q lam zb k) (wb k)) → ‖w - wb‖ ≤ (1 - lam) * ‖z - zb‖) := by
  have hcontr : ∀ z zb w wb : Fin n → ℝ, (∀ k, IsMatVal (localGame g q lam z k) (w k)) →
      (∀ k, IsMatVal (localGame g q lam zb k) (wb k)) → ‖w - wb‖ ≤ (1 - lam) * ‖z - zb‖ := by
    intro z zb w wb hw hwb
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg (by linarith) (norm_nonneg _))).mpr fun k => ?_
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact SSKAux.val_abs_le _ _ _ _ _ (hw k) (hwb k)
      (fun i j => SSKAux.localGame_diff g q hq0 hq1 lam hlam1 z zb k i j)
  have hex : ∀ (z : Fin n → ℝ) (k : Fin n), ∃ w : ℝ, IsMatVal (localGame g q lam z k) w :=
    fun z k => SSKAux.exists_val _
  refine ⟨fun z k => ?_, ?_, hcontr⟩
  · obtain ⟨w, hw⟩ := hex z k
    exact ⟨w, hw, fun w' hw' => SSKAux.isMatVal_unique _ _ _ hw' hw⟩
  · choose Φ hΦ using hex
    let F : (Fin n → ℝ) → (Fin n → ℝ) := fun z k => Φ z k
    let K : NNReal := ⟨1 - lam, by linarith⟩
    have hK : K < 1 := by
      rw [← NNReal.coe_lt_coe]; show 1 - lam < 1; linarith
    have hF : ContractingWith K F := by
      refine ⟨hK, LipschitzWith.of_dist_le_mul fun z zb => ?_⟩
      rw [dist_eq_norm, dist_eq_norm]
      exact hcontr z zb (F z) (F zb) (fun k => hΦ z k) (fun k => hΦ zb k)
    have hfix := hF.fixedPoint_isFixedPt (f := F)
    set v := ContractingWith.fixedPoint F hF
    refine ⟨v, fun k => ?_, fun v' hv' => ?_⟩
    · have := hΦ v k
      have e : F v k = v k := congrFun hfix k
      simp only [F] at e
      rwa [e] at this
    · have h := hcontr v' v v' v hv' (fun k => by
        have := hΦ v k
        have e : F v k = v k := congrFun hfix k
        simp only [F] at e
        rwa [e] at this)
      have h0 : ‖v' - v‖ = 0 := by
        have := norm_nonneg (v' - v); nlinarith
      exact sub_eq_zero.mp (norm_eq_zero.mp h0)
