-- Prove2me | solution 1 for ReLUBinaryDepth.ProductTradeoff.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:42:52.25499+00:00
-- url     : https://prove2.me/submissions/dabc9ced-9123-403f-aeee-2090659d652b

import Mathlib
import Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Network

section
set_option autoImplicit false

noncomputable section
namespace ReLUBinaryDepth.ProductTradeoff.Dev.L23

open ReLUBinaryDepth.ProductTradeoff

/-- The family of reals whose rational span contains the value of a gate. -/
def gf {n : ℕ} (g : AffineGate n) (m : ℕ) (F : ℕ → Finset ℝ) : Finset ℝ :=
  insert g.bias (Finset.univ.image g.inputWeight) ∪
    (Finset.range m).biUnion (fun j => (F j).image (fun r => g.previousWeight j * r))

theorem card_gf {n : ℕ} (g : AffineGate n) (m : ℕ) (F : ℕ → Finset ℝ) :
    (gf g m F).card ≤ (n + 1) + ∑ j ∈ Finset.range m, (F j).card := by
  unfold gf
  refine (Finset.card_union_le _ _).trans ?_
  have h1 : (insert g.bias (Finset.univ.image g.inputWeight)).card ≤ 1 + n := by
    refine (Finset.card_insert_le _ _).trans ?_
    have := Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := g.inputWeight)
    simp at this
    omega
  have h2 : ((Finset.range m).biUnion (fun j => (F j).image (fun r => g.previousWeight j * r))).card
      ≤ ∑ j ∈ Finset.range m, (F j).card := by
    refine Finset.card_biUnion_le.trans ?_
    exact Finset.sum_le_sum (fun j _ => Finset.card_image_le)
  omega

theorem eval_mem_span {n : ℕ} (g : AffineGate n) (m : ℕ) (F : ℕ → Finset ℝ) (x : Cube n)
    (v : List ℝ) (hl : v.length = m)
    (hv : ∀ j, j < m → v.getD j 0 ∈ Submodule.span ℚ (F j : Set ℝ)) :
    g.eval x v ∈ Submodule.span ℚ (gf g m F : Set ℝ) := by
  unfold AffineGate.eval
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · apply Submodule.subset_span
    simp [gf]
  · apply Submodule.sum_mem
    intro i _
    cases hx : x i
    · simp [bit, hx]
    · simp only [bit, hx, if_true, mul_one]
      apply Submodule.subset_span
      simp only [gf, Finset.coe_union, Finset.coe_insert, Finset.coe_image, Finset.coe_univ,
        Set.image_univ, Set.mem_union, Set.mem_insert_iff, Set.mem_range]
      exact Or.inl (Or.inr ⟨i, rfl⟩)
  · apply Submodule.sum_mem
    intro j _
    have hj : j.val < m := hl ▸ j.isLt
    have key : v[j] = v.getD j.val 0 := by simp [List.getD_eq_getElem?_getD]
    rw [key]
    have h1 := hv j.val hj
    have h2 : g.previousWeight j.val * v.getD j.val 0 ∈
        Submodule.span ℚ ((F j.val).image (fun r => g.previousWeight j.val * r) : Set ℝ) := by
      refine Submodule.span_induction (p := fun y _ => g.previousWeight j.val * y ∈
        Submodule.span ℚ ((F j.val).image (fun r => g.previousWeight j.val * r) : Set ℝ))
        ?_ ?_ ?_ ?_ h1
      · intro y hy
        apply Submodule.subset_span
        simp only [Finset.coe_image, Set.mem_image]
        exact ⟨y, hy, rfl⟩
      · simp
      · intro y z _ _ hy hz
        rw [mul_add]; exact Submodule.add_mem _ hy hz
      · intro q y _ hy
        rw [mul_smul_comm]; exact Submodule.smul_mem _ q hy
    refine Submodule.span_mono ?_ h2
    intro r hr
    simp only [gf, Finset.coe_union, Finset.coe_biUnion, Finset.coe_range, Set.mem_union,
      Set.mem_iUnion, Set.mem_Iio]
    exact Or.inr ⟨j.val, hj, hr⟩

theorem relu_mem_span (t : ℝ) (S : Submodule ℚ ℝ) (h : t ∈ S) : relu t ∈ S := by
  unfold relu
  rcases max_choice 0 t with h0 | h0 <;> rw [h0]
  · exact S.zero_mem
  · exact h

def vals {n : ℕ} (N : Network n) (x : Cube n) (k : ℕ) : List ℝ :=
  (N.layers.take k).foldl (fun v layer => v ++ layer.map (fun g => relu (g.eval x v))) []

theorem vals_length {n : ℕ} (N : Network n) (x : Cube n) (k : ℕ) :
    (vals N x k).length = ((N.layers.take k).map List.length).sum := by
  unfold vals
  generalize N.layers.take k = L
  suffices h : ∀ (v : List ℝ), (L.foldl (fun v layer => v ++ layer.map (fun g => relu (g.eval x v))) v).length
      = v.length + (L.map List.length).sum by simpa using h []
  induction L with
  | nil => intro v; simp
  | cons l L ih => intro v; simp [ih]; ring

theorem vals_succ {n : ℕ} (N : Network n) (x : Cube n) (k : ℕ) (hk : k < N.layers.length) :
    vals N x (k + 1) = vals N x k ++ N.layers[k].map (fun g => relu (g.eval x (vals N x k))) := by
  unfold vals
  rw [List.take_succ, List.foldl_append]
  have : N.layers[k]? = some N.layers[k] := by simp [hk]
  rw [this]
  simp

theorem layer_le_width {n : ℕ} (N : Network n) (l : List (AffineGate n)) (hl : l ∈ N.layers) :
    l.length ≤ N.width := by
  unfold Network.width
  have : ∀ (L : List (List (AffineGate n))) (w : ℕ), l ∈ L →
      l.length ≤ L.foldl (fun w layer => max w layer.length) w := by
    intro L
    induction L with
    | nil => intro w h; simp at h
    | cons l' L ih =>
      intro w h
      simp only [List.foldl_cons]
      rcases List.mem_cons.1 h with rfl | h
      · have : ∀ (L' : List (List (AffineGate n))) (w : ℕ),
            w ≤ L'.foldl (fun w layer => max w layer.length) w := by
          intro L'
          induction L' with
          | nil => intro w; simp
          | cons a L' ih' => intro w; simp only [List.foldl_cons]; exact (le_max_left _ _).trans (ih' _)
        exact (le_max_right _ _).trans (this _ _)
      · exact ih _ h
  exact this _ _ hl

theorem width_pos {n : ℕ} (N : Network n) : 1 ≤ N.width := by
  unfold Network.width
  have : ∀ (L : List (List (AffineGate n))) (w : ℕ),
      w ≤ L.foldl (fun w layer => max w layer.length) w := by
    intro L
    induction L with
    | nil => intro w; simp
    | cons a L ih => intro w; simp only [List.foldl_cons]; exact (le_max_left _ _).trans (ih _)
  exact this _ _

/-- Main invariant. -/
theorem inv {n : ℕ} (N : Network n) (w : ℕ) (hw : N.width ≤ w) :
    ∀ k, k ≤ N.layers.length → ∃ F : ℕ → Finset ℝ,
      (∀ x : Cube n, ∀ j, j < ((N.layers.take k).map List.length).sum →
        (vals N x k).getD j 0 ∈ Submodule.span ℚ (F j : Set ℝ)) ∧
      (∑ j ∈ Finset.range ((N.layers.take k).map List.length).sum, (F j).card) + (n + 1) ≤
        (n + 1) * (1 + w) ^ k := by
  intro k
  induction k with
  | zero => intro _; exact ⟨fun _ => ∅, by simp, by simp⟩
  | succ k ih =>
    intro hk
    have hkl : k < N.layers.length := by omega
    obtain ⟨F, hF, hc⟩ := ih (by omega)
    set m := ((N.layers.take k).map List.length).sum with hm
    set ℓ := N.layers[k] with hℓ
    have hlen : ℓ.length ≤ w := (layer_le_width N ℓ (List.getElem_mem hkl)).trans hw
    let dflt : AffineGate n := ⟨0, fun _ => 0, fun _ => 0⟩
    let F' : ℕ → Finset ℝ := fun j => if j < m then F j else gf (ℓ.getD (j - m) dflt) m F
    have hsum : ((N.layers.take (k + 1)).map List.length).sum = m + ℓ.length := by
      rw [List.take_succ]
      have : N.layers[k]? = some ℓ := by simp [hℓ, hkl]
      rw [this]; simp [hm]
    refine ⟨F', ?_, ?_⟩
    · intro x j hj
      rw [hsum] at hj
      rw [vals_succ N x k hkl]
      have hvl : (vals N x k).length = m := vals_length N x k
      by_cases hjm : j < m
      · rw [List.getD_append _ _ _ _ (by omega)]
        simp only [F', if_pos hjm]
        exact hF x j hjm
      · simp only [F', if_neg hjm]
        have hjt : j - m < ℓ.length := by omega
        have e : (vals N x k ++ N.layers[k].map (fun g => relu (g.eval x (vals N x k)))).getD j 0 =
            relu ((ℓ[j - m]).eval x (vals N x k)) := by
          rw [List.getD_append_right _ _ _ _ (by omega), hvl]
          have hjt' : j - m < N.layers[k].length := hjt
          simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
          rw [List.getElem?_eq_getElem hjt']
          simp only [Option.map_some, Option.getD_some]
          rfl
        rw [e]
        have hg : ℓ.getD (j - m) dflt = ℓ[j - m] := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjt]
        rw [hg]
        apply relu_mem_span
        exact eval_mem_span _ m F x (vals N x k) hvl (fun j hj => hF x j hj)
    · rw [hsum, Finset.sum_range_add]
      have h1 : ∑ j ∈ Finset.range m, (F' j).card = ∑ j ∈ Finset.range m, (F j).card := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [F', if_pos (Finset.mem_range.1 hj)]
      have h2 : ∀ t ∈ Finset.range ℓ.length, (F' (m + t)).card ≤ (n + 1) + ∑ j ∈ Finset.range m, (F j).card := by
        intro t ht
        have : ¬ (m + t < m) := by omega
        simp only [F', if_neg this]
        refine (card_gf _ _ _)
      have h3 : ∑ t ∈ Finset.range ℓ.length, (F' (m + t)).card ≤
          ℓ.length * ((n + 1) + ∑ j ∈ Finset.range m, (F j).card) := by
        refine (Finset.sum_le_sum h2).trans ?_
        simp
      rw [h1]
      set s := ∑ j ∈ Finset.range m, (F j).card
      have h4 : ℓ.length * ((n + 1) + s) ≤ w * ((n + 1) + s) := Nat.mul_le_mul_right _ hlen
      calc s + ∑ t ∈ Finset.range ℓ.length, (F' (m + t)).card + (n + 1)
          ≤ (s + (n + 1)) + w * ((n + 1) + s) := by omega
        _ = (1 + w) * (s + (n + 1)) := by ring
        _ ≤ (1 + w) * ((n + 1) * (1 + w) ^ k) := Nat.mul_le_mul_left _ hc
        _ = (n + 1) * (1 + w) ^ (k + 1) := by ring

theorem span_bound {n : ℕ} (N : Network n) (w : ℕ) (hw : N.width ≤ w) (f : Cube n → ℝ)
    (hf : N.Computes f) :
    Module.finrank ℚ (outputSpan f) ≤ (n + 1) * (1 + w) ^ (N.layers.length) := by
  obtain ⟨F, hF, hc⟩ := inv N w hw N.layers.length le_rfl
  rw [List.take_length] at hF hc
  set m := (N.layers.map List.length).sum
  have hvals : ∀ x, N.values x = vals N x N.layers.length := by
    intro x; unfold vals Network.values; rw [List.take_length]
  have hmem : ∀ x, f x ∈ Submodule.span ℚ (gf N.output m F : Set ℝ) := by
    intro x
    rw [← hf x]
    have hvl : (N.values x).length = m := by
      rw [hvals, vals_length, List.take_length]
    have := eval_mem_span N.output m F x (N.values x) hvl
      (fun j hj => by rw [hvals]; exact hF x j hj)
    unfold Network.eval
    simp only []
    split_ifs
    · exact relu_mem_span _ _ this
    · exact this
  have hle : outputSpan f ≤ Submodule.span ℚ (gf N.output m F : Set ℝ) := by
    unfold outputSpan
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact hmem x
  calc Module.finrank ℚ (outputSpan f)
      ≤ Module.finrank ℚ (Submodule.span ℚ (gf N.output m F : Set ℝ)) := Submodule.finrank_mono hle
    _ ≤ (gf N.output m F).card := finrank_span_finset_le_card _
    _ ≤ (n + 1) + ∑ j ∈ Finset.range m, (F j).card := card_gf _ _ _
    _ ≤ (n + 1) * (1 + w) ^ (N.layers.length) := by omega

theorem span_le_pow {n : ℕ} (f : Cube n → ℝ) : Module.finrank ℚ (outputSpan f) ≤ 2 ^ n := by
  unfold outputSpan
  have : Set.range f = ((Finset.univ.image f : Finset ℝ) : Set ℝ) := by simp
  rw [this]
  refine (finrank_span_finset_le_card _).trans ?_
  refine Finset.card_image_le.trans ?_
  simp

theorem arith (n w d : ℕ) (hw1 : 1 ≤ w) (hnw : n ≤ w) (hd : 1 ≤ d) (D : ℕ)
    (h1 : D ≤ 2 ^ n) (h2 : D ≤ (n + 1) * (1 + w) ^ (d - 1)) :
    (D : ℝ) ≤ 3 * (w : ℝ) ^ d := by
  have hwr : (1 : ℝ) ≤ w := by exact_mod_cast hw1
  by_cases hw : w = 1
  · subst hw
    have : n ≤ 1 := hnw
    have : 2 ^ n ≤ 2 := by
      calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
        _ = 2 := by norm_num
    have : (D : ℝ) ≤ 2 := by exact_mod_cast h1.trans this
    simp; linarith
  · have hw2 : 2 ≤ w := by omega
    by_cases hdw : d ≤ w
    · have h3 : (D : ℝ) ≤ ((1 + w : ℕ) : ℝ) ^ d := by
        have : D ≤ (1 + w) ^ d := by
          calc D ≤ (n + 1) * (1 + w) ^ (d - 1) := h2
            _ ≤ (1 + w) * (1 + w) ^ (d - 1) := Nat.mul_le_mul_right _ (by omega)
            _ = (1 + w) ^ d := by
              rw [← pow_succ']; congr 1; omega
        exact_mod_cast this
      refine h3.trans ?_
      push_cast
      have hw0 : (0 : ℝ) < w := by linarith
      have e : ((1 : ℝ) + w) = w * (1 + 1 / w) := by field_simp; ring
      rw [e, mul_pow]
      have : (1 + 1 / (w : ℝ)) ^ d ≤ 3 := by
        have h4 : (1 + 1 / (w : ℝ)) ≤ Real.exp (1 / w) := by
          have := Real.add_one_le_exp (1 / (w : ℝ)); linarith
        calc (1 + 1 / (w : ℝ)) ^ d ≤ (Real.exp (1 / w)) ^ d :=
              pow_le_pow_left₀ (by positivity) h4 d
          _ = Real.exp (d * (1 / w)) := by rw [← Real.exp_nat_mul]
          _ ≤ Real.exp 1 := by
              apply Real.exp_le_exp.2
              rw [mul_one_div, div_le_one hw0]; exact_mod_cast hdw
          _ ≤ 3 := by linarith [Real.exp_one_lt_d9]
      calc (w : ℝ) ^ d * (1 + 1 / w) ^ d ≤ (w : ℝ) ^ d * 3 := by
            exact mul_le_mul_of_nonneg_left this (by positivity)
        _ = 3 * (w : ℝ) ^ d := by ring
    · have hdw' : w ≤ d := by omega
      have : D ≤ w ^ d := by
        calc D ≤ 2 ^ n := h1
          _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hnw
          _ ≤ w ^ w := Nat.pow_le_pow_left hw2 w
          _ ≤ w ^ d := Nat.pow_le_pow_right hw1 hdw'
      have : (D : ℝ) ≤ (w : ℝ) ^ d := by exact_mod_cast this
      nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ w) d]

end ReLUBinaryDepth.ProductTradeoff.Dev.L23
end

namespace ReLUBinaryDepth.ProductTradeoff

open ReLUBinaryDepth.ProductTradeoff.Dev.L23 in
theorem chk_lemma_2_3 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n w : ℕ) (N : Network n) (f : Cube n → ℝ),
      n ≤ w → N.width ≤ w → N.Computes f →
      (Module.finrank ℚ (outputSpan f) : ℝ) ≤ C * (w : ℝ) ^ N.depth := by
  refine ⟨3, by norm_num, fun n w N f hnw hw hf => ?_⟩
  have hw1 : 1 ≤ w := (width_pos N).trans hw
  exact arith n w N.depth hw1 hnw (by simp [Network.depth]) _ (span_le_pow f)
    (by simpa [Network.depth] using span_bound N w hw f hf)

end ReLUBinaryDepth.ProductTradeoff
end

theorem solution : type_of% @ReLUBinaryDepth.ProductTradeoff.chk_lemma_2_3 := @ReLUBinaryDepth.ProductTradeoff.chk_lemma_2_3
