-- Prove2me | solution 1 for OptRobustCD.lemma_4_12
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T17:26:56.350372+00:00
-- url     : https://prove2.me/submissions/1867e76d-1d34-4f1a-9dc1-46d8e0bc283e

import Mathlib
import Definitions.Def_OptRobustCD_BP

namespace OptRobustCD

open Finset
open scoped Classical

theorem adj_iff_aux412 {n : ℕ} (G G' : SimpleGraph (Fin n)) (x : Fin n)
    (hx : x ∉ editEndpoints G G') (w : Fin n) : (G.Adj x w ↔ G'.Adj x w) := by
  by_contra h
  apply hx
  simp only [editEndpoints, mem_filter, mem_univ, true_and]
  exact ⟨w, h⟩

theorem nbrs_eq_aux412 {n : ℕ} (G G' : SimpleGraph (Fin n)) (u : Fin n)
    (hu : u ∉ editEndpoints G G') : nbrs G u = nbrs G' u := by
  ext w
  simp only [nbrs, mem_filter, mem_univ, true_and]
  exact adj_iff_aux412 G G' u hu w

theorem bpMap_congr_aux412 {n : ℕ} (lam : ℝ) (S : Finset (Fin n)) (m m' : Fin n → ℝ)
    (h : ∀ w ∈ S, m w = m' w) : bpMap lam S m = bpMap lam S m' := by
  unfold bpMap
  have e1 : ∏ w ∈ S, (1 + lam * m w) = ∏ w ∈ S, (1 + lam * m' w) :=
    prod_congr rfl (fun w hw => by rw [h w hw])
  have e2 : ∏ w ∈ S, (1 - lam * m w) = ∏ w ∈ S, (1 - lam * m' w) :=
    prod_congr rfl (fun w hw => by rw [h w hw])
  rw [e1, e2]

theorem msg_eq_aux412 {n : ℕ} (G G' : SimpleGraph (Fin n)) (lam γ : ℝ)
    (τ τ' : Fin n × Fin n → Bool)
    (hτ : ∀ p : Fin n × Fin n, (G.Adj p.1 p.2 ↔ G'.Adj p.1 p.2) → τ p = τ' p) :
    ∀ (s : ℕ) (u v : Fin n),
      (∀ x, G.edist u x + 1 ≤ (s : ℕ∞) → x ∉ editEndpoints G G') →
      (u ∉ editEndpoints G G' ∨ v ∉ editEndpoints G G') →
      bpMsg G lam γ τ s u v = bpMsg G' lam γ τ' s u v := by
  intro s
  induction s with
  | zero =>
    intro u v _ huv
    show γ * spinR (τ (v, u)) = γ * spinR (τ' (v, u))
    rw [hτ (v, u) ?_]
    rcases huv with hu | hv
    · have h := adj_iff_aux412 G G' u hu v
      exact ⟨fun h1 => (h.mp h1.symm).symm, fun h1 => (h.mpr h1.symm).symm⟩
    · exact adj_iff_aux412 G G' v hv u
  | succ s ih =>
    intro u v hball _
    have hu : u ∉ editEndpoints G G' := by
      apply hball u
      rw [SimpleGraph.edist_self, zero_add]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le s)
    show bpMap lam ((nbrs G u).erase v) (fun w => bpMsg G lam γ τ s w u) =
      bpMap lam ((nbrs G' u).erase v) (fun w => bpMsg G' lam γ τ' s w u)
    rw [← nbrs_eq_aux412 G G' u hu]
    apply bpMap_congr_aux412
    intro w hw
    have hadj : G.Adj u w := by
      have := mem_of_mem_erase hw
      simpa [nbrs] using this
    apply ih w u _ (Or.inr hu)
    intro x hx
    apply hball x
    have h1 : G.edist u x ≤ G.edist u w + G.edist w x := SimpleGraph.edist_triangle
    rw [SimpleGraph.edist_eq_one_iff_adj.mpr hadj] at h1
    calc G.edist u x + 1 ≤ (1 + G.edist w x) + 1 := by gcongr
      _ = (G.edist w x + 1) + 1 := by ring
      _ ≤ (s : ℕ∞) + 1 := by gcongr
      _ = ((s + 1 : ℕ) : ℕ∞) := by push_cast; rfl

theorem out_eq_aux412 {n : ℕ} (G G' : SimpleGraph (Fin n)) (lam γ : ℝ) (t : ℕ)
    (τ τ' : Fin n × Fin n → Bool)
    (hτ : ∀ p : Fin n × Fin n, (G.Adj p.1 p.2 ↔ G'.Adj p.1 p.2) → τ p = τ' p) (v : Fin n)
    (hv : ∀ x, G.edist v x ≤ (t : ℕ∞) → x ∉ editEndpoints G G') :
    bpOut G lam t γ τ v = bpOut G' lam t γ τ' v := by
  have hvA : v ∉ editEndpoints G G' := hv v (by rw [SimpleGraph.edist_self]; exact zero_le)
  have hmap : bpMap lam (nbrs G v) (fun w => bpMsg G lam γ τ t w v) =
      bpMap lam (nbrs G v) (fun w => bpMsg G' lam γ τ' t w v) := by
    apply bpMap_congr_aux412
    intro w hw
    have hadj : G.Adj v w := by simpa [nbrs] using hw
    apply msg_eq_aux412 G G' lam γ τ τ' hτ t w v _ (Or.inr hvA)
    intro x hx
    apply hv x
    have h1 : G.edist v x ≤ G.edist v w + G.edist w x := SimpleGraph.edist_triangle
    rw [SimpleGraph.edist_eq_one_iff_adj.mpr hadj] at h1
    calc G.edist v x ≤ 1 + G.edist w x := h1
      _ = G.edist w x + 1 := add_comm _ _
      _ ≤ t := hx
  simp only [bpOut]
  rw [← nbrs_eq_aux412 G G' v hvA, hmap]

/-- One coordinate of the rounding law. -/
noncomputable def fAux412 {n : ℕ} (Y : EVec n) (p : Fin n × Fin n) (b : Bool) : ℝ :=
  (1 + spinR b * Real.tanh (Y p)) / 2

/-- The coupling of one coordinate: diagonal where the two laws agree, independent elsewhere. -/
noncomputable def kAux412 {n : ℕ} (Y Y' : EVec n) (p : Fin n × Fin n) (b b' : Bool) : ℝ :=
  if Y p = Y' p then (if b = b' then fAux412 Y p b else 0) else fAux412 Y p b * fAux412 Y' p b'

theorem fAux412_nonneg {n : ℕ} (Y : EVec n) (p : Fin n × Fin n) (b : Bool) :
    0 ≤ fAux412 Y p b := by
  unfold fAux412 spinR
  have h1 := Real.tanh_lt_one (Y p)
  have h2 := Real.neg_one_lt_tanh (Y p)
  cases b <;> simp <;> linarith

theorem fAux412_sum {n : ℕ} (Y : EVec n) (p : Fin n × Fin n) :
    ∑ b, fAux412 Y p b = 1 := by
  rw [Fintype.sum_bool]
  unfold fAux412 spinR
  simp only [if_true, Bool.false_eq_true, if_false]
  ring

theorem kAux412_nonneg {n : ℕ} (Y Y' : EVec n) (p : Fin n × Fin n) (b b' : Bool) :
    0 ≤ kAux412 Y Y' p b b' := by
  unfold kAux412
  split_ifs
  · exact fAux412_nonneg Y p b
  · exact le_refl 0
  · exact mul_nonneg (fAux412_nonneg Y p b) (fAux412_nonneg Y' p b')

theorem kAux412_row {n : ℕ} (Y Y' : EVec n) (p : Fin n × Fin n) (b : Bool) :
    ∑ b', kAux412 Y Y' p b b' = fAux412 Y p b := by
  unfold kAux412
  by_cases h : Y p = Y' p
  · simp only [if_pos h]
    rw [Finset.sum_ite_eq]; simp
  · simp only [if_neg h]
    rw [← Finset.mul_sum, fAux412_sum, mul_one]

theorem kAux412_col {n : ℕ} (Y Y' : EVec n) (p : Fin n × Fin n) (b' : Bool) :
    ∑ b, kAux412 Y Y' p b b' = fAux412 Y' p b' := by
  unfold kAux412
  by_cases h : Y p = Y' p
  · simp only [if_pos h]
    rw [Finset.sum_ite_eq']
    simp only [mem_univ, if_true]
    unfold fAux412; rw [h]
  · simp only [if_neg h]
    rw [← Finset.sum_mul, fAux412_sum, one_mul]

theorem K_row_aux412 {n : ℕ} (Y Y' : EVec n) (τ : Fin n × Fin n → Bool) :
    ∑ τ' : Fin n × Fin n → Bool, ∏ p, kAux412 Y Y' p (τ p) (τ' p) = roundWeight Y τ := by
  have h : ∑ τ' : Fin n × Fin n → Bool, ∏ p, kAux412 Y Y' p (τ p) (τ' p) =
      ∏ p, ∑ b, kAux412 Y Y' p (τ p) b := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [h]
  unfold roundWeight
  exact prod_congr rfl (fun p _ => kAux412_row Y Y' p (τ p))

theorem K_col_aux412 {n : ℕ} (Y Y' : EVec n) (τ' : Fin n × Fin n → Bool) :
    ∑ τ : Fin n × Fin n → Bool, ∏ p, kAux412 Y Y' p (τ p) (τ' p) = roundWeight Y' τ' := by
  have h : ∑ τ : Fin n × Fin n → Bool, ∏ p, kAux412 Y Y' p (τ p) (τ' p) =
      ∏ p, ∑ b, kAux412 Y Y' p b (τ' p) := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [h]
  unfold roundWeight
  exact prod_congr rfl (fun p _ => kAux412_col Y Y' p (τ' p))

end OptRobustCD

open OptRobustCD in
open scoped Classical in
theorem solution (lam : ℝ) (hlam : lam ∈ Set.Ioo (-1 : ℝ) 1) {n : ℕ}
    (G G' : SimpleGraph (Fin n)) (t : ℕ) (ht : 1 ≤ t) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1)
    (y : EVec n) :
    ∃ μ : (Fin n → Bool) → (Fin n → Bool) → ℝ, (∀ a b, 0 ≤ μ a b) ∧
      (∀ a, ∑ b, μ a b = bpProb G lam t γ (restrictTo G y) a) ∧
      (∀ b, ∑ a, μ a b = bpProb G' lam t γ (restrictTo G' y) b) ∧
      ∀ a b, μ a b ≠ 0 → ((Finset.univ.filter fun v => a v ≠ b v).card : ℝ) ≤
        ∑ x ∈ editEndpoints G G', (ballCard G x t : ℝ) := by
  set Y := restrictTo G y with hY
  set Y' := restrictTo G' y with hY'
  let K : (Fin n × Fin n → Bool) → (Fin n × Fin n → Bool) → ℝ :=
    fun τ τ' => ∏ p, kAux412 Y Y' p (τ p) (τ' p)
  have hK0 : ∀ τ τ', 0 ≤ K τ τ' := fun τ τ' =>
    Finset.prod_nonneg (fun p _ => kAux412_nonneg Y Y' p (τ p) (τ' p))
  refine ⟨fun a b => ∑ τ, ∑ τ', K τ τ' * ((if bpOut G lam t γ τ = a then 1 else 0) *
      (if bpOut G' lam t γ τ' = b then 1 else 0)), ?_, ?_, ?_, ?_⟩
  · intro a b
    apply Finset.sum_nonneg; intro τ _
    apply Finset.sum_nonneg; intro τ' _
    apply mul_nonneg (hK0 τ τ')
    split_ifs <;> norm_num
  · intro a
    beta_reduce
    rw [Finset.sum_comm]
    unfold bpProb
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [Finset.sum_comm]
    have h1 : ∀ τ' : Fin n × Fin n → Bool,
        ∑ b, K τ τ' * ((if bpOut G lam t γ τ = a then (1 : ℝ) else 0) *
          (if bpOut G' lam t γ τ' = b then 1 else 0)) =
        K τ τ' * (if bpOut G lam t γ τ = a then 1 else 0) := by
      intro τ'
      rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_ite_eq]
      simp
    rw [Finset.sum_congr rfl (fun τ' _ => h1 τ'), ← Finset.sum_mul]
    rw [K_row_aux412 Y Y' τ]
  · intro b
    beta_reduce
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext τ'; rw [Finset.sum_comm]
    unfold bpProb
    refine Finset.sum_congr rfl (fun τ' _ => ?_)
    have h1 : ∀ τ : Fin n × Fin n → Bool,
        ∑ a, K τ τ' * ((if bpOut G lam t γ τ = a then (1 : ℝ) else 0) *
          (if bpOut G' lam t γ τ' = b then 1 else 0)) =
        K τ τ' * (if bpOut G' lam t γ τ' = b then 1 else 0) := by
      intro τ
      rw [← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_ite_eq]
      simp
    rw [Finset.sum_congr rfl (fun τ _ => h1 τ), ← Finset.sum_mul]
    rw [K_col_aux412 Y Y' τ']
  · intro a b hab
    beta_reduce at hab
    obtain ⟨τ, -, hτne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
    obtain ⟨τ', -, hτ'ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hτne
    have hKne : K τ τ' ≠ 0 := left_ne_zero_of_mul hτ'ne
    have hrest := right_ne_zero_of_mul hτ'ne
    have ha : bpOut G lam t γ τ = a := by
      by_contra h; apply hrest; rw [if_neg h, zero_mul]
    have hb : bpOut G' lam t γ τ' = b := by
      by_contra h; apply hrest; rw [if_neg h, mul_zero]
    have hagree : ∀ p : Fin n × Fin n, (G.Adj p.1 p.2 ↔ G'.Adj p.1 p.2) → τ p = τ' p := by
      intro p hp
      have hYp : Y p = Y' p := by
        rw [hY, hY']
        unfold restrictTo
        by_cases h1 : G.Adj p.1 p.2
        · rw [if_pos h1, if_pos (hp.mp h1)]
        · rw [if_neg h1, if_neg (fun h2 => h1 (hp.mpr h2))]
      have hk := (Finset.prod_ne_zero_iff.mp hKne) p (Finset.mem_univ p)
      unfold kAux412 at hk
      rw [if_pos hYp] at hk
      by_contra hne
      rw [if_neg hne] at hk
      exact hk rfl
    have hsub : (Finset.univ.filter fun v => a v ≠ b v) ⊆
        (editEndpoints G G').biUnion (fun x => Finset.univ.filter fun u => G.edist x u ≤ (t : ℕ∞)) := by
      intro v hv
      rw [Finset.mem_filter] at hv
      by_contra hno
      apply hv.2
      rw [← ha, ← hb]
      apply out_eq_aux412 G G' lam γ t τ τ' hagree v
      intro x hx hxA
      apply hno
      rw [Finset.mem_biUnion]
      refine ⟨x, hxA, ?_⟩
      rw [Finset.mem_filter, SimpleGraph.edist_comm]
      exact ⟨Finset.mem_univ v, hx⟩
    have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have hcardR : ((Finset.univ.filter fun v => a v ≠ b v).card : ℝ) ≤
        ((∑ x ∈ editEndpoints G G',
          (Finset.univ.filter fun u => G.edist x u ≤ (t : ℕ∞)).card : ℕ) : ℝ) := by
      exact_mod_cast hcard
    rw [Nat.cast_sum] at hcardR
    exact hcardR
