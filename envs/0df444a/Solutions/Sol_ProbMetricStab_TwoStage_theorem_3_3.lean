-- Prove2me | solution 1 for ProbMetricStab.TwoStage.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-30T13:01:30.845056+00:00
-- url     : https://prove2.me/submissions/2e1ccc36-2962-4946-b483-70281e1a67db

import Mathlib
import Definitions.Def_ProbMetricStab_TwoStage_Model

set_option autoImplicit false

namespace PMS44

open Matrix

lemma exists_between_fin {ι : Type} (s r : Finset ι) (L U : ι → ℝ)
    (h : ∀ q ∈ s, ∀ p ∈ r, L q ≤ U p) :
    ∃ t : ℝ, (∀ q ∈ s, L q ≤ t) ∧ ∀ p ∈ r, t ≤ U p := by
  by_cases hs : s.Nonempty
  · refine ⟨s.sup' hs L, fun q hq => Finset.le_sup' L hq, fun p hp => ?_⟩
    exact Finset.sup'_le hs L (fun q hq => h q hq p hp)
  · by_cases hr : r.Nonempty
    · exact ⟨r.inf' hr U, fun q hq => absurd ⟨q, hq⟩ hs, fun p hp => Finset.inf'_le U hp⟩
    · exact ⟨0, fun q hq => absurd ⟨q, hq⟩ hs, fun p hp => absurd ⟨p, hp⟩ hr⟩

/-- Theorem of alternatives (Fourier–Motzkin), variables indexed by `Fin n`. -/
theorem fm_alt (n : ℕ) : ∀ {ι : Type} [Fintype ι] (a : ι → Fin n → ℝ) (b : ι → ℝ),
    (∃ x : Fin n → ℝ, ∀ i, ∑ s, a i s * x s ≤ b i) ∨
    (∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ (∀ s, ∑ i, l i * a i s = 0) ∧ ∑ i, l i * b i < 0) := by
  induction n with
  | zero =>
    intro ι _ a b
    classical
    by_cases h : ∀ i, 0 ≤ b i
    · left; exact ⟨0, fun i => by simpa using h i⟩
    · right
      push Not at h
      obtain ⟨i, hi⟩ := h
      refine ⟨fun j => if j = i then 1 else 0, fun j => ?_, fun s => s.elim0, ?_⟩
      · dsimp only; split_ifs <;> norm_num
      · simpa using hi
  | succ n ih =>
    intro ι _ a b
    classical
    let W : ι ⊕ (ι × ι) → ι → ℝ := Sum.elim (fun z i => if a z 0 = 0 ∧ i = z then 1 else 0)
      (fun pq i => if 0 < a pq.1 0 ∧ a pq.2 0 < 0 then
        (if i = pq.1 then -a pq.2 0 else 0) + (if i = pq.2 then a pq.1 0 else 0) else 0)
    have hW0 : ∀ k i, 0 ≤ W k i := by
      intro k i
      rcases k with z | ⟨p, q⟩
      · simp only [W, Sum.elim_inl]; split_ifs <;> norm_num
      · simp only [W, Sum.elim_inr]
        split_ifs with h1 h2 h3 h3 <;> subst_vars <;> first | linarith [h1.1, h1.2] | norm_num
    let C : ι ⊕ (ι × ι) → Fin (n + 1) → ℝ := fun k s => ∑ i, W k i * a i s
    let D : ι ⊕ (ι × ι) → ℝ := fun k => ∑ i, W k i * b i
    have hC0 : ∀ k, C k 0 = 0 := by
      intro k
      rcases k with z | ⟨p, q⟩
      · by_cases hz : a z 0 = 0
        · simp [C, W, hz]
        · simp [C, W, hz]
      · by_cases h : 0 < a p 0 ∧ a q 0 < 0
        · simp only [C, W, Sum.elim_inr, if_pos h, add_mul, ite_mul, zero_mul,
            Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          ring
        · simp [C, W, h]
    rcases ih (fun k s => C k s.succ) D with ⟨y, hy⟩ | ⟨μ, hμ0, hμ1, hμ2⟩
    · left
      let r : ι → ℝ := fun i => b i - ∑ s : Fin n, a i s.succ * y s
      have key : ∀ k, 0 ≤ ∑ i, W k i * r i := by
        intro k
        have e : ∑ i, W k i * r i = D k - ∑ s, C k s.succ * y s := by
          simp only [r, D, C, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul,
            mul_assoc]
          congr 1
          exact Finset.sum_comm
        rw [e]; linarith [hy k]
      have kinl : ∀ z, a z 0 = 0 → 0 ≤ r z := by
        intro z hz
        have := key (Sum.inl z)
        simpa [W, hz] using this
      have kinr : ∀ p q, 0 < a p 0 → a q 0 < 0 → 0 ≤ -a q 0 * r p + a p 0 * r q := by
        intro p q hp hq
        have := key (Sum.inr (p, q))
        simp only [W, Sum.elim_inr, if_pos (And.intro hp hq), add_mul, ite_mul, zero_mul,
          Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
        exact this
      obtain ⟨t, ht1, ht2⟩ := exists_between_fin (Finset.univ.filter (fun q => a q 0 < 0))
        (Finset.univ.filter (fun p => 0 < a p 0)) (fun q => r q / a q 0) (fun p => r p / a p 0)
        (by
          intro q hq p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq hp
          have h := kinr p q hp hq
          have e : -a q 0 * r p + a p 0 * r q =
              -(a p 0 * (-a q 0) * (r q / a q 0 - r p / a p 0)) := by
            have h1 : r p = (r p / a p 0) * a p 0 := (div_mul_cancel₀ _ hp.ne').symm
            have h2 : r q = (r q / a q 0) * a q 0 := (div_mul_cancel₀ _ hq.ne).symm
            set U := r p / a p 0
            set V := r q / a q 0
            rw [h1, h2]; ring
          by_contra hc
          push Not at hc
          have hpq : 0 < a p 0 * (-a q 0) * (r q / a q 0 - r p / a p 0) :=
            mul_pos (mul_pos hp (neg_pos.2 hq)) (sub_pos.2 hc)
          linarith)
      refine ⟨Fin.cons t y, fun i => ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      have hr : r i = b i - ∑ s : Fin n, a i s.succ * y s := rfl
      suffices a i 0 * t ≤ r i by linarith
      rcases lt_trichotomy (a i 0) 0 with hneg | hz | hpos
      · have := ht1 i (by simp [hneg])
        rw [div_le_iff_of_neg hneg] at this
        linarith
      · rw [hz, zero_mul]; exact kinl i hz
      · have := ht2 i (by simp [hpos])
        rw [le_div_iff₀ hpos] at this
        linarith
    · right
      refine ⟨fun i => ∑ k, μ k * W k i, fun i => Finset.sum_nonneg
        (fun k _ => mul_nonneg (hμ0 k) (hW0 k i)), fun s => ?_, ?_⟩
      · have e : ∑ i, (∑ k, μ k * W k i) * a i s = ∑ k, μ k * C k s := by
          simp only [C, Finset.sum_mul, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
        rw [e]
        refine Fin.cases ?_ (fun s => ?_) s
        · simp [hC0]
        · exact hμ1 s
      · have e : ∑ i, (∑ k, μ k * W k i) * b i = ∑ k, μ k * D k := by
          simp only [D, Finset.sum_mul, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
        rw [e]; exact hμ2

/-- Theorem of alternatives over an arbitrary finite variable type. -/
theorem fm_alt' {σ ι : Type} [Fintype σ] [Fintype ι] (a : ι → σ → ℝ) (b : ι → ℝ) :
    (∃ x : σ → ℝ, ∀ i, ∑ s, a i s * x s ≤ b i) ∨
    (∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ (∀ s, ∑ i, l i * a i s = 0) ∧ ∑ i, l i * b i < 0) := by
  classical
  let e := Fintype.equivFin σ
  rcases fm_alt _ (fun i k => a i (e.symm k)) b with ⟨x, hx⟩ | ⟨l, h0, h1, h2⟩
  · left
    refine ⟨fun s => x (e s), fun i => ?_⟩
    rw [Fintype.sum_equiv e _ (fun k => a i (e.symm k) * x k) (fun s => by simp)]
    exact hx i
  · right
    exact ⟨l, h0, fun s => by simpa using h1 (e s), h2⟩



section LP

variable {ι : Type} [Fintype ι] {n : ℕ} (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ) (c : Fin n → ℝ)

def PolyNonneg : Set (Fin n → ℝ) := {x | (∀ i, b i ≤ (A.mulVec x) i) ∧ 0 ≤ x}

def DualPoly : Set (ι → ℝ) := {u | (∀ j, Matrix.vecMul u A j ≤ c j) ∧ 0 ≤ u}

lemma strong (hX : (PolyNonneg A b).Nonempty)
    (hU : (DualPoly A c).Nonempty) :
    ∃ x ∈ PolyNonneg A b, ∃ u ∈ DualPoly A c,
      c ⬝ᵥ x ≤ u ⬝ᵥ b := by
  classical
  rcases fm_alt' (σ := Fin n ⊕ ι) (ι := ι ⊕ (Fin n ⊕ (Fin n ⊕ (ι ⊕ Unit))))
      (Sum.elim (fun i => Sum.elim (fun j => -A i j) 0)
        (Sum.elim (fun j' => Sum.elim (fun j => if j = j' then -1 else 0) 0)
          (Sum.elim (fun j' => Sum.elim 0 (fun i => A i j'))
            (Sum.elim (fun i' => Sum.elim 0 (fun i => if i = i' then -1 else 0))
              (fun _ => Sum.elim c (fun i => -b i))))))
      (Sum.elim (fun i => -b i) (Sum.elim 0 (Sum.elim c (Sum.elim 0 0)))) with
    ⟨z, hz⟩ | ⟨l, h0, h1, h2⟩
  · let x : Fin n → ℝ := fun j => z (Sum.inl j)
    let u : ι → ℝ := fun i => z (Sum.inr i)
    refine ⟨x, ⟨fun i => ?_, fun j => ?_⟩, u, ⟨fun j => ?_, fun i => ?_⟩, ?_⟩
    · have := hz (Sum.inl i)
      simp [Fintype.sum_sum_type] at this
      simp only [Matrix.mulVec, dotProduct, x]
      linarith
    · have := hz (Sum.inr (Sum.inl j))
      simp [Fintype.sum_sum_type] at this
      simp only [x, Pi.zero_apply]
      linarith
    · have := hz (Sum.inr (Sum.inr (Sum.inl j)))
      simp [Fintype.sum_sum_type] at this
      simp only [Matrix.vecMul, dotProduct, u]
      rw [Finset.sum_congr rfl (fun i _ => mul_comm (z (Sum.inr i)) (A i j))]
      linarith
    · have := hz (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))
      simp [Fintype.sum_sum_type] at this
      simp only [u, Pi.zero_apply]
      linarith
    · have := hz (Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))))
      simp [Fintype.sum_sum_type] at this
      simp only [dotProduct, x, u]
      rw [Finset.sum_congr rfl (fun i _ => mul_comm (z (Sum.inr i)) (b i))]
      linarith
  · exfalso
    obtain ⟨x0, hx1, hx2⟩ := hX
    obtain ⟨u0, hu1, hu2⟩ := hU
    let l1 : ι → ℝ := fun i => l (Sum.inl i)
    let l3 : Fin n → ℝ := fun j => l (Sum.inr (Sum.inr (Sum.inl j)))
    let τ : ℝ := l (Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))))
    have hl1 : ∀ i, 0 ≤ l1 i := fun i => h0 _
    have hl3 : ∀ j, 0 ≤ l3 j := fun j => h0 _
    have hτ : 0 ≤ τ := h0 _
    have E1 : ∀ j, (l1 ᵥ* A) j ≤ τ * c j := by
      intro j
      have := h1 (Sum.inl j)
      have h2' := h0 (Sum.inr (Sum.inl j))
      simp [Fintype.sum_sum_type] at this
      simp only [Matrix.vecMul, dotProduct, l1, τ]
      linarith
    have E2 : ∀ i, τ * b i ≤ (A *ᵥ l3) i := by
      intro i
      have := h1 (Sum.inr i)
      have h2' := h0 (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))
      simp [Fintype.sum_sum_type] at this
      simp only [Matrix.mulVec, dotProduct, l3, τ]
      rw [Finset.sum_congr rfl (fun j _ => mul_comm (A i j) (l (Sum.inr (Sum.inr (Sum.inl j)))))]
      linarith
    have R : c ⬝ᵥ l3 < l1 ⬝ᵥ b := by
      have := h2
      simp [Fintype.sum_sum_type] at this
      simp only [dotProduct, l1, l3]
      rw [Finset.sum_congr rfl (fun j _ => mul_comm (c j) (l (Sum.inr (Sum.inr (Sum.inl j)))))]
      linarith
    -- l1 ⬝ b ≤ τ * (c ⬝ x0)
    have K1 : l1 ⬝ᵥ b ≤ τ * (c ⬝ᵥ x0) := by
      calc l1 ⬝ᵥ b ≤ l1 ⬝ᵥ (A *ᵥ x0) :=
            Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx1 i) (hl1 i)
        _ = (l1 ᵥ* A) ⬝ᵥ x0 := dotProduct_mulVec l1 A x0
        _ ≤ (τ • c) ⬝ᵥ x0 := Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_right (by simpa using E1 j) (hx2 j)
        _ = τ * (c ⬝ᵥ x0) := by rw [smul_dotProduct, smul_eq_mul]
    have K2 : τ * (u0 ⬝ᵥ b) ≤ c ⬝ᵥ l3 := by
      calc τ * (u0 ⬝ᵥ b) = u0 ⬝ᵥ (τ • b) := by rw [dotProduct_smul, smul_eq_mul]
        _ ≤ u0 ⬝ᵥ (A *ᵥ l3) := Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (by simpa using E2 i) (hu2 i)
        _ = (u0 ᵥ* A) ⬝ᵥ l3 := dotProduct_mulVec u0 A l3
        _ ≤ c ⬝ᵥ l3 := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hu1 j) (hl3 j)
    have K3 : τ * (l1 ⬝ᵥ b) ≤ τ * (c ⬝ᵥ l3) := by
      calc τ * (l1 ⬝ᵥ b) = l1 ⬝ᵥ (τ • b) := by rw [dotProduct_smul, smul_eq_mul]
        _ ≤ l1 ⬝ᵥ (A *ᵥ l3) := Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (by simpa using E2 i) (hl1 i)
        _ = (l1 ᵥ* A) ⬝ᵥ l3 := dotProduct_mulVec l1 A l3
        _ ≤ (τ • c) ⬝ᵥ l3 := Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_right (by simpa using E1 j) (hl3 j)
        _ = τ * (c ⬝ᵥ l3) := by rw [smul_dotProduct, smul_eq_mul]
    rcases hτ.lt_or_eq with hpos | hzero
    · have := (mul_le_mul_iff_of_pos_left hpos).1 K3
      linarith
    · rw [← hzero] at K1 K2
      simp at K1 K2
      linarith


end LP

section Reduce

variable {κ ρ : Type} [Fintype κ] [DecidableEq κ] [Fintype ρ]

lemma abs_dot_le (a b : κ → ℝ) : |a ⬝ᵥ b| ≤ Fintype.card κ * (‖a‖ * ‖b‖) := by
  unfold dotProduct
  calc |∑ i, a i * b i| ≤ ∑ i, |a i * b i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : κ, ‖a‖ * ‖b‖ := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        have h1 : |a i| ≤ ‖a‖ := by simpa using norm_le_pi_norm a i
        have h2 : |b i| ≤ ‖b‖ := by simpa using norm_le_pi_norm b i
        exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp

lemma exists_inj_const (M : Matrix ρ κ ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : Finset κ,
      (∀ w : κ → ℝ, (∀ j, j ∉ S → w j = 0) → M *ᵥ w = 0 → w = 0) →
      ∀ w : κ → ℝ, (∀ j, j ∉ S → w j = 0) → ‖w‖ ≤ C * ‖M *ᵥ w‖ := by
  have key : ∀ S : Finset κ, ∃ c : ℝ, 0 ≤ c ∧
      ((∀ w : κ → ℝ, (∀ j, j ∉ S → w j = 0) → M *ᵥ w = 0 → w = 0) →
      ∀ w : κ → ℝ, (∀ j, j ∉ S → w j = 0) → ‖w‖ ≤ c * ‖M *ᵥ w‖) := by
    intro S
    by_cases hinj : ∀ w : κ → ℝ, (∀ j, j ∉ S → w j = 0) → M *ᵥ w = 0 → w = 0
    · let V : Submodule ℝ (κ → ℝ) :=
        { carrier := {w | ∀ j, j ∉ S → w j = 0}
          add_mem' := by
            intro a b ha hb j hj
            simp [ha j hj, hb j hj]
          zero_mem' := by
            intro j _
            rfl
          smul_mem' := by
            intro c a ha j hj
            simp [ha j hj] }
      let f : V →ₗ[ℝ] (ρ → ℝ) := (Matrix.mulVecLin M).comp V.subtype
      have hker : LinearMap.ker f = ⊥ := by
        rw [LinearMap.ker_eq_bot']
        intro w hw
        apply Subtype.ext
        exact hinj w.1 w.2 hw
      obtain ⟨K, -, hK⟩ := f.exists_antilipschitzWith hker
      refine ⟨K, NNReal.coe_nonneg K, fun _ w hw => ?_⟩
      have := hK.le_mul_dist (⟨w, hw⟩ : V) 0
      simpa [dist_zero_right, f] using this
    · exact ⟨0, le_rfl, fun h => absurd h hinj⟩
  choose c hc0 hc using key
  refine ⟨∑ S, c S, Finset.sum_nonneg fun S _ => hc0 S, fun S hS w hw => ?_⟩
  calc ‖w‖ ≤ c S * ‖M *ᵥ w‖ := hc S hS w hw
    _ ≤ (∑ S, c S) * ‖M *ᵥ w‖ :=
        mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun S _ => hc0 S) (Finset.mem_univ S)) (norm_nonneg _)

lemma reduce_step (M : Matrix ρ κ ℝ) (a : κ → ℝ) (b : ρ → ℝ) (β : ℝ)
    (hβ : ∀ y : κ → ℝ, 0 ≤ y → M *ᵥ y = b → β ≤ a ⬝ᵥ y)
    (y : κ → ℝ) (hy : 0 ≤ y) (hMy : M *ᵥ y = b) (w : κ → ℝ)
    (hwS : ∀ j, y j = 0 → w j = 0) (hMw : M *ᵥ w = 0) (hw : w ≠ 0) :
    ∃ y' : κ → ℝ, 0 ≤ y' ∧ M *ᵥ y' = b ∧ a ⬝ᵥ y' ≤ a ⬝ᵥ y ∧
      (Finset.univ.filter (fun j => y' j ≠ 0)).card <
        (Finset.univ.filter (fun j => y j ≠ 0)).card := by
  have no_ray : ∀ d : κ → ℝ, 0 ≤ d → M *ᵥ d = 0 → 0 ≤ a ⬝ᵥ d := by
    intro d hd hMd
    by_contra hneg
    push_neg at hneg
    set lam : ℝ := (a ⬝ᵥ y - β + 1) / (-(a ⬝ᵥ d)) with hlam
    have hpos : 0 < -(a ⬝ᵥ d) := by linarith
    have hlam0 : 0 ≤ lam := by
      have := hβ y hy hMy
      exact div_nonneg (by linarith) hpos.le
    have hfeas : 0 ≤ y + lam • d := fun j => by
      have h3 : 0 ≤ lam * d j := mul_nonneg hlam0 (hd j)
      have h4 : 0 ≤ y j := hy j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      linarith
    have hM : M *ᵥ (y + lam • d) = b := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, hMd, smul_zero, add_zero, hMy]
    have h1 := hβ _ hfeas hM
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at h1
    have h2 : lam * (a ⬝ᵥ d) = -(a ⬝ᵥ y - β + 1) := by
      rw [hlam, div_neg, neg_mul, div_mul_cancel₀ _ (ne_of_lt hneg)]
    linarith
  obtain ⟨w1, hMw1, hS1, ha1, hne1⟩ : ∃ w1 : κ → ℝ, M *ᵥ w1 = 0 ∧ (∀ j, y j = 0 → w1 j = 0) ∧
      a ⬝ᵥ w1 ≤ 0 ∧ w1 ≠ 0 := by
    by_cases h : a ⬝ᵥ w ≤ 0
    · exact ⟨w, hMw, hwS, h, hw⟩
    · refine ⟨-w, by simp [Matrix.mulVec_neg, hMw], fun j hj => by simp [hwS j hj], ?_,
        neg_ne_zero.2 hw⟩
      rw [dotProduct_neg]; linarith
  obtain ⟨w', hMw', hS', ha', hneg'⟩ : ∃ w' : κ → ℝ, M *ᵥ w' = 0 ∧ (∀ j, y j = 0 → w' j = 0) ∧
      a ⬝ᵥ w' ≤ 0 ∧ ∃ j, w' j < 0 := by
    by_cases hn : ∃ j, w1 j < 0
    · exact ⟨w1, hMw1, hS1, ha1, hn⟩
    · push_neg at hn
      have h0 := no_ray w1 hn hMw1
      obtain ⟨j, hj⟩ := Function.ne_iff.1 hne1
      have hjpos : 0 < w1 j := lt_of_le_of_ne (hn j) (Ne.symm hj)
      refine ⟨-w1, by simp [Matrix.mulVec_neg, hMw1], fun i hi => by simp [hS1 i hi], ?_,
        ⟨j, by simp; linarith⟩⟩
      rw [dotProduct_neg]; linarith
  classical
  set J := Finset.univ.filter (fun j => w' j < 0) with hJ
  have hJne : J.Nonempty := by
    obtain ⟨j, hj⟩ := hneg'
    exact ⟨j, by simp [hJ, hj]⟩
  set lam := J.inf' hJne (fun j => y j / (-w' j)) with hlam
  obtain ⟨j0, hj0J, hj0⟩ := Finset.exists_mem_eq_inf' hJne (fun j => y j / (-w' j))
  have hj0neg : w' j0 < 0 := by simpa [hJ] using hj0J
  have hlam0 : 0 ≤ lam := by
    apply Finset.le_inf'
    intro j hj
    have : w' j < 0 := by simpa [hJ] using hj
    exact div_nonneg (hy j) (by linarith)
  have hlamle : ∀ j, w' j < 0 → lam * (-w' j) ≤ y j := by
    intro j hj
    have h1 : lam ≤ y j / (-w' j) := Finset.inf'_le _ (by simp [hJ, hj])
    have hp : 0 < -w' j := by linarith
    rwa [le_div_iff₀ hp] at h1
  refine ⟨y + lam • w', ?_, ?_, ?_, ?_⟩
  · intro j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    by_cases hj : w' j < 0
    · have h5 := hlamle j hj
      rw [mul_neg] at h5
      linarith
    · have h4 : 0 ≤ y j := hy j
      have : 0 ≤ lam * w' j := mul_nonneg hlam0 (not_lt.1 hj)
      linarith
  · rw [Matrix.mulVec_add, Matrix.mulVec_smul, hMw', smul_zero, add_zero, hMy]
  · rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    have : lam * (a ⬝ᵥ w') ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam0 ha'
    linarith
  · apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨j0, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro h
        have := hS' j0 h
        linarith
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul]
        rw [← hlam] at hj0
        rw [hj0]
        have hw0 : w' j0 ≠ 0 := ne_of_lt hj0neg
        rw [div_neg, neg_mul, div_mul_cancel₀ _ hw0]
        ring
    · intro j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      intro h hy0
      apply h
      rw [hy0, hS' j hy0]; ring

lemma reduce (M : Matrix ρ κ ℝ) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ S : Finset κ,
      (∀ w : κ → ℝ, (∀ j, j ∉ S → w j = 0) → M *ᵥ w = 0 → w = 0) →
      ∀ w : κ → ℝ, (∀ j, j ∉ S → w j = 0) → ‖w‖ ≤ C * ‖M *ᵥ w‖)
    (a : κ → ℝ) (b : ρ → ℝ) (β : ℝ) (hβ : ∀ y : κ → ℝ, 0 ≤ y → M *ᵥ y = b → β ≤ a ⬝ᵥ y) :
    ∀ (k : ℕ) (y : κ → ℝ), 0 ≤ y → M *ᵥ y = b →
      (Finset.univ.filter (fun j => y j ≠ 0)).card ≤ k →
      ∃ y' : κ → ℝ, 0 ≤ y' ∧ M *ᵥ y' = b ∧ a ⬝ᵥ y' ≤ a ⬝ᵥ y ∧ ‖y'‖ ≤ C * ‖b‖ := by
  intro k
  induction k with
  | zero =>
    intro y hy hMy hk
    refine ⟨y, hy, hMy, le_rfl, ?_⟩
    have : y = 0 := by
      funext j
      by_contra hj
      have hmem : j ∈ Finset.univ.filter (fun j => y j ≠ 0) := by simpa using hj
      have := Finset.card_pos.2 ⟨j, hmem⟩
      omega
    rw [this, norm_zero]
    exact mul_nonneg hC0 (norm_nonneg _)
  | succ k ih =>
    intro y hy hMy hk
    by_cases hinj : ∀ w : κ → ℝ, (∀ j, j ∉ Finset.univ.filter (fun j => y j ≠ 0) → w j = 0) →
        M *ᵥ w = 0 → w = 0
    · refine ⟨y, hy, hMy, le_rfl, ?_⟩
      have := hC _ hinj y (fun j hj => by simpa using hj)
      rwa [hMy] at this
    · push_neg at hinj
      obtain ⟨w, hwS, hMw, hw⟩ := hinj
      obtain ⟨y', hy', hMy', hay', hcard⟩ :=
        reduce_step M a b β hβ y hy hMy w (fun j hj => hwS j (by simp [hj])) hMw hw
      obtain ⟨y'', h1, h2, h3, h4⟩ := ih y' hy' hMy' (by omega)
      exact ⟨y'', h1, h2, h3.trans hay', h4⟩

end Reduce

section PhiSec

open ProbMetricStab.TwoStage

variable {r mbar : ℕ} (W : Matrix (Fin r) (Fin mbar) ℝ)

lemma weak2 {y : Fin mbar → ℝ} {z : Fin r → ℝ} {u : Fin mbar → ℝ} (hy : 0 ≤ y)
    (hz : Wᵀ *ᵥ z ≤ u) : z ⬝ᵥ (W *ᵥ y) ≤ u ⬝ᵥ y := by
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hz j) (hy j)

lemma maxsplit (a w : ℝ) : max a 0 * w + max (-a) 0 * -w = a * w := by
  rcases le_total a 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

lemma strong2 {u : Fin mbar → ℝ} {t : Fin r → ℝ} (hu : u ∈ D W) (ht : t ∈ posW W) :
    ∃ y : Fin mbar → ℝ, 0 ≤ y ∧ W *ᵥ y = t ∧
      ∃ z : Fin r → ℝ, Wᵀ *ᵥ z ≤ u ∧ u ⬝ᵥ y ≤ z ⬝ᵥ t := by
  classical
  obtain ⟨y0, hy0, hWy0⟩ := ht
  obtain ⟨z0, hz0⟩ := hu
  have hX : (PolyNonneg (Matrix.fromRows W (-W)) (Sum.elim t (-t))).Nonempty := by
    refine ⟨y0, fun i => ?_, hy0⟩
    rcases i with i | i
    · simp [Matrix.fromRows_mulVec, ← hWy0]
    · simp [Matrix.fromRows_mulVec, ← hWy0, Matrix.neg_mulVec]
  have hU : (DualPoly (Matrix.fromRows W (-W)) u).Nonempty := by
    refine ⟨Sum.elim (fun i => max (z0 i) 0) (fun i => max (-z0 i) 0), fun j => ?_, ?_⟩
    · have h1 := hz0 j
      have e : (Sum.elim (fun i => max (z0 i) 0) (fun i => max (-z0 i) 0) ᵥ*
          Matrix.fromRows W (-W)) j = (Wᵀ *ᵥ z0) j := by
        simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
          Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Sum.elim_inl, Sum.elim_inr,
          Matrix.neg_apply, Matrix.transpose_apply]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [maxsplit, mul_comm]
      rw [e]; exact h1
    · intro k
      rcases k with i | i <;> simp
  obtain ⟨y, ⟨hy1, hy2⟩, v, ⟨hv1, hv2⟩, hle⟩ := strong (Matrix.fromRows W (-W)) (Sum.elim t (-t)) u hX hU
  refine ⟨y, hy2, ?_, fun i => v (Sum.inl i) - v (Sum.inr i), fun j => ?_, ?_⟩
  · funext i
    have h1 := hy1 (Sum.inl i)
    have h2 := hy1 (Sum.inr i)
    simp [Matrix.fromRows_mulVec, Matrix.neg_mulVec] at h1 h2
    linarith
  · have h1 := hv1 j
    have e : (v ᵥ* Matrix.fromRows W (-W)) j =
        (Wᵀ *ᵥ (fun i => v (Sum.inl i) - v (Sum.inr i))) j := by
      simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
        Matrix.neg_apply, Matrix.transpose_apply]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [← e]; exact h1
  · have e : v ⬝ᵥ Sum.elim t (-t) = (fun i => v (Sum.inl i) - v (Sum.inr i)) ⬝ᵥ t := by
      simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [← e]; exact hle

/-- The dual problem written in standard form, variables `(z⁺, z⁻, s)`. -/
def Md : Matrix (Fin mbar) (Fin r ⊕ Fin r ⊕ Fin mbar) ℝ :=
  Matrix.of fun j k => Sum.elim (fun i => W i j)
    (Sum.elim (fun i => -W i j) (fun j' => if j' = j then (1 : ℝ) else 0)) k

lemma Md_mulVec (v : Fin r ⊕ Fin r ⊕ Fin mbar → ℝ) (j : Fin mbar) :
    (Md W *ᵥ v) j =
      (Wᵀ *ᵥ (fun i => v (Sum.inl i) - v (Sum.inr (Sum.inl i)))) j + v (Sum.inr (Sum.inr j)) := by
  have e1 : ∀ i, Md W j (Sum.inl i) = W i j := fun i => rfl
  have e2 : ∀ i, Md W j (Sum.inr (Sum.inl i)) = -W i j := fun i => rfl
  have e3 : ∀ j', Md W j (Sum.inr (Sum.inr j')) = if j' = j then 1 else 0 := fun j' => rfl
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, e1, e2, e3, Matrix.transpose_apply,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma ad_dot (t : Fin r → ℝ) (v : Fin r ⊕ Fin r ⊕ Fin mbar → ℝ) :
    (Sum.elim (fun i => -t i) (Sum.elim t 0) : Fin r ⊕ Fin r ⊕ Fin mbar → ℝ) ⬝ᵥ v =
      -((fun i => v (Sum.inl i) - v (Sum.inr (Sum.inl i))) ⬝ᵥ t) := by
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, add_zero]
  rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma phi_opt : ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ D W, ∀ t ∈ posW W, ∃ y : Fin mbar → ℝ, ∃ z : Fin r → ℝ,
    0 ≤ y ∧ W *ᵥ y = t ∧ Wᵀ *ᵥ z ≤ u ∧ u ⬝ᵥ y = z ⬝ᵥ t ∧ ‖y‖ ≤ C * ‖t‖ ∧ ‖z‖ ≤ C * ‖u‖ := by
  classical
  obtain ⟨C1, hC10, hC1⟩ := exists_inj_const W
  obtain ⟨C2, hC20, hC2⟩ := exists_inj_const (Md W)
  refine ⟨C1 + 2 * C2, by positivity, fun u hu t ht => ?_⟩
  obtain ⟨y0, hy0, hWy0, z0, hz0, hle0⟩ := strong2 W hu ht
  obtain ⟨y, hy, hWy, hay, hny⟩ := reduce W C1 hC10 hC1 u t (z0 ⬝ᵥ t)
    (fun y hy hWy => by have := weak2 W hy hz0; rwa [hWy] at this) _ y0 hy0 hWy0 le_rfl
  set v0 : Fin r ⊕ Fin r ⊕ Fin mbar → ℝ :=
    Sum.elim (fun i => max (z0 i) 0) (Sum.elim (fun i => max (-z0 i) 0) (u - Wᵀ *ᵥ z0)) with hv0def
  have hv0 : 0 ≤ v0 := by
    intro k
    rcases k with i | i | j
    · simp [hv0def]
    · simp [hv0def]
    · have := hz0 j
      simp [hv0def]
      linarith
  have hz0eq : (fun i => v0 (Sum.inl i) - v0 (Sum.inr (Sum.inl i))) = z0 := by
    funext i
    simp only [hv0def, Sum.elim_inl, Sum.elim_inr]
    rcases le_total (z0 i) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  have hMv0 : Md W *ᵥ v0 = u := by
    funext j
    rw [Md_mulVec, hz0eq]
    simp [hv0def]
  obtain ⟨v, hv, hMv, hav, hnv⟩ := reduce (Md W) C2 hC20 hC2
    (Sum.elim (fun i => -t i) (Sum.elim t 0)) u (-(u ⬝ᵥ y0))
    (fun v hv hMv => by
      rw [ad_dot]
      have hzv : Wᵀ *ᵥ (fun i => v (Sum.inl i) - v (Sum.inr (Sum.inl i))) ≤ u := fun j => by
        have h1 := congrFun hMv j
        rw [Md_mulVec] at h1
        have h2 := hv (Sum.inr (Sum.inr j))
        simp only [Pi.zero_apply] at h2
        linarith
      have := weak2 W hy0 hzv
      rw [hWy0] at this
      linarith) _ v0 hv0 hMv0 le_rfl
  set z : Fin r → ℝ := fun i => v (Sum.inl i) - v (Sum.inr (Sum.inl i)) with hzdef
  have hz : Wᵀ *ᵥ z ≤ u := fun j => by
    have h1 := congrFun hMv j
    rw [Md_mulVec] at h1
    have h2 := hv (Sum.inr (Sum.inr j))
    simp only [Pi.zero_apply] at h2
    show (Wᵀ *ᵥ z) j ≤ u j
    linarith
  have hzt : z0 ⬝ᵥ t ≤ z ⬝ᵥ t := by
    rw [ad_dot, ad_dot, hz0eq] at hav
    linarith
  have hw : z ⬝ᵥ t ≤ u ⬝ᵥ y := by
    have := weak2 W hy hz; rwa [hWy] at this
  refine ⟨y, z, hy, hWy, hz, by linarith, ?_, ?_⟩
  · have : 0 ≤ C2 * ‖t‖ := by positivity
    nlinarith [norm_nonneg t]
  · have hz2 : ‖z‖ ≤ 2 * ‖v‖ := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      have h1 := norm_le_pi_norm v (Sum.inl i)
      have h2 := norm_le_pi_norm v (Sum.inr (Sum.inl i))
      simp only [hzdef, Real.norm_eq_abs] at h1 h2 ⊢
      have := abs_sub (v (Sum.inl i)) (v (Sum.inr (Sum.inl i)))
      linarith
    have : 0 ≤ C1 * ‖u‖ := by positivity
    nlinarith [norm_nonneg u]

noncomputable def phiR (u : Fin mbar → ℝ) (t : Fin r → ℝ) : ℝ := (Phi W u t).toReal

lemma Phi_eq_of_opt {u : Fin mbar → ℝ} {t : Fin r → ℝ} {y : Fin mbar → ℝ} {z : Fin r → ℝ}
    (hy : 0 ≤ y) (hWy : W *ᵥ y = t) (hz : Wᵀ *ᵥ z ≤ u) (heq : u ⬝ᵥ y = z ⬝ᵥ t) :
    Phi W u t = ((u ⬝ᵥ y : ℝ) : EReal) := by
  unfold Phi
  apply le_antisymm
  · exact iInf₂_le y ⟨hy, hWy⟩
  · refine le_iInf₂ fun y' hy' => ?_
    have := weak2 W hy'.1 hz
    rw [hy'.2] at this
    exact EReal.coe_le_coe_iff.2 (by linarith)

lemma phi_facts : ∃ K : ℝ, 0 ≤ K ∧
    (∀ u ∈ D W, ∀ t ∈ posW W, Phi W u t = ((phiR W u t : ℝ) : EReal)) ∧
    (∀ u ∈ D W, ∀ t ∈ posW W, ∃ y : Fin mbar → ℝ, 0 ≤ y ∧ W *ᵥ y = t ∧ phiR W u t = u ⬝ᵥ y) ∧
    (∀ u ∈ D W, ∀ y : Fin mbar → ℝ, 0 ≤ y → phiR W u (W *ᵥ y) ≤ u ⬝ᵥ y) ∧
    (∀ u ∈ D W, ∀ t ∈ posW W, |phiR W u t| ≤ K * (‖u‖ * ‖t‖)) ∧
    (∀ u ∈ D W, ∀ t ∈ posW W, ∀ t' ∈ posW W, |phiR W u t - phiR W u t'| ≤ K * (‖u‖ * ‖t - t'‖)) ∧
    (∀ u ∈ D W, ∀ u' ∈ D W, ∀ t ∈ posW W,
      |phiR W u t - phiR W u' t| ≤ K * (‖t‖ * ‖u - u'‖)) := by
  obtain ⟨C, hC0, hC⟩ := phi_opt W
  have hval : ∀ u ∈ D W, ∀ t ∈ posW W, ∃ y : Fin mbar → ℝ, ∃ z : Fin r → ℝ,
      0 ≤ y ∧ W *ᵥ y = t ∧ Wᵀ *ᵥ z ≤ u ∧ u ⬝ᵥ y = z ⬝ᵥ t ∧ ‖y‖ ≤ C * ‖t‖ ∧ ‖z‖ ≤ C * ‖u‖ ∧
        phiR W u t = u ⬝ᵥ y := by
    intro u hu t ht
    obtain ⟨y, z, hy, hWy, hz, heq, hny, hnz⟩ := hC u hu t ht
    refine ⟨y, z, hy, hWy, hz, heq, hny, hnz, ?_⟩
    unfold phiR
    rw [Phi_eq_of_opt W hy hWy hz heq]
    rfl
  have hle : ∀ u ∈ D W, ∀ y : Fin mbar → ℝ, 0 ≤ y → phiR W u (W *ᵥ y) ≤ u ⬝ᵥ y := by
    intro u hu y hy
    obtain ⟨y1, z1, hy1, hWy1, hz1, heq1, -, -, hphi⟩ := hval u hu _ ⟨y, hy, rfl⟩
    have := weak2 W hy hz1
    rw [hphi, heq1]; exact this
  have hge : ∀ u ∈ D W, ∀ t ∈ posW W, ∀ z : Fin r → ℝ, Wᵀ *ᵥ z ≤ u → z ⬝ᵥ t ≤ phiR W u t := by
    intro u hu t ht z hz
    obtain ⟨y1, z1, hy1, hWy1, hz1, heq1, -, -, hphi⟩ := hval u hu t ht
    have := weak2 W hy1 hz
    rw [hWy1] at this
    rw [hphi]; exact this
  set K := C * ((Fintype.card (Fin r) : ℝ) + Fintype.card (Fin mbar)) with hK
  have hK0 : 0 ≤ K := by positivity
  have cr : (Fintype.card (Fin r) : ℝ) * C ≤ K := by
    rw [hK]; nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (Fin mbar))]
  have cm : (Fintype.card (Fin mbar) : ℝ) * C ≤ K := by
    rw [hK]; nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (Fin r))]
  refine ⟨K, hK0, ?_, ?_, hle, ?_, ?_, ?_⟩
  · intro u hu t ht
    obtain ⟨y, z, hy, hWy, hz, heq, -, -, hphi⟩ := hval u hu t ht
    rw [hphi, Phi_eq_of_opt W hy hWy hz heq]
  · intro u hu t ht
    obtain ⟨y, z, hy, hWy, hz, heq, -, -, hphi⟩ := hval u hu t ht
    exact ⟨y, hy, hWy, hphi⟩
  · intro u hu t ht
    obtain ⟨y, z, hy, hWy, hz, heq, hny, -, hphi⟩ := hval u hu t ht
    rw [hphi]
    have h1 := abs_dot_le u y
    have h2 : ‖u‖ * ‖y‖ ≤ ‖u‖ * (C * ‖t‖) := mul_le_mul_of_nonneg_left hny (norm_nonneg _)
    have h3 : (Fintype.card (Fin mbar) : ℝ) * (‖u‖ * ‖y‖) ≤
        (Fintype.card (Fin mbar) : ℝ) * (‖u‖ * (C * ‖t‖)) :=
      mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
    have h4 : (Fintype.card (Fin mbar) : ℝ) * C * (‖u‖ * ‖t‖) ≤ K * (‖u‖ * ‖t‖) :=
      mul_le_mul_of_nonneg_right cm (by positivity)
    calc |u ⬝ᵥ y| ≤ _ := h1
      _ ≤ _ := h3
      _ = (Fintype.card (Fin mbar) : ℝ) * C * (‖u‖ * ‖t‖) := by ring
      _ ≤ _ := h4
  · intro u hu t ht t' ht'
    have side : ∀ a ∈ posW W, ∀ b ∈ posW W,
        phiR W u a - phiR W u b ≤ K * (‖u‖ * ‖a - b‖) := by
      intro a ha b hb
      obtain ⟨y, z, hy, hWy, hz, heq, -, hnz, hphi⟩ := hval u hu a ha
      have h1 := hge u hu b hb z hz
      have h2 : phiR W u a = z ⬝ᵥ a := by rw [hphi, heq]
      have h3 : phiR W u a - phiR W u b ≤ z ⬝ᵥ (a - b) := by
        rw [dotProduct_sub]; linarith
      have h4 := le_abs_self (z ⬝ᵥ (a - b))
      have h5 := abs_dot_le z (a - b)
      have h6 : ‖z‖ * ‖a - b‖ ≤ C * ‖u‖ * ‖a - b‖ := mul_le_mul_of_nonneg_right hnz (norm_nonneg _)
      have h7 : (Fintype.card (Fin r) : ℝ) * (‖z‖ * ‖a - b‖) ≤
          (Fintype.card (Fin r) : ℝ) * (C * ‖u‖ * ‖a - b‖) :=
        mul_le_mul_of_nonneg_left h6 (Nat.cast_nonneg _)
      have h8 : (Fintype.card (Fin r) : ℝ) * C * (‖u‖ * ‖a - b‖) ≤ K * (‖u‖ * ‖a - b‖) :=
        mul_le_mul_of_nonneg_right cr (by positivity)
      have h9 : (Fintype.card (Fin r) : ℝ) * (C * ‖u‖ * ‖a - b‖) =
          (Fintype.card (Fin r) : ℝ) * C * (‖u‖ * ‖a - b‖) := by ring
      linarith
    rw [abs_le]
    constructor
    · have := side t' ht' t ht
      rw [← norm_neg (t' - t), neg_sub] at this
      linarith
    · exact side t ht t' ht'
  · intro u hu u' hu' t ht
    have side : ∀ a ∈ D W, ∀ b ∈ D W,
        phiR W a t - phiR W b t ≤ K * (‖t‖ * ‖a - b‖) := by
      intro a ha b hb
      obtain ⟨y, z, hy, hWy, hz, heq, hny, -, hphi⟩ := hval b hb t ht
      have h1 := hle a ha y hy
      rw [hWy] at h1
      have h3 : phiR W a t - phiR W b t ≤ (a - b) ⬝ᵥ y := by
        rw [sub_dotProduct, hphi]; linarith
      have h4 := le_abs_self ((a - b) ⬝ᵥ y)
      have h5 := abs_dot_le (a - b) y
      have h6 : ‖a - b‖ * ‖y‖ ≤ ‖a - b‖ * (C * ‖t‖) := mul_le_mul_of_nonneg_left hny (norm_nonneg _)
      have h7 : (Fintype.card (Fin mbar) : ℝ) * (‖a - b‖ * ‖y‖) ≤
          (Fintype.card (Fin mbar) : ℝ) * (‖a - b‖ * (C * ‖t‖)) :=
        mul_le_mul_of_nonneg_left h6 (Nat.cast_nonneg _)
      have h8 : (Fintype.card (Fin mbar) : ℝ) * C * (‖t‖ * ‖a - b‖) ≤ K * (‖t‖ * ‖a - b‖) :=
        mul_le_mul_of_nonneg_right cm (by positivity)
      have h9 : (Fintype.card (Fin mbar) : ℝ) * (‖a - b‖ * (C * ‖t‖)) =
          (Fintype.card (Fin mbar) : ℝ) * C * (‖t‖ * ‖a - b‖) := by ring
      linarith
    rw [abs_le]
    constructor
    · have := side u' hu' u hu
      rw [← norm_neg (u' - u), neg_sub] at this
      linarith
    · exact side u hu u' hu'

end PhiSec


section PartB

open ProbMetricStab.TwoStage

lemma poly_convex {n : ℕ} {Y : Set (EuclideanSpace ℝ (Fin n))} (h : IsPolyhedron Y) :
    Convex ℝ Y := by
  obtain ⟨k, a, b, rfl⟩ := h
  intro x hx y hy p q hp hq hpq i
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  have h1 := mul_le_mul_of_nonneg_left (hx i) hp
  have h2 := mul_le_mul_of_nonneg_left (hy i) hq
  have h3 : p * b i + q * b i = b i := by rw [← add_mul, hpq, one_mul]
  linarith

lemma poly_closed {n : ℕ} {Y : Set (EuclideanSpace ℝ (Fin n))} (h : IsPolyhedron Y) :
    IsClosed Y := by
  obtain ⟨k, a, b, rfl⟩ := h
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_le (continuous_const.inner continuous_id) continuous_const

lemma affine_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E →ᵃ[ℝ] F) :
    ∃ A : ℝ, 0 ≤ A ∧ (∀ ξ ξ', ‖f ξ - f ξ'‖ ≤ A * ‖ξ - ξ'‖) ∧ ∀ ξ, ‖f ξ‖ ≤ A * (1 + ‖ξ‖) := by
  set L := LinearMap.toContinuousLinearMap f.linear with hLdef
  have hL : ∀ v, f.linear v = L v := fun v => rfl
  have hf : ∀ ξ, f ξ = f.linear ξ + f 0 := fun ξ => by
    have := congrFun (AffineMap.decomp f) ξ
    simpa using this
  refine ⟨‖L‖ + ‖f 0‖, by positivity, fun ξ ξ' => ?_, fun ξ => ?_⟩
  · rw [hf ξ, hf ξ', add_sub_add_right_eq_sub, ← map_sub, hL]
    calc ‖L (ξ - ξ')‖ ≤ ‖L‖ * ‖ξ - ξ'‖ := L.le_opNorm _
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [norm_nonneg (f 0)]) (norm_nonneg _)
  · rw [hf ξ, hL]
    have h1 := L.le_opNorm ξ
    calc ‖L ξ + f 0‖ ≤ ‖L ξ‖ + ‖f 0‖ := norm_add_le _ _
      _ ≤ ‖L‖ * ‖ξ‖ + ‖f 0‖ := by linarith
      _ ≤ _ := by nlinarith [norm_nonneg ξ, norm_nonneg (f 0), norm_nonneg L]

lemma ofLp_norm_le {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ‖x.ofLp‖ ≤ ‖x‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun i => by simpa using PiLp.norm_apply_le x i

section Mat
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace

variable {m s r mbar : ℕ} (P : Data m s r mbar)

lemma rhs_bounds : ∃ A : ℝ, 0 ≤ A ∧
    (∀ ξ ξ' x, ‖P.rhs ξ x - P.rhs ξ' x‖ ≤ A * (1 + ‖x‖) * ‖ξ - ξ'‖) ∧
    (∀ ξ x x', ‖P.rhs ξ x - P.rhs ξ x'‖ ≤ A * (1 + ‖ξ‖) * ‖x - x'‖) ∧
    (∀ ξ x, ‖P.rhs ξ x‖ ≤ A * (1 + ‖ξ‖) * (1 + ‖x‖)) := by
  obtain ⟨Ah, hAh0, hAh1, hAh2⟩ := affine_bound P.h
  obtain ⟨AT, hAT0, hAT1, hAT2⟩ := affine_bound P.T
  refine ⟨Ah + AT, by positivity, fun ξ ξ' x => ?_, fun ξ x x' => ?_, fun ξ x => ?_⟩
  · have e : P.rhs ξ x - P.rhs ξ' x = (P.h ξ - P.h ξ') - (P.T ξ - P.T ξ') *ᵥ x.ofLp := by
      simp only [Data.rhs, Matrix.sub_mulVec]; abel
    rw [e]
    have h1 := norm_sub_le (P.h ξ - P.h ξ') ((P.T ξ - P.T ξ') *ᵥ x.ofLp)
    have h2 := Matrix.linfty_opNorm_mulVec (P.T ξ - P.T ξ') x.ofLp
    have h3 := hAT1 ξ ξ'
    have h4 := ofLp_norm_le x
    have h5 := hAh1 ξ ξ'
    have h6 : ‖P.T ξ - P.T ξ'‖ * ‖x.ofLp‖ ≤ (AT * ‖ξ - ξ'‖) * ‖x‖ :=
      mul_le_mul h3 h4 (norm_nonneg _) (by positivity)
    have p1 : 0 ≤ Ah * ‖ξ - ξ'‖ * ‖x‖ := by positivity
    have p2 : 0 ≤ AT * ‖ξ - ξ'‖ := by positivity
    have e2 : (Ah + AT) * (1 + ‖x‖) * ‖ξ - ξ'‖ =
        Ah * ‖ξ - ξ'‖ + (AT * ‖ξ - ξ'‖) * ‖x‖ + (Ah * ‖ξ - ξ'‖ * ‖x‖ + AT * ‖ξ - ξ'‖) := by ring
    rw [e2]
    linarith
  · have e : P.rhs ξ x - P.rhs ξ x' = P.T ξ *ᵥ (x' - x).ofLp := by
      simp only [Data.rhs, WithLp.ofLp_sub, Matrix.mulVec_sub]; abel
    rw [e]
    have h2 := Matrix.linfty_opNorm_mulVec (P.T ξ) (x' - x).ofLp
    have h3 := hAT2 ξ
    have h4 := ofLp_norm_le (x' - x)
    rw [norm_sub_rev] at h4
    have h6 : ‖P.T ξ‖ * ‖(x' - x).ofLp‖ ≤ (AT * (1 + ‖ξ‖)) * ‖x - x'‖ :=
      mul_le_mul h3 h4 (norm_nonneg _) (by positivity)
    have p1 : 0 ≤ Ah * (1 + ‖ξ‖) * ‖x - x'‖ := by positivity
    have e2 : (Ah + AT) * (1 + ‖ξ‖) * ‖x - x'‖ =
        (AT * (1 + ‖ξ‖)) * ‖x - x'‖ + Ah * (1 + ‖ξ‖) * ‖x - x'‖ := by ring
    rw [e2]
    linarith
  · have h1 := norm_sub_le (P.h ξ) (P.T ξ *ᵥ x.ofLp)
    have h2 := Matrix.linfty_opNorm_mulVec (P.T ξ) x.ofLp
    have h3 := hAT2 ξ
    have h4 := ofLp_norm_le x
    have h5 := hAh2 ξ
    have h6 : ‖P.T ξ‖ * ‖x.ofLp‖ ≤ (AT * (1 + ‖ξ‖)) * ‖x‖ :=
      mul_le_mul h3 h4 (norm_nonneg _) (by positivity)
    show ‖P.h ξ - P.T ξ *ᵥ x.ofLp‖ ≤ _
    have p1 : 0 ≤ Ah * (1 + ‖ξ‖) * ‖x‖ := by positivity
    have p2 : 0 ≤ AT * (1 + ‖ξ‖) := by positivity
    have e2 : (Ah + AT) * (1 + ‖ξ‖) * (1 + ‖x‖) =
        Ah * (1 + ‖ξ‖) + (AT * (1 + ‖ξ‖)) * ‖x‖ + (Ah * (1 + ‖ξ‖) * ‖x‖ + AT * (1 + ‖ξ‖)) := by ring
    rw [e2]
    linarith

end Mat

variable {m s r mbar : ℕ} (P : Data m s r mbar)

/-- The real-valued integrand `c x + Φ(q(ξ), h(ξ) − T(ξ) x)`. -/
noncomputable def gR (ξ : EuclideanSpace ℝ (Fin s)) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  inner ℝ P.c x + phiR P.W (P.q ξ) (P.rhs ξ x)

lemma rhs_comb (ξ : EuclideanSpace ℝ (Fin s)) (a b : EuclideanSpace ℝ (Fin m)) (p : ℝ) :
    P.rhs ξ ((1 - p) • a + p • b) = (1 - p) • P.rhs ξ a + p • P.rhs ξ b := by
  funext i
  simp only [Data.rhs, WithLp.ofLp_add, WithLp.ofLp_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma g_facts (hA1 : P.A1) : ∃ K : ℝ, 0 ≤ K ∧
    (∀ ξ ∈ P.Ξ, ∀ x ∈ P.X, P.f0 ξ x = ((gR P ξ x : ℝ) : EReal)) ∧
    (∀ ξ ∈ P.Ξ, ∀ ξ' ∈ P.Ξ, ∀ x ∈ P.X,
      |gR P ξ x - gR P ξ' x| ≤ K * (1 + ‖x‖) * (max 1 (max ‖ξ‖ ‖ξ'‖) * ‖ξ - ξ'‖)) ∧
    (∀ ξ ∈ P.Ξ, ∀ x ∈ P.X, ∀ x' ∈ P.X, |gR P ξ x - gR P ξ x'| ≤ K * (1 + ‖ξ‖) ^ 2 * ‖x - x'‖) ∧
    (∀ ξ ∈ P.Ξ, ∀ x ∈ P.X, |gR P ξ x| ≤ K * (1 + ‖x‖) * (1 + ‖ξ‖) ^ 2) ∧
    (∀ ξ ∈ P.Ξ, ∀ a ∈ P.X, ∀ b ∈ P.X, ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      gR P ξ ((1 - p) • a + p • b) ≤ (1 - p) * gR P ξ a + p * gR P ξ b) := by
  obtain ⟨K0, hK00, hval, hopt, hle, hbd, hlt, hlu⟩ := phi_facts P.W
  obtain ⟨Aq, hAq0, hAq1, hAq2⟩ := affine_bound P.q
  obtain ⟨Ar, hAr0, hAr1, hAr2, hAr3⟩ := rhs_bounds P
  set K := ‖P.c‖ + 4 * K0 * Aq * Ar + 1 with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hKc : ‖P.c‖ ≤ K := by nlinarith [mul_nonneg (mul_nonneg hK00 hAq0) hAr0]
  have hKp : K0 * Aq * Ar * 4 ≤ K := by nlinarith [norm_nonneg P.c]
  refine ⟨K, hK0, ?_, ?_, ?_, ?_, ?_⟩
  · intro ξ hξ x hx
    obtain ⟨h1, h2⟩ := hA1 ξ hξ x hx
    simp only [Data.f0, h1, h2, and_self, if_true, gR]
    rw [hval _ h2 _ h1, EReal.coe_add]
  · intro ξ hξ ξ' hξ' x hx
    obtain ⟨h1, h2⟩ := hA1 ξ hξ x hx
    obtain ⟨h1', h2'⟩ := hA1 ξ' hξ' x hx
    set M := max 1 (max ‖ξ‖ ‖ξ'‖) with hM
    have hM1 : 1 ≤ M := le_max_left _ _
    have hMa : ‖ξ‖ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
    have hMb : ‖ξ'‖ ≤ M := (le_max_right _ _).trans (le_max_right _ _)
    have e : gR P ξ x - gR P ξ' x =
        (phiR P.W (P.q ξ) (P.rhs ξ x) - phiR P.W (P.q ξ) (P.rhs ξ' x)) +
        (phiR P.W (P.q ξ) (P.rhs ξ' x) - phiR P.W (P.q ξ') (P.rhs ξ' x)) := by
      simp only [gR]; ring
    rw [e]
    have t1 := hlt _ h2 _ h1 _ h1'
    have t2 := hlu _ h2 _ h2' _ h1'
    have q1 : ‖P.q ξ‖ ≤ Aq * (2 * M) := by
      have := hAq2 ξ; nlinarith
    have r1 := hAr1 ξ ξ' x
    have r2 : ‖P.rhs ξ' x‖ ≤ Ar * (2 * M) * (1 + ‖x‖) := by
      have := hAr3 ξ' x
      have : Ar * (1 + ‖ξ'‖) * (1 + ‖x‖) ≤ Ar * (2 * M) * (1 + ‖x‖) := by
        gcongr; linarith
      linarith
    have q2 := hAq1 ξ ξ'
    have b1 : K0 * (‖P.q ξ‖ * ‖P.rhs ξ x - P.rhs ξ' x‖) ≤
        K0 * ((Aq * (2 * M)) * (Ar * (1 + ‖x‖) * ‖ξ - ξ'‖)) := by gcongr
    have b2 : K0 * (‖P.rhs ξ' x‖ * ‖P.q ξ - P.q ξ'‖) ≤
        K0 * ((Ar * (2 * M) * (1 + ‖x‖)) * (Aq * ‖ξ - ξ'‖)) := by gcongr
    have b3 : K0 * ((Aq * (2 * M)) * (Ar * (1 + ‖x‖) * ‖ξ - ξ'‖)) +
        K0 * ((Ar * (2 * M) * (1 + ‖x‖)) * (Aq * ‖ξ - ξ'‖)) =
        (K0 * Aq * Ar * 4) * (1 + ‖x‖) * (M * ‖ξ - ξ'‖) := by ring
    have b4 : (K0 * Aq * Ar * 4) * (1 + ‖x‖) * (M * ‖ξ - ξ'‖) ≤ K * (1 + ‖x‖) * (M * ‖ξ - ξ'‖) := by
      gcongr
    calc _ ≤ |phiR P.W (P.q ξ) (P.rhs ξ x) - phiR P.W (P.q ξ) (P.rhs ξ' x)| +
          |phiR P.W (P.q ξ) (P.rhs ξ' x) - phiR P.W (P.q ξ') (P.rhs ξ' x)| := abs_add_le _ _
      _ ≤ _ := by linarith
  · intro ξ hξ x hx x' hx'
    obtain ⟨h1, h2⟩ := hA1 ξ hξ x hx
    obtain ⟨h1', -⟩ := hA1 ξ hξ x' hx'
    have e : gR P ξ x - gR P ξ x' = inner ℝ P.c (x - x') +
        (phiR P.W (P.q ξ) (P.rhs ξ x) - phiR P.W (P.q ξ) (P.rhs ξ x')) := by
      simp only [gR, inner_sub_right]; ring
    rw [e]
    have t1 := hlt _ h2 _ h1 _ h1'
    have c1 : |inner ℝ P.c (x - x')| ≤ ‖P.c‖ * ‖x - x'‖ := abs_real_inner_le_norm _ _
    have q1 := hAq2 ξ
    have r1 := hAr2 ξ x x'
    have b1 : K0 * (‖P.q ξ‖ * ‖P.rhs ξ x - P.rhs ξ x'‖) ≤
        K0 * ((Aq * (1 + ‖ξ‖)) * (Ar * (1 + ‖ξ‖) * ‖x - x'‖)) := by gcongr
    have hξ1 : 1 ≤ (1 + ‖ξ‖) ^ 2 := by nlinarith [norm_nonneg ξ]
    have b2 : ‖P.c‖ * ‖x - x'‖ ≤ K * (1 + ‖ξ‖) ^ 2 * ‖x - x'‖ * (1 / 2) * 2 := by
      have : ‖P.c‖ * ‖x - x'‖ ≤ K * 1 * ‖x - x'‖ := by nlinarith [norm_nonneg (x - x')]
      have : K * 1 * ‖x - x'‖ ≤ K * (1 + ‖ξ‖) ^ 2 * ‖x - x'‖ := by gcongr
      linarith
    have b3 : K0 * ((Aq * (1 + ‖ξ‖)) * (Ar * (1 + ‖ξ‖) * ‖x - x'‖)) =
        (K0 * Aq * Ar) * (1 + ‖ξ‖) ^ 2 * ‖x - x'‖ := by ring
    have b4 : (K0 * Aq * Ar) * (1 + ‖ξ‖) ^ 2 * ‖x - x'‖ + ‖P.c‖ * ‖x - x'‖ ≤
        K * (1 + ‖ξ‖) ^ 2 * ‖x - x'‖ := by
      have hK' : K0 * Aq * Ar + ‖P.c‖ ≤ K := by nlinarith [mul_nonneg (mul_nonneg hK00 hAq0) hAr0]
      have : (K0 * Aq * Ar + ‖P.c‖) * ((1 + ‖ξ‖) ^ 2 * ‖x - x'‖) ≤ K * ((1 + ‖ξ‖) ^ 2 * ‖x - x'‖) := by
        gcongr
      have : ‖P.c‖ * ‖x - x'‖ ≤ ‖P.c‖ * ((1 + ‖ξ‖) ^ 2 * ‖x - x'‖) := by
        have : ‖x - x'‖ ≤ (1 + ‖ξ‖) ^ 2 * ‖x - x'‖ := by nlinarith [norm_nonneg (x - x')]
        gcongr
      nlinarith
    calc _ ≤ |inner ℝ P.c (x - x')| +
          |phiR P.W (P.q ξ) (P.rhs ξ x) - phiR P.W (P.q ξ) (P.rhs ξ x')| := abs_add_le _ _
      _ ≤ _ := by linarith
  · intro ξ hξ x hx
    obtain ⟨h1, h2⟩ := hA1 ξ hξ x hx
    have t1 := hbd _ h2 _ h1
    have c1 : |inner ℝ P.c x| ≤ ‖P.c‖ * ‖x‖ := abs_real_inner_le_norm _ _
    have q1 := hAq2 ξ
    have r1 := hAr3 ξ x
    have b1 : K0 * (‖P.q ξ‖ * ‖P.rhs ξ x‖) ≤
        K0 * ((Aq * (1 + ‖ξ‖)) * (Ar * (1 + ‖ξ‖) * (1 + ‖x‖))) := by gcongr
    have b3 : K0 * ((Aq * (1 + ‖ξ‖)) * (Ar * (1 + ‖ξ‖) * (1 + ‖x‖))) =
        (K0 * Aq * Ar) * ((1 + ‖x‖) * (1 + ‖ξ‖) ^ 2) := by ring
    have hξ1 : 1 ≤ (1 + ‖ξ‖) ^ 2 := by nlinarith [norm_nonneg ξ]
    have b2 : ‖P.c‖ * ‖x‖ ≤ ‖P.c‖ * ((1 + ‖x‖) * (1 + ‖ξ‖) ^ 2) := by
      have : ‖x‖ ≤ (1 + ‖x‖) * (1 + ‖ξ‖) ^ 2 := by nlinarith [norm_nonneg x]
      gcongr
    have hK' : K0 * Aq * Ar + ‖P.c‖ ≤ K := by nlinarith [mul_nonneg (mul_nonneg hK00 hAq0) hAr0]
    have b4 : (K0 * Aq * Ar + ‖P.c‖) * ((1 + ‖x‖) * (1 + ‖ξ‖) ^ 2) ≤
        K * ((1 + ‖x‖) * (1 + ‖ξ‖) ^ 2) := by gcongr
    have e : gR P ξ x = inner ℝ P.c x + phiR P.W (P.q ξ) (P.rhs ξ x) := rfl
    rw [e]
    calc _ ≤ |inner ℝ P.c x| + |phiR P.W (P.q ξ) (P.rhs ξ x)| := abs_add_le _ _
      _ ≤ _ := by nlinarith
  · intro ξ hξ a ha b hb p hp0 hp1
    obtain ⟨h1a, h2⟩ := hA1 ξ hξ a ha
    obtain ⟨h1b, -⟩ := hA1 ξ hξ b hb
    obtain ⟨ya, hya, hWya, hpa⟩ := hopt _ h2 _ h1a
    obtain ⟨yb, hyb, hWyb, hpb⟩ := hopt _ h2 _ h1b
    have hy : 0 ≤ (1 - p) • ya + p • yb := by
      intro j
      have := hya j; have := hyb j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      have : 0 ≤ (1 - p) * ya j := mul_nonneg (by linarith) (hya j)
      have : 0 ≤ p * yb j := mul_nonneg hp0 (hyb j)
      linarith
    have hW : P.W *ᵥ ((1 - p) • ya + p • yb) = P.rhs ξ ((1 - p) • a + p • b) := by
      rw [rhs_comb, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hWya, hWyb]
    have h3 := hle _ h2 _ hy
    rw [hW] at h3
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← hpa, ← hpb] at h3
    simp only [gR, inner_add_right, inner_smul_right]
    nlinarith

end PartB


section PartC

open ProbMetricStab.TwoStage MeasureTheory
open scoped ENNReal

lemma expect_eq_coe {α : Type*} [MeasurableSpace α] (Q : Measure α) (g : α → EReal) (G : α → ℝ)
    (hG : Integrable G Q) (hgG : ∀ᵐ a ∂Q, g a = ((G a : ℝ) : EReal)) :
    DupacovaWets.Consistency.expect Q g = ((∫ a, G a ∂Q : ℝ) : EReal) := by
  have e1 : ∫⁻ a, (g a).toENNReal ∂Q = ∫⁻ a, ENNReal.ofReal (G a) ∂Q :=
    lintegral_congr_ae (hgG.mono fun a ha => by
      show (g a).toENNReal = ENNReal.ofReal (G a)
      rw [ha]; rfl)
  have e2 : ∫⁻ a, (-g a).toENNReal ∂Q = ∫⁻ a, ENNReal.ofReal (-G a) ∂Q :=
    lintegral_congr_ae (hgG.mono fun a ha => by
      show (-g a).toENNReal = ENNReal.ofReal (-G a)
      rw [ha, ← EReal.coe_neg]; rfl)
  have f1 := hG.lintegral_lt_top
  have f2 : ∫⁻ a, ENNReal.ofReal (-G a) ∂Q < ∞ := hG.neg.lintegral_lt_top
  unfold DupacovaWets.Consistency.expect
  rw [e1, e2, if_neg f1.ne, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hG,
    EReal.coe_sub, EReal.coe_ennreal_toReal f1.ne, EReal.coe_ennreal_toReal f2.ne]

lemma sq_integrable {s : ℕ} {Ξ : Set (EuclideanSpace ℝ (Fin s))}
    {ν : Measure (EuclideanSpace ℝ (Fin s))} (hν : ν ∈ Pp Ξ 2) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin s) => ‖ξ‖ ^ 2) (ν.restrict Ξ) := by
  refine ⟨(continuous_norm.pow 2).aestronglyMeasurable, ?_⟩
  have h := hν.2
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (le_of_eq ?_) h
  refine lintegral_congr fun ξ => ?_
  have e : (‖ξ‖₊ : ℝ≥0∞) ^ (2:ℝ) = ENNReal.ofReal (‖ξ‖ ^ 2) := by
    rw [ENNReal.rpow_two, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rfl
  rw [e, Real.enorm_eq_ofReal (by positivity)]

variable {m s r mbar : ℕ} (P : Data m s r mbar)

/-- The real expectation `∫_Ξ g(ξ, x) ν(dξ)`. -/
noncomputable def Ival (ν : Measure (EuclideanSpace ℝ (Fin s))) (x : EuclideanSpace ℝ (Fin m)) :
    ℝ :=
  ∫ ξ in P.Ξ, gR P ξ x ∂ν

lemma C_facts (hP : P.Standing) (hA1 : P.A1) : ∃ K : ℝ, 0 ≤ K ∧
    (∀ ν ∈ Pp P.Ξ 2, ∀ x ∈ P.X, objective P.Ξ P.f0 ν x = ((Ival P ν x : ℝ) : EReal)) ∧
    (∀ ν ∈ Pp P.Ξ 2, ∃ Lν : ℝ, ∀ x ∈ P.X, ∀ x' ∈ P.X,
      |Ival P ν x - Ival P ν x'| ≤ Lν * ‖x - x'‖) ∧
    (∀ ν ∈ Pp P.Ξ 2, ∀ a ∈ P.X, ∀ b ∈ P.X, ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      Ival P ν ((1 - p) • a + p • b) ≤ (1 - p) * Ival P ν a + p * Ival P ν b) ∧
    (∀ μ ∈ Pp P.Ξ 2, ∀ ν ∈ Pp P.Ξ 2, zetaP P.Ξ 2 μ ν ≠ ⊤ → ∀ x ∈ P.X,
      |Ival P μ x - Ival P ν x| ≤ (K * (1 + ‖x‖) + 1) * (zetaP P.Ξ 2 μ ν).toReal) := by
  obtain ⟨K, hK0, hf0, hlξ, hlx, hbd, hcv⟩ := g_facts P hA1
  have hΞm : MeasurableSet P.Ξ := (poly_closed hP.2.2).measurableSet
  have hcont : ∀ x ∈ P.X, ContinuousOn (fun ξ => gR P ξ x) P.Ξ := by
    intro x hx
    rw [Metric.continuousOn_iff]
    intro b hb ε hε
    set Kx := K * (1 + ‖x‖) with hKx
    have hKx0 : 0 ≤ Kx := mul_nonneg hK0 (by positivity)
    have hpos : 0 < Kx * (‖b‖ + 2) + 1 := by
      have := mul_nonneg hKx0 (by positivity : (0:ℝ) ≤ ‖b‖ + 2); linarith
    refine ⟨min 1 (ε / (Kx * (‖b‖ + 2) + 1)), lt_min one_pos (div_pos hε hpos), fun a ha hab => ?_⟩
    rw [Real.dist_eq]
    rw [dist_eq_norm] at hab
    have hab1 : ‖a - b‖ < 1 := lt_of_lt_of_le hab (min_le_left _ _)
    have hab2 : ‖a - b‖ < ε / (Kx * (‖b‖ + 2) + 1) := lt_of_lt_of_le hab (min_le_right _ _)
    have hna : ‖a‖ ≤ ‖b‖ + 1 := by
      have := norm_sub_norm_le a b
      linarith
    have hM : max 1 (max ‖a‖ ‖b‖) ≤ ‖b‖ + 2 :=
      max_le (by linarith [norm_nonneg b]) (max_le (by linarith) (by linarith))
    have h1 := hlξ a ha b hb x hx
    have h2 : Kx * (max 1 (max ‖a‖ ‖b‖) * ‖a - b‖) ≤ Kx * ((‖b‖ + 2) * ‖a - b‖) := by gcongr
    have h3 : (Kx * (‖b‖ + 2)) * ‖a - b‖ ≤ (Kx * (‖b‖ + 2) + 1) * ‖a - b‖ := by
      nlinarith [norm_nonneg (a - b)]
    have h4 : (Kx * (‖b‖ + 2) + 1) * ‖a - b‖ < ε := by
      rw [lt_div_iff₀ hpos] at hab2
      linarith [mul_comm (Kx * (‖b‖ + 2) + 1) ‖a - b‖]
    calc |gR P a x - gR P b x| ≤ K * (1 + ‖x‖) * (max 1 (max ‖a‖ ‖b‖) * ‖a - b‖) := h1
      _ = Kx * (max 1 (max ‖a‖ ‖b‖) * ‖a - b‖) := by rw [hKx]
      _ ≤ _ := h2
      _ = (Kx * (‖b‖ + 2)) * ‖a - b‖ := by ring
      _ < ε := by linarith
  have hint : ∀ ν ∈ Pp P.Ξ 2, ∀ x ∈ P.X, Integrable (fun ξ => gR P ξ x) (ν.restrict P.Ξ) := by
    intro ν hν x hx
    haveI := hν.1.1
    have hb : Integrable (fun ξ : EuclideanSpace ℝ (Fin s) =>
        K * (1 + ‖x‖) * (2 * (1 + ‖ξ‖ ^ 2))) (ν.restrict P.Ξ) :=
      (((integrable_const (1:ℝ)).add (sq_integrable hν)).const_mul 2).const_mul _
    refine hb.mono' ((hcont x hx).aestronglyMeasurable hΞm) ?_
    refine (ae_restrict_iff' hΞm).2 (Filter.Eventually.of_forall fun ξ hξ => ?_)
    rw [Real.norm_eq_abs]
    have h1 := hbd ξ hξ x hx
    have h2 : (1 + ‖ξ‖) ^ 2 ≤ 2 * (1 + ‖ξ‖ ^ 2) := by nlinarith [sq_nonneg (‖ξ‖ - 1)]
    have h3 : K * (1 + ‖x‖) * (1 + ‖ξ‖) ^ 2 ≤ K * (1 + ‖x‖) * (2 * (1 + ‖ξ‖ ^ 2)) := by
      have : 0 ≤ K * (1 + ‖x‖) := mul_nonneg hK0 (by positivity)
      exact mul_le_mul_of_nonneg_left h2 this
    linarith
  refine ⟨K, hK0, ?_, ?_, ?_, ?_⟩
  · intro ν hν x hx
    unfold objective Ival
    exact expect_eq_coe _ _ _ (hint ν hν x hx)
      ((ae_restrict_iff' hΞm).2 (Filter.Eventually.of_forall fun ξ hξ => hf0 ξ hξ x hx))
  · intro ν hν
    haveI := hν.1.1
    refine ⟨∫ ξ in P.Ξ, K * (2 * (1 + ‖ξ‖ ^ 2)) ∂ν, fun x hx x' hx' => ?_⟩
    have hb : Integrable (fun ξ : EuclideanSpace ℝ (Fin s) =>
        K * (2 * (1 + ‖ξ‖ ^ 2)) * ‖x - x'‖) (ν.restrict P.Ξ) :=
      ((((integrable_const (1:ℝ)).add (sq_integrable hν)).const_mul 2).const_mul K).mul_const _
    unfold Ival
    rw [← integral_sub (hint ν hν x hx) (hint ν hν x' hx'), ← integral_mul_const,
      ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hb
      ((ae_restrict_iff' hΞm).2 (Filter.Eventually.of_forall fun ξ hξ => ?_))
    rw [Real.norm_eq_abs]
    have h1 := hlx ξ hξ x hx x' hx'
    have h2 : (1 + ‖ξ‖) ^ 2 ≤ 2 * (1 + ‖ξ‖ ^ 2) := by nlinarith [sq_nonneg (‖ξ‖ - 1)]
    have h3 : K * (1 + ‖ξ‖) ^ 2 * ‖x - x'‖ ≤ K * (2 * (1 + ‖ξ‖ ^ 2)) * ‖x - x'‖ := by
      have := mul_le_mul_of_nonneg_left h2 hK0
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    linarith
  · intro ν hν a ha b hb p hp0 hp1
    have hXc := poly_convex hP.1
    have hab : (1 - p) • a + p • b ∈ P.X := hXc ha hb (by linarith) hp0 (by ring)
    unfold Ival
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
    · refine integral_mono_ae (hint ν hν _ hab) ?_ ?_
      · exact ((hint ν hν a ha).const_mul _).add ((hint ν hν b hb).const_mul _)
      · exact (ae_restrict_iff' hΞm).2
          (Filter.Eventually.of_forall fun ξ hξ => hcv ξ hξ a ha b hb p hp0 hp1)
    · exact (hint ν hν a ha).const_mul _
    · exact (hint ν hν b hb).const_mul _
  · intro μ hμ ν hν hζ x hx
    set ℓ := K * (1 + ‖x‖) + 1 with hℓ
    have hℓ0 : 0 < ℓ := by
      have : 0 ≤ K * (1 + ‖x‖) := mul_nonneg hK0 (by positivity)
      linarith
    set f : EuclideanSpace ℝ (Fin s) → ℝ := fun ξ => gR P ξ x / ℓ with hfdef
    have hfF : f ∈ Fp P.Ξ 2 := by
      intro ξ hξ ξ' hξ'
      simp only [show (2:ℝ) - 1 = 1 by norm_num, Real.rpow_one]
      have h1 := hlξ ξ hξ ξ' hξ' x hx
      have hM : 0 ≤ max 1 (max ‖ξ‖ ‖ξ'‖) * ‖ξ - ξ'‖ := by positivity
      have h2 : K * (1 + ‖x‖) * (max 1 (max ‖ξ‖ ‖ξ'‖) * ‖ξ - ξ'‖) ≤
          ℓ * (max 1 (max ‖ξ‖ ‖ξ'‖) * ‖ξ - ξ'‖) := by
        rw [hℓ]; nlinarith
      simp only [hfdef]
      rw [← sub_div, abs_div, abs_of_pos hℓ0, div_le_iff₀ hℓ0]
      linarith [mul_comm ℓ (max 1 (max ‖ξ‖ ‖ξ'‖) * ‖ξ - ξ'‖)]
    have hfμ : IntegrableOn f P.Ξ μ := (hint μ hμ x hx).div_const ℓ
    have hfν : IntegrableOn f P.Ξ ν := (hint ν hν x hx).div_const ℓ
    have h1 : zetaTerm P.Ξ μ ν f ≤ zetaP P.Ξ 2 μ ν :=
      le_iSup₂ (f := fun f (_ : f ∈ Fp P.Ξ 2) => zetaTerm P.Ξ μ ν f) f hfF
    rw [zetaTerm, if_pos ⟨hfμ, hfν⟩, Real.enorm_eq_ofReal_abs,
      ENNReal.ofReal_le_iff_le_toReal hζ] at h1
    simp only [hfdef, integral_div] at h1
    rw [← sub_div, abs_div, abs_of_pos hℓ0, div_le_iff₀ hℓ0] at h1
    unfold Ival
    linarith [mul_comm ℓ (zetaP P.Ξ 2 μ ν).toReal]

end PartC

section PartD

open ProbMetricStab.TwoStage MeasureTheory Metric
open scoped ENNReal

theorem main33 {m s r mbar : ℕ} (P : Data m s r mbar) (hP : P.Standing) (hA1 : P.A1)
    (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin s))) (hA2 : P.A2 μ)
    (U : Set (EuclideanSpace ℝ (Fin m)))
    (hS : (S P.X P.Ξ P.f0 μ).Nonempty) (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    (hSU : S P.X P.Ξ P.f0 μ ⊆ U) :
    ∃ L δ : ℝ, 0 < L ∧ 0 < δ ∧ ∀ ν : MeasureTheory.Measure (EuclideanSpace ℝ (Fin s)),
      ν ∈ Pp P.Ξ 2 → zetaP P.Ξ 2 μ ν < ENNReal.ofReal δ →
        (v P.X P.Ξ P.f0 μ ≠ ⊤ ∧ v P.X P.Ξ P.f0 μ ≠ ⊥ ∧
          v P.X P.Ξ P.f0 ν ≠ ⊤ ∧ v P.X P.Ξ P.f0 ν ≠ ⊥ ∧
          |(v P.X P.Ξ P.f0 μ).toReal - (v P.X P.Ξ P.f0 ν).toReal| ≤
            L * (zetaP P.Ξ 2 μ ν).toReal) ∧
        (S P.X P.Ξ P.f0 ν).Nonempty ∧
        ∀ x ∈ S P.X P.Ξ P.f0 ν, ∃ y ∈ S P.X P.Ξ P.f0 μ,
          edist x y ≤ Psi P.X P.Ξ P.f0 μ U (ENNReal.ofReal L * zetaP P.Ξ 2 μ ν) := by
  obtain ⟨K, hK0, hobj, hlip, hconv, hzeta⟩ := C_facts P hP hA1
  have hXc : Convex ℝ P.X := poly_convex hP.1
  have hXcl : IsClosed P.X := poly_closed hP.1
  have hv_eq : ∀ ν ∈ Pp P.Ξ 2, v P.X P.Ξ P.f0 ν = ⨅ x ∈ P.X, ((Ival P ν x : ℝ) : EReal) := by
    intro ν hν
    unfold v
    exact iInf_congr fun x => iInf_congr fun hx => hobj ν hν x hx
  have hcontI : ∀ ν ∈ Pp P.Ξ 2, ContinuousOn (Ival P ν) P.X := by
    intro ν hν
    obtain ⟨Lν, hLν⟩ := hlip ν hν
    rw [Metric.continuousOn_iff]
    intro b hb ε hε
    have hp : 0 < |Lν| + 1 := by positivity
    refine ⟨ε / (|Lν| + 1), div_pos hε hp, fun a ha hab => ?_⟩
    rw [Real.dist_eq]
    rw [dist_eq_norm] at hab
    have h1 := hLν a ha b hb
    have h2 : Lν * ‖a - b‖ ≤ (|Lν| + 1) * ‖a - b‖ := by
      have := le_abs_self Lν
      nlinarith [norm_nonneg (a - b)]
    have h3 : (|Lν| + 1) * ‖a - b‖ < ε := by
      rw [lt_div_iff₀ hp] at hab
      linarith [mul_comm (|Lν| + 1) ‖a - b‖]
    linarith
  have hv_min : ∀ ν ∈ Pp P.Ξ 2, ∀ x0 ∈ P.X, (∀ x ∈ P.X, Ival P ν x0 ≤ Ival P ν x) →
      v P.X P.Ξ P.f0 ν = ((Ival P ν x0 : ℝ) : EReal) := by
    intro ν hν x0 hx0 hmin
    rw [hv_eq ν hν]
    apply le_antisymm
    · exact iInf₂_le x0 hx0
    · exact le_iInf₂ fun x hx => EReal.coe_le_coe_iff.2 (hmin x hx)
  have hμ : μ ∈ Pp P.Ξ 2 := hA2
  obtain ⟨xs, hxsS⟩ := hS
  have hxsX : xs ∈ P.X := hxsS.1
  have hmin_mu : ∀ x ∈ P.X, Ival P μ xs ≤ Ival P μ x := by
    intro x hx
    have h1 := hxsS.2
    rw [hobj μ hμ xs hxsX, hv_eq μ hμ] at h1
    have h2 : (⨅ y ∈ P.X, ((Ival P μ y : ℝ) : EReal)) ≤ ((Ival P μ x : ℝ) : EReal) :=
      iInf₂_le x hx
    rw [← h1] at h2
    exact EReal.coe_le_coe_iff.1 h2
  set mμ := Ival P μ xs with hmμ
  have hvμ : v P.X P.Ξ P.f0 μ = ((mμ : ℝ) : EReal) := hv_min μ hμ xs hxsX hmin_mu
  have hSμ : S P.X P.Ξ P.f0 μ = P.X ∩ Ival P μ ⁻¹' {mμ} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, hx2⟩
      refine ⟨hx, ?_⟩
      rw [hobj μ hμ x hx, hvμ] at hx2
      exact_mod_cast hx2
    · rintro ⟨hx, hx2⟩
      refine ⟨hx, ?_⟩
      rw [hobj μ hμ x hx, hvμ, hx2]
  have hSμ_closed : IsClosed (S P.X P.Ξ P.f0 μ) := by
    rw [hSμ]
    exact (hcontI μ hμ).preimage_isClosed_of_isClosed hXcl isClosed_singleton
  have hSμ_cpt : IsCompact (S P.X P.Ξ P.f0 μ) :=
    Metric.isCompact_of_isClosed_isBounded hSμ_closed (hUb.subset hSU)
  have hSμne : (S P.X P.Ξ P.f0 μ).Nonempty := ⟨xs, hxsS⟩
  obtain ⟨δ0, hδ0, hthick⟩ := hSμ_cpt.exists_cthickening_subset_open hUo hSU
  set ε := δ0 / 2 with hεdef
  have hε0 : 0 < ε := by positivity
  set Kε := {x | x ∈ P.X ∧ x ∈ closure U ∧
    ENNReal.ofReal ε ≤ infEDist x (S P.X P.Ξ P.f0 μ)} with hKεdef
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Kε, c ≤ Ival P μ x - mμ := by
    by_cases hKe : Kε.Nonempty
    · have hKcl : IsClosed Kε :=
        hXcl.inter (isClosed_closure.inter (isClosed_le continuous_const continuous_infEDist))
      have hKcpt : IsCompact Kε :=
        Metric.isCompact_of_isClosed_isBounded hKcl (hUb.closure.subset fun x hx => hx.2.1)
      obtain ⟨xk, hxk, hxkmin⟩ := hKcpt.exists_isMinOn hKe ((hcontI μ hμ).mono fun x hx => hx.1)
      have hne : Ival P μ xk ≠ mμ := by
        intro heq
        have hmem : xk ∈ S P.X P.Ξ P.f0 μ := by rw [hSμ]; exact ⟨hxk.1, heq⟩
        have h1 := hxk.2.2
        rw [infEDist_zero_of_mem hmem, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1
        linarith
      have h2 := hmin_mu xk hxk.1
      refine ⟨Ival P μ xk - mμ, sub_pos.2 (lt_of_le_of_ne h2 (Ne.symm hne)), fun x hx => ?_⟩
      have := isMinOn_iff.1 hxkmin x hx
      linarith
    · exact ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hKe⟩
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hUb.closure
  set L := K * (1 + |R|) + 1 with hLdef
  have hL0 : 0 < L := by
    have : 0 ≤ K * (1 + |R|) := mul_nonneg hK0 (by positivity)
    linarith
  have hLx : ∀ x ∈ closure U, K * (1 + ‖x‖) + 1 ≤ L := by
    intro x hx
    have h1 : ‖x‖ ≤ |R| := (hR x hx).trans (le_abs_self R)
    have : K * (1 + ‖x‖) ≤ K * (1 + |R|) := mul_le_mul_of_nonneg_left (by linarith) hK0
    linarith
  set δ := c / (4 * L) with hδdef
  have hδ0 : 0 < δ := div_pos hc0 (by positivity)
  refine ⟨L, δ, hL0, hδ0, fun ν hν hζlt => ?_⟩
  have hζ : zetaP P.Ξ 2 μ ν ≠ ⊤ := ne_top_of_lt hζlt
  set ζ := (zetaP P.Ξ 2 μ ν).toReal with hζdef
  have hζ0 : 0 ≤ ζ := ENNReal.toReal_nonneg
  have hζδ : ζ < δ := by
    have := (ENNReal.toReal_lt_toReal hζ ENNReal.ofReal_ne_top).2 hζlt
    rwa [ENNReal.toReal_ofReal hδ0.le] at this
  set η := L * ζ with hηdef
  have hη0 : 0 ≤ η := mul_nonneg hL0.le hζ0
  have hηc : 4 * η < c := by
    have h1 : L * ζ < L * δ := mul_lt_mul_of_pos_left hζδ hL0
    have h2 : L * δ = c / 4 := by
      rw [hδdef]; field_simp
    linarith
  have hdiff : ∀ x ∈ P.X, x ∈ closure U → |Ival P μ x - Ival P ν x| ≤ η := by
    intro x hx hxU
    have := hzeta μ hμ ν hν hζ x hx
    calc _ ≤ (K * (1 + ‖x‖) + 1) * ζ := this
      _ ≤ L * ζ := mul_le_mul_of_nonneg_right (hLx x hxU) hζ0
  have hXU_cpt : IsCompact (P.X ∩ closure U) :=
    Metric.isCompact_of_isClosed_isBounded (hXcl.inter isClosed_closure)
      (hUb.closure.subset Set.inter_subset_right)
  have hxsU : xs ∈ closure U := subset_closure (hSU hxsS)
  obtain ⟨x0, hx0, hx0min⟩ := hXU_cpt.exists_isMinOn ⟨xs, hxsX, hxsU⟩
    ((hcontI ν hν).mono Set.inter_subset_left)
  have hx0min' : ∀ x ∈ P.X ∩ closure U, Ival P ν x0 ≤ Ival P ν x := isMinOn_iff.1 hx0min
  have hgood : ∀ w ∈ P.X, w ∈ closure U → Ival P ν w ≤ Ival P ν x0 →
      Ival P μ w - mμ ≤ 2 * η ∧ infEDist w (S P.X P.Ξ P.f0 μ) < ENNReal.ofReal ε := by
    intro w hw hwU hwle
    have h1 := hdiff w hw hwU
    have h2 := hdiff xs hxsX hxsU
    have h3 := hx0min' xs ⟨hxsX, hxsU⟩
    rw [abs_le] at h1 h2
    have hb : Ival P μ w - mμ ≤ 2 * η := by linarith
    refine ⟨hb, ?_⟩
    by_contra hcon
    push_neg at hcon
    have := hc w ⟨hw, hwU, hcon⟩
    linarith
  have hthick_sub : ∀ w, infEDist w (S P.X P.Ξ P.f0 μ) < ENNReal.ofReal ε → w ∈ U := by
    intro w hw
    apply hthick
    rw [Metric.mem_cthickening_iff]
    exact le_trans hw.le (ENNReal.ofReal_le_ofReal (by linarith))
  have hx0U : x0 ∈ U := hthick_sub x0 (hgood x0 hx0.1 hx0.2 le_rfl).2
  have hx0glob : ∀ x ∈ P.X, Ival P ν x0 ≤ Ival P ν x := by
    intro x hx
    by_contra hlt
    push_neg at hlt
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hUo x0 hx0U
    have hD : 0 < 2 * (‖x - x0‖ + 1) := by positivity
    set t := min (1 / 2 : ℝ) (ρ / (2 * (‖x - x0‖ + 1))) with htdef
    have ht0 : 0 < t := lt_min (by norm_num) (div_pos hρ hD)
    have ht1 : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
    have hxtX : (1 - t) • x0 + t • x ∈ P.X := hXc hx0.1 hx (by linarith) ht0.le (by ring)
    have hxtU : (1 - t) • x0 + t • x ∈ U := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm]
      have e : (1 - t) • x0 + t • x - x0 = t • (x - x0) := by
        rw [sub_smul, one_smul, smul_sub]; abel
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      have h1 : t ≤ ρ / (2 * (‖x - x0‖ + 1)) := min_le_right _ _
      have h2 : t * ‖x - x0‖ ≤ ρ / (2 * (‖x - x0‖ + 1)) * ‖x - x0‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      have h3 : ρ / (2 * (‖x - x0‖ + 1)) * ‖x - x0‖ < ρ := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hD]
        nlinarith [norm_nonneg (x - x0)]
      linarith
    have h1 := hx0min' _ ⟨hxtX, subset_closure hxtU⟩
    have h2 := hconv ν hν x0 hx0.1 x hx t ht0.le ht1
    have h3 := mul_pos ht0 (sub_pos.2 hlt)
    nlinarith
  have hvν : v P.X P.Ξ P.f0 ν = ((Ival P ν x0 : ℝ) : EReal) := hv_min ν hν x0 hx0.1 hx0glob
  have hSν : ∀ x, x ∈ S P.X P.Ξ P.f0 ν ↔ x ∈ P.X ∧ Ival P ν x = Ival P ν x0 := by
    intro x
    constructor
    · rintro ⟨hx, hx2⟩
      refine ⟨hx, ?_⟩
      rw [hobj ν hν x hx, hvν] at hx2
      exact_mod_cast hx2
    · rintro ⟨hx, hx2⟩
      refine ⟨hx, ?_⟩
      rw [hobj ν hν x hx, hvν, hx2]
  have hval : |mμ - Ival P ν x0| ≤ η := by
    have h1 := hdiff xs hxsX hxsU
    have h2 := hdiff x0 hx0.1 hx0.2
    have h3 := hx0glob xs hxsX
    have h4 := hmin_mu x0 hx0.1
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith
  refine ⟨⟨by rw [hvμ]; exact EReal.coe_ne_top _, by rw [hvμ]; exact EReal.coe_ne_bot _,
    by rw [hvν]; exact EReal.coe_ne_top _, by rw [hvν]; exact EReal.coe_ne_bot _, ?_⟩,
    ⟨x0, (hSν x0).2 ⟨hx0.1, rfl⟩⟩, ?_⟩
  · rw [hvμ, hvν, EReal.toReal_coe, EReal.toReal_coe]
    exact hval
  intro x hxS
  obtain ⟨hxX, hxI⟩ := (hSν x).1 hxS
  have hxgood : infEDist x (S P.X P.Ξ P.f0 μ) < ENNReal.ofReal ε := by
    by_contra hcon
    push_neg at hcon
    set gseg : ℝ → ℝ := fun t => infDist ((1 - t) • x0 + t • x) (S P.X P.Ξ P.f0 μ) with hgdef
    have hgc : Continuous gseg :=
      (continuous_infDist_pt _).comp (by fun_prop)
    have hg0 : gseg 0 ≤ ε := by
      simp only [hgdef, sub_zero, one_smul, zero_smul, add_zero]
      have h1 := (hgood x0 hx0.1 hx0.2 le_rfl).2
      rw [Metric.infDist]
      have h2 := (ENNReal.toReal_le_toReal (ne_top_of_lt h1) ENNReal.ofReal_ne_top).2 h1.le
      rwa [ENNReal.toReal_ofReal hε0.le] at h2
    have hg1 : ε ≤ gseg 1 := by
      simp only [hgdef, sub_self, zero_smul, one_smul, zero_add]
      rw [Metric.infDist]
      exact (ENNReal.ofReal_le_iff_le_toReal (infEDist_ne_top hSμne)).1 hcon
    obtain ⟨t, ⟨ht0, ht1⟩, hgt⟩ := intermediate_value_Icc zero_le_one hgc.continuousOn ⟨hg0, hg1⟩
    have hptX : (1 - t) • x0 + t • x ∈ P.X := hXc hx0.1 hxX (by linarith) ht0 (by ring)
    have hptE : infEDist ((1 - t) • x0 + t • x) (S P.X P.Ξ P.f0 μ) = ENNReal.ofReal ε := by
      have : gseg t = ε := hgt
      simp only [hgdef, Metric.infDist] at this
      rw [← this, ENNReal.ofReal_toReal (infEDist_ne_top hSμne)]
    have hptU : (1 - t) • x0 + t • x ∈ U := by
      apply hthick
      rw [Metric.mem_cthickening_iff, hptE]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have hptI : Ival P ν ((1 - t) • x0 + t • x) ≤ Ival P ν x0 := by
      have := hconv ν hν x0 hx0.1 x hxX t ht0 ht1
      rw [hxI] at this
      linarith
    have := (hgood _ hptX (subset_closure hptU) hptI).2
    rw [hptE] at this
    exact lt_irrefl _ this
  have hxU : x ∈ U := hthick_sub x hxgood
  have hxb := (hgood x hxX (subset_closure hxU) (le_of_eq hxI)).1
  set τ : NNReal := (infEDist x (S P.X P.Ξ P.f0 μ)).toNNReal with hτdef
  have hτ : (τ : ℝ≥0∞) = infEDist x (S P.X P.Ξ P.f0 μ) := ENNReal.coe_toNNReal (ne_top_of_lt hxgood)
  have e2 : 2 * (ENNReal.ofReal L * zetaP P.Ξ 2 μ ν) = ENNReal.ofReal (2 * η) := by
    rw [hηdef, hζdef, ← ENNReal.ofReal_toReal hζ, ENNReal.toReal_ofReal ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_mul hL0.le, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  have hpsi : psi P.X P.Ξ P.f0 μ U τ ≤
      ((2 * (ENNReal.ofReal L * zetaP P.Ξ 2 μ ν) : ℝ≥0∞) : EReal) := by
    have h1 : psi P.X P.Ξ P.f0 μ U τ ≤ objective P.Ξ P.f0 μ x - v P.X P.Ξ P.f0 μ :=
      iInf₂_le x ⟨hxX, subset_closure hxU, hτ.le⟩
    refine h1.trans ?_
    rw [hobj μ hμ x hxX, hvμ, ← EReal.coe_sub, e2, EReal.coe_ennreal_ofReal,
      max_eq_left (by positivity)]
    exact EReal.coe_le_coe_iff.2 hxb
  have hle : infEDist x (S P.X P.Ξ P.f0 μ) ≤
      psiInv P.X P.Ξ P.f0 μ U (2 * (ENNReal.ofReal L * zetaP P.Ξ 2 μ ν)) := by
    rw [← hτ]
    unfold psiInv
    exact le_iSup₂ (f := fun (τ : NNReal) (_ : τ ∈ {τ : NNReal | psi P.X P.Ξ P.f0 μ U τ ≤
      ((2 * (ENNReal.ofReal L * zetaP P.Ξ 2 μ ν) : ℝ≥0∞) : EReal)}) => (τ : ℝ≥0∞)) τ hpsi
  obtain ⟨y, hy, hyd⟩ := hSμ_cpt.exists_infEDist_eq_edist hSμne x
  refine ⟨y, hy, ?_⟩
  rw [← hyd]
  unfold Psi
  exact hle.trans le_add_self

end PartD

end PMS44

open ProbMetricStab.TwoStage in
theorem solution {m s r mbar : ℕ} (P : Data m s r mbar) (hP : P.Standing) (hA1 : P.A1)
    (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin s))) (hA2 : P.A2 μ)
    (U : Set (EuclideanSpace ℝ (Fin m)))
    (hS : (S P.X P.Ξ P.f0 μ).Nonempty) (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    (hSU : S P.X P.Ξ P.f0 μ ⊆ U) :
    ∃ L δ : ℝ, 0 < L ∧ 0 < δ ∧ ∀ ν : MeasureTheory.Measure (EuclideanSpace ℝ (Fin s)),
      ν ∈ Pp P.Ξ 2 → zetaP P.Ξ 2 μ ν < ENNReal.ofReal δ →
        (v P.X P.Ξ P.f0 μ ≠ ⊤ ∧ v P.X P.Ξ P.f0 μ ≠ ⊥ ∧
          v P.X P.Ξ P.f0 ν ≠ ⊤ ∧ v P.X P.Ξ P.f0 ν ≠ ⊥ ∧
          |(v P.X P.Ξ P.f0 μ).toReal - (v P.X P.Ξ P.f0 ν).toReal| ≤
            L * (zetaP P.Ξ 2 μ ν).toReal) ∧
        (S P.X P.Ξ P.f0 ν).Nonempty ∧
        ∀ x ∈ S P.X P.Ξ P.f0 ν, ∃ y ∈ S P.X P.Ξ P.f0 μ,
          edist x y ≤ Psi P.X P.Ξ P.f0 μ U (ENNReal.ofReal L * zetaP P.Ξ 2 μ ν) := by
  exact PMS44.main33 P hP hA1 μ hA2 U hS hUo hUb hSU
