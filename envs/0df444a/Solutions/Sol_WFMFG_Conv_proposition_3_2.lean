-- Prove2me | solution 1 for WFMFG.Conv.proposition_3_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T17:09:28.685793+00:00
-- url     : https://prove2.me/submissions/6d5d9830-8638-470d-8116-96f2573ca17e

import Mathlib
import Definitions.Def_WFMFG_Conv_Simplex
import Definitions.Def_WFMFG_Conv_Multinomial
import Definitions.Def_WFMFG_Conv_Setting

open Finset WFMFG.Conv


namespace WFMFGmult

lemma antidiag_eq (d N : ℕ) :
    Finset.Nat.antidiagonalTuple d N = (Finset.univ : Finset (Fin d)).piAntidiag N := by
  ext k; simp [Finset.mem_piAntidiag, Finset.Nat.mem_antidiagonalTuple]

lemma multW_sum (d N : ℕ) (p : Fin d → ℝ) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW p k = (∑ i, p i) ^ N := by
  rw [Finset.sum_pow_eq_sum_piAntidiag, antidiag_eq]
  rfl

lemma multW_mean (d N : ℕ) (p : Fin d → ℝ) (i : Fin d) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW p k * (k i : ℝ)
      = N * p i * (∑ j, p j) ^ (N - 1) := by
  have key : ∀ s : ℝ, (∑ j, p j + (s - 1) * p i) ^ N
      = ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW p k * s ^ (k i) := by
    intro s
    set q : Fin d → ℝ := fun j => if j = i then s * p j else p j with hq
    have hsum : ∑ j, q j = ∑ j, p j + (s - 1) * p i := by
      have : ∀ j, q j = p j + (if j = i then (s - 1) * p j else 0) := by
        intro j; simp only [hq]; split_ifs <;> ring
      simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← hsum, Finset.sum_pow_eq_sum_piAntidiag, ← antidiag_eq]
    apply Finset.sum_congr rfl
    intro k _
    have hprod : ∏ j, q j ^ k j = (∏ j, p j ^ k j) * s ^ (k i) := by
      have : ∀ j, q j ^ k j = p j ^ k j * (if j = i then s ^ (k j) else 1) := by
        intro j; simp only [hq]; split_ifs with h
        · rw [mul_pow, mul_comm]
        · ring
      simp only [this, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
    rw [hprod]; unfold multW; ring
  have hL : HasDerivAt (fun s : ℝ => (∑ j, p j + (s - 1) * p i) ^ N)
      ((N : ℝ) * (∑ j, p j + (1 - 1) * p i) ^ (N - 1) * p i) 1 := by
    have h1 : HasDerivAt (fun s : ℝ => ∑ j, p j + (s - 1) * p i) (p i) 1 := by
      simpa using (((hasDerivAt_id (1:ℝ)).sub_const 1).mul_const (p i)).const_add (∑ j, p j)
    simpa using h1.fun_pow N
  have hR : HasDerivAt (fun s : ℝ => ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW p k * s ^ (k i))
      (∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW p k * ((k i : ℝ) * 1 ^ (k i - 1))) 1 := by
    apply HasDerivAt.fun_sum
    intro k _
    exact (hasDerivAt_pow (k i) (1:ℝ)).const_mul (multW p k)
  have hfun : (fun s : ℝ => (∑ j, p j + (s - 1) * p i) ^ N)
      = (fun s : ℝ => ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW p k * s ^ (k i)) := funext key
  rw [hfun] at hL
  have := hL.unique hR
  simp only [one_pow, mul_one, sub_self, zero_mul, add_zero] at this
  rw [← this]; ring

end WFMFGmult


namespace WFMFGmax

lemma maxPrinciple {I : Type*} (u u' : I → ℝ → ℝ) (T G R : ℝ) (hT : 0 < T) (hG : 0 ≤ G)
    (hR : 0 < R)
    (hd : ∀ i, ∀ s ∈ Set.Icc 0 T, HasDerivWithinAt (u i) (u' i s) (Set.Icc 0 T) s)
    (hTerm : ∀ i, u i T ≤ 0)
    (hbd : ∀ i, ∀ s ∈ Set.Icc 0 T, u i s ≤ G)
    (hgen : ∀ i, ∀ s ∈ Set.Icc 0 T, ∀ h : ℝ, (∀ j, u j s ≤ h) → -R * (h - u i s) ≤ u' i s) :
    ∀ i, ∀ s ∈ Set.Icc 0 T, u i s ≤ 0 := by
  have step : ∀ n : ℕ, ∀ i, ∀ s ∈ Set.Icc 0 T,
      u i s ≤ G * (R * (T - s)) ^ n / (n.factorial : ℝ) := by
    intro n
    induction n with
    | zero => intro i s hs; simpa using hbd i s hs
    | succ n ih =>
      intro i s hs
      have hcont : ContinuousOn (u i) (Set.Icc 0 T) := fun s hs => (hd i s hs).continuousWithinAt
      let f : ℝ → ℝ := fun τ => u i (T - τ)
      let B : ℝ → ℝ := fun τ => G * (R * τ) ^ (n + 1) / ((n + 1).factorial : ℝ)
      have hmaps : ∀ τ ∈ Set.Icc (0:ℝ) T, T - τ ∈ Set.Icc (0:ℝ) T := fun τ hτ =>
        ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
      have hfc : ContinuousOn f (Set.Icc 0 T) :=
        hcont.comp (by fun_prop : Continuous fun τ : ℝ => T - τ).continuousOn hmaps
      have hfd : ∀ τ ∈ Set.Ico (0:ℝ) T,
          HasDerivWithinAt f (-u' i (T - τ)) (Set.Ici τ) τ := by
        intro τ hτ
        have h1 := hd i (T - τ) ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
        have h2 : HasDerivWithinAt (fun τ : ℝ => T - τ) (-1) (Set.Icc τ T) τ := by
          simpa using ((hasDerivAt_id τ).const_sub T).hasDerivWithinAt
        have h3 := h1.comp τ h2 (fun τ' hτ' => ⟨by linarith [hτ'.2], by linarith [hτ.1, hτ'.1]⟩)
        have h4 : HasDerivWithinAt f (u' i (T - τ) * -1) (Set.Icc τ T) τ := h3
        rw [mul_neg_one] at h4
        exact h4.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hτ.2)
      have hBd : ∀ τ : ℝ, HasDerivAt B (G * R * (R * τ) ^ n / (n.factorial : ℝ)) τ := by
        intro τ
        have h1 : HasDerivAt (fun τ : ℝ => R * τ) R τ := by
          simpa using (hasDerivAt_id τ).const_mul R
        have h2 := ((h1.fun_pow (n + 1)).const_mul G).div_const ((n + 1).factorial : ℝ)
        refine h2.congr_deriv ?_
        rw [Nat.factorial_succ]
        push_cast
        have : (n.factorial : ℝ) ≠ 0 := by positivity
        field_simp
      have key : ∀ ε : ℝ, 0 < ε → f (T - s) ≤ B (T - s) + ε := by
        intro ε hε
        have := image_le_of_deriv_right_lt_deriv_boundary' (f := f)
          (f' := fun τ => -u' i (T - τ)) (a := 0) (b := T)
          (B := fun τ => B τ + ε) (B' := fun τ => G * R * (R * τ) ^ n / (n.factorial : ℝ))
          hfc hfd ?_ ?_ ?_ ?_
        · exact this ⟨by linarith [hs.2], by linarith [hs.1]⟩
        · simp only [f, B, sub_zero]
          have := hTerm i
          simp; linarith
        · exact (Continuous.continuousOn (by
            have : Continuous B := by fun_prop
            fun_prop))
        · intro τ _
          exact ((hBd τ).add_const ε).hasDerivWithinAt
        · intro τ hτ heq
          have hτ' : T - τ ∈ Set.Icc (0:ℝ) T := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
          have hall : ∀ j, u j (T - τ) ≤ G * (R * τ) ^ n / (n.factorial : ℝ) := by
            intro j
            have := ih j (T - τ) hτ'
            simpa using this
          have hg := hgen i (T - τ) hτ' _ hall
          have hB0 : 0 ≤ B τ := by
            simp only [B]
            have : 0 ≤ R * τ := mul_nonneg hR.le hτ.1
            positivity
          have hfe : u i (T - τ) = B τ + ε := heq
          rw [hfe] at hg
          have : 0 < R * (B τ + ε) := mul_pos hR (by linarith)
          have e : G * R * (R * τ) ^ n / (n.factorial : ℝ)
              = R * (G * (R * τ) ^ n / (n.factorial : ℝ)) := by ring
          rw [e]
          nlinarith
      have h := le_of_forall_pos_le_add key
      simpa [f, B] using h
  intro i s hs
  have ht := (FloorSemiring.tendsto_pow_div_factorial_atTop (R * (T - s))).const_mul G
  rw [mul_zero] at ht
  refine ge_of_tendsto' ht (fun n => ?_)
  have := step n i s hs
  rw [mul_div_assoc] at this
  exact this

end WFMFGmax

namespace WFMFG32

lemma empQ_nonneg {d N : ℕ} (x : Fin N → Fin d) (y : Fin N → ℚ) (hy : y ∈ Yset N) (i : Fin d) :
    0 ≤ empQ x y i := by
  unfold empQ
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg; intro l _; split_ifs <;> simp [hy.1 l]

lemma empQ_sum {d N : ℕ} (hN : 1 ≤ N) (x : Fin N → Fin d) (y : Fin N → ℚ) (hy : y ∈ Yset N) :
    ∑ i, empQ x y i = 1 := by
  unfold empQ
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hy.2]
  have hN' : (N:ℚ) ≠ 0 := by positivity
  field_simp

lemma emp_std {d N : ℕ} (hN : 1 ≤ N) (x : Fin N → Fin d) (y : Fin N → ℚ) (hy : y ∈ Yset N) :
    empMeas x y ∈ stdSimplex ℝ (Fin d) := by
  refine ⟨fun i => ?_, ?_⟩
  · simp only [empMeas]; exact_mod_cast empQ_nonneg x y hy i
  · simp only [empMeas]; exact_mod_cast empQ_sum hN x y hy

lemma ratio_cast {d N : ℕ} (x : Fin N → Fin d) (y : Fin N → ℚ) (k : Fin d → ℕ) (l : Fin N) :
    ((ratioQ x y k l : ℚ) : ℝ) =
      if empQ x y (x l) = 0 then 1 else (k (x l) : ℝ) / (N * empMeas x y (x l)) := by
  unfold ratioQ empMeas; split_ifs <;> push_cast <;> rfl

lemma ratioQ_nonneg {d N : ℕ} (x : Fin N → Fin d) (y : Fin N → ℚ) (hy : y ∈ Yset N)
    (k : Fin d → ℕ) (l : Fin N) : 0 ≤ ratioQ x y k l := by
  unfold ratioQ
  split_ifs
  · norm_num
  · have := empQ_nonneg x y hy (x l); positivity

/-- total mass of the common-noise jump kernel is one. -/
lemma noise_mass {d N : ℕ} (hN : 1 ≤ N) (x : Fin N → Fin d) (y : Fin N → ℚ) (hy : y ∈ Yset N)
    (l : Fin N) :
    ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW (empMeas x y) k * (ratioQ x y k l : ℝ) = 1 := by
  have hs : ∑ i, empMeas x y i = 1 := (emp_std hN x y hy).2
  simp_rw [ratio_cast]
  split_ifs with h0
  · simp only [mul_one]; rw [WFMFGmult.multW_sum, hs, one_pow]
  · have hμ : empMeas x y (x l) ≠ 0 := by
      simp only [empMeas]; exact_mod_cast h0
    have hNr : (N:ℝ) ≠ 0 := by have : (0:ℝ) < N := by exact_mod_cast hN
                               exact this.ne'
    simp_rw [mul_div_assoc', ← Finset.sum_div]
    rw [WFMFGmult.multW_mean, hs, one_pow, mul_one]
    field_simp

lemma multW_nonneg {d : ℕ} (p : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i) (k : Fin d → ℕ) :
    0 ≤ multW p k := by
  unfold multW
  apply mul_nonneg (by positivity)
  exact Finset.prod_nonneg (fun i _ => pow_nonneg (hp i) _)

lemma reweight_mem {d N : ℕ} (hN : 1 ≤ N) (x : Fin N → Fin d) (y : Fin N → ℚ) (hy : y ∈ Yset N)
    (k : Fin d → ℕ) (hk : k ∈ Finset.Nat.antidiagonalTuple d N)
    (hw : multW (empMeas x y) k ≠ 0) : reweight x y k ∈ Yset N := by
  refine ⟨fun l => mul_nonneg (hy.1 l) (ratioQ_nonneg x y hy k l), ?_⟩
  -- support condition
  have hsupp : ∀ i, empQ x y i = 0 → k i = 0 := by
    intro i hi
    by_contra hki
    apply hw
    unfold multW
    have : ∏ j, empMeas x y j ^ k j = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      have : empMeas x y i = 0 := by simp only [empMeas]; exact_mod_cast hi
      rw [this]; exact zero_pow hki
    rw [this, mul_zero]
  set r : Fin d → ℚ := fun i => if empQ x y i = 0 then 1 else (k i : ℚ) / (N * empQ x y i) with hr
  have h1 : ∑ l, reweight x y k l = ∑ i, r i * (N * empQ x y i) := by
    have e1 : ∀ l, reweight x y k l = ∑ i, (if x l = i then y l * r i else 0) := by
      intro l
      rw [Finset.sum_ite_eq]; simp only [Finset.mem_univ, if_true, reweight, ratioQ, hr]
    simp_rw [e1]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    have hN' : (N:ℚ) ≠ 0 := by positivity
    have e : r i * (N * empQ x y i) = r i * ∑ l, (if x l = i then y l else 0) := by
      unfold empQ; field_simp
    rw [e, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    split_ifs <;> ring
  rw [h1]
  have h2 : ∀ i, r i * (N * empQ x y i) = k i := by
    intro i
    simp only [hr]
    split_ifs with h
    · rw [h, hsupp i h]; simp
    · have hN' : (N:ℚ) ≠ 0 := by positivity
      field_simp
  simp_rw [h2]
  have := (Finset.Nat.mem_antidiagonalTuple).1 hk
  exact_mod_cast this

lemma sum_le_card {ι : Type*} (s : Finset ι) (X : ι → ℝ) (Y : ℝ) (h : ∀ i ∈ s, X i ≤ Y) :
    ∑ i ∈ s, X i ≤ s.card * Y := by
  have := Finset.sum_le_sum h
  simpa using this

lemma sum_ge_card {ι : Type*} (s : Finset ι) (X : ι → ℝ) (Y : ℝ) (h : ∀ i ∈ s, -Y ≤ X i) :
    -(s.card * Y) ≤ ∑ i ∈ s, X i := by
  have := Finset.sum_le_sum h
  simp at this
  linarith

lemma pos_le_two (a b B : ℝ) (ha : |a| ≤ B) (hb : |b| ≤ B) : pos (a - b) ≤ 2 * B := by
  unfold pos
  apply max_le
  · have := abs_le.1 ha; have := abs_le.1 hb; linarith
  · have := abs_nonneg a; linarith

lemma pos_nonneg (a : ℝ) : 0 ≤ pos a := le_max_right _ _

end WFMFG32

open WFMFG32 WFMFGmax

theorem solution (d N : ℕ) [NeZero d] (hN : 1 ≤ N) (ε T κ δ Mf Mg : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hT : 0 < T) (hδ : 0 < δ)
    (φ : ℝ → ℝ) (hφ : IsCutoff κ δ φ) (f g : Fin d → (Fin d → ℝ) → ℝ)
    (hf : ∀ i, ∀ p ∈ stdSimplex ℝ (Fin d), |f i p| ≤ Mf)
    (hg : ∀ i, ∀ p ∈ stdSimplex ℝ (Fin d), |g i p| ≤ Mg)
    (w : Fin N → ℝ → (Fin N → Fin d) → (Fin N → ℚ) → ℝ) (hw : IsNashSol N ε T φ f g w) :
    ∀ (l : Fin N) (x : Fin N → Fin d), ∀ y ∈ Yset N, ∀ t ∈ Set.Icc 0 T,
      |w l t x y| ≤ T * Mf + Mg ∧
      ∀ j : Fin d, astar (x l) (fun j' => w l t (Function.update x l j') y) j ≤ 2 * T * Mf + 2 * Mg := by
  obtain ⟨hder, hterm, B0, hB0⟩ := hw
  obtain ⟨hφ0, hφanti, _, hφκ, _⟩ := hφ
  set B : ℝ := |B0| with hBdef
  have hB : ∀ l x, ∀ y ∈ Yset N, ∀ t ∈ Set.Icc 0 T, |w l t x y| ≤ B := fun l x y hy t ht =>
    le_trans (hB0 l x y hy t ht) (le_abs_self _)
  have hBn : 0 ≤ B := abs_nonneg _
  have hκ0 : 0 ≤ κ := by
    have := hφκ 0 ⟨le_refl _, hδ.le⟩; rw [← this]; exact hφ0 0 (le_refl _)
  have hφb : ∀ r, 0 ≤ r → φ r ≤ κ := by
    intro r hr
    have h0 := hφκ 0 ⟨le_refl _, hδ.le⟩
    rw [← h0]
    exact hφanti (Set.mem_Ici.2 (le_refl 0)) (Set.mem_Ici.2 hr) hr
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  -- index set
  let I := {p : Fin N × (Fin N → Fin d) × (Fin N → ℚ) // p.2.2 ∈ Yset N}
  let b : ℝ → ℝ := fun s => Mg + (T - s) * Mf
  have hbd : ∀ s : ℝ, HasDerivAt b (-Mf) s := by
    intro s
    have := ((hasDerivAt_id s).const_sub T).mul_const Mf
    have := this.const_add Mg
    simpa [b] using this
  set R : ℝ := N * d * κ + N * d * (2 * B) + d * (2 * B) + ε * N + 1 with hRdef
  have hR : 0 < R := by simp only [hRdef]; positivity
  set G : ℝ := B + |Mg| + T * |Mf| with hGdef
  have hG : 0 ≤ G := by simp only [hGdef]; positivity
  have hbabs : ∀ s ∈ Set.Icc 0 T, |b s| ≤ |Mg| + T * |Mf| := by
    intro s hs
    simp only [b]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_of_nonneg (by linarith [hs.2] : (0:ℝ) ≤ T - s)]
    have : (T - s) * |Mf| ≤ T * |Mf| := mul_le_mul_of_nonneg_right (by linarith [hs.1]) (abs_nonneg _)
    linarith
  -- common facts at an index
  have hdrift_up : ∀ (l : Fin N) (x : Fin N → Fin d) (y : Fin N → ℚ), y ∈ Yset N →
      ∀ s ∈ Set.Icc 0 T, ∀ Δ : ℝ, 0 ≤ Δ →
      (∀ x', w l s x' y - w l s x y ≤ Δ) →
      driftOp φ w l s x y ≤ (N * d * κ + N * d * (2 * B)) * Δ := by
    intro l x y hy s hs Δ hΔ hD
    unfold driftOp
    have hμ0 : ∀ j, 0 ≤ empMeas x y j := (emp_std hN x y hy).1
    have hin1 : ∀ m, ∑ j, φ (empMeas x y j) * (w l s (Function.update x m j) y - w l s x y)
        ≤ d * (κ * Δ) := by
      intro m
      have := sum_le_card (Finset.univ : Finset (Fin d))
        (fun j => φ (empMeas x y j) * (w l s (Function.update x m j) y - w l s x y)) (κ * Δ)
        (fun j _ => le_trans (mul_le_mul_of_nonneg_left (hD _) (hφ0 _ (hμ0 j)))
          (mul_le_mul_of_nonneg_right (hφb _ (hμ0 j)) hΔ))
      simpa using this
    have h1 : ∑ m, ∑ j, φ (empMeas x y j) * (w l s (Function.update x m j) y - w l s x y)
        ≤ N * d * κ * Δ := by
      have := sum_le_card (Finset.univ : Finset (Fin N)) _ _ (fun m _ => hin1 m)
      simp only [Finset.card_univ, Fintype.card_fin] at this
      linarith
    have hin2 : ∀ m, ∑ j, astar (x m) (fun j' => w m s (Function.update x m j') y) j *
          (w l s (Function.update x m j) y - w l s x y) ≤ d * (2 * B * Δ) := by
      intro m
      have := sum_le_card (Finset.univ : Finset (Fin d))
        (fun j => astar (x m) (fun j' => w m s (Function.update x m j') y) j *
          (w l s (Function.update x m j) y - w l s x y)) (2 * B * Δ)
        (fun j _ => le_trans (mul_le_mul_of_nonneg_left (hD _) (pos_nonneg _))
          (mul_le_mul_of_nonneg_right (pos_le_two _ _ _ (hB _ _ y hy s hs) (hB _ _ y hy s hs)) hΔ))
      simpa using this
    have h2 : ∑ m ∈ Finset.univ.erase l, ∑ j,
        astar (x m) (fun j' => w m s (Function.update x m j') y) j *
          (w l s (Function.update x m j) y - w l s x y) ≤ N * d * (2 * B) * Δ := by
      have := sum_le_card (Finset.univ.erase l) _ _ (fun m _ => hin2 m)
      have hc : ((Finset.univ.erase l).card : ℝ) ≤ N := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ l)]
        simp
      have : (((Finset.univ.erase l).card : ℝ)) * (d * (2 * B * Δ)) ≤ N * (d * (2 * B * Δ)) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      linarith
    nlinarith
  have hdrift_lo : ∀ (l : Fin N) (x : Fin N → Fin d) (y : Fin N → ℚ), y ∈ Yset N →
      ∀ s ∈ Set.Icc 0 T, ∀ Δ : ℝ, 0 ≤ Δ →
      (∀ x', -Δ ≤ w l s x' y - w l s x y) →
      -((N * d * κ + N * d * (2 * B)) * Δ) ≤ driftOp φ w l s x y := by
    intro l x y hy s hs Δ hΔ hD
    unfold driftOp
    have hμ0 : ∀ j, 0 ≤ empMeas x y j := (emp_std hN x y hy).1
    have hin1 : ∀ m, -(d * (κ * Δ)) ≤
        ∑ j, φ (empMeas x y j) * (w l s (Function.update x m j) y - w l s x y) := by
      intro m
      have := sum_ge_card (Finset.univ : Finset (Fin d))
        (fun j => φ (empMeas x y j) * (w l s (Function.update x m j) y - w l s x y)) (κ * Δ)
        (fun j _ => by
          have h1 := mul_le_mul_of_nonneg_left (hD (Function.update x m j)) (hφ0 _ (hμ0 j))
          have h2 := mul_le_mul_of_nonneg_right (hφb _ (hμ0 j)) hΔ
          nlinarith)
      simpa using this
    have h1 : -(N * d * κ * Δ) ≤
        ∑ m, ∑ j, φ (empMeas x y j) * (w l s (Function.update x m j) y - w l s x y) := by
      have := sum_ge_card (Finset.univ : Finset (Fin N)) _ _ (fun m _ => hin1 m)
      simp only [Finset.card_univ, Fintype.card_fin] at this
      linarith
    have hin2 : ∀ m, -(d * (2 * B * Δ)) ≤ ∑ j,
        astar (x m) (fun j' => w m s (Function.update x m j') y) j *
          (w l s (Function.update x m j) y - w l s x y) := by
      intro m
      have := sum_ge_card (Finset.univ : Finset (Fin d))
        (fun j => astar (x m) (fun j' => w m s (Function.update x m j') y) j *
          (w l s (Function.update x m j) y - w l s x y)) (2 * B * Δ)
        (fun j _ => by
          have h1 := mul_le_mul_of_nonneg_left (hD (Function.update x m j))
            (pos_nonneg (w m s (Function.update x m (x m)) y - w m s (Function.update x m j) y))
          have h2 := mul_le_mul_of_nonneg_right
            (pos_le_two _ _ _ (hB m (Function.update x m (x m)) y hy s hs)
              (hB m (Function.update x m j) y hy s hs)) hΔ
          simp only [astar]; nlinarith)
      simpa using this
    have h2 : -(N * d * (2 * B) * Δ) ≤ ∑ m ∈ Finset.univ.erase l, ∑ j,
        astar (x m) (fun j' => w m s (Function.update x m j') y) j *
          (w l s (Function.update x m j) y - w l s x y) := by
      have := sum_ge_card (Finset.univ.erase l) _ _ (fun m _ => hin2 m)
      have hc : ((Finset.univ.erase l).card : ℝ) ≤ N := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ l)]
        simp
      have : (((Finset.univ.erase l).card : ℝ)) * (d * (2 * B * Δ)) ≤ N * (d * (2 * B * Δ)) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      linarith
    nlinarith
  have hnoise_up : ∀ (l : Fin N) (x : Fin N → Fin d) (y : Fin N → ℚ), y ∈ Yset N →
      ∀ s : ℝ, ∀ Δ : ℝ, 0 ≤ Δ →
      (∀ y' ∈ Yset N, w l s x y' - w l s x y ≤ Δ) →
      multE N (empMeas x y) (fun k => (ratioQ x y k l : ℝ) * (w l s x (reweight x y k) - w l s x y))
        ≤ Δ := by
    intro l x y hy s Δ hΔ hD
    unfold multE
    have hμ0 : ∀ j, 0 ≤ empMeas x y j := (emp_std hN x y hy).1
    calc _ ≤ ∑ k ∈ Finset.Nat.antidiagonalTuple d N,
          multW (empMeas x y) k * (ratioQ x y k l : ℝ) * Δ := by
          apply Finset.sum_le_sum
          intro k hk
          by_cases hz : multW (empMeas x y) k = 0
          · simp [hz]
          · have hm := reweight_mem hN x y hy k hk hz
            have h1 := hD _ hm
            have h2 := multW_nonneg _ hμ0 k
            have h3 : (0:ℝ) ≤ ratioQ x y k l := by exact_mod_cast ratioQ_nonneg x y hy k l
            rw [mul_assoc]
            apply mul_le_mul_of_nonneg_left _ h2
            exact mul_le_mul_of_nonneg_left h1 h3
      _ = Δ := by rw [← Finset.sum_mul, noise_mass hN x y hy l, one_mul]
  have hnoise_lo : ∀ (l : Fin N) (x : Fin N → Fin d) (y : Fin N → ℚ), y ∈ Yset N →
      ∀ s : ℝ, ∀ Δ : ℝ, 0 ≤ Δ →
      (∀ y' ∈ Yset N, -Δ ≤ w l s x y' - w l s x y) →
      -Δ ≤ multE N (empMeas x y)
        (fun k => (ratioQ x y k l : ℝ) * (w l s x (reweight x y k) - w l s x y)) := by
    intro l x y hy s Δ hΔ hD
    unfold multE
    have hμ0 : ∀ j, 0 ≤ empMeas x y j := (emp_std hN x y hy).1
    calc -Δ = ∑ k ∈ Finset.Nat.antidiagonalTuple d N,
          multW (empMeas x y) k * (ratioQ x y k l : ℝ) * (-Δ) := by
          rw [← Finset.sum_mul, noise_mass hN x y hy l, one_mul]
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro k hk
          by_cases hz : multW (empMeas x y) k = 0
          · simp [hz]
          · have hm := reweight_mem hN x y hy k hk hz
            have h1 := hD _ hm
            have h2 := multW_nonneg _ hμ0 k
            have h3 : (0:ℝ) ≤ ratioQ x y k l := by exact_mod_cast ratioQ_nonneg x y hy k l
            rw [mul_assoc]
            apply mul_le_mul_of_nonneg_left _ h2
            exact mul_le_mul_of_nonneg_left h1 h3
  -- upper bound via the maximum principle
  have hup := maxPrinciple (I := I)
    (fun α s => w α.1.1 s α.1.2.1 α.1.2.2 - b s)
    (fun α s => -(nashOp ε φ f w α.1.1 s α.1.2.1 α.1.2.2) - -Mf) T G R hT hG hR
    (fun α s hs => (hder α.1.1 α.1.2.1 α.1.2.2 α.2 s hs).sub (hbd s).hasDerivWithinAt)
    (fun α => by
      have := hterm α.1.1 α.1.2.1 α.1.2.2 α.2
      have hgb := hg (α.1.2.1 α.1.1) _ (emp_std hN α.1.2.1 α.1.2.2 α.2)
      simp only [b, sub_self, zero_mul, add_zero, this]
      linarith [le_abs_self (g (α.1.2.1 α.1.1) (empMeas α.1.2.1 α.1.2.2))])
    (fun α s hs => by
      have h1 := hB α.1.1 α.1.2.1 α.1.2.2 α.2 s hs
      have h2 := hbabs s hs
      have h3 := neg_abs_le (b s)
      have h4 := le_abs_self (w α.1.1 s α.1.2.1 α.1.2.2)
      simp only [hGdef]; linarith)
    (by
      intro α s hs h hall
      obtain ⟨⟨l, x, y⟩, hy⟩ := α
      simp only at hall ⊢
      have hΔ : 0 ≤ h - (w l s x y - b s) := by linarith [hall ⟨⟨l, x, y⟩, hy⟩]
      set Δ := h - (w l s x y - b s) with hΔdef
      have hDx : ∀ x', w l s x' y - w l s x y ≤ Δ := by
        intro x'; have := hall ⟨⟨l, x', y⟩, hy⟩; simp only at this; linarith
      have hDy : ∀ y' ∈ Yset N, w l s x y' - w l s x y ≤ Δ := by
        intro y' hy'; have := hall ⟨⟨l, x, y'⟩, hy'⟩; simp only at this; linarith
      have hd1 := hdrift_up l x y hy s hs Δ hΔ hDx
      have hn1 := hnoise_up l x y hy s Δ hΔ hDy
      have hham : ham (x l) (fun j => w l s (Function.update x l j) y) ≤ 0 := by
        unfold ham
        have : 0 ≤ ∑ j, pos (w l s (Function.update x l (x l)) y - w l s (Function.update x l j) y) ^ 2 :=
          Finset.sum_nonneg (fun j _ => sq_nonneg _)
        linarith
      have hfb := le_trans (le_abs_self _) (hf (x l) _ (emp_std hN x y hy))
      unfold nashOp
      have hεN : 0 ≤ ε * N := by positivity
      have := mul_le_mul_of_nonneg_left hn1 hεN
      have hRΔ : (N * d * κ + N * d * (2 * B) + ε * N) * Δ ≤ R * Δ := by
        apply mul_le_mul_of_nonneg_right _ hΔ
        simp only [hRdef]
        have : 0 ≤ (d:ℝ) * (2 * B) := by positivity
        linarith
      nlinarith)
  -- lower bound
  have hlo := maxPrinciple (I := I)
    (fun α s => -w α.1.1 s α.1.2.1 α.1.2.2 - b s)
    (fun α s => -(-(nashOp ε φ f w α.1.1 s α.1.2.1 α.1.2.2)) - -Mf) T G R hT hG hR
    (fun α s hs => (hder α.1.1 α.1.2.1 α.1.2.2 α.2 s hs).neg.sub (hbd s).hasDerivWithinAt)
    (fun α => by
      have := hterm α.1.1 α.1.2.1 α.1.2.2 α.2
      have hgb := hg (α.1.2.1 α.1.1) _ (emp_std hN α.1.2.1 α.1.2.2 α.2)
      simp only [b, sub_self, zero_mul, add_zero, this]
      linarith [neg_abs_le (g (α.1.2.1 α.1.1) (empMeas α.1.2.1 α.1.2.2))])
    (fun α s hs => by
      have h1 := hB α.1.1 α.1.2.1 α.1.2.2 α.2 s hs
      have h2 := hbabs s hs
      have h3 := neg_abs_le (b s)
      have h4 := neg_abs_le (w α.1.1 s α.1.2.1 α.1.2.2)
      simp only [hGdef]; linarith)
    (by
      intro α s hs h hall
      obtain ⟨⟨l, x, y⟩, hy⟩ := α
      simp only at hall ⊢
      have hΔ : 0 ≤ h - (-w l s x y - b s) := by linarith [hall ⟨⟨l, x, y⟩, hy⟩]
      set Δ := h - (-w l s x y - b s) with hΔdef
      have hDx : ∀ x', -Δ ≤ w l s x' y - w l s x y := by
        intro x'; have := hall ⟨⟨l, x', y⟩, hy⟩; simp only at this; linarith
      have hDy : ∀ y' ∈ Yset N, -Δ ≤ w l s x y' - w l s x y := by
        intro y' hy'; have := hall ⟨⟨l, x, y'⟩, hy'⟩; simp only at this; linarith
      have hd1 := hdrift_lo l x y hy s hs Δ hΔ hDx
      have hn1 := hnoise_lo l x y hy s Δ hΔ hDy
      have hham : -(d * (2 * B) * Δ) ≤ ham (x l) (fun j => w l s (Function.update x l j) y) := by
        unfold ham
        have hterm' : ∀ j, -(2 * B * Δ) ≤
            -(1 / 2) * pos (w l s (Function.update x l (x l)) y - w l s (Function.update x l j) y) ^ 2
              * (d : ℝ) / d := by
          intro j
          have hd0 : (d:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
          rw [mul_div_assoc, div_self hd0, mul_one]
          set a := w l s (Function.update x l (x l)) y - w l s (Function.update x l j) y with ha
          have hpa : pos a ^ 2 = pos a * a := by
            unfold pos
            rcases le_total a 0 with h | h
            · rw [max_eq_right h]; ring
            · rw [max_eq_left h]; ring
          have hp0 := pos_nonneg a
          have hp2 := pos_le_two _ _ _ (hB l (Function.update x l (x l)) y hy s hs)
            (hB l (Function.update x l j) y hy s hs)
          have hxl : Function.update x l (x l) = x := Function.update_eq_self l x
          have hDa : a ≤ Δ := by
            have := hDx (Function.update x l j); rw [ha, hxl]; linarith
          rw [hpa]
          nlinarith
        have := sum_ge_card (Finset.univ : Finset (Fin d)) _ (2 * B * Δ) (fun j _ => hterm' j)
        simp only [Finset.card_univ, Fintype.card_fin] at this
        have hd0 : (d:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
        have e : ∑ j, -(1 / 2) * pos (w l s (Function.update x l (x l)) y
            - w l s (Function.update x l j) y) ^ 2 * (d : ℝ) / d
            = -(1 / 2) * ∑ j, pos (w l s (Function.update x l (x l)) y
            - w l s (Function.update x l j) y) ^ 2 := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; field_simp
        rw [e] at this
        linarith
      have hfb := neg_le_of_abs_le (hf (x l) _ (emp_std hN x y hy))
      unfold nashOp
      have hεN : 0 ≤ ε * N := by positivity
      have := mul_le_mul_of_nonneg_left hn1 hεN
      have hRΔ : (N * d * κ + N * d * (2 * B) + d * (2 * B) + ε * N) * Δ ≤ R * Δ := by
        apply mul_le_mul_of_nonneg_right _ hΔ
        simp only [hRdef]; linarith
      nlinarith)
  -- conclusion
  have hMf : 0 ≤ Mf := le_trans (abs_nonneg _) (hf 0 _ (emp_std hN (fun _ => 0) (fun _ => 1)
    ⟨fun _ => by norm_num, by simp⟩))
  have habs : ∀ l x, ∀ y ∈ Yset N, ∀ t ∈ Set.Icc 0 T, |w l t x y| ≤ T * Mf + Mg := by
    intro l x y hy t ht
    have h1 := hup ⟨⟨l, x, y⟩, hy⟩ t ht
    have h2 := hlo ⟨⟨l, x, y⟩, hy⟩ t ht
    simp only [b] at h1 h2
    have : (T - t) * Mf ≤ T * Mf := mul_le_mul_of_nonneg_right (by linarith [ht.1]) hMf
    rw [abs_le]; constructor <;> linarith
  intro l x y hy t ht
  refine ⟨habs l x y hy t ht, fun j => ?_⟩
  have h1 := habs l (Function.update x l (x l)) y hy t ht
  have h2 := habs l (Function.update x l j) y hy t ht
  have := pos_le_two _ _ _ h1 h2
  simp only [astar]
  linarith
