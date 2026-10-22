-- Prove2me | solution 1 for WFMFG.Conv.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T17:36:00.388212+00:00
-- url     : https://prove2.me/submissions/65db94af-44b3-476d-9ba8-952b3bb9e5c1

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


namespace WFMFGmaxL

lemma maxPrincipleL {I : Type*} (u u' : I → ℝ → ℝ) (T G R L : ℝ) (hT : 0 < T) (hG : 0 ≤ G)
    (hR : 0 < R) (hL : 0 ≤ L)
    (hd : ∀ i, ∀ s ∈ Set.Icc 0 T, HasDerivWithinAt (u i) (u' i s) (Set.Icc 0 T) s)
    (hTerm : ∀ i, u i T ≤ 0)
    (hbd : ∀ i, ∀ s ∈ Set.Icc 0 T, u i s ≤ G)
    (hgen : ∀ i, ∀ s ∈ Set.Icc 0 T, ∀ h : ℝ, 0 ≤ h → (∀ j, u j s ≤ h) →
      -R * (h - u i s) - L * h ≤ u' i s) :
    ∀ i, ∀ s ∈ Set.Icc 0 T, u i s ≤ 0 := by
  have step : ∀ n : ℕ, ∀ i, ∀ s ∈ Set.Icc 0 T,
      u i s ≤ G * ((R + L) * (T - s)) ^ n / (n.factorial : ℝ) := by
    intro n
    induction n with
    | zero => intro i s hs; simpa using hbd i s hs
    | succ n ih =>
      intro i s hs
      have hcont : ContinuousOn (u i) (Set.Icc 0 T) := fun s hs => (hd i s hs).continuousWithinAt
      let f : ℝ → ℝ := fun τ => u i (T - τ)
      let B : ℝ → ℝ := fun τ => G * ((R + L) * τ) ^ (n + 1) / ((n + 1).factorial : ℝ)
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
      have hBd : ∀ τ : ℝ, HasDerivAt B (G * (R + L) * ((R + L) * τ) ^ n / (n.factorial : ℝ)) τ := by
        intro τ
        have h1 : HasDerivAt (fun τ : ℝ => (R + L) * τ) (R + L) τ := by
          simpa using (hasDerivAt_id τ).const_mul (R + L)
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
          (B := fun τ => B τ + ε) (B' := fun τ => G * (R + L) * ((R + L) * τ) ^ n / (n.factorial : ℝ))
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
          have hall : ∀ j, u j (T - τ) ≤ G * ((R + L) * τ) ^ n / (n.factorial : ℝ) := by
            intro j
            have := ih j (T - τ) hτ'
            simpa using this
          have hh0 : 0 ≤ G * ((R + L) * τ) ^ n / (n.factorial : ℝ) := by
            have : 0 ≤ (R + L) * τ := mul_nonneg (by linarith) hτ.1
            positivity
          have hg := hgen i (T - τ) hτ' _ hh0 hall
          have hB0 : 0 ≤ B τ := by
            simp only [B]
            have : 0 ≤ (R + L) * τ := mul_nonneg (by linarith) hτ.1
            positivity
          have hfe : u i (T - τ) = B τ + ε := heq
          rw [hfe] at hg
          have : 0 < R * (B τ + ε) := mul_pos hR (by linarith)
          have e : G * (R + L) * ((R + L) * τ) ^ n / (n.factorial : ℝ)
              = R * (G * ((R + L) * τ) ^ n / (n.factorial : ℝ))
                + L * (G * ((R + L) * τ) ^ n / (n.factorial : ℝ)) := by ring
          rw [e]
          nlinarith
      have h := le_of_forall_pos_le_add key
      simpa [f, B] using h
  intro i s hs
  have ht := (FloorSemiring.tendsto_pow_div_factorial_atTop ((R + L) * (T - s))).const_mul G
  rw [mul_zero] at ht
  refine ge_of_tendsto' ht (fun n => ?_)
  have := step n i s hs
  rw [mul_div_assoc] at this
  exact this

end WFMFGmaxL

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

namespace WFMFG31

open WFMFG32

variable {d N : ℕ}

/-- the linear jump operator with rates frozen at `v`, applied to `D`. -/
noncomputable def RateOp (ε : ℝ) (φ : ℝ → ℝ)
    (v D : Fin N → (Fin N → Fin d) → (Fin N → ℚ) → ℝ) (l : Fin N) (x : Fin N → Fin d)
    (y : Fin N → ℚ) : ℝ :=
  (∑ m, ∑ j, φ (empMeas x y j) * (D l (Function.update x m j) y - D l x y))
  + ∑ m ∈ univ.erase l, ∑ j, astar (x m) (fun j' => v m (Function.update x m j') y) j
      * (D l (Function.update x m j) y - D l x y)
  + ε * N * multE N (empMeas x y)
      (fun k => (ratioQ x y k l : ℝ) * (D l x (reweight x y k) - D l x y))

lemma nash_split (ε : ℝ) (φ : ℝ → ℝ) (f : Fin d → (Fin d → ℝ) → ℝ)
    (v : Fin N → (Fin N → Fin d) → (Fin N → ℚ) → ℝ) (l : Fin N) (t : ℝ)
    (x : Fin N → Fin d) (y : Fin N → ℚ) :
    nashOp ε φ f (fun l' _ x' y' => v l' x' y') l t x y
      = RateOp ε φ v v l x y + ham (x l) (fun j => v l (Function.update x l j) y)
        + f (x l) (empMeas x y) := by
  unfold nashOp driftOp RateOp; ring

lemma rate_up (hN : 1 ≤ N) (ε κ δ B : ℝ) (hε : 0 ≤ ε) (hδ : 0 < δ) (φ : ℝ → ℝ)
    (hφ : IsCutoff κ δ φ)
    (v D : Fin N → (Fin N → Fin d) → (Fin N → ℚ) → ℝ) (l : Fin N) (x : Fin N → Fin d)
    (y : Fin N → ℚ) (hy : y ∈ Yset N) (hv : ∀ m x', |v m x' y| ≤ B) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hD1 : ∀ x', D l x' y - D l x y ≤ Δ)
    (hD2 : ∀ y' ∈ Yset N, D l x y' - D l x y ≤ Δ) :
    RateOp ε φ v D l x y ≤ (N * d * κ + N * d * (2 * B) + ε * N) * Δ := by
  obtain ⟨hφ0, hφanti, _, hφκ, _⟩ := hφ
  have hφb : ∀ r, 0 ≤ r → φ r ≤ κ := by
    intro r hr
    have h0 := hφκ 0 ⟨le_refl _, hδ.le⟩
    rw [← h0]
    exact hφanti (Set.mem_Ici.2 (le_refl 0)) (Set.mem_Ici.2 hr) hr
  have hμ0 : ∀ j, 0 ≤ empMeas x y j := (emp_std hN x y hy).1
  unfold RateOp
  have hin1 : ∀ m, ∑ j, φ (empMeas x y j) * (D l (Function.update x m j) y - D l x y)
      ≤ d * (κ * Δ) := by
    intro m
    have := sum_le_card (Finset.univ : Finset (Fin d))
      (fun j => φ (empMeas x y j) * (D l (Function.update x m j) y - D l x y)) (κ * Δ)
      (fun j _ => le_trans (mul_le_mul_of_nonneg_left (hD1 _) (hφ0 _ (hμ0 j)))
        (mul_le_mul_of_nonneg_right (hφb _ (hμ0 j)) hΔ))
    simpa using this
  have h1 : ∑ m, ∑ j, φ (empMeas x y j) * (D l (Function.update x m j) y - D l x y)
      ≤ N * d * κ * Δ := by
    have := sum_le_card (Finset.univ : Finset (Fin N)) _ _ (fun m _ => hin1 m)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    linarith
  have hin2 : ∀ m, ∑ j, astar (x m) (fun j' => v m (Function.update x m j') y) j *
        (D l (Function.update x m j) y - D l x y) ≤ d * (2 * B * Δ) := by
    intro m
    have := sum_le_card (Finset.univ : Finset (Fin d))
      (fun j => astar (x m) (fun j' => v m (Function.update x m j') y) j *
        (D l (Function.update x m j) y - D l x y)) (2 * B * Δ)
      (fun j _ => le_trans (mul_le_mul_of_nonneg_left (hD1 _) (pos_nonneg _))
        (mul_le_mul_of_nonneg_right (pos_le_two _ _ _ (hv _ _) (hv _ _)) hΔ))
    simpa using this
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hv l x)
  have h2 : ∑ m ∈ Finset.univ.erase l, ∑ j,
      astar (x m) (fun j' => v m (Function.update x m j') y) j *
        (D l (Function.update x m j) y - D l x y) ≤ N * d * (2 * B) * Δ := by
    have := sum_le_card (Finset.univ.erase l) _ _ (fun m _ => hin2 m)
    have hc : ((Finset.univ.erase l).card : ℝ) ≤ N := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ l)]
      simp
    have : (((Finset.univ.erase l).card : ℝ)) * (d * (2 * B * Δ)) ≤ N * (d * (2 * B * Δ)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    linarith
  have h3 : multE N (empMeas x y) (fun k => (ratioQ x y k l : ℝ) * (D l x (reweight x y k) - D l x y))
      ≤ Δ := by
    unfold multE
    calc _ ≤ ∑ k ∈ Finset.Nat.antidiagonalTuple d N,
          multW (empMeas x y) k * (ratioQ x y k l : ℝ) * Δ := by
          apply Finset.sum_le_sum
          intro k hk
          by_cases hz : multW (empMeas x y) k = 0
          · simp [hz]
          · have hm := reweight_mem hN x y hy k hk hz
            have h1 := hD2 _ hm
            have h2 := multW_nonneg _ hμ0 k
            have h3 : (0:ℝ) ≤ ratioQ x y k l := by exact_mod_cast ratioQ_nonneg x y hy k l
            rw [mul_assoc]
            apply mul_le_mul_of_nonneg_left _ h2
            exact mul_le_mul_of_nonneg_left h1 h3
      _ = Δ := by rw [← Finset.sum_mul, noise_mass hN x y hy l, one_mul]
  have hεN : 0 ≤ ε * N := by positivity
  have := mul_le_mul_of_nonneg_left h3 hεN
  nlinarith

lemma rate_lo (hN : 1 ≤ N) (ε κ δ B : ℝ) (hε : 0 ≤ ε) (hδ : 0 < δ) (φ : ℝ → ℝ)
    (hφ : IsCutoff κ δ φ)
    (v D : Fin N → (Fin N → Fin d) → (Fin N → ℚ) → ℝ) (l : Fin N) (x : Fin N → Fin d)
    (y : Fin N → ℚ) (hy : y ∈ Yset N) (hv : ∀ m x', |v m x' y| ≤ B) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hD1 : ∀ x', -Δ ≤ D l x' y - D l x y)
    (hD2 : ∀ y' ∈ Yset N, -Δ ≤ D l x y' - D l x y) :
    -((N * d * κ + N * d * (2 * B) + ε * N) * Δ) ≤ RateOp ε φ v D l x y := by
  have := rate_up hN ε κ δ B hε hδ φ hφ v (fun l x y => -D l x y) l x y hy hv Δ hΔ
    (fun x' => by have := hD1 x'; linarith) (fun y' hy' => by have := hD2 y' hy'; linarith)
  have e : RateOp ε φ v (fun l x y => -D l x y) l x y = -RateOp ε φ v D l x y := by
    unfold RateOp multE
    simp only [neg_sub_neg, ← neg_sub (D l _ _) (D l x y), mul_neg, Finset.sum_neg_distrib]
    ring
  rw [e] at this
  linarith

lemma ham_lo (v : Fin N → (Fin N → Fin d) → (Fin N → ℚ) → ℝ) (l : Fin N) (x : Fin N → Fin d)
    (y : Fin N → ℚ) (B Δ : ℝ) (hΔ : 0 ≤ Δ) (hv : ∀ x', |v l x' y| ≤ B)
    (hD : ∀ x', -Δ ≤ v l x' y - v l x y) :
    -(d * (2 * B) * Δ) ≤ ham (x l) (fun j => v l (Function.update x l j) y) := by
  unfold ham
  have hxl : Function.update x l (x l) = x := Function.update_eq_self l x
  have hterm : ∀ j, -(2 * B * Δ) ≤
      -(pos (v l (Function.update x l (x l)) y - v l (Function.update x l j) y) ^ 2) := by
    intro j
    set a := v l (Function.update x l (x l)) y - v l (Function.update x l j) y with ha
    have hpa : pos a ^ 2 = pos a * a := by
      unfold pos
      rcases le_total a 0 with h | h
      · rw [max_eq_right h]; ring
      · rw [max_eq_left h]; ring
    have hp0 := pos_nonneg a
    have hp2 := pos_le_two _ _ _ (hv (Function.update x l (x l))) (hv (Function.update x l j))
    have hDa : a ≤ Δ := by
      have := hD (Function.update x l j); rw [ha, hxl]; linarith
    rw [hpa]
    nlinarith
  have := sum_ge_card (Finset.univ : Finset (Fin d)) _ (2 * B * Δ) (fun j _ => hterm j)
  simp only [Finset.card_univ, Fintype.card_fin, Finset.sum_neg_distrib] at this
  have hs : 0 ≤ ∑ j, pos (v l (Function.update x l (x l)) y - v l (Function.update x l j) y) ^ 2 :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  nlinarith

lemma ham_up (v : Fin N → (Fin N → Fin d) → (Fin N → ℚ) → ℝ) (l : Fin N) (x : Fin N → Fin d)
    (y : Fin N → ℚ) : ham (x l) (fun j => v l (Function.update x l j) y) ≤ 0 := by
  unfold ham
  have : 0 ≤ ∑ j, pos (v l (Function.update x l (x l)) y - v l (Function.update x l j) y) ^ 2 :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  linarith

end WFMFG31

namespace WFMFG31b

open WFMFG32 WFMFG31

variable {d N : ℕ}

lemma pos_sq_sub (a b : ℝ) : |pos a ^ 2 - pos b ^ 2| ≤ |a - b| * (|a| + |b|) := by
  have h1 : |pos a - pos b| ≤ |a - b| := abs_max_sub_max_le_abs a b 0
  have ha : |pos a| ≤ |a| := by
    unfold pos; rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self a) (abs_nonneg a)
  have hb : |pos b| ≤ |b| := by
    unfold pos; rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self b) (abs_nonneg b)
  rw [sq_sub_sq, abs_mul, mul_comm]
  have := abs_add_le (pos a) (pos b)
  exact mul_le_mul h1 (by linarith) (abs_nonneg _) (abs_nonneg _)

lemma abs_sub_two (a b c e h : ℝ) (h1 : |a - c| ≤ h) (h2 : |b - e| ≤ h) :
    |(a - b) - (c - e)| ≤ 2 * h := by
  have : (a - b) - (c - e) = (a - c) - (b - e) := by ring
  rw [this]
  have := abs_sub (a - c) (b - e)
  linarith

lemma nash_diff (ε : ℝ) (φ : ℝ → ℝ) (f : Fin d → (Fin d → ℝ) → ℝ)
    (v1 v2 : Fin N → (Fin N → Fin d) → (Fin N → ℚ) → ℝ) (l : Fin N) (t : ℝ)
    (x : Fin N → Fin d) (y : Fin N → ℚ) (B h : ℝ)
    (hv1 : ∀ m x', |v1 m x' y| ≤ B) (hv2 : ∀ m x', |v2 m x' y| ≤ B)
    (hh : ∀ m x', |v1 m x' y - v2 m x' y| ≤ h) :
    |nashOp ε φ f (fun l' _ x' y' => v1 l' x' y') l t x y
      - nashOp ε φ f (fun l' _ x' y' => v2 l' x' y') l t x y
      - RateOp ε φ v1 (fun l x y => v1 l x y - v2 l x y) l x y|
      ≤ (N * d * (4 * B) + d * (4 * B)) * h := by
  rw [nash_split, nash_split]
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hv1 l x)
  have hh0 : 0 ≤ h := le_trans (abs_nonneg _) (hh l x)
  set a1 : Fin N → Fin d → ℝ := fun m j => astar (x m) (fun j' => v1 m (Function.update x m j') y) j
  set a2 : Fin N → Fin d → ℝ := fun m j => astar (x m) (fun j' => v2 m (Function.update x m j') y) j
  have hR : RateOp ε φ v1 v1 l x y - RateOp ε φ v2 v2 l x y
      - RateOp ε φ v1 (fun l x y => v1 l x y - v2 l x y) l x y
      = ∑ m ∈ univ.erase l, ∑ j, (a1 m j - a2 m j)
          * (v2 l (Function.update x m j) y - v2 l x y) := by
    unfold RateOp multE
    have hA : (∑ m, ∑ j, φ (empMeas x y j) * (v1 l (Function.update x m j) y - v1 l x y))
        - (∑ m, ∑ j, φ (empMeas x y j) * (v2 l (Function.update x m j) y - v2 l x y))
        - (∑ m, ∑ j, φ (empMeas x y j) * ((v1 l (Function.update x m j) y
            - v2 l (Function.update x m j) y) - (v1 l x y - v2 l x y))) = 0 := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_eq_zero; intro m _
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_eq_zero; intro j _; ring
    have hBm : (∑ m ∈ univ.erase l, ∑ j, a1 m j * (v1 l (Function.update x m j) y - v1 l x y))
        - (∑ m ∈ univ.erase l, ∑ j, a2 m j * (v2 l (Function.update x m j) y - v2 l x y))
        - (∑ m ∈ univ.erase l, ∑ j, a1 m j * ((v1 l (Function.update x m j) y
            - v2 l (Function.update x m j) y) - (v1 l x y - v2 l x y)))
        = ∑ m ∈ univ.erase l, ∑ j, (a1 m j - a2 m j)
          * (v2 l (Function.update x m j) y - v2 l x y) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro m _
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _; ring
    have hC : (∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW (empMeas x y) k *
          ((ratioQ x y k l : ℝ) * (v1 l x (reweight x y k) - v1 l x y)))
        - (∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW (empMeas x y) k *
          ((ratioQ x y k l : ℝ) * (v2 l x (reweight x y k) - v2 l x y)))
        - (∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW (empMeas x y) k *
          ((ratioQ x y k l : ℝ) * ((v1 l x (reweight x y k) - v2 l x (reweight x y k))
            - (v1 l x y - v2 l x y)))) = 0 := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_eq_zero; intro k _; ring
    simp only [a1, a2] at hBm ⊢
    linear_combination hA + hBm + (ε * N) * hC
  have e : RateOp ε φ v1 v1 l x y + ham (x l) (fun j => v1 l (Function.update x l j) y)
        + f (x l) (empMeas x y)
      - (RateOp ε φ v2 v2 l x y + ham (x l) (fun j => v2 l (Function.update x l j) y)
        + f (x l) (empMeas x y))
      - RateOp ε φ v1 (fun l x y => v1 l x y - v2 l x y) l x y
      = (RateOp ε φ v1 v1 l x y - RateOp ε φ v2 v2 l x y
          - RateOp ε φ v1 (fun l x y => v1 l x y - v2 l x y) l x y)
        + (ham (x l) (fun j => v1 l (Function.update x l j) y)
          - ham (x l) (fun j => v2 l (Function.update x l j) y)) := by ring
  rw [e, hR]
  refine le_trans (abs_add_le _ _) ?_
  have h1 : |∑ m ∈ univ.erase l, ∑ j, (a1 m j - a2 m j)
          * (v2 l (Function.update x m j) y - v2 l x y)| ≤ N * d * (4 * B) * h := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hin : ∀ m, |∑ j, (a1 m j - a2 m j) * (v2 l (Function.update x m j) y - v2 l x y)|
        ≤ d * (4 * B * h) := by
      intro m
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have := sum_le_card (Finset.univ : Finset (Fin d)) (fun j =>
        |(a1 m j - a2 m j) * (v2 l (Function.update x m j) y - v2 l x y)|) (4 * B * h)
        (fun j _ => by
          rw [abs_mul]
          have ha : |a1 m j - a2 m j| ≤ 2 * h := by
            simp only [a1, a2, astar]
            refine le_trans (abs_max_sub_max_le_abs _ _ 0) ?_
            exact abs_sub_two _ _ _ _ _ (hh _ _) (hh _ _)
          have hb : |v2 l (Function.update x m j) y - v2 l x y| ≤ 2 * B := by
            have := abs_sub (v2 l (Function.update x m j) y) (v2 l x y)
            have := hv2 l (Function.update x m j); have := hv2 l x; linarith
          have := mul_le_mul ha hb (abs_nonneg _) (by linarith)
          linarith)
      simpa using this
    have := sum_le_card (Finset.univ.erase l) _ _ (fun m _ => hin m)
    have hc : ((Finset.univ.erase l).card : ℝ) ≤ N := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ l)]
      simp
    have : (((Finset.univ.erase l).card : ℝ)) * (d * (4 * B * h)) ≤ N * (d * (4 * B * h)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    linarith
  have h2 : |ham (x l) (fun j => v1 l (Function.update x l j) y)
          - ham (x l) (fun j => v2 l (Function.update x l j) y)| ≤ d * (4 * B) * h := by
    unfold ham
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul]
    have hin := Finset.abs_sum_le_sum_abs (fun j =>
      pos (v1 l (Function.update x l (x l)) y - v1 l (Function.update x l j) y) ^ 2
      - pos (v2 l (Function.update x l (x l)) y - v2 l (Function.update x l j) y) ^ 2) univ
    have := sum_le_card (Finset.univ : Finset (Fin d)) (fun j =>
      |pos (v1 l (Function.update x l (x l)) y - v1 l (Function.update x l j) y) ^ 2
      - pos (v2 l (Function.update x l (x l)) y - v2 l (Function.update x l j) y) ^ 2|) (8 * B * h)
      (fun j _ => by
        refine le_trans (pos_sq_sub _ _) ?_
        have ha := abs_sub_two _ _ _ _ _ (hh l (Function.update x l (x l)))
          (hh l (Function.update x l j))
        have hb1 : |v1 l (Function.update x l (x l)) y - v1 l (Function.update x l j) y| ≤ 2 * B := by
          have := abs_sub (v1 l (Function.update x l (x l)) y) (v1 l (Function.update x l j) y)
          have := hv1 l (Function.update x l (x l)); have := hv1 l (Function.update x l j); linarith
        have hb2 : |v2 l (Function.update x l (x l)) y - v2 l (Function.update x l j) y| ≤ 2 * B := by
          have := abs_sub (v2 l (Function.update x l (x l)) y) (v2 l (Function.update x l j) y)
          have := hv2 l (Function.update x l (x l)); have := hv2 l (Function.update x l j); linarith
        have := mul_le_mul ha (add_le_add hb1 hb2) (by positivity) (by linarith)
        linarith)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    have habs : |(-(1:ℝ) / 2)| = 1 / 2 := by norm_num
    rw [show (-(1:ℝ) / 2) = -(1/2) by ring] at habs
    rw [habs]
    nlinarith
  nlinarith

end WFMFG31b

namespace WFMFG31c

open WFMFG32 WFMFG31 WFMFG31b WFMFGmaxL

lemma nash_congr {d N : ℕ} (ε : ℝ) (φ : ℝ → ℝ) (f : Fin d → (Fin d → ℝ) → ℝ)
    (w : Fin N → ℝ → (Fin N → Fin d) → (Fin N → ℚ) → ℝ) (l : Fin N) (s : ℝ)
    (x : Fin N → Fin d) (y : Fin N → ℚ) :
    nashOp ε φ f w l s x y = nashOp ε φ f (fun l' _ x' y' => w l' s x' y') l s x y := rfl

lemma uniq {d N : ℕ} (hN : 1 ≤ N) (ε T κ δ : ℝ)
    (hε0 : 0 < ε) (hT : 0 < T) (hδ : 0 < δ)
    (φ : ℝ → ℝ) (hφ : IsCutoff κ δ φ) (f g : Fin d → (Fin d → ℝ) → ℝ)
    (w w' : Fin N → ℝ → (Fin N → Fin d) → (Fin N → ℚ) → ℝ)
    (hw : IsNashSol N ε T φ f g w) (hw' : IsNashSol N ε T φ f g w') :
    ∀ (l : Fin N) (x : Fin N → Fin d), ∀ y ∈ Yset N, ∀ t ∈ Set.Icc 0 T,
      w' l t x y = w l t x y := by
  obtain ⟨hder, hterm, B1, hB1⟩ := hw
  obtain ⟨hder', hterm', B2, hB2⟩ := hw'
  set B : ℝ := |B1| + |B2| with hBdef
  have hB : ∀ l x, ∀ y ∈ Yset N, ∀ t ∈ Set.Icc 0 T, |w l t x y| ≤ B := fun l x y hy t ht => by
    have := hB1 l x y hy t ht; have := le_abs_self B1; have := abs_nonneg B2; linarith
  have hB' : ∀ l x, ∀ y ∈ Yset N, ∀ t ∈ Set.Icc 0 T, |w' l t x y| ≤ B := fun l x y hy t ht => by
    have := hB2 l x y hy t ht; have := le_abs_self B2; have := abs_nonneg B1; linarith
  have hB0 : 0 ≤ B := by positivity
  have hκ0 : 0 ≤ κ := by
    have := hφ.2.2.2.1 0 ⟨le_refl _, hδ.le⟩; rw [← this]; exact hφ.1 0 (le_refl _)
  let I := {p : Fin N × (Fin N → Fin d) × (Fin N → ℚ) // p.2.2 ∈ Yset N}
  let D : I → ℝ → ℝ := fun α s => w α.1.1 s α.1.2.1 α.1.2.2 - w' α.1.1 s α.1.2.1 α.1.2.2
  let D' : I → ℝ → ℝ := fun α s => -(nashOp ε φ f w α.1.1 s α.1.2.1 α.1.2.2)
      - -(nashOp ε φ f w' α.1.1 s α.1.2.1 α.1.2.2)
  let u : I × Bool → ℝ → ℝ := fun p s => if p.2 then D p.1 s else -D p.1 s
  let u' : I × Bool → ℝ → ℝ := fun p s => if p.2 then D' p.1 s else -D' p.1 s
  set R1 : ℝ := N * d * κ + N * d * (2 * B) + ε * N with hR1def
  set Lc : ℝ := N * d * (4 * B) + d * (4 * B) with hLcdef
  have hR1 : 0 ≤ R1 := by rw [hR1def]; positivity
  have hLc0 : 0 ≤ Lc := by rw [hLcdef]; positivity
  have hmax := maxPrincipleL u u' T (2 * B) (R1 + 1) Lc hT (by linarith) (by linarith) hLc0
    (by
      intro p s hs
      have hD : HasDerivWithinAt (D p.1) (D' p.1 s) (Set.Icc 0 T) s :=
        (hder p.1.1.1 p.1.1.2.1 p.1.1.2.2 p.1.2 s hs).sub
          (hder' p.1.1.1 p.1.1.2.1 p.1.1.2.2 p.1.2 s hs)
      rcases p with ⟨α, b⟩
      cases b
      · exact (show HasDerivWithinAt (fun s => -D α s) (-D' α s) (Set.Icc 0 T) s from hD.neg)
      · exact (show HasDerivWithinAt (fun s => D α s) (D' α s) (Set.Icc 0 T) s from hD))
    (by
      intro p
      rcases p with ⟨⟨⟨l, x, y⟩, hy⟩, b⟩
      have : D ⟨⟨l, x, y⟩, hy⟩ T = 0 := by
        simp only [D]; rw [hterm l x y hy, hterm' l x y hy]; ring
      cases b <;> simp [u, this])
    (by
      intro p s hs
      rcases p with ⟨⟨⟨l, x, y⟩, hy⟩, b⟩
      have h1 := hB l x y hy s hs
      have h2 := hB' l x y hy s hs
      have : |D ⟨⟨l, x, y⟩, hy⟩ s| ≤ 2 * B := by
        simp only [D]
        have := abs_sub (w l s x y) (w' l s x y); linarith
      cases b <;> simp only [u, Bool.false_eq_true, if_false, if_true] <;>
        [linarith [neg_abs_le (D ⟨⟨l, x, y⟩, hy⟩ s)]; linarith [le_abs_self (D ⟨⟨l, x, y⟩, hy⟩ s)]])
    (by
      intro p s hs h hh0 hall
      rcases p with ⟨⟨⟨l, x, y⟩, hy⟩, b⟩
      have habs : ∀ (l' : Fin N) (x' : Fin N → Fin d) (y' : Fin N → ℚ) (hy' : y' ∈ Yset N),
          |w l' s x' y' - w' l' s x' y'| ≤ h := by
        intro l' x' y' hy'
        have h1 := hall ⟨⟨⟨l', x', y'⟩, hy'⟩, true⟩
        have h2 := hall ⟨⟨⟨l', x', y'⟩, hy'⟩, false⟩
        simp only [u, D, if_true, Bool.false_eq_true, if_false] at h1 h2
        rw [abs_le]; constructor <;> linarith
      have hnd := nash_diff ε φ f (fun l' x' y' => w l' s x' y') (fun l' x' y' => w' l' s x' y')
        l s x y B h (fun m x' => hB m x' y hy s hs) (fun m x' => hB' m x' y hy s hs)
        (fun m x' => habs m x' y hy)
      rw [← nash_congr, ← nash_congr] at hnd
      have hnd' := abs_le.1 hnd
      set Dl := w l s x y - w' l s x y with hDl
      cases b
      · -- u = -D
        show -(R1 + 1) * (h - -(w l s x y - w' l s x y)) - Lc * h
          ≤ -(-(nashOp ε φ f w l s x y) - -(nashOp ε φ f w' l s x y))
        have hΔ : 0 ≤ h + Dl := by have := abs_le.1 (habs l x y hy); linarith
        have hr := rate_lo hN ε κ δ B hε0.le hδ φ hφ (fun l' x' y' => w l' s x' y')
          (fun l x y => w l s x y - w' l s x y) l x y hy (fun m x' => hB m x' y hy s hs)
          (h + Dl) hΔ
          (fun x' => by have := abs_le.1 (habs l x' y hy); simp only [hDl] at *; linarith)
          (fun y' hy' => by have := abs_le.1 (habs l x y' hy'); simp only [hDl] at *; linarith)
        have : R1 * (h + Dl) ≤ (R1 + 1) * (h - -Dl) := by nlinarith
        rw [← hR1def] at hr
        rw [← hLcdef] at hnd'
        nlinarith
      · show -(R1 + 1) * (h - (w l s x y - w' l s x y)) - Lc * h
          ≤ -(nashOp ε φ f w l s x y) - -(nashOp ε φ f w' l s x y)
        have hΔ : 0 ≤ h - Dl := by have := abs_le.1 (habs l x y hy); linarith
        have hr := rate_up hN ε κ δ B hε0.le hδ φ hφ (fun l' x' y' => w l' s x' y')
          (fun l x y => w l s x y - w' l s x y) l x y hy (fun m x' => hB m x' y hy s hs)
          (h - Dl) hΔ
          (fun x' => by have := abs_le.1 (habs l x' y hy); simp only [hDl] at *; linarith)
          (fun y' hy' => by have := abs_le.1 (habs l x y' hy'); simp only [hDl] at *; linarith)
        have : R1 * (h - Dl) ≤ (R1 + 1) * (h - Dl) := by nlinarith
        rw [← hR1def] at hr
        rw [← hLcdef] at hnd'
        nlinarith)
  intro l x y hy t ht
  have h1 := hmax ⟨⟨⟨l, x, y⟩, hy⟩, true⟩ t ht
  have h2 := hmax ⟨⟨⟨l, x, y⟩, hy⟩, false⟩ t ht
  simp only [u, D, if_true, Bool.false_eq_true, if_false] at h1 h2
  linarith

end WFMFG31c

namespace WFMFG31d

open WFMFG32 WFMFG31 WFMFG31b WFMFG31c WFMFGmaxL

noncomputable def clip (M r : ℝ) : ℝ := max (-M) (min r M)

lemma clip_abs (M r : ℝ) (hM : 0 ≤ M) : |clip M r| ≤ M := by
  unfold clip; rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_right _ _)

lemma clip_lip (M a b : ℝ) : |clip M a - clip M b| ≤ |a - b| := by
  unfold clip
  have h1 := abs_max_sub_max_le_max (-M) (min a M) (-M) (min b M)
  have h2 := abs_min_sub_min_le_max a M b M
  simp only [sub_self, abs_zero] at h1 h2
  have h3 : max 0 |min a M - min b M| = |min a M - min b M| := max_eq_right (abs_nonneg _)
  have h4 : max |a - b| 0 = |a - b| := max_eq_left (abs_nonneg _)
  rw [h3] at h1; rw [h4] at h2; linarith

lemma clip_of_abs (M r : ℝ) (h : |r| ≤ M) : clip M r = r := by
  unfold clip
  have := abs_le.1 h
  rw [min_eq_left this.2, max_eq_right this.1]

lemma clip_mono (M : ℝ) {a b : ℝ} (h : a ≤ b) : clip M a ≤ clip M b := by
  unfold clip; exact max_le_max (le_refl _) (min_le_min h (le_refl _))

lemma clip_diff_le (M a b Δ : ℝ) (hΔ : 0 ≤ Δ) (h : a - b ≤ Δ) : clip M a - clip M b ≤ Δ := by
  rcases le_total a b with hab | hab
  · have := clip_mono M hab; linarith
  · have h1 := clip_lip M a b
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ a - b)] at h1
    have := le_abs_self (clip M a - clip M b)
    linarith

lemma clip_diff_ge (M a b Δ : ℝ) (hΔ : 0 ≤ Δ) (h : -Δ ≤ a - b) : -Δ ≤ clip M a - clip M b := by
  have := clip_diff_le M b a Δ hΔ (by linarith)
  linarith

lemma clip_zero (M : ℝ) (hM : 0 ≤ M) : clip M 0 = 0 := clip_of_abs M 0 (by simpa using hM)

lemma apriori {d N : ℕ} [NeZero d] (hN : 1 ≤ N) (ε T κ δ Mf Mg M : ℝ)
    (hε0 : 0 < ε) (hT : 0 < T) (hδ : 0 < δ) (hM : 0 ≤ M)
    (φ : ℝ → ℝ) (hφ : IsCutoff κ δ φ) (f g : Fin d → (Fin d → ℝ) → ℝ)
    (hf : ∀ i, ∀ p ∈ stdSimplex ℝ (Fin d), |f i p| ≤ Mf)
    (hg : ∀ i, ∀ p ∈ stdSimplex ℝ (Fin d), |g i p| ≤ Mg)
    (w : Fin N → ℝ → (Fin N → Fin d) → (Fin N → ℚ) → ℝ)
    (hder : ∀ l x, ∀ y ∈ Yset N, ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt (fun s => w l s x y)
        (-(nashOp ε φ f (fun l' _ x' y' => clip M (w l' t x' y')) l t x y)) (Set.Icc 0 T) t)
    (hterm : ∀ l x, ∀ y ∈ Yset N, w l T x y = g (x l) (empMeas x y))
    (hB : ∃ B : ℝ, ∀ l x, ∀ y ∈ Yset N, ∀ t ∈ Set.Icc 0 T, |w l t x y| ≤ B) :
    ∀ l x, ∀ y ∈ Yset N, ∀ t ∈ Set.Icc 0 T, |w l t x y| ≤ T * Mf + Mg := by
  obtain ⟨B0, hB0⟩ := hB
  set B : ℝ := |B0| with hBdef
  have hBw : ∀ l x, ∀ y ∈ Yset N, ∀ t ∈ Set.Icc 0 T, |w l t x y| ≤ B := fun l x y hy t ht =>
    le_trans (hB0 l x y hy t ht) (le_abs_self _)
  have hκ0 : 0 ≤ κ := by
    have := hφ.2.2.2.1 0 ⟨le_refl _, hδ.le⟩; rw [← this]; exact hφ.1 0 (le_refl _)
  let I := {p : Fin N × (Fin N → Fin d) × (Fin N → ℚ) // p.2.2 ∈ Yset N}
  let b : ℝ → ℝ := fun s => Mg + (T - s) * Mf
  have hbd : ∀ s : ℝ, HasDerivAt b (-Mf) s := by
    intro s
    have := ((hasDerivAt_id s).const_sub T).mul_const Mf
    have := this.const_add Mg
    simpa [b] using this
  set R1 : ℝ := N * d * κ + N * d * (2 * M) + ε * N with hR1def
  set R : ℝ := R1 + d * (2 * M) + 1 with hRdef
  have hR1 : 0 ≤ R1 := by rw [hR1def]; positivity
  have hR : 0 < R := by rw [hRdef]; positivity
  set G : ℝ := B + |Mg| + T * |Mf| with hGdef
  have hG : 0 ≤ G := by simp only [hGdef]; positivity
  have hbabs : ∀ s ∈ Set.Icc 0 T, |b s| ≤ |Mg| + T * |Mf| := by
    intro s hs
    simp only [b]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_of_nonneg (by linarith [hs.2] : (0:ℝ) ≤ T - s)]
    have : (T - s) * |Mf| ≤ T * |Mf| := mul_le_mul_of_nonneg_right (by linarith [hs.1]) (abs_nonneg _)
    linarith
  let V : ℝ → Fin N → (Fin N → Fin d) → (Fin N → ℚ) → ℝ := fun s l x y => clip M (w l s x y)
  have hV : ∀ s m x' (y : Fin N → ℚ), |V s m x' y| ≤ M := fun s m x' y => clip_abs M _ hM
  have hsplit : ∀ l s x y, nashOp ε φ f (fun l' _ x' y' => clip M (w l' s x' y')) l s x y
      = RateOp ε φ (V s) (V s) l x y + ham (x l) (fun j => V s l (Function.update x l j) y)
        + f (x l) (empMeas x y) := fun l s x y => nash_split ε φ f (V s) l s x y
  have hup := maxPrincipleL (I := I)
    (fun α s => w α.1.1 s α.1.2.1 α.1.2.2 - b s)
    (fun α s => -(nashOp ε φ f (fun l' _ x' y' => clip M (w l' s x' y')) α.1.1 s α.1.2.1 α.1.2.2)
      - -Mf) T G R 0 hT hG hR le_rfl
    (fun α s hs => (hder α.1.1 α.1.2.1 α.1.2.2 α.2 s hs).sub (hbd s).hasDerivWithinAt)
    (fun α => by
      have := hterm α.1.1 α.1.2.1 α.1.2.2 α.2
      have hgb := hg (α.1.2.1 α.1.1) _ (emp_std hN α.1.2.1 α.1.2.2 α.2)
      simp only [b, sub_self, zero_mul, add_zero, this]
      linarith [le_abs_self (g (α.1.2.1 α.1.1) (empMeas α.1.2.1 α.1.2.2))])
    (fun α s hs => by
      have h1 := hBw α.1.1 α.1.2.1 α.1.2.2 α.2 s hs
      have h2 := hbabs s hs
      have h3 := neg_abs_le (b s)
      have h4 := le_abs_self (w α.1.1 s α.1.2.1 α.1.2.2)
      simp only [hGdef]; linarith)
    (by
      intro α s hs h hh0 hall
      obtain ⟨⟨l, x, y⟩, hy⟩ := α
      simp only at hall ⊢
      have hΔ : 0 ≤ h - (w l s x y - b s) := by linarith [hall ⟨⟨l, x, y⟩, hy⟩]
      set Δ := h - (w l s x y - b s) with hΔdef
      have hDx : ∀ x', V s l x' y - V s l x y ≤ Δ := by
        intro x'; have := hall ⟨⟨l, x', y⟩, hy⟩; simp only at this
        exact clip_diff_le M _ _ Δ hΔ (by linarith)
      have hDy : ∀ y' ∈ Yset N, V s l x y' - V s l x y ≤ Δ := by
        intro y' hy'; have := hall ⟨⟨l, x, y'⟩, hy'⟩; simp only at this
        exact clip_diff_le M _ _ Δ hΔ (by linarith)
      have hr := rate_up hN ε κ δ M hε0.le hδ φ hφ (V s) (V s) l x y hy (fun m x' => hV s m x' y)
        Δ hΔ hDx hDy
      have hh := ham_up (V s) l x y
      have hfb := le_trans (le_abs_self _) (hf (x l) _ (emp_std hN x y hy))
      rw [hsplit]
      rw [← hR1def] at hr
      have : R1 * Δ ≤ R * Δ := mul_le_mul_of_nonneg_right (by
        rw [hRdef]; have : (0:ℝ) ≤ d * (2 * M) := by positivity
        linarith) hΔ
      nlinarith)
  have hlo := maxPrincipleL (I := I)
    (fun α s => -w α.1.1 s α.1.2.1 α.1.2.2 - b s)
    (fun α s => -(-(nashOp ε φ f (fun l' _ x' y' => clip M (w l' s x' y')) α.1.1 s α.1.2.1 α.1.2.2))
      - -Mf) T G R 0 hT hG hR le_rfl
    (fun α s hs => (hder α.1.1 α.1.2.1 α.1.2.2 α.2 s hs).neg.sub (hbd s).hasDerivWithinAt)
    (fun α => by
      have := hterm α.1.1 α.1.2.1 α.1.2.2 α.2
      have hgb := hg (α.1.2.1 α.1.1) _ (emp_std hN α.1.2.1 α.1.2.2 α.2)
      simp only [b, sub_self, zero_mul, add_zero, this]
      linarith [neg_abs_le (g (α.1.2.1 α.1.1) (empMeas α.1.2.1 α.1.2.2))])
    (fun α s hs => by
      have h1 := hBw α.1.1 α.1.2.1 α.1.2.2 α.2 s hs
      have h2 := hbabs s hs
      have h3 := neg_abs_le (b s)
      have h4 := neg_abs_le (w α.1.1 s α.1.2.1 α.1.2.2)
      simp only [hGdef]; linarith)
    (by
      intro α s hs h hh0 hall
      obtain ⟨⟨l, x, y⟩, hy⟩ := α
      simp only at hall ⊢
      have hΔ : 0 ≤ h - (-w l s x y - b s) := by linarith [hall ⟨⟨l, x, y⟩, hy⟩]
      set Δ := h - (-w l s x y - b s) with hΔdef
      have hDx : ∀ x', -Δ ≤ V s l x' y - V s l x y := by
        intro x'; have := hall ⟨⟨l, x', y⟩, hy⟩; simp only at this
        exact clip_diff_ge M _ _ Δ hΔ (by linarith)
      have hDy : ∀ y' ∈ Yset N, -Δ ≤ V s l x y' - V s l x y := by
        intro y' hy'; have := hall ⟨⟨l, x, y'⟩, hy'⟩; simp only at this
        exact clip_diff_ge M _ _ Δ hΔ (by linarith)
      have hr := rate_lo hN ε κ δ M hε0.le hδ φ hφ (V s) (V s) l x y hy (fun m x' => hV s m x' y)
        Δ hΔ hDx hDy
      have hh := ham_lo (V s) l x y M Δ hΔ (fun x' => hV s l x' y) hDx
      have hfb := neg_le_of_abs_le (hf (x l) _ (emp_std hN x y hy))
      rw [hsplit]
      rw [← hR1def] at hr
      have : (R1 + d * (2 * M)) * Δ ≤ R * Δ := mul_le_mul_of_nonneg_right (by
        rw [hRdef]; linarith) hΔ
      nlinarith)
  have hMf : 0 ≤ Mf := le_trans (abs_nonneg _) (hf 0 _ (emp_std hN (fun _ => 0) (fun _ => 1)
    ⟨fun _ => by norm_num, by simp⟩))
  intro l x y hy t ht
  have h1 := hup ⟨⟨l, x, y⟩, hy⟩ t ht
  have h2 := hlo ⟨⟨l, x, y⟩, hy⟩ t ht
  simp only [b] at h1 h2
  have : (T - t) * Mf ≤ T * Mf := mul_le_mul_of_nonneg_right (by linarith [ht.1]) hMf
  rw [abs_le]; constructor <;> linarith

end WFMFG31d


namespace WFMFG31e

open WFMFG32 WFMFG31 WFMFG31b WFMFG31c WFMFG31d

abbrev Idx (d N : ℕ) := {p : Fin N × (Fin N → Fin d) × (Fin N → ℚ) // p.2.2 ∈ Yset N}

open Classical in
/-- clipped extension of a coordinate vector to a time-independent 4-argument function. -/
noncomputable def ext {d N : ℕ} (M : ℝ) (v : Idx d N → ℝ) :
    Fin N → ℝ → (Fin N → Fin d) → (Fin N → ℚ) → ℝ :=
  fun l _ x y => if h : y ∈ Yset N then clip M (v ⟨(l, x, y), h⟩) else 0

noncomputable def fieldR {d N : ℕ} (ε : ℝ) (φ : ℝ → ℝ) (f : Fin d → (Fin d → ℝ) → ℝ) (M : ℝ)
    (v : Idx d N → ℝ) : Idx d N → ℝ :=
  fun α => -(nashOp ε φ f (ext M v) α.1.1 0 α.1.2.1 α.1.2.2)

lemma field_lip {d N : ℕ} (hN : 1 ≤ N) (ε κ δ M : ℝ) (hε : 0 ≤ ε) (hδ : 0 < δ) (hM : 0 ≤ M)
    (φ : ℝ → ℝ) (hφ : IsCutoff κ δ φ) (f : Fin d → (Fin d → ℝ) → ℝ)
    (v1 v2 : Idx d N → ℝ) (h : ℝ) (hh0 : 0 ≤ h)
    (hh : ∀ β, |clip M (v1 β) - clip M (v2 β)| ≤ h) (α : Idx d N) :
    |fieldR ε φ f M v1 α - fieldR ε φ f M v2 α|
      ≤ ((N * d * (4 * M) + d * (4 * M)) + 2 * (N * d * κ + N * d * (2 * M) + ε * N)) * h := by
  obtain ⟨⟨l, x, y⟩, hy⟩ := α
  set E1 : Fin N → (Fin N → Fin d) → (Fin N → ℚ) → ℝ := fun l x y => ext M v1 l 0 x y with hE1d
  set E2 : Fin N → (Fin N → Fin d) → (Fin N → ℚ) → ℝ := fun l x y => ext M v2 l 0 x y with hE2d
  have hE1 : ∀ m x' y', |E1 m x' y'| ≤ M := by
    intro m x' y'; simp only [E1, ext]; split_ifs
    · exact clip_abs M _ hM
    · simpa using hM
  have hE2 : ∀ m x' y', |E2 m x' y'| ≤ M := by
    intro m x' y'; simp only [E2, ext]; split_ifs
    · exact clip_abs M _ hM
    · simpa using hM
  have hE12 : ∀ m x' y', |E1 m x' y' - E2 m x' y'| ≤ h := by
    intro m x' y'; simp only [E1, E2, ext]; split_ifs
    · exact hh _
    · simpa using hh0
  have hnd := nash_diff ε φ f E1 E2 l 0 x y M h (fun m x' => hE1 m x' y) (fun m x' => hE2 m x' y)
    (fun m x' => hE12 m x' y)
  have hD : ∀ x' y', |(fun l x y => E1 l x y - E2 l x y) l x' y'| ≤ h := fun x' y' => hE12 l x' y'
  have hr1 := rate_up hN ε κ δ M hε hδ φ hφ E1 (fun l x y => E1 l x y - E2 l x y) l x y hy
    (fun m x' => hE1 m x' y) (2 * h) (by linarith)
    (fun x' => by have := abs_le.1 (hD x' y); have := abs_le.1 (hD x y); linarith)
    (fun y' _ => by have := abs_le.1 (hD x y'); have := abs_le.1 (hD x y); linarith)
  have hr2 := rate_lo hN ε κ δ M hε hδ φ hφ E1 (fun l x y => E1 l x y - E2 l x y) l x y hy
    (fun m x' => hE1 m x' y) (2 * h) (by linarith)
    (fun x' => by have := abs_le.1 (hD x' y); have := abs_le.1 (hD x y); linarith)
    (fun y' _ => by have := abs_le.1 (hD x y'); have := abs_le.1 (hD x y); linarith)
  have e1 : fieldR ε φ f M v1 ⟨(l, x, y), hy⟩
      = -(nashOp ε φ f (fun l' _ x' y' => E1 l' x' y') l 0 x y) := rfl
  have e2 : fieldR ε φ f M v2 ⟨(l, x, y), hy⟩
      = -(nashOp ε φ f (fun l' _ x' y' => E2 l' x' y') l 0 x y) := rfl
  rw [e1, e2]
  have := abs_le.1 hnd
  rw [abs_le]; constructor <;> nlinarith

lemma ext_zero {d N : ℕ} (M : ℝ) (hM : 0 ≤ M) :
    ext M (fun _ : Idx d N => (0:ℝ)) = fun _ _ _ _ => 0 := by
  funext l s x y; simp only [ext]; split_ifs <;> simp [clip_zero M hM]

lemma nash_zero {d N : ℕ} (ε : ℝ) (φ : ℝ → ℝ) (f : Fin d → (Fin d → ℝ) → ℝ) (l : Fin N) (t : ℝ)
    (x : Fin N → Fin d) (y : Fin N → ℚ) :
    nashOp ε φ f (fun _ _ _ _ => 0) l t x y = f (x l) (empMeas x y) := by
  simp [nashOp, driftOp, ham, pos, multE]

end WFMFG31e


namespace WFMFG31f

open WFMFG32 WFMFG31 WFMFG31b WFMFG31c WFMFG31d WFMFG31e
open scoped NNReal ENNReal

theorem exists_sol {d N : ℕ} [NeZero d] (hN : 1 ≤ N) (ε T κ δ Mf Mg : ℝ)
    (hε0 : 0 < ε) (hT : 0 < T) (hδ : 0 < δ)
    (φ : ℝ → ℝ) (hφ : IsCutoff κ δ φ) (f g : Fin d → (Fin d → ℝ) → ℝ)
    (hf : ∀ i, ∀ p ∈ stdSimplex ℝ (Fin d), |f i p| ≤ Mf)
    (hg : ∀ i, ∀ p ∈ stdSimplex ℝ (Fin d), |g i p| ≤ Mg) :
    ∃ w : Fin N → ℝ → (Fin N → Fin d) → (Fin N → ℚ) → ℝ, IsNashSol N ε T φ f g w := by
  classical
  have hY1 : (fun _ : Fin N => (1:ℚ)) ∈ Yset N := ⟨fun _ => by norm_num, by simp⟩
  have hMf : 0 ≤ Mf := le_trans (abs_nonneg _) (hf 0 _ (emp_std hN (fun _ => 0) _ hY1))
  have hMg : 0 ≤ Mg := le_trans (abs_nonneg _) (hg 0 _ (emp_std hN (fun _ => 0) _ hY1))
  set M : ℝ := T * Mf + Mg with hMdef
  have hM : 0 ≤ M := by positivity
  have hκ0 : 0 ≤ κ := by
    have := hφ.2.2.2.1 0 ⟨le_refl _, hδ.le⟩; rw [← this]; exact hφ.1 0 (le_refl _)
  set K0 : ℝ := ((N * d * (4 * M) + d * (4 * M)) + 2 * (N * d * κ + N * d * (2 * M) + ε * N))
    with hK0
  have hK0n : 0 ≤ K0 := by rw [hK0]; positivity
  set L0 : ℝ := K0 * M + Mf with hL0d
  have hL0 : 0 ≤ L0 := by rw [hL0d]; positivity
  have hbd : ∀ v : Idx d N → ℝ, ∀ α, |fieldR ε φ f M v α| ≤ L0 := by
    intro v α
    have h1 := field_lip hN ε κ δ M hε0.le hδ hM φ hφ f v (fun _ => 0) M hM
      (fun β => by rw [clip_zero M hM, sub_zero]; exact clip_abs M _ hM) α
    have h2 : fieldR ε φ f M (fun _ => 0) α = -(f (α.1.2.1 α.1.1) (empMeas α.1.2.1 α.1.2.2)) := by
      simp only [fieldR, ext_zero M hM, nash_zero]
    have h3 := hf (α.1.2.1 α.1.1) _ (emp_std hN α.1.2.1 α.1.2.2 α.2)
    rw [h2] at h1
    have := abs_sub_abs_le_abs_sub (fieldR ε φ f M v α) (-(f (α.1.2.1 α.1.1) (empMeas α.1.2.1 α.1.2.2)))
    rw [abs_neg] at this
    rw [hL0d]; linarith
  let E := lp (fun _ : Idx d N => ℝ) ∞
  let F : E → E := fun v => ⟨fieldR ε φ f M v, memℓp_infty_iff.2 ⟨L0, by
    rintro _ ⟨α, rfl⟩; exact (Real.norm_eq_abs _).le.trans (hbd _ α)⟩⟩
  have hFapp : ∀ v : E, ∀ α, (F v : Idx d N → ℝ) α = fieldR ε φ f M v α := fun v α => rfl
  have hFnorm : ∀ v : E, ‖F v‖ ≤ L0 := fun v =>
    lp.norm_le_of_forall_le hL0 (fun α => by rw [hFapp, Real.norm_eq_abs]; exact hbd _ α)
  have hFlip : LipschitzWith ⟨K0, hK0n⟩ F := by
    apply LipschitzWith.of_dist_le_mul
    intro v1 v2
    rw [dist_eq_norm, dist_eq_norm]
    apply lp.norm_le_of_forall_le (by positivity)
    intro α
    rw [lp.coeFn_sub, Pi.sub_apply, hFapp, hFapp, Real.norm_eq_abs]
    refine (field_lip hN ε κ δ M hε0.le hδ hM φ hφ f v1 v2 ‖v1 - v2‖ (norm_nonneg _)
      (fun β => ?_) α).trans (le_of_eq ?_)
    · refine (clip_lip M _ _).trans ?_
      have := lp.norm_apply_le_norm (by simp : (∞ : ℝ≥0∞) ≠ 0) (v1 - v2) β
      rw [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs] at this; exact this
    · rfl
  let G0 : E := ⟨fun β => g (β.1.2.1 β.1.1) (empMeas β.1.2.1 β.1.2.2), memℓp_infty_iff.2 ⟨Mg, by
    rintro _ ⟨β, rfl⟩
    exact (Real.norm_eq_abs _).le.trans (hg _ _ (emp_std hN β.1.2.1 β.1.2.2 β.2))⟩⟩
  have hPL : IsPicardLindelof (fun _ => F) (tmin := 0) (tmax := T) ⟨T, ⟨hT.le, le_rfl⟩⟩ G0
      ⟨L0 * T, by positivity⟩ 0 ⟨L0, hL0⟩ ⟨K0, hK0n⟩ :=
    IsPicardLindelof.of_time_independent (fun v _ => hFnorm v) (hFlip.lipschitzOnWith) (by
      simp only [NNReal.coe_mk, NNReal.coe_zero, sub_self, sub_zero]
      rw [max_eq_right hT.le]; exact le_rfl)
  obtain ⟨sol, hsol0, hsol⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hcont : ContinuousOn sol (Set.Icc 0 T) := fun t ht => (hsol t ht).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  let w : Fin N → ℝ → (Fin N → Fin d) → (Fin N → ℚ) → ℝ :=
    fun l s x y => if h : y ∈ Yset N then (sol s : Idx d N → ℝ) ⟨(l, x, y), h⟩ else 0
  have hwB : ∀ l x, ∀ y ∈ Yset N, ∀ t ∈ Set.Icc 0 T, |w l t x y| ≤ C := by
    intro l x y hy t ht
    have hw1 : w l t x y = (sol t : Idx d N → ℝ) ⟨(l, x, y), hy⟩ := dif_pos hy
    rw [hw1]
    have := lp.norm_apply_le_norm (by simp : (∞ : ℝ≥0∞) ≠ 0) (sol t) ⟨(l, x, y), hy⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (hC t ht)
  have hext : ∀ t, WFMFG31e.ext M (sol t) = fun l' _ x' y' => clip M (w l' t x' y') := by
    intro t; funext l' s x' y'; simp only [WFMFG31e.ext, w]; split_ifs <;> simp [clip_zero M hM]
  have hderw : ∀ l x, ∀ y ∈ Yset N, ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt (fun s => w l s x y)
        (-(nashOp ε φ f (fun l' _ x' y' => clip M (w l' t x' y')) l t x y)) (Set.Icc 0 T) t := by
    intro l x y hy t ht
    have h1 := (lp.evalCLM ℝ (fun _ : Idx d N => ℝ) ∞ ⟨(l, x, y), hy⟩).hasFDerivAt.comp_hasDerivWithinAt
      t (hsol t ht)
    have e1 : (fun s => w l s x y)
        = (⇑(lp.evalCLM ℝ (fun _ : Idx d N => ℝ) ∞ ⟨(l, x, y), hy⟩) ∘ sol) := by
      funext s; exact dif_pos hy
    have h2 : HasDerivWithinAt (fun s => w l s x y) ((F (sol t) : Idx d N → ℝ) ⟨(l, x, y), hy⟩)
        (Set.Icc 0 T) t := by
      rw [e1]; exact h1
    convert h2 using 1
    show _ = fieldR ε φ f M (sol t) ⟨(l, x, y), hy⟩
    simp only [fieldR, hext t]
    rfl
  have hwT : ∀ l x, ∀ y ∈ Yset N, w l T x y = g (x l) (empMeas x y) := by
    intro l x y hy
    have hw1 : w l T x y = (sol T : Idx d N → ℝ) ⟨(l, x, y), hy⟩ := dif_pos hy
    have : sol T = G0 := hsol0
    rw [hw1, this]
  have hap := apriori hN ε T κ δ Mf Mg M hε0 hT hδ hM φ hφ f g hf hg w hderw hwT ⟨C, hwB⟩
  refine ⟨w, ?_, hwT, ⟨M, hap⟩⟩
  intro l x y hy t ht
  have hcl : (fun l' (_ : ℝ) x' y' => clip M (w l' t x' y')) = fun l' _ x' y' => w l' t x' y' := by
    funext l' s x' y'
    by_cases hy' : y' ∈ Yset N
    · exact clip_of_abs M _ (hap l' x' y' hy' t ht)
    · have hw1 : w l' t x' y' = 0 := dif_neg hy'
      rw [hw1, clip_zero M hM]
  have := hderw l x y hy t ht
  rw [hcl] at this
  exact this

end WFMFG31f

theorem solution (d N : ℕ) [NeZero d] (hN : 1 ≤ N) (ε T κ δ Mf Mg : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hT : 0 < T) (hδ : 0 < δ)
    (φ : ℝ → ℝ) (hφ : IsCutoff κ δ φ) (f g : Fin d → (Fin d → ℝ) → ℝ)
    (hf : ∀ i, ∀ p ∈ stdSimplex ℝ (Fin d), |f i p| ≤ Mf)
    (hg : ∀ i, ∀ p ∈ stdSimplex ℝ (Fin d), |g i p| ≤ Mg) :
    ∃ w : Fin N → ℝ → (Fin N → Fin d) → (Fin N → ℚ) → ℝ, IsNashSol N ε T φ f g w ∧
      ∀ w' : Fin N → ℝ → (Fin N → Fin d) → (Fin N → ℚ) → ℝ, IsNashSol N ε T φ f g w' →
        ∀ (l : Fin N) (x : Fin N → Fin d), ∀ y ∈ Yset N, ∀ t ∈ Set.Icc 0 T,
          w' l t x y = w l t x y := by
  obtain ⟨w, hw⟩ := WFMFG31f.exists_sol hN ε T κ δ Mf Mg hε0 hT hδ φ hφ f g hf hg
  exact ⟨w, hw, fun w' hw' => WFMFG31c.uniq hN ε T κ δ hε0 hT hδ φ hφ f g w w' hw hw'⟩
