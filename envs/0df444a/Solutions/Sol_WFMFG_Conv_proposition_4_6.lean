-- Prove2me | solution 1 for WFMFG.Conv.proposition_4_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T17:43:41.417225+00:00
-- url     : https://prove2.me/submissions/b43724bd-f159-4021-a839-93388be1ff74

import Mathlib
import Definitions.Def_WFMFG_Conv_Simplex
import Definitions.Def_WFMFG_Conv_Multinomial
import Definitions.Def_WFMFG_Conv_Setting
import Theorems.Thm_WFMFG_Conv_lemma_4_8
import Theorems.Thm_WFMFG_Conv_lemma_4_10
import Theorems.Thm_WFMFG_Conv_lemma_4_11

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


namespace WFMFG46

open WFMFG32

lemma emp_perm {d N : ℕ} (x : Fin N → Fin d) (y : Fin N → ℚ) (σ : Equiv.Perm (Fin N))
    (hx : ∀ n, x (σ n) = x n) : empQ x (y ∘ σ) = empQ x y := by
  funext i; unfold empQ; congr 1
  have := Equiv.sum_comp σ (fun n => if x n = i then y n else 0)
  rw [← this]
  apply Finset.sum_congr rfl
  intro n _
  simp only [Function.comp, hx]

lemma empMeas_perm {d N : ℕ} (x : Fin N → Fin d) (y : Fin N → ℚ) (σ : Equiv.Perm (Fin N))
    (hx : ∀ n, x (σ n) = x n) : empMeas x (y ∘ σ) = empMeas x y := by
  funext i; unfold empMeas; rw [emp_perm x y σ hx]

lemma ratio_perm {d N : ℕ} (x : Fin N → Fin d) (y : Fin N → ℚ) (σ : Equiv.Perm (Fin N))
    (hx : ∀ n, x (σ n) = x n) (k : Fin d → ℕ) (n : Fin N) :
    ratioQ x (y ∘ σ) k n = ratioQ x y k n := by
  unfold ratioQ; rw [emp_perm x y σ hx]

lemma reweight_perm {d N : ℕ} (x : Fin N → Fin d) (y : Fin N → ℚ) (σ : Equiv.Perm (Fin N))
    (hx : ∀ n, x (σ n) = x n) (k : Fin d → ℕ) :
    reweight x (y ∘ σ) k = (reweight x y k) ∘ σ := by
  funext n
  simp only [reweight, Function.comp, ratio_perm x y σ hx]
  congr 1
  unfold ratioQ; rw [hx]

/-- The normalized common-noise term of (3.2) along `z^{N,l}`. -/
noncomputable def noiseZ {d N : ℕ} (U : Fin d → ℝ → (Fin d → ℝ) → ℝ) (l : Fin N) (t : ℝ)
    (x : Fin N → Fin d) (y : Fin N → ℚ) : ℝ :=
  multE N (empMeas x y)
    (fun k => (ratioQ x y k l : ℝ) * (zN U l t x (reweight x y k) - zN U l t x y))

lemma noiseZ_perm {d N : ℕ} (U : Fin d → ℝ → (Fin d → ℝ) → ℝ) (l : Fin N) (t : ℝ)
    (x : Fin N → Fin d) (y : Fin N → ℚ) (σ : Equiv.Perm (Fin N))
    (hx : ∀ n, x (σ n) = x n) : noiseZ U l t x (y ∘ σ) = noiseZ U l t x y := by
  unfold noiseZ zN
  rw [empMeas_perm x y σ hx]
  apply Finset.sum_congr rfl
  intro k _
  simp only [ratio_perm x y σ hx, reweight_perm x y σ hx, empMeas_perm x _ σ hx]

/-- The normalized/unnormalized identity: for `y^l > 0`,
`(1/y^l) N E[u(y') - u(y)] = N E[ratio (z(y') - z(y))]`. -/
lemma noise_u_z {d N : ℕ} (hN : 1 ≤ N) (U : Fin d → ℝ → (Fin d → ℝ) → ℝ) (l : Fin N) (t : ℝ)
    (x : Fin N → Fin d) (y : Fin N → ℚ) (hy : y ∈ Yset N) (hyl : 0 < y l) :
    (1 / (y l : ℝ)) * N * multE N (empMeas x y) (fun k => uN U l t x (reweight x y k) - uN U l t x y)
      = N * noiseZ U l t x y := by
  have hyl' : (y l : ℝ) ≠ 0 := by exact_mod_cast hyl.ne'
  have hs : ∑ i, empMeas x y i = 1 := (emp_std hN x y hy).2
  have hm1 : ∑ k ∈ Finset.Nat.antidiagonalTuple d N, multW (empMeas x y) k = 1 := by
    rw [WFMFGmult.multW_sum, hs, one_pow]
  have hm2 := noise_mass hN x y hy l
  set z := zN U l t x y with hz
  have key : ∀ k, multW (empMeas x y) k * (uN U l t x (reweight x y k) - uN U l t x y)
      = (y l : ℝ) * (multW (empMeas x y) k * ((ratioQ x y k l : ℝ) * (zN U l t x (reweight x y k) - z)))
        + (y l : ℝ) * z * (multW (empMeas x y) k * (ratioQ x y k l : ℝ) - multW (empMeas x y) k) := by
    intro k
    unfold uN
    rw [← hz]
    have : ((reweight x y k l : ℚ) : ℝ) = (y l : ℝ) * (ratioQ x y k l : ℝ) := by
      unfold reweight; push_cast; ring
    rw [this]; ring
  unfold multE noiseZ multE
  rw [Finset.sum_congr rfl (fun k _ => key k), Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, Finset.sum_sub_distrib, hm1, hm2]
  field_simp
  ring

lemma ham_eq {d : ℕ} (i : Fin d) (u : Fin d → ℝ) :
    ham i u = -(1 / 2) * ∑ j, (pos (u i - u j)) ^ 2 := rfl

lemma erase_term {d : ℕ} (p a : Fin d → ℝ) (i : Fin d) (hp : ∑ j, p j = 1) :
    ∑ j ∈ univ.erase i, p j * (a i - a j) = ∑ j, ((if j = i then 1 else 0) - p j) * a j := by
  rw [Finset.sum_erase _ (by simp)]
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_mul, hp, one_mul]

lemma drift_term {d : ℕ} (p : Fin d → ℝ) (φ : ℝ → ℝ) (V a : Fin d → ℝ) :
    ∑ j, ∑ k, p k * (φ (p j) + pos (V k - V j)) * (a j - a k)
      = ∑ k, ∑ j, p k * φ (p j) * (a j - a k) + ∑ k, ∑ j, p k * pos (V k - V j) * (a j - a k) := by
  rw [← Finset.sum_add_distrib, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  ring

end WFMFG46

open WFMFG32 WFMFG46

theorem solution (γ' ϵ : ℝ) (hγ0 : 0 < γ') (hγ1 : γ' < 1) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1 / 4) :
    ∃ η : ℝ, 0 < η ∧
    ∀ (d : ℕ) [NeZero d] (ε T κ δ : ℝ), 0 < ε → ε < 1 → 0 < T → 0 < δ →
    ∀ φ : ℝ → ℝ, IsCutoff κ δ φ →
    ∀ f g : Fin d → (Fin d → ℝ) → ℝ,
    ∀ U : Fin d → ℝ → (Fin d → ℝ) → ℝ, IsMasterSol ε T φ f g U → WFReg γ' T U →
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      (∀ (l : Fin N) (x : Fin N → Fin d), ∀ y ∈ Yset N, zN U l T x y = g (x l) (empMeas x y)) ∧
      ∀ (l : Fin N) (t : ℝ) (x : Fin N → Fin d) (y : Fin N → ℚ),
        t ∈ Set.Icc 0 T → y ∈ Yset N → TN ϵ x y →
        ∃ r : ℝ, |r| ≤ C / (N : ℝ) ^ η ∧
          HasDerivWithinAt (fun s => zN U l s x y)
            (r - nashOp ε φ f (fun l' s x' y' => zN U l' s x' y') l t x y) (Set.Icc 0 T) t := by
  obtain ⟨η8, hη8, h48⟩ := WFMFG.Conv.lemma_4_8 γ' ϵ hγ0 hγ1 hϵ0 hϵ1
  obtain ⟨η10, hη10, h410⟩ := WFMFG.Conv.lemma_4_10 γ' ϵ hγ0 hγ1 hϵ0 hϵ1
  refine ⟨min η8 (min η10 ϵ), lt_min hη8 (lt_min hη10 hϵ0), ?_⟩
  intro d _ ε T κ δ hε0 hε1 hT hδ φ hφ f g U hMS hReg
  obtain ⟨C8, hC8⟩ := h48 d T hT U hReg
  obtain ⟨C10, hC10⟩ := h410 d T κ δ hT hδ φ hφ U hReg
  obtain ⟨C11, hC11⟩ := WFMFG.Conv.lemma_4_11 d γ' T hγ0 hγ1 hT U hReg
  set η := min η8 (min η10 ϵ) with hηdef
  refine ⟨ε * |C8| + |C10| + |C11|, fun N hN => ⟨?_, ?_⟩⟩
  · intro l x y hy
    exact hMS.2.2 (x l) _ (emp_std hN x y hy)
  intro l t x y ht hy hTN
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) < N := by linarith
  set μ := empMeas x y with hμ
  have hpos : ∀ i, 0 < μ i := fun i => lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) (hTN.1 i)
  have hs : ∑ i, μ i = 1 := (emp_std hN x y hy).2
  have hint : μ ∈ simplexInt d := ⟨hpos, hs⟩
  have hder := hMS.2.1 (x l) t ht μ hint
  -- powers
  have hpow : ∀ a : ℝ, η ≤ a → (1:ℝ) / (N:ℝ) ^ a ≤ 1 / (N:ℝ) ^ η := by
    intro a ha
    apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos hN0 _)
    exact Real.rpow_le_rpow_of_exponent_le hNr ha
  have hη8' : η ≤ η8 := min_le_left _ _
  have hη10' : η ≤ η10 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hηϵ : η ≤ ϵ := le_trans (min_le_right _ _) (min_le_right _ _)
  -- the noise term
  set WF : ℝ := ∑ j, ((if j = x l then 1 else 0) - μ j) * sD (U (x l) t) μ j
      + (1 / 2) * ∑ j, ∑ k, (μ j * (if j = k then 1 else 0) - μ j * μ k) * sD2 (U (x l) t) μ j k
    with hWF
  have hnoise : |(N:ℝ) * noiseZ U l t x y - WF| ≤ C8 / (N:ℝ) ^ η8 := by
    have hgen : ∀ y'' : Fin N → ℚ, y'' ∈ Yset N → TN ϵ x y'' → 0 < y'' l →
        empMeas x y'' = μ → |(N:ℝ) * noiseZ U l t x y'' - WF| ≤ C8 / (N:ℝ) ^ η8 := by
      intro y'' hy'' hT'' hyl hμ''
      have := hC8 N hN l t x y'' ht hy'' hT'' hyl
      rw [noise_u_z hN U l t x y'' hy'' hyl, hμ''] at this
      rw [hWF]
      have e : (N:ℝ) * noiseZ U l t x y'' - (∑ j, ((if j = x l then 1 else 0) - μ j) * sD (U (x l) t) μ j
          + (1 / 2) * ∑ j, ∑ k, (μ j * (if j = k then 1 else 0) - μ j * μ k) * sD2 (U (x l) t) μ j k)
          = (N:ℝ) * noiseZ U l t x y'' - ∑ j, ((if j = x l then 1 else 0) - μ j) * sD (U (x l) t) μ j
            - (1 / 2) * ∑ j, ∑ k, (μ j * (if j = k then 1 else 0) - μ j * μ k)
                * sD2 (U (x l) t) μ j k := by ring
      rw [e]; exact this
    rcases (hy.1 l).lt_or_eq with hyl | hyl
    · exact hgen y hy hTN hyl rfl
    · -- `y^l = 0`: swap weights with a player in the same state carrying positive weight
      have hμl : 0 < empQ x y (x l) := by
        have := hpos (x l); simp only [hμ, empMeas] at this; exact_mod_cast this
      obtain ⟨m, hxm, hym⟩ : ∃ m, x m = x l ∧ 0 < y m := by
        by_contra hcon
        push_neg at hcon
        have : empQ x y (x l) ≤ 0 := by
          unfold empQ
          apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
          apply Finset.sum_nonpos; intro n _
          split_ifs with h
          · exact hcon n h
          · exact le_rfl
        linarith
      set σ := Equiv.swap l m with hσ
      have hx : ∀ n, x (σ n) = x n := by
        intro n; simp only [hσ, Equiv.swap_apply_def]
        split_ifs with h1 h2
        · rw [h1, hxm]
        · rw [h2, hxm]
        · rfl
      have hy'' : y ∘ σ ∈ Yset N := by
        refine ⟨fun n => hy.1 _, ?_⟩
        rw [← hy.2]; exact Equiv.sum_comp σ y
      have hT'' : TN ϵ x (y ∘ σ) := by
        refine ⟨fun i => ?_, fun n => hTN.2 (σ n)⟩
        rw [empMeas_perm x y σ hx]; exact hTN.1 i
      have hyl'' : 0 < (y ∘ σ) l := by simp [hσ, hym]
      have := hgen (y ∘ σ) hy'' hT'' hyl'' (empMeas_perm x y σ hx)
      rwa [noiseZ_perm U l t x y σ hx] at this
  have hdrift := hC10 N hN l t x y ht hy hTN
  have hham := hC11 ϵ hϵ0 hϵ1 N hN l t x y ht hy hTN
  -- assemble
  refine ⟨nashOp ε φ f (fun l' s x' y' => zN U l' s x' y') l t x y - masterOp ε φ f U (x l) t μ,
    ?_, ?_⟩
  · have hsplit : nashOp ε φ f (fun l' s x' y' => zN U l' s x' y') l t x y
        = driftOp φ (fun l' s x' y' => zN U l' s x' y') l t x y
          + ham (x l) (fun j => zN U l t (Function.update x l j) y) + f (x l) μ
          + ε * N * noiseZ U l t x y := by
      unfold nashOp noiseZ; ring
    have hmaster : masterOp ε φ f U (x l) t μ
        = ham (x l) (fun j => U j t μ) + f (x l) μ
          + (∑ k, ∑ j, μ k * φ (μ j) * (sD (U (x l) t) μ j - sD (U (x l) t) μ k)
            + ∑ k, ∑ j, μ k * pos (U k t μ - U j t μ) * (sD (U (x l) t) μ j - sD (U (x l) t) μ k)
            + ∑ j, φ (μ j) * (U j t μ - U (x l) t μ))
          + ε * WF := by
      unfold masterOp
      rw [ham_eq, drift_term μ φ (fun j => U j t μ) (fun j => sD (U (x l) t) μ j),
        erase_term μ (fun j => sD (U (x l) t) μ j) (x l) hs, hWF]
      ring
    rw [hsplit, hmaster]
    -- bounds
    have hyb : (y l : ℝ) ≤ (1 / 2) * (N : ℝ) ^ (1 - ϵ) := hTN.2 l
    have hyl0 : (0:ℝ) ≤ y l := by exact_mod_cast hy.1 l
    have hham' : |ham (x l) (fun j => zN U l t (Function.update x l j) y) - ham (x l) (fun j => U j t μ)|
        ≤ |C11| / (N:ℝ) ^ η := by
      refine le_trans hham ?_
      have h1 : C11 * (y l : ℝ) / N ≤ |C11| * ((1 / 2) * (N : ℝ) ^ (1 - ϵ)) / N := by
        apply div_le_div_of_nonneg_right _ hN0.le
        exact le_trans (mul_le_mul_of_nonneg_right (le_abs_self _) hyl0)
          (mul_le_mul_of_nonneg_left hyb (abs_nonneg _))
      have h2 : |C11| * ((1 / 2) * (N : ℝ) ^ (1 - ϵ)) / N = (|C11| / 2) * (1 / (N:ℝ) ^ ϵ) := by
        rw [Real.rpow_sub hN0, Real.rpow_one]
        have : (N:ℝ) ^ ϵ ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
        field_simp
      have h3 := hpow ϵ hηϵ
      rw [h2] at h1
      have h4 : (|C11| / 2) * (1 / (N:ℝ) ^ ϵ) ≤ (|C11| / 2) * (1 / (N:ℝ) ^ η) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      have h5 : (|C11| / 2) * (1 / (N:ℝ) ^ η) ≤ |C11| / (N:ℝ) ^ η := by
        have ha : 0 ≤ |C11| * (1 / (N:ℝ) ^ η) := mul_nonneg (abs_nonneg _) (by positivity)
        have e : |C11| / (N:ℝ) ^ η = |C11| * (1 / (N:ℝ) ^ η) := by ring
        rw [e]; linarith
      exact le_trans h1 (le_trans h4 h5)
    have hdrift' : |driftOp φ (fun l' s x' y' => zN U l' s x' y') l t x y
        - (∑ k, ∑ j, μ k * φ (μ j) * (sD (U (x l) t) μ j - sD (U (x l) t) μ k)
            + ∑ k, ∑ j, μ k * pos (U k t μ - U j t μ) * (sD (U (x l) t) μ j - sD (U (x l) t) μ k)
            + ∑ j, φ (μ j) * (U j t μ - U (x l) t μ))| ≤ |C10| / (N:ℝ) ^ η := by
      refine le_trans hdrift ?_
      rw [div_eq_mul_one_div C10, div_eq_mul_one_div |C10|]
      exact le_trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
        (mul_le_mul_of_nonneg_left (hpow η10 hη10') (abs_nonneg _))
    have hnoise' : |ε * N * noiseZ U l t x y - ε * WF| ≤ ε * |C8| / (N:ℝ) ^ η := by
      have e : ε * N * noiseZ U l t x y - ε * WF = ε * ((N:ℝ) * noiseZ U l t x y - WF) := by ring
      rw [e, abs_mul, abs_of_pos hε0, mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ hε0.le
      refine le_trans hnoise ?_
      rw [div_eq_mul_one_div C8, div_eq_mul_one_div |C8|]
      exact le_trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
        (mul_le_mul_of_nonneg_left (hpow η8 hη8') (abs_nonneg _))
    have e : driftOp φ (fun l' s x' y' => zN U l' s x' y') l t x y
          + ham (x l) (fun j => zN U l t (Function.update x l j) y) + f (x l) μ
          + ε * N * noiseZ U l t x y
        - (ham (x l) (fun j => U j t μ) + f (x l) μ
          + (∑ k, ∑ j, μ k * φ (μ j) * (sD (U (x l) t) μ j - sD (U (x l) t) μ k)
            + ∑ k, ∑ j, μ k * pos (U k t μ - U j t μ) * (sD (U (x l) t) μ j - sD (U (x l) t) μ k)
            + ∑ j, φ (μ j) * (U j t μ - U (x l) t μ))
          + ε * WF)
        = (driftOp φ (fun l' s x' y' => zN U l' s x' y') l t x y
        - (∑ k, ∑ j, μ k * φ (μ j) * (sD (U (x l) t) μ j - sD (U (x l) t) μ k)
            + ∑ k, ∑ j, μ k * pos (U k t μ - U j t μ) * (sD (U (x l) t) μ j - sD (U (x l) t) μ k)
            + ∑ j, φ (μ j) * (U j t μ - U (x l) t μ)))
          + (ham (x l) (fun j => zN U l t (Function.update x l j) y) - ham (x l) (fun j => U j t μ))
          + (ε * N * noiseZ U l t x y - ε * WF) := by ring
    rw [e]
    have hsum : (ε * |C8| + |C10| + |C11|) / (N:ℝ) ^ η
        = |C10| / (N:ℝ) ^ η + |C11| / (N:ℝ) ^ η + ε * |C8| / (N:ℝ) ^ η := by ring
    rw [hsum]
    refine le_trans (abs_add_le _ _) ?_
    refine add_le_add ?_ hnoise'
    refine le_trans (abs_add_le _ _) ?_
    exact add_le_add hdrift' hham'
  · have : nashOp ε φ f (fun l' s x' y' => zN U l' s x' y') l t x y - masterOp ε φ f U (x l) t μ
        - nashOp ε φ f (fun l' s x' y' => zN U l' s x' y') l t x y = -(masterOp ε φ f U (x l) t μ) := by
      ring
    rw [this]
    exact hder
