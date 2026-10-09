-- Prove2me | solution 1 for RegretBandits.Contextual.banditron_expected_mistakes
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T17:05:57.13131+00:00
-- url     : https://prove2.me/submissions/31096a02-6930-49ca-a6c5-3735a416ed34

import Mathlib
import Definitions.Def_RegretBandits_Contextual_Protocol
import Definitions.Def_RegretBandits_Contextual_Multiclass
import Definitions.Def_RegretBandits_Contextual_Banditron

set_option autoImplicit false

namespace RegretBandits.Contextual.BanditronAux

open RegretBandits.Contextual Finset

/-! ### Path-law machinery -/

lemma playPrefix_snoc_castSucc {K n : ℕ} (ω : Fin n → Fin K) (i : Fin K) (t : Fin n) :
    playPrefix (Fin.snoc ω i : Fin (n + 1) → Fin K) (Fin.castSucc t) = playPrefix ω t := by
  funext j
  simp only [playPrefix]
  have : (Fin.castLE (Fin.castSucc t).isLt.le j : Fin (n + 1)) =
      Fin.castSucc (Fin.castLE t.isLt.le j) := Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

lemma playPrefix_snoc_last {K n : ℕ} (ω : Fin n → Fin K) (i : Fin K) :
    playPrefix (Fin.snoc ω i : Fin (n + 1) → Fin K) (Fin.last n) = ω := by
  funext j
  simp only [playPrefix]
  have : (Fin.castLE (Fin.last n).isLt.le j : Fin (n + 1)) = Fin.castSucc j := Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

lemma pathProb_snoc {K : ℕ} (p : PlayRule K) (n : ℕ) (ω : Fin n → Fin K) (i : Fin K) :
    pathProb p (n + 1) (Fin.snoc ω i) = pathProb p n ω * p n ω i := by
  unfold pathProb
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl (fun t _ => ?_)
    simp only [playPrefix_snoc_castSucc, Fin.snoc_castSucc]
    rfl
  · simp only [playPrefix_snoc_last, Fin.snoc_last]
    rfl

lemma pathExpect_succ {K : ℕ} (p : PlayRule K) (n : ℕ) (F : (Fin (n + 1) → Fin K) → ℝ) :
    pathExpect p (n + 1) F =
      pathExpect p n (fun ω => ∑ i, p n ω i * F (Fin.snoc ω i)) := by
  unfold pathExpect
  rw [← (Fin.snocEquiv (fun _ => Fin K)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk]
  rw [pathProb_snoc]
  ring

lemma pathExpect_step {K : ℕ} (p : PlayRule K) (hp : ∀ t h, ∑ i, p t h i = 1) (n : ℕ)
    (Φ : (Fin (n + 1) → Fin K) → ℝ) (Ψ : (Fin n → Fin K) → ℝ) (Δ : (Fin n → Fin K) → Fin K → ℝ)
    (hΦ : ∀ ω i, Φ (Fin.snoc ω i) = Ψ ω + Δ ω i) :
    pathExpect p (n + 1) Φ = pathExpect p n Ψ + pathExpect p n (fun ω => ∑ i, p n ω i * Δ ω i) := by
  rw [pathExpect_succ]
  unfold pathExpect
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  simp_rw [hΦ, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hp, one_mul]
  ring

lemma pathExpect_add {K : ℕ} (p : PlayRule K) (n : ℕ) (F G : (Fin n → Fin K) → ℝ) :
    pathExpect p n (fun ω => F ω + G ω) = pathExpect p n F + pathExpect p n G := by
  unfold pathExpect
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun ω _ => by ring)

lemma pathExpect_const {K : ℕ} (p : PlayRule K) (hp : ∀ t h, ∑ i, p t h i = 1) (n : ℕ) (c : ℝ) :
    pathExpect p n (fun _ => c) = c := by
  induction n with
  | zero => simp [pathExpect, pathProb]
  | succ n _ih =>
    rw [pathExpect_succ]
    simp_rw [← Finset.sum_mul, hp, one_mul]
    exact _ih

lemma pathProb_nonneg {K : ℕ} (p : PlayRule K) (hp : ∀ t h i, 0 ≤ p t h i) (n : ℕ)
    (ω : Fin n → Fin K) : 0 ≤ pathProb p n ω :=
  Finset.prod_nonneg (fun _ _ => hp _ _ _)

lemma pathExpect_mono {K : ℕ} (p : PlayRule K) (hp : ∀ t h i, 0 ≤ p t h i) (n : ℕ)
    (F G : (Fin n → Fin K) → ℝ) (hFG : ∀ ω, F ω ≤ G ω) :
    pathExpect p n F ≤ pathExpect p n G := by
  unfold pathExpect
  exact Finset.sum_le_sum (fun ω _ =>
    mul_le_mul_of_nonneg_left (hFG ω) (pathProb_nonneg p hp n ω))

lemma pathExpect_nonneg {K : ℕ} (p : PlayRule K) (hp : ∀ t h i, 0 ≤ p t h i) (n : ℕ)
    (F : (Fin n → Fin K) → ℝ) (hF : ∀ ω, 0 ≤ F ω) : 0 ≤ pathExpect p n F := by
  unfold pathExpect
  exact Finset.sum_nonneg (fun ω _ => mul_nonneg (pathProb_nonneg p hp n ω) (hF ω))

lemma sumPrefix_snoc {K n : ℕ} (f : (t : ℕ) → (Fin t → Fin K) → Fin K → ℝ)
    (ω : Fin n → Fin K) (i : Fin K) :
    ∑ t : Fin (n + 1), f t (playPrefix (Fin.snoc ω i : Fin (n + 1) → Fin K) t)
        ((Fin.snoc ω i : Fin (n + 1) → Fin K) t) =
      ∑ t : Fin n, f t (playPrefix ω t) (ω t) + f n ω i := by
  rw [Fin.sum_univ_castSucc]
  simp only [playPrefix_snoc_castSucc, playPrefix_snoc_last, Fin.snoc_castSucc, Fin.snoc_last]
  rfl

/-- Jensen + Cauchy–Schwarz under the path law. -/
lemma pathExpect_inner_le {K d : ℕ} (p : PlayRule K) (hp0 : ∀ t h i, 0 ≤ p t h i)
    (hp : ∀ t h, ∑ i, p t h i = 1) (n : ℕ)
    (W : (Fin n → Fin K) → Matrix (Fin K) (Fin d) ℝ) (U : Matrix (Fin K) (Fin d) ℝ) :
    pathExpect p n (fun ω => ∑ i, ∑ j, U i j * W ω i j) ≤
      frobNorm U * Real.sqrt (pathExpect p n (fun ω => ∑ i, ∑ j, W ω i j ^ 2)) := by
  have hCS : ∀ ω, ∑ i, ∑ j, U i j * W ω i j ≤
      frobNorm U * Real.sqrt (∑ i, ∑ j, W ω i j ^ 2) := by
    intro ω
    unfold frobNorm
    have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin K × Fin d))
      (fun q => U q.1 q.2) (fun q => W ω q.1 q.2)
    simpa only [Fintype.sum_prod_type] using h
  refine (pathExpect_mono p hp0 n _ _ hCS).trans ?_
  unfold pathExpect
  have hP := pathProb_nonneg p hp0 n
  have hS : ∀ ω : Fin n → Fin K, 0 ≤ ∑ i, ∑ j, W ω i j ^ 2 :=
    fun ω => Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have h1 : ∑ ω, pathProb p n ω * (frobNorm U * Real.sqrt (∑ i, ∑ j, W ω i j ^ 2)) =
      frobNorm U * ∑ ω, Real.sqrt (pathProb p n ω) *
        Real.sqrt (pathProb p n ω * ∑ i, ∑ j, W ω i j ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    rw [Real.sqrt_mul (hP ω), ← mul_assoc (Real.sqrt _) (Real.sqrt _), Real.mul_self_sqrt (hP ω)]
    ring
  rw [h1]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  refine (Real.sum_sqrt_mul_sqrt_le _ hP (fun ω => mul_nonneg (hP ω) (hS ω))).trans ?_
  have h2 : ∑ ω, pathProb p n ω = 1 := by
    have := pathExpect_const p hp n 1
    simpa [pathExpect] using this
  rw [h2, Real.sqrt_one, one_mul]

/-- Solving `x − L ≤ u √(a x + b)`. -/
lemma solve_sqrt_ineq (xv L u a b : ℝ) (hL : 0 ≤ L) (hu : 0 ≤ u) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : 0 ≤ xv) (h : xv - L ≤ u * Real.sqrt (a * xv + b)) :
    xv ≤ L + u ^ 2 * a + u * Real.sqrt (a * L) + u * Real.sqrt b := by
  by_contra hcon
  rw [not_le] at hcon
  set s1 := Real.sqrt (a * L) with hs1
  set s2 := Real.sqrt b with hs2
  have hs1n : 0 ≤ s1 := Real.sqrt_nonneg _
  have hs2n : 0 ≤ s2 := Real.sqrt_nonneg _
  have hs1sq : s1 ^ 2 = a * L := Real.sq_sqrt (mul_nonneg ha hL)
  have hs2sq : s2 ^ 2 = b := Real.sq_sqrt hb
  set z := xv - L with hz
  have hT : 0 ≤ u ^ 2 * a + u * s1 + u * s2 := by positivity
  have hzT : u ^ 2 * a + u * s1 + u * s2 < z := by rw [hz]; linarith
  have hzpos : 0 < z := lt_of_le_of_lt hT hzT
  have hsq : z ^ 2 ≤ u ^ 2 * (a * xv + b) := by
    have h0 : 0 ≤ u * Real.sqrt (a * xv + b) := by positivity
    have hax : 0 ≤ a * xv + b := by positivity
    calc z ^ 2 ≤ (u * Real.sqrt (a * xv + b)) ^ 2 := by
          exact pow_le_pow_left₀ hzpos.le h 2
      _ = u ^ 2 * (a * xv + b) := by rw [mul_pow, Real.sq_sqrt hax]
  have hxv : xv = L + z := by rw [hz]; ring
  rw [hxv] at hsq
  -- z^2 ≤ u^2 a z + u^2 s1^2 + u^2 s2^2
  have hsq' : z ^ 2 ≤ u ^ 2 * a * z + u ^ 2 * s1 ^ 2 + u ^ 2 * s2 ^ 2 := by
    rw [hs1sq, hs2sq]; nlinarith
  have hzs1 : u * s1 ≤ z := by nlinarith
  have hzs2 : u * s2 ≤ z := by nlinarith
  have k1 : u ^ 2 * s1 ^ 2 ≤ u * s1 * z := by
    have := mul_le_mul_of_nonneg_left hzs1 (mul_nonneg hu hs1n); nlinarith
  have k2 : u ^ 2 * s2 ^ 2 ≤ u * s2 * z := by
    have := mul_le_mul_of_nonneg_left hzs2 (mul_nonneg hu hs2n); nlinarith
  have k3 : z * (u ^ 2 * a + u * s1 + u * s2) < z * z := mul_lt_mul_of_pos_left hzT hzpos
  nlinarith

/-! ### Banditron-specific pointwise facts -/

/-- The update direction of the Banditron (row factor of `X̃_t`). -/
noncomputable def cvec {K d : ℕ} (γ : ℝ) (sel : (Fin K → ℝ) → Fin K)
    (W : Matrix (Fin K) (Fin d) ℝ) (xv : Fin d → ℝ) (yv i a : Fin K) : ℝ :=
  (if i = yv ∧ i = a then 1 / banditronDist γ sel W xv a else 0) -
    (if sel (Matrix.mulVec W xv) = a then 1 else 0)

lemma banditronW_snoc {K d : ℕ} (γ : ℝ) (sel : (Fin K → ℝ) → Fin K) (x : ℕ → Fin d → ℝ)
    (y : ℕ → Fin K) (n : ℕ) (ω : Fin n → Fin K) (i : Fin K) :
    banditronW γ sel x y (n + 1) (Fin.snoc ω i) =
      banditronW γ sel x y n ω + Matrix.of (fun a b => x n b *
        cvec γ sel (banditronW γ sel x y n ω) (x n) (y n) i a) := by
  simp only [banditronW, Fin.init_snoc, Fin.snoc_last, cvec]

lemma banditronDist_sum {K d : ℕ} (hK : 0 < K) (γ : ℝ) (sel : (Fin K → ℝ) → Fin K)
    (W : Matrix (Fin K) (Fin d) ℝ) (xv : Fin d → ℝ) :
    ∑ i, banditronDist γ sel W xv i = 1 := by
  simp only [banditronDist, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (K : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma banditronDist_nonneg {K d : ℕ} (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (sel : (Fin K → ℝ) → Fin K) (W : Matrix (Fin K) (Fin d) ℝ) (xv : Fin d → ℝ) (i : Fin K) :
    0 ≤ banditronDist γ sel W xv i := by
  unfold banditronDist
  have h1 : 0 ≤ 1 - γ := by linarith
  have h2 : (0 : ℝ) ≤ (if sel (Matrix.mulVec W xv) = i then 1 else 0) := by split_ifs <;> norm_num
  have h3 : 0 ≤ γ / K := div_nonneg hγ0 (Nat.cast_nonneg K)
  nlinarith [mul_nonneg h1 h2]

lemma inner_expand {K d : ℕ} (U W : Matrix (Fin K) (Fin d) ℝ) (xv : Fin d → ℝ) (c : Fin K → ℝ) :
    ∑ a, ∑ b, U a b * (W + Matrix.of (fun a b => xv b * c a)) a b =
      ∑ a, ∑ b, U a b * W a b + ∑ a, c a * (Matrix.mulVec U xv) a := by
  simp only [Matrix.add_apply, Matrix.of_apply, Matrix.mulVec, dotProduct, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))

lemma sq_expand {K d : ℕ} (W : Matrix (Fin K) (Fin d) ℝ) (xv : Fin d → ℝ) (c : Fin K → ℝ) :
    ∑ a, ∑ b, (W + Matrix.of (fun a b => xv b * c a)) a b ^ 2 =
      ∑ a, ∑ b, W a b ^ 2 + (2 * ∑ a, c a * (Matrix.mulVec W xv) a +
        (∑ a, c a ^ 2) * sqNorm xv) := by
  have row : ∀ a, ∑ b, (W a b + xv b * c a) ^ 2 = ∑ b, W a b ^ 2 +
      (2 * (c a * ∑ b, W a b * xv b) + c a ^ 2 * ∑ b, xv b ^ 2) := by
    intro a
    calc ∑ b, (W a b + xv b * c a) ^ 2
        = ∑ b, (W a b ^ 2 + 2 * (c a * (W a b * xv b)) + c a ^ 2 * xv b ^ 2) :=
          Finset.sum_congr rfl (fun b _ => by ring)
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            ← Finset.mul_sum]
          ring
  simp only [Matrix.add_apply, Matrix.of_apply]
  rw [Finset.sum_congr rfl (fun a _ => row a), Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  simp only [Matrix.mulVec, dotProduct, sqNorm]

lemma sum_mul_ite_sub {K : ℕ} (D : Fin K → ℝ) (yv : Fin K) (α β : ℝ) :
    ∑ i, D i * ((if i = yv then α else 0) - β) = D yv * α - (∑ i, D i) * β := by
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_mul]

lemma cvec_dot {K d : ℕ} (γ : ℝ) (sel : (Fin K → ℝ) → Fin K) (W : Matrix (Fin K) (Fin d) ℝ)
    (xv : Fin d → ℝ) (yv i : Fin K) (v : Fin K → ℝ) :
    ∑ a, cvec γ sel W xv yv i a * v a =
      (if i = yv then v yv / banditronDist γ sel W xv yv else 0) -
        v (sel (Matrix.mulVec W xv)) := by
  unfold cvec
  by_cases hi : i = yv
  · subst hi
    simp [sub_mul, Finset.sum_sub_distrib, ite_mul, Finset.sum_ite_eq, div_eq_inv_mul]
  · simp [hi, sub_mul, Finset.sum_sub_distrib, ite_mul, Finset.sum_ite_eq]

lemma cvec_sq {K d : ℕ} (γ : ℝ) (sel : (Fin K → ℝ) → Fin K) (W : Matrix (Fin K) (Fin d) ℝ)
    (xv : Fin d → ℝ) (yv i : Fin K) :
    ∑ a, cvec γ sel W xv yv i a ^ 2 =
      (if i = yv then 1 / banditronDist γ sel W xv yv ^ 2 -
        2 * (if sel (Matrix.mulVec W xv) = yv then 1 else 0) / banditronDist γ sel W xv yv
        else 0) + 1 := by
  unfold cvec
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  by_cases hi : i = yv
  · subst hi
    by_cases hy : sel (Matrix.mulVec W xv) = i
    · simp [hy, ite_pow, Finset.sum_ite_eq, Finset.sum_ite_eq', mul_ite, ite_mul]
      ring
    · have hy' : i ≠ sel (Matrix.mulVec W xv) := fun h => hy h.symm
      simp [hy, hy', ite_pow, Finset.sum_ite_eq, Finset.sum_ite_eq', mul_ite, ite_mul]
  · simp [hi, ite_pow, Finset.sum_ite_eq, Finset.sum_ite_eq']

/-- F1: unbiasedness of the Banditron update. -/
lemma dist_cvec_dot {K d : ℕ} (hK : 0 < K) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (sel : (Fin K → ℝ) → Fin K) (W : Matrix (Fin K) (Fin d) ℝ)
    (xv : Fin d → ℝ) (yv : Fin K) (v : Fin K → ℝ) :
    ∑ i, banditronDist γ sel W xv i * ∑ a, cvec γ sel W xv yv i a * v a =
      v yv - v (sel (Matrix.mulVec W xv)) := by
  simp_rw [cvec_dot]
  rw [sum_mul_ite_sub, banditronDist_sum hK]
  have hpos : 0 < banditronDist γ sel W xv yv := by
    unfold banditronDist
    have h2 : (0 : ℝ) ≤ (if sel (Matrix.mulVec W xv) = yv then 1 else 0) := by
      split_ifs <;> norm_num
    have h1 : 0 ≤ 1 - γ := by linarith
    have h3 : 0 < γ / K := div_pos hγ0 (by exact_mod_cast hK)
    nlinarith [mul_nonneg h1 h2]
  field_simp

/-- F2: second moment of the Banditron update. -/
lemma dist_cvec_sq {K d : ℕ} (hK : 2 ≤ K) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2)
    (sel : (Fin K → ℝ) → Fin K) (W : Matrix (Fin K) (Fin d) ℝ)
    (xv : Fin d → ℝ) (yv : Fin K) :
    ∑ i, banditronDist γ sel W xv i * ∑ a, cvec γ sel W xv yv i a ^ 2 ≤
      2 * K / γ * (if sel (Matrix.mulVec W xv) ≠ yv then 1 else 0) + 2 * γ := by
  have hK0 : 0 < K := by omega
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  simp_rw [cvec_sq]
  have hsplit : ∀ i, banditronDist γ sel W xv i * ((if i = yv then
      1 / banditronDist γ sel W xv yv ^ 2 -
        2 * (if sel (Matrix.mulVec W xv) = yv then 1 else 0) / banditronDist γ sel W xv yv
        else 0) + 1) =
      banditronDist γ sel W xv i * ((if i = yv then
      1 / banditronDist γ sel W xv yv ^ 2 -
        2 * (if sel (Matrix.mulVec W xv) = yv then 1 else 0) / banditronDist γ sel W xv yv
        else 0) - (-1)) := fun i => by ring
  simp_rw [hsplit]
  rw [sum_mul_ite_sub, banditronDist_sum hK0]
  set D := banditronDist γ sel W xv yv with hDdef
  have hDp : 0 < D := by
    rw [hDdef]; unfold banditronDist
    have h2 : (0 : ℝ) ≤ (if sel (Matrix.mulVec W xv) = yv then 1 else 0) := by
      split_ifs <;> norm_num
    have h1 : 0 ≤ 1 - γ := by linarith
    have h3 : 0 < γ / K := div_pos hγ0 (by exact_mod_cast hK0)
    nlinarith [mul_nonneg h1 h2]
  have e : ∀ I : ℝ, D * (1 / D ^ 2 - 2 * I / D) - 1 * -1 = 1 / D - 2 * I + 1 := by
    intro I; field_simp; ring
  rw [e]
  by_cases hy : sel (Matrix.mulVec W xv) = yv
  · have hD : D = 1 - γ + γ / K := by
      rw [hDdef]; simp [banditronDist, hy]
    rw [if_pos hy, if_neg (not_not_intro hy)]
    have hγK : γ / K ≤ γ / 2 := div_le_div_of_nonneg_left hγ0.le (by norm_num) hKr
    have hγK0 : 0 ≤ γ / K := div_nonneg hγ0.le (by positivity)
    have hDpos : 1 / 2 ≤ D := by rw [hD]; linarith
    have h1D : 1 - D ≤ γ := by rw [hD]; linarith
    have hinv : 1 / D ≤ 1 + 2 * γ := by
      rw [div_le_iff₀ hDp]
      nlinarith [mul_le_mul_of_nonneg_left hDpos (by linarith : (0:ℝ) ≤ 2 * γ)]
    linarith
  · have hD : D = γ / K := by
      rw [hDdef]; simp [banditronDist, hy]
    rw [if_neg hy, if_pos hy, hD, one_div_div]
    have : 1 ≤ K / γ := by rw [le_div_iff₀ hγ0]; linarith
    have : 2 * K / γ = 2 * (K / γ) := by ring
    linarith

/-- F3: actual mistake probability vs. greedy mistake. -/
lemma dist_mistake {K d : ℕ} (hK : 0 < K) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (sel : (Fin K → ℝ) → Fin K) (W : Matrix (Fin K) (Fin d) ℝ)
    (xv : Fin d → ℝ) (yv : Fin K) :
    ∑ i, banditronDist γ sel W xv i * (if i ≠ yv then (1 : ℝ) else 0) ≤
      (if sel (Matrix.mulVec W xv) ≠ yv then 1 else 0) + γ := by
  have hsplit : ∀ i, banditronDist γ sel W xv i * (if i ≠ yv then (1 : ℝ) else 0) =
      banditronDist γ sel W xv i * ((if i = yv then (-1 : ℝ) else 0) - (-1)) := by
    intro i; by_cases h : i = yv <;> simp [h]
  simp_rw [hsplit]
  rw [sum_mul_ite_sub, banditronDist_sum hK]
  by_cases hy : sel (Matrix.mulVec W xv) = yv
  · have hD : banditronDist γ sel W xv yv = 1 - γ + γ / K := by
      simp [banditronDist, hy]
    rw [hD]
    simp only [hy, ne_eq, not_true_eq_false, if_false]
    have hγK0 : 0 ≤ γ / K := div_nonneg hγ0.le (by positivity)
    linarith
  · simp only [hy, ne_eq, not_false_eq_true, if_true]
    have := banditronDist_nonneg γ hγ0.le hγ1 sel W xv yv
    linarith

lemma hinge_step {K d : ℕ} (U : Matrix (Fin K) (Fin d) ℝ) (xv : Fin d → ℝ) (yv yh : Fin K) :
    (if yh ≠ yv then (1 : ℝ) else 0) - hingeLoss U xv yv ≤
      (Matrix.mulVec U xv) yv - (Matrix.mulVec U xv) yh := by
  unfold hingeLoss
  by_cases h : yh = yv
  · subst h
    simp only [ne_eq, not_true_eq_false, if_false, zero_sub, sub_self, neg_nonpos]
    exact le_max_left _ _
  · rw [if_pos h]
    have hs : (Matrix.mulVec U xv) yh ≤ ⨆ i : {i : Fin K // i ≠ yv}, (Matrix.mulVec U xv) i :=
      le_ciSup (f := fun i : {i : Fin K // i ≠ yv} => (Matrix.mulVec U xv) (i : Fin K))
        (Set.finite_range _).bddAbove ⟨yh, h⟩
    have := le_max_right 0
      (1 - (Matrix.mulVec U xv) yv + ⨆ i : {i : Fin K // i ≠ yv}, (Matrix.mulVec U xv) i)
    linarith

end RegretBandits.Contextual.BanditronAux

/-! ### Potential-function induction and the three expectation bounds -/

namespace RegretBandits.Contextual.BanditronAux

open RegretBandits.Contextual Finset

lemma pathExpect_sub {K : ℕ} (p : PlayRule K) (n : ℕ) (F G : (Fin n → Fin K) → ℝ) :
    pathExpect p n (fun ω => F ω - G ω) = pathExpect p n F - pathExpect p n G := by
  unfold pathExpect
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun ω _ => by ring)

lemma pathExpect_smul {K : ℕ} (p : PlayRule K) (n : ℕ) (c : ℝ) (F : (Fin n → Fin K) → ℝ) :
    pathExpect p n (fun ω => c * F ω) = c * pathExpect p n F := by
  unfold pathExpect
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ω _ => by ring)

lemma pathExpect_induct {K : ℕ} (p : PlayRule K) (hp0 : ∀ t h i, 0 ≤ p t h i)
    (hp1 : ∀ t h, ∑ i, p t h i = 1) (N : ℕ) (Φ : (n : ℕ) → (Fin n → Fin K) → ℝ) (c : ℕ → ℝ)
    (h0 : ∀ ω, Φ 0 ω = 0)
    (hstep : ∀ n < N, ∀ ω, ∑ i, p n ω i * Φ (n + 1) (Fin.snoc ω i) ≤ Φ n ω + c n) :
    ∀ n ≤ N, pathExpect p n (Φ n) ≤ ∑ t ∈ Finset.range n, c t := by
  intro n
  induction n with
  | zero => intro _; simp [pathExpect, h0]
  | succ n ih =>
    intro hn
    rw [pathExpect_succ, Finset.sum_range_succ]
    have h1 := pathExpect_mono p hp0 n _ (fun ω => Φ n ω + c n) (hstep n (by omega))
    rw [pathExpect_add, pathExpect_const p hp1] at h1
    have h2 := ih (by omega)
    linarith

lemma step_sum {K : ℕ} (q : Fin K → ℝ) (hq : ∑ i, q i = 1) (Φ α A : ℝ) (g h : Fin K → ℝ) :
    ∑ i, q i * (Φ + (α * g i + h i - A)) = Φ + (α * ∑ i, q i * g i + ∑ i, q i * h i - A) := by
  have e1 : ∀ i, q i * (Φ + (α * g i + h i - A)) = α * (q i * g i) + q i * h i + q i * (Φ - A) :=
    fun i => by ring
  simp_rw [e1]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hq]
  ring

noncomputable def greedyMis {K d : ℕ} (γ : ℝ) (sel : (Fin K → ℝ) → Fin K) (x : ℕ → Fin d → ℝ)
    (y : ℕ → Fin K) (n : ℕ) (ω : Fin n → Fin K) : ℝ :=
  ∑ t : Fin n, if sel (Matrix.mulVec (banditronW γ sel x y t (playPrefix ω t)) (x t)) ≠ y t
    then 1 else 0

lemma greedyMis_snoc {K d : ℕ} (γ : ℝ) (sel : (Fin K → ℝ) → Fin K) (x : ℕ → Fin d → ℝ)
    (y : ℕ → Fin K) (n : ℕ) (ω : Fin n → Fin K) (i : Fin K) :
    greedyMis γ sel x y (n + 1) (Fin.snoc ω i) = greedyMis γ sel x y n ω +
      (if sel (Matrix.mulVec (banditronW γ sel x y n ω) (x n)) ≠ y n then 1 else 0) :=
  sumPrefix_snoc (fun t h _ => if sel (Matrix.mulVec (banditronW γ sel x y t h) (x t)) ≠ y t
    then (1 : ℝ) else 0) ω i

lemma greedyMis_nonneg {K d : ℕ} (γ : ℝ) (sel : (Fin K → ℝ) → Fin K) (x : ℕ → Fin d → ℝ)
    (y : ℕ → Fin K) (n : ℕ) (ω : Fin n → Fin K) : 0 ≤ greedyMis γ sel x y n ω :=
  Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

lemma predictionMistakes_snoc {K : ℕ} (y : ℕ → Fin K) (n : ℕ) (ω : Fin n → Fin K) (i : Fin K) :
    predictionMistakes y (Fin.snoc ω i : Fin (n + 1) → Fin K) =
      predictionMistakes y ω + (if i ≠ y n then 1 else 0) :=
  sumPrefix_snoc (fun t _ j => if j ≠ y t then (1 : ℝ) else 0) ω i

/-- B2 -/
lemma mistakes_le_greedy {K d : ℕ} (hK : 0 < K) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (sel : (Fin K → ℝ) → Fin K) (x : ℕ → Fin d → ℝ) (y : ℕ → Fin K) (n : ℕ) :
    pathExpect (banditronRule γ sel x y) n (predictionMistakes y) -
      pathExpect (banditronRule γ sel x y) n (greedyMis γ sel x y n) ≤ n * γ := by
  have hp0 : ∀ t h i, 0 ≤ banditronRule γ sel x y t h i :=
    fun t h i => banditronDist_nonneg γ hγ0.le hγ1 sel _ _ i
  have hp1 : ∀ t h, ∑ i, banditronRule γ sel x y t h i = 1 :=
    fun t h => banditronDist_sum hK γ sel _ _
  have H := pathExpect_induct (banditronRule γ sel x y) hp0 hp1 n
    (fun n ω => predictionMistakes y ω - greedyMis γ sel x y n ω) (fun _ => γ)
    (fun ω => by simp [predictionMistakes, greedyMis]) (by
      intro m _ ω
      try dsimp only
      have e : ∀ i, predictionMistakes y (Fin.snoc ω i : Fin (m + 1) → Fin K) -
          greedyMis γ sel x y (m + 1) (Fin.snoc ω i) =
          (predictionMistakes y ω - greedyMis γ sel x y m ω) +
            (1 * (if i ≠ y m then (1 : ℝ) else 0) + (fun _ => (0 : ℝ)) i -
              (if sel (Matrix.mulVec (banditronW γ sel x y m ω) (x m)) ≠ y m then 1 else 0)) := by
        intro i; rw [predictionMistakes_snoc, greedyMis_snoc]; ring
      simp only [e]
      rw [step_sum _ (hp1 m ω)]
      have hd : ∑ i, banditronRule γ sel x y m ω i * (if i ≠ y m then (1 : ℝ) else 0) ≤
          (if sel (Matrix.mulVec (banditronW γ sel x y m ω) (x m)) ≠ y m then 1 else 0) + γ :=
        dist_mistake hK γ hγ0 hγ1 sel _ (x m) (y m)
      simp only [mul_zero, Finset.sum_const_zero]
      linarith) n le_rfl
  try dsimp only at H
  rw [pathExpect_sub, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at H
  exact H

/-- B3 -/
lemma greedy_le_inner {K d : ℕ} (hK : 0 < K) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (sel : (Fin K → ℝ) → Fin K) (x : ℕ → Fin d → ℝ) (y : ℕ → Fin K) (n : ℕ)
    (U : Matrix (Fin K) (Fin d) ℝ) :
    pathExpect (banditronRule γ sel x y) n (greedyMis γ sel x y n) -
      pathExpect (banditronRule γ sel x y) n
        (fun ω => ∑ a, ∑ b, U a b * banditronW γ sel x y n ω a b) ≤ cumHinge n x y U := by
  have hp0 : ∀ t h i, 0 ≤ banditronRule γ sel x y t h i :=
    fun t h i => banditronDist_nonneg γ hγ0.le hγ1 sel _ _ i
  have hp1 : ∀ t h, ∑ i, banditronRule γ sel x y t h i = 1 :=
    fun t h => banditronDist_sum hK γ sel _ _
  have H := pathExpect_induct (banditronRule γ sel x y) hp0 hp1 n
    (fun n ω => greedyMis γ sel x y n ω - ∑ a, ∑ b, U a b * banditronW γ sel x y n ω a b)
    (fun t => hingeLoss U (x t) (y t))
    (fun ω => by simp [greedyMis, banditronW]) (by
      intro m _ ω
      try dsimp only
      have e : ∀ i, greedyMis γ sel x y (m + 1) (Fin.snoc ω i) -
          ∑ a, ∑ b, U a b * banditronW γ sel x y (m + 1) (Fin.snoc ω i) a b =
          (greedyMis γ sel x y m ω - ∑ a, ∑ b, U a b * banditronW γ sel x y m ω a b) +
            ((-1) * (∑ a, cvec γ sel (banditronW γ sel x y m ω) (x m) (y m) i a *
                (Matrix.mulVec U (x m)) a) + (fun _ => (0 : ℝ)) i -
              (-(if sel (Matrix.mulVec (banditronW γ sel x y m ω) (x m)) ≠ y m then 1 else 0))) := by
        intro i; rw [greedyMis_snoc, banditronW_snoc, inner_expand]; ring
      simp only [e]
      rw [step_sum _ (hp1 m ω)]
      have hd : ∑ i, banditronRule γ sel x y m ω i *
          ∑ a, cvec γ sel (banditronW γ sel x y m ω) (x m) (y m) i a *
            (Matrix.mulVec U (x m)) a =
          (Matrix.mulVec U (x m)) (y m) -
            (Matrix.mulVec U (x m)) (sel (Matrix.mulVec (banditronW γ sel x y m ω) (x m))) :=
        dist_cvec_dot hK γ hγ0 hγ1 sel _ (x m) (y m) _
      have hh := hinge_step U (x m) (y m) (sel (Matrix.mulVec (banditronW γ sel x y m ω) (x m)))
      simp only [mul_zero, Finset.sum_const_zero]
      linarith) n le_rfl
  try dsimp only at H
  rw [pathExpect_sub] at H
  exact H

/-- B4 -/
lemma sqnorm_le_greedy {K d : ℕ} (hK : 2 ≤ K) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2)
    (sel : (Fin K → ℝ) → Fin K) (hsel : IsArgmaxSelector sel)
    (x : ℕ → Fin d → ℝ) (y : ℕ → Fin K) (n : ℕ) (hx : ∀ t < n, sqNorm (x t) = 1) :
    pathExpect (banditronRule γ sel x y) n
        (fun ω => ∑ a, ∑ b, banditronW γ sel x y n ω a b ^ 2) -
      2 * K / γ * pathExpect (banditronRule γ sel x y) n (greedyMis γ sel x y n) ≤
        n * (2 * γ) := by
  have hK0 : 0 < K := by omega
  have hγ1' : γ ≤ 1 := by linarith
  have hp0 : ∀ t h i, 0 ≤ banditronRule γ sel x y t h i :=
    fun t h i => banditronDist_nonneg γ hγ0.le hγ1' sel _ _ i
  have hp1 : ∀ t h, ∑ i, banditronRule γ sel x y t h i = 1 :=
    fun t h => banditronDist_sum hK0 γ sel _ _
  have H := pathExpect_induct (banditronRule γ sel x y) hp0 hp1 n
    (fun n ω => (∑ a, ∑ b, banditronW γ sel x y n ω a b ^ 2) -
      2 * K / γ * greedyMis γ sel x y n ω)
    (fun _ => 2 * γ)
    (fun ω => by simp [greedyMis, banditronW]) (by
      intro m hm ω
      try dsimp only
      have e : ∀ i, (∑ a, ∑ b, banditronW γ sel x y (m + 1) (Fin.snoc ω i) a b ^ 2) -
          2 * K / γ * greedyMis γ sel x y (m + 1) (Fin.snoc ω i) =
          ((∑ a, ∑ b, banditronW γ sel x y m ω a b ^ 2) -
            2 * K / γ * greedyMis γ sel x y m ω) +
            (2 * (∑ a, cvec γ sel (banditronW γ sel x y m ω) (x m) (y m) i a *
                (Matrix.mulVec (banditronW γ sel x y m ω) (x m)) a) +
              (fun i => ∑ a, cvec γ sel (banditronW γ sel x y m ω) (x m) (y m) i a ^ 2) i -
              2 * K / γ *
                (if sel (Matrix.mulVec (banditronW γ sel x y m ω) (x m)) ≠ y m then 1 else 0)) := by
        intro i
        rw [greedyMis_snoc, banditronW_snoc, sq_expand, hx m hm]
        ring
      simp only [e]
      rw [step_sum _ (hp1 m ω)]
      have hd : ∑ i, banditronRule γ sel x y m ω i *
          ∑ a, cvec γ sel (banditronW γ sel x y m ω) (x m) (y m) i a *
            (Matrix.mulVec (banditronW γ sel x y m ω) (x m)) a =
          (Matrix.mulVec (banditronW γ sel x y m ω) (x m)) (y m) -
            (Matrix.mulVec (banditronW γ sel x y m ω) (x m))
              (sel (Matrix.mulVec (banditronW γ sel x y m ω) (x m))) :=
        dist_cvec_dot hK0 γ hγ0 hγ1' sel _ (x m) (y m) _
      have hs : ∑ i, banditronRule γ sel x y m ω i *
          ∑ a, cvec γ sel (banditronW γ sel x y m ω) (x m) (y m) i a ^ 2 ≤
          2 * K / γ *
            (if sel (Matrix.mulVec (banditronW γ sel x y m ω) (x m)) ≠ y m then 1 else 0) +
              2 * γ :=
        dist_cvec_sq hK γ hγ0 hγ1 sel _ (x m) (y m)
      have ha := hsel (Matrix.mulVec (banditronW γ sel x y m ω) (x m)) (y m)
      linarith) n le_rfl
  try dsimp only at H
  rw [pathExpect_sub, pathExpect_smul, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at H
  exact H

end RegretBandits.Contextual.BanditronAux

open RegretBandits.Contextual in
theorem solution {K d : ℕ} (hK : 2 ≤ K) (n : ℕ) (hn : 8 * K ≤ n)
    (sel : (Fin K → ℝ) → Fin K) (hsel : IsArgmaxSelector sel)
    (x : ℕ → Fin d → ℝ) (y : ℕ → Fin K) (hx : ∀ t < n, sqNorm (x t) = 1)
    (U : Matrix (Fin K) (Fin d) ℝ) :
    pathExpect (banditronRule (((K : ℝ) / n) ^ ((1 : ℝ) / 3)) sel x y) n
        (predictionMistakes y) ≤
      cumHinge n x y U
        + (1 + frobNorm U * Real.sqrt (2 * avgHinge n x y U)) *
            (K : ℝ) ^ ((1 : ℝ) / 3) * (n : ℝ) ^ ((2 : ℝ) / 3)
        + 2 * frobNorm U ^ 2 * (K : ℝ) ^ ((2 : ℝ) / 3) * (n : ℝ) ^ ((1 : ℝ) / 3)
        + Real.sqrt 2 * frobNorm U * (K : ℝ) ^ ((1 : ℝ) / 6) * (n : ℝ) ^ ((1 : ℝ) / 3) := by
  have hK0 : 0 < K := by omega
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hnr : (8 : ℝ) * K ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  -- rpow bookkeeping
  have e23n : (n : ℝ) ^ ((2 : ℝ) / 3) = ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
  have e23K : (K : ℝ) ^ ((2 : ℝ) / 3) = ((K : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
  have e16K : (K : ℝ) ^ ((1 : ℝ) / 6) = Real.sqrt ((K : ℝ) ^ ((1 : ℝ) / 3)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
  have hk3 : ((K : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = K := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
  have hm3 : ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
  have hγkm : ((K : ℝ) / n) ^ ((1 : ℝ) / 3) = (K : ℝ) ^ ((1 : ℝ) / 3) / (n : ℝ) ^ ((1 : ℝ) / 3) :=
    Real.div_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _) _
  have eavg : avgHinge n x y U = cumHinge n x y U / n := rfl
  rw [e23n, e23K, e16K, eavg]
  set γ := ((K : ℝ) / n) ^ ((1 : ℝ) / 3) with hγdef
  set k := (K : ℝ) ^ ((1 : ℝ) / 3) with hkdef
  set m := (n : ℝ) ^ ((1 : ℝ) / 3) with hmdef
  have hk0 : 0 < k := Real.rpow_pos_of_pos (by linarith) _
  have hm0 : 0 < m := Real.rpow_pos_of_pos hn0 _
  have hγ0 : 0 < γ := by rw [hγkm]; positivity
  have h2k : 2 * k ≤ m := by
    by_contra hc
    rw [not_le] at hc
    have h1 := pow_lt_pow_left₀ hc hm0.le (by norm_num : (3 : ℕ) ≠ 0)
    have h2 : (2 * k) ^ 3 = 8 * k ^ 3 := by ring
    rw [h2, hk3, hm3] at h1
    linarith
  have hγ12 : γ ≤ 1 / 2 := by rw [hγkm, div_le_iff₀ hm0]; linarith
  have hγ1 : γ ≤ 1 := by linarith
  have hp0 : ∀ t h i, 0 ≤ banditronRule γ sel x y t h i :=
    fun t h i => BanditronAux.banditronDist_nonneg γ hγ0.le hγ1 sel _ _ i
  have hp1 : ∀ t h, ∑ i, banditronRule γ sel x y t h i = 1 :=
    fun t h => BanditronAux.banditronDist_sum hK0 γ sel _ _
  have B2 := BanditronAux.mistakes_le_greedy hK0 γ hγ0 hγ1 sel x y n
  have B3 := BanditronAux.greedy_le_inner hK0 γ hγ0 hγ1 sel x y n U
  have B4 := BanditronAux.sqnorm_le_greedy hK γ hγ0 hγ12 sel hsel x y n hx
  have B5 := BanditronAux.pathExpect_inner_le (banditronRule γ sel x y) hp0 hp1 n
    (banditronW γ sel x y n) U
  have hG0 : 0 ≤ pathExpect (banditronRule γ sel x y) n (BanditronAux.greedyMis γ sel x y n) :=
    BanditronAux.pathExpect_nonneg _ hp0 n _ (BanditronAux.greedyMis_nonneg γ sel x y n)
  have hL0 : 0 ≤ cumHinge n x y U := Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  have hu0 : 0 ≤ frobNorm U := Real.sqrt_nonneg _
  have ha : 0 ≤ 2 * (K : ℝ) / γ := by positivity
  have hb : 0 ≤ (n : ℝ) * (2 * γ) := by positivity
  have hQ := Real.sqrt_le_sqrt (h := (by linarith : pathExpect (banditronRule γ sel x y) n
      (fun ω => ∑ a, ∑ b, banditronW γ sel x y n ω a b ^ 2) ≤
      2 * (K : ℝ) / γ * pathExpect (banditronRule γ sel x y) n
        (BanditronAux.greedyMis γ sel x y n) + n * (2 * γ)))
  have hQ' := mul_le_mul_of_nonneg_left hQ hu0
  have hB6 := BanditronAux.solve_sqrt_ineq _ _ _ _ _ hL0 hu0 ha hb hG0 (by linarith)
  have e1 : (n : ℝ) * γ = k * m ^ 2 := by
    rw [hγkm, ← hm3]; field_simp
  have e2 : 2 * (K : ℝ) / γ = 2 * k ^ 2 * m := by
    rw [hγkm, ← hk3]; field_simp
  have e3 : Real.sqrt (2 * (K : ℝ) / γ * cumHinge n x y U) =
      Real.sqrt (2 * (cumHinge n x y U / n)) * k * m ^ 2 := by
    rw [e2]
    have h : 2 * k ^ 2 * m * cumHinge n x y U = 2 * (cumHinge n x y U / n) * (k * m ^ 2) ^ 2 := by
      rw [← hm3]; field_simp
    rw [h, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (by positivity)]; ring
  have e4 : Real.sqrt ((n : ℝ) * (2 * γ)) = Real.sqrt 2 * Real.sqrt k * m := by
    have h : (n : ℝ) * (2 * γ) = 2 * k * m ^ 2 := by linear_combination 2 * e1
    rw [h, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_sq hm0.le]
  rw [e3, e2, e4] at hB6
  rw [e1] at B2
  linarith
