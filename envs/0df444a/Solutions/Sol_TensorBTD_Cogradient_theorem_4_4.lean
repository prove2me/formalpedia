-- Prove2me | solution 1 for TensorBTD.Cogradient.theorem_4_4
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T19:02:34.168252+00:00
-- url     : https://prove2.me/submissions/2ccab707-20bc-4c0f-b143-d58d2cd9a7e9

import Mathlib
import Definitions.Def_TensorBTD_Cogradient_Setting

open Matrix

namespace RRAux_TensorBTD_Cogradient_theorem_4_4

lemma normSq_add_mul (a b : ℂ) (t : ℝ) :
    Complex.normSq (a + (t : ℂ) * b) = Complex.normSq a + t * (2 * (a.re * b.re + a.im * b.im))
      + t ^ 2 * Complex.normSq b := by
  simp [Complex.normSq_apply]; ring

lemma quad_deriv_real (a b c : ℝ) :
    HasDerivAt (fun t : ℝ => a + t * b + t ^ 2 * c) b 0 := by
  have h1 : HasDerivAt (fun t : ℝ => t * b) (1 * b) 0 := (hasDerivAt_id 0).mul_const b
  have h2 : HasDerivAt (fun t : ℝ => t ^ 2 * c) ((2 : ℕ) * (0 : ℝ) ^ (2 - 1) * 1 * c) 0 :=
    ((hasDerivAt_id 0).pow 2).mul_const c
  have := (h1.const_add a).add h2
  exact this.congr_deriv (by norm_num)

lemma quad_deriv_sum {ι : Type*} [Fintype ι] (a b c : ι → ℝ) :
    HasDerivAt (fun t : ℝ => (((1 / 2 : ℝ) * ∑ k, (a k + t * b k + t ^ 2 * c k) : ℝ) : ℂ))
      (((1 / 2 : ℝ) * ∑ k, b k : ℝ) : ℂ) 0 := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => quad_deriv_real (a k) (b k) (c k))
  exact (h.const_mul (1 / 2 : ℝ)).ofReal_comp

lemma two_cograd {X ι : Type*} [DecidableEq X] [Fintype ι] (Fs : (X → ℂ) → ι → ℂ)
    (z : X → ℂ) (β : X) (G : ι → ℂ)
    (hlin : ∀ w : ℂ, ∀ k, Fs (z + w • Pi.single β 1) k = Fs z k + w * G k) :
    (2 : ℂ) * TensorBTD.Cogradient.cograd
        (fun x => (((1 / 2 : ℝ) * ∑ k, Complex.normSq (Fs x k) : ℝ) : ℂ)) z β
      = ∑ k, starRingEnd ℂ (Fs z k) * G k := by
  unfold TensorBTD.Cogradient.cograd
  have e1 : (fun t : ℝ => ((((1 / 2 : ℝ) * ∑ k, Complex.normSq (Fs (z + (t : ℂ) • Pi.single β 1) k)) : ℝ) : ℂ))
      = fun t : ℝ => ((((1 / 2 : ℝ) * ∑ k, (Complex.normSq (Fs z k)
          + t * (2 * ((Fs z k).re * (G k).re + (Fs z k).im * (G k).im))
          + t ^ 2 * Complex.normSq (G k))) : ℝ) : ℂ) := by
    funext t
    simp only [hlin, normSq_add_mul]
  have e2 : (fun t : ℝ => ((((1 / 2 : ℝ) * ∑ k, Complex.normSq (Fs (z + ((t : ℂ) * Complex.I) • Pi.single β 1) k)) : ℝ) : ℂ))
      = fun t : ℝ => ((((1 / 2 : ℝ) * ∑ k, (Complex.normSq (Fs z k)
          + t * (2 * ((Fs z k).re * (Complex.I * G k).re + (Fs z k).im * (Complex.I * G k).im))
          + t ^ 2 * Complex.normSq (Complex.I * G k))) : ℝ) : ℂ) := by
    funext t
    simp only [hlin, mul_assoc, normSq_add_mul]
  rw [e1, e2, (quad_deriv_sum _ _ _).deriv, (quad_deriv_sum _ _ _).deriv]
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im, Complex.re_sum, Finset.mul_sum]
  · simp [Complex.mul_re, Complex.mul_im, Complex.im_sum, Finset.mul_sum]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring

section core
variable {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}

/-- the full index obtained from `i` in mode `n` and the remaining indices `ρ` -/
def ext (n : Fin P ⊕ Fin Q) (i : Fin (I n)) (ρ : TensorBTD.Cogradient.KRIdx I {n}) :
    (m : Fin P ⊕ Fin Q) → Fin (I m) :=
  fun m => if h : m = n then h ▸ i else ρ ⟨m, by simpa using h⟩

lemma ext_self (n : Fin P ⊕ Fin Q) (i : Fin (I n)) (ρ : TensorBTD.Cogradient.KRIdx I {n}) :
    ext n i ρ n = i := by
  simp [ext]

lemma ext_ne (n : Fin P ⊕ Fin Q) (i : Fin (I n)) (ρ : TensorBTD.Cogradient.KRIdx I {n})
    (m : {m : Fin P ⊕ Fin Q // m ∉ ({n} : Finset _)}) : ext n i ρ m.1 = ρ m := by
  have h : m.1 ≠ n := by simpa using m.2
  simp [ext, h]

lemma unfolding_eq (T : TensorBTD.Gramian.Tensor I) (n : Fin P ⊕ Fin Q) (i : Fin (I n))
    (ρ : TensorBTD.Cogradient.KRIdx I {n}) :
    TensorBTD.Cogradient.unfolding T n i ρ = T (ext n i ρ) := rfl

lemma sum_ext (n : Fin P ⊕ Fin Q) (i : Fin (I n)) (X : ((m : Fin P ⊕ Fin Q) → Fin (I m)) → ℂ) :
    ∑ ι, (if ι n = i then X ι else 0) = ∑ ρ : TensorBTD.Cogradient.KRIdx I {n}, X (ext n i ρ) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun ι => fun m => ι m.1) (fun ρ => ext n i ρ) ?_ ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_univ _
  · intro a _; simp [ext_self]
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    funext m
    by_cases h : m = n
    · subst h; simp [ext, ha]
    · simp [ext, h]
  · intro a _
    funext m
    exact ext_ne n i a m
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    have : ext n i (fun m => a m.1) = a := by
      funext m
      by_cases h : m = n
      · subst h; simp [ext, ha]
      · simp [ext, h]
    rw [this]

lemma prod_erase_ext (n : Fin P ⊕ Fin Q) (i : Fin (I n)) (ρ : TensorBTD.Cogradient.KRIdx I {n})
    (g : (m : Fin P ⊕ Fin Q) → Fin (I m) → ℂ) :
    ∏ m ∈ Finset.univ.erase n, g m (ext n i ρ m)
      = ∏ m : {m : Fin P ⊕ Fin Q // m ∉ ({n} : Finset _)}, g m.1 (ρ m) := by
  rw [Finset.prod_subtype (Finset.univ.erase n) (p := fun m => m ∉ ({n} : Finset _))
    (fun x => by simp)]
  refine Finset.prod_congr rfl (fun m _ => ?_)
  rw [ext_ne]

lemma prod_ext (n : Fin P ⊕ Fin Q) (i : Fin (I n)) (ρ : TensorBTD.Cogradient.KRIdx I {n})
    (g : (m : Fin P ⊕ Fin Q) → Fin (I m) → ℂ) :
    ∏ m, g m (ext n i ρ m)
      = g n i * ∏ m : {m : Fin P ⊕ Fin Q // m ∉ ({n} : Finset _)}, g m.1 (ρ m) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ n), prod_erase_ext, ext_self]

lemma core (A : (n : Fin P ⊕ Fin Q) → Matrix (Fin (I n)) (TensorBTD.Gramian.Col L) ℂ)
    (T : TensorBTD.Gramian.Tensor I) (n : Fin P ⊕ Fin Q) (i : Fin (I n))
    (c : TensorBTD.Gramian.Col L) :
    ∑ ι, starRingEnd ℂ ((∑ c' : TensorBTD.Gramian.Col L, ∏ m, A m (ι m) c') - T ι)
        * (if ι n = i then ∏ m ∈ Finset.univ.erase n, A m (ι m) c else 0)
      = ((A n).map (starRingEnd ℂ) * TensorBTD.Cogradient.W {n} A
          - (TensorBTD.Cogradient.unfolding T n).map (starRingEnd ℂ)
            * TensorBTD.Cogradient.V {n} A) i c := by
  have h1 : ∀ ι : (m : Fin P ⊕ Fin Q) → Fin (I m),
      starRingEnd ℂ ((∑ c' : TensorBTD.Gramian.Col L, ∏ m, A m (ι m) c') - T ι)
        * (if ι n = i then ∏ m ∈ Finset.univ.erase n, A m (ι m) c else 0)
      = if ι n = i then starRingEnd ℂ ((∑ c' : TensorBTD.Gramian.Col L, ∏ m, A m (ι m) c') - T ι)
          * ∏ m ∈ Finset.univ.erase n, A m (ι m) c else 0 := by
    intro ι; split_ifs <;> simp
  simp only [h1]
  rw [sum_ext n i (fun ι => starRingEnd ℂ ((∑ c' : TensorBTD.Gramian.Col L, ∏ m, A m (ι m) c') - T ι)
          * ∏ m ∈ Finset.univ.erase n, A m (ι m) c)]
  simp only [map_sub, map_sum, map_prod, ← unfolding_eq]
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.map_apply, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  congr 1
  swap
  · refine Finset.sum_congr rfl (fun ρ _ => ?_)
    have e := prod_erase_ext n i ρ (fun m k => A m k c)
    rw [e]
    rfl
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c' _ => ?_)
  have hW : TensorBTD.Cogradient.W {n} A c' c
      = ∏ m : {m : Fin P ⊕ Fin Q // m ∉ ({n} : Finset _)},
          ∑ k, starRingEnd ℂ (A m.1 k c') * A m.1 k c := by
    unfold TensorBTD.Cogradient.W
    rw [Finset.prod_subtype (Finset.univ.filter (· ∉ ({n} : Finset _)))
      (p := fun m => m ∉ ({n} : Finset _)) (fun x => by simp)]
    refine Finset.prod_congr rfl (fun m _ => ?_)
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hW, Fintype.prod_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  have e1 := prod_ext n i ρ (fun m k => starRingEnd ℂ (A m k c'))
  have e2 := prod_erase_ext n i ρ (fun m k => A m k c)
  rw [e1, e2, Finset.prod_mul_distrib]
  ring

lemma residual_lin (T : TensorBTD.Gramian.Tensor I) (z z' : TensorBTD.Gramian.Unk I L → ℂ)
    (n : Fin P ⊕ Fin Q) (w : ℂ) (D : Matrix (Fin (I n)) (TensorBTD.Gramian.Col L) ℂ)
    (hne : ∀ m, m ≠ n → TensorBTD.Gramian.factor z' m = TensorBTD.Gramian.factor z m)
    (heq : ∀ k c'', TensorBTD.Gramian.factor z' n k c''
      = TensorBTD.Gramian.factor z n k c'' + w * D k c'')
    (ι : (m : Fin P ⊕ Fin Q) → Fin (I m)) :
    TensorBTD.Cogradient.residual T z' ι = TensorBTD.Cogradient.residual T z ι
      + w * ∑ c'', D (ι n) c'' * ∏ m ∈ Finset.univ.erase n, TensorBTD.Gramian.factor z m (ι m) c'' := by
  unfold TensorBTD.Cogradient.residual
  have hp : ∀ c'', ∏ m, TensorBTD.Gramian.factor z' m (ι m) c''
      = (TensorBTD.Gramian.factor z n (ι n) c'' + w * D (ι n) c'')
        * ∏ m ∈ Finset.univ.erase n, TensorBTD.Gramian.factor z m (ι m) c'' := by
    intro c''
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ n), heq]
    congr 1
    refine Finset.prod_congr rfl (fun m hm => ?_)
    rw [hne m (Finset.ne_of_mem_erase hm)]
  have hq : ∀ c'', ∏ m, TensorBTD.Gramian.factor z m (ι m) c''
      = TensorBTD.Gramian.factor z n (ι n) c''
        * ∏ m ∈ Finset.univ.erase n, TensorBTD.Gramian.factor z m (ι m) c'' := by
    intro c''
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ n)]
  simp only [hp, hq, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  ring_nf

lemma single_apply_ne (β γ : TensorBTD.Gramian.Unk I L) (w : ℂ) (z : TensorBTD.Gramian.Unk I L → ℂ)
    (h : γ.1 ≠ β.1) :
    (z + w • Pi.single β 1 : TensorBTD.Gramian.Unk I L → ℂ) γ = z γ := by
  have : γ ≠ β := fun e => h (by rw [e])
  simp [this]

lemma factor_ne (z : TensorBTD.Gramian.Unk I L → ℂ) (β : TensorBTD.Gramian.Unk I L) (w : ℂ)
    (m : Fin P ⊕ Fin Q) (hm : m ≠ β.1) :
    TensorBTD.Gramian.factor (z + w • Pi.single β 1) m = TensorBTD.Gramian.factor z m := by
  match m, hm with
  | .inl p', hm =>
    ext k c''
    exact single_apply_ne β ⟨.inl p', (c'', k)⟩ w z hm
  | .inr q', hm =>
    ext k c''
    simp only [TensorBTD.Gramian.factor, Matrix.mul_apply, TensorBTD.Gramian.cMat, Matrix.of_apply]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [single_apply_ne β ⟨.inr q', (r, k)⟩ w z hm]

lemma E_map : (TensorBTD.Gramian.E L).map (starRingEnd ℂ) = TensorBTD.Gramian.E L := by
  ext r c''
  simp only [Matrix.map_apply, TensorBTD.Gramian.E, Matrix.of_apply]
  split_ifs <;> simp

end core

end RRAux_TensorBTD_Cogradient_theorem_4_4

open TensorBTD.Cogradient in
open Matrix in
theorem solution {P Q R : ℕ} (I : Fin P ⊕ Fin Q → ℕ) (L : Fin R → ℕ) (T : TensorBTD.Gramian.Tensor I)
    (z : TensorBTD.Gramian.Unk I L → ℂ) :
    (∀ p : Fin P, (2 : ℂ) • cogradA (fBTD T) z p =
        (Amat z p).map (starRingEnd ℂ) * W {.inl p} (TensorBTD.Gramian.factor z) -
          (unfolding T (.inl p)).map (starRingEnd ℂ) * V {.inl p} (TensorBTD.Gramian.factor z)) ∧
    (∀ q : Fin Q, (2 : ℂ) • cogradC (fBTD T) z q =
        (Cmat z q).map (starRingEnd ℂ) * TensorBTD.Gramian.E L * W {.inr q} (TensorBTD.Gramian.factor z) * (TensorBTD.Gramian.E L)ᵀ -
          (unfolding T (.inr q)).map (starRingEnd ℂ) * V {.inr q} (TensorBTD.Gramian.factor z) * (TensorBTD.Gramian.E L)ᵀ) := by
  constructor
  · intro p
    ext i c
    rw [Matrix.smul_apply, smul_eq_mul]
    simp only [cogradA, Matrix.of_apply]
    set β : TensorBTD.Gramian.Unk I L := ⟨.inl p, (c, i)⟩ with hβ
    let D : Matrix (Fin (I (.inl p))) (TensorBTD.Gramian.Col L) ℂ :=
      fun k c'' => if k = i then (if c'' = c then 1 else 0) else 0
    have hlin : ∀ w : ℂ, ∀ ι, residual T (z + w • Pi.single β 1) ι
        = residual T z ι + w * (if ι (.inl p) = i then
            ∏ m ∈ Finset.univ.erase (.inl p), TensorBTD.Gramian.factor z m (ι m) c else 0) := by
      intro w ι
      rw [RRAux_TensorBTD_Cogradient_theorem_4_4.residual_lin T z (z + w • Pi.single β 1) (.inl p)
        w D (fun m hm => RRAux_TensorBTD_Cogradient_theorem_4_4.factor_ne z β w m hm)]
      · congr 2
        by_cases h : ι (.inl p) = i
        · simp [D, h]
        · simp [D, h]
      · intro k c''
        simp only [TensorBTD.Gramian.factor, TensorBTD.Gramian.aMat, Matrix.of_apply, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul, Pi.single_apply, hβ, D]
        simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
        by_cases hk : k = i
        · by_cases hc : c'' = c
          · subst hk hc; simp
          · simp only [hk, if_true, hc, if_false, mul_zero, add_zero]
            rw [if_neg (fun h => hc (congrArg Prod.fst h)), mul_zero, add_zero]
        · simp only [hk, if_false, mul_zero, add_zero]
          rw [if_neg (fun h => hk (congrArg Prod.snd h)), mul_zero, add_zero]
    have h2 := RRAux_TensorBTD_Cogradient_theorem_4_4.two_cograd (residual T) z β _ hlin
    unfold fBTD
    rw [h2]
    exact RRAux_TensorBTD_Cogradient_theorem_4_4.core (TensorBTD.Gramian.factor z) T (.inl p) i c
  · intro q
    ext i r
    rw [Matrix.smul_apply, smul_eq_mul]
    simp only [cogradC, Matrix.of_apply]
    set β : TensorBTD.Gramian.Unk I L := ⟨.inr q, (r, i)⟩ with hβ
    let D : Matrix (Fin (I (.inr q))) (TensorBTD.Gramian.Col L) ℂ :=
      fun k c'' => if k = i then TensorBTD.Gramian.E L r c'' else 0
    have hlin : ∀ w : ℂ, ∀ ι, residual T (z + w • Pi.single β 1) ι
        = residual T z ι + w * ∑ c'', TensorBTD.Gramian.E L r c'' * (if ι (.inr q) = i then
            ∏ m ∈ Finset.univ.erase (.inr q), TensorBTD.Gramian.factor z m (ι m) c'' else 0) := by
      intro w ι
      rw [RRAux_TensorBTD_Cogradient_theorem_4_4.residual_lin T z (z + w • Pi.single β 1) (.inr q)
        w D (fun m hm => RRAux_TensorBTD_Cogradient_theorem_4_4.factor_ne z β w m hm)]
      · congr 2
        refine Finset.sum_congr rfl (fun c'' _ => ?_)
        by_cases h : ι (.inr q) = i
        · simp [D, h]
        · simp [D, h]
      · intro k c''
        simp only [TensorBTD.Gramian.factor, Matrix.mul_apply, TensorBTD.Gramian.cMat,
          Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, hβ, D,
          add_mul, Finset.sum_add_distrib]
        congr 1
        simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
        by_cases hk : k = i
        · simp only [hk, if_true]
          simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
          rw [Finset.sum_eq_single r (fun x _ hx => if_neg (fun h => hx (congrArg Prod.fst h)))
            (fun h => absurd (Finset.mem_univ r) h), if_pos rfl]
        · simp only [hk, if_false, mul_zero]
          simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
          exact Finset.sum_eq_zero (fun x _ => if_neg (fun h => hk (congrArg Prod.snd h)))
    have h2 := RRAux_TensorBTD_Cogradient_theorem_4_4.two_cograd (residual T) z β _ hlin
    unfold fBTD
    rw [h2]
    have hR : (Cmat z q).map (starRingEnd ℂ) * TensorBTD.Gramian.E L
        = (TensorBTD.Gramian.factor z (.inr q)).map (starRingEnd ℂ) := by
      show _ = (Cmat z q * TensorBTD.Gramian.E L).map (starRingEnd ℂ)
      rw [Matrix.map_mul, RRAux_TensorBTD_Cogradient_theorem_4_4.E_map]
    rw [hR, ← Matrix.sub_mul, Matrix.mul_apply]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c'' _ => ?_)
    rw [← RRAux_TensorBTD_Cogradient_theorem_4_4.core (TensorBTD.Gramian.factor z) T (.inr q) i c'',
      Matrix.transpose_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun ι _ => ?_)
    rw [show residual T z ι = (∑ c', ∏ m, TensorBTD.Gramian.factor z m (ι m) c') - T ι from rfl]
    ring

#print axioms solution
