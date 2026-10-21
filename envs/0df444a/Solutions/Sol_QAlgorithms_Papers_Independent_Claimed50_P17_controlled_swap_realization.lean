-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P17.controlled_swap_realization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T13:10:01.439241+00:00
-- url     : https://prove2.me/submissions/17fa5f80-017f-45ae-8f4d-6c3200f42df1

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P17
noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P17

/-- elementary vectors: v 0 = [A=C, B=m], v 1 = [A=m, B=C] -/
def g59c_V (d : ℕ) (m : Fin d) : Matrix (ABC d) (Fin 2) ℂ :=
  fun x a => (((if a = 0 then (if x.1.1 = x.2 ∧ x.1.2 = m then 1 else 0)
    else (if x.1.1 = m ∧ x.1.2 = x.2 then 1 else 0)) : ℝ) : ℂ)

def g59c_T (d : ℕ) : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Op (ABC d) where
  toFun M := ∑ m, g59c_V d m * M * (g59c_V d m)ᴴ
  map_add' M N := by simp [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c M := by simp [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

lemma g59c_T_apply (d : ℕ) (M : Matrix (Fin 2) (Fin 2) ℂ) (x y : ABC d) :
    g59c_T d M x y = ∑ m, ∑ b, (∑ a, g59c_V d m x a * M a b) * g59c_V d m y b := by
  simp only [g59c_T, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun b _ => ?_))
  congr 1
  simp [g59c_V]

lemma g59c_T_psd (d : ℕ) (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.PosSemidef) :
    (g59c_T d M).PosSemidef := by
  simp only [g59c_T, LinearMap.coe_mk, AddHom.coe_mk]
  exact Matrix.posSemidef_sum _ (fun m _ => hM.mul_mul_conjTranspose_same _)

lemma g59c_EE (d : ℕ) (u : Fin 2 → ℂ) (E : Matrix (ABC d) (Fin d) ℂ)
    (hE : ∀ x m, E x m = ∑ a, g59c_V d m x a * u a) :
    E * Eᴴ = g59c_T d (Matrix.vecMulVec u (star u)) := by
  ext x y
  rw [g59c_T_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hE, Fin.sum_univ_two,
    Matrix.vecMulVec_apply, Pi.star_apply, star_add, star_mul']
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have h : ∀ z a, star (g59c_V d m z a) = g59c_V d m z a := by
    intro z a; simp [g59c_V]
  rw [h, h]; ring

lemma g59c_alpha (d : ℕ) (s : Fin 2) :
    alphaEmbedding d s * (alphaEmbedding d s)ᴴ = g59c_T d (Matrix.vecMulVec
      (fun a => (((if a = 0 then 1 else (if s = 0 then 1 else -1)) /
        Real.sqrt (2 * ((d : ℝ) + if s = 0 then 1 else -1)) : ℝ) : ℂ))
      (star (fun a => (((if a = 0 then 1 else (if s = 0 then 1 else -1)) /
        Real.sqrt (2 * ((d : ℝ) + if s = 0 then 1 else -1)) : ℝ) : ℂ)))) := by
  apply g59c_EE
  intro x m
  simp only [alphaEmbedding, Fin.sum_univ_two, g59c_V]
  push_cast
  ring

lemma g59c_cs (d : ℕ) (z x : AB d × Fin 2) :
    controlledSwap d z x = if z = (if x.2 = 0 then x.1 else (x.1.2, x.1.1), x.2) then 1 else 0 := by
  unfold controlledSwap
  by_cases h : x.2 = 0
  · by_cases h2 : z.2 = 0
    · simp [h, h2, Prod.ext_iff]
    · simp [h, h2, Prod.ext_iff]
  · by_cases h2 : z.2 = x.2
    · simp [h, h2, Prod.ext_iff]
    · simp [h, h2, Prod.ext_iff]

lemma g59c_unitary (d : ℕ) : (controlledSwap d).conjTranspose * controlledSwap d = 1 := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, g59c_cs]
  simp only [apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy; simp
  · rw [if_neg hxy, if_neg]
    intro h
    apply hxy
    rcases x with ⟨⟨a, b⟩, s⟩; rcases y with ⟨⟨a', b'⟩, s'⟩
    simp only [Prod.mk.injEq] at h ⊢
    by_cases hs : s = 0
    · have : s' = 0 := by rw [← h.2]; simp [hs]
      simp [hs, this] at h; exact ⟨h, hs.trans this.symm⟩
    · have : s' ≠ 0 := by intro h'; apply hs; rw [h.2, h']
      simp [hs, this] at h; tauto

lemma g59c_phi (d : ℕ) (hd : 2 ≤ d) (s : Fin 2) (x : ABC d) (m : Fin d) : printedPhi d s x m = ∑ a, g59c_V d m x a * controlEffectVector d s a := by
  simp only [printedPhi, alphaEmbedding, pairDimension, controlEffectVector, controlVector, g59c_V, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  norm_num
  have hd' : (2:ℝ) ≤ d := by exact_mod_cast hd
  have a1 : (√(d:ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  have a2 : (√((d:ℝ)+1) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  have a3 : (√((d:ℝ) + -1) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero']; linarith
  have a4 : (√(2:ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  have h2 : (√(2:ℝ) : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  split_ifs <;> push_cast <;> field_simp <;> linear_combination (0:ℂ) * h2

lemma g59c_prep (d : ℕ) (c k : Fin d) (a : Fin 2) (w : AB d) :
    preparedSwap d ((c,k),a) w = (((1:ℝ)/Real.sqrt 2 : ℝ) : ℂ) * g59c_V d k (w,c) a := by
  simp only [preparedSwap, g59c_cs, Fin.sum_univ_two, controlVector, g59c_V]
  fin_cases a <;> simp [Prod.ext_iff] <;> split_ifs <;> simp_all [eq_comm]

def g59c_Mnet (d : ℕ) (i j k : Fin d) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun a b => (1/2 : ℂ) * ∑ n : Fin 3, (postprocess k n i j : ℂ) * controlPOVM d n b a

lemma g59c_net (d : ℕ) : networkInstrument d =
    liftDiagonal (fun i j k => g59c_T d (g59c_Mnet d i j k)) := by
  funext i j x y
  simp only [networkInstrument, liftDiagonal, g59c_T_apply, g59c_prep, postprocessPOVM,
    g59c_Mnet]
  by_cases h : x.2 = y.2
  · simp only [h, if_true, Prod.mk.eta]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    simp only [Fin.sum_univ_two, map_mul, Complex.conj_ofReal, h]
    have : ((1:ℝ)/Real.sqrt 2 : ℝ) * ((1:ℝ)/Real.sqrt 2 : ℝ) = (1/2 : ℝ) := by
      rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num)]; norm_num
    have hc : (((1:ℝ)/Real.sqrt 2 : ℝ) : ℂ) * (((1:ℝ)/Real.sqrt 2 : ℝ) : ℂ) = 1/2 := by
      rw [← Complex.ofReal_mul, this]; push_cast; ring
    have hV : ∀ z a, conj (g59c_V d m z a) = g59c_V d m z a := by intro z a; simp [g59c_V]
    simp only [hV]
    linear_combination (g59c_V d m x.1 0 * g59c_V d m y.1 0 * ∑ n : Fin 3, (postprocess y.2 n i j : ℂ) * controlPOVM d n 0 0
      + g59c_V d m x.1 0 * g59c_V d m y.1 1 * ∑ n : Fin 3, (postprocess y.2 n i j : ℂ) * controlPOVM d n 1 0
      + g59c_V d m x.1 1 * g59c_V d m y.1 0 * ∑ n : Fin 3, (postprocess y.2 n i j : ℂ) * controlPOVM d n 0 1
      + g59c_V d m x.1 1 * g59c_V d m y.1 1 * ∑ n : Fin 3, (postprocess y.2 n i j : ℂ) * controlPOVM d n 1 1) * hc
  · simp [h, Ne.symm h]

lemma g59c_povm_sum (d : ℕ) (hd : 2 ≤ d) : ∑ n, controlPOVM d n = 1 := by
  have hd' : (2:ℝ) ≤ d := by exact_mod_cast hd
  have a1 : (√(d:ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  have a2 : (√((d:ℝ)+1) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  have a4 : (√(2:ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  have h2 : (√(2:ℝ) : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have h3 : (√(d:ℝ) : ℂ)^2 = d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring
  have h4 : (√((d:ℝ)+1) : ℂ)^2 = d + 1 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring
  have h4' : (√(1 + (d:ℝ)) : ℂ)^2 = 1 + d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring
  have h2f : (√(2:ℝ) : ℂ)^4 = 4 := by
    rw [show (4:ℕ) = 2 * 2 by rfl, pow_mul, h2]; norm_num
  have hdc : (d:ℂ) ≠ 0 := by norm_cast; omega
  have hdc1 : (d:ℂ) + 1 ≠ 0 := by norm_cast
  ext a b
  simp only [Matrix.sum_apply, Fin.sum_univ_three, controlPOVM, Matrix.smul_apply, smul_eq_mul]
  fin_cases a <;> fin_cases b <;>
  simp [controlEffectVector, controlVector, Matrix.one_apply] <;>
  field_simp <;> push_cast <;> ring_nf <;> simp only [h2, h2f, h3, h4, h4', Complex.ofReal_ofNat, Nat.cast_ofNat] <;> ring_nf

lemma g59c_vmv (u : Fin 2 → ℂ) : (fun a b => u a * conj (u b)) = Matrix.vecMulVec u (star u) := by
  ext a b; simp [Matrix.vecMulVec_apply]

lemma g59c_povm_psd (d : ℕ) (hd : 2 ≤ d) (n : Fin 3) : (controlPOVM d n).PosSemidef := by
  unfold controlPOVM
  by_cases h : n = 0
  · simp only [h, if_true]
    rw [g59c_vmv]
    apply Matrix.PosSemidef.smul (Matrix.posSemidef_vecMulVec_self_star _)
    have hd' : (2:ℝ) ≤ d := by exact_mod_cast hd
    have : (0:ℝ) ≤ (9*(d : ℝ)*((d : ℝ)+1)-2)/(9*(d : ℝ)*((d : ℝ)+1)) := by
      apply div_nonneg _ (by positivity); nlinarith
    exact_mod_cast this
  · simp only [h, if_false]
    rw [g59c_vmv]; exact Matrix.posSemidef_vecMulVec_self_star _

lemma g59c_post_nonneg {d : ℕ} (hd : 2 ≤ d) (k : Fin d) (n : Fin 3) (i j : Fin d) :
    0 ≤ postprocess k n i j := by
  have hd' : (2:ℝ) ≤ d := by exact_mod_cast hd
  have : (0:ℝ) ≤ 1 / ((d:ℝ) - 1) := by apply div_nonneg <;> linarith
  unfold postprocess; split_ifs <;> first | exact this | norm_num

lemma g59c_post_sum {d : ℕ} (hd : 2 ≤ d) (k : Fin d) (n : Fin 3) :
    ∑ i, ∑ j, postprocess k n i j = 1 := by
  have hd' : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hc : ((Finset.univ.filter (fun j : Fin d => j ≠ k)).card : ℝ) = (d:ℝ) - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin, Nat.cast_sub (by omega)]; simp
  have hne : (d:ℝ) - 1 ≠ 0 := by linarith
  have hn : n = 0 ∨ n = 1 ∨ n = 2 := by fin_cases n <;> simp
  rcases hn with rfl | rfl | rfl
  · simp [postprocess, ite_and]
  · simp only [postprocess, show (1 : Fin 3) ≠ 0 by decide, if_false, if_true, ite_and]
    rw [Fintype.sum_eq_single k (fun x hx => by simp [hx])]
    simp only [if_true]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hc]
    field_simp
  · simp only [postprocess, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
      if_false, ite_and]
    rw [Finset.sum_comm]
    rw [Fintype.sum_eq_single k (fun x hx => by simp [hx])]
    simp only [if_true]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hc]
    field_simp

def g59c_E (d : ℕ) (k : Fin d) : Matrix (ABCD d) (ABC d) ℂ := fun x z => if x = (z, k) then 1 else 0

lemma g59c_lift_psd {d : ℕ} (B : DiagonalInstrument d) (i j : Fin d)
    (hB : ∀ k, (B i j k).PosSemidef) : (liftDiagonal B i j).PosSemidef := by
  have : liftDiagonal B i j = ∑ k, g59c_E d k * B i j k * (g59c_E d k)ᴴ := by
    ext x y
    rcases x with ⟨x1, x2⟩; rcases y with ⟨y1, y2⟩
    change (if x2 = y2 then B i j x2 x1 y1 else 0) = _
    rw [Matrix.sum_apply]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    simp only [g59c_E, Prod.mk.injEq, ite_and, apply_ite star, star_one, star_zero]
    simp only [ite_mul, zero_mul, one_mul, mul_ite, mul_zero, mul_one]
    simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel,
      Finset.sum_const_zero]
    by_cases h : x2 = y2
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [this]
  exact Matrix.posSemidef_sum _ (fun k _ => (hB k).mul_mul_conjTranspose_same _)

lemma g59c_ce_real (d : ℕ) (s a : Fin 2) :
    (starRingEnd ℂ) (controlEffectVector d s a) = controlEffectVector d s a := by
  simp only [controlEffectVector, controlVector, map_add, map_mul, Complex.conj_ofReal]
  congr 2; split_ifs <;> simp

lemma g59c_block_ne (d : ℕ) (i j k : Fin d) (hij : i ≠ j) :
    g59c_Mnet d i j k =
      (if k = i then (1/(2*((d : ℝ)-1)) : ℂ) • Matrix.vecMulVec (controlEffectVector d 0)
        (star (controlEffectVector d 0)) else 0) +
      (if k = j then (1/(2*((d : ℝ)-1)) : ℂ) • Matrix.vecMulVec (controlEffectVector d 1)
        (star (controlEffectVector d 1)) else 0) := by
  ext a b
  simp only [g59c_Mnet, Fin.sum_univ_three, postprocess, controlPOVM, Matrix.add_apply]
  simp only [show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide, if_true, if_false]
  have h1 := g59c_ce_real d 0 b
  have h2 := g59c_ce_real d 1 b
  have h1' := g59c_ce_real d 0 a
  have h2' := g59c_ce_real d 1 a
  by_cases hki : k = i
  · subst hki
    simp [hij, Ne.symm hij, Matrix.vecMulVec_apply, h1, h1']
    ring
  · by_cases hkj : k = j
    · subst hkj
      simp [hki, Ne.symm hki, Matrix.vecMulVec_apply, h2, h2']
      ring
    · simp [hki, hkj, Ne.symm hki, Ne.symm hkj]

lemma g59c_block_eq (d : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    ((9*pairDimension d 0-1)/(9*(d : ℝ)) : ℂ) •
          (alphaEmbedding d 0 * (alphaEmbedding d 0).conjTranspose) =
      g59c_T d (g59c_Mnet d i i i) := by
  rw [g59c_alpha, ← map_smul]
  congr 1
  have hd' : (2:ℝ) ≤ d := by exact_mod_cast hd
  have a1 : (√(d:ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  have a2 : (√((d:ℝ)+1) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  have a4 : (√(2:ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  have h2 : (√(2:ℝ) : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have h4 : (√((d:ℝ)+1) : ℂ)^2 = d + 1 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring
  have h4' : (√(1 + (d:ℝ)) : ℂ)^2 = 1 + d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring
  have hdc : (d:ℂ) ≠ 0 := by norm_cast; omega
  have hdc1 : (d:ℂ) + 1 ≠ 0 := by norm_cast
  ext a b
  simp only [g59c_Mnet, Fin.sum_univ_three, postprocess, controlPOVM, Matrix.smul_apply,
    smul_eq_mul, Matrix.vecMulVec_apply]
  fin_cases a <;> fin_cases b <;>
  simp [controlVector, pairDimension] <;>
  field_simp <;> push_cast <;> ring_nf <;> simp only [h2, h4, h4', Complex.ofReal_ofNat] <;> ring_nf

lemma g59c_print (d : ℕ) (hd : 2 ≤ d) :
    printedInstrument d = liftDiagonal (fun i j k => g59c_T d (g59c_Mnet d i j k)) := by
  unfold printedInstrument
  congr 1
  funext i j k
  by_cases hij : i = j
  · subst hij
    by_cases hk : k = i
    · subst hk; simp only [if_true]; exact g59c_block_eq d hd k
    · simp only [if_true, if_neg hk]
      have : g59c_Mnet d i i k = 0 := by
        ext a b
        simp [g59c_Mnet, Fin.sum_univ_three, postprocess, hk, Ne.symm hk]
      rw [this, map_zero]
  · simp only [if_neg hij]
    rw [g59c_EE d _ (printedPhi d 0) (g59c_phi d hd 0), g59c_EE d _ (printedPhi d 1) (g59c_phi d hd 1),
      g59c_block_ne d i j k hij, map_add]
    congr 1 <;> split_ifs <;> simp [map_smul]

lemma g59c_Msum (d : ℕ) (hd : 2 ≤ d) (k : Fin d) :
    ∑ i, ∑ j, g59c_Mnet d i j k = (1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hP : ∀ b a, (∑ n, controlPOVM d n) b a = (1 : Matrix (Fin 2) (Fin 2) ℂ) b a :=
    fun b a => by rw [g59c_povm_sum d hd]
  have hs : ∀ n, ∑ i, ∑ j, (postprocess k n i j : ℂ) = 1 := by
    intro n; exact_mod_cast g59c_post_sum hd k n
  ext a b
  simp only [Matrix.sum_apply, g59c_Mnet, Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul]
  have e := hP b a
  simp only [Matrix.sum_apply, Fin.sum_univ_three] at e
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hs, one_mul]
  have e2 : (1 : Matrix (Fin 2) (Fin 2) ℂ) b a = (1 : Matrix (Fin 2) (Fin 2) ℂ) a b := by
    simp [Matrix.one_apply, eq_comm]
  linear_combination (1/2 : ℂ) * e + (1/2 : ℂ) * e2

lemma g59c_trace (d : ℕ) : traceRight (g59c_T d ((1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))) = 1 := by
  ext p q
  simp only [traceRight, Matrix.of_apply, g59c_T_apply, Fin.sum_univ_two, Matrix.smul_apply,
    Matrix.one_apply, g59c_V]
  simp only [Finset.sum_add_distrib]
  rw [Fintype.sum_eq_single p.1 (fun x hx => by simp [Ne.symm hx])]
  rw [Fintype.sum_eq_single p.2 (fun x hx => by simp [Ne.symm hx])]
  rw [Fintype.sum_eq_single p.2 (fun x hx => by simp [Ne.symm hx])]
  rw [Fintype.sum_eq_single p.1 (fun x hx => by simp [Ne.symm hx])]
  rcases p with ⟨p1, p2⟩; rcases q with ⟨q1, q2⟩
  simp only [Prod.mk.injEq, and_self, if_true]
  by_cases h : p1 = q1 ∧ p2 = q2
  · obtain ⟨rfl, rfl⟩ := h; simp; norm_num
  · have h' : ¬(q1 = p1 ∧ q2 = p2) := fun h' => h ⟨h'.1.symm, h'.2.symm⟩
    simp only [h, h', if_false]; push_cast; ring

lemma g59c_povm_symm (d : ℕ) (n : Fin 3) (a b : Fin 2) : controlPOVM d n b a = controlPOVM d n a b := by
  fin_cases n <;> simp [controlPOVM, controlVector, g59c_ce_real] <;> ring

lemma g59c_Mnet_psd (d : ℕ) (hd : 2 ≤ d) (i j k : Fin d) : (g59c_Mnet d i j k).PosSemidef := by
  have : g59c_Mnet d i j k = ∑ n, ((((1/2 : ℝ) * postprocess k n i j : ℝ)) : ℂ) • controlPOVM d n := by
    ext a b
    simp only [g59c_Mnet, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, g59c_povm_symm]
    push_cast; ring_nf
  rw [this]
  refine Matrix.posSemidef_sum _ (fun n _ => Matrix.PosSemidef.smul (g59c_povm_psd d hd n) ?_)
  have := g59c_post_nonneg hd k n i j
  exact_mod_cast (by positivity : (0:ℝ) ≤ (1/2 : ℝ) * postprocess k n i j)

theorem g59c_main (d : ℕ) (hd : 2 ≤ d) :
    IsPOVM (controlPOVM d) ∧
    (∀ k : Fin d, ∀ n : Fin 3,
      (∀ i j, 0 ≤ postprocess k n i j) ∧ (∑ i, ∑ j, postprocess k n i j) = 1) ∧
    (controlledSwap d).conjTranspose * controlledSwap d = 1 ∧
    IsReplicationStrategy .cloning (printedInstrument d) ∧
    printedInstrument d = networkInstrument d := by
  refine ⟨⟨g59c_povm_psd d hd, g59c_povm_sum d hd⟩,
    fun k n => ⟨fun i j => g59c_post_nonneg hd k n i j, g59c_post_sum hd k n⟩,
    g59c_unitary d, ⟨?_, ?_⟩, by rw [g59c_print d hd, g59c_net d]⟩
  · intro i j
    rw [g59c_print d hd]
    apply g59c_lift_psd
    intro k
    apply g59c_T_psd
    exact g59c_Mnet_psd d hd i j k
  · refine ⟨g59c_T d ((1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)), ?_, g59c_trace d, ?_⟩
    · exact g59c_T_psd d _ (Matrix.PosSemidef.smul Matrix.PosSemidef.one
      (by rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) by push_cast; ring]; exact_mod_cast (by norm_num : (0:ℝ) ≤ 1/2)))
    · rw [g59c_print d hd]
      ext x y
      simp only [Matrix.sum_apply, cloningTotal, Matrix.kronecker_apply, Matrix.one_apply]
      rw [← g59c_Msum d hd y.2, map_sum]
      simp only [map_sum, Matrix.sum_apply]
      by_cases h : x.2 = y.2
      · simp [liftDiagonal, h, Matrix.sum_apply, Finset.sum_apply, Matrix.one_apply]
      · simp [liftDiagonal, h, Matrix.sum_apply, Finset.sum_apply]



open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

/-- arXiv:1103.5709v2 PDF p.8, Eqs.(64)-(69): the printed controlled-SWAP
realization identity and its full three-effect POVM and stochastic postprocessing.
Source basis correction: Eq.(66) prints sigma_z; use the explicit reflection
Z_pm=|+><+|-|-><-|, since computational Pauli Z fails the POVM identity sum.
The existing effect-vector formula and Eqs.(64),(69) select exactly this reflection.
All scalar coefficients are unchanged. No optimality of this network is asserted. -/
theorem solution (d : ℕ) (hd : 2 ≤ d) :
    IsPOVM (controlPOVM d) ∧
    (∀ k : Fin d, ∀ n : Fin 3,
      (∀ i j, 0 ≤ postprocess k n i j) ∧ (∑ i, ∑ j, postprocess k n i j) = 1) ∧
    (controlledSwap d).conjTranspose * controlledSwap d = 1 ∧
    IsReplicationStrategy .cloning (printedInstrument d) ∧
    printedInstrument d = networkInstrument d := g59c_main d hd


end
