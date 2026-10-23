-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P39.positiveFourierInsufficient
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T16:01:31.14362+00:00
-- url     : https://prove2.me/submissions/ecc329cf-91e1-4b67-8bad-10451936fdc9

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P39

noncomputable section

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable

namespace X6P39M

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P39

local notation "ω" => SparsePauliNoise.symplecticPairing

theorem sgn_add (x y : ZMod 2) :
    (-1 : ℝ) ^ (x + y).val = (-1 : ℝ) ^ x.val * (-1 : ℝ) ^ y.val := by
  rw [ZMod.val_add, ← neg_one_pow_eq_pow_mod_two, pow_add]

theorem sgn_sum {ι : Type*} (s : Finset ι) (c : ι → ZMod 2) :
    (-1 : ℝ) ^ (∑ a ∈ s, c a).val = ∏ a ∈ s, (-1 : ℝ) ^ (c a).val := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, sgn_add, ih]

theorem omega_add_right {N : ℕ} (u a b : PauliLabel N) : ω u (a + b) = ω u a + ω u b := by
  simp only [SparsePauliNoise.symplecticPairing, Prod.fst_add, Prod.snd_add, dotProduct_add]
  ring

theorem omega_add_left {N : ℕ} (u a b : PauliLabel N) : ω (a + b) u = ω a u + ω b u := by
  simp only [SparsePauliNoise.symplecticPairing, Prod.fst_add, Prod.snd_add, add_dotProduct]
  ring

theorem omega_sum_right {N m : ℕ} (u : PauliLabel N) (b : Fin m → ZMod 2) (e : Fin m → PauliLabel N) :
    ω u (∑ a, b a • e a) = ∑ a, b a * ω u (e a) := by
  simp only [SparsePauliNoise.symplecticPairing, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst,
    Prod.smul_snd, dotProduct_sum, dotProduct_smul, smul_eq_mul, Finset.sum_add_distrib, mul_add]

theorem wht_event {N m : ℕ} (e : Fin m → PauliLabel N) (p : Fin m → ℝ) (u : PauliLabel N) :
    SparsePauliNoise.eigenvalueWHT (eventLaw e p) u =
      ∏ a, ((1 - p a) + p a * (-1 : ℝ) ^ (ω u (e a)).val) := by
  unfold SparsePauliNoise.eigenvalueWHT eventLaw pushLaw
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr (g := fun b : Bits m => (-1 : ℝ) ^ (ω u (∑ a, b a • e a)).val *
    binaryLaw p b) rfl fun b _ => ?_).trans ?_
  · simp_rw [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq]; simp
  simp_rw [omega_sum_right, sgn_sum, binaryLaw, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun a (x : ZMod 2) =>
    (-1 : ℝ) ^ (x * ω u (e a)).val * (if x = 1 then p a else 1 - p a))]
  refine Finset.prod_congr rfl fun a _ => ?_
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} :=
    (Finset.eq_univ_of_card _ (by rw [Finset.card_pair zero_ne_one, ZMod.card])).symm
  rw [huniv, Finset.sum_pair zero_ne_one]
  simp
  ring

theorem triple (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s1 s2 s3 : ℝ)
    (h1 : s1 = 1 ∨ s1 = -1) (h2 : s2 = 1 ∨ s2 = -1) (h3 : s3 = 1 ∨ s3 = -1)
    (h : s1 * s2 * s3 = 1) :
    0 ≤ ((1 - p) + p * s1) * ((1 - p) + p * s2) * ((1 - p) + p * s3) := by
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> rcases h3 with rfl | rfl <;>
    (try norm_num at h) <;> nlinarith [sq_nonneg (1 - 2 * p)]

theorem labels_sum : labelX + labelY + labelZ = (0 : PauliLabel 1) := by
  ext i <;> fin_cases i <;> simp [labelX, labelY, labelZ] <;> decide

theorem indep_nonneg (nu : PauliLabel 1 → ℝ) (h : HasIndependentEvents nu) :
    0 ≤ SparsePauliNoise.eigenvalueWHT nu labelX *
      SparsePauliNoise.eigenvalueWHT nu labelY *
      SparsePauliNoise.eigenvalueWHT nu labelZ := by
  obtain ⟨m, e, p, hp, rfl⟩ := h
  rw [wht_event, wht_event, wht_event, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_nonneg fun a _ => ?_
  have hsum : ω labelX (e a) + ω labelY (e a) + ω labelZ (e a) = 0 := by
    rw [← omega_add_left, ← omega_add_left, labels_sum]
    simp [SparsePauliNoise.symplecticPairing]
  have hprod : (-1 : ℝ) ^ (ω labelX (e a)).val * (-1 : ℝ) ^ (ω labelY (e a)).val *
      (-1 : ℝ) ^ (ω labelZ (e a)).val = 1 := by
    rw [← sgn_add, ← sgn_add, hsum]; simp
  exact triple (p a) (hp a).1 (hp a).2 _ _ _ (neg_one_pow_eq_or ℝ _) (neg_one_pow_eq_or ℝ _)
    (neg_one_pow_eq_or ℝ _) hprod

def proj {N : ℕ} (j : Fin N) (x : PauliLabel N) : PauliLabel 1 :=
  ((fun _ => x.1 j), (fun _ => x.2 j))

theorem push_push {A B C : Type*} [Fintype A] [Fintype B] (q : A → ℝ) (f : A → B) (g : B → C) :
    pushLaw (pushLaw q f) g = pushLaw q (g ∘ f) := by
  funext z
  simp only [pushLaw]
  have : ∀ y, (if g y = z then ∑ b, (if f b = y then q b else 0) else 0) =
      ∑ b, (if f b = y then (if g y = z then q b else 0) else 0) := by
    intro y
    split_ifs with h <;> simp [h]
  simp_rw [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_ite_eq]
  simp

theorem marginal_event {N m : ℕ} (e : Fin m → PauliLabel N) (p : Fin m → ℝ) (j : Fin N) :
    pauliMarginal (eventLaw e p) j = eventLaw (fun a => proj j (e a)) p := by
  unfold pauliMarginal eventLaw
  rw [push_push]
  congr 1
  funext b
  ext i <;> simp [proj, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]

end X6P39M

open scoped Matrix ComplexConjugate

namespace X6P39F

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P39 X6P39M

local notation "ω" => SparsePauliNoise.symplecticPairing

theorem cases4 (e : PauliLabel 1) : e = 0 ∨ e = labelX ∨ e = labelY ∨ e = labelZ := by
  obtain ⟨a, b⟩ := e
  have ha : a = ![a 0] := by ext i; fin_cases i; rfl
  have hb : b = ![b 0] := by ext i; fin_cases i; rfl
  rw [ha, hb]
  generalize a 0 = x
  generalize b 0 = y
  fin_cases x <;> fin_cases y
  · left; ext i <;> fin_cases i <;> rfl
  · right; right; right; rfl
  · right; left; rfl
  · right; right; left; rfl

theorem sum4 (f : PauliLabel 1 → ℝ) : ∑ x, f x = f 0 + f labelX + f labelY + f labelZ := by
  let e : PauliLabel 1 ≃ ZMod 2 × ZMod 2 :=
    (Equiv.funUnique (Fin 1) (ZMod 2)).prodCongr (Equiv.funUnique (Fin 1) (ZMod 2))
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  change ∑ x : Fin 2, ∑ y : Fin 2, f (e.symm (x, y)) = _
  simp only [Fin.sum_univ_two]
  have h00 : e.symm (0, 0) = 0 := by ext i <;> fin_cases i <;> rfl
  have h10 : e.symm (1, 0) = labelX := by ext i <;> fin_cases i <;> rfl
  have h11 : e.symm (1, 1) = labelY := by ext i <;> fin_cases i <;> rfl
  have h01 : e.symm (0, 1) = labelZ := by ext i <;> fin_cases i <;> rfl
  change f (e.symm (0, 0)) + f (e.symm (0, 1)) + (f (e.symm (1, 0)) + f (e.symm (1, 1))) = _
  rw [h00, h10, h11, h01]; ring

theorem X_ne0 : labelX ≠ 0 := by
  intro h; have := congrArg (fun x : PauliLabel 1 => x.1 0) h; simp [labelX] at this
theorem Y_ne0 : labelY ≠ 0 := by
  intro h; have := congrArg (fun x : PauliLabel 1 => x.1 0) h; simp [labelY] at this
theorem Z_ne0 : labelZ ≠ 0 := by
  intro h; have := congrArg (fun x : PauliLabel 1 => x.2 0) h; simp [labelZ] at this
theorem Y_neX : labelY ≠ labelX := by
  intro h; have := congrArg (fun x : PauliLabel 1 => x.2 0) h; simp [labelX, labelY] at this
theorem Z_neX : labelZ ≠ labelX := by
  intro h; have := congrArg (fun x : PauliLabel 1 => x.1 0) h; simp [labelX, labelZ] at this
theorem Z_neY : labelZ ≠ labelY := by
  intro h; have := congrArg (fun x : PauliLabel 1 => x.1 0) h; simp [labelY, labelZ] at this

theorem pv0 (v : Fin 4 → ℝ) : pauliVector v 0 = v 0 := by simp [pauliVector]
theorem pvX (v : Fin 4 → ℝ) : pauliVector v labelX = v 1 := by
  simp [pauliVector, X_ne0]
theorem pvY (v : Fin 4 → ℝ) : pauliVector v labelY = v 2 := by
  simp [pauliVector, Y_ne0, Y_neX]
theorem pvZ (v : Fin 4 → ℝ) : pauliVector v labelZ = v 3 := by
  simp [pauliVector, Z_ne0, Z_neX, Z_neY]

/-- sign table -/
theorem sg (u v : PauliLabel 1) : (-1 : ℝ) ^ (ω u v).val =
    if u = 0 ∨ v = 0 ∨ u = v then 1 else -1 := by
  rcases cases4 u with rfl | rfl | rfl | rfl <;> rcases cases4 v with rfl | rfl | rfl | rfl <;>
    simp [SparsePauliNoise.symplecticPairing, labelX, labelY, labelZ, dotProduct] <;>
    first | rfl | (rw [show (1 : ZMod 2).val = 1 from rfl]; norm_num)

theorem law_eq : positiveFourierLaw = pauliVector (![721/800,1/800,39/800,39/800]) := by
  funext b
  unfold positiveFourierLaw SparsePauliNoise.inverseWHT
  rw [sum4]
  simp only [sg, pv0, pvX, pvY, pvZ]
  rcases cases4 b with rfl | rfl | rfl | rfl <;>
    simp [pv0, pvX, pvY, pvZ, X_ne0, Y_ne0, Z_ne0, Y_neX, Z_neX, Z_neY,
      Y_neX.symm, Z_neX.symm, Z_neY.symm] <;> norm_num

theorem wht_eq : SparsePauliNoise.eigenvalueWHT positiveFourierLaw =
    pauliVector (![1,161/200,9/10,9/10]) := by
  rw [law_eq]
  funext b
  unfold SparsePauliNoise.eigenvalueWHT
  rw [sum4]
  simp only [sg, pv0, pvX, pvY, pvZ]
  rcases cases4 b with rfl | rfl | rfl | rfl <;>
    simp [pv0, pvX, pvY, pvZ, X_ne0, Y_ne0, Z_ne0, Y_neX, Z_neX, Z_neY,
      Y_neX.symm, Z_neX.symm, Z_neY.symm] <;> norm_num

theorem ev (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (sX sY sZ : ℝ)
    (hX : sX = 1 ∨ sX = -1) (hY : sY = 1 ∨ sY = -1) (hZ : sZ = 1 ∨ sZ = -1)
    (hprod : sX * sY * sZ = 1) :
    ∃ G : ℝ, 0 ≤ G ∧ G ≤ 1 ∧
      ((1 - p) + p * sY) * ((1 - p) + p * sZ) = ((1 - p) + p * sX) * G := by
  rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;> rcases hZ with rfl | rfl <;>
    norm_num at hprod
  · exact ⟨1, by norm_num, le_rfl, by ring⟩
  · exact ⟨(1 - 2 * p) ^ 2, sq_nonneg _, by nlinarith, by ring⟩
  · exact ⟨1, by norm_num, le_rfl, by ring⟩
  · exact ⟨1, by norm_num, le_rfl, by ring⟩

theorem not_indep : ¬ HasIndependentEvents positiveFourierLaw := by
  rintro ⟨m, e, p, hp, heq⟩
  have hW := wht_eq
  rw [heq] at hW
  have hx := congrFun hW labelX
  have hy := congrFun hW labelY
  have hz := congrFun hW labelZ
  rw [wht_event, pvX] at hx
  rw [wht_event, pvY] at hy
  rw [wht_event, pvZ] at hz
  have hG : ∀ a, ∃ G : ℝ, 0 ≤ G ∧ G ≤ 1 ∧
      ((1 - p a) + p a * (-1 : ℝ) ^ (ω labelY (e a)).val) *
        ((1 - p a) + p a * (-1 : ℝ) ^ (ω labelZ (e a)).val) =
      ((1 - p a) + p a * (-1 : ℝ) ^ (ω labelX (e a)).val) * G := by
    intro a
    have hsum : ω labelX (e a) + ω labelY (e a) + ω labelZ (e a) = 0 := by
      rw [← omega_add_left, ← omega_add_left, labels_sum]
      simp [SparsePauliNoise.symplecticPairing]
    have hprod : (-1 : ℝ) ^ (ω labelX (e a)).val * (-1 : ℝ) ^ (ω labelY (e a)).val *
        (-1 : ℝ) ^ (ω labelZ (e a)).val = 1 := by
      rw [← sgn_add, ← sgn_add, hsum]; simp
    exact ev (p a) (hp a).1 (hp a).2 _ _ _ (neg_one_pow_eq_or ℝ _) (neg_one_pow_eq_or ℝ _)
      (neg_one_pow_eq_or ℝ _) hprod
  choose G hG0 hG1 hGe using hG
  have key : (∏ a, ((1 - p a) + p a * (-1 : ℝ) ^ (ω labelY (e a)).val)) *
      (∏ a, ((1 - p a) + p a * (-1 : ℝ) ^ (ω labelZ (e a)).val)) =
      (∏ a, ((1 - p a) + p a * (-1 : ℝ) ^ (ω labelX (e a)).val)) * ∏ a, G a := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun a _ => hGe a
  rw [hx, hy, hz] at key
  have h1 : ∏ a, G a ≤ 1 := Finset.prod_le_one (fun a _ => hG0 a) (fun a _ => hG1 a)
  have h3 : (![1, 161/200, 9/10, 9/10] : Fin 4 → ℝ) 3 = 9/10 := rfl
  simp only [Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_zero,
    Matrix.head_cons, Matrix.tail_cons, h3] at key
  norm_num at key
  nlinarith

end X6P39F

open X6P39F in
theorem solution :
    QAlgorithms.Learning.IsDistribution QAlgorithms.Papers.Independent.Information100.P39.positiveFourierLaw ∧
    QAlgorithms.Papers.Independent.Information100.P39.positiveFourierLaw =
      QAlgorithms.Papers.Independent.Information100.P39.pauliVector (![721/800,1/800,39/800,39/800]) ∧
    QAlgorithms.SparsePauliNoise.eigenvalueWHT QAlgorithms.Papers.Independent.Information100.P39.positiveFourierLaw =
      QAlgorithms.Papers.Independent.Information100.P39.pauliVector (![1,161/200,9/10,9/10]) ∧
    (∀ u, 0 < QAlgorithms.SparsePauliNoise.eigenvalueWHT
      QAlgorithms.Papers.Independent.Information100.P39.positiveFourierLaw u) ∧
    ¬ QAlgorithms.Papers.Independent.Information100.P39.HasIndependentEvents
      QAlgorithms.Papers.Independent.Information100.P39.positiveFourierLaw := by
  refine ⟨⟨fun x => ?_, ?_⟩, law_eq, wht_eq, fun u => ?_, not_indep⟩
  · rw [law_eq]
    rcases cases4 x with rfl | rfl | rfl | rfl <;> simp [pv0, pvX, pvY, pvZ] <;> norm_num
  · rw [law_eq, sum4]; simp [pv0, pvX, pvY, pvZ]; norm_num
  · rw [wht_eq]
    rcases cases4 u with rfl | rfl | rfl | rfl <;> simp [pv0, pvX, pvY, pvZ] <;> norm_num
