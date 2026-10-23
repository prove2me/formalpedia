-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P39.singleQubitFourierCriterion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T16:06:51.709868+00:00
-- url     : https://prove2.me/submissions/0dbc62e7-fd5a-45fc-bef6-121bd481b653

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

namespace X6P39C

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P39 X6P39M X6P39F

local notation "ω" => SparsePauliNoise.symplecticPairing
local notation "W" => SparsePauliNoise.eigenvalueWHT

theorem inv_formula (nu : PauliLabel 1 → ℝ) (b : PauliLabel 1) :
    nu b = (1/4) * ∑ u, (-1 : ℝ) ^ (ω b u).val * W nu u := by
  unfold SparsePauliNoise.eigenvalueWHT
  simp only [sum4, sg]
  rcases cases4 b with rfl | rfl | rfl | rfl <;>
    simp [X_ne0, Y_ne0, Z_ne0, Y_neX, Z_neX, Z_neY, Y_neX.symm, Z_neX.symm, Z_neY.symm] <;>
    ring

theorem wht_inj (nu mu : PauliLabel 1 → ℝ) (h : ∀ u, W nu u = W mu u) : nu = mu := by
  funext b
  rw [inv_formula nu, inv_formula mu]
  simp only [h]

theorem wht_zero {N : ℕ} (nu : PauliLabel N → ℝ) : W nu 0 = ∑ v, nu v := by
  unfold SparsePauliNoise.eigenvalueWHT
  simp [SparsePauliNoise.symplecticPairing]

theorem eventLaw_dist {N m : ℕ} (e : Fin m → PauliLabel N) (p : Fin m → ℝ)
    (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) : Learning.IsDistribution (eventLaw e p) := by
  refine ⟨fun x => ?_, ?_⟩
  · unfold eventLaw pushLaw binaryLaw
    refine Finset.sum_nonneg fun b _ => ?_
    split_ifs
    · exact Finset.prod_nonneg fun a _ => by
        split_ifs <;> linarith [(hp a).1, (hp a).2]
    · exact le_rfl
  · rw [← wht_zero, wht_event]
    refine Finset.prod_eq_one fun a _ => ?_
    simp [SparsePauliNoise.symplecticPairing]

theorem wht_xyz (p : Fin 3 → ℝ) :
    W (eventLaw xyzEvents p) 0 = 1 ∧
    W (eventLaw xyzEvents p) labelX = (1 - 2 * p 1) * (1 - 2 * p 2) ∧
    W (eventLaw xyzEvents p) labelY = (1 - 2 * p 0) * (1 - 2 * p 2) ∧
    W (eventLaw xyzEvents p) labelZ = (1 - 2 * p 0) * (1 - 2 * p 1) := by
  simp only [wht_event, Fin.prod_univ_three, sg, xyzEvents]
  simp [X_ne0, Y_ne0, Z_ne0, Y_neX, Z_neX, Z_neY, Y_neX.symm, Z_neX.symm, Z_neY.symm]
  refine ⟨by ring, by ring, by ring⟩

/-- per-event factorization -/
theorem ev3 (p : ℝ) (sX sY sZ : ℝ)
    (hX : sX = 1 ∨ sX = -1) (hY : sY = 1 ∨ sY = -1) (hZ : sZ = 1 ∨ sZ = -1)
    (hprod : sX * sY * sZ = 1) :
    let a := 1 - p * (1 + sX) * (1 - sY) / 2
    let b := 1 - p * (1 + sY) * (1 - sZ) / 2
    let c := 1 - p * (1 + sZ) * (1 - sX) / 2
    ((1 - p) + p * sX) = b * c ∧ ((1 - p) + p * sY) = a * c ∧ ((1 - p) + p * sZ) = a * b ∧
      (a = 1 ∨ a = 1 - 2 * p) ∧ (b = 1 ∨ b = 1 - 2 * p) ∧ (c = 1 ∨ c = 1 - 2 * p) := by
  rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;> rcases hZ with rfl | rfl <;>
    norm_num at hprod <;> simp only <;> refine ⟨by ring, by ring, by ring, ?_, ?_, ?_⟩ <;>
    first | (left; ring1) | (right; ring1)

theorem prod_abs_le {m : ℕ} (f : Fin m → ℝ) (h : ∀ a, f a = 1 ∨ ∃ p, 0 ≤ p ∧ p ≤ 1 ∧ f a = 1 - 2 * p) :
    (∏ a, f a) ∈ Set.Icc (-1 : ℝ) 1 := by
  have : |∏ a, f a| ≤ 1 := by
    rw [Finset.abs_prod]
    refine Finset.prod_le_one (fun a _ => abs_nonneg _) fun a _ => ?_
    rcases h a with h1 | ⟨p, hp0, hp1, h1⟩ <;> rw [h1]
    · simp
    · rw [abs_le]; constructor <;> linarith
  exact ⟨by linarith [neg_abs_le (∏ a, f a)], le_trans (le_abs_self _) this⟩

theorem forward (nu : PauliLabel 1 → ℝ) (h : HasIndependentEvents nu) :
    ∃ a b c : ℝ, a ∈ Set.Icc (-1) 1 ∧ b ∈ Set.Icc (-1) 1 ∧ c ∈ Set.Icc (-1) 1 ∧
      FourierFactors nu a b c := by
  obtain ⟨m, e, p, hp, rfl⟩ := h
  have hE : ∀ a, _ := fun a => ev3 (p a) ((-1 : ℝ) ^ (ω labelX (e a)).val)
    ((-1 : ℝ) ^ (ω labelY (e a)).val) ((-1 : ℝ) ^ (ω labelZ (e a)).val)
    (neg_one_pow_eq_or ℝ _) (neg_one_pow_eq_or ℝ _) (neg_one_pow_eq_or ℝ _) (by
      have hsum : ω labelX (e a) + ω labelY (e a) + ω labelZ (e a) = 0 := by
        rw [← omega_add_left, ← omega_add_left, labels_sum]
        simp [SparsePauliNoise.symplecticPairing]
      rw [← sgn_add, ← sgn_add, hsum]; simp)
  set sX := fun a => (-1 : ℝ) ^ (ω labelX (e a)).val
  set sY := fun a => (-1 : ℝ) ^ (ω labelY (e a)).val
  set sZ := fun a => (-1 : ℝ) ^ (ω labelZ (e a)).val
  refine ⟨∏ a, (1 - p a * (1 + sX a) * (1 - sY a) / 2),
    ∏ a, (1 - p a * (1 + sY a) * (1 - sZ a) / 2),
    ∏ a, (1 - p a * (1 + sZ a) * (1 - sX a) / 2), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine prod_abs_le _ fun a => ?_
    rcases (hE a).2.2.2.1 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨p a, (hp a).1, (hp a).2, h⟩
  · refine prod_abs_le _ fun a => ?_
    rcases (hE a).2.2.2.2.1 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨p a, (hp a).1, (hp a).2, h⟩
  · refine prod_abs_le _ fun a => ?_
    rcases (hE a).2.2.2.2.2 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨p a, (hp a).1, (hp a).2, h⟩
  · rw [wht_event, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun a _ => (hE a).1
  · rw [wht_event, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun a _ => (hE a).2.1
  · rw [wht_event, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun a _ => (hE a).2.2.1

theorem converse (nu : PauliLabel 1 → ℝ) (hnu : Learning.IsDistribution nu) (a b c : ℝ)
    (h : FourierFactors nu a b c) :
    nu = eventLaw xyzEvents (![(1-a)/2, (1-b)/2, (1-c)/2]) := by
  apply wht_inj
  obtain ⟨h0, hx, hy, hz⟩ := wht_xyz (![(1-a)/2, (1-b)/2, (1-c)/2])
  obtain ⟨fx, fy, fz⟩ := h
  intro u
  rcases cases4 u with rfl | rfl | rfl | rfl
  · rw [h0, wht_zero, hnu.2]
  · rw [hx, fx]; simp; ring
  · rw [hy, fy]; simp; ring
  · rw [hz, fz]; simp; ring

theorem shift_wht (mu : PauliLabel 1 → ℝ) (t u : PauliLabel 1) :
    W (fun v => mu (v - t)) u = (-1 : ℝ) ^ (ω u t).val * W mu u := by
  unfold SparsePauliNoise.eigenvalueWHT
  rw [← Equiv.sum_comp (Equiv.addRight t), Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Equiv.coe_addRight, add_sub_cancel_right, omega_add_right, sgn_add]
  ring

theorem sg_ite (u L : PauliLabel 1) (P : Prop) [Decidable P] :
    (-1 : ℝ) ^ (ω u (if P then L else 0)).val = if P then (-1 : ℝ) ^ (ω u L).val else 1 := by
  split_ifs
  · rfl
  · simp [SparsePauliNoise.symplecticPairing]

theorem part3 (nu : PauliLabel 1 → ℝ) (hnu : Learning.IsDistribution nu)
    (h : HasIndependentEvents nu) :
    ∃ t : PauliLabel 1, ∃ mu : PauliLabel 1 → ℝ,
      Learning.IsDistribution mu ∧ HasSmallEvents mu ∧
      (∀ u, 0 ≤ W mu u) ∧ nu = fun u => mu (u - t) := by
  obtain ⟨a, b, c, ha, hb, hc, hf⟩ := forward nu h
  set q : Fin 3 → ℝ := ![(1 - |a|)/2, (1 - |b|)/2, (1 - |c|)/2] with hq
  have hq01 : ∀ i, 0 ≤ q i ∧ q i ≤ 1 / 2 := by
    have h1 := abs_le.2 ⟨ha.1, ha.2⟩
    have h2 := abs_le.2 ⟨hb.1, hb.2⟩
    have h3 := abs_le.2 ⟨hc.1, hc.2⟩
    intro i; fin_cases i <;> simp [hq] <;> constructor <;>
      linarith [abs_nonneg a, abs_nonneg b, abs_nonneg c]
  set mu := eventLaw xyzEvents q
  obtain ⟨m0, mx, my, mz⟩ := wht_xyz q
  have q1 : 1 - 2 * q 0 = |a| := by simp [hq]; ring
  have q2 : 1 - 2 * q 1 = |b| := by simp [hq]; ring
  have q3 : 1 - 2 * q 2 = |c| := by simp [hq]; ring
  rw [q2, q3] at mx; rw [q1, q3] at my; rw [q1, q2] at mz
  let t : PauliLabel 1 := (if a < 0 then labelX else 0) + (if b < 0 then labelY else 0) +
    (if c < 0 then labelZ else 0)
  refine ⟨t, mu, eventLaw_dist _ _ fun i => ⟨(hq01 i).1, by linarith [(hq01 i).2]⟩,
    ⟨3, xyzEvents, q, hq01, rfl⟩, ?_, ?_⟩
  · intro u
    rcases cases4 u with rfl | rfl | rfl | rfl
    · rw [m0]; norm_num
    · rw [mx]; positivity
    · rw [my]; positivity
    · rw [mz]; positivity
  · apply wht_inj
    intro u
    rw [shift_wht]
    simp only [t, omega_add_right, sgn_add, sg_ite]
    obtain ⟨fx, fy, fz⟩ := hf
    rcases cases4 u with rfl | rfl | rfl | rfl
    · rw [m0, wht_zero, hnu.2]; simp [SparsePauliNoise.symplecticPairing]
    · rw [mx, fx]; simp only [sg]
      simp [X_ne0, Y_ne0, Z_ne0, Y_neX, Z_neX, Z_neY, Y_neX.symm, Z_neX.symm, Z_neY.symm]
      split_ifs <;> simp_all [abs_of_neg, abs_of_nonneg, not_lt] <;> ring
    · rw [my, fy]; simp only [sg]
      simp [X_ne0, Y_ne0, Z_ne0, Y_neX, Z_neX, Z_neY, Y_neX.symm, Z_neX.symm, Z_neY.symm]
      split_ifs <;> simp_all [abs_of_neg, abs_of_nonneg, not_lt] <;> ring
    · rw [mz, fz]; simp only [sg]
      simp [X_ne0, Y_ne0, Z_ne0, Y_neX, Z_neX, Z_neY, Y_neX.symm, Z_neX.symm, Z_neY.symm]
      split_ifs <;> simp_all [abs_of_neg, abs_of_nonneg, not_lt] <;> ring

theorem criterion (nu : PauliLabel 1 → ℝ)
    (hnu : Learning.IsDistribution nu) :
    (HasIndependentEvents nu ↔ ∃ a b c : ℝ,
      a ∈ Set.Icc (-1) 1 ∧ b ∈ Set.Icc (-1) 1 ∧ c ∈ Set.Icc (-1) 1 ∧
      FourierFactors nu a b c) ∧
    (∀ a b c : ℝ, a ∈ Set.Icc (-1) 1 → b ∈ Set.Icc (-1) 1 →
      c ∈ Set.Icc (-1) 1 → FourierFactors nu a b c →
      nu = eventLaw xyzEvents (![(1-a)/2, (1-b)/2, (1-c)/2])) ∧
    (HasIndependentEvents nu →
      0 ≤ SparsePauliNoise.eigenvalueWHT nu labelX *
        SparsePauliNoise.eigenvalueWHT nu labelY *
        SparsePauliNoise.eigenvalueWHT nu labelZ ∧
      ∃ t : PauliLabel 1, ∃ mu : PauliLabel 1 → ℝ,
        Learning.IsDistribution mu ∧ HasSmallEvents mu ∧
        (∀ u, 0 ≤ SparsePauliNoise.eigenvalueWHT mu u) ∧
        nu = fun u => mu (u - t)) := by
  refine ⟨⟨forward nu, ?_⟩, fun a b c _ _ _ h => converse nu hnu a b c h,
    fun h => ⟨indep_nonneg nu h, part3 nu hnu h⟩⟩
  rintro ⟨a, b, c, ha, hb, hc, h⟩
  refine ⟨3, xyzEvents, ![(1-a)/2, (1-b)/2, (1-c)/2], fun i => ?_, converse nu hnu a b c h⟩
  fin_cases i <;> simp <;> constructor <;> linarith [ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]

end X6P39C

open X6P39C QAlgorithms QAlgorithms.Papers.Independent.Information100.P39 in
theorem solution (nu : PauliLabel 1 → ℝ)
    (hnu : Learning.IsDistribution nu) :
    (HasIndependentEvents nu ↔ ∃ a b c : ℝ,
      a ∈ Set.Icc (-1) 1 ∧ b ∈ Set.Icc (-1) 1 ∧ c ∈ Set.Icc (-1) 1 ∧
      FourierFactors nu a b c) ∧
    (∀ a b c : ℝ, a ∈ Set.Icc (-1) 1 → b ∈ Set.Icc (-1) 1 →
      c ∈ Set.Icc (-1) 1 → FourierFactors nu a b c →
      nu = eventLaw xyzEvents (![(1-a)/2, (1-b)/2, (1-c)/2])) ∧
    (HasIndependentEvents nu →
      0 ≤ SparsePauliNoise.eigenvalueWHT nu labelX *
        SparsePauliNoise.eigenvalueWHT nu labelY *
        SparsePauliNoise.eigenvalueWHT nu labelZ ∧
      ∃ t : PauliLabel 1, ∃ mu : PauliLabel 1 → ℝ,
        Learning.IsDistribution mu ∧ HasSmallEvents mu ∧
        (∀ u, 0 ≤ SparsePauliNoise.eigenvalueWHT mu u) ∧
        nu = fun u => mu (u - t)) :=
  criterion nu hnu
