-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P29.invariant_orbit_projector
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:48:53.824862+00:00
-- url     : https://prove2.me/submissions/4b1f555f-7de3-4230-b2e5-b8bf8565c718

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P29

namespace S108Q

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P29
open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt rectAct)
open QAlgorithms.Papers.Independent.Support21.P09 (groupLeftRegular)
open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

variable {G : Type} [Group G]

def rho {n : ℕ} (z : Fin (n + 1) → G) : Fin n → G :=
  fun i => (z (Fin.last n))⁻¹ * z i.castSucc

def emb {n : ℕ} (g : G) (k : Fin n → G) : Fin (n + 1) → G :=
  Fin.snoc (fun i => g * k i) g

lemma emb_last {n : ℕ} (g : G) (k : Fin n → G) : emb g k (Fin.last n) = g := by
  simp [emb]

lemma emb_cs {n : ℕ} (g : G) (k : Fin n → G) (i : Fin n) : emb g k i.castSucc = g * k i := by
  simp [emb]

lemma rho_emb {n : ℕ} (g : G) (k : Fin n → G) : rho (emb g k) = k := by
  funext i; simp [rho, emb_last, emb_cs]

lemma emb_rho {n : ℕ} (z : Fin (n + 1) → G) : emb (z (Fin.last n)) (rho z) = z := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [emb_last]
  · simp [emb_cs, rho]

def embEquiv (n : ℕ) : G × (Fin n → G) ≃ (Fin (n + 1) → G) where
  toFun p := emb p.1 p.2
  invFun z := (z (Fin.last n), rho z)
  left_inv p := by
    obtain ⟨g, k⟩ := p
    exact Prod.ext (emb_last g k) (rho_emb g k)
  right_inv z := emb_rho z

variable [Fintype G]

lemma cond_iff {n : ℕ} (z : Fin (n + 1) → G) (h : Fin n → G) :
    (∀ i : Fin n, z i.castSucc = z (Fin.last n) * h i) ↔ h = rho z := by
  constructor
  · intro H; funext i; simp [rho, H i]
  · rintro rfl i; simp [rho]

lemma M_apply {n : ℕ} (z : Fin (n + 1) → G) (h : Fin n → G) :
    invariantOrbitMap G n z h =
      if h = rho z then ((Real.sqrt (Fintype.card G : ℝ))⁻¹ : ℂ) else 0 := by
  unfold invariantOrbitMap
  by_cases H : h = rho z
  · rw [if_pos ((cond_iff z h).2 H), if_pos H]
  · rw [if_neg (fun h' => H ((cond_iff z h).1 h')), if_neg H]

lemma cst_conj : (starRingEnd ℂ) ((Real.sqrt (Fintype.card G : ℝ))⁻¹ : ℂ) =
    ((Real.sqrt (Fintype.card G : ℝ))⁻¹ : ℂ) := by
  simp

lemma cst_sq : ((Real.sqrt (Fintype.card G : ℝ))⁻¹ : ℂ) * ((Real.sqrt (Fintype.card G : ℝ))⁻¹ : ℂ)
    = ((Fintype.card G : ℂ))⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  push_cast; rfl

lemma card_ne : (Fintype.card G : ℂ) ≠ 0 := by
  exact_mod_cast (Fintype.card_pos (α := G)).ne'

lemma cst_mul_sqrt : ((Real.sqrt (Fintype.card G : ℝ))⁻¹ : ℂ) * (Real.sqrt (Fintype.card G : ℝ) : ℂ)
    = 1 := by
  apply inv_mul_cancel₀
  have : 0 < Real.sqrt (Fintype.card G : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast Fintype.card_pos (α := G))
  exact_mod_cast this.ne'

lemma star_ite_zero (p : Prop) [Decidable p] (a : ℂ) :
    star (if p then a else 0) = if p then star a else 0 := by
  split_ifs <;> simp

lemma part1 (n : ℕ) : (invariantOrbitMap G n)ᴴ * invariantOrbitMap G n = 1 := by
  ext h h'
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, M_apply]
  rw [← (embEquiv (G := G) n).sum_comp, Fintype.sum_prod_type]
  simp only [embEquiv, Equiv.coe_fn_mk, rho_emb]
  simp only [star_ite_zero, star_zero, ite_mul, zero_mul, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Matrix.one_apply]
  by_cases hh : h = h'
  · subst hh
    simp only [if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : star ((Real.sqrt (Fintype.card G : ℝ))⁻¹ : ℂ) = ((Real.sqrt (Fintype.card G : ℝ))⁻¹ : ℂ) :=
      cst_conj
    rw [this, cst_sq, mul_inv_cancel₀ card_ne]
  · simp [hh]

lemma act_reg {m : ℕ} (g : G) (ψ : EuclideanSpace ℂ (Fin m → G)) (z : Fin m → G) :
    (act (localTensorMatrix (fun _ : Fin m => groupLeftRegular g)) ψ) z = ψ (fun i => g⁻¹ * z i) := by
  simp only [act, PiLp.toLp_apply, Matrix.mulVec, dotProduct, localTensorMatrix, groupLeftRegular]
  rw [Finset.sum_eq_single (fun i => g⁻¹ * z i)]
  · rw [Finset.prod_eq_one]
    · simp
    · intro i _; simp
  · intro y _ hy
    have : ∃ i, ¬ (z i = g * y i) := by
      by_contra hc
      push_neg at hc
      apply hy
      funext i
      rw [hc i, ← mul_assoc, inv_mul_cancel, one_mul]
    obtain ⟨i, hi⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), zero_mul]
  · simp

lemma emb_one_rho {n : ℕ} (z : Fin (n + 1) → G) :
    emb 1 (rho z) = fun i => (z (Fin.last n))⁻¹ * z i := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [emb_last]
  · simp [emb_cs, rho]

lemma rho_smul {n : ℕ} (g : G) (z : Fin (n + 1) → G) :
    rho (fun i => g * z i) = rho z := by
  funext i; simp [rho, mul_inv_rev, mul_assoc]

lemma part2 {n : ℕ} (ψ : EuclideanSpace ℂ (Fin (n + 1) → G)) :
    RegularInvariant ψ ↔ ∃ φ : EuclideanSpace ℂ (Fin n → G), rectAct (invariantOrbitMap G n) φ = ψ := by
  constructor
  · intro hinv
    refine ⟨WithLp.toLp 2 (fun k => (Real.sqrt (Fintype.card G : ℝ) : ℂ) * ψ (emb 1 k)), ?_⟩
    ext z
    simp only [rectAct, PiLp.toLp_apply, Matrix.mulVec, dotProduct, M_apply, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← mul_assoc, cst_mul_sqrt, one_mul, emb_one_rho]
    have := congrArg (fun v : EuclideanSpace ℂ (Fin (n + 1) → G) => v z) (hinv (z (Fin.last n)))
    simp only [act_reg, inv_inv] at this
    exact this
  · rintro ⟨φ, rfl⟩ g
    ext z
    rw [act_reg]
    simp only [rectAct, PiLp.toLp_apply, Matrix.mulVec, dotProduct, M_apply, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, rho_smul]

lemma P_apply {n : ℕ} (z z' : Fin (n + 1) → G) :
    orbitProjector G n z z' = if rho z = rho z' then ((Fintype.card G : ℂ))⁻¹ else 0 := by
  unfold orbitProjector
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, M_apply, star_ite_zero, star_zero, ite_mul, zero_mul,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have : star ((Real.sqrt (Fintype.card G : ℝ))⁻¹ : ℂ) = ((Real.sqrt (Fintype.card G : ℝ))⁻¹ : ℂ) :=
    cst_conj
  rw [this, cst_sq]
  by_cases h : rho z = rho z'
  · simp [h]
  · simp [h, Ne.symm h]

lemma rho_inj {n : ℕ} (j : Fin (n + 1)) {x y : Fin (n + 1) → G} (hxy : rho x = rho y)
    (hj : x j = y j) : x = y := by
  have hl : x (Fin.last n) = y (Fin.last n) := by
    induction j using Fin.lastCases with
    | last => exact hj
    | cast j0 =>
      have := congrFun hxy j0
      simp only [rho] at this
      rw [hj] at this
      have := mul_right_cancel this
      simpa using this
  rw [← emb_rho x, ← emb_rho y, hl, hxy]

def ext' {n : ℕ} (j : Fin (n + 1)) (a : {i // i ∈ (Finset.univ.erase j)} → G) (t : G) :
    Fin (n + 1) → G :=
  fun i => if h : i = j then t else a ⟨i, by simp [h]⟩

lemma ext'_j {n : ℕ} (j : Fin (n + 1)) (a : {i // i ∈ (Finset.univ.erase j)} → G) (t : G) :
    ext' j a t j = t := by simp [ext']

lemma cond_iff2 {n : ℕ} (j : Fin (n + 1)) (a : {i // i ∈ (Finset.univ.erase j)} → G)
    (x : Fin (n + 1) → G) :
    (∀ i : {i // i ∈ (Finset.univ.erase j)}, x i.val = a i) ↔ x = ext' j a (x j) := by
  constructor
  · intro H
    funext i
    by_cases h : i = j
    · subst h; simp [ext']
    · simp only [ext', dif_neg h]; exact H ⟨i, by simp [h]⟩
  · intro H i
    have hi : i.val ≠ j := Finset.ne_of_mem_erase i.2
    rw [H]; simp only [ext', dif_neg hi]

lemma part5 {n : ℕ} (j : Fin (n + 1)) :
    dependentRegisterTrace (H := fun _ : Fin (n + 1) => G)
      (Finset.univ.erase j) (orbitProjector G n) = 1 := by
  ext a b
  unfold dependentRegisterTrace
  have hR : ∀ x y : Fin (n + 1) → G, (∀ i, i ∉ Finset.univ.erase j → x i = y i) ↔ x j = y j := by
    intro x y
    constructor
    · intro H; exact H j (by simp)
    · intro H i hi; simp at hi; subst hi; exact H
  simp only [hR, cond_iff2 j a, cond_iff2 j b]
  calc _ = ∑ x : RegisterConfig (fun _ : Fin (n + 1) => G),
        (if x = ext' j a (x j) then orbitProjector G n x (ext' j b (x j)) else 0) := by
        refine Finset.sum_congr (by ext; simp) ?_
        intro x _
        rw [Finset.sum_eq_single (ext' j b (x j))]
        · by_cases hx : x = ext' j a (x j)
          · rw [if_pos ⟨hx, by rw [ext'_j], by rw [ext'_j]⟩, if_pos hx]
          · rw [if_neg (fun h => hx h.1), if_neg hx]
        · intro y _ hy
          rw [if_neg]
          rintro ⟨_, h2, h3⟩
          apply hy
          rw [h3]
          exact h2
        · intro h; simp at h
    _ = ∑ x : RegisterConfig (fun _ : Fin (n + 1) => G), ∑ t : G,
        (if x = ext' j a t then orbitProjector G n (ext' j a t) (ext' j b t) else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_eq_single (x j)]
        · by_cases hx : x = ext' j a (x j)
          · rw [if_pos hx, if_pos hx, ← hx]
          · rw [if_neg hx, if_neg hx]
        · intro t _ ht
          rw [if_neg]
          intro h; apply ht; rw [h, ext'_j]
        · intro h; simp at h
    _ = ∑ t : G, orbitProjector G n (ext' j a t) (ext' j b t) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro t _
        rw [Finset.sum_ite_eq']
        simp
    _ = _ := ?_
  simp only [P_apply]
  rw [Matrix.one_apply]
  by_cases hab : a = b
  · subst hab
    simp only [if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ card_ne
  · rw [if_neg hab]
    apply Finset.sum_eq_zero
    intro t _
    rw [if_neg]
    intro h
    have he := rho_inj j h (by rw [ext'_j, ext'_j])
    apply hab
    funext i
    have hi : i.val ≠ j := Finset.ne_of_mem_erase i.2
    have := congrFun he i.val
    simp only [ext', dif_neg hi] at this
    exact this

end S108Q

section
open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P29
open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt rectAct)
open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution
    (G : Type) [Group G] [Fintype G] {n : ℕ} (hn : 1 ≤ n) :
    (invariantOrbitMap G n)ᴴ * invariantOrbitMap G n = 1 ∧
    (∀ ψ : EuclideanSpace ℂ (Fin (n + 1) → G),
      RegularInvariant ψ ↔ ∃ φ : EuclideanSpace ℂ (Fin n → G), rectAct (invariantOrbitMap G n) φ = ψ) ∧
    (orbitProjector G n)ᴴ = orbitProjector G n ∧
    orbitProjector G n * orbitProjector G n = orbitProjector G n ∧
    (∀ j : Fin (n + 1), dependentRegisterTrace (H := fun _ : Fin (n + 1) => G)
      (Finset.univ.erase j) (orbitProjector G n) = 1) := by
  have h1 := S108Q.part1 (G := G) n
  refine ⟨h1, S108Q.part2, ?_, ?_, S108Q.part5⟩
  · unfold orbitProjector
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  · unfold orbitProjector
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (invariantOrbitMap G n)ᴴ, h1, Matrix.one_mul]

end
