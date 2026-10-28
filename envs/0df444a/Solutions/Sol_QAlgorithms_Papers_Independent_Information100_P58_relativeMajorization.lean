-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P58.relativeMajorization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T19:07:07.449996+00:00
-- url     : https://prove2.me/submissions/77eb8a2d-58fc-4b65-a285-261e1c196db9

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58
namespace QAlgorithms.Papers.Independent.Information100.P58

open scoped BigOperators ComplexConjugate Matrix

noncomputable section

open Matrix
open scoped ComplexOrder

/-- coordinate factor -/
def p58rm_cc {d : ℕ} (ψ : EuclideanSpace ℂ (Fin d)) (b : Bool) : Option (Fin d) → ℂ
  | some a => if b then ψ a else 0
  | none => if b then 0 else 1

def p58rm_phi {n d : ℕ} (ψ : EuclideanSpace ℂ (Fin d)) (S : Finset (Fin n)) :
    Output n d → ℂ := fun y => ∏ i, p58rm_cc ψ (decide (i ∈ S)) (y i)

def p58rm_Phi {n d : ℕ} (ψ : EuclideanSpace ℂ (Fin d)) (S : Finset (Fin n)) :
    Operator (Output n d) := vecMulVec (p58rm_phi ψ S) (star (p58rm_phi ψ S))

def p58rm_P {n d : ℕ} (S : Finset (Fin n)) : Operator (Output n d) :=
  diagonal fun y => if support y = S then 1 else 0

lemma p58rm_normsq {d : ℕ} (ψ : EuclideanSpace ℂ (Fin d)) (hψ : ‖ψ‖ = 1) :
    ∑ a, star (ψ a) * ψ a = 1 := by
  have h := EuclideanSpace.norm_eq ψ
  rw [hψ] at h
  have h2 : ∑ a, ‖ψ a‖ ^ 2 = 1 := by
    have := congrArg (· ^ 2) h
    simp only [one_pow] at this
    rw [this, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  have : ∀ a, star (ψ a) * ψ a = ((‖ψ a‖ ^ 2 : ℝ) : ℂ) := by
    intro a
    rw [mul_comm]
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [this]
  rw [← Complex.ofReal_sum, h2]; simp

lemma p58rm_sum_finset_prod {n : ℕ} (f : Fin n → Bool → ℂ) :
    ∑ S : Finset (Fin n), ∏ i, f i (decide (i ∈ S)) = ∏ i, (f i true + f i false) := by
  rw [Finset.prod_add]
  simp only [Finset.powerset_univ]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← Finset.prod_mul_prod_compl S]
  congr 1
  · exact Finset.prod_congr rfl fun i hi => by simp [hi]
  · rw [Finset.compl_eq_univ_sdiff]
    exact Finset.prod_congr rfl fun i hi => by
      have : i ∉ S := by simpa using hi
      simp [this]

lemma p58rm_orth {n d : ℕ} (ψ : EuclideanSpace ℂ (Fin d)) (hψ : ‖ψ‖ = 1)
    (S S' : Finset (Fin n)) :
    ∑ y, star (p58rm_phi ψ S y) * p58rm_phi ψ S' y = if S = S' then 1 else 0 := by
  have hn := p58rm_normsq ψ hψ
  unfold p58rm_phi
  simp_rw [star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i u => star (p58rm_cc ψ (decide (i ∈ S)) u) *
    p58rm_cc ψ (decide (i ∈ S')) u)]
  have key : ∀ i, ∑ u, star (p58rm_cc ψ (decide (i ∈ S)) u) * p58rm_cc ψ (decide (i ∈ S')) u
      = if (i ∈ S ↔ i ∈ S') then 1 else 0 := by
    intro i
    rw [Fintype.sum_option]
    by_cases h1 : i ∈ S <;> by_cases h2 : i ∈ S' <;> simp [p58rm_cc, h1, h2] <;> exact hn
  simp_rw [key]
  split_ifs with h
  · subst h; simp
  · obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ S ↔ i ∈ S') := by
      by_contra hc; push Not at hc; exact h (Finset.ext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma p58rm_supp {n d : ℕ} (ψ : EuclideanSpace ℂ (Fin d)) (S : Finset (Fin n))
    (y : Output n d) (h : support y ≠ S) : p58rm_phi ψ S y = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, ¬ ((y i).isSome ↔ i ∈ S) := by
    by_contra hc; push Not at hc
    exact h (Finset.ext fun i => by simp [support, hc i])
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rcases hy : y i with _ | a <;> simp_all [p58rm_cc]

lemma p58rm_w {n : ℕ} (p : ℝ) (S : Finset (Fin n)) :
    ((patternWeight n p S : ℝ) : ℂ) = ∏ i, (if decide (i ∈ S) then ((1 - p : ℝ) : ℂ) else (p : ℂ)) := by
  rw [← Finset.prod_mul_prod_compl S]
  rw [Finset.prod_congr rfl (fun i (hi : i ∈ S) => by simp [hi] : ∀ i ∈ S,
      (if decide (i ∈ S) then ((1 - p : ℝ) : ℂ) else (p : ℂ)) = ((1 - p : ℝ) : ℂ))]
  rw [Finset.prod_congr rfl (fun i (hi : i ∈ Sᶜ) => by
      have : i ∉ S := by simpa using hi
      simp [this] : ∀ i ∈ Sᶜ,
      (if decide (i ∈ S) then ((1 - p : ℝ) : ℂ) else (p : ℂ)) = (p : ℂ))]
  simp [patternWeight, Finset.card_compl]

lemma p58rm_H {d : ℕ} (p : ℝ) (ψ : EuclideanSpace ℂ (Fin d)) (hψ : ‖ψ‖ = 1)
    (u u' : Option (Fin d)) :
    ∑ a, ∑ b, ψ a * conj (ψ b) * singleErasure d p (Matrix.single a b 1) u u' =
      ((1 - p : ℝ) : ℂ) * p58rm_cc ψ true u *
          star (p58rm_cc ψ true u') +
        (p : ℂ) * p58rm_cc ψ false u *
          star (p58rm_cc ψ false u') := by
  have hn := p58rm_normsq ψ hψ
  rcases u with _ | i <;> rcases u' with _ | j
  · have htr : ∀ a b : Fin d, (Matrix.single a b (1:ℂ)).trace = if a = b then 1 else 0 := by
      intro a b
      split_ifs with h
      · subst h; exact Matrix.trace_single_eq_same _ _
      · exact Matrix.trace_single_eq_of_ne _ _ _ h
    simp only [singleErasure, p58rm_cc, htr]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have : ∑ a, ψ a * conj (ψ a) * (p : ℂ) = (p : ℂ) := by
      rw [← Finset.sum_mul]
      have : ∑ a, ψ a * conj (ψ a) = 1 := by
        rw [← hn]; exact Finset.sum_congr rfl fun a _ => mul_comm _ _
      rw [this, one_mul]
    simpa using this
  · simp [singleErasure, p58rm_cc]
  · simp [singleErasure, p58rm_cc]
  · simp [singleErasure, p58rm_cc, Matrix.single_apply]
    simp_rw [ite_and]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring

lemma p58rm_ref {n d : ℕ} (p : ℝ) (ψ : EuclideanSpace ℂ (Fin d)) (hψ : ‖ψ‖ = 1) :
    reference n d p ψ = ∑ S, ((patternWeight n p S : ℝ) : ℂ) • p58rm_Phi ψ S := by
  ext y y'
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, p58rm_Phi, vecMulVec_apply, Pi.star_apply, smul_eq_mul,
    p58rm_phi, p58rm_w]
  have hR : ∑ S : Finset (Fin n), (∏ i, (if decide (i ∈ S) then ((1 - p : ℝ) : ℂ) else (p : ℂ))) *
      ((∏ i, p58rm_cc ψ (decide (i ∈ S)) (y i)) *
        star (∏ i, p58rm_cc ψ (decide (i ∈ S)) (y' i))) =
      ∏ i, (((1 - p : ℝ) : ℂ) * p58rm_cc ψ true (y i) *
          star (p58rm_cc ψ true (y' i)) +
        (p : ℂ) * p58rm_cc ψ false (y i) *
          star (p58rm_cc ψ false (y' i))) := by
    refine (Finset.sum_congr rfl fun S _ => ?_).trans
      ((p58rm_sum_finset_prod (fun i b => (if b then ((1 - p : ℝ) : ℂ) else (p : ℂ)) *
      p58rm_cc ψ b (y i) * star (p58rm_cc ψ b (y' i)))).trans ?_)
    swap
    · simp
    rw [star_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases h : i ∈ S <;> simp [h, mul_assoc]
  rw [hR]
  simp_rw [← p58rm_H p ψ hψ]
  unfold reference erasure piSuperop pureDensity tensorPow
  simp only [Matrix.of_apply]
  symm
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [map_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

section mats
variable {n d : ℕ} (ψ : EuclideanSpace ℂ (Fin d)) (hψ : ‖ψ‖ = 1)
include hψ

lemma p58rm_PhiPhi (S' S : Finset (Fin n)) :
    p58rm_Phi ψ S' * p58rm_Phi ψ S = if S' = S then p58rm_Phi ψ S else 0 := by
  unfold p58rm_Phi
  rw [vecMulVec_mul_vecMulVec]
  have : star (p58rm_phi ψ S') ⬝ᵥ p58rm_phi ψ S = if S' = S then 1 else 0 := by
    rw [← p58rm_orth ψ hψ S' S]; rfl
  rw [this]
  split_ifs with h
  · subst h; simp
  · ext i j; simp [vecMulVec_apply]

omit hψ in
lemma p58rm_PhiP (S' S : Finset (Fin n)) :
    p58rm_Phi ψ S' * p58rm_P S = if S' = S then p58rm_Phi ψ S else 0 := by
  unfold p58rm_Phi p58rm_P
  ext y y'
  rw [mul_diagonal]
  by_cases h : S' = S
  · subst h
    rw [if_pos rfl]
    by_cases hy : support y' = S'
    · simp [hy]
    · simp [hy, vecMulVec_apply, p58rm_supp ψ S' y' hy]
  · rw [if_neg h]
    by_cases hy : support y' = S
    · have : support y' ≠ S' := fun h' => h (h'.symm.trans hy)
      simp [hy, vecMulVec_apply, p58rm_supp ψ S' y' this]
    · simp [hy]

omit hψ in
lemma p58rm_PPhi (S : Finset (Fin n)) :
    p58rm_P S * p58rm_Phi ψ S = p58rm_Phi ψ S := by
  unfold p58rm_Phi p58rm_P
  ext y y'
  rw [diagonal_mul]
  by_cases hy : support y = S
  · simp [hy]
  · simp [hy, vecMulVec_apply, p58rm_supp ψ S y hy]

omit hψ in
lemma p58rm_PP (S : Finset (Fin n)) :
    (p58rm_P S : Operator (Output n d)) * p58rm_P S = p58rm_P S := by
  unfold p58rm_P
  rw [diagonal_mul_diagonal]
  congr 1; ext y; split_ifs <;> simp

omit hψ in
lemma p58rm_sumP : ∑ S : Finset (Fin n), (p58rm_P S : Operator (Output n d)) = 1 := by
  unfold p58rm_P
  ext y y'
  rw [Matrix.sum_apply]
  by_cases h : y = y'
  · subst h; simp
  · simp [h]

lemma p58rm_trPhi (S : Finset (Fin n)) : (p58rm_Phi ψ S).trace = 1 := by
  unfold p58rm_Phi
  rw [trace_vecMulVec]
  have := p58rm_orth ψ hψ S S
  simp only [if_true] at this
  rw [← this, dotProduct]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

omit hψ in
lemma p58rm_PhiH (S : Finset (Fin n)) : (p58rm_Phi ψ S)ᴴ = p58rm_Phi ψ S :=
  (posSemidef_vecMulVec_self_star _).1

omit hψ in
lemma p58rm_PH (S : Finset (Fin n)) : (p58rm_P S : Operator (Output n d))ᴴ = p58rm_P S := by
  unfold p58rm_P
  rw [diagonal_conjTranspose]
  congr 1; ext y; simp only [Pi.star_apply]; split_ifs <;> simp

lemma p58rm_PhiProj (S : Finset (Fin n)) :
    (p58rm_Phi ψ S)ᴴ * p58rm_Phi ψ S = p58rm_Phi ψ S := by
  rw [p58rm_PhiH, p58rm_PhiPhi ψ hψ]; simp

lemma p58rm_QProj (S : Finset (Fin n)) :
    (p58rm_P S - p58rm_Phi ψ S)ᴴ * (p58rm_P S - p58rm_Phi ψ S) =
      p58rm_P S - p58rm_Phi ψ S := by
  rw [conjTranspose_sub, p58rm_PhiH, p58rm_PH, sub_mul, mul_sub, mul_sub, p58rm_PP,
    p58rm_PPhi, p58rm_PhiP, p58rm_PhiPhi ψ hψ]
  simp

end mats

lemma p58rm_aux {n d : ℕ} (q : Finset (Fin n) → ℝ) :
    auxiliary n d q = ∑ S, (((q S / (d:ℝ)^S.card : ℝ)) : ℂ) • (p58rm_P S : Operator (Output n d)) := by
  ext y y'
  rw [Matrix.sum_apply]
  unfold auxiliary p58rm_P
  by_cases h : y = y'
  · subst h; simp [diagonal_apply]
  · simp [diagonal_apply, h]



/-! ## sector-wise partial traces -/

def p58rm_kk {d : ℕ} (o : Fin d) (b : Bool) (u : Option (Fin d)) (a z : Fin d) : ℂ :=
  if b then (if u = some a ∧ z = o then 1 else 0) else (if u = none ∧ a = z then 1 else 0)

def p58rm_K {n d : ℕ} (o : Fin d) (S : Finset (Fin n)) (z : Word n d) :
    Matrix (Output n d) (Word n d) ℂ :=
  Matrix.of fun y x => ∏ i, p58rm_kk o (decide (i ∈ S)) (y i) (x i) (z i)

def p58rm_sig {n d : ℕ} (o : Fin d) (S : Finset (Fin n)) (ρ : Operator (Word n d)) :
    Operator (Output n d) :=
  ∑ z, p58rm_K o S z * ρ * (p58rm_K o S z)ᴴ

lemma p58rm_star_kk {d : ℕ} (o : Fin d) (b : Bool) (u : Option (Fin d)) (a z : Fin d) :
    star (p58rm_kk o b u a z) = p58rm_kk o b u a z := by
  unfold p58rm_kk; split_ifs <;> simp

lemma p58rm_kk_sum {d : ℕ} (o : Fin d) (b : Bool) (a a' : Fin d) :
    ∑ z, ∑ u, p58rm_kk o b u a z * p58rm_kk o b u a' z = if a = a' then 1 else 0 := by
  cases b
  · simp only [p58rm_kk, Bool.false_eq_true, if_false, Fintype.sum_option]
    simp only [reduceCtorEq, false_and, if_false, mul_zero, Finset.sum_const_zero, add_zero, true_and]
    simp only [mul_ite, mul_one, mul_zero]
    by_cases h : a = a'
    · subst h; simp
    · simp [h]
      try (intros; simp_all [eq_comm])
  · simp only [p58rm_kk, if_true, Fintype.sum_option]
    simp only [reduceCtorEq, false_and, if_false, mul_zero, zero_add, Option.some.injEq]
    by_cases h : a = a'
    · subst h
      simp [ite_and]
    · simp [ite_and, h]
      try (intros; simp_all [eq_comm])

lemma p58rm_KK {n d : ℕ} (o : Fin d) (S : Finset (Fin n)) :
    ∑ z, (p58rm_K o S z)ᴴ * p58rm_K o S z = 1 := by
  ext x x'
  rw [Matrix.sum_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, p58rm_K, Matrix.of_apply, star_prod,
    p58rm_star_kk, ← Finset.prod_mul_distrib]
  have h1 : ∀ z : Word n d, ∑ y : Output n d, ∏ i, p58rm_kk o (decide (i ∈ S)) (y i) (x i) (z i) *
      p58rm_kk o (decide (i ∈ S)) (y i) (x' i) (z i) =
      ∏ i, ∑ u, p58rm_kk o (decide (i ∈ S)) u (x i) (z i) * p58rm_kk o (decide (i ∈ S)) u (x' i) (z i) := by
    intro z
    rw [Fintype.prod_sum]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun i a => ∑ u, p58rm_kk o (decide (i ∈ S)) u (x i) a *
    p58rm_kk o (decide (i ∈ S)) u (x' i) a)]
  simp_rw [p58rm_kk_sum, Matrix.one_apply]
  split_ifs with h
  · subst h; simp
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ x' i := by
      by_contra hc; push Not at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma p58rm_sig_psd {n d : ℕ} (o : Fin d) (S : Finset (Fin n)) (ρ : Operator (Word n d))
    (hρ : ρ.PosSemidef) : (p58rm_sig o S ρ).PosSemidef :=
  posSemidef_sum _ fun z _ => hρ.mul_mul_conjTranspose_same _

lemma p58rm_sig_tr {n d : ℕ} (o : Fin d) (S : Finset (Fin n)) (ρ : Operator (Word n d)) :
    (p58rm_sig o S ρ).trace = ρ.trace := by
  unfold p58rm_sig
  rw [trace_sum]
  simp_rw [fun z => Matrix.trace_mul_comm (p58rm_K o S z * ρ) (p58rm_K o S z)ᴴ, ← Matrix.mul_assoc]
  rw [← trace_sum, ← Finset.sum_mul, p58rm_KK, Matrix.one_mul]

lemma p58rm_PK {n d : ℕ} (o : Fin d) (S : Finset (Fin n)) (z : Word n d) :
    (p58rm_P S : Matrix (Output n d) (Output n d) ℂ) * p58rm_K o S z = p58rm_K o S z := by
  ext y x
  rw [p58rm_P, diagonal_mul]
  by_cases hy : support y = S
  · simp [hy]
  · rw [if_neg hy, zero_mul]
    obtain ⟨i, hi⟩ : ∃ i, ¬ ((y i).isSome ↔ i ∈ S) := by
      by_contra hc; push Not at hc
      exact hy (Finset.ext fun i => by simp [support, hc i])
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rcases hyi : y i with _ | a <;> by_cases hS : i ∈ S <;> simp_all [p58rm_kk]

lemma p58rm_Psig {n d : ℕ} (o : Fin d) (S : Finset (Fin n)) (ρ : Operator (Word n d)) :
    (p58rm_P S : Matrix (Output n d) (Output n d) ℂ) * p58rm_sig o S ρ = p58rm_sig o S ρ := by
  unfold p58rm_sig
  rw [Matrix.mul_sum]
  simp_rw [← Matrix.mul_assoc, p58rm_PK]

lemma p58rm_sigP {n d : ℕ} (o : Fin d) (S : Finset (Fin n)) (ρ : Operator (Word n d)) :
    p58rm_sig o S ρ * (p58rm_P S : Matrix (Output n d) (Output n d) ℂ) = p58rm_sig o S ρ := by
  unfold p58rm_sig
  rw [Matrix.sum_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Matrix.mul_assoc, ← p58rm_PH S, ← conjTranspose_mul, p58rm_PK]

lemma p58rm_conj_apply {A B : Type*} [Fintype A] [Fintype B] (K : Matrix B A ℂ) (ρ : Matrix A A ℂ)
    (y y' : B) : (K * ρ * Kᴴ) y y' = ∑ x, ∑ x', ρ x x' * (K y x * star (K y' x')) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => by ring

lemma p58rm_coord {d : ℕ} (o : Fin d) (p : ℝ) (u u' : Option (Fin d)) (a a' : Fin d) :
    ((1 - p : ℝ) : ℂ) * ∑ z, p58rm_kk o true u a z * p58rm_kk o true u' a' z +
      (p : ℂ) * ∑ z, p58rm_kk o false u a z * p58rm_kk o false u' a' z =
    singleErasure d p (Matrix.single a a' 1) u u' := by
  rcases u with _ | i <;> rcases u' with _ | j
  · simp only [p58rm_kk, singleErasure, if_true, Bool.false_eq_true, if_false]
    simp [ite_and]
    by_cases h : a = a'
    · subst h; simp [Matrix.trace_single_eq_same]
    · rw [Matrix.trace_single_eq_of_ne _ _ _ h]
      simp
      try (intros; simp_all [eq_comm])
  · simp [p58rm_kk, singleErasure]
  · simp [p58rm_kk, singleErasure]
  · simp only [p58rm_kk, singleErasure, if_true, Bool.false_eq_true, if_false]
    simp [ite_and, Matrix.single_apply]
    by_cases h1 : a = i <;> by_cases h2 : a' = j <;> simp [h1, h2, eq_comm]

lemma p58rm_key {n d : ℕ} (o : Fin d) (p : ℝ) (y y' : Output n d) (x x' : Word n d) :
    ∑ S : Finset (Fin n), ((patternWeight n p S : ℝ) : ℂ) *
      ∑ z : Word n d, (∏ i, p58rm_kk o (decide (i ∈ S)) (y i) (x i) (z i)) *
        (∏ i, p58rm_kk o (decide (i ∈ S)) (y' i) (x' i) (z i)) =
    ∏ i, singleErasure d p (Matrix.single (x i) (x' i) 1) (y i) (y' i) := by
  have h1 : ∀ S : Finset (Fin n), ((patternWeight n p S : ℝ) : ℂ) *
      ∑ z : Word n d, (∏ i, p58rm_kk o (decide (i ∈ S)) (y i) (x i) (z i)) *
        (∏ i, p58rm_kk o (decide (i ∈ S)) (y' i) (x' i) (z i)) =
      ∏ i, ((if decide (i ∈ S) then ((1 - p : ℝ) : ℂ) else (p : ℂ)) *
        ∑ c, p58rm_kk o (decide (i ∈ S)) (y i) (x i) c *
          p58rm_kk o (decide (i ∈ S)) (y' i) (x' i) c) := by
    intro S
    simp_rw [← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun i c => p58rm_kk o (decide (i ∈ S)) (y i) (x i) c *
      p58rm_kk o (decide (i ∈ S)) (y' i) (x' i) c), p58rm_w, ← Finset.prod_mul_distrib]
  simp_rw [h1]
  rw [p58rm_sum_finset_prod (fun i b => (if b then ((1 - p : ℝ) : ℂ) else (p : ℂ)) *
      ∑ c, p58rm_kk o b (y i) (x i) c * p58rm_kk o b (y' i) (x' i) c)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← p58rm_coord o p]
  simp

lemma p58rm_erasure {n d : ℕ} (o : Fin d) (p : ℝ) (ρ : Operator (Word n d)) :
    erasure n d p ρ = ∑ S, ((patternWeight n p S : ℝ) : ℂ) • p58rm_sig o S ρ := by
  ext y y'
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, p58rm_sig, Matrix.sum_apply, p58rm_conj_apply,
    p58rm_K, Matrix.of_apply, star_prod, p58rm_star_kk]
  unfold erasure piSuperop
  simp only [Matrix.of_apply]
  simp_rw [← p58rm_key o p y y', Finset.mul_sum]
  symm
  calc _ = ∑ S : Finset (Fin n), ∑ x : Word n d, ∑ z : Word n d, ∑ x' : Word n d,
        ((patternWeight n p S : ℝ) : ℂ) * (ρ x x' *
          ((∏ i, p58rm_kk o (decide (i ∈ S)) (y i) (x i) (z i)) *
            ∏ i, p58rm_kk o (decide (i ∈ S)) (y' i) (x' i) (z i))) :=
        Finset.sum_congr rfl fun S _ => Finset.sum_comm
    _ = ∑ S : Finset (Fin n), ∑ x : Word n d, ∑ x' : Word n d, ∑ z : Word n d,
        ((patternWeight n p S : ℝ) : ℂ) * (ρ x x' *
          ((∏ i, p58rm_kk o (decide (i ∈ S)) (y i) (x i) (z i)) *
            ∏ i, p58rm_kk o (decide (i ∈ S)) (y' i) (x' i) (z i))) :=
        Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x : Word n d, ∑ S : Finset (Fin n), ∑ x' : Word n d, ∑ z : Word n d,
        ((patternWeight n p S : ℝ) : ℂ) * (ρ x x' *
          ((∏ i, p58rm_kk o (decide (i ∈ S)) (y i) (x i) (z i)) *
            ∏ i, p58rm_kk o (decide (i ∈ S)) (y' i) (x' i) (z i))) := Finset.sum_comm
    _ = ∑ x : Word n d, ∑ x' : Word n d, ∑ S : Finset (Fin n), ∑ z : Word n d,
        ((patternWeight n p S : ℝ) : ℂ) * (ρ x x' *
          ((∏ i, p58rm_kk o (decide (i ∈ S)) (y i) (x i) (z i)) *
            ∏ i, p58rm_kk o (decide (i ∈ S)) (y' i) (x' i) (z i))) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
      refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun z _ => ?_
      ring


/-! ## operator inequalities -/

lemma p58rm_tr_sub_psd {A : Type*} [Fintype A] [DecidableEq A] (σ : Matrix A A ℂ)
    (hσ : σ.PosSemidef) : (σ.trace • (1 : Matrix A A ℂ) - σ).PosSemidef := by
  set U := hσ.1.eigenvectorUnitary
  have hs := hσ.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  set lam := hσ.1.eigenvalues
  have htr := hσ.1.trace_eq_sum_eigenvalues
  have hUU : (U : Matrix A A ℂ) * star (U : Matrix A A ℂ) = 1 := Unitary.mul_star_self_of_mem U.2
  have key : σ.trace • (1 : Matrix A A ℂ) - σ =
      (U : Matrix A A ℂ) * diagonal (fun i => ((∑ j, lam j - lam i : ℝ) : ℂ)) * star (U : Matrix A A ℂ) := by
    have : diagonal (fun i => ((∑ j, lam j - lam i : ℝ) : ℂ)) =
        σ.trace • (1 : Matrix A A ℂ) - diagonal (RCLike.ofReal ∘ lam) := by
      ext a b
      by_cases h : a = b
      · subst h; simp [htr, diagonal_apply]; rfl
      · simp [diagonal_apply, h]
    rw [this, Matrix.mul_sub, Matrix.sub_mul, ← hs, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      hUU]
  rw [key, Matrix.star_eq_conjTranspose]
  apply PosSemidef.mul_mul_conjTranspose_same
  apply PosSemidef.diagonal
  intro i
  simp only [Pi.zero_apply]
  apply Complex.zero_le_real.mpr
  have : lam i ≤ ∑ j, lam j :=
    Finset.single_le_sum (fun j _ => hσ.eigenvalues_nonneg j) (Finset.mem_univ i)
  linarith

lemma p58rm_proj_sub_psd {A : Type*} [Fintype A] [DecidableEq A] (P σ : Matrix A A ℂ)
    (hPH : Pᴴ = P) (hPP : P * P = P) (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    (h1 : P * σ = σ) (h2 : σ * P = σ) : (P - σ).PosSemidef := by
  have := (p58rm_tr_sub_psd σ hσ).mul_mul_conjTranspose_same P
  rw [htr, one_smul, hPH, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPP, h1, h2] at this
  exact this

/-! ## measure-and-prepare channels -/

lemma p58rm_vv_conj {ι κ : Type*} [Fintype ι] (w : κ → ℂ) (u : ι → ℂ) (X : Matrix ι ι ℂ) :
    vecMulVec w u * X * (vecMulVec w u)ᴴ = (u ⬝ᵥ (X *ᵥ star u)) • vecMulVec w (star w) := by
  ext a a'
  simp only [Matrix.mul_apply, vecMulVec_apply, conjTranspose_apply, Matrix.smul_apply, smul_eq_mul,
    dotProduct, mulVec, Pi.star_apply, star_mul', Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => by ring

lemma p58rm_vv_norm {ι κ : Type*} [Fintype κ] (w : κ → ℂ) (u : ι → ℂ) :
    (vecMulVec w u)ᴴ * vecMulVec w u = (star w ⬝ᵥ w) • vecMulVec (star u) u := by
  ext b b'
  simp only [Matrix.mul_apply, vecMulVec_apply, conjTranspose_apply, Matrix.smul_apply, smul_eq_mul,
    dotProduct, Pi.star_apply, star_mul', Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => by ring

lemma p58rm_tr_rows {ι : Type*} [Fintype ι] (A X : Matrix ι ι ℂ) :
    ∑ y, A y ⬝ᵥ (X *ᵥ star (A y)) = (A * X * Aᴴ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, dotProduct, mulVec,
    Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => by ring

lemma p58rm_rows_norm {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) :
    ∑ y, vecMulVec (star (A y)) (A y) = Aᴴ * A := by
  ext b b'
  simp [Matrix.sum_apply, vecMulVec_apply, Matrix.mul_apply, conjTranspose_apply]

lemma p58rm_mp_channel {ι κ I : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype I] (A : I → Matrix ι ι ℂ) (σ : I → Matrix κ κ ℂ) (hσ : ∀ i, (σ i).PosSemidef)
    (hnorm : ∑ i, (σ i).trace • ((A i)ᴴ * A i) = 1) :
    IsChannel (fun X : Matrix ι ι ℂ => ∑ i, (A i * X * (A i)ᴴ).trace • σ i) := by
  classical
  choose m v hv using fun i => Matrix.posSemidef_iff_eq_sum_vecMulVec.mp (hσ i)
  let T := Σ i : I, Fin (m i) × ι
  let E : T → Matrix κ ι ℂ := fun t => vecMulVec (v t.1 t.2.1) ((A t.1) t.2.2)
  have hE1 : ∑ t, (E t)ᴴ * E t = 1 := by
    rw [← hnorm, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    simp only [E, p58rm_vv_norm]
    simp_rw [← Finset.smul_sum, p58rm_rows_norm, ← Finset.sum_smul]
    congr 1
    rw [hv i, trace_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [trace_vecMulVec, dotProduct_comm]
  have hE2 : ∀ X, ∑ i, (A i * X * (A i)ᴴ).trace • σ i = ∑ t, E t * X * (E t)ᴴ := by
    intro X
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    simp only [E, p58rm_vv_conj]
    simp_rw [← Finset.sum_smul, p58rm_tr_rows, ← Finset.smul_sum, hv i]
  let e := Fintype.equivFin T
  refine ⟨Fintype.card T, fun k => E (e.symm k), ?_, fun X => ?_⟩
  · unfold IsKrausFamily
    rw [Equiv.sum_comp e.symm (fun t => (E t)ᴴ * E t)]
    exact hE1
  · unfold krausApply
    rw [Equiv.sum_comp e.symm (fun t => E t * X * (E t)ᴴ)]
    exact hE2 X


/-! ## assembly -/

section asm
variable {n d : ℕ} (ψ : EuclideanSpace ℂ (Fin d)) (o : Fin d) (ρ : Operator (Word n d))

def p58rm_Q (S : Finset (Fin n)) : Operator (Output n d) := p58rm_P S - p58rm_Phi ψ S

def p58rm_tau (S : Finset (Fin n)) : Operator (Output n d) :=
  ((p58rm_Q ψ S).trace)⁻¹ • (p58rm_P S - p58rm_sig o S ρ)

def p58rm_A (i : Finset (Fin n) × Bool) : Operator (Output n d) :=
  if i.2 then p58rm_Phi ψ i.1 else p58rm_Q ψ i.1

def p58rm_S (i : Finset (Fin n) × Bool) : Operator (Output n d) :=
  if i.2 then p58rm_sig o i.1 ρ else p58rm_tau ψ o ρ i.1

def p58rm_chan : Superop (Output n d) (Output n d) :=
  fun X => ∑ i, (p58rm_A ψ i * X * (p58rm_A ψ i)ᴴ).trace • p58rm_S ψ o ρ i

lemma p58rm_QH (S : Finset (Fin n)) : (p58rm_Q ψ S)ᴴ = p58rm_Q ψ S := by
  unfold p58rm_Q; rw [conjTranspose_sub, p58rm_PhiH, p58rm_PH]

variable {ψ} (hψ : ‖ψ‖ = 1)
include hψ

lemma p58rm_QQ (S : Finset (Fin n)) : p58rm_Q ψ S * p58rm_Q ψ S = p58rm_Q ψ S := by
  have := p58rm_QProj ψ hψ S
  rwa [← p58rm_Q, p58rm_QH] at this

lemma p58rm_trQ_nonneg (S : Finset (Fin n)) : 0 ≤ (p58rm_Q ψ S).trace := by
  have := p58rm_QProj ψ hψ S
  rw [← p58rm_Q] at this
  rw [← this]
  exact (posSemidef_conjTranspose_mul_self _).trace_nonneg

lemma p58rm_Q_zero (S : Finset (Fin n)) (h : (p58rm_Q ψ S).trace = 0) : p58rm_Q ψ S = 0 := by
  have := p58rm_QProj ψ hψ S
  rw [← p58rm_Q] at this
  rw [← this] at h
  exact trace_conjTranspose_mul_self_eq_zero_iff.mp h

omit hψ in
lemma p58rm_PP' (S S' : Finset (Fin n)) :
    (p58rm_P S : Operator (Output n d)) * p58rm_P S' = if S = S' then p58rm_P S else 0 := by
  unfold p58rm_P
  rw [diagonal_mul_diagonal]
  split_ifs with h
  · subst h; congr 1; ext y; split_ifs <;> simp
  · rw [← diagonal_zero]; congr 1; ext y
    by_cases h1 : support y = S
    · have : support y ≠ S' := fun h2 => h (h1.symm.trans h2)
      simp [h1, this, h]
    · simp [h1]

omit hψ in
lemma p58rm_PPhi' (S S' : Finset (Fin n)) :
    (p58rm_P S : Operator (Output n d)) * p58rm_Phi ψ S' = if S = S' then p58rm_Phi ψ S else 0 := by
  have := congrArg conjTranspose (p58rm_PhiP ψ S' S)
  rw [conjTranspose_mul, p58rm_PhiH, p58rm_PH] at this
  rw [this]
  split_ifs with h1 h2 h2
  · rw [p58rm_PhiH]
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp

lemma p58rm_QPhi (S S' : Finset (Fin n)) : p58rm_Q ψ S * p58rm_Phi ψ S' = 0 := by
  unfold p58rm_Q
  rw [Matrix.sub_mul, p58rm_PPhi', p58rm_PhiPhi ψ hψ]
  split_ifs with h
  · subst h; simp
  · simp

omit hψ in
lemma p58rm_QP (S S' : Finset (Fin n)) :
    p58rm_Q ψ S * p58rm_P S' = if S = S' then p58rm_Q ψ S else 0 := by
  unfold p58rm_Q
  rw [Matrix.sub_mul, p58rm_PP', p58rm_PhiP]
  split_ifs with h
  · subst h; rfl
  · simp

omit hψ in
lemma p58rm_chan_eq (X : Operator (Output n d)) : p58rm_chan ψ o ρ X =
    ∑ S, ((p58rm_Phi ψ S * X * p58rm_Phi ψ S).trace • p58rm_sig o S ρ +
      (p58rm_Q ψ S * X * p58rm_Q ψ S).trace • p58rm_tau ψ o ρ S) := by
  unfold p58rm_chan
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Fintype.sum_bool]
  simp [p58rm_A, p58rm_S, p58rm_PhiH, p58rm_QH]

lemma p58rm_chan_ref (p : ℝ) : p58rm_chan ψ o ρ (reference n d p ψ) = erasure n d p ρ := by
  rw [p58rm_chan_eq (ψ := ψ) o ρ, p58rm_erasure o]
  refine Finset.sum_congr rfl fun S _ => ?_
  have h1 : (p58rm_Phi ψ S * reference n d p ψ * p58rm_Phi ψ S).trace = ((patternWeight n p S : ℝ) : ℂ) := by
    rw [p58rm_ref p ψ hψ, Matrix.mul_sum, Matrix.sum_mul, trace_sum]
    simp_rw [Matrix.mul_smul, Matrix.smul_mul, p58rm_PhiPhi ψ hψ, trace_smul]
    simp only [ite_mul, zero_mul, p58rm_PhiPhi ψ hψ]
    rw [Finset.sum_eq_single S (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp [p58rm_trPhi ψ hψ]
  have h2 : (p58rm_Q ψ S * reference n d p ψ * p58rm_Q ψ S).trace = 0 := by
    rw [p58rm_ref p ψ hψ, Matrix.mul_sum, Matrix.sum_mul, trace_sum]
    simp_rw [Matrix.mul_smul, Matrix.smul_mul, p58rm_QPhi hψ]
    simp
  rw [h1, h2, zero_smul, add_zero]


variable (hρ : IsDensityMatrix ρ)
include hρ

lemma p58rm_sig_tau (S : Finset (Fin n)) :
    p58rm_sig o S ρ + (p58rm_Q ψ S).trace • p58rm_tau ψ o ρ S = p58rm_P S := by
  by_cases h : (p58rm_Q ψ S).trace = 0
  · have hQ := p58rm_Q_zero hψ S h
    have hPΦ : (p58rm_P S : Operator (Output n d)) = p58rm_Phi ψ S := by
      have := hQ; unfold p58rm_Q at this; exact sub_eq_zero.mp this
    rw [h, zero_smul, add_zero]
    have hs : p58rm_sig o S ρ = p58rm_Phi ψ S * p58rm_sig o S ρ * (p58rm_Phi ψ S)ᴴ := by
      rw [p58rm_PhiH, ← hPΦ, p58rm_Psig, p58rm_sigP]
    have hc := hs
    rw [p58rm_Phi, p58rm_vv_conj] at hc
    rw [← p58rm_Phi] at hc
    have htr := congrArg Matrix.trace hc
    rw [trace_smul, p58rm_trPhi ψ hψ, p58rm_sig_tr, hρ.2, smul_eq_mul, mul_one] at htr
    rw [hc, ← htr, one_smul, hPΦ]
  · unfold p58rm_tau
    rw [smul_smul, mul_inv_cancel₀ h, one_smul]
    abel

lemma p58rm_chan_aux (q : Finset (Fin n) → ℝ) :
    p58rm_chan ψ o ρ (auxiliary n d q) = auxiliary n d q := by
  rw [p58rm_chan_eq (ψ := ψ) o ρ]
  conv_rhs => rw [p58rm_aux q]
  refine Finset.sum_congr rfl fun S _ => ?_
  have h1 : (p58rm_Phi ψ S * auxiliary n d q * p58rm_Phi ψ S).trace =
      (((q S / (d:ℝ)^S.card : ℝ)) : ℂ) := by
    rw [p58rm_aux q, Matrix.mul_sum, Matrix.sum_mul, trace_sum]
    simp_rw [Matrix.mul_smul, Matrix.smul_mul, p58rm_PhiP, trace_smul]
    simp only [ite_mul, zero_mul, p58rm_PhiPhi ψ hψ]
    rw [Finset.sum_eq_single S (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp [p58rm_trPhi ψ hψ]
  have h2 : (p58rm_Q ψ S * auxiliary n d q * p58rm_Q ψ S).trace =
      (((q S / (d:ℝ)^S.card : ℝ)) : ℂ) * (p58rm_Q ψ S).trace := by
    rw [p58rm_aux q, Matrix.mul_sum, Matrix.sum_mul, trace_sum]
    simp_rw [Matrix.mul_smul, Matrix.smul_mul, p58rm_QP, trace_smul]
    simp only [ite_mul, zero_mul, p58rm_QQ hψ]
    rw [Finset.sum_eq_single S (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp
  rw [h1, h2, mul_smul, ← smul_add, p58rm_sig_tau o ρ hψ hρ]

omit hψ hρ in
lemma p58rm_inv_nonneg (z : ℂ) (h : 0 ≤ z) : 0 ≤ z⁻¹ := by
  obtain ⟨hr, hi⟩ := Complex.le_def.mp h
  have hz : z = (z.re : ℂ) := Complex.ext rfl (by simp; exact hi.symm)
  rw [hz, ← Complex.ofReal_inv]
  exact Complex.zero_le_real.mpr (inv_nonneg.mpr (by simpa using hr))

lemma p58rm_isChannel : IsChannel (p58rm_chan ψ o ρ) := by
  have hsigpsd : ∀ S, (p58rm_sig o S ρ).PosSemidef := fun S => p58rm_sig_psd o S ρ hρ.1
  have hsigtr : ∀ S, (p58rm_sig o S ρ).trace = 1 := fun S => by rw [p58rm_sig_tr, hρ.2]
  refine p58rm_mp_channel (p58rm_A ψ) (p58rm_S ψ o ρ) (fun i => ?_) ?_
  · rcases i with ⟨S, _ | _⟩
    · simp only [p58rm_S, Bool.false_eq_true, if_false, p58rm_tau]
      refine PosSemidef.smul ?_ (p58rm_inv_nonneg _ (p58rm_trQ_nonneg hψ S))
      exact p58rm_proj_sub_psd _ _ (p58rm_PH S) (p58rm_PP S) (hsigpsd S) (hsigtr S)
        (p58rm_Psig o S ρ) (p58rm_sigP o S ρ)
    · simpa [p58rm_S] using hsigpsd S
  · rw [Fintype.sum_prod_type, ← p58rm_sumP (n := n) (d := d)]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Fintype.sum_bool]
    simp only [p58rm_S, p58rm_A, if_true, Bool.false_eq_true, if_false]
    rw [hsigtr, one_smul, p58rm_PhiProj ψ hψ, p58rm_QH, p58rm_QQ hψ]
    have hq : (p58rm_tau ψ o ρ S).trace • p58rm_Q ψ S = p58rm_Q ψ S := by
      by_cases h : (p58rm_Q ψ S).trace = 0
      · rw [p58rm_Q_zero hψ S h, smul_zero]
      · have htP : (p58rm_P S : Operator (Output n d)).trace = 1 + (p58rm_Q ψ S).trace := by
          unfold p58rm_Q; rw [trace_sub, p58rm_trPhi ψ hψ]; ring
        unfold p58rm_tau
        rw [trace_smul, trace_sub, htP, hsigtr, add_sub_cancel_left, smul_eq_mul,
          inv_mul_cancel₀ h, one_smul]
    rw [hq]
    unfold p58rm_Q; abel

end asm

end

end QAlgorithms.Papers.Independent.Information100.P58

open QAlgorithms.Papers.Independent.Information100.P58 in
theorem solution (n d : ℕ) (hn : 0<n) (hd : 2≤d) (p : ℝ)
    (hp0 : 0≤p) (hp1 : p≤1) (ψ : EuclideanSpace ℂ (Fin d)) (hψ : ‖ψ‖=1)
    (ρ : QAlgorithms.Papers.Independent.Information100.P58.Operator
      (QAlgorithms.Papers.Independent.Information100.P58.Word n d))
    (hρ : QAlgorithms.IsDensityMatrix ρ) :
    ∃ Φ : QAlgorithms.Superop (QAlgorithms.Papers.Independent.Information100.P58.Output n d)
        (QAlgorithms.Papers.Independent.Information100.P58.Output n d),
      QAlgorithms.IsChannel Φ ∧
      Φ (QAlgorithms.Papers.Independent.Information100.P58.reference n d p ψ) =
        QAlgorithms.Papers.Independent.Information100.P58.erasure n d p ρ ∧
      ∀ q : QAlgorithms.Papers.Independent.Information100.P58.Distribution (Finset (Fin n)),
        Φ (QAlgorithms.Papers.Independent.Information100.P58.auxiliary n d q.val) =
          QAlgorithms.Papers.Independent.Information100.P58.auxiliary n d q.val := by
  let o : Fin d := ⟨0, by omega⟩
  exact ⟨p58rm_chan ψ o ρ, p58rm_isChannel o ρ hψ hρ, p58rm_chan_ref o ρ hψ p,
    fun q => p58rm_chan_aux o ρ hψ hρ q.val⟩

