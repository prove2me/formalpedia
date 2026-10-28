-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P58.exactTestingValue
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T19:52:16.880775+00:00
-- url     : https://prove2.me/submissions/1dd986bd-074a-4235-a3da-4cedf65ec59b

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58
namespace QAlgorithms.Papers.Independent.Information100.P58

open scoped BigOperators ComplexConjugate Matrix

noncomputable section

open Matrix
open scoped ComplexOrder

/-- coordinate factor -/
def p58s204_cc {d : ℕ} (ψ : EuclideanSpace ℂ (Fin d)) (b : Bool) : Option (Fin d) → ℂ
  | some a => if b then ψ a else 0
  | none => if b then 0 else 1

def p58s204_phi {n d : ℕ} (ψ : EuclideanSpace ℂ (Fin d)) (S : Finset (Fin n)) :
    Output n d → ℂ := fun y => ∏ i, p58s204_cc ψ (decide (i ∈ S)) (y i)

def p58s204_Phi {n d : ℕ} (ψ : EuclideanSpace ℂ (Fin d)) (S : Finset (Fin n)) :
    Operator (Output n d) := vecMulVec (p58s204_phi ψ S) (star (p58s204_phi ψ S))

def p58s204_P {n d : ℕ} (S : Finset (Fin n)) : Operator (Output n d) :=
  diagonal fun y => if support y = S then 1 else 0

lemma p58s204_normsq {d : ℕ} (ψ : EuclideanSpace ℂ (Fin d)) (hψ : ‖ψ‖ = 1) :
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

lemma p58s204_sum_finset_prod {n : ℕ} (f : Fin n → Bool → ℂ) :
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

lemma p58s204_orth {n d : ℕ} (ψ : EuclideanSpace ℂ (Fin d)) (hψ : ‖ψ‖ = 1)
    (S S' : Finset (Fin n)) :
    ∑ y, star (p58s204_phi ψ S y) * p58s204_phi ψ S' y = if S = S' then 1 else 0 := by
  have hn := p58s204_normsq ψ hψ
  unfold p58s204_phi
  simp_rw [star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i u => star (p58s204_cc ψ (decide (i ∈ S)) u) *
    p58s204_cc ψ (decide (i ∈ S')) u)]
  have key : ∀ i, ∑ u, star (p58s204_cc ψ (decide (i ∈ S)) u) * p58s204_cc ψ (decide (i ∈ S')) u
      = if (i ∈ S ↔ i ∈ S') then 1 else 0 := by
    intro i
    rw [Fintype.sum_option]
    by_cases h1 : i ∈ S <;> by_cases h2 : i ∈ S' <;> simp [p58s204_cc, h1, h2] <;> exact hn
  simp_rw [key]
  split_ifs with h
  · subst h; simp
  · obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ S ↔ i ∈ S') := by
      by_contra hc; push Not at hc; exact h (Finset.ext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma p58s204_supp {n d : ℕ} (ψ : EuclideanSpace ℂ (Fin d)) (S : Finset (Fin n))
    (y : Output n d) (h : support y ≠ S) : p58s204_phi ψ S y = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, ¬ ((y i).isSome ↔ i ∈ S) := by
    by_contra hc; push Not at hc
    exact h (Finset.ext fun i => by simp [support, hc i])
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rcases hy : y i with _ | a <;> simp_all [p58s204_cc]

lemma p58s204_w {n : ℕ} (p : ℝ) (S : Finset (Fin n)) :
    ((patternWeight n p S : ℝ) : ℂ) = ∏ i, (if decide (i ∈ S) then ((1 - p : ℝ) : ℂ) else (p : ℂ)) := by
  rw [← Finset.prod_mul_prod_compl S]
  rw [Finset.prod_congr rfl (fun i (hi : i ∈ S) => by simp [hi] : ∀ i ∈ S,
      (if decide (i ∈ S) then ((1 - p : ℝ) : ℂ) else (p : ℂ)) = ((1 - p : ℝ) : ℂ))]
  rw [Finset.prod_congr rfl (fun i (hi : i ∈ Sᶜ) => by
      have : i ∉ S := by simpa using hi
      simp [this] : ∀ i ∈ Sᶜ,
      (if decide (i ∈ S) then ((1 - p : ℝ) : ℂ) else (p : ℂ)) = (p : ℂ))]
  simp [patternWeight, Finset.card_compl]

lemma p58s204_H {d : ℕ} (p : ℝ) (ψ : EuclideanSpace ℂ (Fin d)) (hψ : ‖ψ‖ = 1)
    (u u' : Option (Fin d)) :
    ∑ a, ∑ b, ψ a * conj (ψ b) * singleErasure d p (Matrix.single a b 1) u u' =
      ((1 - p : ℝ) : ℂ) * p58s204_cc ψ true u *
          star (p58s204_cc ψ true u') +
        (p : ℂ) * p58s204_cc ψ false u *
          star (p58s204_cc ψ false u') := by
  have hn := p58s204_normsq ψ hψ
  rcases u with _ | i <;> rcases u' with _ | j
  · have htr : ∀ a b : Fin d, (Matrix.single a b (1:ℂ)).trace = if a = b then 1 else 0 := by
      intro a b
      split_ifs with h
      · subst h; exact Matrix.trace_single_eq_same _ _
      · exact Matrix.trace_single_eq_of_ne _ _ _ h
    simp only [singleErasure, p58s204_cc, htr]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have : ∑ a, ψ a * conj (ψ a) * (p : ℂ) = (p : ℂ) := by
      rw [← Finset.sum_mul]
      have : ∑ a, ψ a * conj (ψ a) = 1 := by
        rw [← hn]; exact Finset.sum_congr rfl fun a _ => mul_comm _ _
      rw [this, one_mul]
    simpa using this
  · simp [singleErasure, p58s204_cc]
  · simp [singleErasure, p58s204_cc]
  · simp [singleErasure, p58s204_cc, Matrix.single_apply]
    simp_rw [ite_and]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring

lemma p58s204_ref {n d : ℕ} (p : ℝ) (ψ : EuclideanSpace ℂ (Fin d)) (hψ : ‖ψ‖ = 1) :
    reference n d p ψ = ∑ S, ((patternWeight n p S : ℝ) : ℂ) • p58s204_Phi ψ S := by
  ext y y'
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, p58s204_Phi, vecMulVec_apply, Pi.star_apply, smul_eq_mul,
    p58s204_phi, p58s204_w]
  have hR : ∑ S : Finset (Fin n), (∏ i, (if decide (i ∈ S) then ((1 - p : ℝ) : ℂ) else (p : ℂ))) *
      ((∏ i, p58s204_cc ψ (decide (i ∈ S)) (y i)) *
        star (∏ i, p58s204_cc ψ (decide (i ∈ S)) (y' i))) =
      ∏ i, (((1 - p : ℝ) : ℂ) * p58s204_cc ψ true (y i) *
          star (p58s204_cc ψ true (y' i)) +
        (p : ℂ) * p58s204_cc ψ false (y i) *
          star (p58s204_cc ψ false (y' i))) := by
    refine (Finset.sum_congr rfl fun S _ => ?_).trans
      ((p58s204_sum_finset_prod (fun i b => (if b then ((1 - p : ℝ) : ℂ) else (p : ℂ)) *
      p58s204_cc ψ b (y i) * star (p58s204_cc ψ b (y' i)))).trans ?_)
    swap
    · simp
    rw [star_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases h : i ∈ S <;> simp [h, mul_assoc]
  rw [hR]
  simp_rw [← p58s204_H p ψ hψ]
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

lemma p58s204_PhiPhi (S' S : Finset (Fin n)) :
    p58s204_Phi ψ S' * p58s204_Phi ψ S = if S' = S then p58s204_Phi ψ S else 0 := by
  unfold p58s204_Phi
  rw [vecMulVec_mul_vecMulVec]
  have : star (p58s204_phi ψ S') ⬝ᵥ p58s204_phi ψ S = if S' = S then 1 else 0 := by
    rw [← p58s204_orth ψ hψ S' S]; rfl
  rw [this]
  split_ifs with h
  · subst h; simp
  · ext i j; simp [vecMulVec_apply]

omit hψ in
lemma p58s204_PhiP (S' S : Finset (Fin n)) :
    p58s204_Phi ψ S' * p58s204_P S = if S' = S then p58s204_Phi ψ S else 0 := by
  unfold p58s204_Phi p58s204_P
  ext y y'
  rw [mul_diagonal]
  by_cases h : S' = S
  · subst h
    rw [if_pos rfl]
    by_cases hy : support y' = S'
    · simp [hy]
    · simp [hy, vecMulVec_apply, p58s204_supp ψ S' y' hy]
  · rw [if_neg h]
    by_cases hy : support y' = S
    · have : support y' ≠ S' := fun h' => h (h'.symm.trans hy)
      simp [hy, vecMulVec_apply, p58s204_supp ψ S' y' this]
    · simp [hy]

omit hψ in
lemma p58s204_PPhi (S : Finset (Fin n)) :
    p58s204_P S * p58s204_Phi ψ S = p58s204_Phi ψ S := by
  unfold p58s204_Phi p58s204_P
  ext y y'
  rw [diagonal_mul]
  by_cases hy : support y = S
  · simp [hy]
  · simp [hy, vecMulVec_apply, p58s204_supp ψ S y hy]

omit hψ in
lemma p58s204_PP (S : Finset (Fin n)) :
    (p58s204_P S : Operator (Output n d)) * p58s204_P S = p58s204_P S := by
  unfold p58s204_P
  rw [diagonal_mul_diagonal]
  congr 1; ext y; split_ifs <;> simp

omit hψ in
lemma p58s204_sumP : ∑ S : Finset (Fin n), (p58s204_P S : Operator (Output n d)) = 1 := by
  unfold p58s204_P
  ext y y'
  rw [Matrix.sum_apply]
  by_cases h : y = y'
  · subst h; simp
  · simp [h]

lemma p58s204_trPhi (S : Finset (Fin n)) : (p58s204_Phi ψ S).trace = 1 := by
  unfold p58s204_Phi
  rw [trace_vecMulVec]
  have := p58s204_orth ψ hψ S S
  simp only [if_true] at this
  rw [← this, dotProduct]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

omit hψ in
lemma p58s204_PhiH (S : Finset (Fin n)) : (p58s204_Phi ψ S)ᴴ = p58s204_Phi ψ S :=
  (posSemidef_vecMulVec_self_star _).1

omit hψ in
lemma p58s204_PH (S : Finset (Fin n)) : (p58s204_P S : Operator (Output n d))ᴴ = p58s204_P S := by
  unfold p58s204_P
  rw [diagonal_conjTranspose]
  congr 1; ext y; simp only [Pi.star_apply]; split_ifs <;> simp

lemma p58s204_PhiProj (S : Finset (Fin n)) :
    (p58s204_Phi ψ S)ᴴ * p58s204_Phi ψ S = p58s204_Phi ψ S := by
  rw [p58s204_PhiH, p58s204_PhiPhi ψ hψ]; simp

lemma p58s204_QProj (S : Finset (Fin n)) :
    (p58s204_P S - p58s204_Phi ψ S)ᴴ * (p58s204_P S - p58s204_Phi ψ S) =
      p58s204_P S - p58s204_Phi ψ S := by
  rw [conjTranspose_sub, p58s204_PhiH, p58s204_PH, sub_mul, mul_sub, mul_sub, p58s204_PP,
    p58s204_PPhi, p58s204_PhiP, p58s204_PhiPhi ψ hψ]
  simp

end mats

lemma p58s204_tr_nonneg {A : Type*} [Fintype A] [DecidableEq A] (T B : Operator A)
    (hT : T.PosSemidef) (hB : Bᴴ * B = B) : 0 ≤ (T * B).trace.re := by
  rw [← hB, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  have := (hT.mul_mul_conjTranspose_same B).trace_nonneg
  exact (Complex.le_def.mp this).1

lemma p58s204_aux {n d : ℕ} (q : Finset (Fin n) → ℝ) :
    auxiliary n d q = ∑ S, (((q S / (d:ℝ)^S.card : ℝ)) : ℂ) • (p58s204_P S : Operator (Output n d)) := by
  ext y y'
  rw [Matrix.sum_apply]
  unfold auxiliary p58s204_P
  by_cases h : y = y'
  · subst h; simp [diagonal_apply]
  · simp [diagonal_apply, h]

section eff
variable {n d : ℕ} (ψ : EuclideanSpace ℂ (Fin d)) (hψ : ‖ψ‖ = 1)
include hψ

lemma p58s204_tS_bounds (T : Operator (Output n d)) (hT : IsEffect T) (S : Finset (Fin n)) :
    0 ≤ (T * p58s204_Phi ψ S).trace.re ∧ (T * p58s204_Phi ψ S).trace.re ≤ 1 := by
  refine ⟨p58s204_tr_nonneg T _ hT.1 (p58s204_PhiProj ψ hψ S), ?_⟩
  have := p58s204_tr_nonneg (1 - T) _ hT.2 (p58s204_PhiProj ψ hψ S)
  rw [sub_mul, Matrix.one_mul, trace_sub, p58s204_trPhi ψ hψ, Complex.sub_re, Complex.one_re] at this
  linarith

lemma p58s204_tS_le (T : Operator (Output n d)) (hT : IsEffect T) (S : Finset (Fin n)) :
    (T * p58s204_Phi ψ S).trace.re ≤ (T * p58s204_P S).trace.re := by
  have := p58s204_tr_nonneg T _ hT.1 (p58s204_QProj ψ hψ S)
  rw [Matrix.mul_sub, trace_sub, Complex.sub_re] at this
  linarith

lemma p58s204_omega (p : ℝ) (T : Operator (Output n d)) :
    effectProb T (reference n d p ψ) =
      ∑ S, patternWeight n p S * (T * p58s204_Phi ψ S).trace.re := by
  unfold effectProb
  rw [p58s204_ref p ψ hψ, Matrix.mul_sum, trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Matrix.mul_smul, trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

omit hψ in
lemma p58s204_sigma (q : Finset (Fin n) → ℝ) (T : Operator (Output n d)) :
    effectProb T (auxiliary n d q) =
      ∑ S, q S / (d:ℝ)^S.card * (T * p58s204_P S).trace.re := by
  unfold effectProb
  rw [p58s204_aux, Matrix.mul_sum, trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Matrix.mul_smul, trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

/-- the constructed test -/
def p58s204_Tst (t : Finset (Fin n) → ℝ) : Operator (Output n d) :=
  ∑ S, ((t S : ℝ) : ℂ) • p58s204_Phi ψ S

lemma p58s204_Tst_Phi (t : Finset (Fin n) → ℝ) (S : Finset (Fin n)) :
    (p58s204_Tst ψ t * p58s204_Phi ψ S).trace.re = t S := by
  unfold p58s204_Tst
  rw [Matrix.sum_mul]
  simp_rw [Matrix.smul_mul, p58s204_PhiPhi ψ hψ, smul_ite, smul_zero]
  rw [Finset.sum_ite_eq' Finset.univ S, if_pos (Finset.mem_univ _), trace_smul,
    p58s204_trPhi ψ hψ]
  simp

lemma p58s204_Tst_P (t : Finset (Fin n) → ℝ) (S : Finset (Fin n)) :
    (p58s204_Tst ψ t * p58s204_P S).trace.re = t S := by
  unfold p58s204_Tst
  rw [Matrix.sum_mul]
  simp_rw [Matrix.smul_mul, p58s204_PhiP, smul_ite, smul_zero]
  rw [Finset.sum_ite_eq' Finset.univ S, if_pos (Finset.mem_univ _), trace_smul,
    p58s204_trPhi ψ hψ]
  simp

lemma p58s204_Tst_eff (t : Finset (Fin n) → ℝ) (ht : ∀ S, 0 ≤ t S ∧ t S ≤ 1) :
    IsEffect (p58s204_Tst ψ t) := by
  constructor
  · exact posSemidef_sum _ fun S _ =>
      (posSemidef_vecMulVec_self_star _).smul (Complex.zero_le_real.mpr (ht S).1)
  · have : 1 - p58s204_Tst ψ t = ∑ S, (p58s204_P S - p58s204_Phi ψ S) +
        ∑ S, ((1 - t S : ℝ) : ℂ) • p58s204_Phi ψ S := by
      unfold p58s204_Tst
      rw [Finset.sum_sub_distrib, p58s204_sumP]
      simp only [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul, Finset.sum_sub_distrib]
      abel
    rw [this]
    refine (posSemidef_sum _ fun S _ => ?_).add (posSemidef_sum _ fun S _ =>
      (posSemidef_vecMulVec_self_star _).smul
        (Complex.zero_le_real.mpr (by linarith [(ht S).2])))
    rw [← p58s204_QProj ψ hψ S]
    exact posSemidef_conjTranspose_mul_self _

end eff

end

end QAlgorithms.Papers.Independent.Information100.P58

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Information100.P58 in
theorem st_reduction (n d : ℕ) (hn : 0<n) (hd : 2≤d) (p ε : ℝ)
    (hp0 : 0≤p) (hp1 : p≤1) (hε0 : 0≤ε) (hε1 : ε<1)
    (ψ : EuclideanSpace ℂ (Fin d)) (hψ : ‖ψ‖=1) (q : Distribution (Finset (Fin n))) :
    testingBeta ε (reference n d p ψ) (auxiliary n d q.val) =
      sInf {v : ℝ | ∃ t : Finset (Fin n) → ℝ, ScalarFeasible n p ε t ∧ v=scalarCost n d q.val t} ∧
    ∃ t : Finset (Fin n) → ℝ, ScalarFeasible n p ε t ∧
      scalarCost n d q.val t = testingBeta ε (reference n d p ψ) (auxiliary n d q.val) := by
  set K : Set (Finset (Fin n) → ℝ) := {t | ScalarFeasible n p ε t} with hK
  have hclosed : IsClosed K := by
    have : K = (⋂ S, {t : Finset (Fin n) → ℝ | 0 ≤ t S} ∩ {t | t S ≤ 1}) ∩
        {t | 1 - ε ≤ ∑ S, patternWeight n p S * t S} := by
      ext t; simp [hK, ScalarFeasible, Set.mem_iInter]
    rw [this]
    exact (isClosed_iInter fun S => (isClosed_le continuous_const (continuous_apply S)).inter
      (isClosed_le (continuous_apply S) continuous_const)).inter
      (isClosed_le continuous_const
        (continuous_finsetSum _ fun S _ => continuous_const.mul (continuous_apply S)))
  have hKc : IsCompact K := isCompact_Icc.of_isClosed_subset hclosed
    (fun t ht => ⟨fun S => (ht.1 S).1, fun S => (ht.1 S).2⟩)
  have hne : (fun _ => (1:ℝ)) ∈ K := by
    refine ⟨fun _ => ⟨zero_le_one, le_rfl⟩, ?_⟩
    simp only [mul_one, patternWeight]
    rw [Fin.sum_pow_mul_eq_add_pow]
    simp; linarith
  have hcont : Continuous (scalarCost n d q.val) :=
    continuous_finsetSum _ fun S _ => (continuous_const.mul (continuous_apply S)).div_const _
  obtain ⟨t0, ht0, hmin⟩ := hKc.exists_isMinOn ⟨_, hne⟩ hcont.continuousOn
  have hA : IsLeast {v : ℝ | ∃ T : Operator (Output n d), QAlgorithms.IsEffect T ∧
      1 - ε ≤ QAlgorithms.effectProb T (reference n d p ψ) ∧
        v = QAlgorithms.effectProb T (auxiliary n d q.val)}
      (scalarCost n d q.val t0) := by
    constructor
    · refine ⟨p58s204_Tst ψ t0, p58s204_Tst_eff ψ hψ t0 ht0.1, ?_, ?_⟩
      · rw [p58s204_omega ψ hψ]
        simp_rw [p58s204_Tst_Phi ψ hψ]
        exact ht0.2
      · rw [p58s204_sigma]
        simp_rw [p58s204_Tst_P ψ hψ]
        unfold scalarCost
        exact Finset.sum_congr rfl fun S _ => by ring
    · rintro v ⟨T, hT, h1, rfl⟩
      have ht : (fun S => (T * p58s204_Phi ψ S).trace.re) ∈ K :=
        ⟨fun S => p58s204_tS_bounds ψ hψ T hT S, by rw [p58s204_omega ψ hψ] at h1; exact h1⟩
      refine (isMinOn_iff.mp hmin _ ht).trans ?_
      rw [p58s204_sigma]
      unfold scalarCost
      refine Finset.sum_le_sum fun S _ => ?_
      rw [mul_div_right_comm]
      exact mul_le_mul_of_nonneg_left (p58s204_tS_le ψ hψ T hT S)
        (div_nonneg (q.2.1 S) (pow_nonneg (Nat.cast_nonneg _) _))
  have hB : IsLeast {v : ℝ | ∃ t : Finset (Fin n) → ℝ, ScalarFeasible n p ε t ∧
      v = scalarCost n d q.val t} (scalarCost n d q.val t0) :=
    ⟨⟨t0, ht0, rfl⟩, by rintro v ⟨t, ht, rfl⟩; exact isMinOn_iff.mp hmin t ht⟩
  unfold testingBeta
  rw [hA.csInf_eq, hB.csInf_eq]
  exact ⟨rfl, t0, ht0, rfl⟩



namespace QAlgorithms.Papers.Independent.Information100.P58

open scoped BigOperators ComplexConjugate Matrix

noncomputable section

theorem rc_group (n : ℕ) (p : ℝ) (g : ℕ → ℝ) :
    ∑ S : Finset (Fin n), patternWeight n p S * g S.card =
      ∑ k ∈ Finset.range (n + 1), binomialWeight n p k * g k := by
  have := Finset.sum_powerset_apply_card (fun k => (1 - p) ^ k * p ^ (n - k) * g k)
    (x := (Finset.univ : Finset (Fin n)))
  rw [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] at this
  unfold patternWeight binomialWeight
  rw [this]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [nsmul_eq_mul]; ring

theorem rc_wsum (n : ℕ) (p : ℝ) : ∑ S : Finset (Fin n), patternWeight n p S = 1 := by
  have := rc_group n p (fun _ => 1)
  simp only [mul_one] at this
  rw [this]
  have h := (add_pow (1 - p) p n).symm
  rw [show 1 - p + p = 1 by ring, one_pow] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold binomialWeight; ring


theorem rc_w_nonneg' (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset (Fin n)) :
    0 ≤ patternWeight n p S := by
  unfold patternWeight
  have : 0 ≤ 1 - p := by linarith
  positivity

theorem et_bsum (n : ℕ) (p : ℝ) : ∑ k ∈ Finset.range (n + 1), binomialWeight n p k = 1 := by
  have := rc_group n p (fun _ => 1)
  simp only [mul_one] at this
  rw [← this, rc_wsum]

theorem et_bw_nonneg (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) : 0 ≤ binomialWeight n p k := by
  unfold binomialWeight
  have : 0 ≤ 1 - p := by linarith
  positivity

theorem et_B_le_Z (n d : ℕ) (hd : 1 ≤ d) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (j : ℕ) :
    cumulativeB n p j ≤ cumulativeZ n d p j := by
  unfold cumulativeB cumulativeZ
  refine Finset.sum_le_sum fun k _ => ?_
  have : (1:ℝ) ≤ (d:ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hd)
  have := et_bw_nonneg n hp0 hp1 k
  nlinarith

theorem et_T (n d : ℕ) (hd : 1 ≤ d) {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    (∃ j, j ≤ n ∧ ε < cumulativeB n p j ∧
      cumulativeZ n d p j / (cumulativeB n p j - ε) = messageThreshold n d p ε) ∧
    (∀ j, j ≤ n → ε < cumulativeB n p j →
      messageThreshold n d p ε ≤ cumulativeZ n d p j / (cumulativeB n p j - ε)) ∧
    0 < messageThreshold n d p ε := by
  set J := {r : ℝ | ∃ j : ℕ, j ≤ n ∧ ε < cumulativeB n p j ∧
    r = cumulativeZ n d p j / (cumulativeB n p j - ε)} with hJ
  have hfin : J.Finite := by
    apply ((Finset.range (n + 1)).image fun j =>
      cumulativeZ n d p j / (cumulativeB n p j - ε)).finite_toSet.subset
    rintro r ⟨j, hj, _, rfl⟩
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    exact ⟨j, by omega, rfl⟩
  have hBn : cumulativeB n p n = 1 := et_bsum n p
  have hne : J.Nonempty := ⟨_, n, le_rfl, by rw [hBn]; exact hε1, rfl⟩
  have hmem := hne.csInf_mem hfin
  have hT : messageThreshold n d p ε = sInf J := rfl
  have hpos : ∀ r ∈ J, 0 < r := by
    rintro r ⟨j, _, hj, rfl⟩
    have := et_B_le_Z n d hd hp0 hp1 j
    apply div_pos <;> linarith
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨j, hj, hjB, hjr⟩ := hmem
    exact ⟨j, hj, hjB, by rw [hT, hjr]⟩
  · intro j hj hjB
    rw [hT]
    exact csInf_le hfin.bddBelow ⟨j, hj, hjB, rfl⟩
  · rw [hT]; exact hpos _ hmem

/-- Σ b_k min(1, x_k) with monotone x splits at a threshold. -/
theorem et_split (N : ℕ) (b x : ℕ → ℝ) (hx : Monotone x) :
    ∃ j, j ≤ N ∧ (∀ k, k < j → x k < 1) ∧
      ∑ k ∈ Finset.range N, b k * min 1 (x k) =
        ∑ k ∈ Finset.range j, b k * x k + ∑ k ∈ Finset.Ico j N, b k := by
  classical
  have hex : ∃ k, k = N ∨ 1 ≤ x k := ⟨N, Or.inl rfl⟩
  set j := Nat.find hex with hj
  have hjN : j ≤ N := Nat.find_min' hex (Or.inl rfl)
  have hlt : ∀ k, k < j → x k < 1 := by
    intro k hk
    have := Nat.find_min hex hk
    push_neg at this
    exact this.2
  have hge : ∀ k, j ≤ k → k < N → 1 ≤ x k := by
    intro k hk hkN
    rcases Nat.find_spec hex with h | h
    · rw [← hj] at h; omega
    · exact h.trans (hx hk)
  refine ⟨j, hjN, hlt, ?_⟩
  rw [← Finset.sum_range_add_sum_Ico _ hjN]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [min_eq_right (hlt k (Finset.mem_range.mp hk)).le]
  · refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hk
    rw [min_eq_left (hge k h1 h2), mul_one]

theorem et_feasible (n d : ℕ) (hd : 1 ≤ d) {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    1 - ε ≤ ∑ k ∈ Finset.range (n + 1),
      binomialWeight n p k * min 1 ((d:ℝ) ^ k / messageThreshold n d p ε) := by
  obtain ⟨_, hTle, hTpos⟩ := et_T n d hd hp0 hp1 hε0 hε1
  set T := messageThreshold n d p ε
  have hmono : Monotone fun k : ℕ => (d:ℝ) ^ k / T := by
    intro a b hab
    exact div_le_div_of_nonneg_right (pow_le_pow_right₀ (by exact_mod_cast hd) hab) hTpos.le
  obtain ⟨j, hjN, _, hsum⟩ := et_split (n + 1) (binomialWeight n p) _ hmono
  rw [hsum]
  have hIco : ∑ k ∈ Finset.Ico j (n + 1), binomialWeight n p k =
      1 - ∑ k ∈ Finset.range j, binomialWeight n p k := by
    rw [← et_bsum n p, ← Finset.sum_range_add_sum_Ico _ hjN]; ring
  rw [hIco]
  rcases Nat.eq_zero_or_pos j with h0 | hjpos
  · subst h0; simp; linarith
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hZ : ∑ k ∈ Finset.range (j' + 1), binomialWeight n p k * ((d:ℝ) ^ k / T) =
      cumulativeZ n d p j' / T := by
    unfold cumulativeZ; rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hB : ∑ k ∈ Finset.range (j' + 1), binomialWeight n p k = cumulativeB n p j' := rfl
  rw [hZ, hB]
  by_cases hc : ε < cumulativeB n p j'
  · have h := hTle j' (by omega) hc
    have hZpos : 0 ≤ cumulativeZ n d p j' := by
      have := et_B_le_Z n d hd hp0 hp1 j'; linarith
    rw [le_div_iff₀ (by linarith)] at h
    have : cumulativeB n p j' - ε ≤ cumulativeZ n d p j' / T := by
      rw [le_div_iff₀ hTpos]; linarith
    linarith
  · have : 0 ≤ cumulativeZ n d p j' / T := by
      apply div_nonneg _ hTpos.le
      have := et_B_le_Z n d hd hp0 hp1 j'
      have : 0 ≤ cumulativeB n p j' := Finset.sum_nonneg fun k _ => et_bw_nonneg n hp0 hp1 k
      linarith
    push_neg at hc; linarith


theorem et_cost_nonneg {n d : ℕ} {p ε : ℝ} (q : Distribution (Finset (Fin n))) (t : Finset (Fin n) → ℝ)
    (ht : ScalarFeasible n p ε t) : 0 ≤ scalarCost n d q.val t := by
  unfold scalarCost
  exact Finset.sum_nonneg fun S _ => div_nonneg (mul_nonneg (q.2.1 S) (ht.1 S).1)
    (pow_nonneg (Nat.cast_nonneg _) _)

theorem et_upper (n d : ℕ) (hn : 0 < n) (hd : 2 ≤ d) {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (ψ : EuclideanSpace ℂ (Fin d)) (hψ : ‖ψ‖ = 1)
    (q : Distribution (Finset (Fin n))) :
    0 ≤ testingBeta ε (reference n d p ψ) (auxiliary n d q.val) ∧
    testingBeta ε (reference n d p ψ) (auxiliary n d q.val) ≤ 1 / messageThreshold n d p ε := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hβ, t0, ht0, hc0⟩ := st_reduction n d hn hd p ε hp0 hp1 hε0 hε1 ψ hψ q
  obtain ⟨_, _, hTpos⟩ := et_T n d hd1 hp0 hp1 hε0 hε1
  set T := messageThreshold n d p ε
  refine ⟨by rw [← hc0]; exact et_cost_nonneg q t0 ht0, ?_⟩
  let t : Finset (Fin n) → ℝ := fun S => min 1 ((d:ℝ) ^ S.card / T)
  have ht : ScalarFeasible n p ε t := by
    refine ⟨fun S => ⟨le_min zero_le_one (by positivity), min_le_left _ _⟩, ?_⟩
    rw [rc_group n p (fun k => min 1 ((d:ℝ) ^ k / T))]
    exact et_feasible n d hd1 hp0 hp1 hε0 hε1
  have hcost : scalarCost n d q.val t ≤ 1 / T := by
    unfold scalarCost
    calc _ ≤ ∑ S, q.val S * (1 / T) := Finset.sum_le_sum fun S _ => by
          have hdk : (0:ℝ) < (d:ℝ) ^ S.card := by
            have : (0:ℝ) < d := by exact_mod_cast hd1
            positivity
          rw [mul_div_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (q.2.1 S)
          rw [div_le_iff₀ hdk]
          calc t S ≤ (d:ℝ) ^ S.card / T := min_le_right _ _
            _ = 1 / T * (d:ℝ) ^ S.card := by ring
      _ = 1 / T := by rw [← Finset.sum_mul, q.2.2, one_mul]
  rw [hβ]
  refine le_trans (csInf_le ⟨0, ?_⟩ ⟨t, ht, rfl⟩) hcost
  rintro v ⟨t', ht', rfl⟩
  exact et_cost_nonneg q t' ht'

theorem et_opt_eq (n d : ℕ) (p : ℝ) (j : ℕ) (S : Finset (Fin n)) :
    optimizer n d p j S = patternWeight n p S *
      (if S.card ≤ j then (d:ℝ) ^ S.card / cumulativeZ n d p j else 0) := by
  unfold optimizer; split_ifs <;> ring

theorem et_opt_dist (n d : ℕ) (hd : 1 ≤ d) {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε0 : 0 ≤ ε)
    (j : ℕ) (hj : j ≤ n) (hjB : ε < cumulativeB n p j) :
    (∀ S, 0 ≤ optimizer n d p j S) ∧ (∑ S, optimizer n d p j S) = 1 := by
  have hZ : 0 < cumulativeZ n d p j := by have := et_B_le_Z n d hd hp0 hp1 j; linarith
  refine ⟨fun S => ?_, ?_⟩
  · unfold optimizer
    split_ifs
    · have := rc_w_nonneg' n hp0 hp1 S
      positivity
    · exact le_rfl
  · simp only [et_opt_eq]
    rw [rc_group n p (fun k => if k ≤ j then (d:ℝ) ^ k / cumulativeZ n d p j else 0)]
    have : ∑ k ∈ Finset.range (n + 1), binomialWeight n p k *
        (if k ≤ j then (d:ℝ) ^ k / cumulativeZ n d p j else 0) =
        (∑ k ∈ Finset.range (j + 1), binomialWeight n p k * (d:ℝ) ^ k) / cumulativeZ n d p j := by
      rw [Finset.sum_div, ← Finset.sum_range_add_sum_Ico _ (by omega : j + 1 ≤ n + 1)]
      have h0 : ∑ k ∈ Finset.Ico (j + 1) (n + 1), binomialWeight n p k *
          (if k ≤ j then (d:ℝ) ^ k / cumulativeZ n d p j else 0) = 0 :=
        Finset.sum_eq_zero fun k hk => by
          rw [if_neg (by have := (Finset.mem_Ico.mp hk).1; omega), mul_zero]
      rw [h0, add_zero]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [if_pos (by have := Finset.mem_range.mp hk; omega)]; ring
    rw [this]
    exact div_self hZ.ne'

theorem et_tail (n : ℕ) (p : ℝ) (j : ℕ) (hj : j ≤ n) :
    ∑ S : Finset (Fin n), patternWeight n p S * (if j < S.card then 1 else 0) = 1 - cumulativeB n p j := by
  rw [rc_group n p (fun k => if j < k then 1 else 0)]
  rw [show 1 - cumulativeB n p j = (∑ k ∈ Finset.range (n + 1), binomialWeight n p k) -
    cumulativeB n p j by rw [et_bsum]]
  unfold cumulativeB
  rw [← Finset.sum_range_add_sum_Ico _ (by omega : j + 1 ≤ n + 1),
    ← Finset.sum_range_add_sum_Ico (fun k => binomialWeight n p k) (by omega : j + 1 ≤ n + 1)]
  have h1 : ∑ k ∈ Finset.range (j + 1), binomialWeight n p k * (if j < k then (1:ℝ) else 0) = 0 :=
    Finset.sum_eq_zero fun k hk => by
      rw [if_neg (by have := Finset.mem_range.mp hk; omega), mul_zero]
  have h2 : ∑ k ∈ Finset.Ico (j + 1) (n + 1), binomialWeight n p k * (if j < k then (1:ℝ) else 0) =
      ∑ k ∈ Finset.Ico (j + 1) (n + 1), binomialWeight n p k :=
    Finset.sum_congr rfl fun k hk => by
      rw [if_pos (by have := (Finset.mem_Ico.mp hk).1; omega), mul_one]
  rw [h1, h2]; ring

theorem et_lower (n d : ℕ) (hn : 0 < n) (hd : 2 ≤ d) {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (ψ : EuclideanSpace ℂ (Fin d)) (hψ : ‖ψ‖ = 1)
    (j : ℕ) (hj : j ≤ n) (hjB : ε < cumulativeB n p j) (q : Distribution (Finset (Fin n)))
    (hq : q.val = optimizer n d p j) :
    (cumulativeB n p j - ε) / cumulativeZ n d p j ≤
      testingBeta ε (reference n d p ψ) (auxiliary n d q.val) := by
  have hd1 : 1 ≤ d := by omega
  have hZ : 0 < cumulativeZ n d p j := by have := et_B_le_Z n d hd1 hp0 hp1 j; linarith
  obtain ⟨hβ, t0, ht0, _⟩ := st_reduction n d hn hd p ε hp0 hp1 hε0 hε1 ψ hψ q
  rw [hβ]
  refine le_csInf ⟨_, t0, ht0, rfl⟩ ?_
  rintro v ⟨t, ht, rfl⟩
  have e : scalarCost n d q.val t = (∑ S, patternWeight n p S * (if S.card ≤ j then t S else 0)) /
      cumulativeZ n d p j := by
    unfold scalarCost
    rw [hq, Finset.sum_div]
    refine Finset.sum_congr rfl fun S _ => ?_
    have hdk : (0:ℝ) < (d:ℝ) ^ S.card := by
      have : (0:ℝ) < d := by exact_mod_cast hd1
      positivity
    unfold optimizer
    split_ifs <;> field_simp <;> ring
  rw [e]
  apply div_le_div_of_nonneg_right _ hZ.le
  have hsplit : ∀ S : Finset (Fin n), patternWeight n p S * t S =
      patternWeight n p S * (if S.card ≤ j then t S else 0) +
        patternWeight n p S * (if j < S.card then t S else 0) := by
    intro S; split_ifs <;> first | omega | ring
  have hfe := ht.2
  rw [Finset.sum_congr rfl fun S _ => hsplit S, Finset.sum_add_distrib] at hfe
  have htail : ∑ S : Finset (Fin n), patternWeight n p S * (if j < S.card then t S else 0) ≤
      1 - cumulativeB n p j := by
    rw [← et_tail n p j hj]
    refine Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_left ?_ (rc_w_nonneg' n hp0 hp1 S)
    split_ifs
    · exact (ht.1 S).2
    · exact le_rfl
  linarith

theorem et_main (n d : ℕ) (hn : 0 < n) (hd : 2 ≤ d) (p ε : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (ψ : EuclideanSpace ℂ (Fin d)) (hψ : ‖ψ‖ = 1) :
    auxiliaryInf n d p ε ψ = (Real.logb 2 (messageThreshold n d p ε) : EReal) ∧
    ∀ j : ℕ, j ≤ n → ε < cumulativeB n p j →
      cumulativeZ n d p j / (cumulativeB n p j - ε) = messageThreshold n d p ε →
      (∀ S, 0 ≤ optimizer n d p j S) ∧ (∑ S, optimizer n d p j S) = 1 ∧
      testingD ε (reference n d p ψ) (auxiliary n d (optimizer n d p j)) = auxiliaryInf n d p ε ψ ∧
      testingBeta ε (reference n d p ψ) (auxiliary n d (optimizer n d p j)) =
        (cumulativeB n p j - ε) / cumulativeZ n d p j ∧
      (cumulativeB n p j - ε) / cumulativeZ n d p j = 1 / messageThreshold n d p ε := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨⟨j0, hj0, hj0B, hj0T⟩, _, hTpos⟩ := et_T n d hd1 hp0 hp1 hε0 hε1
  set T := messageThreshold n d p ε with hTdef
  have hDle : ∀ q : Distribution (Finset (Fin n)),
      (Real.logb 2 T : EReal) ≤ testingD ε (reference n d p ψ) (auxiliary n d q.val) := by
    intro q
    obtain ⟨h0, h1⟩ := et_upper n d hn hd hp0 hp1 hε0 hε1 ψ hψ q
    unfold testingD
    split_ifs with hb
    · exact le_top
    · have hpos := lt_of_le_of_ne h0 (Ne.symm hb)
      apply EReal.coe_le_coe_iff.mpr
      have := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2) hpos h1
      rw [one_div, Real.logb_inv] at this
      linarith
  -- optimal j gives equality
  have hopt : ∀ j, j ≤ n → ε < cumulativeB n p j →
      cumulativeZ n d p j / (cumulativeB n p j - ε) = T →
      ∃ q : Distribution (Finset (Fin n)), q.val = optimizer n d p j ∧
        testingBeta ε (reference n d p ψ) (auxiliary n d q.val) = 1 / T ∧
        (cumulativeB n p j - ε) / cumulativeZ n d p j = 1 / T ∧
        testingD ε (reference n d p ψ) (auxiliary n d q.val) = (Real.logb 2 T : EReal) := by
    intro j hj hjB hjT
    obtain ⟨hq0, hq1⟩ := et_opt_dist n d hd1 hp0 hp1 hε0 j hj hjB
    let q : Distribution (Finset (Fin n)) := ⟨optimizer n d p j, hq0, hq1⟩
    have hr : (cumulativeB n p j - ε) / cumulativeZ n d p j = 1 / T := by
      rw [← hjT, one_div_div]
    have hlo := et_lower n d hn hd hp0 hp1 hε0 hε1 ψ hψ j hj hjB q rfl
    have hup := (et_upper n d hn hd hp0 hp1 hε0 hε1 ψ hψ q).2
    have hβ : testingBeta ε (reference n d p ψ) (auxiliary n d q.val) = 1 / T := by
      rw [hr] at hlo; exact le_antisymm hup hlo
    refine ⟨q, rfl, hβ, hr, ?_⟩
    unfold testingD
    rw [hβ, if_neg (by positivity)]
    congr 1
    rw [one_div, Real.logb_inv, neg_neg]
  obtain ⟨q0, _, _, _, hq0D⟩ := hopt j0 hj0 hj0B hj0T
  have hinf : auxiliaryInf n d p ε ψ = (Real.logb 2 T : EReal) := by
    apply le_antisymm
    · rw [← hq0D]; exact iInf_le _ q0
    · exact le_iInf hDle
  refine ⟨hinf, fun j hj hjB hjT => ?_⟩
  obtain ⟨hq0', hq1'⟩ := et_opt_dist n d hd1 hp0 hp1 hε0 j hj hjB
  obtain ⟨q, hqv, hβ, hr, hD⟩ := hopt j hj hjB hjT
  rw [hqv] at hβ hD
  exact ⟨hq0', hq1', by rw [hD, hinf], by rw [hβ, hr], hr⟩

end

end QAlgorithms.Papers.Independent.Information100.P58

theorem solution (n d : ℕ) (hn : 0<n) (hd : 2≤d) (p ε : ℝ)
    (hp0 : 0≤p) (hp1 : p≤1) (hε0 : 0≤ε) (hε1 : ε<1)
    (ψ : EuclideanSpace ℂ (Fin d)) (hψ : ‖ψ‖=1) :
    QAlgorithms.Papers.Independent.Information100.P58.auxiliaryInf n d p ε ψ =
      (Real.logb 2 (QAlgorithms.Papers.Independent.Information100.P58.messageThreshold n d p ε) : EReal) ∧
    ∀ j : ℕ, j≤n → ε<QAlgorithms.Papers.Independent.Information100.P58.cumulativeB n p j →
      QAlgorithms.Papers.Independent.Information100.P58.cumulativeZ n d p j /
        (QAlgorithms.Papers.Independent.Information100.P58.cumulativeB n p j-ε) =
          QAlgorithms.Papers.Independent.Information100.P58.messageThreshold n d p ε →
      (∀ S, 0≤QAlgorithms.Papers.Independent.Information100.P58.optimizer n d p j S) ∧
      (∑ S, QAlgorithms.Papers.Independent.Information100.P58.optimizer n d p j S)=1 ∧
      QAlgorithms.Papers.Independent.Information100.P58.testingD ε
        (QAlgorithms.Papers.Independent.Information100.P58.reference n d p ψ)
        (QAlgorithms.Papers.Independent.Information100.P58.auxiliary n d
          (QAlgorithms.Papers.Independent.Information100.P58.optimizer n d p j)) =
        QAlgorithms.Papers.Independent.Information100.P58.auxiliaryInf n d p ε ψ ∧
      QAlgorithms.Papers.Independent.Information100.P58.testingBeta ε
        (QAlgorithms.Papers.Independent.Information100.P58.reference n d p ψ)
        (QAlgorithms.Papers.Independent.Information100.P58.auxiliary n d
          (QAlgorithms.Papers.Independent.Information100.P58.optimizer n d p j)) =
        (QAlgorithms.Papers.Independent.Information100.P58.cumulativeB n p j-ε) /
          QAlgorithms.Papers.Independent.Information100.P58.cumulativeZ n d p j ∧
      (QAlgorithms.Papers.Independent.Information100.P58.cumulativeB n p j-ε) /
          QAlgorithms.Papers.Independent.Information100.P58.cumulativeZ n d p j =
        1/QAlgorithms.Papers.Independent.Information100.P58.messageThreshold n d p ε :=
  QAlgorithms.Papers.Independent.Information100.P58.et_main n d hn hd p ε hp0 hp1 hε0 hε1 ψ hψ
