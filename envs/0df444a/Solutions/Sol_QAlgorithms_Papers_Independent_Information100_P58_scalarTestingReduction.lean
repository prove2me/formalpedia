-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P58.scalarTestingReduction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T17:00:30.741666+00:00
-- url     : https://prove2.me/submissions/693dd1bd-062d-4c15-a018-d45fa9d4e317

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
theorem solution (n d : ℕ) (hn : 0<n) (hd : 2≤d) (p ε : ℝ)
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

