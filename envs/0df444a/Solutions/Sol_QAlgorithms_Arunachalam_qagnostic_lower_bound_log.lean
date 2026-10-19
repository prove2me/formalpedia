-- Prove2me | solution 1 for QAlgorithms.Arunachalam.qagnostic_lower_bound_log
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T09:42:32.000464+00:00
-- url     : https://prove2.me/submissions/967058fd-2b0f-4d02-b3fe-472f3b2f7251

import Definitions.Def_QAlgorithms_Defs_Learning
import Theorems.Thm_QAlgorithms_Arunachalam_helstrom_bound
import Mathlib.Analysis.Matrix.PosDef

set_option autoImplicit false
open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix QAlgorithms QAlgorithms.Learning

private lemma tensor_inner {ι : Type*} [Fintype ι] (T : ℕ)
    (u v : EuclideanSpace ℂ ι) :
    inner ℂ (tensorPow T u) (tensorPow T v) = (inner ℂ u v)^T := by
  simp only [PiLp.inner_apply, tensorPow, RCLike.inner_apply, map_prod,
    ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin T) (i : ι) => v i * (starRingEnd ℂ) (u i))]
  simp

private lemma tensor_state {ι : Type*} [Fintype ι] (T : ℕ)
    (u : EuclideanSpace ℂ ι) (hu : IsState u) : IsState (tensorPow T u) := by
  have h := tensor_inner T u u
  have hu' : inner ℂ u u = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hu]
    norm_num
  rw [hu', one_pow] at h
  have hn : ‖tensorPow T u‖^2 = 1 := by
    calc
      _ = RCLike.re (inner ℂ (tensorPow T u) (tensorPow T u)) :=
        (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
      _ = 1 := by rw [h]; norm_num
  unfold IsState
  nlinarith [norm_nonneg (tensorPow T u)]

private lemma effect_inner {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ)
    (u : EuclideanSpace ℂ ι) :
    effectProb A (pureDensity u) = (inner ℂ u (act A u)).re := by
  unfold effectProb
  congr 1
  simp only [pureDensity, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.of_apply, EuclideanSpace.inner_eq_star_dotProduct, act,
    Matrix.mulVec, dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change A i j * (u j * star (u i)) = (A i j * u j) * star (u i)
  ring

private lemma effect_nonneg {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ)
    (hA : A.PosSemidef) (u : EuclideanSpace ℂ ι) :
    0 ≤ effectProb A (pureDensity u) := by
  rw [effect_inner, EuclideanSpace.inner_eq_star_dotProduct]
  simpa only [RCLike.re_to_complex, act, WithLp.ofLp_toLp, dotProduct_comm]
    using hA.re_dotProduct_nonneg u

private lemma event_mono {O ι : Type*} [Fintype O] [Fintype ι] [DecidableEq ι]
    (M : O → Matrix ι ι ℂ) (hM : IsPOVM M) (u : EuclideanSpace ℂ ι)
    (P Q : O → Prop) [DecidablePred P] [DecidablePred Q] (hPQ : ∀ o, P o → Q o) :
    povmEventProb M (pureDensity u) P ≤ povmEventProb M (pureDensity u) Q := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro o ho
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ o, hPQ o (Finset.mem_filter.mp ho).2⟩
  · intro o _ _
    exact effect_nonneg _ (hM.1 o) u

private lemma effect_sum {O ι : Type*} [Fintype ι] (M : O → Matrix ι ι ℂ)
    (s : Finset O) (ρ : Matrix ι ι ℂ) :
    effectProb (∑ o ∈ s, M o) ρ = ∑ o ∈ s, effectProb (M o) ρ := by
  simp only [effectProb, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]

private lemma coarse_grain {O ι : Type*} [Fintype O] [Fintype ι] [DecidableEq ι]
    (M : O → Matrix ι ι ℂ) (hM : IsPOVM M) (P : O → Prop) [DecidablePred P] :
    ∃ B : Bool → Matrix ι ι ℂ, IsPOVM B ∧
      (∀ ρ, effectProb (B false) ρ = povmEventProb M ρ P) ∧
      (∀ ρ, effectProb (B true) ρ = povmEventProb M ρ (fun o => ¬P o)) := by
  classical
  let B : Bool → Matrix ι ι ℂ := fun b =>
    if b then ∑ o ∈ Finset.univ.filter (fun o => ¬P o), M o
    else ∑ o ∈ Finset.univ.filter P, M o
  refine ⟨B, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro b
    cases b <;> exact Matrix.posSemidef_sum _ (fun o _ => hM.1 o)
  · simp only [Fintype.sum_bool, B, Bool.false_eq_true, ↓reduceIte]
    rw [add_comm, Finset.sum_filter_add_sum_filter_not, hM.2]
  · intro ρ
    exact effect_sum M _ ρ
  · intro ρ
    exact effect_sum M _ ρ

private lemma confidence_bound (δ₀ δ ε : ℝ) (hδ₀ : 0 < δ₀) (hδ₀h : δ₀ < 1/2)
    (hδ : 0 < δ) (hδle : δ ≤ δ₀) (hε : 0 < ε) (hεq : ε < 1/4)
    (T : ℕ) (hov : (1-2*ε)^T ≤ 2 * Real.sqrt (δ*(1-δ))) :
    ((1-2*δ₀)^2/32) * (Real.log (1/δ)/ε) ≤ T := by
  have hdhalf : δ < 1/2 := lt_of_le_of_lt hδle hδ₀h
  have hd1 : 0 < 1-δ := by linarith
  have hq : 0 < 1-2*ε := by linarith
  have hdprod : 0 < 4*δ*(1-δ) := by positivity
  have hdprod' : 0 ≤ δ*(1-δ) := by positivity
  have hsq : ((1-2*ε)^T)^2 ≤ 4*δ*(1-δ) := by
    nlinarith [Real.sq_sqrt hdprod', Real.sqrt_nonneg (δ*(1-δ)),
      pow_nonneg (le_of_lt hq) T]
  have hlog := Real.log_le_log (sq_pos_of_pos (pow_pos hq T)) hsq
  rw [Real.log_pow, Real.log_pow] at hlog
  have hqlog : -Real.log (1-2*ε) ≤ 4*ε := by
    have h := Real.one_sub_inv_le_log_of_pos hq
    have hi : (1-2*ε)⁻¹ ≤ 1+4*ε := by
      rw [inv_le_iff_one_le_mul₀ hq]
      nlinarith
    linarith
  let A := -Real.log (4*δ*(1-δ))
  let g := (1-2*δ₀)^2
  have hg : 0 < g := sq_pos_of_pos (by linarith)
  have hgle : g ≤ 1 := by dsimp [g]; nlinarith
  have hA : g ≤ A := by
    have h := Real.log_le_sub_one_of_pos hdprod
    dsimp [g, A]
    nlinarith
  have hL : Real.log (1/δ) ≤ A+3 := by
    have heq : 4*δ*(1-δ) = δ * (4*(1-δ)) := by ring
    have hlog' := Real.log_le_sub_one_of_pos (by positivity : 0 < 4*(1-δ))
    dsimp [A]
    rw [heq, Real.log_mul (ne_of_gt hδ) (by positivity), one_div, Real.log_inv]
    linarith
  have hgL : g * Real.log (1/δ) ≤ 4*A := by
    have h := mul_le_mul_of_nonneg_left hL (le_of_lt hg)
    have h' := mul_le_mul_of_nonneg_right hgle (le_trans (le_of_lt hg) hA)
    nlinarith
  have hAT : A ≤ 8 * (T:ℝ) * ε := by
    have h := mul_le_mul_of_nonneg_left hqlog (by positivity : 0 ≤ 2*(T:ℝ))
    dsimp [A]
    norm_num at hlog
    nlinarith
  rw [← mul_div_assoc]
  change (g/32 * Real.log (1/δ)) / ε ≤ (T:ℝ)
  apply (div_le_iff₀ hε).mpr
  nlinarith

private lemma agnostic_state {X : Type*} [Fintype X] (D : X × Bool → ℝ)
    (hD : IsDistribution D) : IsState (agnosticExampleState D) := by
  have hsq : ‖agnosticExampleState D‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, ← hD.2]
    apply Finset.sum_congr rfl
    intro p _
    simp [agnosticExampleState, Complex.norm_real, Real.sq_sqrt (hD.1 p)]
  unfold IsState
  nlinarith [norm_nonneg (agnosticExampleState D)]

private lemma agnostic_overlap {X : Type*} [Fintype X] [DecidableEq X]
    (C : Finset (X → Bool)) (hC : IsNontrivialClass C)
    (δ ε : ℝ) (hδ : 0 < δ) (hδh : δ ≤ 1/2) (hε : 0 < ε) (hεq : ε < 1/4)
    (T : ℕ) (M : {c // c ∈ C} →
      Matrix (Fin T → X × Bool) (Fin T → X × Bool) ℂ)
    (hM : IsQAgnosticLearner C ε δ T M) :
    (1-4*ε^2)^T ≤ 2*Real.sqrt (δ*(1-δ)) := by
  classical
  obtain ⟨c, hc, d, hd, hne⟩ := Finset.one_lt_card.mp
    (lt_of_lt_of_le (by decide : 1 < 2) hC.1)
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hne
  let D : Bool → X × Bool → ℝ := fun b p =>
    if p.1 = y then (if p.2 = b then 1/2+ε else 1/2-ε) else 0
  have hDn (b : Bool) (p : X × Bool) : 0 ≤ D b p := by
    dsimp [D]
    split_ifs <;> linarith
  have hD (b : Bool) : IsDistribution (D b) := by
    refine ⟨hDn b, ?_⟩
    rw [Fintype.sum_prod_type]
    cases b <;> simp [D] <;> norm_num
  have herr (b : Bool) (h : X → Bool) :
      agnosticError (D b) h = if h y = b then 1/2-ε else 1/2+ε := by
    unfold agnosticError
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    calc
      _ = ∑ z : X, if z = y then
          (if h y = b then 1/2-ε else 1/2+ε) else 0 := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : z = y
        · subst z
          cases b <;> cases hh : h y <;> simp [D, hh]
        · simp [D, hz]
      _ = _ := by simp
  have hopt (e : X → Bool) (he : e ∈ C) : optError (D (e y)) C ≤ 1/2-ε := by
    have hb : BddBelow (Set.range (fun h : {c // c ∈ C} =>
        agnosticError (D (e y)) h.1)) := (Set.finite_range _).bddBelow
    have h := ciInf_le hb (⟨e, he⟩ : {c // c ∈ C})
    change optError (D (e y)) C ≤ agnosticError (D (e y)) e at h
    simpa only [herr, ↓reduceIte] using h
  have hgood (e : X → Bool) (he : e ∈ C) (h : {c // c ∈ C})
      (hh : agnosticError (D (e y)) h.1 ≤ optError (D (e y)) C + ε) :
      h.1 y = e y := by
    by_contra hn
    rw [herr, if_neg hn] at hh
    have ho := hopt e he
    linarith
  let P : {c // c ∈ C} → Prop := fun h => h.1 y = c y
  obtain ⟨B, hB, hB0, hB1⟩ := coarse_grain M hM.1 P
  have h0 : 1-δ ≤ effectProb (B false)
      (pureDensity (tensorPow T (agnosticExampleState (D (c y))))) := by
    rw [hB0]
    exact (hM.2 _ (hD (c y))).trans (event_mono M hM.1 _ _ _ (hgood c hc))
  have h1 : 1-δ ≤ effectProb (B true)
      (pureDensity (tensorPow T (agnosticExampleState (D (d y))))) := by
    rw [hB1]
    apply (hM.2 _ (hD (d y))).trans
    apply event_mono M hM.1
    intro h hh heq
    exact hy (heq.symm.trans (hgood d hd h hh))
  let ψ : Bool → EuclideanSpace ℂ (Fin T → X × Bool) := fun b =>
    if b then tensorPow T (agnosticExampleState (D (d y)))
    else tensorPow T (agnosticExampleState (D (c y)))
  have hψ : ∀ b, IsState (ψ b) := by
    intro b
    cases b <;> apply tensor_state <;> apply agnostic_state <;> apply hD
  have hsucc : 1-δ ≤ ensembleSuccess (fun _ => (1/2 : ℝ)) ψ B := by
    simp only [ensembleSuccess, Fintype.sum_bool, ψ, Bool.false_eq_true, ↓reduceIte]
    linarith
  have hov := (QAlgorithms.Arunachalam.helstrom_bound ψ hψ B hB).2 δ
    (le_of_lt hδ) hδh hsucc
  let s : ℝ := 2 * Real.sqrt (1/2+ε) * Real.sqrt (1/2-ε)
  have hin : inner ℂ (agnosticExampleState (D (c y)))
      (agnosticExampleState (D (d y))) = (s : ℂ) := by
    rw [PiLp.inner_apply, Fintype.sum_prod_type]
    calc
      _ = ∑ z : X, if z = y then (s : ℂ) else 0 := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : z = y
        · subst z
          cases hc' : c y <;> cases hd' : d y <;>
            simp_all [agnosticExampleState, D, s,
              RCLike.inner_apply, Complex.ofReal_mul, Complex.ofReal_add,
              mul_comm, mul_assoc, two_mul]
        · simp [agnosticExampleState, D, hz]
      _ = _ := by simp
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hssq : s^2 = 1-4*ε^2 := by
    dsimp [s]
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ 1/2+ε),
      Real.sq_sqrt (by linarith : 0 ≤ 1/2-ε)]
  have hs1 : s ≤ 1 := by nlinarith [sq_nonneg ε]
  have hqs : 1-4*ε^2 ≤ s := by nlinarith
  have hnorm : ‖inner ℂ (ψ false) (ψ true)‖ = s^T := by
    dsimp [ψ]
    rw [tensor_inner, hin, ← Complex.ofReal_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hs T)]
  rw [hnorm] at hov
  exact (pow_le_pow_left₀ (by nlinarith : 0 ≤ 1-4*ε^2) hqs T).trans hov

theorem solution :
    ∀ δ₀ : ℝ, 0 < δ₀ → δ₀ < 1 / 2 → ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (n : ℕ) (C : Finset (Qubits n → Bool)), IsNontrivialClass C →
        ∀ δ ε : ℝ, 0 < δ → δ ≤ δ₀ → 0 < ε → ε < 1 / 4 →
          ∀ (T : ℕ) (M : {c // c ∈ C} →
              Matrix (Fin T → Qubits n × Bool) (Fin T → Qubits n × Bool) ℂ),
            IsQAgnosticLearner C ε δ T M → C₀ * (Real.log (1 / δ) / ε ^ 2) ≤ T := by
  intro δ₀ hδ₀ hδ₀h
  refine ⟨(1-2*δ₀)^2/64, div_pos (sq_pos_of_pos (by linarith)) (by norm_num), ?_⟩
  intro n C hC δ ε hδ hδle hε hεq T M hM
  have hε' : 0 < 2*ε^2 := by positivity
  have hεq' : 2*ε^2 < 1/4 := by nlinarith
  have hov := agnostic_overlap C hC δ ε hδ
    (le_trans hδle (le_of_lt hδ₀h)) hε hεq T M hM
  have h := confidence_bound δ₀ δ (2*ε^2) hδ₀ hδ₀h hδ hδle hε' hεq' T (by
    convert hov using 2; ring)
  convert h using 1; ring

