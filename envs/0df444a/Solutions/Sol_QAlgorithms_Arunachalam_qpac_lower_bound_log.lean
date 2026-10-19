-- Prove2me | solution 1 for QAlgorithms.Arunachalam.qpac_lower_bound_log
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T09:34:56.381199+00:00
-- url     : https://prove2.me/submissions/e1981a04-cf33-4c59-b5d8-c6766fdf61ec

import Definitions.Def_QAlgorithms_Defs_Learning
import Theorems.Thm_QAlgorithms_Arunachalam_helstrom_bound
import Mathlib.Analysis.Matrix.PosDef

set_option autoImplicit false
open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix QAlgorithms QAlgorithms.Learning

private lemma concepts_pair {X : Type*} [Fintype X] [DecidableEq X]
    (C : Finset (X → Bool)) (hC : IsNontrivialClass C) :
    ∃ c ∈ C, ∃ d ∈ C, ∃ x y : X, c x = d x ∧ c y ≠ d y := by
  classical
  by_contra hn
  have hcomp (c : X → Bool) (hc : c ∈ C) (d : X → Bool) (hd : d ∈ C)
      (hne : c ≠ d) : d = fun x => !c x := by
    obtain ⟨y, hy⟩ := Function.ne_iff.mp hne
    funext x
    have hx : c x ≠ d x := by
      intro hx
      exact hn ⟨c, hc, d, hd, x, y, hx, hy⟩
    cases hcx : c x <;> cases hdx : d x <;> simp_all
  obtain ⟨c, hc, d, hd, hne⟩ := Finset.one_lt_card.mp (lt_of_lt_of_le (by decide : 1 < 2) hC.1)
  apply hC.2
  refine ⟨c, ?_⟩
  have hd' := hcomp c hc d hd hne
  apply Finset.ext
  intro e
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro he
    by_cases hec : e = c
    · exact Or.inl hec
    · exact Or.inr (hcomp c hc e he (Ne.symm hec))
  · rintro (rfl | rfl)
    · exact hc
    · simpa only [hd'] using hd

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

private lemma example_inner {X : Type*} [Fintype X] (c d : X → Bool) (D : X → ℝ)
    (hD : ∀ i, 0 ≤ D i) :
    inner ℂ (exampleState c D) (exampleState d D) =
      ((∑ i, if c i = d i then D i else 0 : ℝ) : ℂ) := by
  classical
  rw [PiLp.inner_apply, Fintype.sum_prod_type, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_bool]
  cases hc : c i <;> cases hd : d i <;>
    simp [exampleState, hc, hd, ← Complex.ofReal_pow, Real.sq_sqrt (hD i)]

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

private lemma pac_overlap {X : Type*} [Fintype X] [DecidableEq X]
    (C : Finset (X → Bool)) (hC : IsNontrivialClass C)
    (δ ε : ℝ) (hδ : 0 < δ) (hδh : δ ≤ 1/2) (hε : 0 < ε) (hεq : ε < 1/4)
    (T : ℕ) (M : (X → Bool) → Matrix (Fin T → X × Bool) (Fin T → X × Bool) ℂ)
    (hM : IsQPACLearner C ε δ T M) :
    (1-2*ε)^T ≤ 2*Real.sqrt (δ*(1-δ)) := by
  classical
  obtain ⟨c, hc, d, hd, x, y, hx, hy⟩ := concepts_pair C hC
  have hxy : x ≠ y := by intro h; subst y; exact hy hx
  let D : X → ℝ := fun z => (if z = x then 1-2*ε else 0) +
    (if z = y then 2*ε else 0)
  have hDn (z : X) : 0 ≤ D z := by
    dsimp [D]
    split_ifs <;> linarith
  have hD : IsDistribution D := by
    refine ⟨hDn, ?_⟩
    simp [D, Finset.sum_add_distrib]
  have hDy : D y = 2*ε := by simp [D, Ne.symm hxy]
  have hgood (e h : X → Bool) (hh : pacError D e h ≤ ε) : h y = e y := by
    by_contra hn
    have hmem : y ∈ Finset.univ.filter (fun z => h z ≠ e z) := by simp [hn]
    have hbound := Finset.single_le_sum (fun z (_ : z ∈ Finset.univ.filter
      (fun z => h z ≠ e z)) => hDn z) hmem
    change D y ≤ pacError D e h at hbound
    rw [hDy] at hbound
    linarith
  let P : (X → Bool) → Prop := fun h => h y = c y
  obtain ⟨B, hB, hB0, hB1⟩ := coarse_grain M hM.1 P
  have h0 : 1-δ ≤ effectProb (B false) (pureDensity (tensorPow T (exampleState c D))) := by
    rw [hB0]
    exact (hM.2 c hc D hD).trans (event_mono M hM.1 _ _ _ (hgood c))
  have h1 : 1-δ ≤ effectProb (B true) (pureDensity (tensorPow T (exampleState d D))) := by
    rw [hB1]
    apply (hM.2 d hd D hD).trans
    apply event_mono M hM.1
    intro h hh heq
    exact hy (heq.symm.trans (hgood d h hh))
  let ψ : Bool → EuclideanSpace ℂ (Fin T → X × Bool) :=
    fun b => if b then tensorPow T (exampleState d D) else tensorPow T (exampleState c D)
  have hψ : ∀ b, IsState (ψ b) := by
    intro b
    cases b <;> apply tensor_state <;> exact exampleState_norm hD _
  have hsucc : 1-δ ≤ ensembleSuccess (fun _ => (1/2 : ℝ)) ψ B := by
    simp only [ensembleSuccess, Fintype.sum_bool, ψ, Bool.false_eq_true, ↓reduceIte]
    linarith
  have hov := (QAlgorithms.Arunachalam.helstrom_bound ψ hψ B hB).2 δ
    (le_of_lt hδ) hδh hsucc
  have hin : inner ℂ (exampleState c D) (exampleState d D) = ((1-2*ε : ℝ) : ℂ) := by
    rw [example_inner c d D hDn]
    congr 1
    calc
      _ = ∑ z : X, if z = x then 1-2*ε else 0 := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases hzx : z = x
        · subst z; simp [D, hx, hxy]
        · by_cases hzy : z = y
          · subst z; simp [D, hy, Ne.symm hxy]
          · simp [D, hzx, hzy]
      _ = _ := by simp
  have hnorm : ‖inner ℂ (ψ false) (ψ true)‖ = (1-2*ε)^T := by
    dsimp [ψ]
    rw [tensor_inner, hin, ← Complex.ofReal_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by linarith) T)]
  rwa [hnorm] at hov

theorem solution :
    ∀ δ₀ : ℝ, 0 < δ₀ → δ₀ < 1 / 2 → ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (n : ℕ) (C : Finset (Qubits n → Bool)), IsNontrivialClass C →
        ∀ δ ε : ℝ, 0 < δ → δ ≤ δ₀ → 0 < ε → ε < 1 / 4 →
          ∀ (T : ℕ) (M : (Qubits n → Bool) →
              Matrix (Fin T → Qubits n × Bool) (Fin T → Qubits n × Bool) ℂ),
            IsQPACLearner C ε δ T M → C₀ * (Real.log (1 / δ) / ε) ≤ T := by
  intro δ₀ hδ₀ hδ₀h
  refine ⟨(1-2*δ₀)^2/32, div_pos (sq_pos_of_pos (by linarith)) (by norm_num), ?_⟩
  intro n C hC δ ε hδ hδle hε hεq T M hM
  apply confidence_bound δ₀ δ ε hδ₀ hδ₀h hδ hδle hε hεq T
  exact pac_overlap C hC δ ε hδ (le_trans hδle (le_of_lt hδ₀h)) hε hεq T M hM
