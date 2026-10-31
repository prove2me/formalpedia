-- Prove2me | solution 1 for PersonalizedRM.RevenueGap.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T18:41:36.344787+00:00
-- url     : https://prove2.me/submissions/bde23831-50f1-41b3-8fe9-17a1f21d2ed5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PersonalizedRM_RevenueGap_Model
import Theorems.Thm_PersonalizedRM_RevenueGap_lemma_1
import Theorems.Thm_PersonalizedRM_RevenueGap_lemma_2
import Theorems.Thm_PersonalizedRM_RevenueGap_eq_5

open MeasureTheory ProbabilityTheory
open PersonalizedRM.RevenueGap

lemma PRM_aux_diffProb {J d : ℕ} (z : Fin d → ℝ) (S : Finset (Fin J)) (p : Fin J → ℝ)
    (o : Option (Fin J)) :
    Differentiable ℝ (fun θ : Param J d => Real.log (choiceProb θ z S p o)) := by
  have hu : ∀ l, Differentiable ℝ (fun θ : Param J d => utility θ z p l) := by
    intro l; unfold utility; fun_prop
  have hD : Differentiable ℝ (fun θ : Param J d => 1 + ∑ l ∈ S, Real.exp (utility θ z p l)) := by
    fun_prop
  have hDpos : ∀ θ : Param J d, 0 < 1 + ∑ l ∈ S, Real.exp (utility θ z p l) := fun θ => by
    have := Finset.sum_nonneg (s := S) (fun l _ => (Real.exp_pos (utility θ z p l)).le); linarith
  have h2 : ∀ θ : Param J d, 1 + ∑ l ∈ S, Real.exp (utility θ z p l) ≠ 0 :=
    fun θ => (hDpos θ).ne'
  have hDi : Differentiable ℝ (fun θ : Param J d => (1 + ∑ l ∈ S, Real.exp (utility θ z p l))⁻¹) :=
    fun θ => (hD θ).inv (h2 θ)
  cases o with
  | none =>
    simp only [choiceProb, one_div]
    exact fun θ => (hDi θ).log (inv_pos.mpr (hDpos θ)).ne'
  | some j =>
    by_cases hj : j ∈ S
    · simp only [choiceProb, hj, if_true, div_eq_mul_inv]
      exact fun θ => (((hu j θ).exp).mul (hDi θ)).log
        (mul_pos (Real.exp_pos _) (inv_pos.mpr (hDpos θ))).ne'
    · simp only [choiceProb, hj, if_false]
      exact differentiable_const _

lemma PRM_aux_diffNLL {n J d : ℕ} (S : Fin n → Finset (Fin J)) (z : Fin n → Fin d → ℝ)
    (p : Fin n → Fin J → ℝ) (y : Fin n → Option (Fin J)) :
    Differentiable ℝ (negLogLik S z p y) := by
  unfold negLogLik
  have : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      Differentiable ℝ (fun θ : Param J d => Real.log (choiceProb θ (z i) (S i) (p i) (y i))) :=
    fun i _ => PRM_aux_diffProb (z i) (S i) (p i) (y i)
  exact (Differentiable.fun_sum this).const_mul _

lemma PRM_aux_norm_le_l1 {J d : ℕ} (x : Param J d) : ‖x‖ ≤ l1norm x := by
  rw [EuclideanSpace.norm_eq, l1norm]
  apply Real.sqrt_le_iff.mpr
  refine ⟨Finset.sum_nonneg (fun i _ => abs_nonneg _), ?_⟩
  simp only [Real.norm_eq_abs]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => abs_nonneg _)

theorem solution : ∀ ψ : ℝ, 0 < ψ → ∃ Cψ : ℝ, 0 < Cψ ∧ ∀ R : ℝ, 0 < R →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (n J d : ℕ) (S : Fin n → Finset (Fin J)) (z : Fin n → Ω → Fin d → ℝ)
      (price : Fin n → Ω → Fin J → ℝ) (u : Fin n → Ω → ℝ) (y : Fin n → Ω → Option (Fin J))
      (θstar : Param J d) (θhat : Ω → Param J d) (pmin ν ρ : ℝ),
      0 < n →
      Assumption1 P S z price u y θstar pmin ψ → Assumption2 P S z price ν ρ →
      l1norm θstar ≤ R →
      (∀ ω, IsConstrainedMLE R
        (negLogLik S (fun i => z i ω) (fun i => price i ω) (fun i => y i ω)) (θhat ω)) →
      4 * Cψ * Real.log (ν * n) / (ν * min ρ 1 ^ 2) ≤ n →
      P {ω | ¬ ‖θhat ω - θstar‖ ≤
          2 * (1 + Real.exp (-R) + ((J : ℝ) - 1) * Real.exp R) ^ 2 / (Real.exp (-R) * ν * ρ) *
            Real.sqrt (2 * J * ((d : ℝ) + 1) * Real.log (2 * (n : ℝ) * J * ((d : ℝ) + 1)) / n)}
        ≤ ENNReal.ofReal (1 / n + 2 * J / (ν * n)) := by
  intro ψ hψ
  obtain ⟨C₂, hC₂, hL2⟩ := lemma_2 ψ hψ
  refine ⟨max C₂ (Real.exp (2 * C₂)), lt_max_of_lt_left hC₂, fun R hR => ?_⟩
  intro Ω _ P _ n J d S z price u y θstar θhat pmin ν ρ hn hA1 hA2 hR' hmle hsize
  set Cψ := max C₂ (Real.exp (2 * C₂)) with hCψ
  have hν : 0 < ν := hA2.nu_pos
  have hρ : 0 < ρ := hA2.rho_pos
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rcases Nat.eq_zero_or_pos J with hJ | hJ
  · -- no products: the parameter space is trivial and the bad event is empty
    subst hJ
    have : {ω | ¬ ‖θhat ω - θstar‖ ≤
        2 * (1 + Real.exp (-R) + (((0 : ℕ) : ℝ) - 1) * Real.exp R) ^ 2 /
          (Real.exp (-R) * ν * ρ) * Real.sqrt (2 * ((0 : ℕ) : ℝ) * ((d : ℝ) + 1) *
            Real.log (2 * (n : ℝ) * ((0 : ℕ) : ℝ) * ((d : ℝ) + 1)) / n)} = ∅ := by
      ext ω; simp [EuclideanSpace.norm_eq]
    rw [this, measure_empty]; exact zero_le
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  let j0 : Fin J := ⟨0, hJ⟩
  -- ν ≤ 1
  have hcard_le : ((offered S j0).card : ℝ) ≤ n := by
    have := Finset.card_le_univ (offered S j0); simp at this; exact_mod_cast this
  have hcard_pos : (0 : ℝ) < (offered S j0).card :=
    lt_of_lt_of_le (mul_pos hν hnpos) (hA2.offered_ge j0)
  have hνle : ν ≤ 1 := by
    have := (hA2.offered_ge j0).trans hcard_le
    by_contra h; push_neg at h; nlinarith
  -- ρ ≤ 1, since the features are bounded by 1
  have hx : ∀ i ω k, |featPrice (z i ω) (price i ω j0) k| ≤ 1 := by
    intro i ω k
    have hp := hA1.price_mem i ω
    simp only [priceBox, Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies] at hp
    refine Fin.lastCases ?_ (fun l => ?_) k
    · simp only [featPrice, Fin.snoc_last]; rw [abs_le]
      constructor <;> linarith [(hp j0).1, (hp j0).2, hA1.pmin_pos]
    · simp only [featPrice, Fin.snoc_castSucc]; exact hA1.z_bdd i ω l
  have hρle : ρ ≤ 1 := by
    have h := hA2.min_eig j0 (Pi.single 0 1)
    have e1 : ∑ k, (Pi.single 0 1 : Fin (d + 1) → ℝ) k ^ 2 = 1 := by simp [Pi.single_apply]
    have e2 : ∀ x : Fin (d + 1) → ℝ, ∑ k, (Pi.single 0 1 : Fin (d + 1) → ℝ) k * x k = x 0 := by
      intro x; simp [Pi.single_apply]
    simp only [e1, e2, mul_one] at h
    have hint : ∀ i, ∫ ω, featPrice (z i ω) (price i ω j0) 0 ^ 2 ∂P ≤ 1 := by
      intro i
      have := norm_integral_le_of_norm_le_const (μ := P)
        (f := fun ω => featPrice (z i ω) (price i ω j0) 0 ^ 2) (C := 1)
        (Filter.Eventually.of_forall fun ω => by
          simp only [Real.norm_eq_abs, abs_pow]
          nlinarith [abs_nonneg (featPrice (z i ω) (price i ω j0) 0), hx i ω 0])
      simp at this
      exact (le_abs_self _).trans this
    have hsum : ∑ i ∈ offered S j0, ∫ ω, featPrice (z i ω) (price i ω j0) 0 ^ 2 ∂P ≤
        (offered S j0).card := by
      calc _ ≤ ∑ i ∈ offered S j0, (1 : ℝ) := Finset.sum_le_sum fun i _ => hint i
        _ = _ := by simp
    calc ρ ≤ _ := h
      _ ≤ 1 / ((offered S j0).card : ℝ) * (offered S j0).card :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 1 := by field_simp
  have hmin : min ρ 1 = ρ := min_eq_left hρle
  rw [hmin] at hsize
  by_cases htriv : ν * n ≤ 2 * J
  · -- the claimed probability bound is at least 1
    calc P _ ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have : 1 ≤ 2 * J / (ν * n) := (one_le_div (by positivity)).mpr htriv
        have : 0 ≤ 1 / (n : ℝ) := by positivity
        linarith
  push_neg at htriv
  have hlog2 : Real.log 2 ≤ Real.log (ν * n) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlog2pos : (1 : ℝ) / 4 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlogνn : 0 ≤ Real.log (ν * n) := by linarith
  have hνρ : 0 < ν * ρ ^ 2 := by positivity
  have hνρ1 : ν * ρ ^ 2 ≤ 1 := by
    have : ρ ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hCψ2 : Real.exp (2 * C₂) ≤ Cψ := le_max_right _ _
  have hCψ1 : C₂ ≤ Cψ := le_max_left _ _
  -- n is at least exp(2 C₂)
  have hn_big : Real.exp (2 * C₂) ≤ n := by
    have h1 : 4 * Cψ * Real.log (ν * n) ≤ 4 * Cψ * Real.log (ν * n) / (ν * ρ ^ 2) :=
      le_div_self (by positivity) hνρ hνρ1
    have h2 : Real.exp (2 * C₂) ≤ 4 * Cψ * Real.log (ν * n) := by
      have := Real.exp_pos (2 * C₂)
      nlinarith
    linarith
  set L := Real.log (2 * (n : ℝ) * J * ((d : ℝ) + 1)) with hL
  have hLbig : 2 * C₂ ≤ L := by
    have hlogn : 2 * C₂ ≤ Real.log n := by
      rw [← Real.log_exp (2 * C₂)]; exact Real.log_le_log (Real.exp_pos _) hn_big
    have : Real.log n ≤ L := Real.log_le_log hnpos (by
      have : (1 : ℝ) ≤ 2 * J * ((d : ℝ) + 1) := by
        have : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
        nlinarith
      nlinarith)
    linarith
  have hL0 : 0 ≤ L := by linarith
  set K := 1 + Real.exp (-R) + ((J : ℝ) - 1) * Real.exp R with hK
  have hK1 : 1 ≤ K := by
    have : 0 ≤ ((J : ℝ) - 1) * Real.exp R := mul_nonneg (by linarith) (Real.exp_pos _).le
    have := Real.exp_pos (-R)
    linarith
  by_cases hcase : 4 * C₂ * ((J : ℝ) * ((d : ℝ) + 1)) / min ρ 1 ^ 2 ≤ ν * n
  · -- main case: Lemma 1 and Lemma 2 give the result through (5)
    have hlem2hyp : 4 * C₂ * Real.log (ν * n) / (ν * min ρ 1 ^ 2) ≤ n := by
      rw [hmin]
      refine le_trans ?_ hsize
      apply div_le_div_of_nonneg_right _ hνρ.le
      exact mul_le_mul_of_nonneg_right (by linarith) hlogνn
    have h2 := hL2 P n J d S z price u y θstar pmin ν ρ R hn hR hA1 hA2 hlem2hyp hcase
    have h1 := lemma_1 P S z price u y θstar pmin ψ hn hA1
    refine le_trans (measure_mono ?_) (le_trans (measure_union_le _ _)
      ((add_le_add h1 h2).trans_eq
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm))
    intro ω hω
    by_contra hc
    rw [Set.mem_union, not_or] at hc
    obtain ⟨hg, hsc⟩ := hc
    rw [Set.mem_setOf_eq, not_not] at hg hsc
    rw [Set.mem_setOf_eq] at hω
    apply hω
    have hη : 0 < etaSC J R ν ρ := by
      unfold etaSC cMin; have := Real.exp_pos (-R); positivity
    have hstar : θstar ∈ {θ : Param J d | l1norm θ ≤ R} := hR'
    have hhat : θhat ω ∈ {θ : Param J d | l1norm θ ≤ R} := (hmle ω).1
    have hminOn : IsMinOn (negLogLik S (fun i => z i ω) (fun i => price i ω) (fun i => y i ω))
        {θ : Param J d | l1norm θ ≤ R} (θhat ω) := fun θ hθ => (hmle ω).2 θ hθ
    have h5 := eq_5 {θ : Param J d | l1norm θ ≤ R} _ (PRM_aux_diffNLL S _ _ _) _ hη hsc θstar
      (θhat ω) hstar hhat hminOn _ (fun k => hg k.1 k.2)
    have hcardR : ((Fintype.card (Fin J × Fin (d + 1)) : ℕ) : ℝ) = (J : ℝ) * ((d : ℝ) + 1) := by
      simp
    have hgL : Real.log (2 * (n : ℝ) * J * ((d : ℝ) + 1)) = L := rfl
    rw [hcardR, hgL] at h5
    refine h5.trans (le_of_eq ?_)
    rw [show (2 : ℝ) * J * ((d : ℝ) + 1) * L / n = ((J : ℝ) * ((d : ℝ) + 1)) * (2 * L / n) by ring,
      Real.sqrt_mul (by positivity) (2 * L / n)]
    unfold etaSC cMin
    have := Real.exp_pos (-R)
    have hK0 : K ≠ 0 := by linarith
    rw [← hK]
    field_simp
  · -- degenerate case: the bound exceeds the diameter 2R of the ℓ1 ball
    clear_value K L
    push_neg at hcase
    rw [hmin] at hcase
    have hsq : ν * ρ ≤ Real.sqrt (2 * J * ((d : ℝ) + 1) * L / n) := by
      apply Real.le_sqrt_of_sq_le
      rw [le_div_iff₀ hnpos]
      have hc' : ν * n * ρ ^ 2 < 4 * C₂ * ((J : ℝ) * ((d : ℝ) + 1)) := by
        rwa [lt_div_iff₀ (by positivity)] at hcase
      have hJd : 0 ≤ (J : ℝ) * ((d : ℝ) + 1) := by positivity
      have hA : (ν * ρ) ^ 2 * n ≤ ν * n * ρ ^ 2 := by
        have : 0 ≤ ν * n * ρ ^ 2 := by positivity
        nlinarith
      have hB : 4 * C₂ * ((J : ℝ) * ((d : ℝ) + 1)) ≤ 2 * J * ((d : ℝ) + 1) * L := by
        nlinarith
      linarith
    have hbound : 2 * R ≤ 2 * K ^ 2 / (Real.exp (-R) * ν * ρ) *
        Real.sqrt (2 * J * ((d : ℝ) + 1) * L / n) := by
      have he := Real.exp_pos (-R)
      have hfac : 0 ≤ 2 * K ^ 2 / (Real.exp (-R) * ν * ρ) := by positivity
      calc 2 * R ≤ 2 * K ^ 2 * Real.exp R := by
            have h1 := Real.add_one_le_exp R
            have h2 : 1 ≤ K ^ 2 := one_le_pow₀ hK1
            have h3 : Real.exp R ≤ K ^ 2 * Real.exp R :=
              le_mul_of_one_le_left (Real.exp_pos R).le h2
            linarith
        _ = 2 * K ^ 2 / (Real.exp (-R) * ν * ρ) * (ν * ρ) := by
            have hE : Real.exp (-R) * Real.exp R = 1 := by rw [← Real.exp_add]; simp
            rw [div_mul_eq_mul_div, eq_div_iff (by positivity)]
            linear_combination (2 * K ^ 2 * ν * ρ) * hE
        _ ≤ _ := mul_le_mul_of_nonneg_left hsq hfac
    refine le_trans (measure_mono (t := ∅) ?_) (by rw [measure_empty]; exact zero_le)
    intro ω hω
    rw [Set.mem_setOf_eq] at hω
    apply hω
    calc ‖θhat ω - θstar‖ ≤ ‖θhat ω‖ + ‖θstar‖ := norm_sub_le _ _
      _ ≤ l1norm (θhat ω) + l1norm θstar :=
          add_le_add (PRM_aux_norm_le_l1 _) (PRM_aux_norm_le_l1 _)
      _ ≤ 2 * R := by linarith [(hmle ω).1]
      _ ≤ _ := hbound
