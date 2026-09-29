-- Prove2me | solution 1 for Rudin.ch10_closed_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-19T01:01:02.428361+00:00
-- url     : https://prove2.me/submissions/868b68b2-fc7e-4bde-add6-5ca81c315ce0

import Mathlib
import Definitions.Def_Rudin_ch10_forms

open MeasureTheory

namespace RudinCP

open Rudin

/-- The test surface used to localize: near `x` it is the affine simplex of size `ε` spanned by
the coordinate directions `e_{i_1}, …, e_{i_k}`, bent by `arctan` so that its image stays in a
small ball around `x`. -/
noncomputable def testMap {k n : ℕ} (x : Fin n → ℝ) (i : Fin k → Fin n) (ε : ℝ) :
    (Fin k → ℝ) → (Fin n → ℝ) :=
  fun u c => x c + ε * ∑ j : Fin k, (if i j = c then Real.arctan (u j) else 0)

lemma testMap_contDiff {k n : ℕ} (x : Fin n → ℝ) (i : Fin k → Fin n) (ε : ℝ) :
    ContDiff ℝ 1 (testMap x i ε) := by
  refine contDiff_pi.2 fun c => contDiff_const.add (contDiff_const.mul ?_)
  refine ContDiff.sum fun j _ => ?_
  by_cases hc : i j = c
  · have harctan : ContDiff ℝ 1 (fun u : Fin k → ℝ => Real.arctan (u j)) :=
      Real.contDiff_arctan.comp (contDiff_pi.mp contDiff_id j)
    simpa [hc] using harctan
  · simpa [hc] using (contDiff_const : ContDiff ℝ 1 fun _ : Fin k → ℝ => (0 : ℝ))

lemma testMap_dist_le {k n : ℕ} (x : Fin n → ℝ) (i : Fin k → Fin n) {ε : ℝ} (hε : 0 < ε)
    (u : Fin k → ℝ) : dist (testMap x i ε u) x ≤ ε * (k * (Real.pi / 2)) := by
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  refine (dist_pi_le_iff (by positivity)).2 fun c => ?_
  have habs : |∑ j : Fin k, (if i j = c then Real.arctan (u j) else 0)| ≤ k * (Real.pi / 2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ j ∈ (Finset.univ : Finset (Fin k)),
        |if i j = c then Real.arctan (u j) else 0| ≤ Real.pi / 2 := by
      intro j _
      by_cases hc : i j = c
      · simp only [hc, abs_le]
        exact ⟨(Real.neg_pi_div_two_lt_arctan (u j)).le, (Real.arctan_lt_pi_div_two (u j)).le⟩
      · simpa [hc] using hpi
    simpa using Finset.sum_le_sum this
  have : dist (testMap x i ε u c) (x c)
      = |ε| * |∑ j : Fin k, (if i j = c then Real.arctan (u j) else 0)| := by
    simp [testMap]
  rw [this, abs_of_pos hε]
  exact mul_le_mul_of_nonneg_left habs hε.le

lemma hasFDerivAt_testMap_apply {k n : ℕ} (x : Fin n → ℝ) (i : Fin k → Fin n) (ε : ℝ)
    (c : Fin n) (u : Fin k → ℝ) :
    HasFDerivAt (fun v => testMap x i ε v c)
      (ε • ∑ j : Fin k, (if i j = c then (1 + (u j) ^ 2)⁻¹ else 0) •
        (ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ)) u := by
  have h : ∀ j ∈ (Finset.univ : Finset (Fin k)),
      HasFDerivAt (fun v : Fin k → ℝ => if i j = c then Real.arctan (v j) else 0)
        ((if i j = c then (1 + (u j) ^ 2)⁻¹ else 0) •
          (ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ)) u := by
    intro j _
    by_cases hc : i j = c
    · simp only [hc]
      have h := (Real.hasDerivAt_arctan (u j)).comp_hasFDerivAt u
        ((ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ).hasFDerivAt)
      simpa [Function.comp_def, one_div] using h
    · simp only [if_neg hc, zero_smul]
      exact hasFDerivAt_const (0 : ℝ) u
  have hsum := HasFDerivAt.sum h
  have hmul := hsum.const_mul ε
  have hadd := hmul.const_add (x c)
  simpa [testMap, Finset.smul_sum] using hadd

lemma partialDeriv_testMap {k n : ℕ} (x : Fin n → ℝ) (i : Fin k → Fin n) (ε : ℝ)
    (c : Fin n) (t : Fin k) (u : Fin k → ℝ) :
    partialDeriv (fun v => testMap x i ε v c) t u
      = ε * (if i t = c then (1 + (u t) ^ 2)⁻¹ else 0) := by
  rw [partialDeriv, (hasFDerivAt_testMap_apply x i ε c u).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.proj_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single t] <;> simp +contextual [eq_comm]

lemma jacobian_testMap {k n : ℕ} (x : Fin n → ℝ) (i : Fin k → Fin n) (ε : ℝ)
    (l : Fin k → Fin n) (u : Fin k → ℝ) :
    jacobian (testMap x i ε) l u
      = (∏ t : Fin k, ε * (1 + (u t) ^ 2)⁻¹)
        * (Matrix.of fun r t : Fin k => if i t = l r then (1 : ℝ) else 0).det := by
  have hentry : (Matrix.of fun r t : Fin k => partialDeriv (fun v => testMap x i ε v (l r)) t u)
      = Matrix.of fun r t : Fin k => (ε * (1 + (u t) ^ 2)⁻¹)
          * (if i t = l r then (1 : ℝ) else 0) := by
    ext r t
    rw [Matrix.of_apply, Matrix.of_apply, partialDeriv_testMap]
    by_cases h : i t = l r <;> simp [h]
  have hrow := Matrix.det_mul_row (fun t : Fin k => ε * (1 + (u t) ^ 2)⁻¹)
    (Matrix.of fun r t : Fin k => if i t = l r then (1 : ℝ) else 0)
  rw [jacobian, hentry]
  simpa using hrow

lemma sum_det_indicator {k n : ℕ} (c : (Fin k → Fin n) → ℝ) (i : Fin k → Fin n) :
    ∑ l : Fin k → Fin n,
        c l * (Matrix.of fun r t : Fin k => if i t = l r then (1 : ℝ) else 0).det
      = ∑ τ : Equiv.Perm (Fin k), (Equiv.Perm.sign τ : ℝ) * c (fun r => i (τ r)) := by
  have hdet : ∀ l : Fin k → Fin n,
      (Matrix.of fun r t : Fin k => if i t = l r then (1 : ℝ) else 0).det
        = ∑ τ : Equiv.Perm (Fin k), (Equiv.Perm.sign τ : ℝ) *
            ∏ r : Fin k, (if i r = l (τ r) then (1 : ℝ) else 0) := by
    intro l
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp [Units.smul_def]
  have hinner : ∀ τ : Equiv.Perm (Fin k),
      ∑ l : Fin k → Fin n, c l * ∏ r : Fin k, (if i r = l (τ r) then (1 : ℝ) else 0)
        = c (fun s => i (τ.symm s)) := by
    intro τ
    rw [Finset.sum_eq_single (fun s => i (τ.symm s))]
    · simp
    · intro l _ hl
      have : ∃ s, l s ≠ i (τ.symm s) := by
        by_contra hcon
        push_neg at hcon
        exact hl (funext fun s => hcon s)
      obtain ⟨s, hs⟩ := this
      have hprod : ∏ r : Fin k, (if i r = l (τ r) then (1 : ℝ) else 0) = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_univ (τ.symm s)) ?_
        simp only [Equiv.apply_symm_apply]
        exact if_neg fun h => hs h.symm
      rw [hprod, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  calc ∑ l : Fin k → Fin n,
        c l * (Matrix.of fun r t : Fin k => if i t = l r then (1 : ℝ) else 0).det
      = ∑ l : Fin k → Fin n, ∑ τ : Equiv.Perm (Fin k), (Equiv.Perm.sign τ : ℝ) *
          (c l * ∏ r : Fin k, (if i r = l (τ r) then (1 : ℝ) else 0)) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hdet l, Finset.mul_sum]
        exact Finset.sum_congr rfl fun τ _ => by ring
    _ = ∑ τ : Equiv.Perm (Fin k), (Equiv.Perm.sign τ : ℝ) *
          ∑ l : Fin k → Fin n, c l * ∏ r : Fin k, (if i r = l (τ r) then (1 : ℝ) else 0) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun τ _ => by rw [Finset.mul_sum]
    _ = ∑ τ : Equiv.Perm (Fin k), (Equiv.Perm.sign τ : ℝ) * c (fun s => i (τ.symm s)) := by
        exact Finset.sum_congr rfl fun τ _ => by rw [hinner τ]
    _ = ∑ τ : Equiv.Perm (Fin k), (Equiv.Perm.sign τ : ℝ) * c (fun r => i (τ r)) := by
        refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin k))) _ _ fun τ => ?_
        simp [Equiv.Perm.sign_inv]

/-- The standard simplex is compact. -/
lemma isCompact_stdSimplex (k : ℕ) : IsCompact (Rudin.stdSimplex k) := by
  have hclosed : IsClosed (Rudin.stdSimplex k) := by
    have h : Rudin.stdSimplex k
        = (⋂ i : Fin k, {u : Fin k → ℝ | 0 ≤ u i}) ∩ {u : Fin k → ℝ | ∑ i, u i ≤ 1} := by
      ext u
      simp [Rudin.stdSimplex, Set.mem_iInter]
    rw [h]
    refine IsClosed.inter (isClosed_iInter fun i => ?_) ?_
    · exact isClosed_le continuous_const (continuous_apply i)
    · exact isClosed_le (continuous_finset_sum _ fun i _ => continuous_apply i) continuous_const
  have hsub : Rudin.stdSimplex k ⊆ Set.Icc (0 : Fin k → ℝ) 1 := by
    intro u hu
    obtain ⟨hpos, hsum⟩ := hu
    refine ⟨fun t => hpos t, fun t => ?_⟩
    have : u t ≤ ∑ j, u j :=
      Finset.single_le_sum (fun j _ => hpos j) (Finset.mem_univ t)
    exact this.trans hsum
  exact IsCompact.of_isClosed_subset (isCompact_Icc) hclosed hsub

/-- The standard simplex is measurable. -/
lemma measurableSet_stdSimplex (k : ℕ) : MeasurableSet (Rudin.stdSimplex k) :=
  (isCompact_stdSimplex k).isClosed.measurableSet

/-- The standard simplex has positive volume. -/
lemma volume_stdSimplex_pos (k : ℕ) (hk : 0 < k) :
    0 < MeasureTheory.volume (Rudin.stdSimplex k) := by
  set U : Set (Fin k → ℝ) := {u | (∀ t, 0 < u t) ∧ ∑ t, u t < 1} with hU
  have hUopen : IsOpen U := by
    have h1 : IsOpen {u : Fin k → ℝ | ∀ t, 0 < u t} := by
      have : {u : Fin k → ℝ | ∀ t, 0 < u t} = ⋂ t : Fin k, {u : Fin k → ℝ | 0 < u t} := by
        ext u; simp [Set.mem_iInter]
      rw [this]
      exact isOpen_iInter_of_finite fun t => isOpen_lt continuous_const (continuous_apply t)
    have h2 : IsOpen {u : Fin k → ℝ | ∑ t, u t < 1} :=
      isOpen_lt (continuous_finset_sum _ fun t _ => continuous_apply t) continuous_const
    exact h1.inter h2
  have hUne : U.Nonempty := by
    refine ⟨fun _ => 1 / (2 * k), ⟨fun t => by positivity, ?_⟩⟩
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_one_div, div_lt_one (by positivity)]
    linarith
  have hsub : U ⊆ Rudin.stdSimplex k := by
    intro u hu
    exact ⟨fun t => (hu.1 t).le, hu.2.le⟩
  exact lt_of_lt_of_le (hUopen.measure_pos MeasureTheory.volume hUne)
    (MeasureTheory.measure_mono hsub)

end RudinCP

open Rudin in
theorem solution (m n : ℕ) (E : Set (Fin n → ℝ)) (hE : IsOpen E)
    (ω : KForm (m + 1) n) (hω : ∀ i, ContDiffOn ℝ 1 (ω.coeff i) E)
    (hclosed : ∀ Φ : SimplexSurface (m + 1 + 1) n, ContDiff ℝ 1 Φ.map →
      (∀ u, Φ.map u ∈ E) → integralOverSimplex (extDeriv ω) Φ = 0) :
    ∀ x ∈ E, ∀ i : Fin (m + 1 + 1) → Fin n,
      ∑ σ : Equiv.Perm (Fin (m + 1 + 1)), (Equiv.Perm.sign σ : ℝ) *
        (extDeriv ω).coeff (fun r => i (σ r)) x = 0 := by
  intro x hx i
  classical
  set Q : Set (Fin (m + 1 + 1) → ℝ) := stdSimplex (m + 1 + 1) with hQ
  set A : (Fin n → ℝ) → ℝ := fun y =>
    ∑ σ : Equiv.Perm (Fin (m + 1 + 1)), (Equiv.Perm.sign σ : ℝ) *
      (extDeriv ω).coeff (fun r => i (σ r)) y with hAdef
  show A x = 0
  -- `A` is continuous on `E`, because the coefficients of `dω` are.
  have hcoeff : ∀ j : Fin (m + 1 + 1) → Fin n,
      ContinuousOn (fun y => (extDeriv ω).coeff j y) E := by
    intro j
    have h1 : ContinuousOn (fderiv ℝ (ω.coeff fun r => j r.succ)) E :=
      (hω _).continuousOn_fderiv_of_isOpen hE le_rfl
    exact h1.clm_apply continuousOn_const
  have hAcont : ContinuousOn A E :=
    continuousOn_finset_sum _ fun σ _ => continuousOn_const.mul (hcoeff _)
  -- the weight coming from the derivative of `arctan`
  set w : (Fin (m + 1 + 1) → ℝ) → ℝ := fun u => ∏ t, (1 + (u t) ^ 2)⁻¹ with hwdef
  have hwpos : ∀ u, 0 < w u := fun u => Finset.prod_pos fun t _ => by positivity
  have hwcont : Continuous w := by
    refine continuous_finset_prod _ fun t _ => ?_
    refine (continuous_const.add ((continuous_apply t).pow 2)).inv₀ fun u => ?_
    show (1 : ℝ) + (u t) ^ 2 ≠ 0
    positivity
  have hwint : MeasureTheory.IntegrableOn w Q :=
    hwcont.continuousOn.integrableOn_compact (RudinCP.isCompact_stdSimplex _)
  have hIpos : 0 < ∫ u in Q, w u := by
    rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun u => (hwpos u).le) hwint]
    have hsupp : Function.support w ∩ Q = Q := by
      refine Set.inter_eq_right.2 fun u _ => ?_
      exact ne_of_gt (hwpos u)
    rw [hsupp]
    exact RudinCP.volume_stdSimplex_pos _ (Nat.succ_pos _)
  -- the hypothesis, evaluated on the test surfaces
  have key : ∀ ε : ℝ, 0 < ε → (∀ u, RudinCP.testMap x i ε u ∈ E) →
      ∫ u in Q, w u * A (RudinCP.testMap x i ε u) = 0 := by
    intro ε hε hmem
    have h0 := hclosed ⟨RudinCP.testMap x i ε⟩ (RudinCP.testMap_contDiff x i ε) hmem
    rw [integralOverSimplex] at h0
    have hint : ∀ u : Fin (m + 1 + 1) → ℝ,
        (∑ l : Fin (m + 1 + 1) → Fin n, (extDeriv ω).coeff l (RudinCP.testMap x i ε u)
            * jacobian (RudinCP.testMap x i ε) l u)
          = ε ^ (m + 1 + 1) * (w u * A (RudinCP.testMap x i ε u)) := by
      intro u
      have hprod : (∏ t : Fin (m + 1 + 1), ε * (1 + (u t) ^ 2)⁻¹) = ε ^ (m + 1 + 1) * w u := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      calc (∑ l : Fin (m + 1 + 1) → Fin n, (extDeriv ω).coeff l (RudinCP.testMap x i ε u)
              * jacobian (RudinCP.testMap x i ε) l u)
          = ∑ l : Fin (m + 1 + 1) → Fin n, (∏ t : Fin (m + 1 + 1), ε * (1 + (u t) ^ 2)⁻¹) *
              ((extDeriv ω).coeff l (RudinCP.testMap x i ε u) *
                (Matrix.of fun r t : Fin (m + 1 + 1) =>
                  if i t = l r then (1 : ℝ) else 0).det) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [RudinCP.jacobian_testMap]
            ring
        _ = (∏ t : Fin (m + 1 + 1), ε * (1 + (u t) ^ 2)⁻¹) *
              ∑ l : Fin (m + 1 + 1) → Fin n,
                (extDeriv ω).coeff l (RudinCP.testMap x i ε u) *
                  (Matrix.of fun r t : Fin (m + 1 + 1) =>
                    if i t = l r then (1 : ℝ) else 0).det := by
            rw [Finset.mul_sum]
        _ = ε ^ (m + 1 + 1) * (w u * A (RudinCP.testMap x i ε u)) := by
            rw [hprod, RudinCP.sum_det_indicator
              (fun l => (extDeriv ω).coeff l (RudinCP.testMap x i ε u)) i]
            ring
    simp_rw [hint] at h0
    rw [MeasureTheory.integral_const_mul] at h0
    exact (mul_eq_zero.mp h0).resolve_left (by positivity)
  -- conclusion
  by_contra hne
  have habs : 0 < |A x| := abs_pos.2 hne
  set δ : ℝ := |A x| / 2 with hδdef
  have hδpos : 0 < δ := by positivity
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hE x hx
  obtain ⟨ρ, hρ, hρ'⟩ :=
    Metric.continuousWithinAt_iff.mp (hAcont x hx) δ hδpos
  have hc : (0 : ℝ) < ((m + 1 + 1 : ℝ) * (Real.pi / 2)) := by positivity
  set s : ℝ := min r ρ with hs
  have hspos : 0 < s := lt_min hr hρ
  set ε : ℝ := s / (2 * ((m + 1 + 1 : ℝ) * (Real.pi / 2))) with hεdef
  have hεpos : 0 < ε := by positivity
  have hεsmall : ε * ((m + 1 + 1 : ℝ) * (Real.pi / 2)) < s := by
    have h : ε * ((m + 1 + 1 : ℝ) * (Real.pi / 2)) = s / 2 := by
      rw [hεdef]
      field_simp
    rw [h]
    linarith
  have hdist : ∀ u, dist (RudinCP.testMap x i ε u) x < s := by
    intro u
    have h := RudinCP.testMap_dist_le x i hεpos u
    have hcast : ((m + 1 + 1 : ℕ) : ℝ) = (m + 1 + 1 : ℝ) := by push_cast; ring
    rw [hcast] at h
    exact lt_of_le_of_lt h hεsmall
  have hmemE : ∀ u, RudinCP.testMap x i ε u ∈ E := by
    intro u
    exact hball (Metric.mem_ball.2 (lt_of_lt_of_le (hdist u) (min_le_left _ _)))
  have hclose : ∀ u, |A (RudinCP.testMap x i ε u) - A x| ≤ δ := by
    intro u
    have := hρ' (hmemE u) (lt_of_lt_of_le (hdist u) (min_le_right _ _))
    rw [Real.dist_eq] at this
    exact this.le
  have hkey := key ε hεpos hmemE
  -- integrability of the two pieces
  have hcompQ : IsCompact Q := RudinCP.isCompact_stdSimplex _
  have hAQcont : ContinuousOn (fun u => A (RudinCP.testMap x i ε u)) Q :=
    hAcont.comp (RudinCP.testMap_contDiff x i ε).continuous.continuousOn fun u _ => hmemE u
  have hf1 : MeasureTheory.IntegrableOn
      (fun u => w u * A (RudinCP.testMap x i ε u)) Q :=
    (hwcont.continuousOn.mul hAQcont).integrableOn_compact hcompQ
  have hf2 : MeasureTheory.IntegrableOn (fun u => w u * A x) Q := hwint.mul_const _
  have hsplit : (∫ u in Q, w u * (A (RudinCP.testMap x i ε u) - A x))
      = (∫ u in Q, w u * A (RudinCP.testMap x i ε u)) - ∫ u in Q, w u * A x := by
    rw [← MeasureTheory.integral_sub hf1 hf2]
    refine MeasureTheory.setIntegral_congr_fun (RudinCP.measurableSet_stdSimplex _) fun u _ => ?_
    ring
  have hconst : (∫ u in Q, w u * A x) = (∫ u in Q, w u) * A x := by
    rw [MeasureTheory.integral_mul_const]
  have hbound : |∫ u in Q, w u * (A (RudinCP.testMap x i ε u) - A x)| ≤ δ * ∫ u in Q, w u := by
    have hle : ∀ u, ‖w u * (A (RudinCP.testMap x i ε u) - A x)‖ ≤ δ * w u := by
      intro u
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hwpos u), mul_comm]
      exact mul_le_mul_of_nonneg_right (hclose u) (hwpos u).le
    have := MeasureTheory.norm_integral_le_of_norm_le (hwint.const_mul δ)
      (Filter.Eventually.of_forall fun u => hle u)
    rwa [Real.norm_eq_abs, MeasureTheory.integral_const_mul] at this
  rw [hsplit, hkey, hconst, zero_sub, abs_neg, abs_mul, abs_of_pos hIpos] at hbound
  nlinarith [hIpos, habs]

