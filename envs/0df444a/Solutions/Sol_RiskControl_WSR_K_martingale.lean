-- Prove2me | solution 1 for RiskControl.WSR.K_martingale
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T22:30:30.621312+00:00
-- url     : https://prove2.me/submissions/e237a256-c6ad-4a20-8f77-7dbdd4fe7183

import Mathlib
import Definitions.Def_RiskControl_WSR_Process

open MeasureTheory

open RiskControl.WSR

namespace Prove2WSRSubmission

namespace RiskControl.WSR.Lead34KMart

open ProbabilityTheory

/-- For `i < n`, the `(i+1)`-st loss is the `i`-th coordinate. -/
theorem obs_succ {n : ℕ} (ω : Fin n → ℝ) {i : ℕ} (hi : i < n) : obs ω (i + 1) = ω ⟨i, hi⟩ :=
  dif_pos (⟨by omega, by omega⟩ : 1 ≤ i + 1 ∧ i + 1 ≤ n)

/-- Every loss lies in `[0, 1]` once every coordinate does. -/
theorem obs_mem_Icc {n : ℕ} {ω : Fin n → ℝ} (hω : ∀ k : Fin n, ω k ∈ Set.Icc (0 : ℝ) 1) (j : ℕ) :
    obs ω j ∈ Set.Icc (0 : ℝ) 1 := by
  unfold obs
  split_ifs
  · exact hω _
  · exact ⟨le_rfl, zero_le_one⟩

theorem nu_nonneg (n : ℕ) (δ : ℝ) (ω : Fin n → ℝ) (j : ℕ) : 0 ≤ nu n δ ω j :=
  le_min zero_le_one (Real.sqrt_nonneg _)

theorem nu_le_one (n : ℕ) (δ : ℝ) (ω : Fin n → ℝ) (j : ℕ) : nu n δ ω j ≤ 1 :=
  min_le_left _ _

/-- `obs · j` is `filt n i`-measurable for `j ≤ i`. -/
theorem obs_measurable {n i j : ℕ} (hji : j ≤ i) :
    Measurable[filt n i] (fun ω : Fin n → ℝ => obs ω j) :=
  (((Filtration.stronglyAdapted_natural (fun i => stronglyMeasurable_obs n i)) j).mono
    ((filt n).mono hji)).measurable

theorem muHat_measurable {n i j : ℕ} (hji : j ≤ i) :
    Measurable[filt n i] (fun ω : Fin n → ℝ => muHat ω j) := by
  show Measurable[filt n i]
    (fun ω : Fin n → ℝ => (1 / 2 + ∑ k ∈ Finset.Icc 1 j, obs ω k) / (1 + (j : ℝ)))
  exact (measurable_const.add (Finset.measurable_sum _ fun k hk =>
    obs_measurable ((Finset.mem_Icc.mp hk).2.trans hji))).div_const _

theorem sigmaSqHat_measurable {n i j : ℕ} (hji : j ≤ i) :
    Measurable[filt n i] (fun ω : Fin n → ℝ => sigmaSqHat ω j) := by
  show Measurable[filt n i] (fun ω : Fin n → ℝ =>
    (1 / 4 + ∑ k ∈ Finset.Icc 1 j, (obs ω k - muHat ω k) ^ 2) / (1 + (j : ℝ)))
  exact (measurable_const.add (Finset.measurable_sum _ fun k hk =>
    ((obs_measurable ((Finset.mem_Icc.mp hk).2.trans hji)).sub
      (muHat_measurable ((Finset.mem_Icc.mp hk).2.trans hji))).pow_const 2)).div_const _

/-- The betting fraction `ν_j` is predictable: it depends on the losses up to `j - 1`. -/
theorem nu_measurable {n i j : ℕ} (δ : ℝ) (hji : j - 1 ≤ i) :
    Measurable[filt n i] (fun ω : Fin n → ℝ => nu n δ ω j) := by
  show Measurable[filt n i] (fun ω : Fin n → ℝ =>
    min 1 (Real.sqrt (2 * Real.log (1 / δ) / ((n : ℝ) * sigmaSqHat ω (j - 1)))))
  exact measurable_const.min
    (measurable_const.div (measurable_const.mul (sigmaSqHat_measurable hji))).sqrt

theorem K_measurable {n i i' : ℕ} (δ R : ℝ) (hi : i' ≤ i) :
    Measurable[filt n i] (fun ω : Fin n → ℝ => K n δ ω i' R) := by
  show Measurable[filt n i] (fun ω : Fin n → ℝ =>
    ∏ j ∈ Finset.Icc 1 i', (1 - nu n δ ω j * (obs ω j - R)))
  exact Finset.measurable_prod _ fun j hj =>
    measurable_const.sub ((nu_measurable δ (by have := (Finset.mem_Icc.mp hj).2; omega)).mul
      ((obs_measurable ((Finset.mem_Icc.mp hj).2.trans hi)).sub measurable_const))

/-- Under `Qⁿ`, almost surely every coordinate lies in `[0, 1]`. -/
theorem ae_mem_Icc {n : ℕ} {Q : Measure ℝ} [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ x ∂Q, x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ ω ∂(Measure.pi fun _ : Fin n => Q), ∀ k : Fin n, ω k ∈ Set.Icc (0 : ℝ) 1 := by
  rw [ae_all_iff]
  intro k
  exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => Q) (i := k)).eventually hQ

/-- `|1 - ν (L - r)| ≤ 2 + |r|` for `ν, L ∈ [0, 1]`. -/
theorem factor_abs_le {ν L r : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (hL : L ∈ Set.Icc (0 : ℝ) 1) :
    |1 - ν * (L - r)| ≤ 2 + |r| := by
  have hL0 := hL.1
  have hL1 := hL.2
  have hr1 := le_abs_self r
  have hr2 := neg_abs_le r
  have hr3 := abs_nonneg r
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg hν0 hL0, mul_nonneg (sub_nonneg.mpr hν1) hL0,
      mul_nonneg hν0 (by linarith : 0 ≤ |r| + r), mul_nonneg (sub_nonneg.mpr hν1) hr3]
  · nlinarith [mul_nonneg hν0 hL0, mul_nonneg hν0 (by linarith : 0 ≤ |r| - r),
      mul_nonneg (sub_nonneg.mpr hν1) hr3]

theorem K_abs_le {n : ℕ} {ω : Fin n → ℝ} (hω : ∀ k : Fin n, ω k ∈ Set.Icc (0 : ℝ) 1)
    (δ r : ℝ) (i : ℕ) : |K n δ ω i r| ≤ (2 + |r|) ^ (Finset.Icc 1 i).card := by
  show |∏ j ∈ Finset.Icc 1 i, (1 - nu n δ ω j * (obs ω j - r))| ≤
    (2 + |r|) ^ (Finset.Icc 1 i).card
  rw [Finset.abs_prod, ← Finset.prod_const]
  exact Finset.prod_le_prod (fun j _ => abs_nonneg _)
    (fun j _ => factor_abs_le (nu_nonneg n δ ω j) (nu_le_one n δ ω j) (obs_mem_Icc hω j))

theorem K_integrable {n : ℕ} {Q : Measure ℝ} [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ x ∂Q, x ∈ Set.Icc (0 : ℝ) 1) (δ r : ℝ) (i : ℕ) :
    Integrable (fun ω : Fin n → ℝ => K n δ ω i r) (Measure.pi fun _ : Fin n => Q) := by
  refine Integrable.of_bound
    (((K_measurable (n := n) (i := i) δ r le_rfl).mono ((filt n).le i) le_rfl).aestronglyMeasurable)
    ((2 + |r|) ^ (Finset.Icc 1 i).card) ?_
  filter_upwards [ae_mem_Icc hQ] with ω hω
  rw [Real.norm_eq_abs]
  exact K_abs_le hω δ r i

/-- Coordinate `i` is independent of `ℱ_i = σ(L_1, …, L_i)` (which only sees coordinates `< i`). -/
theorem indep_coord {n : ℕ} {Q : Measure ℝ} [IsProbabilityMeasure Q] {i : ℕ} (hi : i < n) :
    Indep (MeasurableSpace.comap (fun ω : Fin n → ℝ => ω ⟨i, hi⟩) inferInstance) (filt n i)
      (Measure.pi fun _ : Fin n => Q) := by
  have hST : Disjoint (Finset.univ.filter (fun k : Fin n => k.val < i))
      ({⟨i, hi⟩} : Finset (Fin n)) :=
    Finset.disjoint_singleton_right.mpr (by simp)
  have hiid : iIndepFun (fun (k : Fin n) (ω : Fin n → ℝ) => ω k)
      (Measure.pi fun _ : Fin n => Q) :=
    iIndepFun_pi (μ := fun _ : Fin n => Q) (X := fun _ (x : ℝ) => x)
      (fun _ => measurable_id.aemeasurable)
  have hfin := (IndepFun_iff_Indep _ _ _).mp
    (hiid.indepFun_finset _ _ hST (fun k => measurable_pi_apply k))
  have hle₁ : MeasurableSpace.comap (fun ω : Fin n → ℝ => ω ⟨i, hi⟩) inferInstance ≤
      MeasurableSpace.comap
        (fun (ω : Fin n → ℝ) (k : ({⟨i, hi⟩} : Finset (Fin n))) => ω k) inferInstance :=
    ((measurable_pi_apply
      (⟨⟨i, hi⟩, Finset.mem_singleton_self _⟩ : ({⟨i, hi⟩} : Finset (Fin n)))).comp
        (comap_measurable
          (fun (ω : Fin n → ℝ) (k : ({⟨i, hi⟩} : Finset (Fin n))) => ω k))).comap_le
  have hle₂ : filt n i ≤ MeasurableSpace.comap
      (fun (ω : Fin n → ℝ) (k : Finset.univ.filter (fun k : Fin n => k.val < i)) => ω k)
      inferInstance := by
    rw [show filt n i = MeasurableSpace.comap
        (fun (ω : Fin n → ℝ) (j : Set.Iic i) => obs ω j) inferInstance from
      Filtration.natural_eq_comap _ _ i]
    let : MeasurableSpace (Fin n → ℝ) :=
      MeasurableSpace.comap
        (fun (ω : Fin n → ℝ) (k : Finset.univ.filter (fun k : Fin n => k.val < i)) => ω k)
        inferInstance
    refine Measurable.comap_le (measurable_pi_lambda _ fun j => ?_)
    unfold obs
    split_ifs with hj
    · have hlt : (j : ℕ) - 1 < n := by omega
      have hmem : (⟨(j : ℕ) - 1, hlt⟩ : Fin n) ∈ Finset.univ.filter (fun k : Fin n => k.val < i) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have := Set.mem_Iic.mp j.2
        omega
      exact (measurable_pi_apply (⟨⟨(j : ℕ) - 1, hlt⟩, hmem⟩ :
        Finset.univ.filter (fun k : Fin n => k.val < i))).comp
          (comap_measurable (fun (ω : Fin n → ℝ)
            (k : Finset.univ.filter (fun k : Fin n => k.val < i)) => ω k))
    · exact measurable_const
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hfin.symm hle₁) hle₂

/-- The one-step martingale identity `K_{min i n} = E[K_{min (i+1) n} | ℱ_i]` at the true mean. -/
theorem one_step {n : ℕ} {Q : Measure ℝ} [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ x ∂Q, x ∈ Set.Icc (0 : ℝ) 1) (δ R : ℝ) (hR : ∫ x, x ∂Q = R) (i : ℕ) :
    (fun ω : Fin n → ℝ => K n δ ω (min i n) R) =ᵐ[Measure.pi fun _ : Fin n => Q]
      condExp (filt n i) (Measure.pi fun _ : Fin n => Q)
        (fun ω : Fin n → ℝ => K n δ ω (min (i + 1) n) R) := by
  rcases lt_or_ge i n with hi | hi
  · rw [min_eq_left hi.le, min_eq_left (by omega : i + 1 ≤ n)]
    have hstep : ∀ ω : Fin n → ℝ, K n δ ω (i + 1) R =
        K n δ ω i R - (K n δ ω i R * nu n δ ω (i + 1)) * (obs ω (i + 1) - R) := by
      intro ω
      show (∏ j ∈ Finset.Icc 1 (i + 1), (1 - nu n δ ω j * (obs ω j - R))) =
        (∏ j ∈ Finset.Icc 1 i, (1 - nu n δ ω j * (obs ω j - R))) -
          ((∏ j ∈ Finset.Icc 1 i, (1 - nu n δ ω j * (obs ω j - R))) * nu n δ ω (i + 1)) *
            (obs ω (i + 1) - R)
      rw [Finset.prod_Icc_succ_top (by omega)]
      ring
    have hKi_meas : Measurable[filt n i] (fun ω : Fin n → ℝ => K n δ ω i R) :=
      K_measurable δ R le_rfl
    have hnu_meas : Measurable[filt n i] (fun ω : Fin n → ℝ => nu n δ ω (i + 1)) :=
      nu_measurable δ (by omega)
    have hh_sm : StronglyMeasurable[filt n i]
        (fun ω : Fin n → ℝ => K n δ ω i R * nu n δ ω (i + 1)) :=
      (hKi_meas.mul hnu_meas).stronglyMeasurable
    have hKi_int : Integrable (fun ω : Fin n → ℝ => K n δ ω i R)
        (Measure.pi fun _ : Fin n => Q) := K_integrable hQ δ R i
    have hKi1_int : Integrable (fun ω : Fin n → ℝ => K n δ ω (i + 1) R)
        (Measure.pi fun _ : Fin n => Q) := K_integrable hQ δ R (i + 1)
    have hobs_int : Integrable (fun ω : Fin n → ℝ => obs ω (i + 1))
        (Measure.pi fun _ : Fin n => Q) := by
      refine Integrable.of_bound
        (((obs_measurable (n := n) (i := i + 1) (j := i + 1) le_rfl).mono
          ((filt n).le (i + 1)) le_rfl).aestronglyMeasurable) 1 ?_
      filter_upwards [ae_mem_Icc hQ] with ω hω
      have hb := obs_mem_Icc hω (i + 1)
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [hb.1], hb.2⟩
    have hg_int : Integrable (fun ω : Fin n → ℝ => obs ω (i + 1) - R)
        (Measure.pi fun _ : Fin n => Q) := hobs_int.sub (integrable_const R)
    have hhg_int : Integrable (fun ω : Fin n → ℝ =>
        (K n δ ω i R * nu n δ ω (i + 1)) * (obs ω (i + 1) - R))
        (Measure.pi fun _ : Fin n => Q) := by
      refine (hKi_int.sub hKi1_int).congr (ae_of_all _ fun ω => ?_)
      show K n δ ω i R - K n δ ω (i + 1) R =
        (K n δ ω i R * nu n δ ω (i + 1)) * (obs ω (i + 1) - R)
      rw [hstep ω]
      ring
    have hobs_cond : condExp (filt n i) (Measure.pi fun _ : Fin n => Q)
        (fun ω : Fin n → ℝ => obs ω (i + 1)) =ᵐ[Measure.pi fun _ : Fin n => Q] fun _ => R := by
      have heq : (fun ω : Fin n → ℝ => obs ω (i + 1)) = fun ω : Fin n → ℝ => ω ⟨i, hi⟩ :=
        funext fun ω => obs_succ ω hi
      have hcm : Measurable[MeasurableSpace.comap (fun ω : Fin n → ℝ => ω ⟨i, hi⟩) inferInstance]
          (fun ω : Fin n → ℝ => ω ⟨i, hi⟩) := comap_measurable _
      have hf_sm : StronglyMeasurable[MeasurableSpace.comap
          (fun ω : Fin n → ℝ => ω ⟨i, hi⟩) inferInstance] (fun ω : Fin n → ℝ => obs ω (i + 1)) := by
        rw [heq]
        exact hcm.stronglyMeasurable
      have hce := condExp_indep_eq ((measurable_pi_apply (⟨i, hi⟩ : Fin n)).comap_le)
        ((filt n).le i) hf_sm (indep_coord (Q := Q) hi)
      refine hce.trans (Filter.EventuallyEq.of_eq ?_)
      funext _
      have hint : ∫ x, obs x (i + 1) ∂(Measure.pi fun _ : Fin n => Q) =
          ∫ x, x ⟨i, hi⟩ ∂(Measure.pi fun _ : Fin n => Q) :=
        integral_congr_ae (ae_of_all _ fun ω => obs_succ ω hi)
      have hcoord : ∫ x, x ⟨i, hi⟩ ∂(Measure.pi fun _ : Fin n => Q) = ∫ x, x ∂Q :=
        integral_comp_eval (μ := fun _ : Fin n => Q) (i := (⟨i, hi⟩ : Fin n))
          (f := fun x : ℝ => x) aestronglyMeasurable_id
      exact hint.trans (hcoord.trans hR)
    have hgzero : condExp (filt n i) (Measure.pi fun _ : Fin n => Q)
        (fun ω : Fin n → ℝ => obs ω (i + 1) - R) =ᵐ[Measure.pi fun _ : Fin n => Q]
          fun _ => (0 : ℝ) := by
      have hs : condExp (filt n i) (Measure.pi fun _ : Fin n => Q)
          (fun ω : Fin n → ℝ => obs ω (i + 1) - R) =ᵐ[Measure.pi fun _ : Fin n => Q]
            fun ω => condExp (filt n i) (Measure.pi fun _ : Fin n => Q)
                (fun ω : Fin n → ℝ => obs ω (i + 1)) ω -
              condExp (filt n i) (Measure.pi fun _ : Fin n => Q) (fun _ : Fin n → ℝ => R) ω :=
        condExp_sub hobs_int (integrable_const R) _
      have hc : ∀ ω : Fin n → ℝ, condExp (filt n i) (Measure.pi fun _ : Fin n => Q)
          (fun _ : Fin n → ℝ => R) ω = R :=
        fun ω => congrFun (condExp_const ((filt n).le i) R) ω
      filter_upwards [hs, hobs_cond] with ω h1 h2
      rw [h1, h2, hc ω, sub_self]
    have hcongr : condExp (filt n i) (Measure.pi fun _ : Fin n => Q)
        (fun ω : Fin n → ℝ => K n δ ω (i + 1) R) =ᵐ[Measure.pi fun _ : Fin n => Q]
          condExp (filt n i) (Measure.pi fun _ : Fin n => Q) (fun ω : Fin n → ℝ =>
            K n δ ω i R - (K n δ ω i R * nu n δ ω (i + 1)) * (obs ω (i + 1) - R)) :=
      condExp_congr_ae (ae_of_all _ hstep)
    have hsub : condExp (filt n i) (Measure.pi fun _ : Fin n => Q) (fun ω : Fin n → ℝ =>
          K n δ ω i R - (K n δ ω i R * nu n δ ω (i + 1)) * (obs ω (i + 1) - R))
        =ᵐ[Measure.pi fun _ : Fin n => Q] fun ω =>
          condExp (filt n i) (Measure.pi fun _ : Fin n => Q)
              (fun ω : Fin n → ℝ => K n δ ω i R) ω -
            condExp (filt n i) (Measure.pi fun _ : Fin n => Q) (fun ω : Fin n → ℝ =>
              (K n δ ω i R * nu n δ ω (i + 1)) * (obs ω (i + 1) - R)) ω :=
      condExp_sub hKi_int hhg_int _
    have hpull : condExp (filt n i) (Measure.pi fun _ : Fin n => Q) (fun ω : Fin n → ℝ =>
          (K n δ ω i R * nu n δ ω (i + 1)) * (obs ω (i + 1) - R))
        =ᵐ[Measure.pi fun _ : Fin n => Q] fun ω =>
          (K n δ ω i R * nu n δ ω (i + 1)) *
            condExp (filt n i) (Measure.pi fun _ : Fin n => Q)
              (fun ω : Fin n → ℝ => obs ω (i + 1) - R) ω :=
      condExp_mul_of_stronglyMeasurable_left hh_sm hhg_int hg_int
    have hKcond : ∀ ω : Fin n → ℝ, condExp (filt n i) (Measure.pi fun _ : Fin n => Q)
        (fun ω : Fin n → ℝ => K n δ ω i R) ω = K n δ ω i R :=
      fun ω => congrFun (condExp_of_stronglyMeasurable ((filt n).le i)
        hKi_meas.stronglyMeasurable hKi_int) ω
    filter_upwards [hcongr, hsub, hpull, hgzero] with ω h0 h1 h2 h3
    rw [h0, h1, h2, h3, hKcond ω]
    ring
  · rw [min_eq_right hi, min_eq_right (by omega : n ≤ i + 1)]
    exact Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable ((filt n).le i)
      (K_measurable δ R hi).stronglyMeasurable (K_integrable hQ δ R n)).symm

end RiskControl.WSR.Lead34KMart

namespace RiskControl.WSR

/-- Proof of Proposition 5, p. 26 (arXiv:2101.02703v3): at the true mean `R = ∫ x dQ` of the
`[0, 1]`-valued losses, the capital process `𝒦_i = 𝒦_i(R; λ)`, `i = 0, …, n`, is a martingale
for the natural filtration `ℱ_i = σ(L_1, …, L_i)` under the i.i.d. law `Qⁿ`; it is extended
constantly past `n` (index `min i n`) to a process indexed by `ℕ`. -/
theorem K_martingale (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ x ∂Q, x ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) (δ : ℝ) :
    Martingale (fun i (ω : Fin n → ℝ) => K n δ ω (min i n) (∫ x, x ∂Q)) (filt n)
      (Measure.pi fun _ : Fin n => Q) := by
  refine martingale_nat ?_ ?_ ?_
  · intro i
    exact (Lead34KMart.K_measurable δ _ (min_le_left i n)).stronglyMeasurable
  · intro i
    exact Lead34KMart.K_integrable hQ δ _ (min i n)
  · intro i
    exact Lead34KMart.one_step hQ δ _ rfl i

end RiskControl.WSR

end Prove2WSRSubmission

theorem solution (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ x ∂Q, x ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) (δ : ℝ) :
    Martingale (fun i (ω : Fin n → ℝ) => K n δ ω (min i n) (∫ x, x ∂Q)) (filt n)
      (Measure.pi fun _ : Fin n => Q) := by
  exact _root_.Prove2WSRSubmission.RiskControl.WSR.K_martingale Q hQ n δ
