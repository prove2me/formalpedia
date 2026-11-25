-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.xiIntH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:40:34.409221+00:00
-- url     : https://prove2.me/submissions/0af21123-a9b5-4b11-9a57-76804b62c660

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XiIntH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_XI_cont_gN
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_XI_lam_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_XI_meas_xi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_XI_xi_bd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Xi.XI
namespace XI
private theorem lintegral_prod_le_lintegral_lintegral {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (f : α × β → ℝ≥0∞) :
    ∫⁻ p, f p ∂(μ.prod ν) ≤ ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ := by
  obtain ⟨g, hgm, hgle, hgeq⟩ := exists_measurable_le_lintegral_eq (μ.prod ν) f
  rw [hgeq]
  have e : μ.prod ν = Measure.bind μ (fun x => Measure.map (Prod.mk x) ν) := by
    first
      | exact Measure.prod_def μ ν
      | rw [Measure.prod_def]
      | rw [Measure.prod]
  rw [e]
  first
    | rw [Measure.bind, Measure.lintegral_join hgm.aemeasurable]
    | (unfold Measure.bind; rw [Measure.lintegral_join hgm.aemeasurable])
    | rw [Measure.bind, Measure.lintegral_join hgm]
  calc ∫⁻ m, ∫⁻ p, g p ∂m ∂(Measure.map (fun x => Measure.map (Prod.mk x) ν) μ)
      ≤ ∫⁻ x, ∫⁻ p, g p ∂(Measure.map (Prod.mk x) ν) ∂μ :=
        lintegral_map_le (fun m : Measure (α × β) => ∫⁻ p, g p ∂m) _
    _ ≤ ∫⁻ x, ∫⁻ y, g (x, y) ∂ν ∂μ := lintegral_mono fun x => lintegral_map_le g (Prod.mk x)
    _ ≤ ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ :=
        lintegral_mono fun x => lintegral_mono fun y => hgle (x, y)
private theorem side {k r : ℕ} (s : Fin (r + 1) → ℝ) (hs : ∀ l, 0 ≤ s l) (z : Fin (2 * r + k + 1) → ℂ)
    (μW μN : Measure (Mt k r)) (hW : IsHaarOn (UWset k r z) μW)
    (hconj : ∀ h₀ ∈ UWset k r z, μN.map (conjM h₀) = μN) (hcomp : IsCompact (UWset k r z))
    (hcl : IsClosedSubgroup (UWset k r z)) (hI : IInt μN z s (1 / 2) < ∞) :
    (∫⁻ p : Mt k r × Mt k r, (xiN k r s (Matrix.of p.2 * Matrix.of p.1) : ℝ≥0∞) *
      ENNReal.ofReal ((1 + |lam k r z (Matrix.of p.2)|) ^ (-(2 : ℝ))) ∂(μW.prod μN)) < ∞ := by
  obtain ⟨K₀, hK₀⟩ := hcomp.exists_bound_of_continuousOn (cont_gN (k := k) (r := r)).continuousOn
  obtain ⟨K, hK1, hKb⟩ : ∃ K : ℝ, 1 ≤ K ∧ ∀ g ∈ UWset k r z, gN g ≤ K := by
    refine ⟨max K₀ 1, le_max_right _ _, fun g hg => ?_⟩
    have h1 := hK₀ g hg
    rw [Real.norm_eq_abs] at h1
    exact (le_abs_self _).trans (h1.trans (le_max_left _ _))
  obtain ⟨C, hC0, hCeq⟩ : ∃ C : ℝ, 0 ≤ C ∧ C = ∏ l : Fin (r + 1), (K ^ (l.val + 1)) ^ s l :=
    ⟨_, Finset.prod_nonneg fun l _ => Real.rpow_nonneg (pow_nonneg (by linarith) _) _, rfl⟩
  have hlam : Continuous (fun m : Mt k r => lam k r z (Matrix.of m)) := by
    unfold lam ell
    refine Complex.continuous_re.comp (continuous_const.mul (continuous_finset_sum _ fun a _ => ?_))
    split_ifs with ha
    · first
        | (simp only [Matrix.of_apply]; fun_prop)
        | fun_prop
        | exact (continuous_apply _).comp (continuous_apply _)
    · first
        | (simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]; fun_prop)
        | (simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.of_apply]; fun_prop)
        | exact (continuous_apply _).comp (Continuous.matrix_mulVec continuous_id continuous_const)
  have hWfin : μW Set.univ < ∞ := by
    have h2 : μW Set.univ ≤ μW (UWset k r z) + μW (UWset k r z)ᶜ := by
      first
        | exact measure_univ_le_add_compl _
        | (rw [← Set.union_compl_self (UWset k r z)]; exact measure_union_le _ _)
    rw [hW.conc, add_zero] at h2
    exact lt_of_le_of_lt h2 (hW.finite_compact _ hcomp)
  have hae : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z := by
    rw [ae_iff]
    first
      | exact hW.conc
      | exact measure_mono_null (fun a ha => ha) hW.conc
  have hinner : ∀ h ∈ UWset k r z, (∫⁻ n : Mt k r, (xiN k r s (Matrix.of n * h) : ℝ≥0∞) *
      ENNReal.ofReal ((1 + |lam k r z (Matrix.of n)|) ^ (-(2 : ℝ))) ∂μN) ≤
      ENNReal.ofReal C * IInt μN z s (1 / 2) := by
    intro h hh
    have hu : IsUnit h.det := hcl.unit h hh
    have hinv : h⁻¹ ∈ UWset k r z := hcl.inv_mem h hh
    have hu' : IsUnit h⁻¹.det := hcl.unit _ hinv
    have hii : h⁻¹⁻¹ = h := Matrix.nonsing_inv_nonsing_inv h hu
    have hcm : Measurable (conjM (k := k) (r := r) h⁻¹) := by
      apply Continuous.measurable
      first
        | exact continuous_pi fun i => continuous_pi fun j => by
            simp only [conjM, Matrix.mul_apply, Matrix.of_apply]; fun_prop
        | (unfold conjM; fun_prop)
        | (unfold conjM; exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
    have hG : Measurable (fun m : Mt k r => ENNReal.ofReal (xiR k r s (Matrix.of m)) *
        ENNReal.ofReal ((1 + |lam k r z (Matrix.of m)|) ^ (-(1 / 2 : ℝ)))) := by
      have hm1 : Measurable (fun m : Mt k r => ENNReal.ofReal (xiR k r s (Matrix.of m))) :=
        (meas_xi k r s).coe_nnreal_ennreal
      have hm2 : Measurable (fun m : Mt k r =>
          ENNReal.ofReal ((1 + |lam k r z (Matrix.of m)|) ^ (-(1 / 2 : ℝ)))) :=
        ENNReal.measurable_ofReal.comp ((continuous_const.add hlam.abs).measurable.pow_const _)
      exact hm1.mul hm2
    have hpt : ∀ n : Mt k r, (xiN k r s (Matrix.of n * h) : ℝ≥0∞) *
        ENNReal.ofReal ((1 + |lam k r z (Matrix.of n)|) ^ (-(2 : ℝ))) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (xiR k r s (Matrix.of (conjM h⁻¹ n))) *
          ENNReal.ofReal ((1 + |lam k r z (Matrix.of (conjM h⁻¹ n))|) ^ (-(1 / 2 : ℝ)))) := by
      intro n
      have e : Matrix.of (conjM h⁻¹ n) = h⁻¹ * Matrix.of n * h := by
        show h⁻¹ * Matrix.of n * h⁻¹⁻¹ = _
        rw [hii]
      have hl : lam k r z (h⁻¹ * Matrix.of n * h) = lam k r z (Matrix.of n) := by
        have := lam_conj hinv hu' (Matrix.of n)
        rwa [hii] at this
      have hxi : xiR k r s (Matrix.of n * h) ≤ C * xiR k r s (h⁻¹ * Matrix.of n * h) := by
        have := xi_bd s hs h hu K hK1 (hKb h hh) (hKb h⁻¹ hinv) (h⁻¹ * Matrix.of n * h)
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu,
          Matrix.one_mul] at this
        rw [hCeq]
        exact this
      have hw : (1 + |lam k r z (Matrix.of n)|) ^ (-(2 : ℝ)) ≤
          (1 + |lam k r z (Matrix.of n)|) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg (lam k r z (Matrix.of n))])
          (by norm_num)
      rw [e, hl, ← mul_assoc, ← ENNReal.ofReal_mul hC0]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal hxi) (ENNReal.ofReal_le_ofReal hw)
    calc (∫⁻ n : Mt k r, (xiN k r s (Matrix.of n * h) : ℝ≥0∞) *
          ENNReal.ofReal ((1 + |lam k r z (Matrix.of n)|) ^ (-(2 : ℝ))) ∂μN)
        ≤ ∫⁻ n : Mt k r, ENNReal.ofReal C * (ENNReal.ofReal (xiR k r s (Matrix.of (conjM h⁻¹ n))) *
          ENNReal.ofReal ((1 + |lam k r z (Matrix.of (conjM h⁻¹ n))|) ^ (-(1 / 2 : ℝ)))) ∂μN :=
          lintegral_mono hpt
      _ = ENNReal.ofReal C * ∫⁻ n : Mt k r, (ENNReal.ofReal (xiR k r s (Matrix.of (conjM h⁻¹ n))) *
          ENNReal.ofReal ((1 + |lam k r z (Matrix.of (conjM h⁻¹ n))|) ^ (-(1 / 2 : ℝ)))) ∂μN :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal C * ∫⁻ m : Mt k r, (ENNReal.ofReal (xiR k r s (Matrix.of m)) *
          ENNReal.ofReal ((1 + |lam k r z (Matrix.of m)|) ^ (-(1 / 2 : ℝ)))) ∂(μN.map (conjM h⁻¹)) := by
          rw [lintegral_map hG hcm]
      _ = ENNReal.ofReal C * IInt μN z s (1 / 2) := by
          rw [hconj h⁻¹ hinv]
          try rfl
  calc (∫⁻ p : Mt k r × Mt k r, (xiN k r s (Matrix.of p.2 * Matrix.of p.1) : ℝ≥0∞) *
        ENNReal.ofReal ((1 + |lam k r z (Matrix.of p.2)|) ^ (-(2 : ℝ))) ∂(μW.prod μN))
      ≤ ∫⁻ x : Mt k r, ∫⁻ n : Mt k r, (xiN k r s (Matrix.of n * Matrix.of x) : ℝ≥0∞) *
        ENNReal.ofReal ((1 + |lam k r z (Matrix.of n)|) ^ (-(2 : ℝ))) ∂μN ∂μW :=
        lintegral_prod_le_lintegral_lintegral μW μN _
    _ ≤ ∫⁻ _x : Mt k r, ENNReal.ofReal C * IInt μN z s (1 / 2) ∂μW :=
        lintegral_mono_ae (hae.mono fun x hx => hinner (Matrix.of x) hx)
    _ = ENNReal.ofReal C * IInt μN z s (1 / 2) * μW Set.univ := lintegral_const _
    _ < ∞ := by
        first
          | exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI) hWfin
          | exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_ne_top hI.ne) hWfin.ne
end XI
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Xi.XI
namespace ReciprocityTheory.ChartRestriction.DS.Xi
theorem _root_.solution (hB2 : InductiveHeisenbergInputs) : XiIntStep := by
  unfold InductiveHeisenbergInputs at hB2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hCI, hCW, -, -, -, -, -, -, -, hClW, -, -, -, -, -⟩ := hB2
  intro k r Wp Wq _ _ _ _ _ _ D s hs hI hI'
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast D.k_pos
  have hs0 : ∀ l, 0 ≤ s l := by
    intro l
    have h1 := (hs l).2
    have h2 : (1 : ℝ) ≤ s0 k r l := by
      unfold s0
      split_ifs <;> linarith
    linarith
  unfold XiInt
  refine ⟨XI.meas_xi k r s, ?_, ?_⟩
  · exact XI.side s hs0 D.z D.μW D.μN D.haarW
      (fun h₀ hh => hCI k r Wp Wq D h₀ (Set.mem_union_left _ hh))
      (hCW k r D.z D.z_mem D.T_pos) (hClW k r D.z) hI
  · exact XI.side s hs0 D.z' D.μW' D.μN D.haarW'
      (fun h₀ hh => hCI k r Wp Wq D h₀ (Set.mem_union_right _ hh))
      (hCW k r D.z' D.z'_mem D.T'_pos) (hClW k r D.z') hI'
end ReciprocityTheory.ChartRestriction.DS.Xi
