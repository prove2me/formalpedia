-- Prove2me | solution 1 for PI.ProdFormulaE.HaarBox.scale_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:20:52.937093+00:00
-- url     : https://prove2.me/submissions/3f25c4a3-d574-4726-8cd3-e3d5c28b1ec0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarBox
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarScale
import Theorems.Thm_PI_ProdFormulaE_HaarBox_exists_ball_of_isCompact
import Theorems.Thm_PI_ProdFormulaE_HaarBox_continuous_coord
import Theorems.Thm_PI_ProdFormulaE_HaarBox_isCompact_box
import Theorems.Thm_PI_ProdFormulaE_HaarBox_isOpen_ball
import Theorems.Thm_PI_ProdFormulaE_HaarBox_locallyCompact
import Theorems.Thm_PI_ProdFormulaE_HaarBox_secondCountable
import Theorems.Thm_PI_ProdFormulaE_HaarBox_secondCountableE


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.style.haveILetI false
open MeasureTheory Measure ValuativeRel Topology Filter Module
open scoped NNReal ENNReal Pointwise
open PI PI.ProdFormulaE PI.ProdFormulaE.HaarBox
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable [MeasurableSpace E] [BorelSpace E]
namespace PI.ProdFormulaE.HaarBox
theorem _root_.solution (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure] (i : ι) (a : K)
    (ha : a ≠ 0) :
    μ (Matrix.toLin b b (Matrix.diagonal (Function.update 1 i a)) '' box b 1) =
      (distribHaarChar K (Units.mk0 a ha) : ℝ≥0∞) * μ (box b 1) := by
  letI : MeasurableSpace K := borel K
  haveI : BorelSpace K := ⟨rfl⟩
  haveI : IsTopologicalAddGroup E := IsModuleTopology.topologicalAddGroup K E
  haveI := locallyCompact b
  haveI := secondCountableE b
  haveI := secondCountable K
  obtain ⟨c, hc⟩ : ∃ c : E → K, c = fun x => b.repr x i := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Set E, P = {x | ∀ j, j ≠ i → valuation K (b.repr x j) ≤ 1} :=
    ⟨_, rfl⟩
  have hcc : Continuous c := by rw [hc]; exact continuous_coord b i
  have hcm : Measurable c := hcc.measurable
  have hPo : IsOpen P := by
    have h : P = ⋂ j ∈ (Finset.univ.filter (· ≠ i)),
        (fun x : E => b.repr x j) ⁻¹' {z : K | valuation K z ≤ 1} := by
      rw [hP]; ext x; simp
    rw [h]
    exact isOpen_biInter_finset
      (fun j _ => (isOpen_ball 1 one_ne_zero).preimage (continuous_coord b j))
  let ν : Measure K := (μ.restrict P).map c
  have hνA : ∀ A : Set K, MeasurableSet A → ν A = μ (P ∩ c ⁻¹' A) := by
    intro A hA
    show ((μ.restrict P).map c) A = _
    rw [Measure.map_apply hcm hA, Measure.restrict_apply (hcm hA), Set.inter_comm]
  have hrepr_add : ∀ (t : K) (x : E) (j : ι),
      b.repr (t • b i + x) j = (if i = j then t else 0) + b.repr x j := by
    intro t x j
    rw [map_add, map_smul, Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.single_apply]
    split_ifs <;> simp
  haveI : ν.IsAddLeftInvariant := by
    refine ⟨fun t => ?_⟩
    ext A hA
    rw [Measure.map_apply (measurable_const_add t) hA, hνA _ hA,
      hνA _ (measurable_const_add t hA)]
    have hset : P ∩ c ⁻¹' ((fun x => t + x) ⁻¹' A) =
        (fun x : E => t • b i + x) ⁻¹' (P ∩ c ⁻¹' A) := by
      ext x
      rw [hP, hc]
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, hrepr_add]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun j hj => by rw [if_neg (Ne.symm hj), zero_add]; exact h1 j hj, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨fun j hj => ?_, h2⟩
        have := h1 j hj
        rwa [if_neg (Ne.symm hj), zero_add] at this
    rw [hset, measure_preimage_add]
  haveI : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun C hC => ?_⟩
    obtain ⟨y, hy0, hCy⟩ := exists_ball_of_isCompact hC
    have hyv : valuation K y ≠ 0 := (Valuation.ne_zero_iff _).2 hy0
    have hB : IsOpen {x : K | valuation K x ≤ valuation K y} := isOpen_ball _ hyv
    calc ν C ≤ ν {x | valuation K x ≤ valuation K y} := measure_mono hCy
      _ = μ (P ∩ c ⁻¹' {x | valuation K x ≤ valuation K y}) := hνA _ hB.measurableSet
      _ ≤ μ (box b (Function.update 1 i (valuation K y))) := by
          apply measure_mono
          rintro x ⟨hx1, hx2⟩ j
          by_cases hj : j = i
          · subst hj
            rw [Function.update_self]
            rw [Set.mem_preimage, hc] at hx2
            exact hx2
          · rw [Function.update_of_ne hj]
            rw [hP] at hx1
            exact hx1 j hj
      _ < ⊤ := (isCompact_box b _).measure_lt_top
  haveI : IsOpenPosMeasure ν := by
    refine ⟨fun U hU hne => ?_⟩
    obtain ⟨u, hu⟩ := hne
    rw [hνA U hU.measurableSet]
    have hO : IsOpen (P ∩ c ⁻¹' U) := hPo.inter (hU.preimage hcc)
    refine hO.measure_ne_zero μ ⟨u • b i, ?_, ?_⟩
    · rw [hP]
      intro j hj
      rw [map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
        if_neg (Ne.symm hj), smul_zero, map_zero]
      exact zero_le'
    · rw [Set.mem_preimage, hc]
      simpa using hu
  haveI : ν.IsAddHaarMeasure := { }
  let g : Kˣ := Units.mk0 a ha
  have hOo : IsOpen {x : K | valuation K x ≤ 1} := isOpen_ball 1 one_ne_zero
  have hgO : IsOpen (g • {x : K | valuation K x ≤ 1}) := hOo.smul g
  have hscale : ν (g • {x : K | valuation K x ≤ 1}) =
      (distribHaarChar K g : ℝ≥0∞) * ν {x | valuation K x ≤ 1} := by
    have h1 : (DomMulAct.mk g • ν) {x : K | valuation K x ≤ 1} =
        ν (g • {x : K | valuation K x ≤ 1}) := by
      simp [domSMul_apply]
    rw [← h1, measure_isAddHaarMeasure_eq_smul_of_isOpen _ ν hOo,
      addHaarScalarFactor_smul_eq_distribHaarChar, ENNReal.smul_def, smul_eq_mul]
  have hrepr : ∀ (d : ι → K) (x : E) (j : ι),
      b.repr (Matrix.toLin b b (Matrix.diagonal d) x) j = d j * b.repr x j := by
    intro d x j
    rw [Matrix.repr_toLin, Matrix.mulVec_diagonal]
  have hR : box b 1 = P ∩ c ⁻¹' {x : K | valuation K x ≤ 1} := by
    ext x
    rw [hP, hc]
    constructor
    · intro h
      exact ⟨fun j _ => h j, h i⟩
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; exact h2
      · exact h1 j hj
  have hL : (Matrix.toLin b b (Matrix.diagonal (Function.update 1 i a))) '' box b 1 =
      P ∩ c ⁻¹' (g • {x : K | valuation K x ≤ 1}) := by
    ext y
    rw [hP, hc]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨fun j hj => ?_, ?_⟩
      · show valuation K (b.repr _ j) ≤ 1
        rw [hrepr, Function.update_of_ne hj, Pi.one_apply, one_mul]
        exact hx j
      · show b.repr _ i ∈ g • {x : K | valuation K x ≤ 1}
        rw [hrepr, Function.update_self]
        exact Set.mem_smul_set.2 ⟨b.repr x i, hx i, rfl⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨z, hz, hzy⟩ := Set.mem_smul_set.1 h2
      have hzy' : a * z = b.repr y i := hzy
      let T' := Matrix.toLin b b (Matrix.diagonal (Function.update (1 : ι → K) i a⁻¹))
      refine ⟨T' y, fun j => ?_, ?_⟩
      · show valuation K (b.repr (T' y) j) ≤ 1
        rw [hrepr]
        by_cases hj : j = i
        · subst hj
          rw [Function.update_self, ← hzy', ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
          exact hz
        · rw [Function.update_of_ne hj, Pi.one_apply, one_mul]
          exact h1 j hj
      · show Matrix.toLin b b _ (Matrix.toLin b b _ y) = y
        rw [← LinearMap.comp_apply, ← Matrix.toLin_mul, Matrix.diagonal_mul_diagonal]
        have hdd : (fun k => Function.update (1 : ι → K) i a k * Function.update (1 : ι → K) i a⁻¹ k) =
            (1 : ι → K) := by
          funext k
          by_cases hk : k = i
          · subst hk; simp [ha]
          · simp [Function.update_of_ne hk]
        rw [hdd, Pi.one_def, Matrix.diagonal_one, Matrix.toLin_one, LinearMap.id_apply]
  rw [hL, hR, ← hνA _ hgO.measurableSet, ← hνA _ hOo.measurableSet, hscale]
end PI.ProdFormulaE.HaarBox
