-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.blockPoly_claim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:36:17.133015+00:00
-- url     : https://prove2.me/submissions/8c363b84-4fff-456b-ac72-2105e053d237

import Definitions.Def_ReciprocityTheory_SemistableReduction_IntCoresA
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntCoresB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_BlockPoly_restrict
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_continuous_spherePoint
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sphere_zero_null


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (hSJ : SJStatement) (n : ℕ) : ∀ (k : ℕ) (a : Fin k → ℕ)
    (F : (Fin k → Fin n → ℂ) → ℂ), BlockPoly k n a F → ∀ z0 : Fin k → UnitSphereC n,
    onSpheres F z0 ≠ 0 →
    Integrable (fun z => Real.log ‖onSpheres F z‖) (Measure.pi fun _ : Fin k => sphereProb n) ∧
      Measure.pi (fun _ : Fin k => sphereProb n) {z | onSpheres F z = 0} = 0 := by
  haveI : IsFiniteMeasure (sphereProb n) := by unfold sphereProb; infer_instance
  intro k
  induction k with
  | zero =>
    intro a F hF z0 hz0
    have hconst : ∀ z : Fin 0 → UnitSphereC n, onSpheres F z = onSpheres F z0 := by
      intro z
      unfold onSpheres
      congr 1
      funext b
      exact b.elim0
    refine ⟨?_, ?_⟩
    · simp_rw [hconst]
      exact integrable_const _
    · simp_rw [hconst]
      simp [hz0]
  | succ k ih =>
    intro a F hF z0 hz0
    set μ := sphereProb n with hμ
    set ν := Measure.pi fun _ : Fin k => sphereProb n with hν
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => UnitSphereC n) 0
    have mp : MeasurePreserving e (Measure.pi fun _ : Fin (k + 1) => sphereProb n) (μ.prod ν) :=
      measurePreserving_piFinSuccAbove (fun _ => sphereProb n) 0
    let e2 := e.trans MeasurableEquiv.prodComm
    have mp2 : MeasurePreserving e2 (Measure.pi fun _ : Fin (k + 1) => sphereProb n) (ν.prod μ) :=
      (Measure.measurePreserving_swap).comp mp
    have hcont : Continuous (onSpheres F : (Fin (k + 1) → UnitSphereC n) → ℂ) :=
      hF.1.comp (continuous_pi fun b => (continuous_spherePoint n).comp (continuous_apply b))
    let H : (Fin k → UnitSphereC n) × UnitSphereC n → ℂ := fun q => onSpheres F (e2.symm q)
    have hHm : Measurable H := hcont.measurable.comp e2.symm.measurable
    have hsymm : ∀ z' w, e2.symm (z', w) = Fin.cons w z' := by
      intro z' w
      simp [e2, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_zero']
      rfl
    have hH : ∀ z' w, H (z', w) = F (Fin.cons (spherePoint w) (fun b => spherePoint (z' b))) := by
      intro z' w
      simp only [H, onSpheres, hsymm]
      congr 1
      funext b
      refine Fin.cases ?_ (fun j => ?_) b <;> simp
    have hcomp : ∀ z, onSpheres F z = H (e2 z) := by
      intro z
      simp only [H, MeasurableEquiv.symm_apply_apply]
    set v0 := spherePoint (z0 0) with hv0
    have hR := hF.restrict v0
    have hG : ∀ z', onSpheres (fun p => F (Fin.cons v0 p)) z' = H (z', z0 0) := by
      intro z'
      rw [hH]
      rfl
    have hz0' : onSpheres (fun p => F (Fin.cons v0 p)) (fun j => z0 j.succ) ≠ 0 := by
      simp only [onSpheres] at hz0 ⊢
      convert hz0 using 2
      funext b
      refine Fin.cases ?_ (fun j => ?_) b <;> simp [v0]
    obtain ⟨ihInt, ihNull⟩ := ih _ _ hR _ hz0'
    simp_rw [hG] at ihInt ihNull
    have hgood : ∀ᵐ z' ∂ν, H (z', z0 0) ≠ 0 := by
      rw [ae_iff]
      simpa using ihNull
    have hslice : ∀ z', H (z', z0 0) ≠ 0 →
        Integrable (fun w => Real.log ‖H (z', w)‖) μ ∧
        Real.log ‖H (z', z0 0)‖ - (a 0 : ℝ) / 2 * (harmonic (n - 1) : ℝ) ≤
          ∫ w, Real.log ‖H (z', w)‖ ∂μ ∧ μ {w | H (z', w) = 0} = 0 := by
      intro z' hz'
      obtain ⟨g, hg, hgF⟩ := hF.2 0 (Fin.cons 0 (fun b => spherePoint (z' b)))
      have hHw : ∀ w, H (z', w) = MvPolynomial.eval (spherePoint w) g := by
        intro w
        rw [hH, ← hgF, Fin.update_cons_zero]
      have hu : ‖(z0 0 : EuclideanSpace ℂ (Fin n))‖ = 1 := norm_eq_of_mem_sphere _
      have hgu : MvPolynomial.eval (WithLp.ofLp (z0 0 : EuclideanSpace ℂ (Fin n))) g ≠ 0 := by
        rw [hHw] at hz'
        exact hz'
      obtain ⟨hI, hL⟩ := hSJ n (a 0) g _ hg hu hgu
      have hN := sphere_zero_null hSJ g hg _ hu hgu
      simp_rw [hHw]
      exact ⟨hI, hL, hN⟩
    obtain ⟨C, hC⟩ : ∃ C, ∀ z, ‖onSpheres F z‖ ≤ C := by
      obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
      exact ⟨C, fun z => hC z (Set.mem_univ _)⟩
    set M := Real.log (max C 1) with hMdef
    have hM0 : 0 ≤ M := Real.log_nonneg (le_max_right _ _)
    have hLM : ∀ q, Real.log ‖H q‖ ≤ M := by
      intro q
      rcases (norm_nonneg (H q)).eq_or_lt with h0 | hpos
      · rw [← h0, Real.log_zero]
        exact hM0
      · exact Real.log_le_log hpos ((hC _).trans (le_max_left _ _))
    have habs : ∀ q, ‖Real.log ‖H q‖‖ ≤ 2 * M - Real.log ‖H q‖ := by
      intro q
      rw [Real.norm_eq_abs]
      have := hLM q
      rcases le_total 0 (Real.log ‖H q‖) with h | h
      · rw [abs_of_nonneg h]; linarith
      · rw [abs_of_nonpos h]; linarith
    have hfm : AEStronglyMeasurable (fun q => Real.log ‖H q‖) (ν.prod μ) :=
      (Real.measurable_log.comp hHm.norm).aestronglyMeasurable
    have hInt2 : Integrable (fun q => Real.log ‖H q‖) (ν.prod μ) := by
      rw [integrable_prod_iff hfm]
      refine ⟨hgood.mono fun z' hz' => (hslice z' hz').1, ?_⟩
      refine Integrable.mono'
        (g := fun z' => ∫ _w, (2 * M) ∂μ -
          (Real.log ‖H (z', z0 0)‖ - (a 0 : ℝ) / 2 * (harmonic (n - 1) : ℝ)))
        ((integrable_const _).sub (ihInt.sub (integrable_const _)))
        hfm.norm.integral_prod_right' ?_
      filter_upwards [hgood] with z' hz'
      obtain ⟨hI, hL, -⟩ := hslice z' hz'
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      calc ∫ w, ‖Real.log ‖H (z', w)‖‖ ∂μ ≤ ∫ w, (2 * M - Real.log ‖H (z', w)‖) ∂μ :=
            integral_mono hI.norm ((integrable_const _).sub hI) (fun w => habs _)
        _ = ∫ _w, (2 * M) ∂μ - ∫ w, Real.log ‖H (z', w)‖ ∂μ :=
            integral_sub (integrable_const _) hI
        _ ≤ _ := by linarith
    have hNull2 : (ν.prod μ) {q | H q = 0} = 0 := by
      have hms : MeasurableSet {q | H q = 0} := hHm (measurableSet_singleton 0)
      rw [Measure.measure_prod_null hms]
      filter_upwards [hgood] with z' hz'
      simpa [Set.preimage] using (hslice z' hz').2.2
    refine ⟨?_, ?_⟩
    · have h1 : (fun z => Real.log ‖onSpheres F z‖) = (fun q => Real.log ‖H q‖) ∘ e2 := by
        funext z
        simp only [Function.comp_apply]
        rw [hcomp z]
      rw [h1, mp2.integrable_comp_emb e2.measurableEmbedding]
      exact hInt2
    · have h1 : {z | onSpheres F z = 0} = e2 ⁻¹' {q | H q = 0} := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_preimage]
        rw [hcomp z]
      rw [h1, mp2.measure_preimage_emb e2.measurableEmbedding]
      exact hNull2
end ReciprocityTheory.MultiplicativeHeights
