-- Prove2me | solution 1 for SupportVectorMachines.Classification.theorem_5_31_instance_restricted_bayes_risk_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T04:26:26.798575+00:00
-- url     : https://prove2.me/submissions/f33aed41-465d-4510-a01d-6ef279244d00

import Mathlib
import Definitions.Def_SupportVectorMachines_Classification_RiskBasics_v2
import Definitions.Def_SupportVectorMachines_Classification_ClassificationLosses_v2
import Definitions.Def_SupportVectorMachines_Classification_RKHSAndSVM_v2

set_option autoImplicit false

open MeasureTheory

namespace P694

open SupportVectorMachines.Classification

/-- Every RKHS function is measurable (measurable kernel). -/
theorem rkhs_measurable {X : Type*} [MeasurableSpace X]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (f : H) : Measurable (toFun f) := by
  obtain ⟨hinj, ⟨kAt, hk, hev⟩, hmeas⟩ := hRKHS
  have hsymm : ∀ x x', k x x' = k x' x := by
    intro x x'
    rw [← hk x x', ← hk x' x, hev, hev, real_inner_comm]
  have hbasic : ∀ x, Measurable (toFun (kAt x)) := by
    intro x
    have : toFun (kAt x) = fun x' => k x' x := by
      funext x'; rw [hk, hsymm]
    rw [this]; exact hmeas x
  set S : Submodule ℝ H := Submodule.span ℝ (Set.range kAt) with hS
  have hspan : ∀ g ∈ S, Measurable (toFun g) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, rfl⟩ := hx
      exact hbasic y
    | zero => simp only [map_zero]; exact measurable_const
    | add a b _ _ ha hb => rw [map_add]; exact ha.add hb
    | smul c a _ ha => rw [map_smul]; exact ha.const_smul c
  have hperp : Sᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro g hg
    apply hinj
    rw [map_zero]
    funext x
    rw [hev]
    have : kAt x ∈ S := Submodule.subset_span ⟨x, rfl⟩
    have h0 := (Submodule.mem_orthogonal' S g).1 hg (kAt x) this
    simpa [real_inner_comm] using h0
  have htop : S.topologicalClosure = ⊤ := (Submodule.topologicalClosure_eq_top_iff (K := S)).2 hperp
  have hf : f ∈ closure (S : Set H) := by
    rw [← Submodule.topologicalClosure_coe, htop]; trivial
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hf
  refine measurable_of_tendsto_metrizable (fun n => hspan (u n) (hu n)) ?_
  rw [tendsto_pi_nhds]
  intro x
  simp only [hev]
  exact hlim.inner tendsto_const_nhds

theorem hinge_bound (y a t : ℝ) (hy : y = -1 ∨ y = 1) :
    max 0 (1 - y * a) ≤ max 0 (1 - y * t) + |a - max (-1) (min 1 t)| := by
  have h1 := le_abs_self (a - max (-1) (min 1 t))
  have h2 := neg_le_abs (a - max (-1) (min 1 t))
  have h0 : 0 ≤ |a - max (-1) (min 1 t)| := abs_nonneg _
  rcases hy with rfl | rfl
  · have hc : 1 + max (-1) (min 1 t) ≤ max 0 (1 - -1 * t) := by
      rcases le_total (-1) t with h | h
      · have : max (-1) (min 1 t) ≤ t := max_le h (min_le_right _ _)
        linarith [le_max_right 0 (1 - -1 * t)]
      · have : max (-1) (min 1 t) = -1 := by
          rw [min_eq_right (by linarith)]; exact max_eq_left h
        rw [this]; norm_num
    exact max_le (by linarith [le_max_left 0 (1 - -1 * t)]) (by linarith)
  · have hc : 1 - max (-1) (min 1 t) ≤ max 0 (1 - 1 * t) := by
      rcases le_total t 1 with h | h
      · have : t ≤ max (-1) (min 1 t) := le_max_of_le_right (le_min h le_rfl)
        linarith [le_max_right 0 (1 - 1 * t)]
      · have : max (-1) (min 1 t) = 1 := by
          rw [min_eq_left h]; norm_num
        rw [this]; norm_num
    exact max_le (by linarith [le_max_left 0 (1 - 1 * t)]) (by linarith)

end P694

open MeasureTheory SupportVectorMachines.Classification in
theorem solution {X : Type*} [MeasurableSpace X]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (hY : P (Set.univ ×ˢ ({-1, 1} : Set ℝ)) = 1)
    (hDense : DenseInL1 H toFun (P.map Prod.fst)) :
    restrictedBayesRisk H toFun hingeLoss P = bayesRisk hingeLoss P := by
  have hmeasH := P694.rkhs_measurable H toFun k hRKHS
  have hms : MeasurableSet ((Set.univ : Set X) ×ˢ ({-1, 1} : Set ℝ)) :=
    MeasurableSet.univ.prod (Set.toFinite _).measurableSet
  have h0 : P ((Set.univ : Set X) ×ˢ ({-1, 1} : Set ℝ))ᶜ = 0 := (prob_compl_eq_zero_iff hms).2 hY
  have hae : ∀ᵐ p ∂P, p.2 = -1 ∨ p.2 = 1 := by
    have hS : ∀ᵐ p ∂P, p ∈ (Set.univ : Set X) ×ˢ ({-1, 1} : Set ℝ) := mem_ae_iff.2 h0
    filter_upwards [hS] with p hp
    simpa using hp
  apply le_antisymm
  · unfold bayesRisk
    refine le_iInf₂ fun f hf => ?_
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    set g : X → ℝ := fun x => max (-1) (min 1 (f x)) with hg
    have hgm : Measurable g := measurable_const.max (measurable_const.min hf)
    have hgi : Integrable g (P.map Prod.fst) := by
      refine Integrable.of_bound hgm.aestronglyMeasurable 1 (ae_of_all _ fun x => ?_)
      simp only [hg, Real.norm_eq_abs, abs_le]
      constructor
      · exact le_max_left _ _
      · exact max_le (by norm_num) (min_le_left _ _)
    obtain ⟨h, hhi, hhε⟩ := hDense g hgi ε (NNReal.coe_pos.2 hε)
    have hm2 : Measurable fun x => ENNReal.ofReal |toFun h x - g x| :=
      ENNReal.measurable_ofReal.comp ((hmeasH h).sub hgm).abs
    have hfm : Measurable fun p : X × ℝ =>
        ENNReal.ofReal ((hingeLoss : Loss X) p.1 p.2 (f p.1)) :=
      ENNReal.measurable_ofReal.comp ((hingeLoss : Loss X).measurable.comp
        (measurable_fst.prodMk (measurable_snd.prodMk (hf.comp measurable_fst))))
    calc restrictedBayesRisk H toFun hingeLoss P ≤ risk hingeLoss P (toFun h) := iInf_le _ h
      _ ≤ ∫⁻ p, (ENNReal.ofReal ((hingeLoss : Loss X) p.1 p.2 (f p.1)) +
            ENNReal.ofReal |toFun h p.1 - g p.1|) ∂P := by
          unfold risk
          refine lintegral_mono_ae ?_
          filter_upwards [hae] with p hp
          rw [← ENNReal.ofReal_add ((hingeLoss : Loss X).nonneg _ _ _) (abs_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (P694.hinge_bound p.2 _ _ hp)
      _ = risk hingeLoss P f + ∫⁻ p, ENNReal.ofReal |toFun h p.1 - g p.1| ∂P := by
          unfold risk
          rw [lintegral_add_left hfm]
      _ ≤ risk hingeLoss P f + ε := by
          gcongr
          have hint := ofReal_integral_eq_lintegral_ofReal
            (f := fun x => |toFun h x - g x|) (μ := P.map Prod.fst) (hhi.sub hgi).abs
            (ae_of_all _ fun x => abs_nonneg _)
          rw [← lintegral_map hm2 measurable_fst, ← hint, ← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal hhε.le
  · unfold bayesRisk restrictedBayesRisk
    exact le_iInf fun h => iInf₂_le (toFun h) (hmeasH h)
