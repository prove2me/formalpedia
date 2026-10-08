-- Prove2me | solution 1 for WassDDRO.Consistency.theorem_3_6
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T12:56:26.166344+00:00
-- url     : https://prove2.me/submissions/ce0d0bf6-7f72-49ea-aa89-1cac7ebddd7b

import Definitions.Def_WassDDRO_Consistency_Setting
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_WassersteinDRO_Duality_worstCaseRisk
import Mathlib
set_option autoImplicit false
section
set_option autoImplicit false
open MeasureTheory
namespace WassConsistencyCodex

noncomputable def transportCost {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (π : Measure (E × E)) : ENNReal := ∫⁻ z : E × E, ENNReal.ofReal ‖z.1-z.2‖ ∂π

theorem transportCost_joint_bound {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] (τ : Measure (E × (E × E))) :
    transportCost τ.snd ≤ transportCost (τ.map (Prod.map id Prod.fst)) +
      transportCost (τ.map (Prod.map id Prod.snd)) := by
  have hf : Measurable (fun z : E × E => ENNReal.ofReal ‖z.1-z.2‖) :=
    (measurable_fst.sub measurable_snd).norm.ennreal_ofReal
  unfold transportCost
  rw [Measure.snd,lintegral_map hf measurable_snd,
    lintegral_map hf (show Measurable (Prod.map id Prod.fst : E × (E × E) → E × E) by fun_prop),
    lintegral_map hf (show Measurable (Prod.map id Prod.snd : E × (E × E) → E × E) by fun_prop)]
  have hl : Measurable (fun z : E × (E × E) => ENNReal.ofReal ‖z.1-z.2.1‖) := by fun_prop
  change (∫⁻ z : E × (E × E), ENNReal.ofReal ‖z.2.1-z.2.2‖ ∂τ) ≤
    (∫⁻ z : E × (E × E), ENNReal.ofReal ‖z.1-z.2.1‖ ∂τ) +
    (∫⁻ z : E × (E × E), ENNReal.ofReal ‖z.1-z.2.2‖ ∂τ)
  rw [← lintegral_add_left hl]
  apply lintegral_mono
  intro z
  change ENNReal.ofReal ‖z.2.1-z.2.2‖ ≤ ENNReal.ofReal ‖z.1-z.2.1‖ + ENNReal.ofReal ‖z.1-z.2.2‖
  rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have he : z.2.1-z.2.2 = (z.2.1-z.1)+(z.1-z.2.2) := by abel
  rw [he]
  have hn := norm_add_le (z.2.1-z.1) (z.1-z.2.2)
  rwa [norm_sub_rev z.2.1 z.1] at hn
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace WassConsistencyCodex

theorem integrable_distance_of_finite_cost {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (π : Measure (E × E)) (hc : transportCost π < ∞) :
    Integrable (fun z : E × E => ‖z.1-z.2‖) π := by
  refine ⟨(measurable_fst.sub measurable_snd).norm.aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simpa only [norm_norm,transportCost] using hc

theorem coupling_integral_bound {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P Q : Measure E) (π : Measure (E × E))
    (hπ : π.map Prod.fst = P ∧ π.map Prod.snd = Q)
    (hc : transportCost π < ∞) (Ξ : Set E) (hQ : Q Ξᶜ = 0)
    (h f : E → ℝ) (K : NNReal) (hf : LipschitzWith K f)
    (hintf : Integrable f P) (hinth : Integrable h Q) (hhf : ∀ y ∈ Ξ, h y ≤ f y) :
    (∫ y, h y ∂Q) ≤ (∫ x, f x ∂P)+(K : ℝ)*(transportCost π).toReal := by
  have hfm : Integrable f (π.map Prod.fst) := by rwa [hπ.1]
  have hhm : Integrable h (π.map Prod.snd) := by rwa [hπ.2]
  have hfi : Integrable (fun z : E × E => f z.1) π :=
    (integrable_map_measure hfm.aestronglyMeasurable measurable_fst.aemeasurable).mp hfm
  have hhi : Integrable (fun z : E × E => h z.2) π :=
    (integrable_map_measure hhm.aestronglyMeasurable measurable_snd.aemeasurable).mp hhm
  have hci := integrable_distance_of_finite_cost π hc
  have hs : ∀ᵐ z : E × E ∂π, z.2 ∈ Ξ := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    rw [hπ.2]
    exact mem_ae_iff.mpr hQ
  have hb : ∀ᵐ z : E × E ∂π, h z.2 ≤ f z.1+(K : ℝ)*‖z.1-z.2‖ := by
    filter_upwards [hs] with z hz
    have hd := hf.dist_le_mul z.2 z.1
    rw [Real.dist_eq,dist_eq_norm,norm_sub_rev z.2 z.1] at hd
    have hl := le_abs_self (f z.2-f z.1)
    have he := hhf z.2 hz
    linarith
  have hi := integral_mono_ae hhi (hfi.add (hci.const_mul (K : ℝ))) hb
  change (∫ z : E × E, h z.2 ∂π) ≤
    ∫ z : E × E, f z.1+(K : ℝ)*‖z.1-z.2‖ ∂π at hi
  rw [integral_add hfi (hci.const_mul (K : ℝ)),integral_const_mul] at hi
  have hp : (∫ z : E × E, f z.1 ∂π) = ∫ x, f x ∂P := by
    rw [← integral_map measurable_fst.aemeasurable hfm.aestronglyMeasurable,hπ.1]
  have hq : (∫ z : E × E, h z.2 ∂π) = ∫ y, h y ∂Q := by
    rw [← integral_map measurable_snd.aemeasurable hhm.aestronglyMeasurable,hπ.2]
  have ht : (∫ z : E × E, ‖z.1-z.2‖ ∂π) = (transportCost π).toReal := by
    exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun z => norm_nonneg _)) hci.aestronglyMeasurable
  rw [hp,hq,ht] at hi
  exact hi
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
namespace WassConsistencyCodex

theorem jointKernel_left {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (R : Measure A) [SFinite R] (K : Kernel A B) [IsMarkovKernel K]
    (L : Kernel A C) [IsMarkovKernel L] :
    (R ⊗ₘ (K ×ₖ L)).map (Prod.map id Prod.fst) = R ⊗ₘ K := by
  rw [← Measure.compProd_map measurable_fst]
  rw [← Kernel.fst_eq,Kernel.fst_prod]

theorem jointKernel_right {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (R : Measure A) [SFinite R] (K : Kernel A B) [IsMarkovKernel K]
    (L : Kernel A C) [IsMarkovKernel L] :
    (R ⊗ₘ (K ×ₖ L)).map (Prod.map id Prod.snd) = R ⊗ₘ L := by
  rw [← Measure.compProd_map measurable_snd]
  rw [← Kernel.snd_eq,Kernel.snd_prod]
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
namespace WassConsistencyCodex

noncomputable def glueCoupling {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
    (R : Measure E) (π ρ : Measure (E × E)) [IsFiniteMeasure π] [IsFiniteMeasure ρ] :
    Measure (E × E) := (R ⊗ₘ (π.condKernel ×ₖ ρ.condKernel)).snd

theorem glueCoupling_marginals {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
    (R : Measure E) [SFinite R] (π ρ : Measure (E × E)) [IsFiniteMeasure π] [IsFiniteMeasure ρ]
    (hπ : π.fst = R) (hρ : ρ.fst = R) :
    (glueCoupling R π ρ).fst = π.snd ∧ (glueCoupling R π ρ).snd = ρ.snd := by
  let τ := R ⊗ₘ (π.condKernel ×ₖ ρ.condKernel)
  have hl : τ.map (Prod.map id Prod.fst) = π := by
    dsimp [τ]
    rw [jointKernel_left,← hπ,Measure.disintegrate]
  have hr : τ.map (Prod.map id Prod.snd) = ρ := by
    dsimp [τ]
    rw [jointKernel_right,← hρ,Measure.disintegrate]
  constructor
  · have hm := congrArg (fun μ : Measure (E × E) => μ.map Prod.snd) hl
    rw [Measure.map_map measurable_snd (by fun_prop)] at hm
    change τ.map (fun z => z.2.1) = π.snd at hm
    change τ.snd.fst = π.snd
    rw [Measure.fst,Measure.snd,Measure.map_map measurable_fst measurable_snd]
    exact hm
  · have hm := congrArg (fun μ : Measure (E × E) => μ.map Prod.snd) hr
    rw [Measure.map_map measurable_snd (by fun_prop)] at hm
    change τ.map (fun z => z.2.2) = ρ.snd at hm
    change τ.snd.snd = ρ.snd
    rw [Measure.snd,Measure.snd,Measure.map_map measurable_snd measurable_snd]
    exact hm
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
namespace WassConsistencyCodex

theorem transportCost_glue {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] [StandardBorelSpace E]
    (R : Measure E) [SFinite R] (π ρ : Measure (E × E)) [IsFiniteMeasure π] [IsFiniteMeasure ρ]
    (hπ : π.fst = R) (hρ : ρ.fst = R) :
    transportCost (glueCoupling R π ρ) ≤ transportCost π + transportCost ρ := by
  have hl : (R ⊗ₘ (π.condKernel ×ₖ ρ.condKernel)).map (Prod.map id Prod.fst) = π := by
    rw [jointKernel_left,← hπ,Measure.disintegrate]
  have hr : (R ⊗ₘ (π.condKernel ×ₖ ρ.condKernel)).map (Prod.map id Prod.snd) = ρ := by
    rw [jointKernel_right,← hρ,Measure.disintegrate]
  have hc := transportCost_joint_bound (R ⊗ₘ (π.condKernel ×ₖ ρ.condKernel))
  rw [hl,hr] at hc
  exact hc
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassConsistencyCodex

theorem wassersteinDistance_symm {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] (p : ℝ) (P Q : Measure E) :
    WassersteinDRO.Duality.wassersteinDistance p P Q =
      WassersteinDRO.Duality.wassersteinDistance p Q P := by
  have hcost (P Q : Measure E) :
      (⨅ (π : Measure (E × E)) (_ : π.map Prod.fst = P ∧ π.map Prod.snd = Q),
        ∫⁻ z : E × E, ENNReal.ofReal (‖z.1-z.2‖ ^ p) ∂π) ≤
      (⨅ (π : Measure (E × E)) (_ : π.map Prod.fst = Q ∧ π.map Prod.snd = P),
        ∫⁻ z : E × E, ENNReal.ofReal (‖z.1-z.2‖ ^ p) ∂π) := by
    apply le_iInf
    intro π
    apply le_iInf
    intro hπ
    apply iInf_le_of_le (π.map Prod.swap)
    have hm : (π.map Prod.swap).map Prod.fst = P ∧ (π.map Prod.swap).map Prod.snd = Q := by
      constructor
      · change (π.map Prod.swap).fst = P
        rw [Measure.fst_map_swap]
        exact hπ.2
      · change (π.map Prod.swap).snd = Q
        rw [Measure.snd_map_swap]
        exact hπ.1
    apply iInf_le_of_le hm
    have hf : Measurable (fun z : E × E => ENNReal.ofReal (‖z.1-z.2‖ ^ p)) :=
      (((measurable_fst.sub measurable_snd).norm.pow_const p).ennreal_ofReal)
    rw [lintegral_map hf measurable_swap]
    change (∫⁻ z : E × E, ENNReal.ofReal (‖z.2-z.1‖ ^ p) ∂π) ≤ _
    simp only [norm_sub_rev]
    exact le_rfl
  unfold WassersteinDRO.Duality.wassersteinDistance
  rw [le_antisymm (hcost P Q) (hcost Q P)]
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassConsistencyCodex
open WassersteinDRO.Duality

theorem wassersteinDistance_one_eq {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (P Q : Measure E) : wassersteinDistance 1 P Q =
      ⨅ (π : Measure (E × E)) (_ : π.map Prod.fst = P ∧ π.map Prod.snd = Q), transportCost π := by
  simp only [wassersteinDistance,one_div_one,ENNReal.rpow_one,Real.rpow_one,transportCost]

theorem wassersteinDistance_common_middle {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [StandardBorelSpace E]
    (P R Q : Measure E) [IsProbabilityMeasure R] :
    wassersteinDistance 1 P Q ≤ wassersteinDistance 1 R P + wassersteinDistance 1 R Q := by
  rw [wassersteinDistance_one_eq,wassersteinDistance_one_eq,wassersteinDistance_one_eq]
  apply ENNReal.le_iInf₂_add_iInf₂
  intro π hπ ρ hρ
  haveI : IsProbabilityMeasure (π.map Prod.fst) := hπ.1.symm ▸ inferInstance
  haveI : IsProbabilityMeasure π := Measure.isProbabilityMeasure_of_map Prod.fst
  haveI : IsProbabilityMeasure (ρ.map Prod.fst) := hρ.1.symm ▸ inferInstance
  haveI : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_of_map Prod.fst
  have hm := glueCoupling_marginals R π ρ hπ.1 hρ.1
  apply (iInf_le_of_le (glueCoupling R π ρ) (iInf_le_of_le
    (show (glueCoupling R π ρ).map Prod.fst = P ∧ (glueCoupling R π ρ).map Prod.snd = Q from
      ⟨hm.1.trans hπ.2,hm.2.trans hρ.2⟩) le_rfl)).trans
  exact transportCost_glue R π ρ hπ.1 hρ.1

theorem wassersteinDistance_triangle {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [StandardBorelSpace E]
    (P R Q : Measure E) [IsProbabilityMeasure R] :
    wassersteinDistance 1 P Q ≤ wassersteinDistance 1 P R + wassersteinDistance 1 R Q := by
  rw [wassersteinDistance_symm 1 P R]
  exact wassersteinDistance_common_middle P R Q
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassConsistencyCodex
open WassersteinDRO.Duality

theorem exists_coupling_cost_lt {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (P Q : Measure E) (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : ε < δ)
    (hd : wassersteinDistance 1 P Q ≤ ENNReal.ofReal ε) :
    ∃ π : Measure (E × E), (π.map Prod.fst = P ∧ π.map Prod.snd = Q) ∧
      transportCost π < ENNReal.ofReal δ := by
  have he : ENNReal.ofReal ε < ENNReal.ofReal δ :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hε).mpr hδ
  have hi := hd.trans_lt he
  rw [wassersteinDistance_one_eq] at hi
  obtain ⟨π,hπ⟩ := iInf_lt_iff.mp hi
  obtain ⟨hguard,hcost⟩ := iInf_lt_iff.mp hπ
  exact ⟨π,hguard,hcost⟩

theorem le_penalty_of_all_larger_radii (u c K ε : ℝ) (hK : 0 ≤ K)
    (hu : ∀ δ, ε < δ → u ≤ c+K*δ) : u ≤ c+K*ε := by
  by_cases hz : K = 0
  · simpa only [hz,zero_mul,add_zero] using hu (ε+1) (by linarith)
  · have hk : 0 < K := lt_of_le_of_ne hK (Ne.symm hz)
    apply le_of_forall_gt_imp_ge_of_dense
    intro b hb
    let δ := (b-c)/K
    have hd : ε < δ := (lt_div_iff₀ hk).mpr (by linarith)
    have hv := hu δ hd
    have he : c+K*δ = b := by dsimp [δ]; field_simp <;> ring
    rwa [he] at hv
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace WassConsistencyCodex
open WassersteinDRO.Duality

theorem integral_le_of_wasserstein_bound {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P Q : Measure E) (ε : ℝ) (hε : 0 ≤ ε)
    (hd : wassersteinDistance 1 P Q ≤ ENNReal.ofReal ε)
    (Ξ : Set E) (hQ : Q Ξᶜ = 0) (h f : E → ℝ) (K : NNReal) (hf : LipschitzWith K f)
    (hintf : Integrable f P) (hinth : Integrable h Q) (hhf : ∀ y ∈ Ξ, h y ≤ f y) :
    (∫ y, h y ∂Q) ≤ (∫ x, f x ∂P)+(K : ℝ)*ε := by
  apply le_penalty_of_all_larger_radii _ _ _ ε K.coe_nonneg
  intro δ hδ
  obtain ⟨π,hπ,hcost⟩ := exists_coupling_cost_lt P Q ε δ hε hδ hd
  have hc : transportCost π < ∞ := hcost.trans (ENNReal.ofReal_lt_top)
  have hb := coupling_integral_bound P Q π hπ hc Ξ hQ h f K hf hintf hinth hhf
  exact hb.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (ENNReal.toReal_lt_of_lt_ofReal hcost).le K.coe_nonneg))
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassConsistencyCodex
open WassersteinDRO.Duality

theorem worstCaseRisk_le_lipschitz_expectation {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (PN : Measure E) (Ξ : Set E) (ε : ℝ) (hε : 0 ≤ ε)
    (h f : E → ℝ) (K : NNReal) (hf : LipschitzWith K f)
    (hint : Integrable f PN) (hhf : ∀ y ∈ Ξ, h y ≤ f y) :
    worstCaseRisk ε 1 Ξ PN h ≤ ((∫ x, f x ∂PN)+(K : ℝ)*ε : ℝ) := by
  unfold worstCaseRisk
  apply iSup_le
  intro Q
  apply iSup_le
  intro hball
  apply iSup_le
  intro hInt
  apply EReal.coe_le_coe_iff.mpr
  have hd : wassersteinDistance 1 PN Q ≤ ENNReal.ofReal ε := by
    rw [wassersteinDistance_symm 1 PN Q]
    exact hball.2.2
  exact integral_le_of_wasserstein_bound PN Q ε hε hd Ξ hball.2.1 h f K hf hint hInt hhf

theorem worstCaseRisk_le_true_lipschitz_expectation {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P PN : Measure E) (Ξ : Set E) (ε : ℝ) (hε : 0 ≤ ε)
    (hd : wassersteinDistance 1 P PN ≤ ENNReal.ofReal ε)
    (h f : E → ℝ) (K : NNReal) (hf : LipschitzWith K f)
    (hintP : Integrable f P) (hintPN : Integrable f PN) (hhf : ∀ y ∈ Ξ, h y ≤ f y) :
    worstCaseRisk ε 1 Ξ PN h ≤ ((∫ x, f x ∂P)+2*(K : ℝ)*ε : ℝ) := by
  apply (worstCaseRisk_le_lipschitz_expectation PN Ξ ε hε h f K hf hintPN hhf).trans
  apply EReal.coe_le_coe_iff.mpr
  have he := integral_le_of_wasserstein_bound P PN ε hε hd Set.univ (by simp)
    f f K hf hintP hintPN (fun _ _ => le_rfl)
  linarith
end WassConsistencyCodex

end

section
set_option autoImplicit false
namespace WassConsistencyCodex

noncomputable def upperEnvelope {E : Type*} [NormedAddCommGroup E] (Ξ : Set E) (h : E → ℝ)
    (lam : ℝ) (x : E) : ℝ := sSup ((fun y => h y-lam*‖y-x‖) '' Ξ)

theorem envelope_point_bound {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (h : E → ℝ) (L lam : ℝ) (hL : 0 ≤ L) (hlam : L ≤ lam)
    (hg : ∀ y∈Ξ, h y ≤ L*(1+‖y‖)) (x y : E) (hy : y∈Ξ) :
    h y-lam*‖y-x‖ ≤ L*(1+‖x‖) := by
  have hn : ‖y‖ ≤ ‖y-x‖+‖x‖ := by
    calc
      _ = ‖(y-x)+x‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have hm := mul_le_mul_of_nonneg_left hn hL
  have hp := mul_le_mul_of_nonneg_right hlam (norm_nonneg (y-x))
  nlinarith [hg y hy]

theorem envelope_bddAbove {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (h : E → ℝ) (L lam : ℝ) (hL : 0 ≤ L) (hlam : L ≤ lam)
    (hg : ∀ y∈Ξ, h y ≤ L*(1+‖y‖)) (x : E) :
    BddAbove ((fun y => h y-lam*‖y-x‖) '' Ξ) := by
  refine ⟨L*(1+‖x‖),?_⟩
  rintro r ⟨y,hy,rfl⟩
  exact envelope_point_bound Ξ h L lam hL hlam hg x y hy

theorem upperEnvelope_upper {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (hne : Ξ.Nonempty) (h : E → ℝ) (L lam : ℝ) (hL : 0 ≤ L) (hlam : L ≤ lam)
    (hg : ∀ y∈Ξ, h y ≤ L*(1+‖y‖)) (x : E) : upperEnvelope Ξ h lam x ≤ L*(1+‖x‖) := by
  apply csSup_le (hne.image _)
  rintro r ⟨y,hy,rfl⟩
  exact envelope_point_bound Ξ h L lam hL hlam hg x y hy

theorem le_upperEnvelope_on {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (h : E → ℝ) (L lam : ℝ) (hL : 0 ≤ L) (hlam : L ≤ lam)
    (hg : ∀ y∈Ξ, h y ≤ L*(1+‖y‖)) (x : E) (hx : x∈Ξ) : h x ≤ upperEnvelope Ξ h lam x := by
  apply le_csSup (envelope_bddAbove Ξ h L lam hL hlam hg x)
  exact ⟨x,hx,by simp⟩
end WassConsistencyCodex

end

section
set_option autoImplicit false
namespace WassConsistencyCodex

theorem upperEnvelope_le_add {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (hne : Ξ.Nonempty) (h : E → ℝ) (L lam : ℝ) (hL : 0 ≤ L) (hlam : L ≤ lam)
    (hg : ∀ z∈Ξ, h z ≤ L*(1+‖z‖)) (x y : E) :
    upperEnvelope Ξ h lam x ≤ upperEnvelope Ξ h lam y+lam*‖x-y‖ := by
  apply csSup_le (hne.image _)
  rintro r ⟨z,hz,rfl⟩
  have hd : ‖z-y‖ ≤ ‖z-x‖+‖x-y‖ := by
    have he : z-y=(z-x)+(x-y) := by abel
    rw [he]
    exact norm_add_le _ _
  have hm := mul_le_mul_of_nonneg_left hd (hL.trans hlam)
  have hy : h z-lam*‖z-y‖ ≤ upperEnvelope Ξ h lam y :=
    le_csSup (envelope_bddAbove Ξ h L lam hL hlam hg y) ⟨z,hz,rfl⟩
  linarith

theorem upperEnvelope_lipschitz {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (hne : Ξ.Nonempty) (h : E → ℝ) (L lam : ℝ) (hL : 0 ≤ L) (hlam : L ≤ lam)
    (hg : ∀ z∈Ξ, h z ≤ L*(1+‖z‖)) :
    LipschitzWith (Real.toNNReal lam) (upperEnvelope Ξ h lam) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.coe_toNNReal lam (hL.trans hlam),Real.dist_eq,dist_eq_norm,abs_le]
  constructor
  · have hm := upperEnvelope_le_add Ξ hne h L lam hL hlam hg y x
    rw [norm_sub_rev y x] at hm
    linarith
  · have hm := upperEnvelope_le_add Ξ hne h L lam hL hlam hg x y
    linarith

theorem upperEnvelope_antitone_penalty {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (hne : Ξ.Nonempty) (h : E → ℝ) (L lam mu : ℝ) (hL : 0 ≤ L)
    (hlam : L ≤ lam) (hmu : lam ≤ mu) (hg : ∀ z∈Ξ, h z ≤ L*(1+‖z‖)) (x : E) :
    upperEnvelope Ξ h mu x ≤ upperEnvelope Ξ h lam x := by
  apply csSup_le (hne.image _)
  rintro r ⟨z,hz,rfl⟩
  have hp := mul_le_mul_of_nonneg_right hmu (norm_nonneg (z-x))
  have hm : h z-lam*‖z-x‖ ≤ upperEnvelope Ξ h lam x :=
    le_csSup (envelope_bddAbove Ξ h L lam hL hlam hg x) ⟨z,hz,rfl⟩
  linarith
end WassConsistencyCodex

end

section
set_option autoImplicit false
open Filter Topology
namespace WassConsistencyCodex

theorem upperEnvelope_eventual_upper {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (h : E → ℝ) (husc : UpperSemicontinuousOn h Ξ) (L : ℝ) (hL : 0 ≤ L)
    (hg : ∀ y∈Ξ, h y ≤ L*(1+‖y‖)) (x : E) (hx : x∈Ξ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ lam0 : ℝ, L ≤ lam0 ∧ ∀ lam : ℝ, lam0 ≤ lam → upperEnvelope Ξ h lam x ≤ h x+δ := by
  have hn : ∀ᶠ y in 𝓝[Ξ] x, h y < h x+δ := (husc x hx) _ (by linarith)
  obtain ⟨ρ,hρ,hlocal⟩ := Metric.mem_nhdsWithin_iff.mp hn
  let C : ℝ := L*(1+‖x‖)
  let w : ℝ := max 0 ((C-(h x+δ))/ρ)
  have hw : 0 ≤ w := le_max_left _ _
  have hwr : C-(h x+δ) ≤ w*ρ := (div_le_iff₀ hρ).mp (le_max_right _ _)
  refine ⟨L+w,by linarith,?_⟩
  intro lam hlam0
  have hlam : L ≤ lam := by linarith
  have hlam0' : 0 ≤ lam := hL.trans hlam
  have hdiff : w ≤ lam-L := by linarith
  have hdiff0 : 0 ≤ lam-L := sub_nonneg.mpr hlam
  apply csSup_le ((show Ξ.Nonempty from ⟨x,hx⟩).image _)
  rintro r ⟨y,hy,rfl⟩
  by_cases hd : ‖y-x‖ < ρ
  · have hh : h y < h x+δ := hlocal ⟨by simpa [Metric.mem_ball,dist_eq_norm] using hd,hy⟩
    have hp : 0 ≤ lam*‖y-x‖ := mul_nonneg hlam0' (norm_nonneg _)
    linarith
  · have hdist : ρ ≤ ‖y-x‖ := le_of_not_gt hd
    have hp : w*ρ ≤ (lam-L)*‖y-x‖ :=
      (mul_le_mul_of_nonneg_right hdiff hρ.le).trans (mul_le_mul_of_nonneg_left hdist hdiff0)
    have hh := envelope_point_bound Ξ h L L hL le_rfl hg x y hy
    change h y-L*‖y-x‖ ≤ C at hh
    calc
      _ = (h y-L*‖y-x‖)-(lam-L)*‖y-x‖ := by ring
      _ ≤ C-(lam-L)*‖y-x‖ := sub_le_sub_right hh _
      _ ≤ _ := by linarith
end WassConsistencyCodex

end

section
set_option autoImplicit false
open Filter Topology
namespace WassConsistencyCodex

theorem upperEnvelope_nat_tendsto {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (h : E → ℝ) (husc : UpperSemicontinuousOn h Ξ) (L : ℝ) (hL : 0 ≤ L)
    (hg : ∀ y∈Ξ, h y ≤ L*(1+‖y‖)) (x : E) (hx : x∈Ξ) :
    Tendsto (fun k : ℕ => upperEnvelope Ξ h (L+(k : ℝ)+1) x) atTop (𝓝 (h x)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨lam0,hL0,hupper⟩ := upperEnvelope_eventual_upper Ξ h husc L hL hg x hx (ε/2) (by positivity)
  obtain ⟨N,hN⟩ := exists_nat_ge lam0
  refine ⟨N,?_⟩
  intro k hk
  have hNk : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlam : lam0 ≤ L+(k : ℝ)+1 := by linarith
  have hΓ : L ≤ L+(k : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hlo := le_upperEnvelope_on Ξ h L (L+(k : ℝ)+1) hL hΓ hg x hx
  have hup := hupper (L+(k : ℝ)+1) hlam
  rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hlo)]
  linarith

theorem upperEnvelope_nat_antitone {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (hne : Ξ.Nonempty) (h : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hg : ∀ y∈Ξ, h y ≤ L*(1+‖y‖)) (k : ℕ) (x : E) :
    upperEnvelope Ξ h (L+((k+1 : ℕ) : ℝ)+1) x ≤ upperEnvelope Ξ h (L+(k : ℝ)+1) x := by
  apply upperEnvelope_antitone_penalty Ξ hne h L _ _ hL _ _ hg x
  · linarith [Nat.cast_nonneg (α := ℝ) k]
  · push_cast
    linarith
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassConsistencyCodex

theorem norm_le_exp_rpow {E : Type*} [NormedAddCommGroup E] (ξ : E) (a : ℝ) (ha : 1 ≤ a) :
    ‖ξ‖ ≤ Real.exp (‖ξ‖ ^ a) := by
  by_cases hn : ‖ξ‖ ≤ 1
  · have hp : 0 ≤ ‖ξ‖ ^ a := Real.rpow_nonneg (norm_nonneg ξ) a
    have he : 1 ≤ Real.exp (‖ξ‖ ^ a) := Real.one_le_exp_iff.mpr hp
    exact hn.trans he
  · have hp : ‖ξ‖ ≤ ‖ξ‖ ^ a := Real.self_le_rpow_of_one_le (le_of_not_ge hn) ha
    have he := Real.add_one_le_exp (‖ξ‖ ^ a)
    linarith

theorem integrable_norm_of_exp_moment {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (P : Measure E) (a : ℝ) (ha : 1 ≤ a)
    (hA : Integrable (fun ξ => Real.exp (‖ξ‖ ^ a)) P) : Integrable (fun ξ => ‖ξ‖) P := by
  apply hA.mono' measurable_norm.aestronglyMeasurable
  apply ae_of_all
  intro ξ
  simpa only [norm_norm] using norm_le_exp_rpow ξ a ha

theorem integrable_of_linear_growth {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (P : Measure E) [IsFiniteMeasure P]
    (Ξ : Set E) (hP : P Ξᶜ = 0) (f : E → ℝ) (hf : Measurable f)
    (L : ℝ) (hg : ∀ ξ ∈ Ξ, |f ξ| ≤ L*(1+‖ξ‖))
    (hn : Integrable (fun ξ => ‖ξ‖) P) : Integrable f P := by
  have hdom : Integrable (fun ξ => L*(1+‖ξ‖)) P := ((integrable_const (1 : ℝ)).add hn).const_mul L
  apply hdom.mono' hf.aestronglyMeasurable
  have hs : ∀ᵐ ξ ∂P, ξ ∈ Ξ := mem_ae_iff.mpr hP
  filter_upwards [hs] with ξ hξ
  simpa only [Real.norm_eq_abs] using hg ξ hξ
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassConsistencyCodex

theorem integrable_lipschitz_of_first_moment {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (P : Measure E) [IsFiniteMeasure P]
    (f : E → ℝ) (K : NNReal) (hf : LipschitzWith K f)
    (hn : Integrable (fun ξ => ‖ξ‖) P) : Integrable f P := by
  apply integrable_of_norm_sub_le hf.continuous.measurable.aestronglyMeasurable
    (integrable_const (f 0)) (hn.const_mul (K : ℝ))
  apply ae_of_all
  intro ξ
  simpa only [Real.norm_eq_abs,Real.dist_eq,dist_zero_left] using hf.dist_le_mul 0 ξ
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory Filter Topology
namespace WassConsistencyCodex

theorem upperEnvelope_integral_tendsto {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (P : Measure E) [IsProbabilityMeasure P]
    (Ξ : Set E) (hP : P Ξᶜ = 0) (h : E → ℝ) (husc : UpperSemicontinuousOn h Ξ)
    (L : ℝ) (hL : 0 ≤ L) (hgrowth : ∀ ξ ∈ Ξ, |h ξ| ≤ L*(1+‖ξ‖))
    (hn : Integrable (fun ξ => ‖ξ‖) P) :
    Tendsto (fun k : ℕ => ∫ ξ, upperEnvelope Ξ h (L+(k : ℝ)+1) ξ ∂P)
      atTop (𝓝 (∫ ξ, h ξ ∂P)) := by
  have hs : ∀ᵐ ξ ∂P, ξ ∈ Ξ := mem_ae_iff.mpr hP
  have hne : Ξ.Nonempty := hs.exists
  have hg : ∀ ξ ∈ Ξ, h ξ ≤ L*(1+‖ξ‖) := fun ξ hξ => (le_abs_self _).trans (hgrowth ξ hξ)
  have hΓ (k : ℕ) : L ≤ L+(k : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  apply tendsto_integral_of_dominated_convergence (fun ξ => L*(1+‖ξ‖))
  · intro k
    exact (upperEnvelope_lipschitz Ξ hne h L _ hL (hΓ k) hg).continuous.measurable.aestronglyMeasurable
  · exact ((integrable_const (1 : ℝ)).add hn).const_mul L
  · intro k
    filter_upwards [hs] with ξ hξ
    rw [Real.norm_eq_abs,abs_le]
    constructor
    · exact (abs_le.mp (hgrowth ξ hξ)).1.trans
        (le_upperEnvelope_on Ξ h L _ hL (hΓ k) hg ξ hξ)
    · exact upperEnvelope_upper Ξ hne h L _ hL (hΓ k) hg ξ
  · exact hs.mono (fun ξ hξ => upperEnvelope_nat_tendsto Ξ h husc L hL hg ξ hξ)
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory WassersteinDRO.Duality
namespace WassConsistencyCodex
/-- Reuses the checked finite-atomic integral argument from the completed Codex reduction lane. -/
theorem empirical_integrable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E) (f : E → ℝ) :
    Integrable f (empiricalDistribution ξhat) := by
  unfold empiricalDistribution
  apply Integrable.smul_measure
  · apply integrable_finsetSum_measure.mpr
    intro i hi
    exact integrable_dirac (by simp)
  · exact ENNReal.inv_ne_top.mpr (by exact_mod_cast hN.ne')
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassConsistencyCodex
open WassersteinDRO.Duality

theorem worstCaseRisk_upperEnvelope_bound {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure E) [IsProbabilityMeasure P] (Ξ : Set E) (hP : P Ξᶜ = 0)
    (h : E → ℝ) (L : ℝ) (hL : 0 ≤ L) (hg : ∀ ξ ∈ Ξ, h ξ ≤ L*(1+‖ξ‖))
    (hn : Integrable (fun ξ => ‖ξ‖) P) {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E)
    (ε : ℝ) (hε : 0 ≤ ε) (hd : wassersteinDistance 1 P (empiricalDistribution ξhat) ≤ ENNReal.ofReal ε)
    (k : ℕ) : worstCaseRisk ε 1 Ξ (empiricalDistribution ξhat) h ≤
      ((∫ ξ, upperEnvelope Ξ h (L+(k : ℝ)+1) ξ ∂P)+2*(L+(k : ℝ)+1)*ε : ℝ) := by
  have hs : ∀ᵐ ξ ∂P, ξ ∈ Ξ := mem_ae_iff.mpr hP
  have hne : Ξ.Nonempty := hs.exists
  have hΓ : L ≤ L+(k : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hf := upperEnvelope_lipschitz Ξ hne h L _ hL hΓ hg
  have hi := integrable_lipschitz_of_first_moment P _ _ hf hn
  have hnint := empirical_integrable hN ξhat (upperEnvelope Ξ h (L+(k : ℝ)+1))
  have hb := worstCaseRisk_le_true_lipschitz_expectation P (empiricalDistribution ξhat) Ξ ε hε hd
    h (upperEnvelope Ξ h (L+(k : ℝ)+1)) _ hf hi hnint
    (fun ξ hξ => le_upperEnvelope_on Ξ h L _ hL hΓ hg ξ hξ)
  rw [Real.coe_toNNReal _ (hL.trans hΓ)] at hb
  exact hb
end WassConsistencyCodex

end

section
set_option autoImplicit false
open Filter Topology
namespace WassConsistencyCodex

theorem tendsto_infimum_of_envelope_bounds {D : Type*} (X : Set D) (a : D → ℝ)
    (b : D → ℕ → ℝ) (C : ℕ → ℝ) (ε : ℕ → ℝ) (F : ℕ → EReal)
    (hlower : ∀ᶠ N in atTop, (⨅ x ∈ X, (a x : EReal)) ≤ F N)
    (hε : Tendsto ε atTop (𝓝 0))
    (hb : ∀ x ∈ X, Tendsto (b x) atTop (𝓝 (a x)))
    (hu : ∀ x ∈ X, ∀ k, ∀ᶠ N in atTop, F N ≤ (b x k+C k*ε N : ℝ)) :
    Tendsto F atTop (𝓝 (⨅ x ∈ X, (a x : EReal))) := by
  apply tendsto_order.mpr
  constructor
  · intro c hc
    exact hlower.mono (fun N hN => hc.trans_le hN)
  · intro c hc
    obtain ⟨x,hx⟩ := iInf_lt_iff.mp hc
    obtain ⟨hX,hax⟩ := iInf_lt_iff.mp hx
    have hbc : Tendsto (fun k => (b x k : EReal)) atTop (𝓝 (a x : EReal)) :=
      (continuous_coe_real_ereal.tendsto (a x)).comp (hb x hX)
    obtain ⟨k,hk⟩ := (hbc.eventually (Iio_mem_nhds hax)).exists
    have hlim : Tendsto (fun N => (b x k+C k*ε N : EReal)) atTop (𝓝 (b x k : EReal)) := by
      have hr : Tendsto (fun N => b x k+C k*ε N) atTop (𝓝 (b x k)) := by
        simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hε)
      exact (continuous_coe_real_ereal.tendsto (b x k)).comp hr
    filter_upwards [hu x hX k,hlim.eventually (Iio_mem_nhds hk)] with N hN hNc
    exact hN.trans_lt hNc
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassConsistencyCodex
open WassDDRO.Consistency WassersteinDRO.Duality

theorem nominalRisk_le_worstCase {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (P PN : Measure E) (Ξ : Set E) (ε : ℝ) (h : E → ℝ)
    (hball : P ∈ ambiguitySet ε 1 Ξ PN) (hint : Integrable h P) :
    ((∫ ξ, h ξ ∂P : ℝ) : EReal) ≤ worstCaseRisk ε 1 Ξ PN h := by
  unfold worstCaseRisk
  exact le_iSup_of_le P (le_iSup_of_le hball (le_iSup_of_le hint le_rfl))

theorem optimizer_guarantee {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    {D : Type*} {N : ℕ} (P : Measure E) (Ξ : Set E) (ε : ℝ)
    (X : Set D) (h : D → E → ℝ) (ξhat : Fin N → E) (xh : D)
    (hball : P ∈ ambiguitySet ε 1 Ξ (empiricalDistribution ξhat))
    (hint : Integrable (h xh) P) (hopt : ∀ x ∈ X,
      worstCaseRisk ε 1 Ξ (empiricalDistribution ξhat) (h xh) ≤
        worstCaseRisk ε 1 Ξ (empiricalDistribution ξhat) (h x)) :
    ((∫ ξ, h xh ξ ∂P : ℝ) : EReal) ≤ droValue X h ε Ξ ξhat := by
  apply (nominalRisk_le_worstCase P _ Ξ ε (h xh) hball hint).trans
  exact le_iInf₂ hopt

theorem true_distribution_mem_ball {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (P PN : Measure E) [IsProbabilityMeasure P]
    (Ξ : Set E) (ε : ℝ) (hP : P Ξᶜ = 0)
    (hd : wassersteinDistance 1 P PN ≤ ENNReal.ofReal ε) :
    P ∈ ambiguitySet ε 1 Ξ PN := by
  exact ⟨measure_univ,hP,hd⟩
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassConsistencyCodex
open WassDDRO.Consistency

theorem prefix_measurePreserving {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (N : ℕ) :
    MeasurePreserving (fun ω : ℕ → E => fun i : Fin N => ω i) (P_inf P)
      (Measure.pi fun _ : Fin N => P) := by
  let I := Finset.range N
  let e : I ≃ Fin N :=
    { toFun := fun i => ⟨i.val,Finset.mem_range.mp i.property⟩
      invFun := fun i => ⟨i.val,Finset.mem_range.mpr i.isLt⟩
      left_inv := fun i => by rfl
      right_inv := fun i => by rfl }
  have hr : MeasurePreserving I.restrict (P_inf P) (Measure.pi fun _ : I => P) :=
    ⟨Finset.measurable_restrict I,Measure.infinitePi_map_restrict (fun _ : ℕ => P)⟩
  have he := measurePreserving_piCongrLeft (fun _ : Fin N => P) e
  convert he.comp hr using 1
  funext ω i
  rfl

theorem infinite_samples_mem_support_ae {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (Ξ : Set E) (hP : P Ξᶜ = 0) :
    ∀ᵐ ω ∂P_inf P, ∀ i, ω i ∈ Ξ := by
  have hs : ∀ᵐ x ∂P, x ∈ Ξ := mem_ae_iff.mpr hP
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => P) i).quasiMeasurePreserving.ae hs
end WassConsistencyCodex

end

section
set_option autoImplicit false
namespace WassConsistencyCodex
open WassDDRO.Consistency

theorem rpow_nonneg_small_exponent (x y : ℝ) (hy : 0 ≤ y) (hy' : y ≤ 1/2) :
    0 ≤ x ^ y := by
  by_cases hx : 0 ≤ x
  · exact Real.rpow_nonneg hx y
  · rw [Real.rpow_def_of_neg (lt_of_not_ge hx)]
    apply mul_nonneg (Real.exp_pos _).le
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · nlinarith [Real.pi_pos,mul_nonneg hy Real.pi_pos.le]
    · nlinarith [Real.pi_pos,mul_nonneg (sub_nonneg.mpr hy') Real.pi_pos.le]

theorem radius_nonnegative (c₁ c₂ a : ℝ) (m N : ℕ) (b : ℝ)
    (hc₂ : 0 < c₂) (hN : 1 ≤ N) : 0 ≤ radius c₁ c₂ a m N b := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hm : (2 : ℝ) ≤ (max m 2 : ℝ) := by exact_mod_cast (le_max_right m 2)
  unfold radius
  split_ifs with hh
  · apply rpow_nonneg_small_exponent
    · positivity
    · apply (div_le_iff₀ (by linarith : 0 < (max m 2 : ℝ))).mpr
      linarith
  · apply Real.rpow_nonneg
    have hl : 0 < Real.log (c₁/b) := by
      have hg : (N : ℝ) < Real.log (c₁/b)/c₂ := lt_of_not_ge hh
      have := (lt_div_iff₀ hc₂).mp hg
      nlinarith
    positivity
end WassConsistencyCodex

end

section
set_option autoImplicit false
namespace WassConsistencyCodex
open WassDDRO.Consistency

theorem radius_positive_calibrated (c₁ c₂ a : ℝ) (m N : ℕ) (b : ℝ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (ha : 0 < a) (hN : 1 ≤ N)
    (hb : 0 < b) (hbc : b < c₁) :
    0 < radius c₁ c₂ a m N b ∧
    (if radius c₁ c₂ a m N b ≤ 1 then
      c₁ * Real.exp (-c₂*N*(radius c₁ c₂ a m N b) ^ (max m 2 : ℝ))
    else c₁ * Real.exp (-c₂*N*(radius c₁ c₂ a m N b) ^ a)) = b := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hm : 0 < (max m 2 : ℝ) := by
    have : (2 : ℝ) ≤ (max m 2 : ℝ) := by exact_mod_cast le_max_right m 2
    linarith
  have hcdiv : 0 < c₁/b := div_pos hc₁ hb
  have hlog : 0 < Real.log (c₁/b) := Real.log_pos ((lt_div_iff₀ hb).mpr (by simpa using hbc))
  let q := Real.log (c₁/b)/(c₂*N)
  have hq : 0 < q := div_pos hlog (mul_pos hc₂ hn)
  have hpow (t : ℝ) (ht : 0 < t) : (q ^ (1/t)) ^ t = q := by
    rw [← Real.rpow_mul hq.le,one_div_mul_cancel ht.ne',Real.rpow_one]
  have hcal : c₁*Real.exp (-c₂*N*q) = b := by
    have hid : -c₂*N*q = -Real.log (c₁/b) := by dsimp [q]; field_simp
    rw [hid,Real.exp_neg,Real.exp_log hcdiv]
    field_simp
  by_cases hbranch : Real.log (c₁/b)/c₂ ≤ (N : ℝ)
  · simp only [radius,if_pos hbranch]
    have hqle : q ≤ 1 := by
      apply (div_le_iff₀ (mul_pos hc₂ hn)).mpr
      have hl := (div_le_iff₀ hc₂).mp hbranch
      simpa [mul_comm] using hl
    have hrle : q ^ (1/(max m 2 : ℝ)) ≤ 1 := Real.rpow_le_one hq.le hqle (by positivity)
    refine ⟨Real.rpow_pos_of_pos hq _,?_⟩
    change (if q ^ (1/(max m 2 : ℝ)) ≤ 1 then _ else _) = b
    rw [if_pos hrle,hpow _ hm]
    exact hcal
  · simp only [radius,if_neg hbranch]
    have hql : 1 < q := by
      apply (lt_div_iff₀ (mul_pos hc₂ hn)).mpr
      have hl := (lt_div_iff₀ hc₂).mp (lt_of_not_ge hbranch)
      simpa [mul_comm] using hl
    have hrl : 1 < q ^ (1/a) := Real.one_lt_rpow hql (by positivity)
    refine ⟨Real.rpow_pos_of_pos hq _,?_⟩
    change (if q ^ (1/a) ≤ 1 then _ else _) = b
    rw [if_neg (not_le.mpr hrl),hpow _ ha]
    exact hcal
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassConsistencyCodex

theorem measure_positive_le_of_uniform_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (d : Ω → ENNReal) (C : ENNReal)
    (ht : ∀ ε : ℝ, 0 < ε → μ {ω | ENNReal.ofReal ε ≤ d ω} ≤ C) :
    μ {ω | 0 < d ω} ≤ C := by
  let s : ℕ → Set Ω := fun n => {ω | ENNReal.ofReal (1/(n+1 : ℝ)) ≤ d ω}
  have hs : Monotone s := by
    intro n m hnm ω hn
    change ENNReal.ofReal (1/(m+1 : ℝ)) ≤ d ω
    change ENNReal.ofReal (1/(n+1 : ℝ)) ≤ d ω at hn
    apply le_trans _ hn
    apply ENNReal.ofReal_le_ofReal
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast Nat.add_le_add_right hnm 1
  have heq : {ω | 0 < d ω} = ⋃ n, s n := by
    ext ω
    constructor
    · intro hω
      obtain ⟨r,hr,hrd⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hω
      have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
      obtain ⟨n,hn⟩ := exists_nat_one_div_lt hr'
      apply Set.mem_iUnion.mpr
      refine ⟨n,?_⟩
      change ENNReal.ofReal (1/(n+1 : ℝ)) ≤ d ω
      have hc : ENNReal.ofReal (r : ℝ) = (r : ENNReal) := ENNReal.ofReal_coe_nnreal
      exact (ENNReal.ofReal_le_ofReal hn.le).trans (hc ▸ hrd.le)
    · intro hω
      obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hω
      have hp : 0 < ENNReal.ofReal (1/(n+1 : ℝ)) := ENNReal.ofReal_pos.mpr (by positivity)
      exact hp.trans_le hn
  rw [heq,hs.measure_iUnion]
  exact iSup_le (fun n => ht _ (by positivity))
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassConsistencyCodex
open WassDDRO.Consistency WassersteinDRO.Duality

theorem concentration_tail_le_c1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (P : Measure E) [IsProbabilityMeasure P]
    (a c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (h7 : Concentration7 P a c₁ c₂)
    (N : ℕ) (hN : 1 ≤ N) (ε : ℝ) (hε : 0 < ε) :
    (Measure.pi fun _ : Fin N => P)
      {ω | ENNReal.ofReal ε ≤ wassersteinDistance 1 P (empiricalDistribution ω)} ≤
      ENNReal.ofReal c₁ := by
  apply (h7 N hN ε hε).trans
  apply ENNReal.ofReal_le_ofReal
  split_ifs
  all_goals
    apply mul_le_of_le_one_right hc₁
    apply Real.exp_le_one_iff.mpr
    have hr : 0 ≤ ε ^ (max (Module.finrank ℝ E) 2 : ℝ) := Real.rpow_nonneg hε.le _
    have hra : 0 ≤ ε ^ a := Real.rpow_nonneg hε.le _
    have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    nlinarith [mul_nonneg hc₂ hn,mul_nonneg (mul_nonneg hc₂ hn) hr,
      mul_nonneg (mul_nonneg hc₂ hn) hra]

theorem concentration_positive_tail_le_c1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (P : Measure E) [IsProbabilityMeasure P]
    (a c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (h7 : Concentration7 P a c₁ c₂)
    (N : ℕ) (hN : 1 ≤ N) :
    (Measure.pi fun _ : Fin N => P)
      {ω | 0 < wassersteinDistance 1 P (empiricalDistribution ω)} ≤ ENNReal.ofReal c₁ := by
  apply measure_positive_le_of_uniform_tail
  exact fun ε hε => concentration_tail_le_c1 P a c₁ c₂ hc₁ hc₂ h7 N hN ε hε
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassConsistencyCodex
open WassDDRO.Consistency WassersteinDRO.Duality

theorem concentration_radius_tail {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (P : Measure E) [IsProbabilityMeasure P]
    (a c₁ c₂ : ℝ) (ha : 0 < a) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (h7 : Concentration7 P a c₁ c₂) (N : ℕ) (hN : 1 ≤ N) (b : ℝ) (hb : 0 < b) :
    (Measure.pi fun _ : Fin N => P)
      {ω | ENNReal.ofReal (radius c₁ c₂ a (Module.finrank ℝ E) N b) <
        wassersteinDistance 1 P (empiricalDistribution ω)} ≤ ENNReal.ofReal b := by
  by_cases hbc : b < c₁
  · obtain ⟨hr,hcal⟩ := radius_positive_calibrated c₁ c₂ a (Module.finrank ℝ E) N b
      hc₁ hc₂ ha hN hb hbc
    have hs : {ω : Fin N → E | ENNReal.ofReal (radius c₁ c₂ a (Module.finrank ℝ E) N b) < wassersteinDistance 1 P (empiricalDistribution ω)} ⊆
        {ω | ENNReal.ofReal (radius c₁ c₂ a (Module.finrank ℝ E) N b) ≤ wassersteinDistance 1 P (empiricalDistribution ω)} := by
      intro ω hω
      change ENNReal.ofReal (radius c₁ c₂ a (Module.finrank ℝ E) N b) < wassersteinDistance 1 P (empiricalDistribution ω) at hω
      change ENNReal.ofReal (radius c₁ c₂ a (Module.finrank ℝ E) N b) ≤ wassersteinDistance 1 P (empiricalDistribution ω)
      exact le_of_lt hω
    apply (measure_mono hs).trans
    have ht := h7 N hN _ hr
    rw [hcal] at ht
    exact ht
  · have hs : {ω : Fin N → E | ENNReal.ofReal (radius c₁ c₂ a (Module.finrank ℝ E) N b) < wassersteinDistance 1 P (empiricalDistribution ω)} ⊆
        {ω | 0 < wassersteinDistance 1 P (empiricalDistribution ω)} := by
      intro ω hω
      change ENNReal.ofReal (radius c₁ c₂ a (Module.finrank ℝ E) N b) < wassersteinDistance 1 P (empiricalDistribution ω) at hω
      change 0 < wassersteinDistance 1 P (empiricalDistribution ω)
      exact lt_of_le_of_lt bot_le hω
    apply (measure_mono hs).trans
    exact (concentration_positive_tail_le_c1 P a c₁ c₂ hc₁.le hc₂.le h7 N hN).trans
      (ENNReal.ofReal_le_ofReal (le_of_not_gt hbc))
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal
namespace WassConsistencyCodex
open WassDDRO.Consistency WassersteinDRO.Duality

theorem true_distance_eventually_le_radius {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (P : Measure E) [IsProbabilityMeasure P]
    (a c₁ c₂ : ℝ) (ha : 0 < a) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (h7 : Concentration7 P a c₁ c₂) (β : ℕ → ℝ) (hβ : ∀ N, 0 < β N) (hsum : Summable β) :
    ∀ᵐ ω ∂P_inf P, ∀ᶠ N in atTop,
      wassersteinDistance 1 P (empiricalDistribution (fun i : Fin N => ω i)) ≤
        ENNReal.ofReal (radius c₁ c₂ a (Module.finrank ℝ E) N (β N)) := by
  let s : ℕ → Set (ℕ → E) := fun N => if 1 ≤ N then
    {ω | ENNReal.ofReal (radius c₁ c₂ a (Module.finrank ℝ E) N (β N)) <
      wassersteinDistance 1 P (empiricalDistribution (fun i : Fin N => ω i))} else ∅
  have hb (N : ℕ) : (P_inf P) (s N) ≤ ENNReal.ofReal (β N) := by
    by_cases hN : 1 ≤ N
    · simp only [s,if_pos hN]
      let t : Set (Fin N → E) := {ξhat | ENNReal.ofReal (radius c₁ c₂ a (Module.finrank ℝ E) N (β N)) <
        wassersteinDistance 1 P (empiricalDistribution ξhat)}
      change (P_inf P) ((fun ω : ℕ → E => fun i : Fin N => ω i) ⁻¹' t) ≤ _
      have hp := prefix_measurePreserving P N
      apply (Measure.le_map_apply hp.measurable.aemeasurable t).trans
      rw [hp.map_eq]
      exact concentration_radius_tail P a c₁ c₂ ha hc₁ hc₂ h7 N hN (β N) (hβ N)
    · simp only [s,if_neg hN,measure_empty]
      exact bot_le
  have hfin : (∑' N, (P_inf P) (s N)) ≠ ∞ :=
    (lt_of_le_of_lt (ENNReal.tsum_le_tsum hb) hsum.tsum_ofReal_lt_top).ne
  filter_upwards [ae_eventually_notMem hfin] with ω hω
  filter_upwards [hω,eventually_ge_atTop 1] with N hnot hN
  simpa only [s,if_pos hN,Set.mem_ofPred_eq,not_lt] using hnot

theorem true_distribution_eventually_mem_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (P : Measure E) [IsProbabilityMeasure P]
    (Ξ : Set E) (hP : P Ξᶜ = 0)
    (a c₁ c₂ : ℝ) (ha : 0 < a) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (h7 : Concentration7 P a c₁ c₂) (β : ℕ → ℝ) (hβ : ∀ N, 0 < β N) (hsum : Summable β) :
    ∀ᵐ ω ∂P_inf P, ∀ᶠ N in atTop,
      P ∈ ambiguitySet (radius c₁ c₂ a (Module.finrank ℝ E) N (β N)) 1 Ξ
        (empiricalDistribution (fun i : Fin N => ω i)) := by
  filter_upwards [true_distance_eventually_le_radius P a c₁ c₂ ha hc₁ hc₂ h7 β hβ hsum] with ω hω
  exact hω.mono (fun N hd => true_distribution_mem_ball P _ Ξ _ hP hd)

theorem empirical_distance_tendsto_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (P : Measure E) [IsProbabilityMeasure P]
    (a c₁ c₂ : ℝ) (ha : 0 < a) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (h7 : Concentration7 P a c₁ c₂) (β : ℕ → ℝ) (hβ : ∀ N, 0 < β N) (hsum : Summable β)
    (hlim : Tendsto (fun N => radius c₁ c₂ a (Module.finrank ℝ E) N (β N)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P_inf P,
      Tendsto (fun N => wassersteinDistance 1 P (empiricalDistribution (fun i : Fin N => ω i)))
        atTop (𝓝 0) := by
  filter_upwards [true_distance_eventually_le_radius P a c₁ c₂ ha hc₁ hc₂ h7 β hβ hsum] with ω hω
  have hr : Tendsto (fun N => ENNReal.ofReal (radius c₁ c₂ a (Module.finrank ℝ E) N (β N))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero,Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hr
    (Eventually.of_forall (fun _ => bot_le)) hω
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory Filter Topology
namespace WassConsistencyCodex
open WassDDRO.Consistency WassersteinDRO.Duality

theorem trueValue_le_droValue {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    {D : Type*} {N : ℕ} (P : Measure E) (X : Set D) (h : D → E → ℝ)
    (ε : ℝ) (Ξ : Set E) (ξhat : Fin N → E)
    (hint : ∀ x ∈ X, Integrable (h x) P)
    (hball : P ∈ ambiguitySet ε 1 Ξ (empiricalDistribution ξhat)) :
    trueValue X h P ≤ droValue X h ε Ξ ξhat := by
  unfold droValue
  apply le_iInf
  intro x
  apply le_iInf
  intro hx
  apply (iInf_le_of_le x (iInf_le_of_le hx le_rfl)).trans
  exact nominalRisk_le_worstCase P _ Ξ ε (h x) hball (hint x hx)

theorem trueValue_eventually_le_droValue {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (P : Measure E) [IsProbabilityMeasure P]
    (Ξ : Set E) (hP : P Ξᶜ = 0) (a c₁ c₂ : ℝ) (ha : 1 < a)
    (hA : Integrable (fun ξ => Real.exp (‖ξ‖ ^ a)) P)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (h7 : Concentration7 P a c₁ c₂)
    (β : ℕ → ℝ) (hβ : ∀ N, 0 < β N) (hsum : Summable β)
    {D : Type*} (X : Set D) (h : D → E → ℝ) (hmeas : ∀ x, Measurable (h x))
    (L : ℝ) (hg : ∀ x ∈ X, ∀ ξ ∈ Ξ, |h x ξ| ≤ L*(1+‖ξ‖)) :
    ∀ᵐ ω ∂P_inf P, ∀ᶠ N in atTop, trueValue X h P ≤
      droValue X h (radius c₁ c₂ a (Module.finrank ℝ E) N (β N)) Ξ (fun i : Fin N => ω i) := by
  have hn := integrable_norm_of_exp_moment P a ha.le hA
  have hint : ∀ x ∈ X, Integrable (h x) P := fun x hx =>
    integrable_of_linear_growth P Ξ hP (h x) (hmeas x) L (hg x hx) hn
  filter_upwards [true_distribution_eventually_mem_ball P Ξ hP a c₁ c₂
    (by linarith) hc₁ hc₂ h7 β hβ hsum] with ω hω
  exact hω.mono (fun N hball => trueValue_le_droValue P X h _ Ξ _ hint hball)
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory Filter Topology
namespace WassConsistencyCodex
open WassDDRO.Consistency WassersteinDRO.Duality

theorem droValue_consistency {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (Ξ : Set E) (hP : P Ξᶜ = 0)
    (a : ℝ) (ha : 1 < a) (hA : Integrable (fun ξ => Real.exp (‖ξ‖ ^ a)) P)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (h7 : Concentration7 P a c₁ c₂)
    (β : ℕ → ℝ) (hβ : ∀ N, 0 < β N) (hsum : Summable β)
    (hlim : Tendsto (fun N => radius c₁ c₂ a (Module.finrank ℝ E) N (β N)) atTop (𝓝 0))
    {D : Type*} (X : Set D) (h : D → E → ℝ) (hmeas : ∀ x, Measurable (h x))
    (husc : ∀ x ∈ X, UpperSemicontinuousOn (h x) Ξ)
    (L : ℝ) (hL : 0 ≤ L) (hg : ∀ x ∈ X, ∀ ξ ∈ Ξ, |h x ξ| ≤ L*(1+‖ξ‖)) :
    ∀ᵐ ω ∂P_inf P,
      (∀ᶠ N in atTop, trueValue X h P ≤ droValue X h
        (radius c₁ c₂ a (Module.finrank ℝ E) N (β N)) Ξ (fun i : Fin N => ω i)) ∧
      Tendsto (fun N => droValue X h (radius c₁ c₂ a (Module.finrank ℝ E) N (β N)) Ξ
        (fun i : Fin N => ω i)) atTop (𝓝 (trueValue X h P)) := by
  have hn := integrable_norm_of_exp_moment P a ha.le hA
  filter_upwards [trueValue_eventually_le_droValue P Ξ hP a c₁ c₂ ha hA hc₁ hc₂ h7 β hβ hsum X h hmeas L hg,
    true_distance_eventually_le_radius P a c₁ c₂ (by linarith) hc₁ hc₂ h7 β hβ hsum] with ω hlower hdist
  refine ⟨hlower,?_⟩
  apply tendsto_infimum_of_envelope_bounds X (fun x => ∫ ξ, h x ξ ∂P)
    (fun x k => ∫ ξ, upperEnvelope Ξ (h x) (L+(k : ℝ)+1) ξ ∂P)
    (fun k => 2*(L+(k : ℝ)+1))
    (fun N => radius c₁ c₂ a (Module.finrank ℝ E) N (β N)) _ hlower hlim
  · intro x hx
    exact upperEnvelope_integral_tendsto P Ξ hP (h x) (husc x hx) L hL (hg x hx) hn
  · intro x hx k
    filter_upwards [hdist,eventually_ge_atTop 1] with N hd hN
    have hupper := worstCaseRisk_upperEnvelope_bound P Ξ hP (h x) L hL
      (fun ξ hξ => (le_abs_self _).trans (hg x hx ξ hξ)) hn (by omega)
      (fun i : Fin N => ω i) (radius c₁ c₂ a (Module.finrank ℝ E) N (β N))
      (radius_nonnegative c₁ c₂ a _ N (β N) hc₂ hN) hd k
    exact (iInf_le_of_le x (iInf_le_of_le hx le_rfl)).trans hupper
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal
namespace WassConsistencyCodex

theorem ofReal_shift_le_liminf (f : ℕ → ℝ) (a B : ℝ)
    (hl : ∀ r < a, ∀ᶠ n in atTop, r < f n) :
    ENNReal.ofReal (a+B) ≤ liminf (fun n => ENNReal.ofReal (f n+B)) atTop := by
  apply (le_liminf_iff' (f := atTop) (u := fun n => ENNReal.ofReal (f n+B))).mpr
  intro y hy
  have hyfin : y ≠ ∞ := ne_top_of_lt (hy.trans (ENNReal.ofReal_lt_top))
  have hyr : y.toReal < a+B := ENNReal.toReal_lt_of_lt_ofReal hy
  have hr : y.toReal-B < a := by linarith
  filter_upwards [hl (y.toReal-B) hr] with n hn
  rw [← ENNReal.ofReal_toReal hyfin]
  apply ENNReal.ofReal_le_ofReal
  linarith

theorem integral_le_of_shifted_fatou {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : ℕ → Ω → ℝ) (f B : Ω → ℝ)
    (hFm : ∀ n, Measurable (F n)) (hBm : Measurable B)
    (hFi : ∀ n, Integrable (F n) P) (hfi : Integrable f P) (hBi : Integrable B P)
    (hFnonneg : ∀ n, ∀ᵐ ξ ∂P, 0 ≤ F n ξ+B ξ)
    (hfnonneg : ∀ᵐ ξ ∂P, 0 ≤ f ξ+B ξ)
    (hl : ∀ᵐ ξ ∂P, ∀ r < f ξ, ∀ᶠ n in atTop, r < F n ξ)
    (c : ℝ) (hu : ∀ᶠ n in atTop, (∫ ξ, F n ξ ∂P) ≤ c) :
    (∫ ξ, f ξ ∂P) ≤ c := by
  have hp : (∫⁻ ξ, ENNReal.ofReal (f ξ+B ξ) ∂P) ≤
      liminf (fun n => ∫⁻ ξ, ENNReal.ofReal (F n ξ+B ξ) ∂P) atTop := by
    apply (lintegral_mono_ae (hl.mono (fun ξ hξ => ofReal_shift_le_liminf (fun n => F n ξ) _ _ hξ))).trans
    exact lintegral_liminf_le (fun n => ((hFm n).add hBm).ennreal_ofReal)
  have hupper : ∀ᶠ n in atTop,
      (∫⁻ ξ, ENNReal.ofReal (F n ξ+B ξ) ∂P) ≤ ENNReal.ofReal (c+∫ ξ, B ξ ∂P) := by
    filter_upwards [hu] with n hn
    have hFn : Integrable (fun ξ => F n ξ+B ξ) P := (hFi n).add hBi
    rw [← ofReal_integral_eq_lintegral_ofReal hFn (hFnonneg n),
      integral_add (hFi n) hBi]
    apply ENNReal.ofReal_le_ofReal
    linarith
  have hb := hp.trans (liminf_le_of_frequently_le' hupper.frequently)
  have hfb : Integrable (fun ξ => f ξ+B ξ) P := hfi.add hBi
  rw [← ofReal_integral_eq_lintegral_ofReal hfb hfnonneg,
    integral_add hfi hBi] at hb
  have hf0 : 0 ≤ (∫ ξ, f ξ ∂P)+(∫ ξ, B ξ ∂P) := by
    rw [← integral_add hfi hBi]
    exact integral_nonneg_of_ae hfnonneg
  have hc0 : 0 ≤ c+(∫ ξ, B ξ ∂P) := by
    obtain ⟨n,hn⟩ := hu.exists
    have hpos : 0 ≤ ∫ ξ, F n ξ+B ξ ∂P := integral_nonneg_of_ae (hFnonneg n)
    rw [integral_add (hFi n) hBi] at hpos
    linarith
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal hf0,ENNReal.toReal_ofReal hc0] at hreal
  linarith

end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory Filter Topology
namespace WassConsistencyCodex

theorem integral_le_of_lsc_sequence {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (P : Measure E) [IsFiniteMeasure P]
    (Ξ : Set E) (hP : P Ξᶜ = 0) {D : Type*} [TopologicalSpace D]
    (X : Set D) (h : D → E → ℝ) (hmeas : ∀ x, Measurable (h x))
    (L : ℝ) (hg : ∀ x ∈ X, ∀ ξ ∈ Ξ, |h x ξ| ≤ L*(1+‖ξ‖))
    (hn : Integrable (fun ξ => ‖ξ‖) P)
    (hlsc : ∀ ξ ∈ Ξ, LowerSemicontinuousOn (fun x => h x ξ) X)
    (u : ℕ → D) (huX : ∀ n, u n ∈ X) (xstar : D) (hx : xstar ∈ X)
    (hu : Tendsto u atTop (𝓝 xstar)) (c : ℝ)
    (hupper : ∀ᶠ n in atTop, (∫ ξ, h (u n) ξ ∂P) ≤ c) :
    (∫ ξ, h xstar ξ ∂P) ≤ c := by
  let B : E → ℝ := fun ξ => L*(1+‖ξ‖)
  have hB : Integrable B P := ((integrable_const (1 : ℝ)).add hn).const_mul L
  have hBm : Measurable B := (measurable_const.add measurable_norm).const_mul L
  have hi : ∀ x ∈ X, Integrable (h x) P := fun x hxx =>
    integrable_of_linear_growth P Ξ hP (h x) (hmeas x) L (hg x hxx) hn
  have hs : ∀ᵐ ξ ∂P, ξ ∈ Ξ := mem_ae_iff.mpr hP
  have huw : Tendsto u atTop (𝓝[X] xstar) :=
    tendsto_nhdsWithin_iff.mpr ⟨hu,Eventually.of_forall huX⟩
  apply integral_le_of_shifted_fatou P (fun n ξ => h (u n) ξ) (h xstar) B
    (fun n => hmeas (u n)) hBm (fun n => hi (u n) (huX n)) (hi xstar hx) hB
  · intro n
    filter_upwards [hs] with ξ hξ
    have hl := (abs_le.mp (hg (u n) (huX n) ξ hξ)).1
    change 0 ≤ h (u n) ξ+L*(1+‖ξ‖)
    linarith
  · filter_upwards [hs] with ξ hξ
    have hl := (abs_le.mp (hg xstar hx ξ hξ)).1
    change 0 ≤ h xstar ξ+L*(1+‖ξ‖)
    linarith
  · filter_upwards [hs] with ξ hξ
    intro r hr
    exact huw.eventually (hlsc ξ hξ xstar hx r hr)
  · exact hupper
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory Filter Topology
namespace WassConsistencyCodex

theorem cluster_optimality_of_objective_bounds {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (P : Measure E) [IsFiniteMeasure P]
    (Ξ : Set E) (hP : P Ξᶜ = 0) {D : Type*} [TopologicalSpace D] [FirstCountableTopology D]
    (X : Set D) (hX : IsClosed X) (h : D → E → ℝ) (hmeas : ∀ x, Measurable (h x))
    (L : ℝ) (hg : ∀ x ∈ X, ∀ ξ ∈ Ξ, |h x ξ| ≤ L*(1+‖ξ‖))
    (hn : Integrable (fun ξ => ‖ξ‖) P)
    (hlsc : ∀ ξ ∈ Ξ, LowerSemicontinuousOn (fun x => h x ξ) X)
    (u : ℕ → D) (huX : ∀ᶠ N in atTop, u N ∈ X) (F : ℕ → EReal) (J : EReal)
    (hF : Tendsto F atTop (𝓝 J))
    (huF : ∀ᶠ N in atTop, ((∫ ξ, h (u N) ξ ∂P : ℝ) : EReal) ≤ F N)
    (hJ : ∀ x ∈ X, J ≤ ((∫ ξ, h x ξ ∂P : ℝ) : EReal)) :
    ∀ xstar : D, MapClusterPt xstar atTop u →
      xstar ∈ X ∧ ∀ x ∈ X, (∫ ξ, h xstar ξ ∂P) ≤ ∫ ξ, h x ξ ∂P := by
  classical
  intro xstar hcluster
  obtain ⟨ψ,hseq,hψ⟩ := hcluster.exists_seq_tendsto
  have hu' : Tendsto (fun n => u (ψ n)) atTop (𝓝 xstar) := by simpa only [Function.comp_def] using hseq
  have hux : ∀ᶠ n in atTop, u (ψ n) ∈ X := hψ.eventually huX
  have hx : xstar ∈ X := hX.mem_of_tendsto hu' hux
  refine ⟨hx,?_⟩
  let w : ℕ → D := fun n => if u (ψ n) ∈ X then u (ψ n) else xstar
  have hwX (n : ℕ) : w n ∈ X := by
    dsimp [w]
    split_ifs with hmem
    · exact hmem
    · exact hx
  have hweq : w =ᶠ[atTop] (fun n => u (ψ n)) := hux.mono (fun n hn => if_pos hn)
  have hw : Tendsto w atTop (𝓝 xstar) := hu'.congr' hweq.symm
  intro x hxx
  apply le_of_forall_gt_imp_ge_of_dense
  intro d hd
  have hJd : J < (d : EReal) := (hJ x hxx).trans_lt (EReal.coe_lt_coe_iff.mpr hd)
  have hFd : ∀ᶠ n in atTop, F (ψ n) < (d : EReal) := hψ.eventually (hF.eventually (Iio_mem_nhds hJd))
  have hnom : ∀ᶠ n in atTop, (∫ ξ, h (w n) ξ ∂P) ≤ d := by
    filter_upwards [hψ.eventually huF,hFd,hweq] with n hNF hNd heq
    have hh : ((∫ ξ, h (w n) ξ ∂P : ℝ) : EReal) < (d : EReal) := by
      rw [heq]
      exact hNF.trans_lt hNd
    exact (EReal.coe_lt_coe_iff.mp hh).le
  exact integral_le_of_lsc_sequence P Ξ hP X h hmeas L hg hn hlsc w hwX xstar hx hw d hnom
end WassConsistencyCodex

end

set_option autoImplicit false
open MeasureTheory Filter Topology WassDDRO.Consistency
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (Ξ : Set E) (hP : P Ξᶜ = 0)
    (a : ℝ) (ha : 1 < a) (hA : Integrable (fun ξ => Real.exp (‖ξ‖ ^ a)) P)
    (hm : Module.finrank ℝ E ≠ 2)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (h7 : Concentration7 P a c₁ c₂)
    (β : ℕ → ℝ) (hβ : ∀ N, 0 < β N ∧ β N < 1) (hsum : Summable β)
    (hlim : Tendsto (fun N => radius c₁ c₂ a (Module.finrank ℝ E) N (β N)) atTop (𝓝 0))
    {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → E → ℝ)
    (hmeas : ∀ x, Measurable (h x))
    (xhat : (N : ℕ) → (Fin N → E) → EuclideanSpace ℝ (Fin n))
    (hopt : ∀ (N : ℕ) (ξhat : Fin N → E), 1 ≤ N → (∀ i, ξhat i ∈ Ξ) →
      xhat N ξhat ∈ X ∧ ∀ x ∈ X,
        WassersteinDRO.Duality.worstCaseRisk (radius c₁ c₂ a (Module.finrank ℝ E) N (β N)) 1 Ξ
            (WassersteinDRO.Duality.empiricalDistribution ξhat) (h (xhat N ξhat)) ≤
          WassersteinDRO.Duality.worstCaseRisk (radius c₁ c₂ a (Module.finrank ℝ E) N (β N)) 1 Ξ
            (WassersteinDRO.Duality.empiricalDistribution ξhat) (h x)) :
    ((∀ x ∈ X, UpperSemicontinuousOn (h x) Ξ) → ∀ L : ℝ, 0 ≤ L →
        (∀ x ∈ X, ∀ ξ ∈ Ξ, |h x ξ| ≤ L * (1 + ‖ξ‖)) →
        ∀ᵐ ω ∂(P_inf P),
          (∀ᶠ N in atTop, trueValue X h P ≤
            droValue X h (radius c₁ c₂ a (Module.finrank ℝ E) N (β N)) Ξ (fun i : Fin N => ω i)) ∧
          Tendsto (fun N => droValue X h (radius c₁ c₂ a (Module.finrank ℝ E) N (β N)) Ξ
            (fun i : Fin N => ω i)) atTop (𝓝 (trueValue X h P))) ∧
    ((∀ x ∈ X, UpperSemicontinuousOn (h x) Ξ) → ∀ L : ℝ, 0 ≤ L →
        (∀ x ∈ X, ∀ ξ ∈ Ξ, |h x ξ| ≤ L * (1 + ‖ξ‖)) →
        IsClosed X → (∀ ξ ∈ Ξ, LowerSemicontinuousOn (fun x => h x ξ) X) →
        ∀ᵐ ω ∂(P_inf P), ∀ xstar : EuclideanSpace ℝ (Fin n),
          MapClusterPt xstar atTop (fun N => xhat N (fun i : Fin N => ω i)) →
          xstar ∈ X ∧ ∀ x ∈ X, ∫ ξ, h xstar ξ ∂P ≤ ∫ ξ, h x ξ ∂P) := by
  constructor
  · intro husc L hL hg
    exact WassConsistencyCodex.droValue_consistency P Ξ hP a ha hA c₁ c₂ hc₁ hc₂ h7 β
      (fun N => (hβ N).1) hsum hlim X h hmeas husc L hL hg
  · intro husc L hL hg hX hlsc
    have hn := WassConsistencyCodex.integrable_norm_of_exp_moment P a ha.le hA
    have hint : ∀ x ∈ X, Integrable (h x) P := fun x hx =>
      WassConsistencyCodex.integrable_of_linear_growth P Ξ hP (h x) (hmeas x) L (hg x hx) hn
    filter_upwards [WassConsistencyCodex.droValue_consistency P Ξ hP a ha hA c₁ c₂ hc₁ hc₂ h7 β
        (fun N => (hβ N).1) hsum hlim X h hmeas husc L hL hg,
      WassConsistencyCodex.infinite_samples_mem_support_ae P Ξ hP,
      WassConsistencyCodex.true_distribution_eventually_mem_ball P Ξ hP a c₁ c₂
        (by linarith) hc₁ hc₂ h7 β (fun N => (hβ N).1) hsum] with ω hvalue hω hball
    let u : ℕ → EuclideanSpace ℝ (Fin n) := fun N => xhat N (fun i : Fin N => ω i)
    let F : ℕ → EReal := fun N => droValue X h
      (radius c₁ c₂ a (Module.finrank ℝ E) N (β N)) Ξ (fun i : Fin N => ω i)
    have huX : ∀ᶠ N in atTop, u N ∈ X := (eventually_ge_atTop 1).mono
      (fun N hN => (hopt N (fun i : Fin N => ω i) hN (fun i => hω i)).1)
    have hnom : ∀ᶠ N in atTop, ((∫ ξ, h (u N) ξ ∂P : ℝ) : EReal) ≤ F N := by
      filter_upwards [hball,eventually_ge_atTop 1] with N hb hN
      have ho := hopt N (fun i : Fin N => ω i) hN (fun i => hω i)
      exact WassConsistencyCodex.optimizer_guarantee P Ξ _ X h (fun i : Fin N => ω i) (u N)
        hb (hint _ ho.1) ho.2
    exact WassConsistencyCodex.cluster_optimality_of_objective_bounds P Ξ hP X hX h hmeas L hg hn
      hlsc u huX F (trueValue X h P) hvalue.2 hnom
      (fun x hx => iInf_le_of_le x (iInf_le_of_le hx le_rfl))


#print axioms solution
