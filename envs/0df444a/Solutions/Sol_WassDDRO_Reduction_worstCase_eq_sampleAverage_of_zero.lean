-- Prove2me | solution 1 for WassDDRO.Reduction.worstCase_eq_sampleAverage_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T09:07:13.564085+00:00
-- url     : https://prove2.me/submissions/d3542c4b-5921-46a0-9423-6ac310fb9044

import Definitions.Def_WassDDRO_Reduction_Setting
import Mathlib
set_option autoImplicit false
section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open DupacovaWets.Consistency

lemma expect_mono {Z : Type*} [MeasurableSpace Z] (Q : Measure Z)
    (f g : Z → EReal) (hfg : f ≤ᵐ[Q] g) :
    expect Q f ≤ expect Q g := by
  have hpos : (∫⁻ z, (f z).toENNReal ∂Q) ≤ ∫⁻ z, (g z).toENNReal ∂Q :=
    lintegral_mono_ae (hfg.mono fun z hz => EReal.toENNReal_le_toENNReal hz)
  have hneg : (∫⁻ z, (-g z).toENNReal ∂Q) ≤ ∫⁻ z, (-f z).toENNReal ∂Q :=
    lintegral_mono_ae (hfg.mono fun z hz => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr hz))
  unfold expect
  by_cases hgtop : (∫⁻ z, (g z).toENNReal ∂Q) = ⊤
  · rw [if_pos hgtop]
    exact le_top
  · have hftop : (∫⁻ z, (f z).toENNReal ∂Q) ≠ ⊤ :=
      (lt_of_le_of_lt hpos (lt_top_iff_ne_top.mpr hgtop)).ne
    rw [if_neg hgtop, if_neg hftop]
    exact EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hpos)
      (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hneg)

end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open DupacovaWets.Consistency
lemma expect_eq_integral {E : Type*} [MeasurableSpace E]
    (Q : Measure E) (l : E → ℝ) (hl : Integrable l Q) :
    expect Q (fun x => (l x : EReal)) = (∫ x, l x ∂Q : ℝ) := by
  have hp : (∫⁻ x, ENNReal.ofReal (l x) ∂Q) ≠ ⊤ :=
    ((lintegral_ofReal_le_lintegral_enorm l).trans_lt hl.2).ne
  have hn : (∫⁻ x, ENNReal.ofReal (-l x) ∂Q) ≠ ⊤ :=
    ((lintegral_ofReal_le_lintegral_enorm (fun x => -l x)).trans_lt hl.neg.2).ne
  unfold expect
  rw [if_neg (show (∫⁻ x, ((l x : EReal)).toENNReal ∂Q) ≠ ⊤ from hp)]
  simp only [EReal.real_coe_toENNReal, ← EReal.coe_neg]
  rw [ ← EReal.coe_ennreal_toReal hp, ← EReal.coe_ennreal_toReal hn,
    ← EReal.coe_sub, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hl]


end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open DupacovaWets.Consistency
 theorem expect_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (Q : Measure α) (g : α → β) (f : β → EReal) (hg : Measurable g) (hf : Measurable f) :
    expect (Q.map g) f=expect Q (fun x => f (g x)) := by
  have hp : (∫⁻ y, (f y).toENNReal ∂Q.map g) = ∫⁻ x, (f (g x)).toENNReal ∂Q :=
    lintegral_map (by fun_prop) hg
  have hn : (∫⁻ y, (-f y).toENNReal ∂Q.map g) = ∫⁻ x, (-f (g x)).toENNReal ∂Q :=
    lintegral_map (by fun_prop) hg
  unfold expect
  rw [hp,hn]
 theorem expect_le_integrable_upper {α : Type*} [MeasurableSpace α]
    (Q : Measure α) (f : α → EReal) (g : α → ℝ) (hg : Integrable g Q)
    (hfg : f ≤ᵐ[Q] fun x => (g x : EReal)) :
    expect Q f ≤ ((∫ x, g x ∂Q : ℝ) : EReal) := by
  rw [← expect_eq_integral Q g hg]
  exact expect_mono Q f _ hfg
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open DupacovaWets.Consistency
 theorem coupling_upper {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    (Q P : Measure E) (π : Measure (E×E)) (L : E → EReal) (ψ : E → ℝ) (lam : ℝ)
    (hL : Measurable L) (hψ : Integrable ψ P)
    (hm : π.map Prod.fst=Q ∧ π.map Prod.snd=P)
    (hcost : (∫⁻ w, ENNReal.ofReal ‖w.1-w.2‖ ∂π) ≠ ⊤)
    (hbound : ∀ᵐ w ∂π, L w.1 ≤ ((lam*‖w.1-w.2‖+ψ w.2 : ℝ) : EReal)) :
    expect Q L ≤ ((lam*(∫⁻ w, ENNReal.ofReal ‖w.1-w.2‖ ∂π).toReal+
      ∫ y, ψ y ∂P : ℝ) : EReal) := by
  have hc : Measurable (fun w : E×E => ‖w.1-w.2‖) := (measurable_fst.sub measurable_snd).norm
  have hi : Integrable (fun w : E×E => ‖w.1-w.2‖) π :=
    (lintegral_ofReal_ne_top_iff_integrable hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => norm_nonneg (w.1-w.2))).mp hcost
  have hp : Integrable ψ (π.map Prod.snd) := by rw [hm.2];exact hψ
  have hs : Integrable (fun w : E×E => ψ w.2) π := hp.comp_measurable measurable_snd
  have hb : Integrable (fun w : E×E => lam*‖w.1-w.2‖+ψ w.2) π := (hi.const_mul lam).add hs
  have he : expect Q L=expect π (fun w => L w.1) := by
    rw [←hm.1]
    exact expect_map π Prod.fst L measurable_fst hL
  rw [he]
  have hup := expect_le_integrable_upper π (fun w => L w.1) _ hb hbound
  have hsnd : (∫ w : E×E, ψ w.2 ∂π) = ∫ y, ψ y ∂P := by
    rw [←hm.2]
    symm
    exact integral_map measurable_snd.aemeasurable hp.aestronglyMeasurable
  have hreal : (∫ w : E×E, lam*‖w.1-w.2‖+ψ w.2 ∂π) =
      lam*(∫⁻ w, ENNReal.ofReal ‖w.1-w.2‖ ∂π).toReal+∫ y, ψ y ∂P := by
    rw [integral_add (hi.const_mul lam) hs, integral_const_mul, hsnd,
      integral_eq_lintegral_of_nonneg_ae (f:=fun w : E×E => ‖w.1-w.2‖)
        (Filter.Eventually.of_forall fun w => norm_nonneg (w.1-w.2)) hc.aestronglyMeasurable]
  rwa [hreal] at hup
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open WassersteinDRO.Duality
 theorem wasserstein_one_eq {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (Q P : Measure E) : wassersteinDistance 1 Q P =
      ⨅ (π : Measure (E×E)) (_ : π.map Prod.fst=Q ∧ π.map Prod.snd=P),
        ∫⁻ w, ENNReal.ofReal ‖w.1-w.2‖ ∂π := by simp [wassersteinDistance]
 theorem exists_coupling_lt_budget_add {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (Q P : Measure E) (ε η : ℝ) (hε : 0≤ε) (hη : 0<η)
    (hbudget : wassersteinDistance 1 Q P≤ENNReal.ofReal ε) :
    ∃ π : Measure (E×E), (π.map Prod.fst=Q ∧ π.map Prod.snd=P) ∧
      (∫⁻ w, ENNReal.ofReal ‖w.1-w.2‖ ∂π)<ENNReal.ofReal (ε+η) := by
  have hlt : wassersteinDistance 1 Q P<ENNReal.ofReal (ε+η) :=
    lt_of_le_of_lt hbudget ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hε).mpr (by linarith))
  rw [wasserstein_one_eq,iInf_lt_iff] at hlt
  obtain ⟨π,hπ⟩ := hlt
  rw [iInf_lt_iff] at hπ
  obtain ⟨hm,hc⟩ := hπ
  exact ⟨π,hm,hc⟩
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory Filter Topology
namespace WassReductionCodex
open WassersteinDRO.Duality DupacovaWets.Consistency

lemma zero_budget_integral_le_of_lipschitz {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Q P : Measure E) (l : E → ℝ) (K : NNReal) (hl : LipschitzWith K l)
    (hQ : Integrable l Q) (hP : Integrable l P)
    (hzero : wassersteinDistance 1 Q P ≤ 0) :
    (∫ x, l x ∂Q) ≤ ∫ x, l x ∂P := by
  have hb : wassersteinDistance 1 Q P ≤ ENNReal.ofReal 0 := by simpa using hzero
  have hup (η : ℝ) (hη : 0 < η) :
      (∫ x, l x ∂Q) ≤ (K : ℝ)*η+∫ x, l x ∂P := by
    obtain ⟨π,hm,hc⟩ := exists_coupling_lt_budget_add Q P 0 η le_rfl hη hb
    have hcfin : (∫⁻ w, ENNReal.ofReal ‖w.1-w.2‖ ∂π) ≠ ⊤ :=
      (lt_of_lt_of_le hc le_top).ne
    have hbound : ∀ᵐ w : E×E ∂π,
        (l w.1 : EReal) ≤ (((K : ℝ)*‖w.1-w.2‖+l w.2 : ℝ) : EReal) := by
      apply Eventually.of_forall
      intro w
      apply EReal.coe_le_coe_iff.mpr
      have hh : |l w.1-l w.2| ≤ (K : ℝ)*‖w.1-w.2‖ := by
        simpa [dist_eq_norm,Real.norm_eq_abs] using hl.dist_le_mul w.1 w.2
      have := le_trans (le_abs_self _) hh
      linarith
    have hu := coupling_upper Q P π (fun x => (l x : EReal)) l K
      (continuous_coe_real_ereal.measurable.comp hl.continuous.measurable) hP hm hcfin hbound
    rw [expect_eq_integral Q l hQ] at hu
    have hr := mul_le_mul_of_nonneg_left (ENNReal.toReal_lt_of_lt_ofReal hc).le K.coe_nonneg
    apply EReal.coe_le_coe_iff.mp
    exact le_trans hu (EReal.coe_le_coe_iff.mpr (by simpa using add_le_add_right hr (∫ x, l x ∂P)))
  have ht : Tendsto (fun n : ℕ => (K : ℝ)*((1 : ℝ)/(n+1))+∫ x, l x ∂P)
      atTop (𝓝 (∫ x, l x ∂P)) := by
    simpa using (tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat).add
      (tendsto_const_nhds (x:=(∫ x, l x ∂P)))
  exact isClosed_Ici.mem_of_tendsto ht
    (Eventually.of_forall fun n => hup ((1 : ℝ)/(n+1)) (by positivity))

lemma zero_budget_integral_eq_of_lipschitz {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Q P : Measure E) (l : E → ℝ) (K : NNReal) (hl : LipschitzWith K l)
    (hQ : Integrable l Q) (hP : Integrable l P)
    (hzero : wassersteinDistance 1 Q P ≤ 0) :
    (∫ x, l x ∂Q) = ∫ x, l x ∂P := by
  have hu := zero_budget_integral_le_of_lipschitz Q P l K hl hQ hP hzero
  have hn := zero_budget_integral_le_of_lipschitz Q P (fun x => -l x) K hl.neg hQ.neg hP.neg hzero
  simp only [integral_neg] at hn
  exact le_antisymm hu (by linarith)

lemma zero_budget_measure_eq {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Q P : Measure E) [IsFiniteMeasure Q] [IsFiniteMeasure P]
    (hzero : wassersteinDistance 1 Q P ≤ 0) : Q = P := by
  have hclosed : ∀ F : Set E, IsClosed F → Q F = P F := by
    intro F hF
    have heq : ∀ n : ℕ,
        (∫⁻ x, (thickenedIndicator (δ := 1 / (n + 1)) Nat.one_div_pos_of_nat F x : ENNReal) ∂Q) =
        ∫⁻ x, (thickenedIndicator (δ := 1 / (n + 1)) Nat.one_div_pos_of_nat F x : ENNReal) ∂P := by
      intro n
      let δ := (1 : ℝ) / (n + 1)
      have hδ : 0 < δ := Nat.one_div_pos_of_nat
      let f := thickenedIndicator hδ F
      have hl : LipschitzWith δ.toNNReal⁻¹ (fun x => (f x : ℝ)) := by
        have h := NNReal.isometry_coe.lipschitz.comp (lipschitzWith_thickenedIndicator hδ F)
        change LipschitzWith δ.toNNReal⁻¹ (NNReal.toReal ∘ ⇑f)
        simpa only [one_mul] using h
      have hiP : Integrable (fun x => (f x : ℝ)) P := integrable_thickenedIndicator F hδ
      have hiQ : Integrable (fun x => (f x : ℝ)) Q := integrable_thickenedIndicator F hδ
      have he := zero_budget_integral_eq_of_lipschitz Q P (fun x => (f x : ℝ)) _ hl hiQ hiP hzero
      rw [lintegral_coe_eq_integral _ hiQ, lintegral_coe_eq_integral _ hiP]
      exact congrArg ENNReal.ofReal he
    have hQ := tendsto_lintegral_thickenedIndicator_of_isClosed Q hF
      (fun _ => Nat.one_div_pos_of_nat) tendsto_one_div_add_atTop_nhds_zero_nat
    have hP := tendsto_lintegral_thickenedIndicator_of_isClosed P hF
      (fun _ => Nat.one_div_pos_of_nat) tendsto_one_div_add_atTop_nhds_zero_nat
    simp_rw [heq] at hQ
    exact tendsto_nhds_unique hQ hP
  apply ext_of_generate_finite {F : Set E | IsClosed F} ?_ isPiSystem_isClosed
  · exact hclosed
  · exact hclosed Set.univ isClosed_univ
  · rw [BorelSpace.measurable_eq (α := E), borel_eq_generateFrom_isClosed]


end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open MeasureTheory WassersteinDRO.Duality
lemma empirical_probability {Z : Type*} [MeasurableSpace Z] {n : ℕ}
    (hn : 0 < n) (X : Fin n → Z) : IsProbabilityMeasure (empiricalDistribution X) := by
  constructor
  simp [empiricalDistribution, Measure.smul_apply, Measure.finsetSum_apply]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n)

lemma empirical_map {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W] {n : ℕ}
    (X : Fin n → Z) (f : Z → W) (hf : Measurable f) :
    (empiricalDistribution X).map f = empiricalDistribution (fun i => f (X i)) := by
  unfold empiricalDistribution
  rw [Measure.map_smul, Measure.map_finset_sum' hf.aemeasurable]
  simp only [Measure.map_dirac' hf]

lemma empirical_lintegral {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {n : ℕ} (X : Fin n → Z) (f : Z → ENNReal) :
    (∫⁻ z, f z ∂empiricalDistribution X) = (n : ENNReal)⁻¹ * ∑ i, f (X i) := by
  unfold empiricalDistribution
  rw [lintegral_smul_measure, lintegral_finsetSum_measure]
  simp only [lintegral_dirac]
  rfl

lemma empirical_coupling {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Z) (Y : Fin n → W) :
    IsProbabilityMeasure (empiricalDistribution (fun i => (X i, Y i))) ∧
    (empiricalDistribution (fun i => (X i, Y i))).map Prod.fst = empiricalDistribution X ∧
    (empiricalDistribution (fun i => (X i, Y i))).map Prod.snd = empiricalDistribution Y := by
  refine ⟨empirical_probability hn _, ?_, ?_⟩
  · exact empirical_map _ Prod.fst measurable_fst
  · exact empirical_map _ Prod.snd measurable_snd

lemma empirical_integrable {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Z) (l : Z → ℝ) :
    Integrable l (empiricalDistribution X) := by
  unfold empiricalDistribution
  apply Integrable.smul_measure
  · apply integrable_finsetSum_measure.mpr
    intro i hi
    exact integrable_dirac (by simp)
  · exact ENNReal.inv_ne_top.mpr (by exact_mod_cast hn.ne')

lemma empirical_integral {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {n : ℕ} (X : Fin n → Z) (l : Z → ℝ) :
    (∫ z, l z ∂empiricalDistribution X) = (n : ℝ)⁻¹ * ∑ i, l (X i) := by
  unfold empiricalDistribution
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  · intro i hi
    exact integrable_dirac (by simp)


end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open WassDDRO.Reduction WassersteinDRO.Duality DupacovaWets.Consistency

theorem empirical_self_distance_zero {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [MeasurableSingletonClass E] {N : ℕ} (hN : 0 < N)
    (ξhat : Fin N → E) : wassersteinDistance 1 (empiricalDistribution ξhat)
      (empiricalDistribution ξhat) = 0 := by
  obtain ⟨_,hfst,hsnd⟩ := empirical_coupling hN ξhat ξhat
  apply le_antisymm _ bot_le
  rw [wasserstein_one_eq]
  apply le_trans (iInf_le _ (empiricalDistribution (fun i => (ξhat i,ξhat i))))
  apply le_trans (iInf_le _ ⟨hfst,hsnd⟩)
  rw [empirical_lintegral]
  simp

theorem zero_ambiguity_eq_singleton {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {N : ℕ} (hN : 0 < N) (Ξ : Set E) (ξhat : Fin N → E)
    (hξ : ∀ i, ξhat i ∈ Ξ) :
    ambiguitySet 0 1 Ξ (empiricalDistribution ξhat) = {empiricalDistribution ξhat} := by
  have hPN := empirical_probability hN ξhat
  ext Q
  constructor
  · intro hQ
    have h : Q Set.univ=1 ∧ Q Ξᶜ=0 ∧
        wassersteinDistance 1 Q (empiricalDistribution ξhat) ≤ ENNReal.ofReal 0 := hQ
    have : IsProbabilityMeasure Q := ⟨h.1⟩
    exact zero_budget_measure_eq Q (empiricalDistribution ξhat) (by simpa using h.2.2)
  · intro hQ
    have he : Q=empiricalDistribution ξhat := hQ
    subst Q
    change (empiricalDistribution ξhat) Set.univ=1 ∧
      (empiricalDistribution ξhat) Ξᶜ=0 ∧
      wassersteinDistance 1 (empiricalDistribution ξhat) (empiricalDistribution ξhat) ≤ ENNReal.ofReal 0
    refine ⟨measure_univ, ?_, ?_⟩
    · simp [empiricalDistribution,Measure.smul_apply,Measure.finsetSum_apply,
        Measure.dirac_apply',hξ]
    · rw [empirical_self_distance_zero hN ξhat]
      exact bot_le

theorem zero_worstCase_eq_empirical_expect {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {N : ℕ} (hN : 0 < N) (Ξ : Set E) (ξhat : Fin N → E)
    (hξ : ∀ i, ξhat i ∈ Ξ) (L : E → EReal) :
    worstCaseExpectation 0 Ξ ξhat L = expect (empiricalDistribution ξhat) L := by
  unfold worstCaseExpectation
  rw [zero_ambiguity_eq_singleton hN Ξ ξhat hξ]
  simp
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open WassersteinDRO.Duality DupacovaWets.Consistency

theorem empirical_ae_of_samples {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] {N : ℕ} (ξhat : Fin N → E)
    (p : E → Prop) (hp : ∀ i, p (ξhat i)) : ∀ᵐ x ∂empiricalDistribution ξhat, p x := by
  unfold empiricalDistribution
  apply Measure.ae_smul_measure
  rw [ae_finsetSum_measure_iff]
  intro i hi
  rw [ae_dirac_eq]
  exact hp i

theorem empirical_expect_eq_of_finite_samples {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E)
    (L : E → EReal) (htop : ∀ i, L (ξhat i) ≠ ⊤) (hbot : ∀ i, L (ξhat i) ≠ ⊥) :
    expect (empiricalDistribution ξhat) L =
      ((1 / (N : ℝ) : ℝ) : EReal) * (∑ i, L (ξhat i)) := by
  let f : E → ℝ := fun x => (L x).toReal
  have hae : L =ᵐ[empiricalDistribution ξhat] (fun x => (f x : EReal)) := by
    apply empirical_ae_of_samples
    intro i
    exact (EReal.coe_toReal (htop i) (hbot i)).symm
  have he : expect (empiricalDistribution ξhat) L =
      expect (empiricalDistribution ξhat) (fun x => (f x : EReal)) := by
    apply le_antisymm
    · exact expect_mono _ _ _ (hae.mono fun x hx => hx.le)
    · exact expect_mono _ _ _ (hae.mono fun x hx => hx.ge)
  rw [he, expect_eq_integral _ f (empirical_integrable hN ξhat f),empirical_integral]
  have hs : (∑ i, L (ξhat i)) = ((∑ i, f (ξhat i) : ℝ) : EReal) := by
    have hh : ∀ i, L (ξhat i) = (f (ξhat i) : EReal) :=
      fun i => (EReal.coe_toReal (htop i) (hbot i)).symm
    simp only [hh]
    exact (map_sum (⟨⟨Real.toEReal, EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal) _ _).symm
  rw [hs,←EReal.coe_mul,one_div]
theorem empirical_expect_eq_of_ne_top_samples {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E)
    (L : E → EReal) (htop : ∀ i, L (ξhat i) ≠ ⊤) :
    expect (empiricalDistribution ξhat) L =
      ((1 / (N : ℝ) : ℝ) : EReal) * (∑ i, L (ξhat i)) := by
  by_cases hb : ∃ i, L (ξhat i) = ⊥
  · obtain ⟨i,hi⟩ := hb
    have hpos : (∫⁻ x, (L x).toENNReal ∂empiricalDistribution ξhat) ≠ ⊤ := by
      rw [empirical_lintegral]
      apply ENNReal.mul_ne_top
      · exact ENNReal.inv_ne_top.mpr (by exact_mod_cast hN.ne')
      · exact ENNReal.sum_ne_top.mpr (fun j _ => EReal.toENNReal_ne_top_iff.mpr (htop j))
    have hneg : (∫⁻ x, (-L x).toENNReal ∂empiricalDistribution ξhat) = ⊤ := by
      rw [empirical_lintegral]
      have hs : (∑ j : Fin N, (-L (ξhat j)).toENNReal) = ⊤ := by
        apply top_le_iff.mp
        have hh := Finset.single_le_sum (f:=fun j : Fin N => (-L (ξhat j)).toENNReal) (fun j _ => (bot_le : (0 : ENNReal) ≤ (-L (ξhat j)).toENNReal)) (Finset.mem_univ i)
        simpa [hi] using hh
      rw [hs,ENNReal.mul_top]
      simp
    have hs : (∑ j : Fin N, L (ξhat j)) = ⊥ := by
      rw [←Finset.add_sum_erase _ _ (Finset.mem_univ i),hi,EReal.bot_add]
    rw [expect,if_neg hpos,hneg,EReal.coe_ennreal_top,EReal.sub_top,hs]
    symm
    exact EReal.mul_bot_of_pos (by exact_mod_cast (one_div_pos.mpr (Nat.cast_pos.mpr hN)))
  · apply empirical_expect_eq_of_finite_samples hN ξhat L htop
    intro i hi
    exact hb ⟨i,hi⟩

end WassReductionCodex


end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open WassDDRO.Reduction

theorem zero_worstCase_eq_sampleAverage {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (ξhat : Fin N → E) (hξ : ∀ i, ξhat i ∈ Ξ)
    (hne_top : ∀ k x, ℓ k x ≠ ⊤) :
    worstCaseExpectation 0 Ξ ξhat (maxLoss ℓ) =
      ((1 / (N : ℝ) : ℝ) : EReal) * (∑ i, maxLoss ℓ (ξhat i)) := by
  rw [zero_worstCase_eq_empirical_expect hN Ξ ξhat hξ]
  apply empirical_expect_eq_of_ne_top_samples hN ξhat
  intro i
  exact iSup_ne_top (fun k => hne_top k (ξhat i))
end WassReductionCodex

end

section
set_option autoImplicit false
open Filter Topology
namespace WassReductionCodex

/-- A linearly bounded upper semicontinuous extended-real loss has exact
zero-radius penalized envelopes, including value minus infinity at the sample. -/
theorem envelope_small_of_linear_upper {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (L : E → EReal) (xhat : E) (C A r : ℝ)
    (husc : UpperSemicontinuousAt L xhat)
    (hupper : ∀ x ∈ Ξ, L x ≤ ((C+A*‖x-xhat‖ : ℝ) : EReal))
    (hr : L xhat < (r : EReal)) :
    ∃ lam : ℝ, 0 ≤ lam ∧
      (⨆ x ∈ Ξ, L x-((lam*‖x-xhat‖ : ℝ) : EReal)) ≤ (r : EReal) := by
  have hn : ∀ᶠ x in 𝓝 xhat, L x < (r : EReal) := husc r hr
  obtain ⟨δ,hδ,hlocal⟩ := Metric.eventually_nhds_iff.mp hn
  let B := max 0 ((C-r)/δ)
  let lam := max 0 A+B
  have hB : 0 ≤ B := le_max_left _ _
  have hlam : 0 ≤ lam := add_nonneg (le_max_left _ _) hB
  refine ⟨lam,hlam,?_⟩
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  by_cases hd : ‖x-xhat‖ < δ
  · have hl : L x ≤ (r : EReal) := (hlocal (by simpa [dist_eq_norm] using hd)).le
    have hp : (0 : EReal) ≤ ((lam*‖x-xhat‖ : ℝ) : EReal) := by
      exact EReal.coe_nonneg.mpr (mul_nonneg hlam (norm_nonneg _))
    exact le_trans (by simpa using EReal.sub_le_sub le_rfl hp) hl
  · have hdist : δ ≤ ‖x-xhat‖ := le_of_not_gt hd
    have hfrac : (C-r)/δ ≤ B := le_max_right _ _
    have hCd : C-r ≤ B*δ := (div_le_iff₀ hδ).mp hfrac
    have hBd : B*δ ≤ B*‖x-xhat‖ := mul_le_mul_of_nonneg_left hdist hB
    have hAd : A*‖x-xhat‖ ≤ max 0 A*‖x-xhat‖ :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
    have hb : C+A*‖x-xhat‖-lam*‖x-xhat‖ ≤ r := by
      dsimp [lam]
      nlinarith
    have hh := EReal.sub_le_sub (hupper x hx) (le_refl ((lam*‖x-xhat‖ : ℝ) : EReal))
    rw [←EReal.coe_sub] at hh
    exact hh.trans (EReal.coe_le_coe_iff.mpr hb)

theorem envelope_limit_of_linear_upper {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (L : E → EReal) (xhat : E) (hxhat : xhat ∈ Ξ) (C A : ℝ)
    (husc : UpperSemicontinuousAt L xhat)
    (hupper : ∀ x ∈ Ξ, L x ≤ ((C+A*‖x-xhat‖ : ℝ) : EReal)) :
    Tendsto (fun lam : ℝ => ⨆ x ∈ Ξ, L x-((lam*‖x-xhat‖ : ℝ) : EReal))
      atTop (𝓝 (L xhat)) := by
  let F : ℝ → EReal := fun lam => ⨆ x ∈ Ξ, L x-((lam*‖x-xhat‖ : ℝ) : EReal)
  have hanti : Antitone F := by
    intro a b hab
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    apply le_trans _ (le_iSup₂_of_le x hx le_rfl)
    apply EReal.sub_le_sub le_rfl
    exact EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_right hab (norm_nonneg _))
  have hle : L xhat ≤ ⨅ lam, F lam := by
    apply le_iInf
    intro lam
    have hh : L xhat-((lam*‖xhat-xhat‖ : ℝ) : EReal) ≤ F lam :=
      le_iSup₂_of_le xhat hxhat le_rfl
    simpa [F] using hh
  have hge : (⨅ lam, F lam) ≤ L xhat := by
    by_contra hh
    obtain ⟨r,hr,hri⟩ := EReal.exists_between_coe_real (lt_of_not_ge hh)
    obtain ⟨lam,_,hlam⟩ := envelope_small_of_linear_upper Ξ L xhat C A r husc hupper hr
    exact (not_le_of_gt hri) ((iInf_le F lam).trans hlam)
  have he : (⨅ lam, F lam)=L xhat := le_antisymm hge hle
  rw [←he]
  exact tendsto_atTop_iInf hanti
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open WassDDRO.Reduction
 theorem ereal_neg_upper {α : Type*} [TopologicalSpace α] (f : α → EReal)
    (hf : LowerSemicontinuous f) : UpperSemicontinuous (fun x => -f x) := by
  change LowerSemicontinuous (fun x => OrderDual.toDual (-f x))
  have hg : Continuous (fun t : EReal => OrderDual.toDual (-t)) := continuous_neg
  have hm : Monotone (fun t : EReal => OrderDual.toDual (-t)) := fun x y h => EReal.neg_le_neg_iff.mpr h
  simpa only [Function.comp_def] using hg.comp_lowerSemicontinuous hf hm
 theorem shifted_upperSemicontinuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {K : ℕ} (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hA : Assumption41 Ξ ℓ) (k : Fin K) (z : StrongDual ℝ E) (xhat : E) :
    UpperSemicontinuous (fun ξ => ℓ k ξ-((z (ξ-xhat) : ℝ) : EReal)) := by
  have hl : UpperSemicontinuous (ℓ k) := by
    simpa only [neg_neg] using ereal_neg_upper (fun ξ => -ℓ k ξ) (hA.lsc k)
  have hc : Continuous (fun ξ => ((-z (ξ-xhat) : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp (z.continuous.comp (continuous_id.sub continuous_const)).neg
  have hs := hl.add' hc.upperSemicontinuous (fun ξ =>
    EReal.continuousAt_add (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _)))
  simpa only [sub_eq_add_neg, EReal.coe_neg] using hs
 theorem shifted_dual_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (L : EReal) : Continuous (fun z : StrongDual ℝ E => L-((z v : ℝ) : EReal)) := by
  have hc : Continuous (fun z : StrongDual ℝ E => ((-z v : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp ((ContinuousLinearMap.apply ℝ ℝ v).continuous.neg)
  have hs : Continuous (fun z : StrongDual ℝ E => L+((-z v : ℝ) : EReal)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (EReal.continuousAt_add (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _))).comp
      (continuousAt_const.prodMk hc.continuousAt)
  simpa only [sub_eq_add_neg,EReal.coe_neg] using hs
end WassReductionCodex

end

section
set_option autoImplicit false
open Filter Topology
namespace WassReductionCodex

theorem linear_upper_of_convex_epigraph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (L : E → EReal)
    (hne_top : ∀ x, L x ≠ ⊤)
    (hconvex : Convex ℝ {p : E×ℝ | -L p.1 ≤ (p.2 : EReal)})
    (x0 : E) (a : ℝ) (ha : L x0=(a : EReal))
    (husc : UpperSemicontinuousAt L x0) :
    ∃ C A : ℝ, 0 ≤ A ∧ ∀ x, L x ≤ ((C+A*‖x-x0‖ : ℝ) : EReal) := by
  have hn : ∀ᶠ x in 𝓝 x0, L x < ((a+1 : ℝ) : EReal) := by
    apply husc
    rw [ha]
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  obtain ⟨δ,hδ,hlocal⟩ := Metric.eventually_nhds_iff.mp hn
  refine ⟨a+1,2/δ,by positivity,?_⟩
  intro x
  cases hx : L x using EReal.rec with
  | bot => exact bot_le
  | top => exact False.elim (hne_top x hx)
  | coe b =>
    by_cases hd : ‖x-x0‖ < δ
    · have hb : b < a+1 := EReal.coe_lt_coe_iff.mp (by
        rw [←hx]
        exact hlocal (by simpa [dist_eq_norm] using hd))
      apply EReal.coe_le_coe_iff.mpr
      have hp : 0 ≤ (2/δ)*‖x-x0‖ := by positivity
      linarith
    · have hd0 : 0 < ‖x-x0‖ := lt_of_lt_of_le hδ (le_of_not_gt hd)
      let t : ℝ := δ/(2*‖x-x0‖)
      have ht : 0 < t := by dsimp [t];positivity
      have ht1 : t ≤ 1 := by
        dsimp [t]
        apply (div_le_iff₀ (by positivity)).mpr
        linarith [le_of_not_gt hd]
      have hp0 : (x0,-a) ∈ {p : E×ℝ | -L p.1 ≤ (p.2 : EReal)} := by
        change -L x0 ≤ ((-a : ℝ) : EReal)
        simp [ha, EReal.coe_neg]
      have hpx : (x,-b) ∈ {p : E×ℝ | -L p.1 ≤ (p.2 : EReal)} := by
        change -L x ≤ ((-b : ℝ) : EReal)
        simp [hx, EReal.coe_neg]
      have hc := hconvex hp0 hpx (sub_nonneg.mpr ht1) ht.le (by ring : (1-t)+t=1)
      change -L ((1-t) • x0+t • x) ≤ (((1-t)*(-a)+t*(-b) : ℝ) : EReal) at hc
      have hvec : (1-t) • x0+t • x-x0 = t • (x-x0) := by module
      have hnorm : ‖(1-t) • x0+t • x-x0‖ = δ/2 := by
        rw [hvec,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
        dsimp [t]
        field_simp
      have hu := (hlocal (y:=(1-t) • x0+t • x) (by
        rw [dist_eq_norm,hnorm];linarith)).le
      have hlow : (((1-t)*a+t*b : ℝ) : EReal) ≤ L ((1-t) • x0+t • x) := by
        have hc' : -L ((1-t) • x0+t • x) ≤ -(((1-t)*a+t*b : ℝ) : EReal) := by
          convert hc using 1 <;> simp only [←EReal.coe_neg] <;> congr 1 <;> ring
        exact EReal.neg_le_neg_iff.mp hc'
      have hb : (1-t)*a+t*b ≤ a+1 := by
        have hh := hlow.trans hu
        exact EReal.coe_le_coe_iff.mp hh
      have htd : t*((2/δ)*‖x-x0‖)=1 := by dsimp [t];field_simp <;> ring
      apply EReal.coe_le_coe_iff.mpr
      have hbx : b ≤ a+(2/δ)*‖x-x0‖ := by nlinarith
      linarith
end WassReductionCodex

end

section
set_option autoImplicit false
open Filter Topology
namespace WassReductionCodex
open WassDDRO.Reduction

theorem maxLoss_upperSemicontinuous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] {K : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ) :
    UpperSemicontinuous (maxLoss ℓ) := by
  intro x r hr
  obtain ⟨q,hq,hqr⟩ := exists_between hr
  have he : ∀ k, ∀ᶠ y in 𝓝 x, ℓ k y < q := by
    intro k
    have hu : UpperSemicontinuous (ℓ k) := by
      simpa only [neg_neg] using ereal_neg_upper (fun y => -ℓ k y) (hA.lsc k)
    exact hu x q (lt_of_le_of_lt (le_iSup (fun k => ℓ k x) k) hq)
  filter_upwards [eventually_all.mpr he] with y hy
  exact lt_of_le_of_lt (iSup_le (fun k => (hy k).le)) hqr

theorem maxLoss_linear_upper {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] {K : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ) (xhat : E) :
    ∃ C A : ℝ, 0 ≤ A ∧ ∀ x, maxLoss ℓ x ≤ ((C+A*‖x-xhat‖ : ℝ) : EReal) := by
  classical
  have hp : ∀ k, ∃ C A : ℝ, 0 ≤ A ∧ ∀ x, ℓ k x ≤ ((C+A*‖x-xhat‖ : ℝ) : EReal) := by
    intro k
    obtain ⟨x0,_,hx0⟩ := hA.not_bot_on k
    have ha := EReal.coe_toReal (hA.ne_top k x0) hx0
    have hu : UpperSemicontinuous (ℓ k) := by
      simpa only [neg_neg] using ereal_neg_upper (fun y => -ℓ k y) (hA.lsc k)
    obtain ⟨C,A,hA0,hbound⟩ := linear_upper_of_convex_epigraph (ℓ k) (hA.ne_top k)
      (hA.convex_epigraph k) x0 (ℓ k x0).toReal ha.symm (hu x0)
    refine ⟨C+A*‖xhat-x0‖,A,hA0,?_⟩
    intro x
    have hd : ‖x-x0‖ ≤ ‖x-xhat‖+‖xhat-x0‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    apply (hbound x).trans
    apply EReal.coe_le_coe_iff.mpr
    nlinarith [mul_le_mul_of_nonneg_left hd hA0]
  choose C A hA0 hbound using hp
  refine ⟨∑ k, |C k|, ∑ k, A k,Finset.sum_nonneg (fun k _ => hA0 k),?_⟩
  intro x
  apply iSup_le
  intro k
  have hc : C k ≤ ∑ j, |C j| := (le_abs_self _).trans
    (Finset.single_le_sum (f:=fun j : Fin K => |C j|) (fun j _ => abs_nonneg _) (Finset.mem_univ k))
  have ha : A k ≤ ∑ j, A j := Finset.single_le_sum (fun j _ => hA0 j) (Finset.mem_univ k)
  apply (hbound k x).trans
  exact EReal.coe_le_coe_iff.mpr (add_le_add hc (mul_le_mul_of_nonneg_right ha (norm_nonneg _)))

theorem maxLoss_envelope_limit {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] {K : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (xhat : E) (hxhat : xhat ∈ Ξ) :
    Tendsto (fun lam : ℝ => ⨆ x ∈ Ξ, maxLoss ℓ x-((lam*‖x-xhat‖ : ℝ) : EReal))
      atTop (𝓝 (maxLoss ℓ xhat)) := by
  obtain ⟨C,A,_,hupper⟩ := maxLoss_linear_upper Ξ ℓ hA xhat
  exact envelope_limit_of_linear_upper Ξ (maxLoss ℓ) xhat hxhat C A
    (maxLoss_upperSemicontinuous Ξ ℓ hA xhat) (fun x _ => hupper x)
end WassReductionCodex

end

section
set_option autoImplicit false
open Filter Topology
namespace WassReductionCodex
open WassDDRO.Reduction

lemma ereal_sum_ne_top {ι : Type*} (s : Finset ι) (f : ι → EReal)
    (hf : ∀ i ∈ s, f i ≠ ⊤) : (∑ i ∈ s, f i) ≠ ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact EReal.add_ne_top (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma tendsto_ereal_finset_sum {α ι : Type*} (F : Filter α) (s : Finset ι)
    (f : ι → α → EReal) (a : ι → EReal)
    (ha : ∀ i ∈ s, a i ≠ ⊤) (hf : ∀ i ∈ s, Tendsto (f i) F (𝓝 (a i))) :
    Tendsto (fun x => ∑ i ∈ s, f i x) F (𝓝 (∑ i ∈ s, a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (tendsto_const_nhds : Tendsto (fun _ : α => (0 : EReal)) F (𝓝 0))
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    have hs := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hc := EReal.continuousAt_add (p:=(a i, ∑ j ∈ s, a j)) (.inl (ha i (Finset.mem_insert_self _ _)))
      (.inr (ereal_sum_ne_top s a (fun j hj => ha j (Finset.mem_insert_of_mem hj))))
    exact hc.tendsto.comp ((hf i (Finset.mem_insert_self _ _)).prodMk_nhds hs)

theorem envelope_average_limit {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] {K N : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (ξhat : Fin N → E) (hξ : ∀ i, ξhat i ∈ Ξ) :
    Tendsto (fun lam : ℝ => ((1 / (N : ℝ) : ℝ) : EReal) *
      ∑ i, (⨆ x ∈ Ξ, maxLoss ℓ x-((lam*‖x-ξhat i‖ : ℝ) : EReal)))
      atTop (𝓝 (((1 / (N : ℝ) : ℝ) : EReal) * (∑ i, maxLoss ℓ (ξhat i)))) := by
  have ht := tendsto_ereal_finset_sum atTop Finset.univ
    (fun i (lam : ℝ) => ⨆ x ∈ Ξ, maxLoss ℓ x-((lam*‖x-ξhat i‖ : ℝ) : EReal))
    (fun i => maxLoss ℓ (ξhat i))
    (fun i _ => iSup_ne_top (fun k => hA.ne_top k (ξhat i)))
    (fun i _ => maxLoss_envelope_limit Ξ ℓ hA (ξhat i) (hξ i))
  exact EReal.Tendsto.const_mul ht (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))
end WassReductionCodex

end

section
set_option autoImplicit false
open Filter Topology
namespace WassReductionCodex

theorem exists_real_scores_lt_average {N : ℕ} (a : Fin N → EReal)
    (hne_top : ∀ i, a i ≠ ⊤) (r : ℝ)
    (hr : ((1/(N : ℝ) : ℝ) : EReal)*(∑ i, a i) < (r : EReal)) :
    ∃ s : Fin N → ℝ, (∀ i, a i < (s i : EReal)) ∧ (1/(N : ℝ))*∑ i, s i < r := by
  classical
  let s : Fin N → ℕ → ℝ := fun i n => if a i=⊥ then -(n : ℝ) else (a i).toReal+1/(n+1)
  have hscore : ∀ i n, a i < (s i n : EReal) := by
    intro i n
    by_cases hb : a i=⊥
    · simpa only [s,if_pos hb,hb] using EReal.bot_lt_coe (-(n : ℝ))
    · dsimp only [s]
      rw [if_neg hb,←EReal.coe_toReal (hne_top i) hb]
      apply EReal.coe_lt_coe_iff.mpr
      simpa using (Nat.one_div_pos_of_nat (n:=n) : (0 : ℝ)<1/(n+1))
  have ht : ∀ i, Tendsto (fun n => (s i n : EReal)) atTop (𝓝 (a i)) := by
    intro i
    by_cases hb : a i=⊥
    · simp only [s,hb,if_pos]
      exact EReal.tendsto_coe_nhds_bot_iff.mpr
        (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
    · simp only [s,if_neg hb]
      rw [←EReal.coe_toReal (hne_top i) hb]
      apply continuous_coe_real_ereal.continuousAt.tendsto.comp
      simpa using (tendsto_const_nhds (x:=(a i).toReal)).add
        tendsto_one_div_add_atTop_nhds_zero_nat
  have hsum := tendsto_ereal_finset_sum atTop Finset.univ
    (fun i n => (s i n : EReal)) a (fun i _ => hne_top i) (fun i _ => ht i)
  have hav := EReal.Tendsto.const_mul (a:=((1/(N : ℝ) : ℝ) : EReal)) hsum
    (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))
  have hev : ∀ᶠ n : ℕ in atTop,
      ((1/(N : ℝ) : ℝ) : EReal)*(∑ i, (s i n : EReal)) < (r : EReal) :=
    hav.eventually (isOpen_Iio.mem_nhds hr)
  obtain ⟨n,hn⟩ := hev.exists
  refine ⟨fun i => s i n,fun i => hscore i n,?_⟩
  have hs : (∑ i, (s i n : EReal)) = ((∑ i, s i n : ℝ) : EReal) :=
    (map_sum (⟨⟨Real.toEReal,EReal.coe_zero⟩,EReal.coe_add⟩ : ℝ →+ EReal) _ _).symm
  rw [hs,←EReal.coe_mul] at hn
  exact EReal.coe_lt_coe_iff.mp hn
end WassReductionCodex

end

section
set_option autoImplicit false
open Filter Topology
namespace WassReductionCodex
open WassDDRO.Reduction

theorem zero_program_le_scores {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] {K N : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (ξhat : Fin N → E) (s : Fin N → ℝ)
    (hs : ∀ i, maxLoss ℓ (ξhat i) < (s i : EReal)) :
    program12cValue 0 Ξ ξhat (maxLoss ℓ) ≤ (((1/(N : ℝ))*∑ i, s i : ℝ) : EReal) := by
  classical
  have hp : ∀ i, ∃ lam : ℝ, 0 ≤ lam ∧
      (⨆ x ∈ Ξ, maxLoss ℓ x-((lam*‖x-ξhat i‖ : ℝ) : EReal)) ≤ (s i : EReal) := by
    intro i
    obtain ⟨C,A,_,hupper⟩ := maxLoss_linear_upper Ξ ℓ hA (ξhat i)
    exact envelope_small_of_linear_upper Ξ (maxLoss ℓ) (ξhat i) C A (s i)
      (maxLoss_upperSemicontinuous Ξ ℓ hA (ξhat i)) (fun x _ => hupper x) (hs i)
  choose lam hnonneg hbound using hp
  let Λ : ℝ := ∑ i, lam i
  have hΛ : 0 ≤ Λ := Finset.sum_nonneg (fun i _ => hnonneg i)
  have he : ∀ i, (⨆ x ∈ Ξ, maxLoss ℓ x-((Λ*‖x-ξhat i‖ : ℝ) : EReal)) ≤ (s i : EReal) := by
    intro i
    apply le_trans _ (hbound i)
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    apply le_trans _ (le_iSup₂_of_le x hx le_rfl)
    apply EReal.sub_le_sub le_rfl
    apply EReal.coe_le_coe_iff.mpr
    exact mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)) (norm_nonneg _)
  unfold program12cValue
  apply iInf_le_of_le Λ
  apply iInf_le_of_le s
  apply iInf_le_of_le he
  apply iInf_le_of_le hΛ
  simp

theorem zero_program_le_sampleAverage {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] {K N : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (ξhat : Fin N → E) :
    program12cValue 0 Ξ ξhat (maxLoss ℓ) ≤
      ((1/(N : ℝ) : ℝ) : EReal)*(∑ i, maxLoss ℓ (ξhat i)) := by
  by_contra h
  obtain ⟨r,hr,hrp⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
  obtain ⟨s,hs,havg⟩ := exists_real_scores_lt_average (fun i => maxLoss ℓ (ξhat i))
    (fun i => iSup_ne_top (fun k => hA.ne_top k (ξhat i))) r hr
  have hp := zero_program_le_scores Ξ ℓ hA ξhat s hs
  exact (not_le_of_gt hrp) (hp.trans (EReal.coe_le_coe_iff.mpr havg.le))
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
 theorem exists_sample_barrier {E : Type*} {N : ℕ} (ξhat : Fin N → E) (s : Fin N → ℝ) :
    ∃ ψ : E → ℝ, (∀ i, ψ (ξhat i)≤ s i) ∧
      ∀ y ∈ Set.range ξhat, ∃ i, ξhat i=y ∧ ψ y=s i := by
  classical
  have hchoose (y : E) (hy : y ∈ Set.range ξhat) :
      ∃ i, ξhat i=y ∧ ∀ j, ξhat j=y → s i≤ s j := by
    obtain ⟨j,hj⟩ := hy
    have hn : (Finset.univ.filter (fun i => ξhat i=y)).Nonempty := ⟨j,by simp [hj]⟩
    obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image (Finset.univ.filter (fun i => ξhat i=y)) s hn
    refine ⟨i,(Finset.mem_filter.mp hi).2,?_⟩
    intro j hj
    exact hmin j (by simp [hj])
  choose idx hi hmin using hchoose
  let ψ := fun y => if hy : y ∈ Set.range ξhat then s (idx y hy) else 0
  refine ⟨ψ,?_,?_⟩
  · intro i
    have hy : ξhat i ∈ Set.range ξhat := Set.mem_range_self i
    simp only [ψ,dif_pos hy]
    exact hmin (ξhat i) hy i rfl
  · intro y hy
    refine ⟨idx y hy,hi y hy,?_⟩
    simp only [ψ,dif_pos hy]
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory Filter Topology
namespace WassReductionCodex
open WassDDRO.Reduction WassersteinDRO.Duality DupacovaWets.Consistency
 theorem transport_epigraph_upper {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] {N : ℕ} (hN : 0<N)
    (Ξ : Set E) (L : E → EReal) (hL : Measurable L) (ξhat : Fin N → E)
    (ε lam : ℝ) (hε : 0≤ε) (hlam : 0≤lam) (s : Fin N → ℝ)
    (he : ∀ i, (⨆ ξ ∈ Ξ, L ξ-((lam*‖ξ-ξhat i‖ : ℝ) : EReal)) ≤ (s i : EReal))
    (Q : Measure E) (hQ : Q Ξᶜ=0)
    (hbudget : wassersteinDistance 1 Q (empiricalDistribution ξhat)≤ENNReal.ofReal ε) :
    expect Q L ≤ ((lam*ε+(1/(N : ℝ))*∑ i, s i : ℝ) : EReal) := by
  obtain ⟨ψ,hψ,hsel⟩ := exists_sample_barrier ξhat s
  have hiψ := empirical_integrable hN ξhat ψ
  have hav : (∫ y, ψ y ∂empiricalDistribution ξhat) ≤ (1/(N : ℝ))*∑ i, s i := by
    rw [empirical_integral,one_div]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hψ i)) (by positivity)
  have hsupport : (empiricalDistribution ξhat) (Set.range ξhat)ᶜ=0 := by
    simp [empiricalDistribution,Measure.smul_apply,Measure.finsetSum_apply,Measure.dirac_apply',Set.mem_range_self]
  have hupper (η : ℝ) (hη : 0<η) :
      expect Q L ≤ ((lam*(ε+η)+(1/(N : ℝ))*∑ i, s i : ℝ) : EReal) := by
    obtain ⟨π,hm,hc⟩ := exists_coupling_lt_budget_add Q (empiricalDistribution ξhat) ε η hε hη hbudget
    have hcfin : (∫⁻ w, ENNReal.ofReal ‖w.1-w.2‖ ∂π) ≠ ⊤ := (lt_of_lt_of_le hc le_top).ne
    have hx : ∀ᵐ w ∂π, w.1∈Ξ := by
      rw [ae_iff]
      change π (Prod.fst ⁻¹' Ξᶜ)=0
      have ht := π.le_map_apply measurable_fst.aemeasurable Ξᶜ
      rw [hm.1,hQ] at ht
      exact le_antisymm ht bot_le
    have hy : ∀ᵐ w ∂π, w.2∈Set.range ξhat := by
      rw [ae_iff]
      change π (Prod.snd ⁻¹' (Set.range ξhat)ᶜ)=0
      have ht := π.le_map_apply measurable_snd.aemeasurable (Set.range ξhat)ᶜ
      rw [hm.2,hsupport] at ht
      exact le_antisymm ht bot_le
    have hb : ∀ᵐ w ∂π, L w.1≤((lam*‖w.1-w.2‖+ψ w.2 : ℝ) : EReal) := by
      filter_upwards [hx,hy] with w hwx hwy
      obtain ⟨i,hiy,hψy⟩ := hsel w.2 hwy
      have hp : L w.1-((lam*‖w.1-ξhat i‖ : ℝ) : EReal) ≤ (s i : EReal) :=
        le_trans (le_iSup₂_of_le w.1 hwx le_rfl) (he i)
      rw [hiy] at hp
      have hu := (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))).mp hp
      simpa only [hψy,← EReal.coe_add,add_comm] using hu
    have hg := coupling_upper Q (empiricalDistribution ξhat) π L ψ lam hL hiψ hm hcfin hb
    have hr := mul_le_mul_of_nonneg_left (ENNReal.toReal_lt_of_lt_ofReal hc).le hlam
    exact le_trans hg (EReal.coe_le_coe_iff.mpr (add_le_add hr hav))
  have hη : Tendsto (fun n : ℕ => (1 : ℝ)/(n+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have htR : Tendsto (fun n : ℕ => lam*(ε+(1 : ℝ)/(n+1))+(1/(N : ℝ))*∑ i, s i)
      atTop (𝓝 (lam*ε+(1/(N : ℝ))*∑ i, s i)) := by
    have heR : Tendsto (fun n : ℕ => ε+(1 : ℝ)/(n+1)) atTop (𝓝 ε) := by
      simpa using tendsto_const_nhds.add hη
    exact (tendsto_const_nhds.mul heR).add tendsto_const_nhds
  have ht := (continuous_coe_real_ereal.tendsto (lam*ε+(1/(N : ℝ))*∑ i, s i)).comp htR
  exact isClosed_Ici.mem_of_tendsto ht
    (Eventually.of_forall fun n => hupper ((1 : ℝ)/(n+1)) (by positivity))

end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
 theorem dual_ball_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (lam : ℝ) (hlam : 0≤lam) :
    ∃ z : StrongDual ℝ E, ‖z‖≤lam ∧ z v=lam*‖v‖ ∧
      ∀ w : StrongDual ℝ E, ‖w‖≤lam → w v≤lam*‖v‖ := by
  obtain ⟨g,hg,hv⟩ := exists_dual_vector'' ℝ v
  refine ⟨lam • g, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam]
    nlinarith [mul_le_mul_of_nonneg_left hg hlam]
  · simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hv, RCLike.ofReal_real_eq_id, id_eq]
  · intro w hw
    calc
      w v ≤ |w v| := le_abs_self _
      _ ≤ ‖w‖*‖v‖ := by simpa only [Real.norm_eq_abs] using w.le_opNorm v
      _ ≤ lam*‖v‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg v)
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
 theorem pointwise_dual_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (lam : ℝ) (hlam : 0≤lam) (L : EReal) :
    L-((lam*‖v‖ : ℝ) : EReal) =
      (⨅ z ∈ {z : StrongDual ℝ E | ‖z‖≤lam}, L-((z v : ℝ) : EReal)) ∧
    ∃ z : StrongDual ℝ E, ‖z‖≤lam ∧ L-((z v : ℝ) : EReal)=L-((lam*‖v‖ : ℝ) : EReal) := by
  obtain ⟨z,hz,he,hbound⟩ := dual_ball_support v lam hlam
  refine ⟨?_,z,hz,?_⟩
  · apply le_antisymm
    · apply le_iInf
      intro w
      apply le_iInf
      intro hw
      exact EReal.sub_le_sub le_rfl (EReal.coe_le_coe_iff.mpr (hbound w hw))
    · apply iInf_le_of_le z
      apply iInf_le_of_le hz
      rw [he]
  · rw [he]
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open WassDDRO.Reduction
 theorem finite_threshold_iff (L : EReal) (r d : ℝ) :
    -L ≤ ((-r-d : ℝ) : EReal) ↔ (r : EReal) ≤ L-(d : EReal) := by
  cases L using EReal.rec <;> simp only [EReal.neg_bot, EReal.neg_top,
    EReal.bot_sub, EReal.top_sub (EReal.coe_ne_top _), top_le_iff, le_bot_iff,
    EReal.coe_ne_top, EReal.coe_ne_bot, not_false_eq_true, false_iff, iff_false,
    ← EReal.coe_neg, ← EReal.coe_sub, EReal.coe_le_coe_iff, bot_le, le_top]
  constructor <;> intro h <;> linarith
 theorem shifted_quasiconcave {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {K : ℕ} (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hA : Assumption41 Ξ ℓ) (k : Fin K) (z : StrongDual ℝ E) (xhat : E) :
    QuasiconcaveOn ℝ Ξ (fun ξ => ℓ k ξ-((z (ξ-xhat) : ℝ) : EReal)) := by
  intro r
  cases r using EReal.rec with
  | bot => simpa using hA.convex
  | top =>
    have he : Ξ ∩ {ξ | (⊤ : EReal) ≤ ℓ k ξ-((z (ξ-xhat) : ℝ) : EReal)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ξ hx
      have hn : ℓ k ξ-((z (ξ-xhat) : ℝ) : EReal) ≠ ⊤ := by
        cases h : ℓ k ξ using EReal.rec
        · simp
        · simp [← EReal.coe_sub]
        · exact False.elim (hA.ne_top k ξ h)
      exact hn (top_le_iff.mp hx.2)
    change Convex ℝ (Ξ ∩ {ξ | (⊤ : EReal) ≤ ℓ k ξ-((z (ξ-xhat) : ℝ) : EReal)})
    rw [he]
    exact convex_empty
  | coe r =>
    intro x hx y hy a b ha hb hab
    refine ⟨hA.convex hx.1 hy.1 ha hb hab, ?_⟩
    have hx' : (x,-r-z (x-xhat)) ∈ {p : E×ℝ | -ℓ k p.1 ≤ (p.2 : EReal)} :=
      (finite_threshold_iff (ℓ k x) r (z (x-xhat))).mpr hx.2
    have hy' : (y,-r-z (y-xhat)) ∈ {p : E×ℝ | -ℓ k p.1 ≤ (p.2 : EReal)} :=
      (finite_threshold_iff (ℓ k y) r (z (y-xhat))).mpr hy.2
    have hc := hA.convex_epigraph k hx' hy' ha hb hab
    change -ℓ k (a • x+b • y) ≤
      ((a*(-r-z (x-xhat))+b*(-r-z (y-xhat)) : ℝ) : EReal) at hc
    have hd : a*(-r-z (x-xhat))+b*(-r-z (y-xhat)) = -r-z (a • x+b • y-xhat) := by
      simp only [map_sub,map_add,map_smul,smul_eq_mul]
      linear_combination (-r+z xhat)*hab
    rw [hd] at hc
    exact (finite_threshold_iff (ℓ k (a • x+b • y)) r (z (a • x+b • y-xhat))).mp hc
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open WassDDRO.Reduction
 theorem shifted_dual_quasiconvex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set (StrongDual ℝ E)) (hC : Convex ℝ C) (v : E) (L : EReal) :
    QuasiconvexOn ℝ C (fun z => L-((z v : ℝ) : EReal)) := by
  cases L using EReal.rec with
  | bot => intro r;simpa only [EReal.bot_sub,bot_le,Set.sep_true] using hC
  | top =>
    intro r
    by_cases hr : (⊤ : EReal)≤r
    · simpa only [EReal.top_sub (EReal.coe_ne_top _),hr,Set.sep_true] using hC
    · simpa only [EReal.top_sub (EReal.coe_ne_top _),hr,Set.sep_false] using
        (show Convex ℝ (∅ : Set (StrongDual ℝ E)) from convex_empty)
  | coe r =>
    have hc : ConvexOn ℝ C (fun z : StrongDual ℝ E => r-z v) := by
      refine ⟨hC, ?_⟩
      intro x hx y hy a b ha hb hab
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      have hr := congrArg (fun t : ℝ => t*r) hab
      nlinarith
    have hm : Monotone (fun r : ℝ => (r : EReal)) := fun a b h => EReal.coe_le_coe_iff.mpr h
    simpa only [Function.comp_def, ← EReal.coe_sub] using hc.quasiconvexOn.monotone_comp hm

 theorem minimax_dual_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] {K : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (k : Fin K) (xhat : E) (lam : ℝ) (hlam : 0≤lam) :
    (⨆ ξ ∈ Ξ, ℓ k ξ-((lam*‖ξ-xhat‖ : ℝ) : EReal)) =
      (⨅ z ∈ {z : StrongDual ℝ E | ‖z‖≤lam},
        ⨆ ξ ∈ Ξ, ℓ k ξ-((z (ξ-xhat) : ℝ) : EReal)) ∧
    ∃ z : StrongDual ℝ E, ‖z‖≤lam ∧
      (⨆ ξ ∈ Ξ, ℓ k ξ-((z (ξ-xhat) : ℝ) : EReal)) =
        (⨆ ξ ∈ Ξ, ℓ k ξ-((lam*‖ξ-xhat‖ : ℝ) : EReal)) := by
  let B := {z : StrongDual ℝ E | ‖z‖≤lam}
  let F := fun (z : StrongDual ℝ E) (ξ : E) => ℓ k ξ-((z (ξ-xhat) : ℝ) : EReal)
  have hB : B=Metric.closedBall (0 : StrongDual ℝ E) lam := by
    ext z
    simp only [B,Set.mem_setOf_eq,Metric.mem_closedBall,dist_zero_right]
  have hne : B.Nonempty := ⟨0,by simpa only [B,Set.mem_setOf_eq,norm_zero] using hlam⟩
  have hc : Convex ℝ B := by rw [hB];exact convex_closedBall 0 lam
  have hk : IsCompact B := by rw [hB];exact isCompact_closedBall 0 lam
  have hsion := Sion.minimax' (f:=F) hne hc hk
    (fun ξ _ => (shifted_dual_continuous (ξ-xhat) (ℓ k ξ)).lowerSemicontinuous.lowerSemicontinuousOn B)
    (fun ξ _ => shifted_dual_quasiconvex B hc (ξ-xhat) (ℓ k ξ)) hA.convex
    (fun z _ => (shifted_upperSemicontinuous Ξ ℓ hA k z xhat).upperSemicontinuousOn Ξ)
    (fun z _ => shifted_quasiconcave Ξ ℓ hA k z xhat)
  have hp (ξ : E) : (⨅ z ∈ B, F z ξ)=ℓ k ξ-((lam*‖ξ-xhat‖ : ℝ) : EReal) :=
    (pointwise_dual_ball (ξ-xhat) lam hlam (ℓ k ξ)).1.symm
  have he : (⨆ ξ ∈ Ξ, ℓ k ξ-((lam*‖ξ-xhat‖ : ℝ) : EReal)) = ⨅ z ∈ B, ⨆ ξ ∈ Ξ, F z ξ := by
    simpa only [hp] using hsion.symm
  have hlow : LowerSemicontinuous (fun z => ⨆ ξ ∈ Ξ, F z ξ) :=
    lowerSemicontinuous_iSup (fun ξ => lowerSemicontinuous_iSup (fun _ =>
      (shifted_dual_continuous (ξ-xhat) (ℓ k ξ)).lowerSemicontinuous))
  obtain ⟨z,hz,hmin⟩ := hlow.lowerSemicontinuousOn B |>.exists_isMinOn hne hk
  have hv : (⨅ w ∈ B, ⨆ ξ ∈ Ξ, F w ξ) = ⨆ ξ ∈ Ξ, F z ξ := by
    apply le_antisymm
    · exact iInf_le_of_le z (iInf_le_of_le hz le_rfl)
    · exact le_iInf₂ hmin
  refine ⟨he,z,hz,?_⟩
  rw [he,hv]
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open WassDDRO.Reduction
 theorem iSup_sub_real {α : Sort*} (f : α → EReal) (c : ℝ) :
    (⨆ i, f i)-(c : EReal) = ⨆ i, f i-(c : EReal) := by
  have hs {a b : EReal} : a-(c : EReal)≤b ↔ a≤b+(c : EReal) :=
    EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot c)) (.inl (EReal.coe_ne_top c))
  apply le_antisymm
  · apply hs.mpr
    apply iSup_le
    intro i
    exact hs.mp (le_iSup (fun i => f i-(c : EReal)) i)
  · apply iSup_le
    intro i
    exact EReal.sub_le_sub (le_iSup f i) le_rfl
 theorem conjugate_neg_sign {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (Ξ : Set E) (ℓ : E → EReal) (z : StrongDual ℝ E) (xhat : E) :
    conjOn Ξ (fun ξ => -ℓ ξ) (-z) - (((-z) xhat : ℝ) : EReal) =
      ⨆ ξ ∈ Ξ, ℓ ξ-((z (ξ-xhat) : ℝ) : EReal) := by
  rw [conjOn,iSup_sub_real]
  congr 1
  funext ξ
  rw [iSup_sub_real]
  congr 1
  funext hξ
  cases h : ℓ ξ using EReal.rec <;>
    simp only [neg_apply, map_sub, EReal.neg_bot, EReal.neg_top,
      EReal.sub_top, EReal.sub_bot (EReal.coe_ne_bot _), EReal.top_sub (EReal.coe_ne_top _), EReal.bot_sub,
      ← EReal.coe_neg, ← EReal.coe_sub]
  congr 1
  ring
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open WassDDRO.Reduction
 theorem envelope_to_conjugate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] {K N : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (ξhat : Fin N → E) (lam : ℝ) (hlam : 0≤lam) (s : Fin N → ℝ)
    (h : ∀ i, (⨆ ξ ∈ Ξ, maxLoss ℓ ξ-((lam*‖ξ-ξhat i‖ : ℝ) : EReal)) ≤ (s i : EReal)) :
    ∃ z : Fin N → Fin K → StrongDual ℝ E,
      (∀ i k, conjOn Ξ (fun ξ => -ℓ k ξ) (z i k)-((z i k (ξhat i) : ℝ) : EReal) ≤ (s i : EReal)) ∧
      ∀ i k, ‖z i k‖≤lam := by
  classical
  choose z hz he using (fun (i : Fin N) (k : Fin K) => (minimax_dual_ball Ξ ℓ hA k (ξhat i) lam hlam).2)
  refine ⟨fun i k => -z i k, ?_, ?_⟩
  · intro i k
    rw [conjugate_neg_sign,he i k]
    apply iSup_le
    intro ξ
    apply iSup_le
    intro hξ
    have hp : ℓ k ξ ≤ maxLoss ℓ ξ := le_iSup (fun j => ℓ j ξ) k
    exact le_trans (EReal.sub_le_sub hp le_rfl)
      (le_trans (le_iSup₂_of_le ξ hξ le_rfl) (h i))
  · intro i k
    simpa only [norm_neg] using hz i k
 theorem conjugate_to_envelope {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {K N : ℕ} (hK : 0<K) (hN : 0<N)
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (ξhat : Fin N → E) (lam : ℝ) (s : Fin N → ℝ)
    (z : Fin N → Fin K → StrongDual ℝ E)
    (hc : ∀ i k, conjOn Ξ (fun ξ => -ℓ k ξ) (z i k)-((z i k (ξhat i) : ℝ) : EReal) ≤ (s i : EReal))
    (hn : ∀ i k, ‖z i k‖≤lam) :
    0≤lam ∧ ∀ i, (⨆ ξ ∈ Ξ, maxLoss ℓ ξ-((lam*‖ξ-ξhat i‖ : ℝ) : EReal)) ≤ (s i : EReal) := by
  have hlam : 0≤lam := le_trans (norm_nonneg (z ⟨0,hN⟩ ⟨0,hK⟩)) (hn _ _)
  refine ⟨hlam, ?_⟩
  intro i
  apply iSup_le
  intro ξ
  apply iSup_le
  intro hξ
  rw [maxLoss,iSup_sub_real]
  apply iSup_le
  intro k
  have hb : ‖-z i k‖≤lam := by simpa only [norm_neg] using hn i k
  have hp := (pointwise_dual_ball (ξ-ξhat i) lam hlam (ℓ k ξ)).1
  rw [hp]
  apply le_trans (iInf_le_of_le (-z i k) (iInf_le_of_le hb le_rfl))
  have he := conjugate_neg_sign Ξ (ℓ k) (-z i k) (ξhat i)
  simp only [neg_neg] at he
  have hci := hc i k
  rw [he] at hci
  exact le_trans (le_iSup₂_of_le ξ hξ le_rfl) hci
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open WassDDRO.Reduction
 theorem worstCase_le_program12c {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hN : 0<N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (ξhat : Fin N → E) (ε : ℝ) (hε : 0≤ε) :
    worstCaseExpectation ε Ξ ξhat (maxLoss ℓ)≤program12cValue ε Ξ ξhat (maxLoss ℓ) := by
  have hL : Measurable (maxLoss ℓ) := by
    unfold maxLoss
    exact Measurable.iSup hmeas
  unfold worstCaseExpectation program12cValue
  apply le_iInf
  intro lam
  apply le_iInf
  intro s
  apply le_iInf
  intro he
  apply le_iInf
  intro hlam
  apply iSup_le
  intro Q
  apply iSup_le
  intro hQ
  exact transport_epigraph_upper hN Ξ (maxLoss ℓ) hL ξhat ε lam hε hlam s he Q hQ.2.1 hQ.2.2
 theorem program12c_le_program12f {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {K N : ℕ} (hK : 0<K) (hN : 0<N)
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (ξhat : Fin N → E) (ε : ℝ) :
    program12cValue ε Ξ ξhat (maxLoss ℓ)≤program12fValue ε Ξ ξhat ℓ := by
  unfold program12cValue program12fValue
  apply le_iInf
  intro lam
  apply le_iInf
  intro s
  apply le_iInf
  intro z
  apply le_iInf
  intro hc
  apply le_iInf
  intro hn
  obtain ⟨hlam,he⟩ := conjugate_to_envelope hK hN Ξ ℓ ξhat lam s z hc hn
  exact iInf_le_of_le lam (iInf_le_of_le s (iInf_le_of_le he (iInf_le_of_le hlam le_rfl)))
 theorem approximate_reduction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hK : 0<K) (hN : 0<N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (ξhat : Fin N → E) (ε : ℝ) (hε : 0≤ε) :
    worstCaseExpectation ε Ξ ξhat (maxLoss ℓ)≤program12fValue ε Ξ ξhat ℓ :=
  le_trans (worstCase_le_program12c hN Ξ ℓ hmeas ξhat ε hε)
    (program12c_le_program12f hK hN Ξ ℓ ξhat ε)
end WassReductionCodex

end

set_option autoImplicit false
open MeasureTheory Filter Topology WassDDRO.Reduction
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (ξhat : Fin N → E) (hξ : ∀ i, ξhat i ∈ Ξ)
    (hA : Assumption41 Ξ ℓ) :
    worstCaseExpectation 0 Ξ ξhat (maxLoss ℓ)
        = ((1 / (N : ℝ) : ℝ) : EReal) * (∑ i, maxLoss ℓ (ξhat i)) ∧
      Tendsto (fun lam : ℝ => ((1 / (N : ℝ) : ℝ) : EReal) *
          ∑ i, (⨆ ξ ∈ Ξ, maxLoss ℓ ξ - ((lam * ‖ξ - ξhat i‖ : ℝ) : EReal)))
        atTop (𝓝 (((1 / (N : ℝ) : ℝ) : EReal) * (∑ i, maxLoss ℓ (ξhat i)))) ∧
      worstCaseExpectation 0 Ξ ξhat (maxLoss ℓ) = program12cValue 0 Ξ ξhat (maxLoss ℓ) := by
  have hz := WassReductionCodex.zero_worstCase_eq_sampleAverage hN Ξ ℓ ξhat hξ hA.ne_top
  refine ⟨hz, WassReductionCodex.envelope_average_limit Ξ ℓ hA ξhat hξ, ?_⟩
  apply le_antisymm
  · exact WassReductionCodex.worstCase_le_program12c hN Ξ ℓ hmeas ξhat 0 le_rfl
  · rw [hz]
    exact WassReductionCodex.zero_program_le_sampleAverage Ξ ℓ hA ξhat



#print axioms solution
