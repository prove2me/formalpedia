-- Prove2me | solution 1 for ResidualsDRO.Wass.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T11:38:51.290649+00:00
-- url     : https://prove2.me/submissions/c4d4e5d6-6704-48a0-8ba6-7f2e6ea5c247

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Definitions.Def_ResidualsDRO_Wass_Setting
import Theorems.Thm_ResidualsDRO_Wass_eq_6

open MeasureTheory

namespace RDROL3Aux

open WassersteinDRO.Duality

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [DecidableEq E] {n : ℕ}

/-- multiplicity of the value `v` among the atoms `a`. -/
def mult (a : Fin n → E) (v : E) : ℕ := (Finset.univ.filter (fun j => a j = v)).card

/-- the glued measure on `Fin n × E`. -/
noncomputable def glue (a : Fin n → E) (π : Measure (E × E)) : Measure (Fin n × E) :=
  ∑ i, ((mult a (a i) : ENNReal)⁻¹) •
    (π.restrict (Prod.fst ⁻¹' {a i})).map (fun z => (i, z.2))

lemma glue_lintegral (a : Fin n → E) (π : Measure (E × E)) (F : Fin n × E → ENNReal)
    (hF : Measurable F) :
    ∫⁻ w, F w ∂(glue a π) =
      ∑ i, ((mult a (a i) : ENNReal)⁻¹) * ∫⁻ z in Prod.fst ⁻¹' {a i}, F (i, z.2) ∂π := by
  unfold glue
  rw [lintegral_finset_sum_measure]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lintegral_smul_measure, lintegral_map hF (measurable_const.prodMk measurable_snd)]
  rfl

lemma emp_apply (b : Fin n → E) (T : Set E) (hT : MeasurableSet T) :
    empiricalDistribution b T = (n : ENNReal)⁻¹ * ∑ i, T.indicator 1 (b i) := by
  unfold empiricalDistribution
  rw [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.dirac_apply' _ hT]

lemma mult_pos (a : Fin n → E) (i : Fin n) : 0 < mult a (a i) := by
  unfold mult
  exact Finset.card_pos.2 ⟨i, by simp⟩

lemma piS (a : Fin n → E) (π : Measure (E × E)) (h1 : π.map Prod.fst = empiricalDistribution a)
    (i : Fin n) : π (Prod.fst ⁻¹' {a i}) = (n : ENNReal)⁻¹ * mult a (a i) := by
  rw [← Measure.map_apply measurable_fst (measurableSet_singleton _), h1,
    emp_apply _ _ (measurableSet_singleton _)]
  congr 1
  unfold mult
  simp only [Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply]
  rw [Finset.sum_boole]

lemma fiber (a : Fin n → E) (π : Measure (E × E)) (h1 : π.map Prod.fst = empiricalDistribution a)
    (H : E × E → ENNReal) :
    ∑ i, ((mult a (a i) : ENNReal)⁻¹) * ∫⁻ z in Prod.fst ⁻¹' {a i}, H z ∂π = ∫⁻ z, H z ∂π := by
  classical
  -- the complement of the atoms is null
  have hR : MeasurableSet (Set.range a) := (Set.finite_range a).measurableSet
  have hnull : π (Prod.fst ⁻¹' Set.range a)ᶜ = 0 := by
    rw [← Set.preimage_compl, ← Measure.map_apply measurable_fst hR.compl, h1,
      emp_apply _ _ hR.compl]
    simp
  rw [← lintegral_add_compl H (measurable_fst hR), setLIntegral_measure_zero _ _ hnull, add_zero]
  have hU : (Prod.fst ⁻¹' Set.range a : Set (E × E)) = ⋃ v ∈ Finset.univ.image a, Prod.fst ⁻¹' ({v} : Set E) := by
    ext z; simp [eq_comm]
  rw [hU, lintegral_biUnion_finset]
  · rw [Finset.sum_comp (fun v => ((mult a v : ENNReal)⁻¹) *
      ∫⁻ z in Prod.fst ⁻¹' {v}, H z ∂π) a]
    refine Finset.sum_congr rfl fun v hv => ?_
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
    rw [nsmul_eq_mul, ← mul_assoc]
    have : ((Finset.univ.filter (fun j => a j = a i)).card : ENNReal) = mult a (a i) := rfl
    rw [this, ENNReal.mul_inv_cancel (by exact_mod_cast (mult_pos a i).ne')
      (ENNReal.natCast_ne_top _), one_mul]
  · intro v _ w _ hvw
    exact Set.disjoint_iff.2 fun z ⟨h1, h2⟩ => hvw (h1.symm.trans h2)
  · intro v _
    exact measurable_fst (measurableSet_singleton v)

/-- The gluing bound for one coupling. -/
theorem glue_bound (hn : 1 ≤ n) (p : ℝ) (hp : 1 ≤ p) (a b : Fin n → E) (Q : Measure E)
    (π : Measure (E × E))
    (hπ : π.map Prod.fst = empiricalDistribution a ∧ π.map Prod.snd = Q) :
    wassersteinDistance p (empiricalDistribution b) Q ≤
      ENNReal.ofReal (ResidualsDRO.Wass.powerMean p (fun i => ‖b i - a i‖)) +
        (∫⁻ z : E × E, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  set ν := glue a π
  have hgm : Measurable (fun w : Fin n × E => (b w.1, w.2)) :=
    ((measurable_of_finite b).comp measurable_fst).prodMk measurable_snd
  set π' := ν.map (fun w : Fin n × E => (b w.1, w.2))
  have hS : ∀ i, MeasurableSet (Prod.fst ⁻¹' ({a i} : Set E) : Set (E × E)) :=
    fun i => measurable_fst (measurableSet_singleton _)
  -- integral of a function of the index only
  have hidx : ∀ G : Fin n → ENNReal, ∫⁻ w, G w.1 ∂ν = (n : ENNReal)⁻¹ * ∑ i, G i := by
    intro G
    rw [glue_lintegral a π (fun w => G w.1) ((measurable_of_finite G).comp measurable_fst)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only []
    rw [setLIntegral_const, piS a π hπ.1 i]
    have hm : (mult a (a i) : ENNReal) ≠ 0 := by exact_mod_cast (mult_pos a i).ne'
    have hm' : (mult a (a i) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    calc ((mult a (a i) : ENNReal))⁻¹ * (G i * ((n : ENNReal)⁻¹ * mult a (a i)))
        = (n : ENNReal)⁻¹ * G i * (((mult a (a i) : ENNReal))⁻¹ * mult a (a i)) := by ring
      _ = _ := by rw [ENNReal.inv_mul_cancel hm hm', mul_one]
  have hπ' : π'.map Prod.fst = empiricalDistribution b ∧ π'.map Prod.snd = Q := by
    constructor
    · ext T hT
      rw [Measure.map_apply measurable_fst hT, Measure.map_apply hgm (measurable_fst hT),
        emp_apply b T hT, ← lintegral_indicator_one (hgm (measurable_fst hT))]
      have : ∀ w : Fin n × E, ((fun w : Fin n × E => (b w.1, w.2)) ⁻¹' (Prod.fst ⁻¹' T)).indicator
          (1 : Fin n × E → ENNReal) w = (fun i => T.indicator (1 : E → ENNReal) (b i)) w.1 := by
        intro w; rfl
      simp_rw [this]
      exact hidx (fun i => T.indicator 1 (b i))
    · ext T hT
      rw [Measure.map_apply measurable_snd hT, Measure.map_apply hgm (measurable_snd hT),
        ← lintegral_indicator_one (hgm (measurable_snd hT)), ← hπ.2,
        Measure.map_apply measurable_snd hT, ← lintegral_indicator_one (measurable_snd hT)]
      rw [glue_lintegral a π (((fun w : Fin n × E => (b w.1, w.2)) ⁻¹' (Prod.snd ⁻¹' T)).indicator 1)
        ((measurable_indicator_const_iff 1).2 (hgm (measurable_snd hT)))]
      rw [← fiber a π hπ.1]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
  -- the cost bound
  have hW : wassersteinDistance p (empiricalDistribution b) Q ≤
      (∫⁻ z : E × E, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π') ^ (1 / p) := by
    unfold wassersteinDistance
    gcongr
    exact iInf₂_le π' hπ'
  refine hW.trans ?_
  have hcm : Measurable (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ p)) := by
    fun_prop
  rw [lintegral_map hcm hgm]
  have hen : ∀ v : E, ENNReal.ofReal (‖v‖ ^ p) = ‖v‖ₑ ^ p := by
    intro v
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le, ofReal_norm_eq_enorm]
  simp_rw [hen]
  set g1 : Fin n × E → E := fun w => b w.1 - a w.1
  set g2 : Fin n × E → E := fun w => a w.1 - w.2
  have hfg : (fun w : Fin n × E => b w.1 - w.2) = g1 + g2 := by
    funext w; simp [g1, g2]
  have hmeas1 : Measurable g1 :=
    ((measurable_of_finite b).comp measurable_fst).sub ((measurable_of_finite a).comp measurable_fst)
  have hmeas2 : Measurable g2 :=
    ((measurable_of_finite a).comp measurable_fst).sub measurable_snd
  have key := eLpNorm'_add_le (μ := ν) hmeas1.aestronglyMeasurable hmeas2.aestronglyMeasurable hp
  rw [← hfg] at key
  simp only [eLpNorm'_eq_lintegral_enorm] at key
  refine key.trans (add_le_add (le_of_eq ?_) (le_of_eq ?_))
  · -- the first term is the power mean
    rw [hidx (fun i => ‖b i - a i‖ₑ ^ p)]
    unfold ResidualsDRO.Wass.powerMean
    rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    congr 1
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity),
      ENNReal.ofReal_inv_of_pos (by exact_mod_cast hn), ENNReal.ofReal_natCast]
    simp_rw [hen]
  · -- the second term is the cost of `π`
    congr 1
    rw [glue_lintegral a π (fun w => ‖g2 w‖ₑ ^ p) (hmeas2.enorm.pow_const p)]
    rw [← fiber a π hπ.1 (fun z => ‖z.1 - z.2‖ₑ ^ p)]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    refine setLIntegral_congr_fun (hS i) fun z hz => ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
    simp [g2, hz]

/-- The triangle-type bound for discrete measures with matched atoms. -/
theorem wass_bound (hn : 1 ≤ n) (p : ℝ) (hp : 1 ≤ p) (a b : Fin n → E) (Q : Measure E) :
    wassersteinDistance p (empiricalDistribution b) Q ≤
      ENNReal.ofReal (ResidualsDRO.Wass.powerMean p (fun i => ‖b i - a i‖)) +
        wassersteinDistance p (empiricalDistribution a) Q := by
  have hp0 : 0 < 1 / p := by have : 0 < p := by linarith
                             positivity
  have e : ∀ x : ENNReal, x ^ (1 / p) = ENNReal.orderIsoRpow (1 / p) hp0 x := fun x => rfl
  conv_rhs => rw [wassersteinDistance, e]
  simp_rw [OrderIso.map_iInf, ENNReal.orderIsoRpow_apply]
  rw [ENNReal.add_iInf]
  refine le_iInf fun π => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun hπ => ?_
  exact glue_bound hn p hp a b Q π hπ

end RDROL3Aux

open ResidualsDRO.Wass in
theorem solution {dx dy n : ℕ} (hn : 1 ≤ n) (p : ℝ) (hp : 1 ≤ p)
    (𝒴 : Set (EuclideanSpace ℝ (Fin dy)))
    (h𝒴c : IsClosed 𝒴) (h𝒴v : Convex ℝ 𝒴) (h𝒴n : 𝒴.Nonempty)
    (proj : EuclideanSpace ℝ (Fin dy) → EuclideanSpace ℝ (Fin dy))
    (hproj : IsNearestPointProj 𝒴 proj)
    (Pε : Measure (EuclideanSpace ℝ (Fin dy))) [IsProbabilityMeasure Pε]
    (fstar fhat : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin dy))
    (xs : Fin n → EuclideanSpace ℝ (Fin dx)) (eps : Fin n → EuclideanSpace ℝ (Fin dy))
    (x : EuclideanSpace ℝ (Fin dx)) (hY : ∀ i, fstar x + eps i ∈ 𝒴) :
    WassersteinDRO.Duality.wassersteinDistance p (erEmpirical proj fstar fhat xs eps x)
        (condLaw Pε fstar x) ≤
      ENNReal.ofReal (powerMean p (fun i => ‖epsTilde fstar fhat xs eps x i‖)) +
        WassersteinDRO.Duality.wassersteinDistance p (trueEmpirical fstar eps x)
          (condLaw Pε fstar x) := by
  classical
  have h := RDROL3Aux.wass_bound hn p hp (fun i => fstar x + eps i)
    (fun i => proj (fhat x + residual fstar fhat xs eps i)) (condLaw Pε fstar x)
  refine h.trans (add_le_add ?_ le_rfl)
  apply ENNReal.ofReal_le_ofReal
  unfold powerMean
  have hp0 : 0 < p := by linarith
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro i _
  apply Real.rpow_le_rpow (norm_nonneg _) _ hp0.le
  exact (eq_6 𝒴 h𝒴c h𝒴v h𝒴n proj hproj fstar fhat xs eps x hY i).1
