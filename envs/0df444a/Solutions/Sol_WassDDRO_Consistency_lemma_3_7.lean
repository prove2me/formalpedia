-- Prove2me | solution 1 for WassDDRO.Consistency.lemma_3_7
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T12:31:10.815686+00:00
-- url     : https://prove2.me/submissions/5d2d0e57-8074-4418-b0f6-a5397fe29289

import Definitions.Def_WassDDRO_Consistency_Setting
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Mathlib
set_option autoImplicit false
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
open MeasureTheory WassersteinDRO.Duality
namespace WassConsistencyCodex
/-- Reuses the checked empirical-law calculation from the completed Codex reduction lane. -/
theorem empirical_probability {E : Type*} [MeasurableSpace E] {N : ℕ}
    (hN : 0 < N) (ξhat : Fin N → E) : IsProbabilityMeasure (empiricalDistribution ξhat) := by
  constructor
  simp [empiricalDistribution,Measure.smul_apply,Measure.finsetSum_apply]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (ENNReal.natCast_ne_top N)
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
    (Qhat : ℕ → (ℕ → E) → Measure E)
    (hQ : ∀ N (ω : ℕ → E), 1 ≤ N → (∀ i, ω i ∈ Ξ) →
      Qhat N ω ∈ WassersteinDRO.Duality.ambiguitySet
        (radius c₁ c₂ a (Module.finrank ℝ E) N (β N)) 1 Ξ
        (WassersteinDRO.Duality.empiricalDistribution (fun i : Fin N => ω i))) :
    ∀ᵐ ω ∂(P_inf P),
      Tendsto (fun N => WassersteinDRO.Duality.wassersteinDistance 1 P (Qhat N ω)) atTop (𝓝 0) := by
  have hr : Tendsto (fun N => ENNReal.ofReal (radius c₁ c₂ a (Module.finrank ℝ E) N (β N))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero,Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hlim
  have hrs : Tendsto (fun N => ENNReal.ofReal (radius c₁ c₂ a (Module.finrank ℝ E) N (β N)) +
      ENNReal.ofReal (radius c₁ c₂ a (Module.finrank ℝ E) N (β N))) atTop (𝓝 0) := by
    simpa only [add_zero] using hr.add hr
  filter_upwards [WassConsistencyCodex.true_distance_eventually_le_radius P a c₁ c₂
      (by linarith) hc₁ hc₂ h7 β (fun N => (hβ N).1) hsum,
    WassConsistencyCodex.infinite_samples_mem_support_ae P Ξ hP] with ω hdist hω
  have hbound : ∀ᶠ N in atTop, WassersteinDRO.Duality.wassersteinDistance 1 P (Qhat N ω) ≤
      ENNReal.ofReal (radius c₁ c₂ a (Module.finrank ℝ E) N (β N)) +
      ENNReal.ofReal (radius c₁ c₂ a (Module.finrank ℝ E) N (β N)) := by
    filter_upwards [hdist,eventually_ge_atTop 1] with N hd hN
    let PN := WassersteinDRO.Duality.empiricalDistribution (fun i : Fin N => ω i)
    haveI : IsProbabilityMeasure PN := WassConsistencyCodex.empirical_probability (by omega) _
    have hsel := hQ N ω hN hω
    have htri := WassConsistencyCodex.wassersteinDistance_triangle P PN (Qhat N ω)
    rw [WassConsistencyCodex.wassersteinDistance_symm 1 PN (Qhat N ω)] at htri
    exact htri.trans (add_le_add hd hsel.2.2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrs
    (Eventually.of_forall (fun N => bot_le)) hbound


#print axioms solution
