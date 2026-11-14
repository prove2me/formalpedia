-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.coloring_vertex_entropy_increment
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:03:15.371177+00:00
-- url     : https://prove2.me/submissions/1c121f03-8e07-48a3-b388-538beb8c207c

import Theorems.Thm_ZeroFreeRRG_Hardcore_coloring_observation_density
import Theorems.Thm_ZeroFreeRRG_Hardcore_bounded_latent_mixture_entropy
import Theorems.Thm_ZeroFreeRRG_Hardcore_coloring_vertex_density_mixture
import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators
open MeasureTheory Set ZeroFreeRRG.Hardcore

private noncomputable def obs (q : ℕ) (i : Fin q) (x : Fin q → ℝ) : ℝ :=
  (q:ℝ)*(1 - max 0 (min 1 (x i)))/((q:ℝ)-1)

private theorem obs_properties (q : ℕ) (hq : 3 ≤ q) (ν : ProbabilityMeasure (Fin q → ℝ))
    (hν : ν ∈ cavityLaws (.potts q) 0) :
    (∀ i, Continuous (obs q i)) ∧
    (∀ i x, 0 ≤ obs q i x ∧ obs q i x ≤ (q:ℝ)/((q:ℝ)-1)) ∧
    (∀ i, (∫ x, obs q i x ∂(ν : Measure (Fin q → ℝ))) = 1) ∧
    (∀ᵐ x ∂(ν : Measure (Fin q → ℝ)), ∀ i,
      obs q i x = (q:ℝ)*(1-x i)/((q:ℝ)-1)) := by
  have hq' : (3:ℝ) ≤ q := by exact_mod_cast hq
  have hd : 0 < (q:ℝ)-1 := by linarith
  have hq0 : 0 ≤ (q:ℝ) := by positivity
  have hae : ∀ᵐ x ∂(ν : Measure (Fin q → ℝ)), ∀ i,
      obs q i x = (q:ℝ)*(1-x i)/((q:ℝ)-1) := by
    filter_upwards [ae_iff.mpr hν.1] with x hx i
    have hxi := mem_Icc_of_mem_stdSimplex hx i
    dsimp [obs]
    rw [min_eq_right hxi.2, max_eq_right hxi.1]
  refine ⟨?_,?_,?_,hae⟩
  · intro i
    unfold obs
    fun_prop
  · intro i x
    have hc0 : 0 ≤ max 0 (min 1 (x i)) := le_max_left _ _
    have hc1 : max 0 (min 1 (x i)) ≤ 1 := max_le (by norm_num) (min_le_left _ _)
    dsimp [obs]
    constructor
    · exact div_nonneg (mul_nonneg hq0 (by linarith)) hd.le
    · apply (div_le_div_iff₀ hd hd).2
      nlinarith [mul_nonneg hq0 hc0]
  · intro i
    have heq : (∫ x, obs q i x ∂(ν : Measure (Fin q → ℝ))) =
        ∫ x, (q:ℝ)*(1-x i)/((q:ℝ)-1) ∂(ν : Measure (Fin q → ℝ)) := by
      apply integral_congr_ae
      filter_upwards [hae] with x hx
      exact hx i
    rw [heq]
    exact ((coloring_observation_density q hq ν hν).1 i).2.2


private noncomputable def baseweight (q k : ℕ) (xs : Fin k → Fin q → ℝ) (i : Fin q) : ℝ :=
  (q:ℝ)⁻¹ * ∏ j, obs q i (xs j)

private theorem split {X : Type} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (k : ℕ) (f : (Fin (k+1) → X) → ℝ) :
    (∫ xs, f xs ∂(Measure.pi fun _ : Fin (k+1) => μ)) =
    ∫ p : X × (Fin k → X), f (Fin.cons p.1 p.2) ∂(μ.prod (Measure.pi fun _ : Fin k => μ)) := by
  rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (k+1) => μ) 0).symm).integral_comp' f]
  simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Equiv.coe_fn_mk, cast_eq]


private noncomputable def mix (q n : ℕ) (xs : Fin n → Fin q → ℝ) : ℝ :=
  ∑ i : Fin q, baseweight q n xs i

private theorem mix_properties (q n : ℕ) (hq : 3 ≤ q) (ν : ProbabilityMeasure (Fin q → ℝ))
    (hν : ν ∈ cavityLaws (.potts q) 0) :
    Continuous (mix q n) ∧
    (∀ xs, 0 ≤ mix q n xs ∧ mix q n xs ≤ ((q:ℝ)/((q:ℝ)-1))^n) := by
  have hp := obs_properties q hq ν hν
  let C := (q:ℝ)/((q:ℝ)-1)
  have hq' : (3:ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : 0 < (q:ℝ) := by linarith
  have hC : 0 ≤ C := div_nonneg (by positivity) (by linarith)
  constructor
  · unfold mix baseweight
    have hw : ∀ i : Fin q, Continuous (obs q i) := hp.1
    fun_prop
  · intro xs
    have hprod0 (i : Fin q) : 0 ≤ ∏ j, obs q i (xs j) :=
      Finset.prod_nonneg (fun j _ => (hp.2.1 i (xs j)).1)
    have hprodC (i : Fin q) : (∏ j, obs q i (xs j)) ≤ C^n := by
      calc
        _ ≤ ∏ _j : Fin n, C := Finset.prod_le_prod
          (fun j _ => (hp.2.1 i (xs j)).1) (fun j _ => (hp.2.1 i (xs j)).2)
        _ = _ := by simp
    have hterm (i : Fin q) : baseweight q n xs i ≤ (q:ℝ)⁻¹ * C^n := by
      dsimp [baseweight]
      exact mul_le_mul_of_nonneg_left (hprodC i) (le_of_lt (inv_pos.mpr hqpos))
    constructor
    · dsimp [mix,baseweight]
      exact Finset.sum_nonneg (fun i _ => mul_nonneg (le_of_lt (inv_pos.mpr hqpos)) (hprod0 i))
    · dsimp [mix]
      calc
        _ ≤ ∑ _i : Fin q, (q:ℝ)⁻¹*C^n := Finset.sum_le_sum (fun i _ => hterm i)
        _ = C^n := by simp [ne_of_gt hqpos]

private theorem mix_entropy_integrable (q n : ℕ) (hq : 3 ≤ q)
    (ν : ProbabilityMeasure (Fin q → ℝ)) (hν : ν ∈ cavityLaws (.potts q) 0) :
    Integrable (fun xs => mix q n xs * Real.log (mix q n xs))
      (Measure.pi fun _ : Fin n => (ν : Measure (Fin q → ℝ))) := by
  have hp := mix_properties q n hq ν hν
  let C := ((q:ℝ)/((q:ℝ)-1))^n
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) C)).exists_bound_of_continuousOn
    Real.continuous_mul_log.continuousOn
  apply Integrable.of_bound (Real.continuous_mul_log.comp hp.1).aestronglyMeasurable B
  filter_upwards with xs
  exact hB _ ⟨(hp.2 xs).1, (hp.2 xs).2⟩

private theorem mix_cons (q n : ℕ) (x : Fin q → ℝ) (xs : Fin n → Fin q → ℝ) :
    mix q (n+1) (Fin.cons x xs) = ∑ i : Fin q, baseweight q n xs i * obs q i x := by
  dsimp [mix,baseweight]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ]
  ring

private theorem mix_cons_cons (q n : ℕ) (x y : Fin q → ℝ) (xs : Fin n → Fin q → ℝ) :
    mix q (n+2) (Fin.cons x (Fin.cons y xs)) =
      ∑ i : Fin q, baseweight q n xs i * obs q i x * obs q i y := by
  dsimp [mix,baseweight]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Fin.prod_univ_succ,Fin.prod_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ]
  ring

private theorem split_integrable {X : Type} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (k : ℕ) (f : (Fin (k+1) → X) → ℝ)
    (hf : Integrable f (Measure.pi fun _ : Fin (k+1) => μ)) :
    Integrable (fun p : X × (Fin k → X) => f (Fin.cons p.1 p.2))
      (μ.prod (Measure.pi fun _ : Fin k => μ)) := by
  have hh := (((measurePreserving_piFinSuccAbove (fun _ : Fin (k+1) => μ) 0).symm).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)).2 hf
  simp_rw [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Equiv.coe_fn_mk, cast_eq] at hh
  exact hh

private theorem split2 {X : Type} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (k : ℕ) :
    MeasurePreserving (fun p : (Fin k → X) × (X × X) => Fin.cons p.2.1 (Fin.cons p.2.2 p.1))
      ((Measure.pi fun _ : Fin k => μ).prod (μ.prod μ)) (Measure.pi fun _ : Fin (k+2) => μ) := by
  let πk : Measure (Fin k → X) := Measure.pi fun _ => μ
  let πk1 : Measure (Fin (k+1) → X) := Measure.pi fun _ => μ
  let πk2 : Measure (Fin (k+2) → X) := Measure.pi fun _ => μ
  have h1 : MeasurePreserving (fun p : (Fin k → X) × (X × X) => (p.2,p.1))
      (πk.prod (μ.prod μ)) ((μ.prod μ).prod πk) := Measure.measurePreserving_swap
  have h2 : MeasurePreserving (fun p : (X × X) × (Fin k → X) => (p.1.1,(p.1.2,p.2)))
      ((μ.prod μ).prod πk) (μ.prod (μ.prod πk)) := measurePreserving_prodAssoc μ μ πk
  have hs1 : MeasurePreserving (fun p : X × (Fin k → X) => Fin.cons p.1 p.2)
      (μ.prod πk) πk1 := by
    have hh := (measurePreserving_piFinSuccAbove (fun _ : Fin (k+1) => μ) 0).symm
    simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero, Equiv.coe_fn_mk, cast_eq] at hh
    exact hh
  have hs2 : MeasurePreserving (fun p : X × (Fin (k+1) → X) => Fin.cons p.1 p.2)
      (μ.prod πk1) πk2 := by
    have hh := (measurePreserving_piFinSuccAbove (fun _ : Fin (k+2) => μ) 0).symm
    simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero, Equiv.coe_fn_mk, cast_eq] at hh
    exact hh
  have h3 : MeasurePreserving (fun p : X × (X × (Fin k → X)) => (p.1,Fin.cons p.2.1 p.2.2))
      (μ.prod (μ.prod πk)) (μ.prod πk1) := by
    convert (MeasurePreserving.id μ).prod hs1 using 1
    funext p
    rfl
  exact hs2.comp (h3.comp (h2.comp h1))

private theorem split2_emb {X : Type} [MeasurableSpace X] (k : ℕ) :
    MeasurableEmbedding (fun p : (Fin k → X) × (X × X) => (Fin.cons p.2.1 (Fin.cons p.2.2 p.1) : Fin (k+2) → X)) := by
  let e1 : ((Fin k → X) × (X × X)) ≃ᵐ ((X × X) × (Fin k → X)) := MeasurableEquiv.prodComm
  let e2 : ((X × X) × (Fin k → X)) ≃ᵐ (X × (X × (Fin k → X))) := MeasurableEquiv.prodAssoc
  let e3 : (X × (X × (Fin k → X))) ≃ᵐ (X × (Fin (k+1) → X)) :=
    (MeasurableEquiv.refl X).prodCongr (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => X) 0).symm
  let e4 : (X × (Fin (k+1) → X)) ≃ᵐ (Fin (k+2) → X) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+2) => X) 0).symm
  let e := ((e1.trans e2).trans e3).trans e4
  have he : (⇑e) = (fun p : (Fin k → X) × (X × X) => Fin.cons p.2.1 (Fin.cons p.2.2 p.1)) := by
    funext p
    simp [e,e1,e2,e3,e4, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero, cast_eq, MeasurableEquiv.prodCongr, MeasurableEquiv.prodAssoc, MeasurableEquiv.prodComm]
  rw [← he]
  exact e.measurableEmbedding


private theorem entropy_mix_eq (q n : ℕ) (hq : 3 ≤ q)
    (ν : ProbabilityMeasure (Fin q → ℝ)) (hν : ν ∈ cavityLaws (.potts q) 0) :
    (∫ xs, xlogx (vertexFactor (.potts q) 0 n xs)
      ∂(Measure.pi fun _ : Fin n => (ν : Measure (Fin q → ℝ)))) =
    ∫ xs, mix q n xs * Real.log (mix q n xs)
      ∂(Measure.pi fun _ : Fin n => (ν : Measure (Fin q → ℝ))) := by
  have hs : ∀ᵐ x ∂(ν : Measure (Fin q → ℝ)), x ∈ stdSimplex ℝ (Fin q) := ae_iff.mpr hν.1
  have hp := obs_properties q hq ν hν
  have ha : ∀ᵐ xs ∂(Measure.pi fun _ : Fin n => (ν : Measure (Fin q → ℝ))),
      ∀ j, xs j ∈ stdSimplex ℝ (Fin q) ∧
        ∀ i, obs q i (xs j) = (q:ℝ)*(1-(xs j) i)/((q:ℝ)-1) := by
    have hgood : ∀ᵐ x ∂(ν : Measure (Fin q → ℝ)), x ∈ stdSimplex ℝ (Fin q) ∧
        ∀ i, obs q i x = (q:ℝ)*(1-x i)/((q:ℝ)-1) := by
      filter_upwards [hs,hp.2.2.2] with x hx hobs
      exact ⟨hx,hobs⟩
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi (fun _ : Fin n => hgood)
  apply integral_congr_ae
  filter_upwards [ha] with xs hx
  have heq : vertexFactor (.potts q) 0 n xs = mix q n xs := by
    rw [coloring_vertex_density_mixture q n hq xs (fun j => (hx j).1.2)]
    dsimp [mix,baseweight]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    exact ((hx j).2 i).symm
  simp [xlogx,heq]

/-- Pointwise conditional entropy step after fixing the first k observations. -/
private theorem conditional_entropy (q k : ℕ) (hq : 3 ≤ q) (ν : ProbabilityMeasure (Fin q → ℝ))
    (hν : ν ∈ cavityLaws (.potts q) 0) (xs : Fin k → Fin q → ℝ) :
    let A := baseweight q k xs
    let L := fun x => ∑ i : Fin q, A i * obs q i x
    let T := fun p : (Fin q → ℝ) × (Fin q → ℝ) => ∑ i : Fin q, A i*obs q i p.1*obs q i p.2
    2*(∫ x, L x*Real.log (L x) ∂(ν : Measure (Fin q → ℝ))) ≤
      (∫ p, T p*Real.log (T p) ∂((ν : Measure (Fin q → ℝ)).prod (ν : Measure (Fin q → ℝ)))) +
      (∑ i, A i)*Real.log (∑ i, A i) := by
  classical
  dsimp only
  let A := baseweight q k xs
  have hp := obs_properties q hq ν hν
  have hq' : (3:ℝ) ≤ q := by exact_mod_cast hq
  have hqn : 0 ≤ (q:ℝ)⁻¹ := by positivity
  have hA (i : Fin q) : 0 ≤ A i := by
    dsimp [A,baseweight]
    exact mul_nonneg hqn (Finset.prod_nonneg (fun j _ => (hp.2.1 i (xs j)).1))
  have hS : 0 ≤ ∑ i, A i := Finset.sum_nonneg (fun i _ => hA i)
  by_cases hz : (∑ i, A i) = 0
  · have ha0 : ∀ i, A i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hA i)).mp hz i (Finset.mem_univ i)
    have ha0' : ∀ i, baseweight q k xs i = 0 := ha0
    simp [ha0']
  · have hspos : 0 < ∑ i, A i := lt_of_le_of_ne hS (Ne.symm hz)
    have hC : 0 ≤ (q:ℝ)/((q:ℝ)-1) := div_nonneg (by positivity) (by linarith)
    exact bounded_latent_mixture_entropy (ν : Measure (Fin q → ℝ)) A (obs q)
      ((q:ℝ)/((q:ℝ)-1)) hA hspos hC hp.2.1 (fun i => (hp.1 i).measurable) hp.2.2.1


theorem solution (q : ℕ) (hq : 3 ≤ q)
    (ν : ProbabilityMeasure ((.potts q : Model).Spin → ℝ)) (hν : ν ∈ cavityLaws (.potts q) 0)
    (k : ℕ) :
    let A := fun n : ℕ => ∫ xs, xlogx (vertexFactor (.potts q) 0 n xs)
      ∂(Measure.pi fun _ : Fin n => (ν : Measure ((.potts q : Model).Spin → ℝ)))
    A (k+1)-A k ≤ A (k+2)-A (k+1) := by
  classical
  change ProbabilityMeasure (Fin q → ℝ) at ν
  let μ : Measure (Fin q → ℝ) := ν
  let πk : Measure (Fin k → Fin q → ℝ) := Measure.pi fun _ => μ
  let F0 : (Fin k → Fin q → ℝ) → ℝ := fun xs => mix q k xs * Real.log (mix q k xs)
  let F1 : (Fin k → Fin q → ℝ) × (Fin q → ℝ) → ℝ := fun p =>
    mix q (k+1) (Fin.cons p.2 p.1)*Real.log (mix q (k+1) (Fin.cons p.2 p.1))
  let F2 : (Fin k → Fin q → ℝ) × ((Fin q → ℝ) × (Fin q → ℝ)) → ℝ := fun p =>
    mix q (k+2) (Fin.cons p.2.1 (Fin.cons p.2.2 p.1))*Real.log (mix q (k+2) (Fin.cons p.2.1 (Fin.cons p.2.2 p.1)))
  have hF0 : Integrable F0 πk := mix_entropy_integrable q k hq ν hν
  have hF1 : Integrable F1 (πk.prod μ) := by
    have hh := (split_integrable μ k _ (mix_entropy_integrable q (k+1) hq ν hν)).swap
    exact hh
  have hF2 : Integrable F2 (πk.prod (μ.prod μ)) := by
    have hh := ((split2 μ k).integrable_comp_emb (split2_emb k)).2 (mix_entropy_integrable q (k+2) hq ν hν)
    exact hh
  have hpoint (xs : Fin k → Fin q → ℝ) :
      2*(∫ x, F1 (xs,x) ∂μ) ≤ (∫ p, F2 (xs,p) ∂(μ.prod μ)) + F0 xs := by
    have hh := conditional_entropy q k hq ν hν xs
    dsimp only at hh
    dsimp [F0,F1,F2]
    simp only [mix_cons_cons]
    simp only [mix_cons]
    simpa only [mix] using hh
  have hI := integral_mono ((hF1.integral_prod_left).const_mul 2) (hF2.integral_prod_left.add hF0) hpoint
  have hI' : 2*(∫ xs, ∫ x, F1 (xs,x) ∂μ ∂πk) ≤
      (∫ xs, ∫ p, F2 (xs,p) ∂(μ.prod μ) ∂πk) + ∫ xs, F0 xs ∂πk := by
    have hh := integral_add hF2.integral_prod_left hF0
    simp only [Pi.add_apply] at hI
    rw [integral_const_mul,hh] at hI
    exact hI
  have h1eq : (∫ xs, ∫ x, F1 (xs,x) ∂μ ∂πk) =
      ∫ ys, mix q (k+1) ys * Real.log (mix q (k+1) ys)
        ∂(Measure.pi fun _ : Fin (k+1) => μ) := by
    rw [← integral_prod _ hF1]
    rw [split μ k (fun ys => mix q (k+1) ys * Real.log (mix q (k+1) ys))]
    change (∫ p, F1 p ∂(πk.prod μ)) = ∫ p, F1 p.swap ∂(μ.prod πk)
    exact (integral_prod_swap F1).symm
  have h2eq : (∫ xs, ∫ p, F2 (xs,p) ∂(μ.prod μ) ∂πk) =
      ∫ ys, mix q (k+2) ys * Real.log (mix q (k+2) ys)
        ∂(Measure.pi fun _ : Fin (k+2) => μ) := by
    rw [← integral_prod _ hF2]
    change (∫ p, mix q (k+2) (Fin.cons p.2.1 (Fin.cons p.2.2 p.1)) *
      Real.log (mix q (k+2) (Fin.cons p.2.1 (Fin.cons p.2.2 p.1))) ∂(πk.prod (μ.prod μ))) = _
    exact (split2 μ k).integral_comp (split2_emb k) (fun ys => mix q (k+2) ys * Real.log (mix q (k+2) ys))
  rw [h1eq,h2eq] at hI'
  dsimp only
  change (∫ xs : Fin (k+1) → Fin q → ℝ, xlogx (vertexFactor (.potts q) 0 (k+1) xs) ∂(Measure.pi fun _ : Fin (k+1) => μ)) -
    (∫ xs : Fin k → Fin q → ℝ, xlogx (vertexFactor (.potts q) 0 k xs) ∂(Measure.pi fun _ : Fin k => μ)) ≤
    (∫ xs : Fin (k+2) → Fin q → ℝ, xlogx (vertexFactor (.potts q) 0 (k+2) xs) ∂(Measure.pi fun _ : Fin (k+2) => μ)) -
    (∫ xs : Fin (k+1) → Fin q → ℝ, xlogx (vertexFactor (.potts q) 0 (k+1) xs) ∂(Measure.pi fun _ : Fin (k+1) => μ))
  rw [entropy_mix_eq q (k+1) hq ν hν, entropy_mix_eq q k hq ν hν,
    entropy_mix_eq q (k+2) hq ν hν]
  change _ ≤ _
  dsimp [F0] at hI'
  linarith
