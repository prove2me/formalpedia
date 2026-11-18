-- Prove2me | solution 1 for PrivateAgnosticHalfspace.Gaussian.proposition_C_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T20:56:34.476892+00:00
-- url     : https://prove2.me/submissions/8c690da7-a8b0-4249-bdd3-11125ebd0e89

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Regression
import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_B_3
import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_B_5
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option maxHeartbeats 400000
attribute [local instance] Classical.propDecidable
namespace PrivateAgnosticHalfspace.Gaussian

lemma continuous_hermite (d : ℕ) (κ : Fin d → ℕ) : Continuous (hermite d κ) := by
  unfold hermite AMPLowDeg.RankOne.hermNorm
  fun_prop

lemma continuous_features (d p : ℕ) : Continuous (features d p) := by
  unfold features
  apply Continuous.comp (PiLp.continuous_toLp 2 (fun _ : Index d p => ℝ))
  apply continuous_pi
  intro κ
  exact continuous_hermite d (fun i => (κ.val i).val)

lemma radius_pos (d p : ℕ) : 0 < radius d p := by
  unfold radius
  have hD : 0 < featureDimension d p := Nat.choose_pos (by omega)
  have hD' : (0 : ℝ) < featureDimension d p := by exact_mod_cast hD
  positivity

lemma continuous_clipped (d p : ℕ) : Continuous (clipped d p) := by
  unfold clipped clipScale
  have hs : Continuous (fun x : Vec d => radius d p / max (radius d p) ‖features d p x‖) := by
    apply continuous_const.div (continuous_const.max (continuous_features d p).norm)
    intro x
    exact (lt_of_lt_of_le (radius_pos d p) (le_max_left _ _)).ne'
  exact continuous_smul.comp (hs.prodMk (continuous_features d p))

lemma measurable_sign : Measurable (PrivateAgnosticHalfspace.Gaussian.sign : ℝ → Bool) := by
  apply measurable_to_bool
  have heq : PrivateAgnosticHalfspace.Gaussian.sign ⁻¹' {true} = Set.Ici (0 : ℝ) := by
    ext x
    simp [PrivateAgnosticHalfspace.Gaussian.sign]
  rw [heq]
  exact measurableSet_Ici

lemma measurable_candidate (d p M : ℕ) (v : Coeff d p) (l : Fin M) :
    Measurable (candidate d p M v l) := by
  unfold candidate score
  apply measurable_sign.comp
  exact ((continuous_const.inner (continuous_clipped d p)).sub continuous_const).measurable

lemma measurable_candidate_joint (d p M : ℕ) (l : Fin M) :
    Measurable (fun vx : Coeff d p × Vec d => candidate d p M vx.1 l vx.2) := by
  unfold candidate score
  apply measurable_sign.comp
  exact ((continuous_fst.inner ((continuous_clipped d p).comp continuous_snd)).sub continuous_const).measurable

lemma measurable_pi_measure {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {Y : ι → Type*} [∀ i, MeasurableSpace (Y i)]
    (κ : ∀ i, Ω → Measure (Y i)) (hκ : ∀ i, Measurable (κ i))
    (hp : ∀ i ω, IsProbabilityMeasure (κ i ω)) :
    Measurable (fun ω => Measure.pi (fun i => κ i ω)) := by
  letI (i : ι) (ω : Ω) := hp i ω
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (S := Set.univ.pi '' Set.univ.pi (fun i : ι => {s : Set (Y i) | MeasurableSet s}))
  · exact generateFrom_pi.symm
  · exact isPiSystem_pi
  · intro s hs
    rcases hs with ⟨t,ht,rfl⟩
    have ht' : ∀ i, MeasurableSet (t i) := fun i => ht i (Set.mem_univ _)
    simp_rw [Measure.pi_pi]
    exact Finset.measurable_prod _ (fun i _ => (Measure.measurable_coe (ht' i)).comp (hκ i))
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def selectionLaw (d p k M m : ℕ) (ε : ℝ)
    (v : Fin k → UnitBall d p) (V : Fin m → Example d) : Measure (Output d p M) :=
  let w := fun jl : Fin k × Fin M =>
    Real.exp (-ε * m * empiricalError V (candidate d p M (v jl.1).val jl.2) / 2)
  ∑ jl : Fin k × Fin M,
    ENNReal.ofReal (w jl / ∑ il : Fin k × Fin M, w il) • Measure.dirac (v jl.1, jl.2)

lemma selectionLaw_probability (d p k M m : ℕ) (hk : 0 < k) (hM : 0 < M)
    (ε : ℝ) (v : Fin k → UnitBall d p) (V : Fin m → Example d) :
    IsProbabilityMeasure (selectionLaw d p k M m ε v V) := by
  classical
  have hne : (Finset.univ : Finset (Fin k × Fin M)).Nonempty :=
    ⟨(⟨0,hk⟩,⟨0,hM⟩), Finset.mem_univ _⟩
  have hw : 0 < ∑ jl : Fin k × Fin M,
      Real.exp (-ε * m * empiricalError V (candidate d p M (v jl.1).val jl.2) / 2) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) hne
  constructor
  simp only [selectionLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity), ← Finset.sum_div]
  rw [div_self hw.ne']
  norm_num

lemma measurable_measure_smul {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (f : Ω → ℝ≥0∞) (κ : Ω → Measure Y) (hf : Measurable f) (hκ : Measurable κ) :
    Measurable (fun ω => f ω • κ ω) := by
  apply Measure.measurable_of_measurable_coe
  intro U hU
  simp only [Measure.smul_apply, smul_eq_mul]
  exact hf.mul ((Measure.measurable_coe hU).comp hκ)

lemma measurable_selectionLaw (d p k M m : ℕ) (ε : ℝ) :
    Measurable (fun z : (Fin k → UnitBall d p) × (Fin m → Example d) =>
      selectionLaw d p k M m ε z.1 z.2) := by
  classical
  have hscore (j : Fin k) (l : Fin M) (i : Fin m) :
      Measurable (fun z : (Fin k → UnitBall d p) × (Fin m → Example d) =>
        candidate d p M (z.1 j).val l (z.2 i).1) := by
    have hv : Measurable (fun z : (Fin k → UnitBall d p) × (Fin m → Example d) =>
        (z.1 j).val) :=
      measurable_subtype_coe.comp ((measurable_pi_apply j).comp measurable_fst)
    have hx : Measurable (fun z : (Fin k → UnitBall d p) × (Fin m → Example d) =>
        (z.2 i).1) :=
      measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd)
    unfold candidate score
    exact measurable_sign.comp ((hv.inner ((continuous_clipped d p).measurable.comp hx)).sub_const _)

  have her (jl : Fin k × Fin M) :
      Measurable (fun z : (Fin k → UnitBall d p) × (Fin m → Example d) =>
        empiricalError z.2 (candidate d p M (z.1 jl.1).val jl.2)) := by
    unfold empiricalError
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro i _
    apply Measurable.ite _ measurable_const measurable_const
    exact measurableSet_eq_fun (hscore jl.1 jl.2 i)
      (measurable_snd.comp ((measurable_pi_apply i).comp measurable_snd))
  have hw (jl : Fin k × Fin M) :
      Measurable (fun z : (Fin k → UnitBall d p) × (Fin m → Example d) =>
        Real.exp (-ε * m * empiricalError z.2 (candidate d p M (z.1 jl.1).val jl.2) / 2)) :=
    (((her jl).const_mul (-ε * m)).div_const 2).exp
  unfold selectionLaw
  apply Finset.measurable_sum
  intro jl _
  apply measurable_measure_smul
  · exact ((hw jl).div (Finset.measurable_sum _ (fun il _ => hw il))).ennreal_ofReal
  · apply Measure.measurable_dirac.comp
    exact ((measurable_pi_apply jl.1).comp measurable_fst).prodMk measurable_const

lemma measurable_prod_measures {Ω Y Z : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Y] [MeasurableSpace Z]
    (κ : Ω → Measure Y) (η : Ω → Measure Z) (hκ : Measurable κ) (hη : Measurable η)
    (hκp : ∀ ω, IsProbabilityMeasure (κ ω)) (hηp : ∀ ω, IsProbabilityMeasure (η ω)) :
    Measurable (fun ω => (κ ω).prod (η ω)) := by
  letI (ω : Ω) := hκp ω
  letI (ω : Ω) := hηp ω
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_prod.symm isPiSystem_prod
  intro U hU
  rcases hU with ⟨V,hV,W,hW,rfl⟩
  simp_rw [Measure.prod_prod]
  exact ((Measure.measurable_coe hV).comp hκ).mul ((Measure.measurable_coe hW).comp hη)

lemma bind_map_eq {Ω Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure Ω) (f : Ω → Y) (hf : Measurable f) (κ : Y → Measure Z)
    (hκ : Measurable κ) : (μ.map f).bind κ = μ.bind (κ ∘ f) := by
  ext U hU
  rw [Measure.bind_apply hU hκ.aemeasurable, Measure.bind_apply hU (hκ.comp hf).aemeasurable]
  simpa only [Function.comp_apply] using lintegral_map ((Measure.measurable_coe hU).comp hκ) hf
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def trainingBlocks (d k n₀ m : ℕ)
    (S : Fin (k * n₀ + m) → Example d) : Fin k → Fin n₀ → Example d := fun j i =>
  S ⟨j.val * n₀ + i.val, by
    have hj := Nat.mul_le_mul_right n₀ (Nat.succ_le_of_lt j.isLt)
    have hi := i.isLt
    nlinarith⟩
noncomputable def validationBlock (d k n₀ m : ℕ)
    (S : Fin (k * n₀ + m) → Example d) : Fin m → Example d := fun i =>
  S ⟨k * n₀ + i.val, by omega⟩

lemma algorithmLaw_eq (O : Optimizer) (d p k M n₀ m : ℕ) (ε δ : ℝ)
    (S : Fin (k * n₀ + m) → Example d) :
    algorithmLaw O d p k M n₀ m ε δ S =
      (Measure.pi (fun j : Fin k => (O d p n₀ ε δ (trainingBlocks d k n₀ m S j) : Measure (UnitBall d p)))).bind
        (fun v => selectionLaw d p k M m ε v (validationBlock d k n₀ m S)) := rfl

lemma algorithmLaw_probability (O : Optimizer) (d p k M n₀ m : ℕ)
    (hk : 0 < k) (hM : 0 < M) (ε δ : ℝ) (S : Fin (k * n₀ + m) → Example d) :
    IsProbabilityMeasure (algorithmLaw O d p k M n₀ m ε δ S) := by
  rw [algorithmLaw_eq]
  exact isProbabilityMeasure_bind
    ((measurable_selectionLaw d p k M m ε).comp (measurable_id.prodMk measurable_const)).aemeasurable
    (ae_of_all _ (fun v => selectionLaw_probability d p k M m hk hM ε v _))

lemma measurable_algorithmLaw (O : Optimizer) (d p k M n₀ m : ℕ) (ε δ : ℝ)
    (hOmeas : Measurable (fun S => (O d p n₀ ε δ S : Measure (UnitBall d p)))) :
    Measurable (fun S => algorithmLaw O d p k M n₀ m ε δ S) := by
  let train := fun S : Fin (k * n₀ + m) → Example d =>
    Measure.pi (fun j : Fin k => (O d p n₀ ε δ (trainingBlocks d k n₀ m S j) : Measure (UnitBall d p)))
  have htrain : Measurable train := by
    apply measurable_pi_measure _ _ (fun _ _ => by infer_instance)
    intro j
    apply hOmeas.comp
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply _
  have hv : Measurable (validationBlock d k n₀ m) := by
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply _
  have hpair : Measurable (fun S => (train S).prod (Measure.dirac (validationBlock d k n₀ m S))) :=
    measurable_prod_measures _ _ htrain (Measure.measurable_dirac.comp hv)
      (fun _ => by infer_instance) (fun _ => by infer_instance)
  have hfull := (Measure.measurable_bind' (measurable_selectionLaw d p k M m ε)).comp hpair
  have heq (S : Fin (k * n₀ + m) → Example d) :
      ((train S).prod (Measure.dirac (validationBlock d k n₀ m S))).bind
        (fun z => selectionLaw d p k M m ε z.1 z.2) = algorithmLaw O d p k M n₀ m ε δ S := by
    rw [Measure.prod_dirac]
    have hmap := bind_map_eq (train S)
      (fun x : Fin k → UnitBall d p => (x, validationBlock d k n₀ m S))
      (measurable_id.prodMk measurable_const)
      (fun z => selectionLaw d p k M m ε z.1 z.2) (measurable_selectionLaw d p k M m ε)
    exact hmap.trans (algorithmLaw_eq O d p k M n₀ m ε δ S).symm
  change Measurable (fun S => ((train S).prod (Measure.dirac (validationBlock d k n₀ m S))).bind
    (fun z => selectionLaw d p k M m ε z.1 z.2)) at hfull
  simpa only [heq] using hfull
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
lemma dp_prod_right {X Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (n : ℕ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 ≤ δ ∧ δ < 1)
    (M : PrivateUniformGen.Characterization.Mechanism X Y n)
    (hM : PrivateUniformGen.Characterization.IsDP M ε δ)
    (ρ : Measure Z) [IsProbabilityMeasure ρ] :
    ∃ N : PrivateUniformGen.Characterization.Mechanism X (Y × Z) n,
      (∀ S, (N S : Measure (Y × Z)) = (M S : Measure Y).prod ρ) ∧
      PrivateUniformGen.Characterization.IsDP N ε δ := by
  let f : Kernel Y (Y × Z) := Kernel.id ×ₖ Kernel.const Y ρ
  obtain ⟨N,hN,hDP⟩ := lemma_B_3 n ε δ hε hδ M hM f
  refine ⟨N, ?_, hDP⟩
  intro S
  rw [hN S]
  exact (Measure.compProd_eq_comp_prod (M S : Measure Y) (Kernel.const Y ρ)).symm.trans
    Measure.compProd_const
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
lemma private_product_one_coordinate {X Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (k n : ℕ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 ≤ δ ∧ δ < 1)
    (F : Fin (k + 1) → PrivateUniformGen.Characterization.Mechanism X Y n)
    (hF : ∀ j, PrivateUniformGen.Characterization.IsDP (F j) ε δ)
    (B B' : Fin (k + 1) → Fin n → X) (i : Fin (k + 1))
    (hi : PrivateUniformGen.Characterization.Neighbors (B i) (B' i))
    (hother : ∀ j, j ≠ i → B j = B' j)
    (H : Kernel (Fin (k + 1) → Y) Z) [IsMarkovKernel H]
    (U : Set Z) (hU : MeasurableSet U) :
    ((Measure.pi (fun j => (F j (B j) : Measure Y))).bind H).real U ≤
      Real.exp ε * ((Measure.pi (fun j => (F j (B' j) : Measure Y))).bind H).real U + δ := by
  let ρ := Measure.pi (fun j : Fin k => (F (i.succAbove j) (B (i.succAbove j)) : Measure Y))
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => Y) i
  obtain ⟨N,hN,hNdp⟩ := dp_prod_right n ε δ hε hδ (F i) (hF i) ρ
  let K : Kernel (Y × (Fin k → Y)) Z := Kernel.comap H e.symm e.symm.measurable
  obtain ⟨A,hA,hAdp⟩ := lemma_B_3 n ε δ hε hδ N hNdp K
  have hrest : (fun j : Fin k => (F (i.succAbove j) (B' (i.succAbove j)) : Measure Y)) =
      (fun j : Fin k => (F (i.succAbove j) (B (i.succAbove j)) : Measure Y)) := by
    funext j
    rw [hother (i.succAbove j) (Fin.succAbove_ne i j)]
  have hlaw (D : Fin (k + 1) → Fin n → X)
      (hr : (fun j : Fin k => (F (i.succAbove j) (D (i.succAbove j)) : Measure Y)) =
        (fun j : Fin k => (F (i.succAbove j) (B (i.succAbove j)) : Measure Y))) :
      (A (D i) : Measure Z) = (Measure.pi (fun j => (F j (D j) : Measure Y))).bind H := by
    rw [hA (D i), hN (D i)]
    have he := (measurePreserving_piFinSuccAbove (fun j => (F j (D j) : Measure Y)) i).symm
    have hmap : ((F i (D i) : Measure Y).prod ρ).map e.symm =
        Measure.pi (fun j => (F j (D j) : Measure Y)) := by
      simpa only [hr] using he.map_eq
    have hm := bind_map_eq ((F i (D i) : Measure Y).prod ρ) e.symm e.symm.measurable H H.measurable
    rw [hmap] at hm
    exact hm.symm
  have hh := hAdp (B i) (B' i) hi U hU
  rw [hlaw B rfl, hlaw B' hrest] at hh
  exact hh
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
lemma selectionLaw_reindex (d p k M m : ℕ) (ε : ℝ)
    (v : Fin k → UnitBall d p) (V : Fin m → Example d) :
    let e : Fin (k * M) ≃ Fin k × Fin M := finProdFinEquiv.symm
    (validationLaw (fun j => candidate d p M (v (e j).1).val (e j).2) ε V).map
      (fun j => (v (e j).1, (e j).2)) = selectionLaw d p k M m ε v V := by
  classical
  let e : Fin (k * M) ≃ Fin k × Fin M := finProdFinEquiv.symm
  let out := fun j : Fin (k * M) => (v (e j).1, (e j).2)
  have hout : Measurable out := measurable_of_countable _
  let w := fun jl : Fin k × Fin M => Real.exp (-ε * m * empiricalError V
    (candidate d p M (v jl.1).val jl.2) / 2)
  have hden : ∑ j : Fin (k * M), w (e j) = ∑ jl : Fin k × Fin M, w jl := e.sum_comp w
  change (∑ j : Fin (k * M), ENNReal.ofReal (w (e j) / ∑ i, w (e i)) •
    Measure.dirac j).map out = ∑ jl : Fin k × Fin M,
      ENNReal.ofReal (w jl / ∑ il, w il) • Measure.dirac (v jl.1, jl.2)
  rw [Measure.map_finset_sum' hout.aemeasurable]
  simp only [Measure.map_smul, Measure.map_dirac' hout, hden]
  exact e.sum_comp (fun jl => ENNReal.ofReal (w jl / ∑ il, w il) • Measure.dirac (v jl.1, jl.2))

lemma private_selectionLaw (d p k M m : ℕ) (hk : 0 < k) (hM : 0 < M) (hm : 0 < m)
    (ε : ℝ) (hε : 0 < ε) (v : Fin k → UnitBall d p) :
    ∃ N : PrivateUniformGen.Characterization.Mechanism (Example d) (Output d p M) m,
      (∀ V, (N V : Measure (Output d p M)) = selectionLaw d p k M m ε v V) ∧
      PrivateUniformGen.Characterization.IsDP N ε 0 := by
  let e : Fin (k * M) ≃ Fin k × Fin M := finProdFinEquiv.symm
  let out := fun j : Fin (k * M) => (v (e j).1, (e j).2)
  let h := fun j : Fin (k * M) => candidate d p M (v (e j).1).val (e j).2
  have hh : ∀ j, Measurable (h j) := fun j => measurable_candidate _ _ _ _ _
  obtain ⟨N,hN,_,hNdp,_⟩ := lemma_B_5 (k * M) m (Nat.mul_pos hk hM) hm
    (Measure.dirac (0, true) : Measure (Example d)) h hh ε (1/2) hε (by norm_num)
  have hout : Measurable out := measurable_of_countable _
  obtain ⟨A,hA,hAdp⟩ := lemma_B_3 m ε 0 hε (by norm_num) N hNdp (Kernel.deterministic out hout)
  refine ⟨A, ?_, hAdp⟩
  intro V
  rw [hA V, Measure.deterministic_comp_eq_map hout, hN V]
  exact selectionLaw_reindex d p k M m ε v V
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
lemma selectionLaw_neighbor_le (d p k M m : ℕ) (hk : 0 < k) (hM : 0 < M) (hm : 0 < m)
    (ε : ℝ) (hε : 0 < ε) (v : Fin k → UnitBall d p)
    (V V' : Fin m → Example d) (hVV : PrivateUniformGen.Characterization.Neighbors V V')
    (U : Set (Output d p M)) (hU : MeasurableSet U) :
    (selectionLaw d p k M m ε v V) U ≤
      ENNReal.ofReal (Real.exp ε) * (selectionLaw d p k M m ε v V') U := by
  obtain ⟨N,hN,hDP⟩ := private_selectionLaw d p k M m hk hM hm ε hε v
  have hh := hDP V V' hVV U hU
  simp only [hN, add_zero] at hh
  have hh' := ENNReal.ofReal_le_ofReal hh
  haveI := selectionLaw_probability d p k M m hk hM ε v V
  haveI := selectionLaw_probability d p k M m hk hM ε v V'
  simpa [Measure.real, ENNReal.ofReal_mul (Real.exp_pos ε).le] using hh'

set_option maxHeartbeats 50000 in
lemma validation_bind_private (d p k M m : ℕ) (hk : 0 < k) (hM : 0 < M) (hm : 0 < m)
    (ε : ℝ) (hε : 0 < ε)
    (μ : Measure (Fin k → UnitBall d p)) [IsProbabilityMeasure μ]
    (V V' : Fin m → Example d) (hVV : PrivateUniformGen.Characterization.Neighbors V V')
    (U : Set (Output d p M)) (hU : MeasurableSet U) :
    (μ.bind (fun v => selectionLaw d p k M m ε v V)).real U ≤
      Real.exp ε * (μ.bind (fun v => selectionLaw d p k M m ε v V')).real U := by
  have hmeas (W : Fin m → Example d) :
      Measurable (fun v : Fin k → UnitBall d p => selectionLaw d p k M m ε v W) := by
    have hpair : Measurable (fun v : Fin k → UnitBall d p => (v, W)) :=
      measurable_id.prodMk measurable_const
    have hh := (measurable_selectionLaw d p k M m ε).comp hpair
    simpa only [Function.comp_def] using hh
  have hp (W : Fin m → Example d) :
      IsProbabilityMeasure (μ.bind (fun v => selectionLaw d p k M m ε v W)) :=
    isProbabilityMeasure_bind (hmeas W).aemeasurable
      (ae_of_all _ (fun v => selectionLaw_probability d p k M m hk hM ε v W))
  haveI := hp V'
  have hbound : (μ.bind (fun v => selectionLaw d p k M m ε v V)) U ≤
      ENNReal.ofReal (Real.exp ε) * (μ.bind (fun v => selectionLaw d p k M m ε v V')) U := by
    rw [Measure.bind_apply hU (hmeas V).aemeasurable,
      Measure.bind_apply hU (hmeas V').aemeasurable]
    calc
      _ ≤ ∫⁻ v, ENNReal.ofReal (Real.exp ε) * (selectionLaw d p k M m ε v V') U ∂μ :=
        lintegral_mono (fun v => selectionLaw_neighbor_le d p k M m hk hM hm ε hε v V V' hVV U hU)
      _ = _ := lintegral_const_mul _ (((Measure.measurable_coe hU).comp (hmeas V')))
  have hh := ENNReal.toReal_mono (by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hbound
  simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos ε).le] using hh
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
lemma block_neighbors (d k n₀ m : ℕ) (hn : 0 < n₀)
    (S S' : Fin (k * n₀ + m) → Example d)
    (hSS : PrivateUniformGen.Characterization.Neighbors S S') :
    (∃ j : Fin k,
      PrivateUniformGen.Characterization.Neighbors (trainingBlocks d k n₀ m S j) (trainingBlocks d k n₀ m S' j) ∧
      (∀ r, r ≠ j → trainingBlocks d k n₀ m S r = trainingBlocks d k n₀ m S' r) ∧
      validationBlock d k n₀ m S = validationBlock d k n₀ m S') ∨
    (trainingBlocks d k n₀ m S = trainingBlocks d k n₀ m S' ∧
      PrivateUniformGen.Characterization.Neighbors (validationBlock d k n₀ m S) (validationBlock d k n₀ m S')) := by
  classical
  rcases hSS with ⟨i,hne,heq⟩
  by_cases ht : i.val < k * n₀
  · let j : Fin k := ⟨i.val / n₀, (Nat.div_lt_iff_lt_mul hn).2 ht⟩
    let l : Fin n₀ := ⟨i.val % n₀, Nat.mod_lt _ hn⟩
    have hidx : j.val * n₀ + l.val = i.val := by
      dsimp [j,l]
      simpa [Nat.mul_comm] using Nat.div_add_mod i.val n₀
    have hquot (r : Fin k) (a : Fin n₀) : (r.val * n₀ + a.val) / n₀ = r.val := by
      rw [Nat.mul_comm r.val n₀, Nat.mul_add_div hn, Nat.div_eq_of_lt a.isLt, Nat.add_zero]
    left
    refine ⟨j, ⟨l, ?_, ?_⟩, ?_, ?_⟩
    · change S ⟨j.val * n₀ + l.val, _⟩ ≠ S' ⟨j.val * n₀ + l.val, _⟩
      have hi : (⟨j.val * n₀ + l.val, by omega⟩ : Fin (k * n₀ + m)) = i := Fin.ext hidx
      simpa only [hi] using hne
    · intro a hal
      apply heq
      intro hh
      apply hal
      apply Fin.ext
      have hv := congrArg Fin.val hh
      change j.val * n₀ + a.val = i.val at hv
      omega
    · intro r hr
      funext a
      apply heq
      intro hh
      apply hr
      apply Fin.ext
      have hv := congrArg (fun x : Fin (k * n₀ + m) => x.val / n₀) hh
      change (r.val * n₀ + a.val) / n₀ = i.val / n₀ at hv
      simpa only [hquot] using hv
    · funext a
      apply heq
      intro hh
      have hv := congrArg Fin.val hh
      change k * n₀ + a.val = i.val at hv
      omega
  · right
    have hi0 : k * n₀ ≤ i.val := by omega
    let l : Fin m := ⟨i.val - k * n₀, by omega⟩
    have hidx : k * n₀ + l.val = i.val := by dsimp [l]; omega
    refine ⟨?_, l, ?_, ?_⟩
    · funext r a
      apply heq
      intro hh
      have hv := congrArg Fin.val hh
      change r.val * n₀ + a.val = i.val at hv
      have hj := Nat.mul_le_mul_right n₀ (Nat.succ_le_of_lt r.isLt)
      have ha := a.isLt
      nlinarith
    · change S ⟨k * n₀ + l.val, _⟩ ≠ S' ⟨k * n₀ + l.val, _⟩
      have hi : (⟨k * n₀ + l.val, by omega⟩ : Fin (k * n₀ + m)) = i := Fin.ext hidx
      simpa only [hi] using hne
    · intro a hal
      apply heq
      intro hh
      apply hal
      apply Fin.ext
      have hv := congrArg Fin.val hh
      change k * n₀ + a.val = i.val at hv
      omega
end PrivateAgnosticHalfspace.Gaussian

open PrivateAgnosticHalfspace.Gaussian

theorem solution (O : Optimizer) (d p k M n₀ m : ℕ)
    (hk : 0 < k) (hM : 0 < M) (hn : 2 ≤ n₀) (hm : 0 < m)
    (ε δ : ℝ) (hε : 0 < ε ∧ ε ≤ 1 / 2) (hδ : 0 < δ ∧ δ ≤ 1 / 2)
    (hOmeas : Measurable (fun S => (O d p n₀ ε δ S : Measure (UnitBall d p))))
    (hOprivate : PrivateUniformGen.Characterization.IsDP (O d p n₀ ε δ) ε δ) :
    ∃ A : PrivateUniformGen.Characterization.Mechanism (Example d) (Output d p M) (k * n₀ + m),
      (∀ S, (A S : Measure (Output d p M)) = algorithmLaw O d p k M n₀ m ε δ S) ∧
      Measurable (fun S => (A S : Measure (Output d p M))) ∧
      PrivateUniformGen.Characterization.IsDP A ε δ := by
  let A : PrivateUniformGen.Characterization.Mechanism (Example d) (Output d p M) (k * n₀ + m) :=
    fun S => ⟨algorithmLaw O d p k M n₀ m ε δ S,
      algorithmLaw_probability O d p k M n₀ m hk hM ε δ S⟩
  refine ⟨A, (fun _ => rfl), measurable_algorithmLaw O d p k M n₀ m ε δ hOmeas, ?_⟩
  intro S S' hSS U hU
  change (algorithmLaw O d p k M n₀ m ε δ S).real U ≤
    Real.exp ε * (algorithmLaw O d p k M n₀ m ε δ S').real U + δ
  rw [algorithmLaw_eq, algorithmLaw_eq]
  rcases block_neighbors d k n₀ m (by omega) S S' hSS with
    ⟨j,hj,hother,hval⟩ | ⟨hblocks,hval⟩
  · cases k with
    | zero => exact Fin.elim0 j
    | succ k =>
      have hsel : Measurable (fun v : Fin (k + 1) → UnitBall d p =>
          selectionLaw d p (k + 1) M m ε v (validationBlock d (k + 1) n₀ m S)) := by
        have hpair : Measurable (fun v : Fin (k + 1) → UnitBall d p =>
            (v, validationBlock d (k + 1) n₀ m S)) := measurable_id.prodMk measurable_const
        have hh := (measurable_selectionLaw d p (k + 1) M m ε).comp hpair
        simpa only [Function.comp_def] using hh
      let H : Kernel (Fin (k + 1) → UnitBall d p) (Output d p M) :=
        ⟨fun v => selectionLaw d p (k + 1) M m ε v (validationBlock d (k + 1) n₀ m S), hsel⟩
      letI : IsMarkovKernel H := ⟨fun v => selectionLaw_probability d p (k + 1) M m hk hM ε v _⟩
      have hh := private_product_one_coordinate k n₀ ε δ hε.1
        ⟨hδ.1.le, by linarith [hδ.2]⟩
        (fun _ => O d p n₀ ε δ) (fun _ => hOprivate)
        (trainingBlocks d (k + 1) n₀ m S) (trainingBlocks d (k + 1) n₀ m S') j hj hother H U hU
      rw [← hval]
      exact hh
  · rw [hblocks]
    have hh := validation_bind_private d p k M m hk hM hm ε hε.1
      (Measure.pi (fun j => (O d p n₀ ε δ (trainingBlocks d k n₀ m S' j) : Measure (UnitBall d p))))
      (validationBlock d k n₀ m S) (validationBlock d k n₀ m S') hval U hU
    exact hh.trans (le_add_of_nonneg_right hδ.1.le)
