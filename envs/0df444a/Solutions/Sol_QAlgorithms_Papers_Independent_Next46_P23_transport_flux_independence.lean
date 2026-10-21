-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P23.transport_flux_independence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:23:27.649805+00:00
-- url     : https://prove2.me/submissions/a206a6a6-b98d-4f98-896a-145edc3f33a5

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23
noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

open QAlgorithms.Papers.Independent.Next46.P23

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15 (propagator legendre rightSlope leftSlope FiniteExperiment exponentialMoment)

open QAlgorithms.Papers.Independent.Dependency50.P05 (uniformDensity)

open QAlgorithms.Papers.Independent.Dependency50.P28 (Schwarz)

open QAlgorithms.Papers.Independent.Frontier30.P28 (inverseExponent)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms (traceRight)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem g64t_param {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (G : E × ℝ → ℝ) (hG : ContDiff ℝ 1 G) (a b : ℝ) (x0 : E) :
    HasFDerivAt (fun x => ∫ s in a..b, G (x, s))
      (∫ s in a..b, (fderiv ℝ G (x0, s)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x0 := by
  have hd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hcf : Continuous (fderiv ℝ G) := hG.continuous_fderiv (by norm_num)
  set F' : E → ℝ → E →L[ℝ] ℝ := fun x s => (fderiv ℝ G (x, s)).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hF'c : Continuous (fun p : E × ℝ => F' p.1 p.2) := by
    simp only [F']
    exact (hcf.comp (continuous_fst.prodMk continuous_snd)).clm_comp continuous_const
  obtain ⟨C, hC⟩ := (IsCompact.prod (isCompact_closedBall x0 1) (isCompact_uIcc (a := a) (b := b))).exists_bound_of_continuousOn
    hF'c.continuousOn
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (F' := F') (bound := fun _ => C)
    (Metric.closedBall_mem_nhds x0 one_pos) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · exact Filter.Eventually.of_forall (fun x =>
      (hG.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact (hG.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · exact (hF'c.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun s hs x hx => hC (x, s) ⟨hx, ?_⟩)
    exact Set.uIoc_subset_uIcc hs
  · refine Filter.Eventually.of_forall (fun s _ x _ => ?_)
    have h1 : HasFDerivAt (fun x : E => (x, s)) (ContinuousLinearMap.inl ℝ E ℝ) x :=
      (hasFDerivAt_id x).prodMk (hasFDerivAt_const s x)
    exact (hd (x, s)).hasFDerivAt.comp x h1

theorem g64t_exp : ContDiff ℝ 1 (NormedSpace.exp : Mat I → Mat I) :=
  contDiff_iff_contDiffAt.mpr (fun x => (NormedSpace.exp_analytic x).contDiffAt)

theorem g64t_trre : ContDiff ℝ 1 (fun M : Mat I => M.trace.re) := by
  have : (fun M : Mat I => M.trace.re) =
      Complex.reCLM.comp (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap I ℝ ℂ)) := by
    funext M; rfl
  rw [this]; exact ContinuousLinearMap.contDiff _

theorem g64t_prop {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (H : E → Mat I)
    (hH : ContDiff ℝ 1 H) (c : ℝ) :
    ContDiff ℝ 1 (fun p : E × ℝ => propagator (H p.1) (c * p.2)) := by
  unfold propagator
  have : ContDiff ℝ 1 (fun p : E × ℝ => ((c * p.2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_snd))
  exact g64t_exp.comp (ContDiff.smul (f := fun p : E × ℝ => (-((c * p.2 : ℝ) : ℂ) * Complex.I))
    (this.neg.mul contDiff_const) (hH.comp contDiff_fst))

def g64tG {E : Type*} (H ω Ψ : E → Mat I) : E × ℝ → ℝ :=
  fun p => ev (ω p.1) (tau (H p.1) p.2 (Ψ p.1))

theorem g64tG_eq {E : Type*} (H ω Ψ : E → Mat I) (p : E × ℝ) :
    g64tG H ω Ψ p = ((propagator (H p.1) ((-1) * p.2) * Ψ p.1 * propagator (H p.1) (1 * p.2)) * ω p.1).trace.re := by
  simp [g64tG, ev, QAlgorithms.effectProb, tau]

theorem g64tG_cd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (H ω Ψ : E → Mat I)
    (hH : ContDiff ℝ 1 H) (hω : ContDiff ℝ 1 ω) (hΨ : ContDiff ℝ 1 Ψ) : ContDiff ℝ 1 (g64tG H ω Ψ) := by
  have e : g64tG H ω Ψ = fun p => ((propagator (H p.1) ((-1) * p.2) * Ψ p.1 *
      propagator (H p.1) (1 * p.2)) * ω p.1).trace.re := funext (g64tG_eq H ω Ψ)
  rw [e]
  exact g64t_trre.comp ((((g64t_prop H hH (-1)).mul (hΨ.comp contDiff_fst)).mul (g64t_prop H hH 1)).mul
    (hω.comp contDiff_fst))

theorem g64tG_cyc {E : Type*} (H ω Ψ : E → Mat I) (x : E) (s : ℝ) :
    g64tG H ω Ψ (x, s) = (Ψ x * (propagator (H x) (1 * s) * ω x * propagator (H x) ((-1) * s))).trace.re := by
  rw [g64tG_eq]
  dsimp only
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem g64tG_hasfd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (H ω Ψ : E → Mat I)
    (hH : ContDiff ℝ 1 H) (hω : ContDiff ℝ 1 ω) (hΨ : ContDiff ℝ 1 Ψ) (x0 : E) (h0 : Ψ x0 = 0) (s : ℝ) :
    HasFDerivAt (fun x => g64tG H ω Ψ (x, s))
      ((LinearMap.toContinuousLinearMap (Matrix.traceLinearMap I ℝ ℂ)).comp
        ((ContinuousLinearMap.mul ℝ (Mat I)).flip
          (propagator (H x0) (1 * s) * ω x0 * propagator (H x0) ((-1) * s)) |>.comp (fderiv ℝ Ψ x0))
        |> Complex.reCLM.comp) x0 := by
  set Q : E → Mat I := fun x => propagator (H x) (1 * s) * ω x * propagator (H x) ((-1) * s) with hQ
  have hQd : ContDiff ℝ 1 Q := by
    have h1 := (g64t_prop H hH 1).comp (contDiff_id.prodMk (contDiff_const (c := s)))
    have h2 := (g64t_prop H hH (-1)).comp (contDiff_id.prodMk (contDiff_const (c := s)))
    exact (h1.mul hω).mul h2
  have e : (fun x => g64tG H ω Ψ (x, s)) = fun x => (Ψ x * Q x).trace.re := by
    funext x; rw [g64tG_cyc]
  rw [e]
  have hm := ((hΨ.differentiable (by norm_num)) x0).hasFDerivAt.mul'
    ((hQd.differentiable (by norm_num)) x0).hasFDerivAt
  have ht := (Complex.reCLM.comp (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap I ℝ ℂ))).hasFDerivAt.comp x0 hm
  refine ht.congr_fderiv ?_
  ext v
  simp [h0, MulOpposite.smul_eq_mul_unop, hQ]

theorem g64t_D0 {n : ℕ} (D : (Fin n → ℝ) → Fin n → Mat I) (hD : ∀ j, Continuous (fun X => D X j))
    (hsum : ∀ X, ∑ j, ((X j : ℝ) : ℂ) • D X j = 0) (k : Fin n) : D 0 k = 0 := by
  set g : ℝ → Mat I := fun ε => D (ε • Pi.single k 1) k with hg
  have hgc : Continuous g := (hD k).comp (continuous_id.smul continuous_const)
  have hz : ∀ ε, ε ≠ 0 → g ε = 0 := by
    intro ε hε
    have := hsum (ε • Pi.single k 1)
    rw [Finset.sum_eq_single k (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)] at this
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at this
    exact (smul_eq_zero.mp this).resolve_left (by exact_mod_cast hε)
  have h1 : Filter.Tendsto g (nhdsWithin 0 {0}ᶜ) (nhds (g 0)) := hgc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto g (nhdsWithin 0 {0}ᶜ) (nhds 0) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall (fun ε hε => (hz ε hε).symm))
  have := tendsto_nhds_unique h1 h2
  simpa [hg] using this

theorem g64t_Q {n : ℕ} (D : (Fin n → ℝ) → Fin n → Mat I) (hD : ∀ j, ContDiff ℝ 1 (fun X => D X j))
    (hsum : ∀ X, ∑ j, ((X j : ℝ) : ℂ) • D X j = 0) (v : Fin n → ℝ) :
    ∑ j, ((v j : ℝ) : ℂ) • fderiv ℝ (fun X => D X j) 0 v = 0 := by
  have h0 := g64t_D0 D (fun j => (hD j).continuous) hsum
  set h : ℝ → Mat I := fun ε => ∑ j, ((v j : ℝ) : ℂ) • D (ε • v) j with hh
  have hz : ∀ ε, h ε = 0 := by
    intro ε
    by_cases hε : ε = 0
    · subst hε; simp [hh, h0]
    · have := hsum (ε • v)
      simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, mul_smul] at this
      rw [← Finset.smul_sum] at this
      exact (smul_eq_zero.mp this).resolve_left (by exact_mod_cast hε)
  have hd : HasDerivAt h (∑ j, ((v j : ℝ) : ℂ) • fderiv ℝ (fun X => D X j) 0 v) 0 := by
    apply HasDerivAt.fun_sum
    intro j _
    refine (?_ : HasDerivAt (fun y : ℝ => D (y • v) j) _ 0).const_smul (((v j : ℝ) : ℂ))
    have hl : HasDerivAt (fun ε : ℝ => ε • v) v 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).smul_const v
    have hf : HasFDerivAt (fun X => D X j) (fderiv ℝ (fun X => D X j) 0) ((0 : ℝ) • v) := by
      rw [zero_smul]; exact ((hD j).differentiable (by norm_num) 0).hasFDerivAt
    exact hf.comp_hasDerivAt (0:ℝ) hl
  have hc : HasDerivAt h 0 0 := by
    have : h = fun _ => 0 := funext hz
    rw [this]; exact hasDerivAt_const _ _
  exact hd.unique hc

theorem g64t_anti {n : ℕ} (D : (Fin n → ℝ) → Fin n → Mat I) (hD : ∀ j, ContDiff ℝ 1 (fun X => D X j))
    (hsum : ∀ X, ∑ j, ((X j : ℝ) : ℂ) • D X j = 0) (j k : Fin n) :
    fderiv ℝ (fun X => D X j) 0 (Pi.single k 1) + fderiv ℝ (fun X => D X k) 0 (Pi.single j 1) = 0 := by
  set L : Fin n → (Fin n → ℝ) →L[ℝ] Mat I := fun j => fderiv ℝ (fun X => D X j) 0 with hL
  have key : ∀ (a b : Fin n) (w : Fin n → ℝ),
      ∑ i, (((Pi.single a 1 + Pi.single b 1 : Fin n → ℝ) i : ℝ) : ℂ) • L i w = L a w + L b w := by
    intro a b w
    simp only [Pi.add_apply, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single a (fun i _ hi => by simp [Pi.single_apply, hi]) (by simp)]; simp
    · rw [Finset.sum_eq_single b (fun i _ hi => by simp [Pi.single_apply, hi]) (by simp)]; simp
  have single : ∀ a, L a (Pi.single a 1) = 0 := by
    intro a
    have := g64t_Q D hD hsum (Pi.single a 1)
    rw [Finset.sum_eq_single a (fun i _ hi => by simp [Pi.single_apply, hi]) (by simp)] at this
    simpa using this
  have h2 := g64t_Q D hD hsum (Pi.single j 1 + Pi.single k 1)
  have h3 := key j k (Pi.single j 1 + Pi.single k 1)
  rw [h3, map_add, map_add, single j, single k] at h2
  have : L j (Pi.single k 1) + L k (Pi.single j 1) = 0 := by
    rw [← h2]; abel
  exact this

theorem g64t_kin {n : ℕ} (H ω Ψ : (Fin n → ℝ) → Mat I) (hH : ContDiff ℝ 1 H) (hω : ContDiff ℝ 1 ω)
    (hΨ : ContDiff ℝ 1 Ψ) (t : ℝ) (v : Fin n → ℝ) :
    fderiv ℝ (fun X => t⁻¹ * ∫ s in (0:ℝ)..t, g64tG H ω Ψ (X, s)) 0 v =
      t⁻¹ * ∫ s in (0:ℝ)..t, fderiv ℝ (g64tG H ω Ψ) (0, s) (v, 0) := by
  have hG := g64tG_cd H ω Ψ hH hω hΨ
  have h1 := (g64t_param (g64tG H ω Ψ) hG 0 t 0).const_mul t⁻¹
  rw [h1.fderiv]
  have hcf : Continuous (fderiv ℝ (g64tG H ω Ψ)) := hG.continuous_fderiv (by norm_num)
  have hint : IntervalIntegrable (fun s => (fderiv ℝ (g64tG H ω Ψ) (0, s)).comp
      (ContinuousLinearMap.inl ℝ (Fin n → ℝ) ℝ)) MeasureTheory.volume 0 t :=
    ((hcf.comp (continuous_const.prodMk continuous_id)).clm_comp continuous_const).intervalIntegrable _ _
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [ContinuousLinearMap.intervalIntegral_apply hint]
  rfl

theorem g64t_diff {n : ℕ} (H ω Ψ Ψ' : (Fin n → ℝ) → Mat I) (hH : ContDiff ℝ 1 H) (hω : ContDiff ℝ 1 ω)
    (hΨ : ContDiff ℝ 1 Ψ) (hΨ' : ContDiff ℝ 1 Ψ') (h0 : Ψ 0 = Ψ' 0) (t : ℝ) (v : Fin n → ℝ) :
    fderiv ℝ (fun X => t⁻¹ * ∫ s in (0:ℝ)..t, g64tG H ω Ψ (X, s)) 0 v -
      fderiv ℝ (fun X => t⁻¹ * ∫ s in (0:ℝ)..t, g64tG H ω Ψ' (X, s)) 0 v =
      t⁻¹ * ∫ s in (0:ℝ)..t, ((fderiv ℝ Ψ 0 v - fderiv ℝ Ψ' 0 v) *
        (propagator (H 0) (1 * s) * ω 0 * propagator (H 0) ((-1) * s))).trace.re := by
  rw [g64t_kin H ω Ψ hH hω hΨ, g64t_kin H ω Ψ' hH hω hΨ', ← mul_sub]
  congr 1
  have hG := g64tG_cd H ω Ψ hH hω hΨ
  have hG' := g64tG_cd H ω Ψ' hH hω hΨ'
  have hc : ∀ (K : (Fin n → ℝ) × ℝ → ℝ), ContDiff ℝ 1 K →
      IntervalIntegrable (fun s => fderiv ℝ K (0, s) (v, 0)) MeasureTheory.volume 0 t := by
    intro K hK
    exact (((hK.continuous_fderiv (by norm_num)).comp (continuous_const.prodMk continuous_id)).clm_apply
      continuous_const).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub (hc _ hG) (hc _ hG')]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  have hdiff : g64tG H ω Ψ - g64tG H ω Ψ' = g64tG H ω (Ψ - Ψ') := by
    funext p
    simp only [Pi.sub_apply, g64tG, ev, QAlgorithms.effectProb, tau, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.trace_sub, Complex.sub_re]
  have hd1 := (hG.differentiable (by norm_num) (0, s))
  have hd2 := (hG'.differentiable (by norm_num) (0, s))
  rw [← ContinuousLinearMap.sub_apply, ← fderiv_sub hd1 hd2]
  show fderiv ℝ (g64tG H ω Ψ - g64tG H ω Ψ') (0, s) (v, 0) = _
  rw [hdiff]
  have hD : ContDiff ℝ 1 (Ψ - Ψ') := hΨ.sub hΨ'
  have hDd := (g64tG_cd H ω (Ψ - Ψ') hH hω hD).differentiable (by norm_num) (0, s)
  have hpart : HasFDerivAt (fun x => g64tG H ω (Ψ - Ψ') (x, s))
      ((fderiv ℝ (g64tG H ω (Ψ - Ψ')) (0, s)).comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) ℝ)) 0 := by
    have h1 : HasFDerivAt (fun x : Fin n → ℝ => (x, s)) (ContinuousLinearMap.inl ℝ (Fin n → ℝ) ℝ) 0 :=
      (hasFDerivAt_id (0 : Fin n → ℝ)).prodMk (hasFDerivAt_const s (0 : Fin n → ℝ))
    have h3 : HasFDerivAt (g64tG H ω (Ψ - Ψ')) (fderiv ℝ (g64tG H ω (Ψ - Ψ')) (0, s))
        ((fun x : Fin n → ℝ => (x, s)) 0) := hDd.hasFDerivAt
    exact h3.comp (0 : Fin n → ℝ) h1
  have h2 := g64tG_hasfd H ω (Ψ - Ψ') hH hω hD 0 (by simp [h0]) s
  have := congrArg (fun L => L v) (hpart.unique h2)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] at this
  rw [this]
  simp [fderiv_sub (hΨ.differentiable (by norm_num) 0) (hΨ'.differentiable (by norm_num) 0),
    Matrix.sub_mul, Matrix.trace_sub]

/-- Proposition3.13, source PDF p.88: symmetric parts agree for two flux relations.
Equality of coefficients requires ORR for both descriptions. -/
theorem solution [Nonempty I] {n : ℕ} (F G : FluxFamily I n)
    (hF : FluxC1 F) (hG : FluxC1 G) (hH : F.H = G.H) (homega : F.omega = G.omega)
    (t : ℝ) (ht : 0 < t) :
    (∀ j k, kineticCoefficient F t j k + kineticCoefficient F t k j = kineticCoefficient G t j k + kineticCoefficient G t k j) ∧
    ((∀ j k, kineticCoefficient F t j k = kineticCoefficient F t k j) →
      (∀ j k, kineticCoefficient G t j k = kineticCoefficient G t k j) →
        ∀ j k, kineticCoefficient F t j k = kineticCoefficient G t j k) 
:= by
  obtain ⟨hFH, hFω, hFΦ⟩ := hF
  obtain ⟨_, _, hGΦ⟩ := hG
  set D : (Fin n → ℝ) → Fin n → Mat I := fun X j => F.Phi X j - G.Phi X j with hDdef
  have hDc : ∀ j, ContDiff ℝ 1 (fun X => D X j) := fun j => (hFΦ j).sub (hGΦ j)
  have hsum : ∀ X, ∑ j, ((X j : ℝ) : ℂ) • D X j = 0 := by
    intro X
    have h1 := F.flux_relation X
    have h2 := G.flux_relation X
    rw [← hH, ← homega] at h2
    simp only [hDdef, smul_sub, Finset.sum_sub_distrib]
    rw [← h1, ← h2, sub_self]
  have hD0 := g64t_D0 D (fun j => (hDc j).continuous) hsum
  have hdiff : ∀ j k, kineticCoefficient F t j k - kineticCoefficient G t j k =
      t⁻¹ * ∫ s in (0:ℝ)..t, ((fderiv ℝ (fun X => D X j) 0 (Pi.single k 1)) *
        (propagator (F.H 0) (1 * s) * F.omega 0 * propagator (F.H 0) ((-1) * s))).trace.re := by
    intro j k
    unfold kineticCoefficient
    rw [← hH, ← homega]
    have h0 : F.Phi 0 j = G.Phi 0 j := sub_eq_zero.mp (hD0 j)
    have := g64t_diff F.H F.omega (fun X => F.Phi X j) (fun X => G.Phi X j) hFH hFω (hFΦ j) (hGΦ j) h0 t
      (Pi.single k 1)
    rw [show (fun X => D X j) = (fun X => F.Phi X j) - (fun X => G.Phi X j) from rfl,
      fderiv_sub ((hFΦ j).differentiable (by norm_num) 0) ((hGΦ j).differentiable (by norm_num) 0)]
    exact this
  have hQc : Continuous (fun s : ℝ => propagator (F.H 0) (1 * s) * F.omega 0 * propagator (F.H 0) ((-1) * s)) := by
    have h1 := ((g64t_prop F.H hFH 1).continuous).comp (continuous_const.prodMk continuous_id (f := fun _ : ℝ => (0 : Fin n → ℝ)))
    have h2 := ((g64t_prop F.H hFH (-1)).continuous).comp (continuous_const.prodMk continuous_id (f := fun _ : ℝ => (0 : Fin n → ℝ)))
    exact (h1.mul continuous_const).mul h2
  have hII : ∀ M : Mat I, IntervalIntegrable (fun s => (M * (propagator (F.H 0) (1 * s) * F.omega 0 *
      propagator (F.H 0) ((-1) * s))).trace.re) MeasureTheory.volume 0 t := by
    intro M
    exact (g64t_trre.continuous.comp (continuous_const.mul hQc)).intervalIntegrable _ _
  have hanti : ∀ j k, (kineticCoefficient F t j k - kineticCoefficient G t j k) +
      (kineticCoefficient F t k j - kineticCoefficient G t k j) = 0 := by
    intro j k
    rw [hdiff j k, hdiff k j, ← mul_add, ← intervalIntegral.integral_add (hII _) (hII _)]
    have : ∀ s : ℝ, ((fderiv ℝ (fun X => D X j) 0 (Pi.single k 1)) *
          (propagator (F.H 0) (1 * s) * F.omega 0 * propagator (F.H 0) ((-1) * s))).trace.re +
        ((fderiv ℝ (fun X => D X k) 0 (Pi.single j 1)) *
          (propagator (F.H 0) (1 * s) * F.omega 0 * propagator (F.H 0) ((-1) * s))).trace.re = 0 := by
      intro s
      rw [← Complex.add_re, ← Matrix.trace_add, ← Matrix.add_mul, g64t_anti D hDc hsum j k]
      simp
    simp only [this, intervalIntegral.integral_zero, mul_zero]
  refine ⟨fun j k => ?_, fun hsF hsG j k => ?_⟩
  · linarith [hanti j k]
  · have := hanti j k
    rw [hsF k j, hsG k j] at this
    linarith
end
