-- Prove2me | solution 1 for SmaleNinth.bss_one_variable_lp_no_linear_program
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-07T18:35:03.5457+00:00
-- url     : https://prove2.me/submissions/6b6ab876-e52c-40dc-a811-517edd6bab32

import Definitions.Def_Polyhedron
import Definitions.Def_SmaleNinth_BSSMachine
import Mathlib
import Mathlib.Tactic

/-!
# No uniform BSS program decides one-variable LP feasibility in linear time

Disproof of `SmaleNinth.bss_decides_one_variable_lp`. Every instruction of the
machine addresses fixed cells within a window `[-W, W]` around the head, and
only whole-tape shifts move the window. For a fixed program, choose `p` active
constraints with coefficients `x ∈ ℝ^p` far to the left of a boundary `β` and
right-hand sides far to the right; on the corner instances (coefficients `x`,
right-hand sides `x`) some boundary is crossed at most `C + 1` times, so the
run is determined across `β` by a transcript of at most `(C+1)(2W+1) < p`
reals (the window contents at the crossing times). Near a generic `x` the run
follows a fixed branch and the transcript is a `C¹` function of `x`; the
coupling of two corner runs with equal transcripts shows the mixed instance
`(x, x')` is decided like the corner ones, hence feasible, which forces
`x = x'`. So the transcript is injective on an open set, contradicting the
fact that a `C¹` map into a lower-dimensional space is nowhere injective
(implicit function theorem).
-/

/-!
Analytic core of the lower bound: a `C¹` map from a finite-dimensional real
normed space into one of strictly smaller dimension is not injective on any
nonempty open set. Proof: at a point of maximal rank `r` of the derivative
the rank is locally constant, so the level set of `r` independent components
is a `C¹` submanifold of positive dimension along which the map is constant
(implicit function theorem plus vanishing derivative).
-/

open Filter Topology Module

namespace SmaleNinth.LB

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The rank of the derivative of `f` at `y`. -/
noncomputable def drank (f : E → F) (y : E) : ℕ :=
  finrank ℝ (LinearMap.range (fderiv ℝ f y : E →ₗ[ℝ] F))

lemma natCast_le_rank_iff {F' : Type*} [AddCommGroup F'] [Module ℝ F'] [FiniteDimensional ℝ F']
    {L : E →ₗ[ℝ] F'} {n : ℕ} :
    (n : Cardinal) ≤ LinearMap.rank L ↔ n ≤ finrank ℝ (LinearMap.range L) := by
  unfold LinearMap.rank
  rw [← Module.finrank_eq_rank, Nat.cast_le]

/-- A point of maximal derivative rank. -/
lemma exists_max_drank (f : E → F) (U : Set E) (hne : U.Nonempty) :
    ∃ x₀ ∈ U, ∀ y ∈ U, drank f y ≤ drank f x₀ := by
  have hbdd : BddAbove (drank f '' U) := ⟨finrank ℝ F, by
    rintro _ ⟨y, _, rfl⟩; exact Submodule.finrank_le _⟩
  obtain ⟨x₀, hx₀U, hx₀⟩ : ∃ x₀ ∈ U, drank f x₀ = sSup (drank f '' U) :=
    Nat.sSup_mem (hne.image _) hbdd
  exact ⟨x₀, hx₀U, fun y hy => by rw [hx₀]; exact le_csSup hbdd ⟨y, hy, rfl⟩⟩

/-- Near a point of maximal rank, composing with a map `π` that is injective on the range at
that point does not change kernels. -/
lemma exists_open_ker_eq {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    [FiniteDimensional ℝ R] (f : E → F) (U : Set E) (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (x₀ : E) (hx₀U : x₀ ∈ U) (hmax : ∀ y ∈ U, drank f y ≤ drank f x₀) (π : F →L[ℝ] R)
    (hπ : drank f x₀ ≤ finrank ℝ (LinearMap.range
      ((π : F →ₗ[ℝ] R).comp (fderiv ℝ f x₀ : E →ₗ[ℝ] F)))) :
    ∃ V : Set E, IsOpen V ∧ x₀ ∈ V ∧ V ⊆ U ∧ ∀ y ∈ V,
      LinearMap.ker ((π : F →ₗ[ℝ] R).comp (fderiv ℝ f y : E →ₗ[ℝ] F))
        = LinearMap.ker (fderiv ℝ f y : E →ₗ[ℝ] F) := by
  set r := drank f x₀ with hr
  have hcont : ContinuousOn (fderiv ℝ f) U := hf.continuousOn_fderiv_of_isOpen hU le_rfl
  set S₁ : Set (E →L[ℝ] F) := {L | (r : Cardinal) ≤ LinearMap.rank (L : E →ₗ[ℝ] F)} with hS₁
  set S₂ : Set (E →L[ℝ] R) := {L | (r : Cardinal) ≤ LinearMap.rank (L : E →ₗ[ℝ] R)} with hS₂
  have hS₁o : IsOpen S₁ := isOpen_setOfPred_nat_le_rank r
  have hS₂o : IsOpen S₂ := isOpen_setOfPred_nat_le_rank r
  have hcont' : ContinuousOn (fun y => π.comp (fderiv ℝ f y)) U :=
    continuousOn_const.clm_comp hcont
  have h1 := hcont.isOpen_inter_preimage hU hS₁o
  have h2 := hcont'.isOpen_inter_preimage hU hS₂o
  refine ⟨(U ∩ fderiv ℝ f ⁻¹' S₁) ∩ (U ∩ (fun y => π.comp (fderiv ℝ f y)) ⁻¹' S₂),
    h1.inter h2, ⟨⟨hx₀U, ?_⟩, ⟨hx₀U, ?_⟩⟩, fun y hy => hy.1.1, ?_⟩
  · show (r : Cardinal) ≤ LinearMap.rank (fderiv ℝ f x₀ : E →ₗ[ℝ] F)
    exact natCast_le_rank_iff.mpr le_rfl
  · show (r : Cardinal) ≤ LinearMap.rank ((π.comp (fderiv ℝ f x₀) : E →L[ℝ] R) : E →ₗ[ℝ] R)
    exact natCast_le_rank_iff.mpr hπ
  · intro y hy
    obtain ⟨⟨hyU, hy1⟩, ⟨_, hy2⟩⟩ := hy
    have hy1' : r ≤ finrank ℝ (LinearMap.range (fderiv ℝ f y : E →ₗ[ℝ] F)) :=
      natCast_le_rank_iff.mp hy1
    have hy2' : r ≤ finrank ℝ (LinearMap.range
        ((π : F →ₗ[ℝ] R).comp (fderiv ℝ f y : E →ₗ[ℝ] F))) := natCast_le_rank_iff.mp hy2
    have hle1 : finrank ℝ (LinearMap.range (fderiv ℝ f y : E →ₗ[ℝ] F)) ≤ r := hmax y hyU
    have hle2 : finrank ℝ (LinearMap.range ((π : F →ₗ[ℝ] R).comp (fderiv ℝ f y : E →ₗ[ℝ] F)))
        ≤ finrank ℝ (LinearMap.range (fderiv ℝ f y : E →ₗ[ℝ] F)) := by
      rw [LinearMap.range_comp]; exact Submodule.finrank_map_le _ _
    have e1 := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ f y : E →ₗ[ℝ] F)
    have e2 := LinearMap.finrank_range_add_finrank_ker
      ((π : F →ₗ[ℝ] R).comp (fderiv ℝ f y : E →ₗ[ℝ] F))
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · exact LinearMap.ker_le_ker_comp _ _
    · omega

set_option maxHeartbeats 1000000 in
theorem not_injOn_of_finrank_lt (f : E → F) (U : Set E) (hU : IsOpen U) (hne : U.Nonempty)
    (hf : ContDiffOn ℝ 1 f U) (hdim : finrank ℝ F < finrank ℝ E) : ¬ Set.InjOn f U := by
  intro hinj
  obtain ⟨x₀, hx₀U, hmax⟩ := exists_max_drank f U hne
  set r := drank f x₀ with hr
  set D : E →L[ℝ] F := fderiv ℝ f x₀ with hD
  set K : Submodule ℝ E := LinearMap.ker (D : E →ₗ[ℝ] F) with hK
  set R : Submodule ℝ F := LinearMap.range (D : E →ₗ[ℝ] F) with hR
  have hfinR : finrank ℝ R = r := rfl
  have hrn : finrank ℝ R + finrank ℝ K = finrank ℝ E :=
    LinearMap.finrank_range_add_finrank_ker (D : E →ₗ[ℝ] F)
  have hrF : r ≤ finrank ℝ F := Submodule.finrank_le _
  have hKpos : 0 < finrank ℝ K := by omega
  obtain ⟨K', hKK'⟩ := K.exists_isCompl
  obtain ⟨R', hRR'⟩ := R.exists_isCompl
  have hfinK' : finrank ℝ K' = r := by
    have := Submodule.finrank_add_eq_of_isCompl hKK'
    omega
  -- the projection `π : F → R`
  let π : F →L[ℝ] R := LinearMap.toContinuousLinearMap
    ((LinearMap.fst ℝ R R') ∘ₗ (Submodule.prodEquivOfIsCompl R R' hRR').symm.toLinearMap)
  have hπ : ∀ v : R, π (v : F) = v := fun v => by simp [π]
  have hrankπD : r ≤ finrank ℝ (LinearMap.range ((π : F →ₗ[ℝ] R).comp (D : E →ₗ[ℝ] F))) := by
    have hfac : (D : E →ₗ[ℝ] F) = R.subtype ∘ₗ ((π : F →ₗ[ℝ] R).comp (D : E →ₗ[ℝ] F)) := by
      ext v
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, ContinuousLinearMap.coe_coe]
      have hmem : D v ∈ R := LinearMap.mem_range_self (D : E →ₗ[ℝ] F) v
      have h := hπ (⟨D v, hmem⟩ : R)
      simp only at h
      rw [h]
    have hmap : LinearMap.range (D : E →ₗ[ℝ] F) =
        Submodule.map R.subtype (LinearMap.range ((π : F →ₗ[ℝ] R).comp (D : E →ₗ[ℝ] F))) := by
      rw [← LinearMap.range_comp, ← hfac]
    show finrank ℝ (LinearMap.range (D : E →ₗ[ℝ] F)) ≤ _
    rw [hmap]
    exact Submodule.finrank_map_le _ _
  obtain ⟨V, hVopen, hx₀V, hVU, hker⟩ :=
    exists_open_ker_eq f U hU hf x₀ hx₀U hmax π hrankπD
  -- the coordinate change `e : K × K' ≃ E`
  let e : (K × K') ≃L[ℝ] E := (Submodule.prodEquivOfIsCompl K K' hKK').toContinuousLinearEquiv
  have he : ∀ z : K × K', e z = (z.1 : E) + (z.2 : E) := fun z => rfl
  set u : K × K' := e.symm x₀ with hu
  have heu : e u = x₀ := e.apply_symm_apply x₀
  -- g̃ = π ∘ f ∘ e
  set g : K × K' → R := fun z => π (f (e z)) with hg
  have hfx₀ : ContDiffAt ℝ 1 f x₀ := hf.contDiffAt (hU.mem_nhds hx₀U)
  have hfx₀' : ContDiffAt ℝ 1 f (e u) := by rw [heu]; exact hfx₀
  have cdf : ContDiffAt ℝ 1 g u :=
    (hfx₀'.continuousLinearMap_comp π).comp u e.contDiff.contDiffAt
  have hDg : fderiv ℝ g u = π.comp (D.comp (e : K × K' →L[ℝ] E)) := by
    have h1 : HasFDerivAt f D (e u) := by rw [heu]; exact (hfx₀.differentiableAt (by simp)).hasFDerivAt
    exact (π.hasFDerivAt.comp u (h1.comp u e.hasFDerivAt)).fderiv
  -- invertibility of the partial derivative
  set M : K' →L[ℝ] R := π.comp (D.comp ((e : K × K' →L[ℝ] E).comp (ContinuousLinearMap.inr ℝ K K')))
    with hM
  have hMapply : ∀ k : K', (M k : F) = D (k : E) := fun k => by
    simp only [hM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    rw [ContinuousLinearEquiv.coe_coe, he]
    simp only [Submodule.coe_zero, zero_add]
    have hmem : D (k : E) ∈ R := LinearMap.mem_range_self (D : E →ₗ[ℝ] F) _
    have h := hπ (⟨D (k : E), hmem⟩ : R)
    simp only at h
    rw [h]
  have hMinj : LinearMap.ker (M : K' →ₗ[ℝ] R) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro k hk
    have h1 : D (k : E) = 0 := by
      have := congrArg (fun v : R => (v : F)) (show M k = 0 from hk)
      simpa [hMapply] using this
    have hkK : (k : E) ∈ K := by simpa [hK] using h1
    have : (k : E) ∈ K ⊓ K' := ⟨hkK, k.2⟩
    rw [hKK'.inf_eq_bot] at this
    exact Subtype.ext (by simpa using this)
  have hMsurj : LinearMap.range (M : K' →ₗ[ℝ] R) = ⊤ := by
    have hinjM : Function.Injective (M : K' →ₗ[ℝ] R) := LinearMap.ker_eq_bot.mp hMinj
    have hsurjM := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [hfinK', hfinR])).mp hinjM
    exact LinearMap.range_eq_top.mpr hsurjM
  have if₂ : (fderiv ℝ g u ∘L ContinuousLinearMap.inr ℝ K K').IsInvertible := by
    have : fderiv ℝ g u ∘L ContinuousLinearMap.inr ℝ K K' = M := by
      rw [hDg, hM]; rfl
    rw [this]
    exact ⟨ContinuousLinearEquiv.ofBijective M hMinj hMsurj,
      ContinuousLinearEquiv.coe_ofBijective M hMinj hMsurj⟩
  -- the implicit function
  set ψ : K → K' := cdf.implicitFunction (by simp) if₂ with hψ
  have hψu : ψ u.1 = u.2 := cdf.implicitFunction_apply_self (by simp) if₂
  have hev : ∀ᶠ x in 𝓝 u.1, g (x, ψ x) = g u := cdf.eventually_apply_implicitFunction (by simp) if₂
  have hψc : ContDiffAt ℝ 1 ψ u.1 := cdf.contDiffAt_implicitFunction (by simp) if₂
  -- a neighbourhood on which everything is nice
  have hφcont : ContinuousAt (fun x : K => e (x, ψ x)) u.1 := by
    have : ContinuousAt ψ u.1 := hψc.continuousAt
    exact e.continuous.continuousAt.comp (continuousAt_id.prodMk this)
  have hevV : ∀ᶠ x in 𝓝 u.1, e (x, ψ x) ∈ V := by
    apply hφcont.preimage_mem_nhds
    rw [hψu, Prod.mk.eta, heu]
    exact hVopen.mem_nhds hx₀V
  have hevψ : ∀ᶠ x in 𝓝 u.1, ContDiffAt ℝ 1 ψ x := hψc.eventually (by simp)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hev.and (hevV.and hevψ))
  -- h is constant on the ball
  set h : K → F := fun x => f (e (x, ψ x)) with hh
  have hderiv : ∀ x ∈ Metric.ball u.1 ε, HasFDerivAt h (0 : K →L[ℝ] F) x := by
    intro x hx
    obtain ⟨hgx, hxV, hψx⟩ := hball hx
    have hψd : DifferentiableAt ℝ ψ x := hψx.differentiableAt (by simp)
    set y := e (x, ψ x) with hy
    have hyU : y ∈ U := hVU hxV
    have hfy : HasFDerivAt f (fderiv ℝ f y) y :=
      ((hf.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by simp)).hasFDerivAt
    have hφ : HasFDerivAt (fun x : K => e (x, ψ x))
        ((e : K × K' →L[ℝ] E).comp ((ContinuousLinearMap.id ℝ K).prod (fderiv ℝ ψ x))) x :=
      e.hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk hψd.hasFDerivAt)
    have hhd : HasFDerivAt h ((fderiv ℝ f y).comp
        ((e : K × K' →L[ℝ] E).comp ((ContinuousLinearMap.id ℝ K).prod (fderiv ℝ ψ x)))) x :=
      hfy.comp x hφ
    -- the composite with π is locally constant
    have hπf : HasFDerivAt (π ∘ f) (π.comp (fderiv ℝ f y)) y := π.hasFDerivAt.comp y hfy
    have hgd' := hπf.comp x hφ
    have hgd : HasFDerivAt (fun x : K => π (f (e (x, ψ x)))) ((π.comp (fderiv ℝ f y)).comp
        ((e : K × K' →L[ℝ] E).comp ((ContinuousLinearMap.id ℝ K).prod (fderiv ℝ ψ x)))) x :=
      hgd'
    have hgconst : HasFDerivAt (fun x : K => π (f (e (x, ψ x)))) (0 : K →L[ℝ] R) x := by
      have hloc : (fun x : K => π (f (e (x, ψ x)))) =ᶠ[𝓝 x] fun _ => g u := by
        have hopen : IsOpen (Metric.ball u.1 ε) := Metric.isOpen_ball
        filter_upwards [hopen.mem_nhds hx] with z hz
        exact (hball hz).1
      exact (hasFDerivAt_const (g u) x).congr_of_eventuallyEq hloc
    have hzero := hgd.unique hgconst
    have hkerx := hker y hxV
    have : (fderiv ℝ f y).comp
        ((e : K × K' →L[ℝ] E).comp ((ContinuousLinearMap.id ℝ K).prod (fderiv ℝ ψ x))) = 0 := by
      ext v
      have hv : (e ((ContinuousLinearMap.id ℝ K).prod (fderiv ℝ ψ x) v)) ∈
          LinearMap.ker ((π : F →ₗ[ℝ] R).comp (fderiv ℝ f y : E →ₗ[ℝ] F)) := by
        rw [LinearMap.mem_ker]
        have := congrArg (fun L => L v) hzero
        simpa using this
      rw [hkerx, LinearMap.mem_ker] at hv
      simpa using hv
    rw [this] at hhd
    exact hhd
  have hconst : ∀ x ∈ Metric.ball u.1 ε, h x = h u.1 := by
    intro x hx
    have hdiff : DifferentiableOn ℝ h (Metric.ball u.1 ε) :=
      fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt
    refine (convex_ball u.1 ε).is_const_of_fderivWithin_eq_zero hdiff ?_ hx
      (Metric.mem_ball_self hε)
    intro z hz
    rw [fderivWithin_of_isOpen Metric.isOpen_ball hz, (hderiv z hz).fderiv]
  -- a second point in the ball
  obtain ⟨k, hk⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hKpos
  have hknorm : 0 < ‖k‖ := norm_pos_iff.mpr hk
  set x := u.1 + (ε / 2 / ‖k‖) • k with hx
  have hxball : x ∈ Metric.ball u.1 ε := by
    rw [Metric.mem_ball, dist_eq_norm, hx, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity), div_mul_cancel₀ _ hknorm.ne']
    linarith
  have hxne : x ≠ u.1 := by
    intro hxe
    rw [hx] at hxe
    have : (ε / 2 / ‖k‖) • k = 0 := by
      have := congrArg (fun z => z - u.1) hxe
      simpa using this
    rw [smul_eq_zero] at this
    rcases this with h1 | h1
    · have : ε / 2 / ‖k‖ > 0 := by positivity
      linarith
    · exact hk h1
  have h1 : h x = h u.1 := hconst x hxball
  have h2 : e (u.1, ψ u.1) = x₀ := by rw [hψu, Prod.mk.eta, heu]
  have hxU : e (x, ψ x) ∈ U := hVU (hball hxball).2.1
  have hinj' := hinj hxU hx₀U (by simpa [hh, h2] using h1)
  apply hxne
  have : (x, ψ x) = u := by
    have := congrArg e.symm hinj'
    rwa [e.symm_apply_apply, ← hu] at this
  exact congrArg Prod.fst this

end SmaleNinth.LB

/-!
Genericity: a nonempty open subset of `ℝ^p` contains a point avoiding the zero
sets of finitely many nonzero polynomials.
-/

open MvPolynomial Filter Topology

namespace SmaleNinth.LB

lemma analyticOnNhd_eval (p : ℕ) (P : MvPolynomial (Fin p) ℝ) :
    AnalyticOnNhd ℝ (fun x : Fin p → ℝ => eval x P) Set.univ := by
  have := AnalyticOnNhd.eval_continuousLinearMap (𝕜 := ℝ)
    (ContinuousLinearMap.id ℝ (Fin p → ℝ)) P
  simpa using this

lemma continuous_eval' (p : ℕ) (P : MvPolynomial (Fin p) ℝ) :
    Continuous (fun x : Fin p → ℝ => eval x P) := by
  exact continuousOn_univ.mp (analyticOnNhd_eval p P).continuousOn

lemma contDiff_eval' (p : ℕ) (P : MvPolynomial (Fin p) ℝ) :
    ContDiff ℝ 1 (fun x : Fin p → ℝ => eval x P) := by
  rw [← contDiffOn_univ]
  exact (analyticOnNhd_eval p P).contDiffOn (n := 1) uniqueDiffOn_univ

lemma eq_zero_of_eval_eq_zero_on_open (p : ℕ) (P : MvPolynomial (Fin p) ℝ)
    (U : Set (Fin p → ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (hP : ∀ x ∈ U, eval x P = 0) : P = 0 := by
  obtain ⟨u, hu⟩ := hne
  have h0 : (fun x : Fin p → ℝ => eval x P) =ᶠ[𝓝 u] 0 := by
    filter_upwards [hU.mem_nhds hu] with x hx using hP x hx
  have := (analyticOnNhd_eval p P).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ u) h0
  apply MvPolynomial.funext
  intro x
  simpa using this (Set.mem_univ x)

lemma isClosed_zeroSet (p : ℕ) (P : MvPolynomial (Fin p) ℝ) :
    IsClosed {x : Fin p → ℝ | eval x P = 0} :=
  isClosed_eq (continuous_eval' p P) continuous_const

/-- A nonempty open set contains a point at which every nonzero polynomial of a finite
family is nonzero. -/
lemma exists_avoid (p : ℕ) (S : Finset (MvPolynomial (Fin p) ℝ)) (U : Set (Fin p → ℝ))
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ u ∈ U, ∀ P ∈ S, P ≠ 0 → eval u P ≠ 0 := by
  classical
  induction S using Finset.induction_on generalizing U with
  | empty =>
    obtain ⟨u, hu⟩ := hne
    exact ⟨u, hu, by simp⟩
  | insert P S hPS ih =>
    by_cases hP : P = 0
    · obtain ⟨u, hu, h⟩ := ih U hU hne
      refine ⟨u, hu, fun Q hQ hQ0 => ?_⟩
      rcases Finset.mem_insert.mp hQ with rfl | hQ
      · exact absurd hP hQ0
      · exact h Q hQ hQ0
    · have hU' : IsOpen (U ∩ {x | eval x P ≠ 0}) :=
        hU.inter (isOpen_compl_iff.mpr (isClosed_zeroSet p P))
      have hne' : (U ∩ {x | eval x P ≠ 0}).Nonempty := by
        by_contra h
        rw [Set.not_nonempty_iff_eq_empty] at h
        apply hP
        apply eq_zero_of_eval_eq_zero_on_open p P U hU hne
        intro x hx
        by_contra hx'
        exact (Set.eq_empty_iff_forall_notMem.mp h x) ⟨hx, hx'⟩
      obtain ⟨u, ⟨hu, hu'⟩, h⟩ := ih _ hU' hne'
      refine ⟨u, hu, fun Q hQ hQ0 => ?_⟩
      rcases Finset.mem_insert.mp hQ with rfl | hQ
      · exact hu'
      · exact h Q hQ hQ0

end SmaleNinth.LB

/-!
Logical coordinates for the BSS machine, locality of a step, and the coupling of
two time-aligned runs across a boundary.
-/

open SmaleNinth

namespace SmaleNinth.LB

/-- The addresses used by an instruction. -/
def addrs : BSSInstr → List ℤ
  | .const dst _ => [dst]
  | .add dst i j => [dst, i, j]
  | .sub dst i j => [dst, i, j]
  | .mul dst i j => [dst, i, j]
  | .div dst i j => [dst, i, j]
  | .shiftL => []
  | .shiftR => []
  | .jle i _ => [i]
  | .accept => []
  | .reject => []

/-- All addresses of `P` lie in `[-W, W]`. -/
def AddrBound (P : BSSProgram) (W : ℤ) : Prop :=
  ∀ ins ∈ P, ∀ a ∈ addrs ins, -W ≤ a ∧ a ≤ W

/-- Every program has an address bound. -/
lemma exists_addrBound (P : BSSProgram) : ∃ W : ℤ, 0 ≤ W ∧ AddrBound P W := by
  refine ⟨(P.flatMap addrs).foldr (fun a m => max |a| m) 0, ?_, ?_⟩
  · induction P.flatMap addrs with
    | nil => simp
    | cons a l ih => simp only [List.foldr_cons]; exact le_max_of_le_right ih
  · intro ins hins a ha
    have hmem : a ∈ P.flatMap addrs := List.mem_flatMap.mpr ⟨ins, hins, ha⟩
    have key : ∀ l : List ℤ, a ∈ l → |a| ≤ l.foldr (fun a m => max |a| m) 0 := by
      intro l hl
      induction l with
      | nil => simp at hl
      | cons b l ih =>
        simp only [List.foldr_cons]
        rcases List.mem_cons.mp hl with rfl | hl
        · exact le_max_left _ _
        · exact le_max_of_le_right (ih hl)
    have := abs_le.mp (key _ hmem)
    exact ⟨this.1, this.2⟩

/-- The shift contributed by an instruction. -/
def shiftAmt : Option BSSInstr → ℤ
  | some .shiftL => 1
  | some .shiftR => -1
  | _ => 0

lemma shiftAmt_abs_le (ins : Option BSSInstr) : -1 ≤ shiftAmt ins ∧ shiftAmt ins ≤ 1 := by
  rcases ins with _ | ins
  · simp [shiftAmt]
  · cases ins <;> simp [shiftAmt]

/-- The tape offset after `t` steps: physical cell `k` at time `t` carries the logical
coordinate `k + off t`. -/
noncomputable def off (P : BSSProgram) (x : ℤ → ℝ) : ℕ → ℤ
  | 0 => 0
  | t + 1 => off P x t + shiftAmt (P[(BSSRun P x t).pc]?)

/-- The logical content at coordinate `c` after `t` steps. -/
noncomputable def cont (P : BSSProgram) (x : ℤ → ℝ) (t : ℕ) (c : ℤ) : ℝ :=
  (BSSRun P x t).tape (c - off P x t)

lemma cont_zero (P : BSSProgram) (x : ℤ → ℝ) (c : ℤ) : cont P x 0 c = x c := by
  simp [cont, off, BSSRun]

lemma BSSRun_succ (P : BSSProgram) (x : ℤ → ℝ) (t : ℕ) :
    BSSRun P x (t + 1) = BSSStep P (BSSRun P x t) := by
  unfold BSSRun; rw [Function.iterate_succ_apply']

/-- The program counter after one step. -/
def nextPc (ins : Option BSSInstr) (pc : ℕ) (test : Bool) : ℕ :=
  match ins with
  | none => pc
  | some .accept => pc
  | some .reject => pc
  | some (.jle _ target) => if test then target else pc + 1
  | some _ => pc + 1

/-- The tested address of an instruction (for `jle`), else `0`. -/
def testAddr : Option BSSInstr → ℤ
  | some (.jle i _) => i
  | _ => 0

/-- The new logical content at coordinate `c` after executing `ins` at offset `o`,
given the old content function `f`. -/
noncomputable def nextCont (ins : Option BSSInstr) (o : ℤ) (f : ℤ → ℝ) (c : ℤ) : ℝ :=
  match ins with
  | some (.const dst v) => if c = o + dst then v else f c
  | some (.add dst i j) => if c = o + dst then f (o + i) + f (o + j) else f c
  | some (.sub dst i j) => if c = o + dst then f (o + i) - f (o + j) else f c
  | some (.mul dst i j) => if c = o + dst then f (o + i) * f (o + j) else f c
  | some (.div dst i j) => if c = o + dst then f (o + i) / f (o + j) else f c
  | _ => f c

lemma pc_succ (P : BSSProgram) (x : ℤ → ℝ) (t : ℕ) :
    (BSSRun P x (t + 1)).pc = nextPc (P[(BSSRun P x t).pc]?) (BSSRun P x t).pc
      (decide (cont P x t (off P x t + testAddr (P[(BSSRun P x t).pc]?)) ≤ 0)) := by
  rw [BSSRun_succ]
  unfold BSSStep nextPc testAddr cont
  rcases h : P[(BSSRun P x t).pc]? with _ | ins
  · rfl
  · rcases ins with ⟨dst, v⟩ | ⟨dst, i, j⟩ | ⟨dst, i, j⟩ | ⟨dst, i, j⟩ | ⟨dst, i, j⟩ | _ | _ |
      ⟨i, target⟩ | _ | _
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · simp only [add_sub_cancel_left]
      by_cases htest : (BSSRun P x t).tape i ≤ 0 <;> simp [htest]
    · rfl
    · rfl

lemma cont_succ (P : BSSProgram) (x : ℤ → ℝ) (t : ℕ) (c : ℤ) :
    cont P x (t + 1) c = nextCont (P[(BSSRun P x t).pc]?) (off P x t) (cont P x t) c := by
  unfold cont
  rw [BSSRun_succ]
  show (BSSStep P (BSSRun P x t)).tape (c - (off P x t + shiftAmt (P[(BSSRun P x t).pc]?)))
    = nextCont (P[(BSSRun P x t).pc]?) (off P x t) (fun c => (BSSRun P x t).tape (c - off P x t)) c
  unfold BSSStep nextCont shiftAmt
  rcases h : P[(BSSRun P x t).pc]? with _ | ins
  · simp
  · rcases ins with ⟨dst, v⟩ | ⟨dst, i, j⟩ | ⟨dst, i, j⟩ | ⟨dst, i, j⟩ | ⟨dst, i, j⟩ | _ | _ |
      ⟨i, target⟩ | _ | _
    · simp only [add_zero, Function.update_apply]
      by_cases hc : c = off P x t + dst
      · simp [hc]
      · rw [if_neg (by omega), if_neg hc]
    · simp only [add_zero, Function.update_apply]
      by_cases hc : c = off P x t + dst
      · simp [hc]
      · rw [if_neg (by omega), if_neg hc]
    · simp only [add_zero, Function.update_apply]
      by_cases hc : c = off P x t + dst
      · simp [hc]
      · rw [if_neg (by omega), if_neg hc]
    · simp only [add_zero, Function.update_apply]
      by_cases hc : c = off P x t + dst
      · simp [hc]
      · rw [if_neg (by omega), if_neg hc]
    · simp only [add_zero, Function.update_apply]
      by_cases hc : c = off P x t + dst
      · simp [hc]
      · rw [if_neg (by omega), if_neg hc]
    · simp only []; congr 1; ring
    · simp only []; congr 1; ring
    · simp only [add_zero]; split_ifs <;> rfl
    · simp
    · simp

/-! ### Locality of `nextCont` -/

lemma nextCont_congr (ins : Option BSSInstr) (W o : ℤ)
    (hins : ∀ a ∈ ins.elim [] addrs, -W ≤ a ∧ a ≤ W) (f g : ℤ → ℝ)
    (hfg : ∀ c, o - W ≤ c → c ≤ o + W → f c = g c) (c : ℤ)
    (hc : o - W ≤ c ∧ c ≤ o + W) :
    nextCont ins o f c = nextCont ins o g c := by
  rcases ins with _ | ins
  · exact hfg c hc.1 hc.2
  · rcases ins with ⟨dst, v⟩ | ⟨dst, i, j⟩ | ⟨dst, i, j⟩ | ⟨dst, i, j⟩ | ⟨dst, i, j⟩ | _ | _ |
      ⟨i, target⟩ | _ | _ <;> simp only [nextCont, Option.elim, addrs] at hins ⊢
    · split_ifs <;> [rfl; exact hfg c hc.1 hc.2]
    all_goals first
      | (have hi := hins i (by simp); have hj := hins j (by simp)
         split_ifs
         · rw [hfg (o + i) (by omega) (by omega), hfg (o + j) (by omega) (by omega)]
         · exact hfg c hc.1 hc.2)
      | exact hfg c hc.1 hc.2

lemma nextCont_of_outside (ins : Option BSSInstr) (W o : ℤ)
    (hins : ∀ a ∈ ins.elim [] addrs, -W ≤ a ∧ a ≤ W) (f : ℤ → ℝ) (c : ℤ)
    (hc : c < o - W ∨ o + W < c) : nextCont ins o f c = f c := by
  rcases ins with _ | ins
  · rfl
  · rcases ins with ⟨dst, v⟩ | ⟨dst, i, j⟩ | ⟨dst, i, j⟩ | ⟨dst, i, j⟩ | ⟨dst, i, j⟩ | _ | _ |
      ⟨i, target⟩ | _ | _ <;> simp only [nextCont, Option.elim, addrs] at hins ⊢
    all_goals first
      | (have hd := hins dst (by simp); rw [if_neg (by omega)])
      | rfl

lemma nextCont_shift (ins : Option BSSInstr) (hs : shiftAmt ins ≠ 0) (o : ℤ) (f : ℤ → ℝ) (c : ℤ) :
    nextCont ins o f c = f c := by
  rcases ins with _ | ins
  · rfl
  · cases ins <;> simp [nextCont, shiftAmt] at hs ⊢

lemma testAddr_bound (ins : Option BSSInstr) (W : ℤ) (hW : 0 ≤ W)
    (hins : ∀ a ∈ ins.elim [] addrs, -W ≤ a ∧ a ≤ W) :
    -W ≤ testAddr ins ∧ testAddr ins ≤ W := by
  rcases ins with _ | ins
  · simp [testAddr]; omega
  · cases ins <;> simp only [testAddr, Option.elim, addrs] at hins ⊢ <;> try (constructor <;> omega)
    rename_i i target
    exact hins i (by simp)

/-! ### The coupling invariant -/

/-- The coupling invariant across boundary `β` with window `W`: the run on `y` agrees with
the run on `x` on the left region and zone, and with the run on `x'` on the right region,
in a left phase; and symmetrically in a right phase. -/
def Coupled (P : BSSProgram) (W β : ℤ) (x x' y : ℤ → ℝ) (t : ℕ) : Prop :=
  (BSSRun P y t).pc = (BSSRun P x t).pc ∧ off P y t = off P x t ∧
  (off P x t < β →
      (∀ c, c ≤ β + W → cont P y t c = cont P x t c) ∧
      (∀ c, β + W < c → cont P y t c = cont P x' t c)) ∧
  (β ≤ off P x t →
      (∀ c, β - W ≤ c → cont P y t c = cont P x' t c) ∧
      (∀ c, c < β - W → cont P y t c = cont P x t c))

/-- Offsets are determined by the program-counter sequence. -/
lemma off_eq_of_pc_eq (P : BSSProgram) (x x' : ℤ → ℝ) (T : ℕ)
    (h : ∀ t ≤ T, (BSSRun P x t).pc = (BSSRun P x' t).pc) :
    ∀ t ≤ T, off P x t = off P x' t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    simp only [off]
    rw [ih (by omega), h t (by omega)]

/-- A step of the run crosses the boundary `β`. -/
def Crosses (P : BSSProgram) (x : ℤ → ℝ) (β : ℤ) (t : ℕ) : Prop :=
  (off P x t < β ∧ β ≤ off P x (t + 1)) ∨ (off P x (t + 1) < β ∧ β ≤ off P x t)

/-- The coupling invariant propagates one step. -/
theorem coupled_step (P : BSSProgram) (W β : ℤ) (hW : 0 ≤ W) (hP : AddrBound P W)
    (x x' y : ℤ → ℝ) (t : ℕ)
    (hpc : (BSSRun P x t).pc = (BSSRun P x' t).pc)
    (hpc1 : (BSSRun P x (t + 1)).pc = (BSSRun P x' (t + 1)).pc)
    (hoff : off P x t = off P x' t)
    (hzone : Crosses P x β t → ∀ c, β - W ≤ c → c ≤ β + W → cont P x t c = cont P x' t c)
    (hc : Coupled P W β x x' y t) : Coupled P W β x x' y (t + 1) := by
  obtain ⟨hpcy, hoffy, hL, hR⟩ := hc
  set o := off P x t with ho
  set pc := (BSSRun P x t).pc with hpcdef
  set ins := P[pc]? with hinsdef
  have hins : ∀ a ∈ ins.elim [] addrs, -W ≤ a ∧ a ≤ W := by
    intro a ha
    rcases h : P[pc]? with _ | i
    · simp [hinsdef, h] at ha
    · rw [hinsdef, h] at ha
      exact hP i (List.mem_of_getElem? h) a ha
  -- offsets after the step
  have hoff' : off P x (t + 1) = o + shiftAmt ins := rfl
  have hoffy' : off P y (t + 1) = o + shiftAmt ins := by
    simp only [off]; rw [hoffy, hpcy]
  have hoffx' : off P x' (t + 1) = o + shiftAmt ins := by
    simp only [off]; rw [← hoff, ← hpc]
  -- contents after the step
  have hcx : ∀ c, cont P x (t + 1) c = nextCont ins o (cont P x t) c := cont_succ P x t
  have hcy : ∀ c, cont P y (t + 1) c = nextCont ins o (cont P y t) c := by
    intro c; rw [cont_succ, hpcy, hoffy]
  have hcx' : ∀ c, cont P x' (t + 1) c = nextCont ins o (cont P x' t) c := by
    intro c; rw [cont_succ, ← hpc, ← hoff]
  -- program counters after the step
  have hta := testAddr_bound ins W hW hins
  have hpcy' : (BSSRun P y (t + 1)).pc = (BSSRun P x (t + 1)).pc := by
    rw [pc_succ, pc_succ, hpcy, hoffy, ← hpcdef, ← hinsdef, ← ho]
    by_cases hlt : o < β
    · rw [(hL hlt).1 _ (by omega)]
    · have hge : β ≤ o := not_lt.mp hlt
      rw [(hR hge).1 _ (by omega)]
      have := hpc1
      rw [pc_succ, pc_succ, ← hpc, ← hoff, ← hpcdef, ← hinsdef, ← ho] at this
      exact this.symm
  refine ⟨hpcy', by rw [hoffy', hoff'], ?_, ?_⟩
  · -- left phase at t + 1
    intro hlt'
    rw [hoff'] at hlt'
    have hs := shiftAmt_abs_le ins
    by_cases hlt : o < β
    · -- stayed left
      obtain ⟨hL1, hL2⟩ := hL hlt
      by_cases hsh : shiftAmt ins = 0
      · refine ⟨fun c hc => ?_, fun c hc => ?_⟩
        · rw [hcy, hcx]
          rcases lt_or_ge c (o - W) with h1 | h1
          · rw [nextCont_of_outside ins W o hins _ c (Or.inl h1),
              nextCont_of_outside ins W o hins _ c (Or.inl h1)]
            exact hL1 c hc
          · rcases lt_or_ge (o + W) c with h2 | h2
            · rw [nextCont_of_outside ins W o hins _ c (Or.inr h2),
                nextCont_of_outside ins W o hins _ c (Or.inr h2)]
              exact hL1 c hc
            · exact nextCont_congr ins W o hins _ _ (fun c' h1' h2' => hL1 c' (by omega)) c
                ⟨h1, h2⟩
        · rw [hcy, hcx', nextCont_of_outside ins W o hins _ c (Or.inr (by omega)),
            nextCont_of_outside ins W o hins _ c (Or.inr (by omega))]
          exact hL2 c hc
      · -- a shift that keeps us left
        refine ⟨fun c hc => ?_, fun c hc => ?_⟩
        · rw [hcy, hcx, nextCont_shift ins hsh, nextCont_shift ins hsh]; exact hL1 c hc
        · rw [hcy, hcx', nextCont_shift ins hsh, nextCont_shift ins hsh]; exact hL2 c hc
    · -- crossed from right to left: a shift
      have hge : β ≤ o := not_lt.mp hlt
      obtain ⟨hR1, hR2⟩ := hR hge
      have hsh : shiftAmt ins ≠ 0 := by intro h; rw [h] at hlt'; omega
      have hcross : Crosses P x β t := Or.inr ⟨by rw [hoff']; exact hlt', hge⟩
      have hz := hzone hcross
      refine ⟨fun c hc => ?_, fun c hc => ?_⟩
      · rw [hcy, hcx, nextCont_shift ins hsh, nextCont_shift ins hsh]
        rcases lt_or_ge c (β - W) with h1 | h1
        · exact hR2 c h1
        · rw [hR1 c h1, hz c h1 hc]
      · rw [hcy, hcx', nextCont_shift ins hsh, nextCont_shift ins hsh]
        exact hR1 c (by omega)
  · -- right phase at t + 1
    intro hge'
    rw [hoff'] at hge'
    have hs := shiftAmt_abs_le ins
    by_cases hge : β ≤ o
    · -- stayed right
      obtain ⟨hR1, hR2⟩ := hR hge
      by_cases hsh : shiftAmt ins = 0
      · refine ⟨fun c hc => ?_, fun c hc => ?_⟩
        · rw [hcy, hcx']
          rcases lt_or_ge c (o - W) with h1 | h1
          · rw [nextCont_of_outside ins W o hins _ c (Or.inl h1),
              nextCont_of_outside ins W o hins _ c (Or.inl h1)]
            exact hR1 c hc
          · rcases lt_or_ge (o + W) c with h2 | h2
            · rw [nextCont_of_outside ins W o hins _ c (Or.inr h2),
                nextCont_of_outside ins W o hins _ c (Or.inr h2)]
              exact hR1 c hc
            · exact nextCont_congr ins W o hins _ _ (fun c' h1' h2' => hR1 c' (by omega)) c
                ⟨h1, h2⟩
        · rw [hcy, hcx, nextCont_of_outside ins W o hins _ c (Or.inl (by omega)),
            nextCont_of_outside ins W o hins _ c (Or.inl (by omega))]
          exact hR2 c hc
      · refine ⟨fun c hc => ?_, fun c hc => ?_⟩
        · rw [hcy, hcx', nextCont_shift ins hsh, nextCont_shift ins hsh]; exact hR1 c hc
        · rw [hcy, hcx, nextCont_shift ins hsh, nextCont_shift ins hsh]; exact hR2 c hc
    · -- crossed from left to right: a shift
      have hlt : o < β := not_le.mp hge
      obtain ⟨hL1, hL2⟩ := hL hlt
      have hsh : shiftAmt ins ≠ 0 := by intro h; rw [h] at hge'; omega
      have hcross : Crosses P x β t := Or.inl ⟨hlt, by rw [hoff']; exact hge'⟩
      have hz := hzone hcross
      refine ⟨fun c hc => ?_, fun c hc => ?_⟩
      · rw [hcy, hcx', nextCont_shift ins hsh, nextCont_shift ins hsh]
        rcases le_or_gt c (β + W) with h1 | h1
        · rw [hL1 c h1, hz c hc h1]
        · exact hL2 c h1
      · rw [hcy, hcx, nextCont_shift ins hsh, nextCont_shift ins hsh]
        exact hL1 c (by omega)

/-- The coupling invariant holds along the whole run. -/
theorem coupled_run (P : BSSProgram) (W β : ℤ) (hW : 0 ≤ W) (hP : AddrBound P W)
    (x x' y : ℤ → ℝ) (T : ℕ)
    (hpc : ∀ t ≤ T, (BSSRun P x t).pc = (BSSRun P x' t).pc)
    (hzone : ∀ t < T, Crosses P x β t → ∀ c, β - W ≤ c → c ≤ β + W →
      cont P x t c = cont P x' t c)
    (h0 : Coupled P W β x x' y 0) : ∀ t ≤ T, Coupled P W β x x' y t := by
  intro t
  induction t with
  | zero => intro _; exact h0
  | succ t ih =>
    intro ht
    exact coupled_step P W β hW hP x x' y t (hpc t (by omega)) (hpc (t + 1) ht)
      (off_eq_of_pc_eq P x x' T hpc t (by omega)) (hzone t (by omega)) (ih (by omega))

/-- Initial coupling: `y` agrees with `x` up to `β + W` and with `x'` beyond. -/
lemma coupled_zero (P : BSSProgram) (W β : ℤ) (hβ : 0 < β) (x x' y : ℤ → ℝ)
    (hy1 : ∀ c, c ≤ β + W → y c = x c) (hy2 : ∀ c, β + W < c → y c = x' c) :
    Coupled P W β x x' y 0 := by
  refine ⟨rfl, rfl, fun _ => ⟨fun c hc => ?_, fun c hc => ?_⟩, fun h => ?_⟩
  · rw [cont_zero, cont_zero]; exact hy1 c hc
  · rw [cont_zero, cont_zero]; exact hy2 c hc
  · exfalso; simp [off] at h; omega

end SmaleNinth.LB

/-!
Symbolic execution: cell contents as numerator/denominator polynomial pairs in
the input variables, a symbolic machine driven by a branch oracle, evaluation,
critical polynomials, and branch stability near a generic input.
-/

open SmaleNinth MvPolynomial Filter Topology

namespace SmaleNinth.LB

/-- A symbolic cell content. -/
structure Sym (p : ℕ) where
  num : MvPolynomial (Fin p) ℝ
  den : MvPolynomial (Fin p) ℝ

variable {p : ℕ}

namespace Sym

/-- Real evaluation (junk-tolerant). -/
noncomputable def ev (s : Sym p) (x : Fin p → ℝ) : ℝ := eval x s.num / eval x s.den

/-- A constant. -/
noncomputable def cst (c : ℝ) : Sym p := ⟨C c, 1⟩

/-- The `j`-th input variable. -/
noncomputable def var (j : Fin p) : Sym p := ⟨X j, 1⟩

noncomputable def add (a b : Sym p) : Sym p := ⟨a.num * b.den + b.num * a.den, a.den * b.den⟩
noncomputable def sub (a b : Sym p) : Sym p := ⟨a.num * b.den - b.num * a.den, a.den * b.den⟩
noncomputable def mul (a b : Sym p) : Sym p := ⟨a.num * b.num, a.den * b.den⟩
noncomputable def div (a b : Sym p) : Sym p :=
  if b.num = 0 then ⟨0, 1⟩ else ⟨a.num * b.den, a.den * b.num⟩

lemma ev_cst (c : ℝ) (x : Fin p → ℝ) : (cst c : Sym p).ev x = c := by simp [ev, cst]
lemma ev_var (j : Fin p) (x : Fin p → ℝ) : (var j : Sym p).ev x = x j := by simp [ev, var]

lemma ev_add (a b : Sym p) (x : Fin p → ℝ) (ha : eval x a.den ≠ 0) (hb : eval x b.den ≠ 0) :
    (add a b).ev x = a.ev x + b.ev x := by
  simp only [ev, add, map_add, map_mul]; field_simp

lemma ev_sub (a b : Sym p) (x : Fin p → ℝ) (ha : eval x a.den ≠ 0) (hb : eval x b.den ≠ 0) :
    (sub a b).ev x = a.ev x - b.ev x := by
  simp only [ev, sub, map_sub, map_mul]; field_simp

lemma ev_mul (a b : Sym p) (x : Fin p → ℝ) (ha : eval x a.den ≠ 0) (hb : eval x b.den ≠ 0) :
    (mul a b).ev x = a.ev x * b.ev x := by
  simp only [ev, mul, map_mul]; field_simp

lemma ev_div (a b : Sym p) (x : Fin p → ℝ) (ha : eval x a.den ≠ 0) (hb : eval x b.den ≠ 0)
    (hbn : b.num = 0 ∨ eval x b.num ≠ 0) :
    (div a b).ev x = a.ev x / b.ev x := by
  unfold div
  split_ifs with h
  · simp [ev, h]
  · rcases hbn with hbn | hbn
    · exact absurd hbn h
    · simp only [ev, map_mul]; field_simp

end Sym

/-- A symbolic configuration. -/
structure SymConfig (p : ℕ) where
  pc : ℕ
  tape : ℤ → Sym p

/-- One symbolic step; `b` is the oracle's decision for a `jle`. -/
noncomputable def symStep (P : BSSProgram) (b : Bool) (s : SymConfig p) : SymConfig p :=
  match P[s.pc]? with
  | none => s
  | some ins =>
    match ins with
    | .const dst c => ⟨s.pc + 1, Function.update s.tape dst (Sym.cst c)⟩
    | .add dst i j => ⟨s.pc + 1, Function.update s.tape dst (Sym.add (s.tape i) (s.tape j))⟩
    | .sub dst i j => ⟨s.pc + 1, Function.update s.tape dst (Sym.sub (s.tape i) (s.tape j))⟩
    | .mul dst i j => ⟨s.pc + 1, Function.update s.tape dst (Sym.mul (s.tape i) (s.tape j))⟩
    | .div dst i j => ⟨s.pc + 1, Function.update s.tape dst (Sym.div (s.tape i) (s.tape j))⟩
    | .shiftL => ⟨s.pc + 1, fun k => s.tape (k + 1)⟩
    | .shiftR => ⟨s.pc + 1, fun k => s.tape (k - 1)⟩
    | .jle _ target => if b then ⟨target, s.tape⟩ else ⟨s.pc + 1, s.tape⟩
    | .accept => s
    | .reject => s

/-- The symbolic run with branch oracle `br`. -/
noncomputable def symRun (P : BSSProgram) (br : ℕ → Bool) (x₀ : ℤ → Sym p) : ℕ → SymConfig p
  | 0 => ⟨0, x₀⟩
  | t + 1 => symStep P (br t) (symRun P br x₀ t)

lemma symRun_congr (P : BSSProgram) (br br' : ℕ → Bool) (x₀ : ℤ → Sym p) (T : ℕ)
    (h : ∀ t < T, br t = br' t) : ∀ t ≤ T, symRun P br x₀ t = symRun P br' x₀ t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih => intro ht; simp only [symRun]; rw [ih (by omega), h t (by omega)]

/-- Evaluation of a symbolic configuration at an input. -/
noncomputable def evConfig (s : SymConfig p) (x : Fin p → ℝ) : BSSConfig :=
  ⟨s.pc, fun k => (s.tape k).ev x⟩

/-- The real input tape obtained from a symbolic initial tape. -/
noncomputable def inp (x₀ : ℤ → Sym p) (x : Fin p → ℝ) : ℤ → ℝ := fun k => (x₀ k).ev x

/-- All denominators are nonzero at `x`. -/
def DenOK (s : SymConfig p) (x : Fin p → ℝ) : Prop := ∀ k, eval x (s.tape k).den ≠ 0

/-- The step is faithful at `x` with oracle value `b`. -/
def StepOK (P : BSSProgram) (s : SymConfig p) (x : Fin p → ℝ) (b : Bool) : Prop :=
  match P[s.pc]? with
  | some (.div _ _ j) => (s.tape j).num = 0 ∨ eval x (s.tape j).num ≠ 0
  | some (.jle i _) => b = decide ((s.tape i).ev x ≤ 0)
  | _ => True

/-- One symbolic step evaluates to one real step. -/
theorem step_ev (P : BSSProgram) (s : SymConfig p) (x : Fin p → ℝ) (b : Bool)
    (hden : DenOK s x) (hok : StepOK P s x b) :
    evConfig (symStep P b s) x = BSSStep P (evConfig s x) ∧ DenOK (symStep P b s) x := by
  unfold StepOK at hok
  unfold symStep BSSStep evConfig
  simp only []
  rcases h : P[s.pc]? with _ | ins
  · rw [h] at hok; exact ⟨rfl, hden⟩
  · rw [h] at hok
    rcases ins with ⟨dst, v⟩ | ⟨dst, i, j⟩ | ⟨dst, i, j⟩ | ⟨dst, i, j⟩ | ⟨dst, i, j⟩ | _ | _ |
      ⟨i, target⟩ | _ | _
    · refine ⟨?_, ?_⟩
      · congr 1; funext k; simp only [Function.update_apply]; split_ifs <;> simp [Sym.ev_cst]
      · intro k; simp only [Function.update_apply]; split_ifs
        · simp [Sym.cst]
        · exact hden k
    · refine ⟨?_, ?_⟩
      · congr 1; funext k; simp only [Function.update_apply]; split_ifs
        · exact Sym.ev_add _ _ x (hden i) (hden j)
        · rfl
      · intro k; simp only [Function.update_apply]; split_ifs
        · simp only [Sym.add, map_mul]; exact mul_ne_zero (hden i) (hden j)
        · exact hden k
    · refine ⟨?_, ?_⟩
      · congr 1; funext k; simp only [Function.update_apply]; split_ifs
        · exact Sym.ev_sub _ _ x (hden i) (hden j)
        · rfl
      · intro k; simp only [Function.update_apply]; split_ifs
        · simp only [Sym.sub, map_mul]; exact mul_ne_zero (hden i) (hden j)
        · exact hden k
    · refine ⟨?_, ?_⟩
      · congr 1; funext k; simp only [Function.update_apply]; split_ifs
        · exact Sym.ev_mul _ _ x (hden i) (hden j)
        · rfl
      · intro k; simp only [Function.update_apply]; split_ifs
        · simp only [Sym.mul, map_mul]; exact mul_ne_zero (hden i) (hden j)
        · exact hden k
    · refine ⟨?_, ?_⟩
      · congr 1; funext k; simp only [Function.update_apply]; split_ifs
        · exact Sym.ev_div _ _ x (hden i) (hden j) hok
        · rfl
      · intro k; simp only [Function.update_apply]; split_ifs
        · unfold Sym.div
          split_ifs with h0
          · simp
          · simp only [map_mul]
            rcases hok with hok | hok
            · exact absurd hok h0
            · exact mul_ne_zero (hden i) hok
        · exact hden k
    · exact ⟨rfl, fun k => hden (k + 1)⟩
    · exact ⟨rfl, fun k => hden (k - 1)⟩
    · refine ⟨?_, ?_⟩
      · rw [hok]
        by_cases ht : (s.tape i).ev x ≤ 0 <;> simp [ht]
      · intro k; by_cases hb : b <;> simp [hb] <;> exact hden k
    · exact ⟨rfl, hden⟩
    · exact ⟨rfl, hden⟩

/-- The run evaluates faithfully as long as every step is faithful. -/
theorem run_ev (P : BSSProgram) (br : ℕ → Bool) (x₀ : ℤ → Sym p) (x : Fin p → ℝ)
    (hx₀ : DenOK ⟨0, x₀⟩ x) (T : ℕ)
    (hok : ∀ t < T, StepOK P (symRun P br x₀ t) x (br t)) :
    ∀ t ≤ T, evConfig (symRun P br x₀ t) x = BSSRun P (inp x₀ x) t ∧
      DenOK (symRun P br x₀ t) x := by
  intro t
  induction t with
  | zero => intro _; exact ⟨rfl, hx₀⟩
  | succ t ih =>
    intro ht
    obtain ⟨h1, h2⟩ := ih (by omega)
    have := step_ev P (symRun P br x₀ t) x (br t) h2 (hok t (by omega))
    refine ⟨?_, this.2⟩
    rw [BSSRun_succ, ← h1]
    exact this.1

/-- The critical polynomials of a configuration: the divisor's numerator for a `div`,
the tested numerator for a `jle`. -/
noncomputable def critAt (P : BSSProgram) (s : SymConfig p) : Finset (MvPolynomial (Fin p) ℝ) :=
  match P[s.pc]? with
  | some (.div _ _ j) => {(s.tape j).num}
  | some (.jle i _) => {(s.tape i).num}
  | _ => ∅

/-- Extension of a finite branch prefix by `false`. -/
def ext (T : ℕ) (b : Fin T → Bool) : ℕ → Bool := fun t => if h : t < T then b ⟨t, h⟩ else false

/-- All critical polynomials of all branches of length `T`. -/
noncomputable def critAll (P : BSSProgram) (x₀ : ℤ → Sym p) (T : ℕ) :
    Finset (MvPolynomial (Fin p) ℝ) :=
  (Finset.univ : Finset (Fin T → Bool)).biUnion fun b =>
    (Finset.range T).biUnion fun t => critAt P (symRun P (ext T b) x₀ t)

/-- The oracle recorded by the real run at `u`. -/
noncomputable def realBranch (P : BSSProgram) (z : ℤ → ℝ) : ℕ → Bool := fun t =>
  decide ((BSSRun P z t).tape (testAddr (P[(BSSRun P z t).pc]?)) ≤ 0)

/-- A good neighbourhood for one step: the faithfulness conditions at `u` transfer to all
`x` near `u`. -/
lemma exists_nhd_stepOK (P : BSSProgram) (s : SymConfig p) (u : Fin p → ℝ) (hden : DenOK s u)
    (hcrit : ∀ Q ∈ critAt P s, Q ≠ 0 → eval u Q ≠ 0) :
    ∃ N : Set (Fin p → ℝ), IsOpen N ∧ u ∈ N ∧
      ∀ x ∈ N, StepOK P s x (decide (((evConfig s u).tape (testAddr (P[s.pc]?))) ≤ 0)) := by
  unfold StepOK critAt at *
  rcases h : P[s.pc]? with _ | ins
  · exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ _ => by dsimp only⟩
  · rcases ins with ⟨dst, v⟩ | ⟨dst, i, j⟩ | ⟨dst, i, j⟩ | ⟨dst, i, j⟩ | ⟨dst, i, j⟩ | _ | _ |
      ⟨i, target⟩ | _ | _
    all_goals try exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ _ => trivial⟩
    · -- div
      by_cases h0 : (s.tape j).num = 0
      · exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ _ => Or.inl h0⟩
      · have hnu : eval u (s.tape j).num ≠ 0 := hcrit _ (by rw [h]; simp) h0
        exact ⟨{x | eval x (s.tape j).num ≠ 0},
          isOpen_compl_iff.mpr (isClosed_zeroSet p _), hnu, fun x hx => Or.inr hx⟩
    · -- jle
      have hcrit' : (s.tape i).num ≠ 0 → eval u (s.tape i).num ≠ 0 := fun h0 => by
        apply hcrit _ _ h0; rw [h]; simp
      suffices hsuff : ∃ N : Set (Fin p → ℝ), IsOpen N ∧ u ∈ N ∧ ∀ x ∈ N,
          decide ((s.tape i).ev u ≤ 0) = decide ((s.tape i).ev x ≤ 0) by
        obtain ⟨N, hNo, huN, hN⟩ := hsuff
        refine ⟨N, hNo, huN, fun x hx => ?_⟩
        show decide (((evConfig s u).tape (testAddr (some (.jle i target)))) ≤ 0)
          = decide ((s.tape i).ev x ≤ 0)
        exact hN x hx
      by_cases h0 : (s.tape i).num = 0
      · exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun x _ => by simp [Sym.ev, h0]⟩
      · have hnu := hcrit' h0
        have hdu : eval u (s.tape i).den ≠ 0 := hden i
        by_cases hpos : 0 < eval u (s.tape i).num * eval u (s.tape i).den
        · refine ⟨{x | 0 < eval x (s.tape i).num * eval x (s.tape i).den},
            isOpen_lt continuous_const ((continuous_eval' p _).mul (continuous_eval' p _)), hpos,
            fun x hx => ?_⟩
          simp only [Set.mem_ofPred_eq] at hx
          have h1 : ¬ (s.tape i).ev u ≤ 0 := by
            simp only [Sym.ev]; rw [div_nonpos_iff, ← mul_nonpos_iff]; exact not_le.mpr hpos
          have h2 : ¬ (s.tape i).ev x ≤ 0 := by
            simp only [Sym.ev]; rw [div_nonpos_iff, ← mul_nonpos_iff]; exact not_le.mpr hx
          simp [h1, h2]
        · have hneg : eval u (s.tape i).num * eval u (s.tape i).den < 0 :=
            lt_of_le_of_ne (not_lt.mp hpos) (mul_ne_zero hnu hdu)
          refine ⟨{x | eval x (s.tape i).num * eval x (s.tape i).den < 0},
            isOpen_lt ((continuous_eval' p _).mul (continuous_eval' p _)) continuous_const, hneg,
            fun x hx => ?_⟩
          simp only [Set.mem_ofPred_eq] at hx
          have h1 : (s.tape i).ev u ≤ 0 := by
            simp only [Sym.ev]; rw [div_nonpos_iff, ← mul_nonpos_iff]; exact le_of_lt hneg
          have h2 : (s.tape i).ev x ≤ 0 := by
            simp only [Sym.ev]; rw [div_nonpos_iff, ← mul_nonpos_iff]; exact le_of_lt hx
          simp [h1, h2]

/-- **Branch stability.** Near a generic input `u`, the real run follows the branch of `u`
and evaluates the symbolic run. -/
theorem branch_stability (P : BSSProgram) (x₀ : ℤ → Sym p)
    (hx₀ : ∀ k x, eval x (x₀ k).den ≠ 0) (T : ℕ) (u : Fin p → ℝ)
    (hu : ∀ Q ∈ critAll P x₀ T, Q ≠ 0 → eval u Q ≠ 0) :
    ∃ (br : ℕ → Bool) (N : Set (Fin p → ℝ)), IsOpen N ∧ u ∈ N ∧
      ∀ x ∈ N, ∀ t ≤ T, evConfig (symRun P br x₀ t) x = BSSRun P (inp x₀ x) t ∧
        DenOK (symRun P br x₀ t) x := by
  set br := realBranch P (inp x₀ u) with hbr
  -- the symbolic run with `br` matches the real run at `u`
  have hden0 : ∀ x, DenOK (⟨0, x₀⟩ : SymConfig p) x := fun x k => hx₀ k x
  have hu_run : ∀ t ≤ T, evConfig (symRun P br x₀ t) u = BSSRun P (inp x₀ u) t ∧
      DenOK (symRun P br x₀ t) u := by
    intro t
    induction t with
    | zero => intro _; exact ⟨rfl, hden0 u⟩
    | succ t ih =>
      intro ht
      obtain ⟨h1, h2⟩ := ih (by omega)
      have hok : StepOK P (symRun P br x₀ t) u (br t) := by
        unfold StepOK
        rcases h : P[(symRun P br x₀ t).pc]? with _ | ins
        · trivial
        · rcases ins with ⟨dst, v⟩ | ⟨dst, i, j⟩ | ⟨dst, i, j⟩ | ⟨dst, i, j⟩ | ⟨dst, i, j⟩ | _ | _ |
            ⟨i, target⟩ | _ | _
          all_goals try trivial
          · -- div: the divisor numerator is critical
            by_cases h0 : ((symRun P br x₀ t).tape j).num = 0
            · exact Or.inl h0
            · right
              apply hu _ _ h0
              unfold critAll
              rw [Finset.mem_biUnion]
              refine ⟨fun s => br s, Finset.mem_univ _, ?_⟩
              rw [Finset.mem_biUnion]
              refine ⟨t, Finset.mem_range.mpr (by omega), ?_⟩
              rw [symRun_congr P (ext T fun s => br s) br x₀ T
                (fun s hs => by simp [ext, hs]) t (by omega)]
              unfold critAt; rw [h]; simp
          · -- jle: the oracle is the real test at `u`
            have hbt : br t = decide ((BSSRun P (inp x₀ u) t).tape
                (testAddr (P[(BSSRun P (inp x₀ u) t).pc]?)) ≤ 0) := rfl
            rw [hbt, ← h1]
            simp [evConfig, testAddr, h]
      have := step_ev P (symRun P br x₀ t) u (br t) h2 hok
      refine ⟨?_, this.2⟩
      rw [BSSRun_succ, ← h1]
      exact this.1
  -- good neighbourhoods for every step
  have hN : ∀ t < T, ∃ N : Set (Fin p → ℝ), IsOpen N ∧ u ∈ N ∧
      ∀ x ∈ N, StepOK P (symRun P br x₀ t) x (br t) := by
    intro t ht
    have hcrit : ∀ Q ∈ critAt P (symRun P br x₀ t), Q ≠ 0 → eval u Q ≠ 0 := by
      intro Q hQ hQ0
      apply hu _ _ hQ0
      unfold critAll
      rw [Finset.mem_biUnion]
      refine ⟨fun s => br s, Finset.mem_univ _, ?_⟩
      rw [Finset.mem_biUnion]
      refine ⟨t, Finset.mem_range.mpr ht, ?_⟩
      rwa [symRun_congr P (ext T fun s => br s) br x₀ T (fun s hs => by simp [ext, hs]) t
        (by omega)]
    obtain ⟨N, hNo, huN, hN⟩ := exists_nhd_stepOK P (symRun P br x₀ t) u (hu_run t (by omega)).2
      hcrit
    refine ⟨N, hNo, huN, fun x hx => ?_⟩
    have := hN x hx
    have hbrt : br t = decide (((evConfig (symRun P br x₀ t) u).tape
        (testAddr (P[(symRun P br x₀ t).pc]?))) ≤ 0) := by
      have hbt : br t = decide ((BSSRun P (inp x₀ u) t).tape
          (testAddr (P[(BSSRun P (inp x₀ u) t).pc]?)) ≤ 0) := rfl
      rw [hbt, ← (hu_run t (by omega)).1]
      rfl
    rw [hbrt]; exact this
  choose! N hNo huN hNok using hN
  refine ⟨br, ⋂ t ∈ Finset.range T, N t, ?_, ?_, ?_⟩
  · exact isOpen_biInter_finset fun t ht => hNo t (Finset.mem_range.mp ht)
  · exact Set.mem_iInter₂.mpr fun t ht => huN t (Finset.mem_range.mp ht)
  · intro x hx
    rw [Set.mem_iInter₂] at hx
    exact run_ev P br x₀ x (hden0 x) T
      (fun t ht => hNok t ht x (hx t (Finset.mem_range.mpr ht)))

end SmaleNinth.LB

/-!
Assembly of the lower bound: no uniform BSS program decides one-variable LP
feasibility in linear time.
-/

open SmaleNinth MvPolynomial Matrix LinearOptimization Filter Topology
open scoped Classical

namespace SmaleNinth.LB

/-! ### Halting facts -/

lemma step_of_halted (P : BSSProgram) (s : BSSConfig) (b : Bool) (h : BSSHaltedWith P s b) :
    BSSStep P s = s := by
  unfold BSSHaltedWith at h
  unfold BSSStep
  rw [h]
  cases b <;> rfl

lemma run_of_halted (P : BSSProgram) (x : ℤ → ℝ) (t : ℕ) (b : Bool)
    (h : BSSHaltedWith P (BSSRun P x t) b) : ∀ t' ≥ t, BSSRun P x t' = BSSRun P x t := by
  intro t' ht'
  induction t', ht' using Nat.le_induction with
  | base => rfl
  | succ t' _ ih => rw [BSSRun_succ, ih, step_of_halted P _ b h]

lemma halted_unique (P : BSSProgram) (x : ℤ → ℝ) (t t' : ℕ) (b b' : Bool)
    (h : BSSHaltedWith P (BSSRun P x t) b) (h' : BSSHaltedWith P (BSSRun P x t') b') : b = b' := by
  wlog hle : t ≤ t' generalizing t t' b b'
  · exact (this t' t b' b h' h (by omega)).symm
  rw [run_of_halted P x t b h t' hle] at h'
  unfold BSSHaltedWith at h h'
  rw [h] at h'
  cases b <;> cases b' <;> first | rfl | (simp at h')

/-! ### The instance family -/

/-- Coefficient (and right-hand side) of index `j`: the `j`-th variable for `j < p`, the
sentinel `-1` at `j = p`, and `0` beyond. -/
noncomputable def xval (p : ℕ) (x : Fin p → ℝ) (j : ℕ) : ℝ :=
  if h : j < p then x ⟨j, h⟩ else if j = p then -1 else 0

noncomputable def Amat (p m : ℕ) (x : Fin p → ℝ) : Matrix (Fin m) (Fin 1) ℝ :=
  fun i _ => xval p x i

noncomputable def bvec (p m : ℕ) (y : Fin p → ℝ) : Fin m → ℝ := fun i => xval p y i

lemma feasible_iff (p m : ℕ) (hpm : p < m) (x y : Fin p → ℝ) (hx : ∀ j, 0 < x j) :
    (polyhedron (Amat p m x) (bvec p m y)).Nonempty ↔ ∀ j, y j ≤ x j := by
  constructor
  · rintro ⟨z, hz⟩
    have hz' : ∀ i, bvec p m y i ≤ (Amat p m x *ᵥ z) i := hz
    have hsent := hz' ⟨p, hpm⟩
    simp only [bvec, Amat, xval, Matrix.mulVec, dotProduct, Fin.sum_univ_one, lt_irrefl,
      dite_false, if_true] at hsent
    intro j
    have hj := hz' ⟨j, by omega⟩
    simp only [bvec, Amat, xval, Matrix.mulVec, dotProduct, Fin.sum_univ_one, Fin.is_lt,
      dite_true] at hj
    have := hx j
    nlinarith
  · intro h
    refine ⟨fun _ => 1, fun i => ?_⟩
    simp only [bvec, Amat, xval, Matrix.mulVec, dotProduct, Fin.sum_univ_one, mul_one]
    split_ifs
    · exact h _
    · exact le_rfl
    · exact le_rfl

/-- The mixed input tape: coefficients from `x`, right-hand sides from `y`. -/
noncomputable def mixed (p m : ℕ) (x y : Fin p → ℝ) : ℤ → ℝ := encodeLP (Amat p m x) (bvec p m y)

lemma mixed_apply (p m : ℕ) (x y : Fin p → ℝ) (k : ℤ) :
    mixed p m x y k = if k = 0 then (m : ℝ) else if k = 1 then 1
      else if 2 ≤ k ∧ k < 2 + (m : ℤ) then xval p x (k - 2).toNat
      else if 2 + (m : ℤ) ≤ k ∧ k < 2 + (m : ℤ) + m then xval p y (k - 2 - m).toNat
      else 0 := by
  unfold mixed encodeLP
  simp only [Nat.cast_one, mul_one]
  by_cases h0 : k = 0
  · simp [h0]
  by_cases h1 : k = 1
  · simp [h1]
  rw [if_neg h0, if_neg h1, if_neg h0, if_neg h1]
  by_cases h2 : 2 ≤ k ∧ k < 2 + (m : ℤ)
  · rw [if_pos h2, if_pos h2]
    unfold matrixEntryRM
    rw [dif_pos ⟨by omega, by omega⟩]
    simp [Amat, Nat.div_one]
  · rw [if_neg h2, if_neg h2]
    by_cases h3 : 2 + (m : ℤ) ≤ k ∧ k < 2 + (m : ℤ) + m
    · rw [dif_pos h3, if_pos h3]
      show xval p y (k - (2 + (m : ℤ))).toNat = xval p y (k - 2 - m).toNat
      congr 1; omega
    · rw [dif_neg h3, if_neg h3]

/-- The symbolic initial tape of the family. -/
noncomputable def x₀ (p m : ℕ) : ℤ → Sym p := fun k =>
  if k = 0 then Sym.cst m else if k = 1 then Sym.cst 1
  else if h : 2 ≤ k ∧ k < 2 + (p : ℤ) then Sym.var ⟨(k - 2).toNat, by omega⟩
  else if k = 2 + (p : ℤ) then Sym.cst (-1)
  else if h : 2 + (m : ℤ) ≤ k ∧ k < 2 + (m : ℤ) + p then Sym.var ⟨(k - 2 - m).toNat, by omega⟩
  else if k = 2 + (m : ℤ) + p then Sym.cst (-1)
  else Sym.cst 0

lemma x₀_den (p m : ℕ) (k : ℤ) (x : Fin p → ℝ) : eval x (x₀ p m k).den ≠ 0 := by
  unfold x₀
  split_ifs <;> simp [Sym.cst, Sym.var]

lemma inp_x₀ (p m : ℕ) (hpm : p < m) (x : Fin p → ℝ) : inp (x₀ p m) x = mixed p m x x := by
  funext k
  rw [mixed_apply]
  unfold inp x₀
  by_cases h0 : k = 0
  · simp [h0, Sym.ev_cst]
  by_cases h1 : k = 1
  · simp [h1, Sym.ev_cst]
  rw [if_neg h0, if_neg h1, if_neg h0, if_neg h1]
  by_cases h2 : 2 ≤ k ∧ k < 2 + (p : ℤ)
  · rw [dif_pos h2, if_pos ⟨h2.1, by omega⟩, Sym.ev_var]
    unfold xval
    rw [dif_pos (by omega)]
  · rw [dif_neg h2]
    by_cases h3 : k = 2 + (p : ℤ)
    · rw [if_pos h3, if_pos ⟨by omega, by omega⟩, Sym.ev_cst]
      unfold xval
      rw [dif_neg (by omega), if_pos (by omega)]
    · rw [if_neg h3]
      by_cases h4 : 2 + (m : ℤ) ≤ k ∧ k < 2 + (m : ℤ) + p
      · rw [dif_pos h4, if_neg (by omega), if_pos ⟨h4.1, by omega⟩, Sym.ev_var]
        unfold xval
        rw [dif_pos (by omega)]
      · rw [dif_neg h4]
        by_cases h5 : k = 2 + (m : ℤ) + p
        · rw [if_pos h5, if_neg (by omega), if_pos ⟨by omega, by omega⟩, Sym.ev_cst]
          unfold xval
          rw [dif_neg (by omega), if_pos (by omega)]
        · rw [if_neg h5, Sym.ev_cst]
          by_cases h6 : 2 ≤ k ∧ k < 2 + (m : ℤ)
          · rw [if_pos h6]
            unfold xval
            rw [dif_neg (by omega), if_neg (by omega)]
          · rw [if_neg h6]
            by_cases h7 : 2 + (m : ℤ) ≤ k ∧ k < 2 + (m : ℤ) + m
            · rw [if_pos h7]
              unfold xval
              rw [dif_neg (by omega), if_neg (by omega)]
            · rw [if_neg h7]

/-- The mixed tape agrees with the pure `x` tape below the right-hand sides. -/
lemma mixed_left (p m : ℕ) (x y : Fin p → ℝ) (c : ℤ) (hc : c < 2 + (m : ℤ)) :
    mixed p m x y c = mixed p m x x c := by
  rw [mixed_apply, mixed_apply]
  split_ifs <;> first | rfl | omega

/-- The mixed tape agrees with the pure `y` tape above the active coefficients. -/
lemma mixed_right (p m : ℕ) (x y : Fin p → ℝ) (c : ℤ) (hc : (p : ℤ) + 1 < c) :
    mixed p m x y c = mixed p m y y c := by
  rw [mixed_apply, mixed_apply]
  split_ifs with h0 h1 h2 h3 <;> try rfl
  · unfold xval
    have : ¬ ((c - 2).toNat < p) := by omega
    rw [dif_neg this, dif_neg this]

/-! ### Counting crossings -/

lemma crosses_unique (P : BSSProgram) (x : ℤ → ℝ) (t : ℕ) (β β' : ℤ)
    (h : Crosses P x β t) (h' : Crosses P x β' t) : β = β' := by
  have hs := shiftAmt_abs_le (P[(BSSRun P x t).pc]?)
  have : off P x (t + 1) = off P x t + shiftAmt (P[(BSSRun P x t).pc]?) := rfl
  unfold Crosses at h h'
  omega

/-- The number of crossings of `β` before time `T`. -/
noncomputable def crossCount (P : BSSProgram) (x : ℤ → ℝ) (T : ℕ) (β : ℤ) : ℕ :=
  ((Finset.range T).filter (fun t => Crosses P x β t)).card

lemma sum_crossCount_le (P : BSSProgram) (x : ℤ → ℝ) (T : ℕ) (B : Finset ℤ) :
    ∑ β ∈ B, crossCount P x T β ≤ T := by
  classical
  unfold crossCount
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  calc ∑ t ∈ Finset.range T, ∑ β ∈ B, (if Crosses P x β t then 1 else 0)
      ≤ ∑ t ∈ Finset.range T, 1 := by
        apply Finset.sum_le_sum
        intro t _
        rw [← Finset.card_filter]
        rw [Finset.card_le_one]
        intro a ha b hb
        rw [Finset.mem_filter] at ha hb
        exact crosses_unique P x t a b ha.2 hb.2
    _ = T := by simp

lemma exists_few_crossings (P : BSSProgram) (x : ℤ → ℝ) (T : ℕ) (B : Finset ℤ) (K : ℕ)
    (hB : T < (K + 1) * B.card) : ∃ β ∈ B, crossCount P x T β ≤ K := by
  by_contra h
  push_neg at h
  have : (K + 1) * B.card ≤ ∑ β ∈ B, crossCount P x T β := by
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun β hβ => h β hβ
  have := sum_crossCount_le P x T B
  omega

/-! ### The main theorem -/

theorem no_linear_program (P : BSSProgram) (C : ℕ)
    (hcorr : ∀ (m : ℕ) (A : Matrix (Fin m) (Fin 1) ℝ) (b : Fin m → ℝ),
      ∃ result : Bool, BSSDecidesInTime P (encodeLP A b) (C * (m + 1)) result ∧
        (result = true ↔ (polyhedron A b).Nonempty)) : False := by
  classical
  obtain ⟨W, hW0, hPW⟩ := exists_addrBound P
  set Wn : ℕ := W.toNat with hWn
  have hWW : (Wn : ℤ) = W := Int.toNat_of_nonneg hW0
  -- parameters
  set p : ℕ := (C + 1) * (2 * Wn + 1) + 1 with hp
  set m : ℕ := (C + 1) * (p + 2 * Wn) + C + 1 with hm
  set T : ℕ := C * (m + 1) with hT
  have hpm : p < m := by
    have : (C + 1) * (p + 2 * Wn) ≥ p := by nlinarith
    omega
  set B : Finset ℤ := Finset.Icc ((p : ℤ) + W + 2) ((m : ℤ) + 1 - W) with hB
  have hBcard : B.card = m - p - 2 * Wn := by
    rw [hB, Int.card_Icc]
    have : (m : ℤ) + 1 - W + 1 - ((p : ℤ) + W + 2) = ((m - p - 2 * Wn : ℕ) : ℤ) := by
      rw [← hWW]
      have : p + 2 * Wn ≤ m := by
        have : (C + 1) * (p + 2 * Wn) ≥ p + 2 * Wn := by nlinarith
        omega
      omega
    rw [this, Int.toNat_natCast]
  have hTB : T < (C + 1 + 1) * B.card := by
    rw [hBcard, hT, hm]
    have hQ : (C + 1) * (p + 2 * Wn) + C + 1 - p - 2 * Wn = C * (p + 2 * Wn) + C + 1 := by
      have : (C + 1) * (p + 2 * Wn) = C * (p + 2 * Wn) + (p + 2 * Wn) := by ring
      omega
    rw [hQ]
    nlinarith
  -- the positive orthant
  set U₀ : Set (Fin p → ℝ) := {x | ∀ j, 0 < x j} with hU₀
  have hU₀open : IsOpen U₀ := by
    have : U₀ = ⋂ j, {x : Fin p → ℝ | 0 < x j} := by ext x; simp [hU₀]
    rw [this]
    exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (continuous_apply j)
  have hU₀ne : U₀.Nonempty := ⟨fun _ => 1, fun _ => one_pos⟩
  -- a generic point
  obtain ⟨u, huU, hu⟩ := exists_avoid p (critAll P (x₀ p m) T) U₀ hU₀open hU₀ne
  -- branch stability
  obtain ⟨br, N, hNopen, huN, hstab⟩ :=
    branch_stability P (x₀ p m) (fun k x => x₀_den p m k x) T u hu
  -- runs on the family
  have hrun : ∀ x ∈ N, ∀ t ≤ T, BSSRun P (mixed p m x x) t = evConfig (symRun P br (x₀ p m) t) x :=
    fun x hx t ht => by rw [← inp_x₀ p m hpm]; exact ((hstab x hx t ht).1).symm
  have hpcN : ∀ x ∈ N, ∀ t ≤ T, (BSSRun P (mixed p m x x) t).pc = (symRun P br (x₀ p m) t).pc :=
    fun x hx t ht => by rw [hrun x hx t ht]; rfl
  have hoffN : ∀ x ∈ N, ∀ t ≤ T, off P (mixed p m x x) t = off P (mixed p m u u) t := by
    intro x hx
    apply off_eq_of_pc_eq
    intro t ht
    rw [hpcN x hx t ht, hpcN u huN t ht]
  -- a boundary with few crossings
  obtain ⟨β, hβB, hβcross⟩ := exists_few_crossings P (mixed p m u u) T B (C + 1) hTB
  have hβ1 : (p : ℤ) + W + 2 ≤ β := (Finset.mem_Icc.mp hβB).1
  have hβ2 : β ≤ (m : ℤ) + 1 - W := (Finset.mem_Icc.mp hβB).2
  set Cr : Finset ℕ := (Finset.range T).filter (fun t => Crosses P (mixed p m u u) β t) with hCr
  have hCrcard : Cr.card ≤ C + 1 := by unfold crossCount at hβcross; exact hβcross
  -- the transcript map
  set q : ℕ := 2 * Wn + 1 with hq
  set o : ℕ → ℤ := off P (mixed p m u u) with ho
  set τ : (Fin p → ℝ) → (Cr → Fin q → ℝ) := fun x t k =>
    ((symRun P br (x₀ p m) t).tape ((β - W + (k : ℕ)) - o t)).ev x with hτ
  have hτcont : ∀ x ∈ N, ∀ t (ht : t ∈ Cr), ∀ k : Fin q,
      τ x ⟨t, ht⟩ k = cont P (mixed p m x x) t (β - W + k) := by
    intro x hx t ht k
    have htT : t ≤ T := by have := Finset.mem_range.mp (Finset.mem_filter.mp ht).1; omega
    simp only [hτ, cont]
    rw [hrun x hx t htT, hoffN x hx t htT]
    rfl
  -- the transcript map is C¹ on N
  have hτC1 : ContDiffOn ℝ 1 τ N := by
    rw [contDiffOn_pi]
    intro t
    rw [contDiffOn_pi]
    intro k
    have htT : (t : ℕ) ≤ T := by
      have := Finset.mem_range.mp (Finset.mem_filter.mp t.2).1; omega
    simp only [hτ, Sym.ev]
    apply ContDiffOn.div
    · exact (contDiff_eval' p _).contDiffOn
    · exact (contDiff_eval' p _).contDiffOn
    · intro x hx
      exact (hstab x hx t htT).2 _
  -- injectivity of the transcript on N ∩ U₀
  have hinj : Set.InjOn τ (N ∩ U₀) := by
    intro x ⟨hxN, hxU⟩ x' ⟨hx'N, hx'U⟩ hτeq
    -- coupling: the run on `mixed x x'` follows the run on `mixed x x`
    have hcouple : ∀ (a a' : Fin p → ℝ), a ∈ N → a' ∈ N → τ a = τ a' →
        ∀ t ≤ T, (BSSRun P (mixed p m a a') t).pc = (BSSRun P (mixed p m a a) t).pc := by
      intro a a' haN ha'N hτ t ht
      have hpc : ∀ t ≤ T, (BSSRun P (mixed p m a a) t).pc = (BSSRun P (mixed p m a' a') t).pc :=
        fun t ht => by rw [hpcN a haN t ht, hpcN a' ha'N t ht]
      have hzone : ∀ t < T, Crosses P (mixed p m a a) β t → ∀ c, β - W ≤ c → c ≤ β + W →
          cont P (mixed p m a a) t c = cont P (mixed p m a' a') t c := by
        intro t ht hcr c hc1 hc2
        have hcr' : Crosses P (mixed p m u u) β t := by
          unfold Crosses at hcr ⊢
          rw [hoffN a haN t (by omega), hoffN a haN (t + 1) (by omega)] at hcr
          exact hcr
        have htCr : t ∈ Cr := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht, hcr'⟩
        have hk : ((c - (β - W)).toNat) < q := by rw [hq]; omega
        have e1 := hτcont a haN t htCr ⟨(c - (β - W)).toNat, hk⟩
        have e2 := hτcont a' ha'N t htCr ⟨(c - (β - W)).toNat, hk⟩
        have hc' : β - W + (((c - (β - W)).toNat : ℕ) : ℤ) = c := by omega
        rw [hc'] at e1 e2
        rw [← e1, ← e2, hτ]
      have h0 : Coupled P W β (mixed p m a a) (mixed p m a' a') (mixed p m a a') 0 := by
        apply coupled_zero P W β (by omega)
        · intro c hc; exact mixed_left p m a a' c (by omega)
        · intro c hc; exact mixed_right p m a a' c (by omega)
      exact (coupled_run P W β hW0 hPW _ _ _ T hpc hzone h0 t ht).1
    -- verdicts
    have hverdict : ∀ (a a' : Fin p → ℝ), a ∈ N → a' ∈ N → τ a = τ a' →
        ((polyhedron (Amat p m a) (bvec p m a')).Nonempty ↔
          (polyhedron (Amat p m a) (bvec p m a)).Nonempty) := by
      intro a a' haN ha'N hτ
      obtain ⟨r1, hd1, hr1⟩ := hcorr m (Amat p m a) (bvec p m a')
      obtain ⟨r2, hd2, hr2⟩ := hcorr m (Amat p m a) (bvec p m a)
      obtain ⟨t2, ht2, hh2⟩ := hd2
      have hpc := hcouple a a' haN ha'N hτ t2 ht2
      have hh1 : BSSHaltedWith P (BSSRun P (mixed p m a a') t2) r2 := by
        unfold BSSHaltedWith at hh2 ⊢
        rw [hpc]; exact hh2
      obtain ⟨t1, _, hh1'⟩ := hd1
      have := halted_unique P (mixed p m a a') t1 t2 r1 r2 hh1' hh1
      rw [← hr1, ← hr2, this]
    have h1 := (hverdict x x' hxN hx'N hτeq).mp
    have h2 := (hverdict x' x hx'N hxN hτeq.symm).mp
    have hxx : ∀ j, x j ≤ x j := fun j => le_rfl
    have hfeas1 : ∀ j, x' j ≤ x j :=
      (feasible_iff p m hpm x x' hxU).mp ((hverdict x x' hxN hx'N hτeq).mpr
        ((feasible_iff p m hpm x x hxU).mpr hxx))
    have hfeas2 : ∀ j, x j ≤ x' j :=
      (feasible_iff p m hpm x' x hx'U).mp ((hverdict x' x hx'N hxN hτeq.symm).mpr
        ((feasible_iff p m hpm x' x' hx'U).mpr fun j => le_rfl))
    funext j
    exact le_antisymm (hfeas2 j) (hfeas1 j)
  -- dimension count
  have hdim : Module.finrank ℝ (Cr → Fin q → ℝ) < Module.finrank ℝ (Fin p → ℝ) := by
    rw [Module.finrank_pi_fintype, Module.finrank_fin_fun]
    simp only [Module.finrank_fin_fun, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
      smul_eq_mul]
    rw [hp, hq]
    calc Cr.card * (2 * Wn + 1) ≤ (C + 1) * (2 * Wn + 1) := by gcongr
      _ < (C + 1) * (2 * Wn + 1) + 1 := by omega
  exact not_injOn_of_finrank_lt τ (N ∩ U₀) (hNopen.inter hU₀open) ⟨u, huN, huU⟩
    (hτC1.mono Set.inter_subset_left) hdim hinj

end SmaleNinth.LB

open SmaleNinth Matrix LinearOptimization

theorem solution (P : BSSProgram) (C : ℕ) :
    ¬ ∀ (m : ℕ) (A : Matrix (Fin m) (Fin 1) ℝ) (b : Fin m → ℝ),
        ∃ result : Bool,
          BSSDecidesInTime P (encodeLP A b) (C * (m + 1)) result ∧
          (result = true ↔ (polyhedron A b).Nonempty) :=
  fun h => SmaleNinth.LB.no_linear_program P C h
