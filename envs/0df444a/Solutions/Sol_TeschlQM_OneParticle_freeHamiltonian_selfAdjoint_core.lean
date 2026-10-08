-- Prove2me | solution 1 for TeschlQM.OneParticle.freeHamiltonian_selfAdjoint_core
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-07T16:21:47.572115+00:00
-- url     : https://prove2.me/submissions/da544f7b-0294-4252-a7ca-c1de9506fc02

import Mathlib
import Definitions.Def_TeschlQM_OneParticle_multiplicationOperator
import Definitions.Def_TeschlQM_OneParticle_freeHamiltonian
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_OneParticle_essentialSpectrum
import Definitions.Def_TeschlQM_OneParticle_testFunctions

/-!
# Teschl, Theorem 7.8 and Lemma 7.9: the free Schrödinger operator

For `n ≥ 1`, `H₀ = F⁻¹ (2π|ξ|)² F` on `H²(ℝⁿ)` is self-adjoint, `σ_ess(H₀) = [0, ∞)` and
`C_c^∞(ℝⁿ)` is a core.

* `SDAux`: smooth compactly supported functions are dense in Schwartz space (truncation
  `ρ(x/R) φ(x)`, with explicit seminorm estimates).
* `FHAux` (basic part): `H₀` is symmetric and maximal on the Fourier side, hence self-adjoint once
  its domain is dense.
* `FHAux` (core part): Schwartz functions lie in `𝔇(H₀)` and approximate every element of `𝔇(H₀)`
  in the graph norm; combined with the density of `C_c^∞` in `𝓢` this gives the core property, and
  the density of `C_c^∞` in `L²` gives the dense domain.
* `FHAux` (spectral part): `H₀` has no eigenvalues (level sets of the symbol are spheres, which are
  Lebesgue-null), the resolvent off `[0, ∞)` is a Fourier multiplier, and every `t ≥ 0` is
  approximately an eigenvalue. Hence `σ(H₀) = σ_ess(H₀) = [0, ∞)`.
-/

open SchwartzMap Filter Topology Metric
open scoped ContDiff

namespace SDAux

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The fixed bump: `1` on the closed unit ball, supported in the ball of radius `2`. -/
noncomputable def bump : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩

/-- `η = 1 - ρ`. -/
noncomputable def eta (x : E) : ℝ := 1 - (bump : ContDiffBump (0 : E)) x

lemma eta_contDiff : ContDiff ℝ ∞ (eta (E := E)) :=
  contDiff_const.sub (bump : ContDiffBump (0 : E)).contDiff

/-- Uniform bounds for the derivatives of `η`. -/
lemma eta_deriv_bound (i : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ y : E, ‖iteratedFDeriv ℝ i eta y‖ ≤ K := by
  have hρ : ContDiff ℝ ∞ (bump : ContDiffBump (0 : E)) := (bump : ContDiffBump (0 : E)).contDiff (n := ⊤)
  have hc : Continuous (iteratedFDeriv ℝ i (bump : ContDiffBump (0 : E))) :=
    hρ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hcs : HasCompactSupport (iteratedFDeriv ℝ i (bump : ContDiffBump (0 : E))) :=
    (bump : ContDiffBump (0 : E)).hasCompactSupport.iteratedFDeriv i
  obtain ⟨M, hM⟩ := hc.norm.bddAbove_range_of_hasCompactSupport hcs.norm
  refine ⟨1 + max M 0, by positivity, fun y => ?_⟩
  have hsub : iteratedFDeriv ℝ i eta y = iteratedFDeriv ℝ i (fun _ : E => (1 : ℝ)) y -
      iteratedFDeriv ℝ i (bump : ContDiffBump (0 : E)) y := by
    have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := i) (x := y)
      (f := fun _ : E => (1 : ℝ)) (g := (bump : ContDiffBump (0 : E)))
      contDiff_const.contDiffAt (hρ.contDiffAt.of_le (by exact_mod_cast le_top))
    exact this
  have h1 : ‖iteratedFDeriv ℝ i (fun _ : E => (1 : ℝ)) y‖ ≤ 1 := by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · rw [iteratedFDeriv_const_of_ne hi.ne']; simp
  have h2 : ‖iteratedFDeriv ℝ i (bump : ContDiffBump (0 : E)) y‖ ≤ max M 0 :=
    (hM ⟨y, rfl⟩).trans (le_max_left _ _)
  rw [hsub]
  exact (norm_sub_le _ _).trans (add_le_add h1 h2)

/-- The rescaled cut-off `η_R(x) = η(x / R)`. -/
noncomputable def etaR (R : ℝ) (x : E) : ℝ := eta (R⁻¹ • x)

lemma etaR_contDiff (R : ℝ) : ContDiff ℝ ∞ (etaR (E := E) R) :=
  eta_contDiff.comp (contDiff_const_smul _)

lemma etaR_eq_comp (R : ℝ) :
    etaR (E := E) R = eta ∘ (R⁻¹ • ContinuousLinearMap.id ℝ E) := by
  ext x; simp [etaR]

lemma etaR_deriv_zero {R : ℝ} (hR : 0 < R) (i : ℕ) {x : E} (hx : ‖x‖ < R) :
    iteratedFDeriv ℝ i (etaR R) x = 0 := by
  have hev : etaR (E := E) R =ᶠ[𝓝 x] fun _ => 0 := by
    have : ball (0 : E) R ∈ 𝓝 x := isOpen_ball.mem_nhds (by simpa using hx)
    filter_upwards [this] with y hy
    simp only [etaR, eta]
    rw [ContDiffBump.one_of_mem_closedBall, sub_self]
    rw [mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hR]
    rw [mem_ball, dist_zero_right] at hy
    change R⁻¹ * ‖y‖ ≤ 1
    rw [inv_mul_le_iff₀ hR, mul_one]; exact hy.le
  rw [(hev.iteratedFDeriv ℝ i).eq_of_nhds]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · ext; simp
  · rw [iteratedFDeriv_const_of_ne hi.ne']; rfl

lemma etaR_deriv_bound (i : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ x : E,
    ‖iteratedFDeriv ℝ i (etaR R) x‖ ≤ K * (‖x‖ / R) := by
  obtain ⟨K, hK0, hK⟩ := eta_deriv_bound (E := E) i
  refine ⟨K, hK0, fun R hR x => ?_⟩
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  by_cases hx : ‖x‖ < R
  · rw [etaR_deriv_zero hR0 i hx, norm_zero]; positivity
  · push Not at hx
    have h1 : 1 ≤ ‖x‖ / R := by rw [le_div_iff₀ hR0, one_mul]; exact hx
    refine le_trans ?_ (le_mul_of_one_le_right hK0 h1)
    rw [etaR_eq_comp, ContinuousLinearMap.iteratedFDeriv_comp_right _ eta_contDiff _
      (by exact_mod_cast le_top)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have hL : ‖(R⁻¹ • ContinuousLinearMap.id ℝ E)‖ ≤ 1 := by
      refine (norm_smul_le (R⁻¹) (ContinuousLinearMap.id ℝ E)).trans ?_
      rw [norm_inv, Real.norm_eq_abs, abs_of_pos hR0]
      calc R⁻¹ * ‖ContinuousLinearMap.id ℝ E‖ ≤ R⁻¹ * 1 := by
            gcongr; exact ContinuousLinearMap.norm_id_le
        _ ≤ 1 := by rw [mul_one]; exact inv_le_one_of_one_le₀ hR
    calc ‖iteratedFDeriv ℝ i eta ((R⁻¹ • ContinuousLinearMap.id ℝ E) x)‖ *
          ∏ _j : Fin i, ‖(R⁻¹ • ContinuousLinearMap.id ℝ E)‖
        ≤ K * ∏ _j : Fin i, (1 : ℝ) := by
          gcongr
          · exact hK _
      _ = K := by simp

/-- The truncation `χ_R φ = ρ(x / R) φ` of a Schwartz function, `R = N + 1`. -/
noncomputable def trunc (N : ℕ) (φ : 𝓢(E, F)) : 𝓢(E, F) :=
  HasCompactSupport.toSchwartzMap
    (f := fun x => (bump : ContDiffBump (0 : E)) (((N : ℝ) + 1)⁻¹ • x) • φ x)
    (((bump : ContDiffBump (0 : E)).hasCompactSupport.comp_smul
      (inv_ne_zero (by positivity))).smul_right)
    (((bump : ContDiffBump (0 : E)).contDiff.comp (contDiff_const_smul _)).smul φ.smooth')

lemma trunc_apply (N : ℕ) (φ : 𝓢(E, F)) (x : E) :
    trunc N φ x = (bump : ContDiffBump (0 : E)) (((N : ℝ) + 1)⁻¹ • x) • φ x := rfl

lemma trunc_hasCompactSupport (N : ℕ) (φ : 𝓢(E, F)) : HasCompactSupport (trunc N φ) :=
  ((bump : ContDiffBump (0 : E)).hasCompactSupport.comp_smul
      (inv_ne_zero (by positivity))).smul_right

lemma sub_trunc_apply (N : ℕ) (φ : 𝓢(E, F)) :
    ((φ - trunc N φ : 𝓢(E, F)) : E → F) = fun x => etaR ((N : ℝ) + 1) x • φ x := by
  ext x
  simp [trunc_apply, etaR, eta, sub_smul]

lemma seminorm_sub_trunc_le (φ : 𝓢(E, F)) (k m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
    SchwartzMap.seminorm ℝ k m (φ - trunc N φ) ≤ C / ((N : ℝ) + 1) := by
  choose K hK0 hK using etaR_deriv_bound (E := E)
  set C : ℝ := ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * K i *
    SchwartzMap.seminorm ℝ (k + 1) (m - i) φ with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => by
    have := hK0 i; positivity
  refine ⟨C, hC0, fun N => ?_⟩
  set R : ℝ := (N : ℝ) + 1
  have hR1 : 1 ≤ R := by simp [R]
  have hR0 : 0 < R := by positivity
  refine SchwartzMap.seminorm_le_bound ℝ k m _ (by positivity) fun x => ?_
  rw [sub_trunc_apply]
  have hle := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (etaR_contDiff (E := E) R) φ.smooth' x
    (n := m) (by exact_mod_cast le_top)
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (fun x => etaR R x • φ x) x‖
      ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (etaR R) x‖ *
            ‖iteratedFDeriv ℝ (m - i) φ x‖ := by gcongr; exact hle
    _ = ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (etaR R) x‖ *
            (‖x‖ ^ k * ‖iteratedFDeriv ℝ (m - i) φ x‖) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * (K i * (‖x‖ / R)) *
            (‖x‖ ^ k * ‖iteratedFDeriv ℝ (m - i) φ x‖) := by
          gcongr with i hi
          exact hK i R hR1 x
    _ = (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * K i *
            (‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ (m - i) φ x‖)) / R := by
          rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => by ring
    _ ≤ C / R := by
          gcongr
          rw [hC]
          refine Finset.sum_le_sum fun i _ => ?_
          have := hK0 i
          gcongr
          exact SchwartzMap.le_seminorm ℝ (k + 1) (m - i) φ x

/-- Smooth compactly supported functions are dense in Schwartz space: the truncations converge. -/
theorem tendsto_trunc (φ : 𝓢(E, F)) : Tendsto (fun N : ℕ => trunc N φ) atTop (𝓝 φ) := by
  rw [(schwartz_withSeminorms ℝ E F).tendsto_nhds_atTop]
  rintro ⟨k, m⟩ ε hε
  obtain ⟨C, hC0, hC⟩ := seminorm_sub_trunc_le φ k m
  obtain ⟨N0, hN0⟩ := exists_nat_gt (C / ε)
  refine ⟨N0, fun N hN => ?_⟩
  rw [schwartzSeminormFamily_apply, map_sub_rev]
  refine (hC N).trans_lt ?_
  have hN' : C / ε < (N : ℝ) + 1 := by
    have : (N0 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  rw [div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ hε] at hN'
  linarith

end SDAux

open MeasureTheory TeschlQM.OneParticle ComplexConjugate
open scoped InnerProductSpace

namespace FHAux

variable {n : ℕ}

lemma inner_pt (a b : ℂ) : ⟪a, b⟫_ℂ = conj a * b := by simp [mul_comm]

lemma inner_L2 (f g : L2 n) : ⟪f, g⟫_ℂ = ∫ x, conj (f x) * g x := by
  rw [L2.inner_def]; simp only [inner_pt]

lemma symb_real (ξ : EuclideanSpace ℝ (Fin n)) : conj (laplaceSymbol n ξ) = laplaceSymbol n ξ := by
  unfold laplaceSymbol; exact Complex.conj_ofReal _

lemma continuous_symb : Continuous (laplaceSymbol n) := by
  unfold laplaceSymbol; fun_prop

lemma norm_symb_le (ξ : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hξ : ‖ξ‖ ≤ R) :
    ‖laplaceSymbol n ξ‖ ≤ (2 * Real.pi * R) ^ 2 := by
  unfold laplaceSymbol
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have : 0 ≤ ‖ξ‖ := norm_nonneg _
  gcongr

lemma mem_dom_iff (ψ : L2 n) : ψ ∈ (freeHamiltonian n).domain ↔
    MemLp (fun ξ => laplaceSymbol n ξ * (fourierL2 n ψ) ξ) 2 volume := Iff.rfl

lemma fH_apply (ψ : (freeHamiltonian n).domain) :
    freeHamiltonian n ψ = (fourierL2 n).symm
      ((show MemLp (fun ξ => laplaceSymbol n ξ * (fourierL2 n ψ) ξ) 2 volume from ψ.2).toLp _) :=
  rfl

lemma fourier_fH (ψ : (freeHamiltonian n).domain) :
    fourierL2 n (freeHamiltonian n ψ) =
      (show MemLp (fun ξ => laplaceSymbol n ξ * (fourierL2 n ψ) ξ) 2 volume from ψ.2).toLp _ := by
  rw [fH_apply, LinearIsometryEquiv.apply_symm_apply]

lemma fourier_fH_ae (ψ : (freeHamiltonian n).domain) :
    (fourierL2 n (freeHamiltonian n ψ) : _ → ℂ) =ᵐ[volume]
      fun ξ => laplaceSymbol n ξ * (fourierL2 n ψ) ξ := by
  rw [fourier_fH]; exact MemLp.coeFn_toLp _

/-- `H₀` is symmetric. -/
lemma fH_symm (x y : (freeHamiltonian n).domain) :
    ⟪freeHamiltonian n x, (y : L2 n)⟫_ℂ = ⟪(x : L2 n), freeHamiltonian n y⟫_ℂ := by
  rw [← LinearIsometryEquiv.inner_map_map (fourierL2 n),
    ← LinearIsometryEquiv.inner_map_map (fourierL2 n) (x : L2 n), inner_L2, inner_L2]
  apply integral_congr_ae
  filter_upwards [fourier_fH_ae x, fourier_fH_ae y] with ξ h1 h2
  rw [h1, h2, map_mul, symb_real]; ring

/-- Maximality on the Fourier side: if `⟪W, X⟫ = ⟪G, s X⟫` for every `X` with `s X ∈ L²`, then
`s G = W` almost everywhere. -/
lemma symb_max (G W : L2 n)
    (h : ∀ X : L2 n, ∀ hX : MemLp (fun ξ => laplaceSymbol n ξ * X ξ) 2 volume,
      ⟪W, X⟫_ℂ = ⟪G, hX.toLp _⟫_ℂ) :
    (fun ξ => laplaceSymbol n ξ * G ξ) =ᵐ[volume] (W : _ → ℂ) := by
  have hR : ∀ R : ℕ, (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R).indicator
      (fun ξ => laplaceSymbol n ξ * G ξ - W ξ) =ᵐ[volume] 0 := by
    intro R
    set B := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R
    set C : ℝ := (2 * Real.pi * R) ^ 2
    have hsm : AEStronglyMeasurable (laplaceSymbol n) volume :=
      continuous_symb.aestronglyMeasurable
    have hBm : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
    have h1 : MemLp (B.indicator (fun ξ => laplaceSymbol n ξ * G ξ)) 2 volume := by
      refine MemLp.of_le_mul (c := C) (Lp.memLp G) ?_ ?_
      · exact (hsm.mul (Lp.aestronglyMeasurable G)).indicator hBm
      · refine Filter.Eventually.of_forall fun ξ => ?_
        by_cases hξ : ξ ∈ B
        · rw [Set.indicator_of_mem hξ, norm_mul]
          gcongr
          exact norm_symb_le ξ (by simpa [B] using hξ)
        · rw [Set.indicator_of_notMem hξ, norm_zero]; positivity
    have h2 : MemLp (B.indicator (fun ξ => laplaceSymbol n ξ * G ξ - W ξ)) 2 volume := by
      have := h1.sub ((Lp.memLp W).indicator hBm)
      refine this.ae_eq (Filter.Eventually.of_forall fun ξ => ?_)
      by_cases hξ : ξ ∈ B
      · simp [Set.indicator_of_mem hξ]
      · simp [Set.indicator_of_notMem hξ]
    set X : L2 n := h2.toLp _ with hXdef
    have hXae := h2.coeFn_toLp
    have hXB : ∀ᵐ ξ ∂volume, ξ ∉ B → X ξ = 0 := by
      filter_upwards [hXae] with ξ hξ hξB
      rw [hξ, Set.indicator_of_notMem hξB]
    have hX : MemLp (fun ξ => laplaceSymbol n ξ * X ξ) 2 volume := by
      refine MemLp.of_le_mul (c := C) (Lp.memLp X) ?_ ?_
      · exact hsm.mul (Lp.aestronglyMeasurable X)
      · filter_upwards [hXB] with ξ hξ
        by_cases hξB : ξ ∈ B
        · rw [norm_mul]; gcongr; exact norm_symb_le ξ (by simpa [B] using hξB)
        · rw [hξ hξB]; simp
    have hmain := h X hX
    have hXX : ⟪X, X⟫_ℂ = 0 := by
      have e : ⟪X, X⟫_ℂ = ⟪G, hX.toLp _⟫_ℂ - ⟪W, X⟫_ℂ := by
        rw [L2.inner_def, L2.inner_def, L2.inner_def, ← integral_sub
          (L2.integrable_inner _ _) (L2.integrable_inner _ _)]
        apply integral_congr_ae
        filter_upwards [hXae, hX.coeFn_toLp] with ξ hξ hξ'
        simp only [inner_pt, hξ']
        by_cases hξB : ξ ∈ B
        · rw [hξ, Set.indicator_of_mem hξB, map_sub, map_mul, symb_real]; ring
        · rw [hξ, Set.indicator_of_notMem hξB]; simp
      rw [e, hmain, sub_self]
    have hX0 : X = 0 := inner_self_eq_zero.mp hXX
    have := hXae.symm.trans (show (X : _ → ℂ) =ᵐ[volume] 0 by
      rw [hX0]; exact Lp.coeFn_zero _ _ _)
    exact this
  have hR' : ∀ᵐ ξ ∂volume, ∀ R : ℕ, (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R).indicator
      (fun ξ => laplaceSymbol n ξ * G ξ - W ξ) ξ = 0 := ae_all_iff.mpr hR
  filter_upwards [hR'] with ξ hξ
  obtain ⟨R, hRξ⟩ := exists_nat_ge ‖ξ‖
  have := hξ R
  rw [Set.indicator_of_mem (by simpa using hRξ)] at this
  exact sub_eq_zero.mp this

lemma mem_dom_of_fourier (y : L2 n)
    (h : MemLp (fun ξ => laplaceSymbol n ξ * (fourierL2 n y) ξ) 2 volume) :
    y ∈ (freeHamiltonian n).domain := h

/-- `H₀` is self-adjoint (given that its domain is dense). -/
theorem fH_selfAdjoint_of_dense (fH_dense : Dense ((freeHamiltonian n).domain : Set (L2 n))) :
    IsSelfAdjoint (freeHamiltonian n) := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · -- adjoint ≤ H₀
    have hadj := LinearPMap.adjoint_isFormalAdjoint fH_dense
    have key : ∀ y : (freeHamiltonian n).adjoint.domain,
        (fun ξ => laplaceSymbol n ξ * (fourierL2 n (y : L2 n)) ξ) =ᵐ[volume]
          (fourierL2 n ((freeHamiltonian n).adjoint y) : _ → ℂ) := by
      intro y
      apply symb_max
      intro X hX
      set x : (freeHamiltonian n).domain := ⟨(fourierL2 n).symm X, by
        rw [mem_dom_iff, LinearIsometryEquiv.apply_symm_apply]; exact hX⟩ with hxdef
      have hFx : fourierL2 n (x : L2 n) = X := LinearIsometryEquiv.apply_symm_apply _ _
      have h1 := hadj y x
      rw [← LinearIsometryEquiv.inner_map_map (fourierL2 n),
        ← LinearIsometryEquiv.inner_map_map (fourierL2 n) (y : L2 n), hFx, fourier_fH] at h1
      rw [h1]
      congr 1
      apply MemLp.toLp_congr
      rw [hFx]
    refine ⟨fun y hy => ?_, fun y x hxy => ?_⟩
    · rw [mem_dom_iff]
      exact (Lp.memLp _).ae_eq (key ⟨y, hy⟩).symm
    · apply (fourierL2 n).injective
      rw [fourier_fH]
      ext1
      refine (key y).symm.trans ?_
      refine Filter.EventuallyEq.trans ?_ (MemLp.coeFn_toLp _).symm
      rw [hxy]
  · exact LinearPMap.IsFormalAdjoint.le_adjoint fH_dense (fun x y => fH_symm x y)

end FHAux

open MeasureTheory TeschlQM.OneParticle ComplexConjugate SchwartzMap FourierTransform Filter Topology
open scoped InnerProductSpace ContDiff

namespace FHAux

variable {n : ℕ}

lemma symb_temperate : (laplaceSymbol n).HasTemperateGrowth := by
  have h : laplaceSymbol n =
      fun ξ : EuclideanSpace ℝ (Fin n) => ((((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ) := by
    ext ξ; simp only [laplaceSymbol]; push_cast; ring
  rw [h]
  fun_prop

lemma fourierL2_eq (f : L2 n) : fourierL2 n f = 𝓕 f := rfl

lemma fourierL2_symm_eq (f : L2 n) : (fourierL2 n).symm f = 𝓕⁻ f := rfl

/-- The Fourier multiplier `H₀` on Schwartz space. -/
noncomputable def Lop (n : ℕ) : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
  fourierMultiplierCLM ℂ (laplaceSymbol n)

lemma schwartz_mem_dom (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    φ.toLp 2 volume ∈ (freeHamiltonian n).domain := by
  rw [mem_dom_iff, fourierL2_eq, SchwartzMap.toLp_fourier_eq]
  refine ((smulLeftCLM ℂ (laplaceSymbol n) (𝓕 φ)).memLp 2 (μ := volume)).ae_eq ?_
  filter_upwards [(𝓕 φ).coeFn_toLp 2 volume] with ξ hξ
  rw [hξ, smulLeftCLM_apply_apply symb_temperate, smul_eq_mul]

lemma fourier_toLp_ae (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    (fourierL2 n (φ.toLp 2 volume) : _ → ℂ) =ᵐ[volume]
      ⇑(𝓕 φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) := by
  rw [fourierL2_eq, SchwartzMap.toLp_fourier_eq]; exact (𝓕 φ).coeFn_toLp 2 volume

lemma fH_schwartz (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    freeHamiltonian n ⟨φ.toLp 2 volume, schwartz_mem_dom φ⟩ = (Lop n φ).toLp 2 volume := by
  have hS : MemLp (fun ξ => laplaceSymbol n ξ * (fourierL2 n (φ.toLp 2 volume)) ξ) 2 volume :=
    schwartz_mem_dom φ
  have e1 : freeHamiltonian n ⟨φ.toLp 2 volume, schwartz_mem_dom φ⟩ =
      (fourierL2 n).symm (hS.toLp _) := rfl
  have e2 : (hS.toLp _ : L2 n) = (smulLeftCLM ℂ (laplaceSymbol n) (𝓕 φ)).toLp 2 volume := by
    ext1
    filter_upwards [hS.coeFn_toLp, (smulLeftCLM ℂ (laplaceSymbol n) (𝓕 φ)).coeFn_toLp 2 volume,
      fourier_toLp_ae φ] with ξ h1 h2 h3
    rw [h1, h2, h3, smulLeftCLM_apply_apply symb_temperate, smul_eq_mul]
  rw [e1, e2, fourierL2_symm_eq, SchwartzMap.toLp_fourierInv_eq]
  rfl

lemma fourier_fH_sub_ae (x y : (freeHamiltonian n).domain) :
    (fourierL2 n (freeHamiltonian n x - freeHamiltonian n y) : _ → ℂ) =ᵐ[volume]
      fun ξ => laplaceSymbol n ξ * ((fourierL2 n (x : L2 n)) ξ - (fourierL2 n (y : L2 n)) ξ) := by
  rw [map_sub]
  filter_upwards [Lp.coeFn_sub (fourierL2 n (freeHamiltonian n x))
    (fourierL2 n (freeHamiltonian n y)), fourier_fH_ae x, fourier_fH_ae y] with ξ h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3, mul_sub]

lemma norm_symb_div_le (ξ : EuclideanSpace ℝ (Fin n)) :
    ‖laplaceSymbol n ξ‖ / (1 + ‖ξ‖ ^ 2) ≤ (2 * Real.pi) ^ 2 := by
  unfold laplaceSymbol
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    div_le_iff₀ (by positivity)]
  nlinarith [Real.pi_pos, sq_nonneg ‖ξ‖, sq_nonneg (2 * Real.pi)]

/-- Every element of `𝔇(H₀)` can be approximated in the graph norm by Schwartz functions. -/
lemma approx_schwartz (ψ : (freeHamiltonian n).domain) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), ‖φ.toLp 2 volume - (ψ : L2 n)‖ < ε ∧
      ‖(Lop n φ).toLp 2 volume - freeHamiltonian n ψ‖ < ε := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : L2 n, Ψ = fourierL2 n ψ := ⟨_, rfl⟩
  have hS : MemLp (fun ξ => laplaceSymbol n ξ * Ψ ξ) 2 volume := by rw [hΨ]; exact ψ.2
  obtain ⟨wR, hwR⟩ : ∃ wR : EuclideanSpace ℝ (Fin n) → ℝ, wR = fun ξ => 1 + ‖ξ‖ ^ 2 :=
    ⟨_, rfl⟩
  have hw1 : ∀ ξ, 1 ≤ wR ξ := fun ξ => by rw [hwR]; nlinarith [sq_nonneg ‖ξ‖]
  have hw0 : ∀ ξ, (wR ξ : ℂ) ≠ 0 := fun ξ => by
    have := hw1 ξ; exact_mod_cast (show wR ξ ≠ 0 by linarith)
  have hwΨ : MemLp (fun ξ => (wR ξ : ℂ) * Ψ ξ) 2 volume := by
    have := (Lp.memLp Ψ).add (hS.const_mul (((2 * Real.pi) ^ 2 : ℝ)⁻¹ : ℂ))
    refine this.ae_eq (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [Pi.add_apply, hwR, laplaceSymbol]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ε / ((2 * Real.pi) ^ 2 + 2) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  obtain ⟨g, hgc, hgs, hgn⟩ := hwΨ.exist_eLpNorm_sub_le (by norm_num) (by norm_num) hδ0
  have hwinv : ContDiff ℝ ∞ (fun ξ : EuclideanSpace ℝ (Fin n) => ((wR ξ)⁻¹ : ℝ)) := by
    rw [hwR]
    refine ContDiff.inv (contDiff_const.add (contDiff_norm_sq ℝ)) fun ξ => ?_
    positivity
  have hΦs : ContDiff ℝ ∞ (fun ξ => ((wR ξ)⁻¹ : ℝ) • g ξ) := hwinv.smul hgs
  have hΦc : HasCompactSupport (fun ξ => ((wR ξ)⁻¹ : ℝ) • g ξ) :=
    HasCompactSupport.smul_left (f := fun ξ => ((wR ξ)⁻¹ : ℝ)) hgc
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), ∀ ξ, Φ ξ = ((wR ξ)⁻¹ : ℝ) • g ξ :=
    ⟨hΦc.toSchwartzMap hΦs, fun ξ => by simp⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), φ = 𝓕⁻ Φ := ⟨_, rfl⟩
  have hFφ : fourierL2 n (φ.toLp 2 volume) = Φ.toLp 2 volume := by
    rw [hφ, ← SchwartzMap.toLp_fourierInv_eq, ← fourierL2_symm_eq,
      LinearIsometryEquiv.apply_symm_apply]
  have hD : MemLp (fun ξ => (wR ξ : ℂ) * Ψ ξ - g ξ) 2 volume :=
    hwΨ.sub (hgs.continuous.memLp_of_hasCompactSupport hgc)
  obtain ⟨D, hDdef⟩ : ∃ D : L2 n, D = hD.toLp _ := ⟨_, rfl⟩
  have hDn : ‖D‖ ≤ δ := by
    rw [hDdef, Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal hδ0.le (by simpa [Pi.sub_def] using hgn)
  have hpt : ∀ᵐ ξ ∂volume, (fourierL2 n (φ.toLp 2 volume)) ξ - Ψ ξ =
      -(((wR ξ)⁻¹ : ℝ) : ℂ) * D ξ := by
    rw [hFφ, hDdef]
    filter_upwards [Φ.coeFn_toLp 2 volume, hD.coeFn_toLp] with ξ h1 h2
    rw [h1, h2, hΦ]
    have := hw0 ξ
    simp only [Complex.real_smul]
    push_cast
    field_simp
    ring
  refine ⟨φ, ?_, ?_⟩
  · rw [← (fourierL2 n).norm_map, map_sub, ← hΨ]
    refine lt_of_le_of_lt (Lp.norm_le_mul_norm_of_ae_le_mul (c := 1) (g := D) ?_) ?_
    · filter_upwards [Lp.coeFn_sub (fourierL2 n (φ.toLp 2 volume)) Ψ, hpt] with ξ h1 h2
      rw [h1, Pi.sub_apply, h2, norm_mul, norm_neg, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_inv, abs_of_pos (by linarith [hw1 ξ])]
      exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ (hw1 ξ))
    · calc 1 * ‖D‖ ≤ δ := by rw [one_mul]; exact hDn
        _ < ε := by
          rw [hδ, div_lt_iff₀ (by positivity)]
          nlinarith [Real.pi_pos, sq_nonneg (2 * Real.pi)]
  · rw [← fH_schwartz φ, ← (fourierL2 n).norm_map]
    refine lt_of_le_of_lt
      (Lp.norm_le_mul_norm_of_ae_le_mul (c := (2 * Real.pi) ^ 2) (g := D) ?_) ?_
    · filter_upwards [fourier_fH_sub_ae ⟨φ.toLp 2 volume, schwartz_mem_dom φ⟩ ψ, hpt]
        with ξ h1 h2
      rw [h1]
      rw [← hΨ, h2, norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_inv,
        abs_of_pos (by linarith [hw1 ξ]), ← mul_assoc]
      gcongr
      have := norm_symb_div_le ξ
      rw [hwR]
      rwa [div_eq_mul_inv] at this
    · calc (2 * Real.pi) ^ 2 * ‖D‖ ≤ (2 * Real.pi) ^ 2 * δ := by gcongr
        _ < ε := by
          rw [hδ, mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith [Real.pi_pos, sq_nonneg (2 * Real.pi)]

lemma schwartz_cpt_mem_test (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (h : HasCompactSupport φ) :
    φ.toLp 2 volume ∈ testFunctions n :=
  ⟨φ, φ.smooth ⊤, h, φ.coeFn_toLp 2 volume⟩

lemma test_le_dom : testFunctions n ≤ (freeHamiltonian n).domain := by
  rintro ψ ⟨f, hf, hfc, hψ⟩
  have : ψ = (hfc.toSchwartzMap hf).toLp 2 volume := by
    ext1
    refine hψ.trans ?_
    filter_upwards [(hfc.toSchwartzMap hf).coeFn_toLp 2 volume] with x hx
    rw [hx]; simp
  rw [this]; exact schwartz_mem_dom _

lemma test_dense : Dense (testFunctions n : Set (L2 n)) := by
  rw [Metric.dense_iff]
  intro f r hr
  obtain ⟨g, hgc, hgs, hgn⟩ := (Lp.memLp f).exist_eLpNorm_sub_le (by norm_num) (by norm_num)
    (half_pos hr)
  have hgm : MemLp g 2 volume := hgs.continuous.memLp_of_hasCompactSupport hgc
  refine ⟨hgm.toLp g, ?_, ⟨g, hgs, hgc, hgm.coeFn_toLp⟩⟩
  rw [Metric.mem_ball, dist_comm, dist_eq_norm, Lp.norm_def]
  have hae : ((f - hgm.toLp g : L2 n) : _ → ℂ) =ᵐ[volume] (f : _ → ℂ) - g := by
    filter_upwards [Lp.coeFn_sub f (hgm.toLp g), hgm.coeFn_toLp] with x h1 h2
    rw [h1, Pi.sub_apply, h2, Pi.sub_apply]
  rw [eLpNorm_congr_ae hae]
  refine lt_of_le_of_lt (ENNReal.toReal_le_of_le_ofReal (half_pos hr).le hgn) (half_lt_self hr)

lemma fH_dense : Dense ((freeHamiltonian n).domain : Set (L2 n)) :=
  test_dense.mono test_le_dom

theorem fH_selfAdjoint : IsSelfAdjoint (freeHamiltonian n) :=
  fH_selfAdjoint_of_dense fH_dense

/-- Graph-norm approximation by test functions. -/
lemma approx_test (ψ : (freeHamiltonian n).domain) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : (freeHamiltonian n).domain, (y : L2 n) ∈ testFunctions n ∧
      ‖(y : L2 n) - (ψ : L2 n)‖ < ε ∧ ‖freeHamiltonian n y - freeHamiltonian n ψ‖ < ε := by
  obtain ⟨φ, h1, h2⟩ := approx_schwartz ψ (half_pos hε)
  have hc1 : Continuous fun f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) => f.toLp 2 volume :=
    (SchwartzMap.toLpCLM ℂ ℂ 2 volume).continuous
  have hc2 : Continuous fun f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) => (Lop n f).toLp 2 volume :=
    (SchwartzMap.toLpCLM ℂ ℂ 2 volume).continuous.comp (Lop n).continuous
  have ht := SDAux.tendsto_trunc φ
  have e1 := (hc1.tendsto φ).comp ht
  have e2 := (hc2.tendsto φ).comp ht
  have ev1 := (Metric.tendsto_nhds.mp e1) (ε / 2) (half_pos hε)
  have ev2 := (Metric.tendsto_nhds.mp e2) (ε / 2) (half_pos hε)
  obtain ⟨N, hN1, hN2⟩ := (ev1.and ev2).exists
  simp only [Function.comp_apply, dist_eq_norm] at hN1 hN2
  refine ⟨⟨(SDAux.trunc N φ).toLp 2 volume, schwartz_mem_dom _⟩,
    schwartz_cpt_mem_test _ (SDAux.trunc_hasCompactSupport N φ), ?_, ?_⟩
  · calc ‖(SDAux.trunc N φ).toLp 2 volume - (ψ : L2 n)‖
        = ‖((SDAux.trunc N φ).toLp 2 volume - φ.toLp 2 volume) +
            (φ.toLp 2 volume - (ψ : L2 n))‖ := by abel_nf
      _ ≤ _ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hN1 h1
      _ = ε := add_halves ε
  · rw [fH_schwartz]
    calc ‖(Lop n (SDAux.trunc N φ)).toLp 2 volume - freeHamiltonian n ψ‖
        = ‖((Lop n (SDAux.trunc N φ)).toLp 2 volume - (Lop n φ).toLp 2 volume) +
            ((Lop n φ).toLp 2 volume - freeHamiltonian n ψ)‖ := by abel_nf
      _ ≤ _ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hN2 h2
      _ = ε := add_halves ε

/-- `C_c^∞(ℝⁿ)` is a core for `H₀`. -/
theorem fH_hasCore : (freeHamiltonian n).HasCore (testFunctions n) := by
  refine ⟨test_le_dom, ?_⟩
  have hcl : (freeHamiltonian n).IsClosed := fH_selfAdjoint.isClosed
  have hle : (freeHamiltonian n).domRestrict (testFunctions n) ≤ freeHamiltonian n :=
    LinearPMap.domRestrict_le
  have hTc : ((freeHamiltonian n).domRestrict (testFunctions n)).IsClosable :=
    hcl.isClosable.leIsClosable hle
  apply le_antisymm
  · have h1 := hcl.isClosable.closure_mono hle
    have h2 : (freeHamiltonian n).closure = freeHamiltonian n := by
      apply LinearPMap.eq_of_eq_graph
      rw [← hcl.isClosable.graph_closure_eq_closure_graph]
      exact hcl.submodule_topologicalClosure_eq
    rwa [h2] at h1
  · apply LinearPMap.le_of_le_graph
    rw [← hTc.graph_closure_eq_closure_graph]
    intro p hp
    rw [LinearPMap.mem_graph_iff] at hp
    obtain ⟨y, hy1, hy2⟩ := hp
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨z, hzD, hz1, hz2⟩ := approx_test y hε
    refine ⟨((z : L2 n), freeHamiltonian n z), ?_, ?_⟩
    · rw [SetLike.mem_coe, LinearPMap.mem_graph_iff]
      refine ⟨⟨(z : L2 n), ⟨hzD, z.2⟩⟩, rfl, ?_⟩
      exact LinearPMap.domRestrict_apply rfl
    · rw [Prod.dist_eq, max_lt_iff, ← hy1, ← hy2, dist_eq_norm, dist_eq_norm, norm_sub_rev,
        norm_sub_rev (freeHamiltonian n y)]
      exact ⟨hz1, hz2⟩

end FHAux

open MeasureTheory TeschlQM.OneParticle ComplexConjugate Filter Topology
open scoped InnerProductSpace

namespace FHAux

variable {n : ℕ}

/-! ### No eigenvalues -/

lemma symb_eq_imp (ξ : EuclideanSpace ℝ (Fin n)) (z : ℂ) (h : laplaceSymbol n ξ = z) :
    ξ ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt z.re / (2 * Real.pi)) := by
  rw [mem_sphere_zero_iff_norm, eq_div_iff (by positivity)]
  have hre : z.re = (2 * Real.pi * ‖ξ‖) ^ 2 := by rw [← h]; unfold laplaceSymbol; exact Complex.ofReal_re _
  rw [hre, Real.sqrt_sq (by positivity)]; ring

lemma eigenspace_fH_eq_bot (hn : 1 ≤ n) (z : ℂ) : eigenspace (freeHamiltonian n) z = ⊥ := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    infer_instance
  rw [eq_bot_iff]
  rintro ψ ⟨v, hv, rfl⟩
  rw [Submodule.mem_bot]
  have hv' : freeHamiltonian n v = z • (v : L2 n) := by
    have hv0 : (freeHamiltonian n).toFun v - z • (v : L2 n) = 0 := hv
    exact sub_eq_zero.mp hv0
  have hae := fourier_fH_ae v
  rw [hv', map_smul] at hae
  have hnull : volume {ξ : EuclideanSpace ℝ (Fin n) | laplaceSymbol n ξ = z} = 0 :=
    measure_mono_null (fun ξ hξ => symb_eq_imp ξ z hξ) (Measure.addHaar_sphere volume _ _)
  have h0 : (fourierL2 n (v : L2 n) : _ → ℂ) =ᵐ[volume] (0 : L2 n) := by
    have hne : ∀ᵐ ξ ∂volume, laplaceSymbol n ξ ≠ z := by
      rw [ae_iff]; simpa using hnull
    filter_upwards [hae, Lp.coeFn_smul z (fourierL2 n (v : L2 n)), hne,
      Lp.coeFn_zero ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))] with ξ h1 h2 h3 h4
    rw [h4, Pi.zero_apply]
    rw [h2, Pi.smul_apply, smul_eq_mul] at h1
    have : (laplaceSymbol n ξ - z) * (fourierL2 n (v : L2 n)) ξ = 0 := by
      rw [sub_mul, ← h1, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h3)
  have : fourierL2 n (v : L2 n) = 0 := Lp.ext h0
  simpa using this

/-! ### Bounded multiplication operators -/

lemma memLp_mul_bdd {m : EuclideanSpace ℝ (Fin n) → ℂ} (hm : AEStronglyMeasurable m volume)
    {C : ℝ} (hC : ∀ ξ, ‖m ξ‖ ≤ C) (f : L2 n) : MemLp (fun ξ => m ξ * f ξ) 2 volume :=
  MemLp.of_le_mul (c := C) (Lp.memLp f) (hm.mul (Lp.aestronglyMeasurable f))
    (Eventually.of_forall fun ξ => by rw [norm_mul]; gcongr; exact hC ξ)

/-- Multiplication by a bounded measurable function, as a bounded operator on `L²`. -/
noncomputable def mulCLM {m : EuclideanSpace ℝ (Fin n) → ℂ} (hm : AEStronglyMeasurable m volume)
    {C : ℝ} (hC : ∀ ξ, ‖m ξ‖ ≤ C) : L2 n →L[ℂ] L2 n :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_mul_bdd hm hC f).toLp _
      map_add' := fun f g => by
        ext1
        filter_upwards [(memLp_mul_bdd hm hC (f + g)).coeFn_toLp,
          (memLp_mul_bdd hm hC f).coeFn_toLp, (memLp_mul_bdd hm hC g).coeFn_toLp,
          Lp.coeFn_add f g, Lp.coeFn_add ((memLp_mul_bdd hm hC f).toLp _)
            ((memLp_mul_bdd hm hC g).toLp _)] with ξ h1 h2 h3 h4 h5
        rw [h5, Pi.add_apply, h1, h2, h3, h4, Pi.add_apply, mul_add]
      map_smul' := fun c f => by
        ext1
        filter_upwards [(memLp_mul_bdd hm hC (c • f)).coeFn_toLp,
          (memLp_mul_bdd hm hC f).coeFn_toLp, Lp.coeFn_smul c f,
          Lp.coeFn_smul c ((memLp_mul_bdd hm hC f).toLp _)] with ξ h1 h2 h3 h4
        rw [RingHom.id_apply, h4, Pi.smul_apply, h1, h2, h3, Pi.smul_apply, smul_eq_mul,
          smul_eq_mul]
        ring }
    C (fun f => by
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [(memLp_mul_bdd hm hC f).coeFn_toLp] with ξ h1
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [h1, norm_mul]; gcongr; exact hC ξ)

lemma mulCLM_ae {m : EuclideanSpace ℝ (Fin n) → ℂ} (hm : AEStronglyMeasurable m volume)
    {C : ℝ} (hC : ∀ ξ, ‖m ξ‖ ≤ C) (f : L2 n) :
    (mulCLM hm hC f : _ → ℂ) =ᵐ[volume] fun ξ => m ξ * f ξ :=
  (memLp_mul_bdd hm hC f).coeFn_toLp

lemma fourier_sub_smul_ae (v : (freeHamiltonian n).domain) (z : ℂ) :
    (fourierL2 n (freeHamiltonian n v - z • (v : L2 n)) : _ → ℂ) =ᵐ[volume]
      fun ξ => (laplaceSymbol n ξ - z) * (fourierL2 n (v : L2 n)) ξ := by
  rw [map_sub, map_smul]
  filter_upwards [Lp.coeFn_sub (fourierL2 n (freeHamiltonian n v)) (z • fourierL2 n (v : L2 n)),
    Lp.coeFn_smul z (fourierL2 n (v : L2 n)), fourier_fH_ae v] with ξ h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3, Pi.smul_apply, smul_eq_mul, sub_mul]

/-! ### The resolvent off `[0, ∞)` -/

lemma resolvent_of_not_mem (z : ℂ) (hz : z ∉ (fun t : ℝ => (t : ℂ)) '' Set.Ici 0) :
    z ∈ TeschlQM.Shared.resolventSet (freeHamiltonian n) := by
  set c : ℝ := max |z.im| (-z.re) with hcdef
  have hc : 0 < c := by
    by_contra h
    push Not at h
    have him : z.im = 0 := abs_nonpos_iff.mp ((le_max_left _ _).trans h)
    have hre : 0 ≤ z.re := by linarith [(le_max_right |z.im| (-z.re)).trans h]
    exact hz ⟨z.re, hre, Complex.ext (by simp) (by simp [him])⟩
  have hbd : ∀ ξ, c ≤ ‖laplaceSymbol n ξ - z‖ := by
    intro ξ
    have hs_re : (laplaceSymbol n ξ).re = (2 * Real.pi * ‖ξ‖) ^ 2 := by
      unfold laplaceSymbol; exact Complex.ofReal_re _
    have hs_im : (laplaceSymbol n ξ).im = 0 := by
      unfold laplaceSymbol; exact Complex.ofReal_im _
    refine max_le ?_ ?_
    · have := Complex.abs_im_le_norm (laplaceSymbol n ξ - z)
      rwa [Complex.sub_im, hs_im, zero_sub, abs_neg] at this
    · have h1 := Complex.re_le_norm (laplaceSymbol n ξ - z)
      rw [Complex.sub_re, hs_re] at h1
      nlinarith [sq_nonneg (2 * Real.pi * ‖ξ‖)]
  have hne : ∀ ξ, laplaceSymbol n ξ - z ≠ 0 := fun ξ h => by
    have := hbd ξ; rw [h, norm_zero] at this; linarith
  set m : EuclideanSpace ℝ (Fin n) → ℂ := fun ξ => (laplaceSymbol n ξ - z)⁻¹ with hmdef
  have hmc : Continuous m := (continuous_symb.sub continuous_const).inv₀ hne
  have hmb : ∀ ξ, ‖m ξ‖ ≤ c⁻¹ := fun ξ => by
    simp only [m, norm_inv]
    exact inv_anti₀ hc (hbd ξ)
  set M := mulCLM hmc.aestronglyMeasurable hmb
  set R : L2 n →L[ℂ] L2 n := ((fourierL2 n).symm : L2 n →L[ℂ] L2 n) ∘L M ∘L
    (fourierL2 n : L2 n →L[ℂ] L2 n) with hRdef
  have hFR : ∀ φ, fourierL2 n (R φ) = M (fourierL2 n φ) := fun φ => by
    simp [R]
  refine ⟨R, fun φ => ?_, fun ψ => ?_⟩
  · have hFRae : (fourierL2 n (R φ) : _ → ℂ) =ᵐ[volume] fun ξ => m ξ * (fourierL2 n φ) ξ := by
      rw [hFR]; exact mulCLM_ae _ _ _
    have hdom : R φ ∈ (freeHamiltonian n).domain := by
      rw [mem_dom_iff]
      refine ((Lp.memLp (fourierL2 n φ)).add ((Lp.memLp (M (fourierL2 n φ))).const_mul z)).ae_eq ?_
      filter_upwards [hFRae, mulCLM_ae hmc.aestronglyMeasurable hmb (fourierL2 n φ)]
        with ξ h1 h2
      rw [h1, Pi.add_apply, h2]
      have := hne ξ
      simp only [m]
      field_simp
      ring
    refine ⟨hdom, ?_⟩
    apply (fourierL2 n).injective
    ext1
    filter_upwards [fourier_sub_smul_ae ⟨R φ, hdom⟩ z, hFRae] with ξ h1 h2
    rw [h1]
    rw [h2]
    have := hne ξ
    simp only [m]
    field_simp
  · apply (fourierL2 n).injective
    rw [hFR]
    ext1
    filter_upwards [mulCLM_ae hmc.aestronglyMeasurable hmb
      (fourierL2 n (freeHamiltonian n ψ - z • (ψ : L2 n))), fourier_sub_smul_ae ψ z] with ξ h1 h2
    rw [h1, h2]
    have := hne ξ
    simp only [m]
    field_simp

/-! ### `[0, ∞)` lies in the spectrum -/

lemma not_resolvent (hn : 1 ≤ n) (t : ℝ) (ht : 0 ≤ t) :
    (t : ℂ) ∉ TeschlQM.Shared.resolventSet (freeHamiltonian n) := by
  rintro ⟨R, -, hR2⟩
  set ε : ℝ := 1 / (‖R‖ + 1) with hεdef
  have hε : 0 < ε := by positivity
  have hεR : ε * ‖R‖ < 1 := by
    rw [hεdef, one_div, inv_mul_lt_iff₀ (by positivity)]; linarith
  -- a point where the symbol equals `t`
  set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ)
  have he : ‖e‖ = 1 := by simp [e]
  set ξ0 : EuclideanSpace ℝ (Fin n) := (Real.sqrt t / (2 * Real.pi)) • e
  have hξ0n : ‖ξ0‖ = Real.sqrt t / (2 * Real.pi) := by
    rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hsξ0 : laplaceSymbol n ξ0 = t := by
    unfold laplaceSymbol
    rw [hξ0n, mul_div_cancel₀ _ (by positivity), Real.sq_sqrt ht]
  set ρ : ℝ := ‖ξ0‖ + 1
  set U : Set (EuclideanSpace ℝ (Fin n)) :=
    {ξ | ‖laplaceSymbol n ξ - t‖ < ε} ∩ Metric.ball 0 ρ with hUdef
  have hUo : IsOpen U :=
    (isOpen_lt (continuous_symb.sub continuous_const).norm continuous_const).inter
      Metric.isOpen_ball
  have hξ0U : ξ0 ∈ U := ⟨by simp [hsξ0, hε], by simp [ρ]⟩
  have hμpos : 0 < volume U := hUo.measure_pos volume ⟨ξ0, hξ0U⟩
  have hμfin : volume U < ⊤ :=
    (measure_mono Set.inter_subset_right).trans_lt measure_ball_lt_top
  set Φ : L2 n := indicatorConstLp 2 hUo.measurableSet hμfin.ne (1 : ℂ)
  have hΦpos : 0 < ‖Φ‖ := by
    rw [norm_indicatorConstLp (by norm_num) (by norm_num), norm_one, one_mul]
    apply Real.rpow_pos_of_pos
    rw [measureReal_def]
    exact ENNReal.toReal_pos hμpos.ne' hμfin.ne
  have hΦU : ∀ᵐ ξ ∂volume, ξ ∉ U → Φ ξ = 0 := indicatorConstLp_coeFn_notMem
  set ψ : L2 n := (fourierL2 n).symm Φ
  have hFψ : fourierL2 n ψ = Φ := LinearIsometryEquiv.apply_symm_apply _ _
  have hdom : ψ ∈ (freeHamiltonian n).domain := by
    rw [mem_dom_iff, hFψ]
    refine MemLp.of_le_mul (c := (2 * Real.pi * ρ) ^ 2) (Lp.memLp Φ)
      (continuous_symb.aestronglyMeasurable.mul (Lp.aestronglyMeasurable Φ)) ?_
    filter_upwards [hΦU] with ξ hξ
    by_cases hξU : ξ ∈ U
    · rw [norm_mul]; gcongr
      exact norm_symb_le ξ (by have := hξU.2; rw [Metric.mem_ball, dist_zero_right] at this;
                                exact this.le)
    · rw [hξ hξU]; simp
  have hψΦ : ‖ψ‖ = ‖Φ‖ := by
    rw [← hFψ]; exact ((fourierL2 n).norm_map ψ).symm
  set v : (freeHamiltonian n).domain := ⟨ψ, hdom⟩
  have hw : ‖freeHamiltonian n v - (t : ℂ) • (v : L2 n)‖ ≤ ε * ‖ψ‖ := by
    rw [← (fourierL2 n).norm_map, hψΦ]
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [fourier_sub_smul_ae v (t : ℂ), hΦU] with ξ h1 h2
    rw [h1]
    change ‖(laplaceSymbol n ξ - t) * (fourierL2 n ψ) ξ‖ ≤ ε * ‖Φ ξ‖
    rw [hFψ, norm_mul]
    by_cases hξU : ξ ∈ U
    · gcongr; exact hξU.1.le
    · rw [h2 hξU]; simp
  have key := hR2 v
  have hψpos : 0 < ‖ψ‖ := by rw [hψΦ]; exact hΦpos
  have : ‖ψ‖ ≤ ‖R‖ * (ε * ‖ψ‖) := by
    calc ‖ψ‖ = ‖R (freeHamiltonian n v - (t : ℂ) • (v : L2 n))‖ := by rw [key]
      _ ≤ ‖R‖ * ‖freeHamiltonian n v - (t : ℂ) • (v : L2 n)‖ := R.le_opNorm _
      _ ≤ ‖R‖ * (ε * ‖ψ‖) := by gcongr
  nlinarith [norm_nonneg R]

lemma spectrum_fH (hn : 1 ≤ n) :
    TeschlQM.Shared.spectrum (freeHamiltonian n) = (fun t : ℝ => (t : ℂ)) '' Set.Ici 0 := by
  ext z
  constructor
  · intro hz
    by_contra h
    exact hz (resolvent_of_not_mem z h)
  · rintro ⟨t, ht, rfl⟩
    exact not_resolvent hn t ht

theorem essentialSpectrum_fH (hn : 1 ≤ n) :
    essentialSpectrum (freeHamiltonian n) = (fun t : ℝ => (t : ℂ)) '' Set.Ici 0 := by
  have hd : discreteSpectrum (freeHamiltonian n) = ∅ := by
    ext z
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hz
    exact hz.2.1 (eigenspace_fH_eq_bot hn z)
  rw [essentialSpectrum, hd, Set.sdiff_empty, spectrum_fH hn]

end FHAux

open TeschlQM.OneParticle in
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    IsSelfAdjoint (freeHamiltonian n) ∧
      essentialSpectrum (freeHamiltonian n) = (fun t : ℝ => (t : ℂ)) '' Set.Ici 0 ∧
      (freeHamiltonian n).HasCore (testFunctions n) :=
  ⟨FHAux.fH_selfAdjoint, FHAux.essentialSpectrum_fH hn, FHAux.fH_hasCore⟩
