-- Prove2me | solution 1 for TeschlQM.OneParticle.potential_relativelyCompact
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-07T16:48:45.453872+00:00
-- url     : https://prove2.me/submissions/0e28e048-e676-4b17-8726-d414facbe9b1

import Mathlib
import Definitions.Def_TeschlQM_OneParticle_multiplicationOperator
import Definitions.Def_TeschlQM_OneParticle_freeHamiltonian
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_IsRelativelyCompact
import Definitions.Def_TeschlQM_OneParticle_IsBoundedVanishingAtInfinity
import Definitions.Def_TeschlQM_OneParticle_essentialSpectrum
import Definitions.Def_TeschlQM_OneParticle_testFunctions

/-!
# Teschl, proof of Theorem 10.2: `V ∈ L^∞_∞ (+ L²  for n ≤ 3)` is `H₀`-relatively compact

We take `z = -1` and `R = R₀(-1) = F⁻¹ (s+1)⁻¹ F`, and show that `V R₀(-1)` is compact.

* `SDAux`, `FHAux`: infrastructure on the free Schrödinger operator (Fourier multipliers,
  bounded multiplication operators, the resolvent as a Fourier multiplier).
* `SobAux`: `L²` Fourier inversion for integrable functions and integrability of `(s+1)⁻²`
  for `n ≤ 3`.
* `RCAux`:
  - `cpt_core`: `W(x) g(p)` is compact for bounded `W, g` with bounded supports
    (Arzelà–Ascoli type total-boundedness argument: the image functions are uniformly bounded
    and uniformly Lipschitz, and `W` is in `L²` with compact support).
  - `cpt_cs`: `W (H₀+1)⁻¹` compact for bounded `W` with bounded support (cut off the symbol).
  - `cpt_bvi`: `W (H₀+1)⁻¹` compact for bounded `W` vanishing at infinity (cut off `W`).
  - `R0_sup`, `cpt_mulL2`: for `n ≤ 3`, `(H₀+1)⁻¹ : L² → L^∞` is bounded, and
    `W (H₀+1)⁻¹` is compact for `W ∈ L²` (approximate `W` in `L²` by `C_c` functions).
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

lemma isResolventAt_mul (z : ℂ) {c : ℝ} (hc : 0 < c) (hbd : ∀ ξ, c ≤ ‖laplaceSymbol n ξ - z‖)
    (hmc : Continuous fun ξ : EuclideanSpace ℝ (Fin n) => (laplaceSymbol n ξ - z)⁻¹)
    (hmb : ∀ ξ, ‖(laplaceSymbol n ξ - z)⁻¹‖ ≤ c⁻¹) :
    TeschlQM.Shared.IsResolventAt (freeHamiltonian n) z
      (((fourierL2 n).symm : L2 n →L[ℂ] L2 n) ∘L mulCLM hmc.aestronglyMeasurable hmb ∘L
        (fourierL2 n : L2 n →L[ℂ] L2 n)) := by
  have hne : ∀ ξ, laplaceSymbol n ξ - z ≠ 0 := fun ξ h => by
    have := hbd ξ; rw [h, norm_zero] at this; linarith
  set m : EuclideanSpace ℝ (Fin n) → ℂ := fun ξ => (laplaceSymbol n ξ - z)⁻¹ with hmdef
  set M := mulCLM hmc.aestronglyMeasurable hmb
  set R : L2 n →L[ℂ] L2 n := ((fourierL2 n).symm : L2 n →L[ℂ] L2 n) ∘L M ∘L
    (fourierL2 n : L2 n →L[ℂ] L2 n) with hRdef
  have hFR : ∀ φ, fourierL2 n (R φ) = M (fourierL2 n φ) := fun φ => by
    simp [R]
  refine ⟨fun φ => ?_, fun ψ => ?_⟩
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
  have hmc : Continuous fun ξ : EuclideanSpace ℝ (Fin n) => (laplaceSymbol n ξ - z)⁻¹ :=
    (continuous_symb.sub continuous_const).inv₀ hne
  have hmb : ∀ ξ, ‖(laplaceSymbol n ξ - z)⁻¹‖ ≤ c⁻¹ := fun ξ => by
    rw [norm_inv]; exact inv_anti₀ hc (hbd ξ)
  exact ⟨_, isResolventAt_mul z hc hbd hmc hmb⟩

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

open MeasureTheory FourierTransform SchwartzMap
open scoped ContDiff ZeroAtInfty InnerProductSpace
open Filter Topology
open TeschlQM.OneParticle

namespace SobAux

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

lemma fourierInv_fun_eq (G : V → ℂ) :
    𝓕⁻ G = VectorFourier.fourierIntegral Real.fourierChar volume (-innerₗ V) G := rfl

lemma continuous_fourierInv_fun {G : V → ℂ} (hG : Integrable G) : Continuous (𝓕⁻ G) := by
  rw [fourierInv_fun_eq]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by simp; exact continuous_inner.neg) hG

lemma integral_fourierInv_smul_eq_fun {f g : V → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, 𝓕⁻ f ξ • g ξ = ∫ x, f x • 𝓕⁻ g x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := Real.fourierChar)
    (μ := volume) (ν := volume) (L := -innerₗ V) Real.continuous_fourierChar
    (by simp; exact continuous_inner.neg) hf hg
  have hflip : (-innerₗ V).flip = -innerₗ V := by
    ext x y
    simp [real_inner_comm]
  rw [hflip] at h
  exact h

lemma fourierInv_L2_ae_eq (g : Lp ℂ 2 (volume : Measure V)) (hg : Integrable (g : V → ℂ)) :
    ((𝓕⁻ g : Lp ℂ 2 (volume : Measure V)) : V → ℂ) =ᵐ[volume] 𝓕⁻ (g : V → ℂ) := by
  have hc := continuous_fourierInv_fun hg
  have hA : LocallyIntegrable (((𝓕⁻ g : Lp ℂ 2 (volume : Measure V)) : V → ℂ)) volume :=
    (Lp.memLp _).locallyIntegrable (by norm_num)
  have hli : LocallyIntegrable (fun x => ((𝓕⁻ g : Lp ℂ 2 (volume : Measure V)) : V → ℂ) x -
      𝓕⁻ (g : V → ℂ) x) volume := hA.sub hc.locallyIntegrable
  have key := ae_eq_zero_of_integral_contDiff_smul_eq_zero hli ?_
  · filter_upwards [key] with x hx using sub_eq_zero.mp hx
  intro φ hφs hφc
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hφc.comp_left rfl
  have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := Complex.ofRealCLM.contDiff.comp hφs
  set ψ := hg₁.toSchwartzMap hg₂ with hψdef
  have hψ : ∀ x, ψ x = (φ x : ℂ) := fun x => by simp [ψ]
  have e1 : ∫ x, φ x • ((𝓕⁻ g : Lp ℂ 2 (volume : Measure V)) : V → ℂ) x =
      ∫ ξ, (𝓕⁻ (ψ : V → ℂ)) ξ • g ξ := by
    have := Lp.toTemperedDistribution_apply (𝓕⁻ g) ψ
    rw [← Lp.fourierInv_toTemperedDistribution_eq, TemperedDistribution.fourierInv_apply,
      Lp.toTemperedDistribution_apply, SchwartzMap.fourierInv_coe] at this
    rw [this]
    simp [hψ, Complex.real_smul]
  have e2 : ∫ x, φ x • 𝓕⁻ (g : V → ℂ) x = ∫ ξ, (𝓕⁻ (ψ : V → ℂ)) ξ • g ξ := by
    rw [integral_fourierInv_smul_eq_fun ψ.integrable hg]
    simp [hψ, Complex.real_smul]
  have i1 : Integrable (fun x => φ x • ((𝓕⁻ g : Lp ℂ 2 (volume : Measure V)) : V → ℂ) x) :=
    hA.integrable_smul_left_of_hasCompactSupport hφs.continuous hφc
  have i2 : Integrable (fun x => φ x • 𝓕⁻ (g : V → ℂ) x) :=
    hc.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hφs.continuous hφc
  simp_rw [smul_sub]
  rw [integral_sub i1 i2, e1, e2, sub_self]

lemma tendsto_fourierInv_fun (G : V → ℂ) : Tendsto (𝓕⁻ G) (cocompact V) (𝓝 0) := by
  rw [Real.fourierInv_eq_fourier_comp_neg]
  exact tendsto_integral_exp_inner_smul_cocompact (fun x => G (-x))

/-- The inverse Fourier integral of an integrable function, as a `C₀` function. -/
noncomputable def c0OfL1 (G : V → ℂ) (hG : Integrable G) : V →C₀ ℂ where
  toFun := 𝓕⁻ G
  continuous_toFun := continuous_fourierInv_fun hG
  zero_at_infty' := tendsto_fourierInv_fun G

@[simp] lemma coe_c0OfL1 (G : V → ℂ) (hG : Integrable G) : ⇑(c0OfL1 G hG) = 𝓕⁻ G := rfl

lemma norm_c0OfL1_le (G : V → ℂ) (hG : Integrable G) : ‖c0OfL1 G hG‖ ≤ ∫ v, ‖G v‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm,
    BoundedContinuousFunction.norm_le (integral_nonneg fun _ => norm_nonneg _)]
  intro x
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

variable {n : ℕ}

lemma re_inner_pt' (a b : ℂ) : (⟪a, b⟫_ℂ).re = a.re * b.re + a.im * b.im := by
  simp
  ring

/-- The weight `(2π|ξ|)² + t`. -/
noncomputable def wt (t : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) : ℝ := (2 * Real.pi * ‖ξ‖) ^ 2 + t

lemma wt_pos {t : ℝ} (ht : 0 < t) (ξ : EuclideanSpace ℝ (Fin n)) : 0 < wt t ξ := by
  unfold wt
  positivity

lemma continuous_wt (t : ℝ) : Continuous (fun ξ : EuclideanSpace ℝ (Fin n) => wt t ξ) := by
  unfold wt
  fun_prop

lemma wt_bound {t : ℝ} (ht : 1 ≤ t) (ξ : EuclideanSpace ℝ (Fin n)) :
    (wt t ξ)⁻¹ ^ 2 ≤ 4 * (1 + ‖ξ‖) ^ (-4 : ℝ) := by
  have hr := norm_nonneg ξ
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have h1 : ‖ξ‖ ^ 2 ≤ (2 * Real.pi * ‖ξ‖) ^ 2 :=
    pow_le_pow_left₀ hr (le_mul_of_one_le_left hr hpi) 2
  have hw : ‖ξ‖ ^ 2 + 1 ≤ wt t ξ := by unfold wt; linarith
  have hwpos : 0 < wt t ξ := wt_pos (by linarith) ξ
  have h2 : (1 + ‖ξ‖) ^ 2 ≤ 2 * wt t ξ := by nlinarith [sq_nonneg (1 - ‖ξ‖)]
  have h3 : (1 + ‖ξ‖) ^ 4 ≤ 4 * wt t ξ ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) h2 2
    nlinarith
  rw [Real.rpow_neg (by positivity), show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, inv_pow, inv_eq_one_div, ← div_eq_mul_inv,
    div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast
  nlinarith

lemma integrable_bound (hn : n ≤ 3) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin n) => 4 * (1 + ‖ξ‖) ^ (-4 : ℝ)) := by
  have hint := integrable_one_add_norm (E := EuclideanSpace ℝ (Fin n)) (μ := volume) (r := 4)
    (by rw [finrank_euclideanSpace_fin]; exact_mod_cast (by omega : n < 4))
  exact hint.const_mul 4

lemma integrable_wt_inv_sq (hn : n ≤ 3) {t : ℝ} (ht : 1 ≤ t) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin n) => (wt t ξ)⁻¹ ^ 2) := by
  refine (integrable_bound hn).mono' ?_ ?_
  · exact (((continuous_wt t).inv₀ fun ξ => (wt_pos (by linarith) ξ).ne').pow 2).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ξ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact wt_bound ht ξ

lemma tendsto_integral_wt (hn : n ≤ 3) :
    Tendsto (fun t : ℝ => ∫ ξ : EuclideanSpace ℝ (Fin n), (wt t ξ)⁻¹ ^ 2) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
    (F := fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) => (wt t ξ)⁻¹ ^ 2) (f := fun _ => 0)
    (fun ξ => 4 * (1 + ‖ξ‖) ^ (-4 : ℝ)) ?_ ?_ (integrable_bound hn) ?_
  · simpa using h
  · filter_upwards [eventually_ge_atTop 1] with t ht
    exact (((continuous_wt t).inv₀ fun ξ => (wt_pos (by linarith) ξ).ne').pow 2).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop 1] with t ht
    refine Filter.Eventually.of_forall fun ξ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact wt_bound ht ξ
  · refine Filter.Eventually.of_forall fun ξ => ?_
    have h1 : Tendsto (fun t : ℝ => wt t ξ) atTop atTop :=
      tendsto_atTop_add_const_left _ _ tendsto_id
    have h2 := (tendsto_inv_atTop_zero.comp h1).pow 2
    simpa using h2

lemma L1_bound (G : L2 n) (hS : MemLp (fun ξ => laplaceSymbol n ξ * G ξ) 2 volume) {t : ℝ}
    (ht : 0 < t) (hI : Integrable (fun ξ : EuclideanSpace ℝ (Fin n) => (wt t ξ)⁻¹ ^ 2)) :
    Integrable (G : EuclideanSpace ℝ (Fin n) → ℂ) ∧
      ∫ ξ, ‖G ξ‖ ≤ Real.sqrt (∫ ξ : EuclideanSpace ℝ (Fin n), (wt t ξ)⁻¹ ^ 2) *
        (‖hS.toLp _‖ + t * ‖G‖) := by
  have hwpos : ∀ ξ : EuclideanSpace ℝ (Fin n), 0 < wt t ξ := wt_pos ht
  have hwc := continuous_wt (n := n) t
  have hwic : Continuous (fun ξ : EuclideanSpace ℝ (Fin n) => (wt t ξ)⁻¹) :=
    hwc.inv₀ (fun ξ => (hwpos ξ).ne')
  have hFr : MemLp (fun ξ : EuclideanSpace ℝ (Fin n) => (wt t ξ)⁻¹) 2 volume :=
    (memLp_two_iff_integrable_sq hwic.aestronglyMeasurable).mpr hI
  have hF : MemLp (fun ξ : EuclideanSpace ℝ (Fin n) => (((wt t ξ)⁻¹ : ℝ) : ℂ)) 2 volume :=
    hFr.ofReal
  have hsum : MemLp (fun ξ => laplaceSymbol n ξ * G ξ + (t : ℂ) • G ξ) 2 volume :=
    hS.add ((Lp.memLp G).const_smul (t : ℂ))
  have hpt : ∀ ξ, ‖(((wt t ξ * ‖G ξ‖ : ℝ)) : ℂ)‖ =
      ‖laplaceSymbol n ξ * G ξ + (t : ℂ) • G ξ‖ := by
    intro ξ
    have : laplaceSymbol n ξ * G ξ + (t : ℂ) • G ξ = ((wt t ξ : ℝ) : ℂ) * G ξ := by
      simp only [laplaceSymbol, wt, smul_eq_mul]
      push_cast
      ring
    rw [this, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (hwpos ξ), abs_mul, abs_of_pos (hwpos ξ), abs_norm]
  have hGt : MemLp (fun ξ => (((wt t ξ * ‖G ξ‖ : ℝ)) : ℂ)) 2 volume :=
    hsum.of_le (Complex.continuous_ofReal.comp_aestronglyMeasurable
      (hwc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable G).norm))
      (Filter.Eventually.of_forall fun ξ => (hpt ξ).le)
  set F := hF.toLp _ with hFdef
  set Gt := hGt.toLp _ with hGtdef
  have hpt2 : ∀ᵐ ξ ∂volume, (⟪(F : EuclideanSpace ℝ (Fin n) → ℂ) ξ,
      (Gt : EuclideanSpace ℝ (Fin n) → ℂ) ξ⟫_ℂ).re = ‖G ξ‖ := by
    filter_upwards [hF.coeFn_toLp, hGt.coeFn_toLp] with ξ h1 h2
    have := (hwpos ξ).ne'
    rw [h1, h2, re_inner_pt']
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero]
    field_simp
  have hintRe := (L2.integrable_inner (𝕜 := ℂ) F Gt).re
  have hGint : Integrable (fun ξ => ‖G ξ‖) := hintRe.congr hpt2
  have hGi : Integrable (G : EuclideanSpace ℝ (Fin n) → ℂ) :=
    (integrable_norm_iff (Lp.aestronglyMeasurable G)).mp hGint
  refine ⟨hGi, ?_⟩
  have hinner : (⟪F, Gt⟫_ℂ).re = ∫ ξ, ‖G ξ‖ := by
    rw [L2.inner_def, ← integral_congr_ae hpt2]
    exact (integral_re (L2.integrable_inner (𝕜 := ℂ) F Gt)).symm
  have hFn : ‖F‖ ≤ Real.sqrt (∫ ξ : EuclideanSpace ℝ (Fin n), (wt t ξ)⁻¹ ^ 2) := by
    have hsq : ‖F‖ ^ 2 = ∫ ξ : EuclideanSpace ℝ (Fin n), (wt t ξ)⁻¹ ^ 2 := by
      rw [show ‖F‖ ^ 2 = (⟪F, F⟫_ℂ).re by simpa using (norm_sq_eq_re_inner (𝕜 := ℂ) F),
        L2.inner_def]
      rw [show (∫ a, ⟪(F : EuclideanSpace ℝ (Fin n) → ℂ) a, (F : EuclideanSpace ℝ (Fin n) → ℂ) a⟫_ℂ).re
        = ∫ a, (⟪(F : EuclideanSpace ℝ (Fin n) → ℂ) a, (F : EuclideanSpace ℝ (Fin n) → ℂ) a⟫_ℂ).re
        from (integral_re (L2.integrable_inner (𝕜 := ℂ) F F)).symm]
      apply integral_congr_ae
      filter_upwards [hF.coeFn_toLp] with ξ h
      rw [h, re_inner_pt']
      simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero]
      ring
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  have hGtn : ‖Gt‖ ≤ ‖hS.toLp _‖ + t * ‖G‖ := by
    calc ‖Gt‖ ≤ ‖hS.toLp _ + (t : ℂ) • G‖ := by
          apply Lp.norm_le_norm_of_ae_le
          filter_upwards [hGt.coeFn_toLp, Lp.coeFn_add (hS.toLp _) ((t : ℂ) • G),
            hS.coeFn_toLp, Lp.coeFn_smul (t : ℂ) G] with ξ h1 h2 h3 h4
          rw [h1, h2, Pi.add_apply, h3, h4, Pi.smul_apply]
          exact (hpt ξ).le
      _ ≤ ‖hS.toLp _‖ + ‖(t : ℂ) • G‖ := norm_add_le _ _
      _ = ‖hS.toLp _‖ + t * ‖G‖ := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  calc ∫ ξ, ‖G ξ‖ = (⟪F, Gt⟫_ℂ).re := hinner.symm
    _ ≤ ‖F‖ * ‖Gt‖ := by simpa using re_inner_le_norm (𝕜 := ℂ) F Gt
    _ ≤ _ := mul_le_mul hFn hGtn (norm_nonneg _) (Real.sqrt_nonneg _)

end SobAux

open MeasureTheory TeschlQM.OneParticle ComplexConjugate Filter Topology FourierTransform
open scoped InnerProductSpace

namespace RCAux

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Sup bound for an inverse Fourier integral. -/
lemma norm_fourierInv_le (G : E → ℂ) (x : E) : ‖𝓕⁻ G x‖ ≤ ∫ v, ‖G v‖ := by
  rw [Real.fourierInv_eq']
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; ext v
  rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Lipschitz bound for the inverse Fourier integral of an integrable function supported in a ball. -/
lemma fourierInv_lip (G : E → ℂ) (hG : Integrable G) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hs : ∀ᵐ v ∂volume, ρ < ‖v‖ → G v = 0) (x y : E) :
    ‖𝓕⁻ G x - 𝓕⁻ G y‖ ≤ 2 * Real.pi * ρ * ‖x - y‖ * ∫ v, ‖G v‖ := by
  have hint : ∀ z : E, Integrable
      (fun v : E => Complex.exp (↑(2 * Real.pi * ⟪v, z⟫_ℝ) * Complex.I) • G v) := by
    intro z
    have hc : Continuous fun v : E => Complex.exp (↑(2 * Real.pi * ⟪v, z⟫_ℝ) * Complex.I) := by
      fun_prop
    refine hG.norm.mono' (hc.aestronglyMeasurable.smul hG.aestronglyMeasurable)
      (Eventually.of_forall fun v => ?_)
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [Real.fourierInv_eq', Real.fourierInv_eq', ← integral_sub (hint x) (hint y)]
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hG.norm.const_mul _) ?_
  filter_upwards [hs] with v hv
  rw [← sub_smul, norm_smul]
  by_cases hvρ : ρ < ‖v‖
  · rw [hv hvρ, norm_zero, mul_zero]; positivity
  · push Not at hvρ
    gcongr
    have hfac : Complex.exp (↑(2 * Real.pi * ⟪v, x⟫_ℝ) * Complex.I) -
        Complex.exp (↑(2 * Real.pi * ⟪v, y⟫_ℝ) * Complex.I) =
        Complex.exp (↑(2 * Real.pi * ⟪v, y⟫_ℝ) * Complex.I) *
          (Complex.exp (Complex.I * ↑(2 * Real.pi * ⟪v, x - y⟫_ℝ)) - 1) := by
      rw [mul_sub, mul_one, ← Complex.exp_add, inner_sub_right]
      congr 2
      push_cast; ring
    rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
    have h1 : |⟪v, x - y⟫_ℝ| ≤ ‖v‖ * ‖x - y‖ := abs_real_inner_le_norm _ _
    have h2 : ‖v‖ * ‖x - y‖ ≤ ρ * ‖x - y‖ := by gcongr
    nlinarith [Real.pi_pos, norm_nonneg (x - y)]

/-- The `L²` norm as an integral. -/
noncomputable def L2c (g : E → ℂ) : ℝ := (∫ v, ‖g v‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))

lemma L2c_nonneg (g : E → ℂ) : 0 ≤ L2c g := by
  unfold L2c; exact Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _

lemma norm_eq_L2c (f : L2 n) : ‖f‖ = L2c (f : E → ℂ) := by
  rw [Lp.norm_def, (Lp.memLp f).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _)]
  simp [L2c]

lemma int_mul_le (g : E → ℂ) (hg : MemLp g 2 volume) (f : L2 n) :
    ∫ v, ‖g v‖ * ‖f v‖ ≤ L2c g * ‖f‖ := by
  rw [norm_eq_L2c]
  have := integral_mul_norm_le_Lp_mul_Lq (μ := volume) (f := g) (g := (f : E → ℂ))
    Real.HolderConjugate.two_two (by simpa using hg) (by simpa using Lp.memLp f)
  simpa [L2c] using this

/-- An Arzelà–Ascoli type criterion: if `T φ = W · u_φ` with `W ∈ L²` supported in a ball and the
`u_φ` (for `‖φ‖ ≤ 1`) uniformly bounded and uniformly Lipschitz, then `T` maps the unit ball to a
totally bounded set. -/
lemma tb_of_lip (T : L2 n →L[ℂ] L2 n) (W : E → ℂ) (hW2 : MemLp W 2 volume) (ρW : ℝ)
    (hWs : ∀ x, ρW < ‖x‖ → W x = 0) (u : L2 n → E → ℂ) (M L : ℝ)
    (hTae : ∀ φ, (T φ : E → ℂ) =ᵐ[volume] fun x => W x * u φ x)
    (hbd : ∀ φ : L2 n, ‖φ‖ ≤ 1 → ∀ x, ‖u φ x‖ ≤ M) (hL : 0 ≤ L)
    (hlip : ∀ φ : L2 n, ‖φ‖ ≤ 1 → ∀ x y, ‖u φ x - u φ y‖ ≤ L * ‖x - y‖) :
    TotallyBounded (T '' Metric.closedBall 0 1) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbd 0 (by simp) 0)
  apply Metric.totallyBounded_of_finite_discretization
  intro ε hε
  set CW : ℝ := ‖hW2.toLp W‖ with hCW
  have hCW0 : 0 ≤ CW := norm_nonneg _
  set δ : ℝ := ε / (8 * (CW + 1) * (L + 1)) with hδ
  set ε' : ℝ := ε / (8 * (CW + 1)) with hε'
  have hδ0 : 0 < δ := by positivity
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨N, -, hNf, hcov⟩ := finite_cover_balls_of_compact
    (isCompact_closedBall (0 : E) ρW) hδ0
  have : Fintype N := hNf.fintype
  set Φ : Metric.closedBall (0 : L2 n) 1 → (N → ℂ) := fun φ j => u φ j with hΦ
  have hA : TotallyBounded (Set.range Φ) := by
    refine (isCompact_closedBall (0 : N → ℂ) M).totallyBounded.subset ?_
    rintro _ ⟨φ, rfl⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hM]
    intro j
    exact hbd φ (mem_closedBall_zero_iff.mp φ.2) j
  obtain ⟨t, htf, hcovt⟩ := Metric.totallyBounded_iff.mp hA ε' hε'0
  have : Fintype t := htf.fintype
  have hcen : ∀ φ : Metric.closedBall (0 : L2 n) 1, ∃ y : t, Φ φ ∈ Metric.ball (y : N → ℂ) ε' := by
    intro φ
    have := hcovt (Set.mem_range_self φ)
    rw [Set.mem_iUnion₂] at this
    obtain ⟨y, hy, hφy⟩ := this
    exact ⟨⟨y, hy⟩, hφy⟩
  choose cen hcenspec using hcen
  have hpre : ∀ x : T '' Metric.closedBall 0 1,
      ∃ φ : Metric.closedBall (0 : L2 n) 1, T φ = x := by
    rintro ⟨x, φ, hφ, rfl⟩
    exact ⟨⟨φ, hφ⟩, rfl⟩
  choose pre hprespec using hpre
  refine ⟨t, inferInstance, fun x => cen (pre x), ?_⟩
  intro x y hxy
  set φ := pre x
  set ψ := pre y
  have hφ1 : ‖(φ : L2 n)‖ ≤ 1 := mem_closedBall_zero_iff.mp φ.2
  have hψ1 : ‖(ψ : L2 n)‖ ≤ 1 := mem_closedBall_zero_iff.mp ψ.2
  have hd : dist (Φ φ) (Φ ψ) < 2 * ε' := by
    have h1 := hcenspec φ
    have h2 := hcenspec ψ
    change cen φ = cen ψ at hxy
    rw [hxy] at h1
    rw [Metric.mem_ball] at h1 h2
    calc dist (Φ φ) (Φ ψ) ≤ dist (Φ φ) (cen ψ : N → ℂ) + dist (Φ ψ) (cen ψ : N → ℂ) :=
          dist_triangle_right _ _ _
      _ < ε' + ε' := add_lt_add h1 h2
      _ = 2 * ε' := by ring
  have hj : ∀ j : N, ‖u φ j - u ψ j‖ < 2 * ε' := by
    intro j
    have := (dist_le_pi_dist (Φ φ) (Φ ψ) j).trans_lt hd
    rwa [dist_eq_norm] at this
  have hpt : ∀ z : E, ‖z‖ ≤ ρW → ‖u φ z - u ψ z‖ ≤ 2 * L * δ + 2 * ε' := by
    intro z hz
    have hzK : z ∈ Metric.closedBall (0 : E) ρW := by simpa using hz
    have := hcov hzK
    rw [Set.mem_iUnion₂] at this
    obtain ⟨j, hjN, hzj⟩ := this
    rw [Metric.mem_ball, dist_eq_norm] at hzj
    have e1 := hlip φ hφ1 z j
    have e2 := hlip ψ hψ1 j z
    have e3 := hj ⟨j, hjN⟩
    rw [norm_sub_rev j z] at e2
    calc ‖u φ z - u ψ z‖ = ‖(u φ z - u φ j) + (u φ j - u ψ j) + (u ψ j - u ψ z)‖ := by
          congr 1; ring
      _ ≤ ‖u φ z - u φ j‖ + ‖u φ j - u ψ j‖ + ‖u ψ j - u ψ z‖ := norm_add₃_le
      _ ≤ L * ‖z - j‖ + 2 * ε' + L * ‖z - j‖ := by
          have := e3.le
          gcongr
      _ ≤ L * δ + 2 * ε' + L * δ := by gcongr
      _ = 2 * L * δ + 2 * ε' := by ring
  have hxy' : dist (x : L2 n) y = ‖T φ - T ψ‖ := by
    rw [hprespec x, hprespec y, dist_eq_norm]
  rw [hxy']
  have hbound : ‖T φ - T ψ‖ ≤ (2 * L * δ + 2 * ε') * CW := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [Lp.coeFn_sub (T φ) (T ψ), hTae φ, hTae ψ, hW2.coeFn_toLp] with z h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, h3, h4, ← mul_sub, norm_mul, mul_comm]
    by_cases hz : ‖z‖ ≤ ρW
    · gcongr; exact hpt z hz
    · push Not at hz; rw [hWs z hz, norm_zero, mul_zero, mul_zero]
  refine hbound.trans_lt ?_
  have h1 : 2 * L * δ * CW ≤ ε / 4 := by
    rw [hδ]
    have : 2 * L * (ε / (8 * (CW + 1) * (L + 1))) * CW =
        ε / 4 * (L / (L + 1)) * (CW / (CW + 1)) := by field_simp; ring
    rw [this]
    have hl : L / (L + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have hc : CW / (CW + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    calc ε / 4 * (L / (L + 1)) * (CW / (CW + 1)) ≤ ε / 4 * 1 * 1 := by gcongr
      _ = ε / 4 := by ring
  have h2 : 2 * ε' * CW ≤ ε / 4 := by
    rw [hε']
    have : 2 * (ε / (8 * (CW + 1))) * CW = ε / 4 * (CW / (CW + 1)) := by field_simp; ring
    rw [this]
    have hc : CW / (CW + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    calc ε / 4 * (CW / (CW + 1)) ≤ ε / 4 * 1 := by gcongr
      _ = ε / 4 := by ring
  nlinarith

open FHAux in
/-- The key compactness lemma: `W(x) g(p)` is compact for bounded `W`, `g` with bounded supports. -/
lemma cpt_core {W g : E → ℂ} {BW Bg ρW ρg : ℝ} (hWm : AEStronglyMeasurable W volume)
    (hWb : ∀ x, ‖W x‖ ≤ BW) (hW2 : MemLp W 2 volume) (hWs : ∀ x, ρW < ‖x‖ → W x = 0)
    (hgm : AEStronglyMeasurable g volume) (hgb : ∀ ξ, ‖g ξ‖ ≤ Bg) (hg2 : MemLp g 2 volume)
    (hρg : 0 ≤ ρg) (hgs : ∀ ξ, ρg < ‖ξ‖ → g ξ = 0) :
    IsCompactOperator (mulCLM hWm hWb ∘L ((fourierL2 n).symm : L2 n →L[ℂ] L2 n) ∘L
      mulCLM hgm hgb ∘L (fourierL2 n : L2 n →L[ℂ] L2 n)) := by
  set T := mulCLM hWm hWb ∘L ((fourierL2 n).symm : L2 n →L[ℂ] L2 n) ∘L
      mulCLM hgm hgb ∘L (fourierL2 n : L2 n →L[ℂ] L2 n) with hTdef
  -- the Fourier-side function
  set G : L2 n → L2 n := fun φ => mulCLM hgm hgb (fourierL2 n φ) with hGdef
  have hGae : ∀ φ, (G φ : E → ℂ) =ᵐ[volume] fun ξ => g ξ * (fourierL2 n φ) ξ := fun φ =>
    mulCLM_ae _ _ _
  have hGint : ∀ φ, Integrable (G φ : E → ℂ) := fun φ =>
    (hg2.integrable_mul (Lp.memLp (fourierL2 n φ))).congr (hGae φ).symm
  have hGL1 : ∀ φ, ∫ ξ, ‖(G φ : E → ℂ) ξ‖ ≤ L2c g * ‖φ‖ := by
    intro φ
    calc ∫ ξ, ‖(G φ : E → ℂ) ξ‖ = ∫ ξ, ‖g ξ‖ * ‖(fourierL2 n φ) ξ‖ := by
          apply integral_congr_ae
          filter_upwards [hGae φ] with ξ h
          rw [h, norm_mul]
      _ ≤ L2c g * ‖fourierL2 n φ‖ := int_mul_le g hg2 _
      _ = L2c g * ‖φ‖ := by rw [LinearIsometryEquiv.norm_map]
  have hGs : ∀ φ, ∀ᵐ ξ ∂volume, ρg < ‖ξ‖ → (G φ : E → ℂ) ξ = 0 := by
    intro φ
    filter_upwards [hGae φ] with ξ h hξ
    rw [h, hgs ξ hξ, zero_mul]
  set u : L2 n → E → ℂ := fun φ => 𝓕⁻ (G φ : E → ℂ) with hudef
  have hTae : ∀ φ, (T φ : E → ℂ) =ᵐ[volume] fun x => W x * u φ x := by
    intro φ
    have h1 := mulCLM_ae hWm hWb ((fourierL2 n).symm (G φ))
    have h2 := SobAux.fourierInv_L2_ae_eq (G φ) (hGint φ)
    filter_upwards [h1, h2] with x hx1 hx2
    change (mulCLM hWm hWb ((fourierL2 n).symm (G φ)) : E → ℂ) x = _
    rw [hx1, fourierL2_symm_eq, hx2]
  have hu_bd : ∀ φ x, ‖u φ x‖ ≤ L2c g * ‖φ‖ := fun φ x =>
    (norm_fourierInv_le _ x).trans (hGL1 φ)
  have hu_lip : ∀ φ x y, ‖u φ x - u φ y‖ ≤ 2 * Real.pi * ρg * ‖x - y‖ * (L2c g * ‖φ‖) := by
    intro φ x y
    refine (fourierInv_lip _ (hGint φ) hρg (hGs φ) x y).trans ?_
    gcongr
    exact hGL1 φ
  have hK0 := L2c_nonneg g
  have htb := tb_of_lip T W hW2 ρW hWs u (L2c g) (2 * Real.pi * ρg * L2c g) hTae
    (fun φ hφ x => (hu_bd φ x).trans (by nlinarith [norm_nonneg φ]))
    (by positivity)
    (fun φ hφ x y => (hu_lip φ x y).trans (by
      have := norm_nonneg (x - y)
      have h2 : 0 ≤ 2 * Real.pi * ρg := by positivity
      calc 2 * Real.pi * ρg * ‖x - y‖ * (L2c g * ‖φ‖)
          = (2 * Real.pi * ρg * L2c g) * ‖x - y‖ * ‖φ‖ := by ring
        _ ≤ (2 * Real.pi * ρg * L2c g) * ‖x - y‖ * 1 := by gcongr
        _ = _ := by ring))
  rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact]
  exact ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds _ one_pos, closure _,
    htb.closure.isCompact_of_isClosed isClosed_closure, subset_closure⟩

/-! ### The resolvent at `-1` -/

lemma symb_add_one_bound (ξ : E) : 1 ≤ ‖laplaceSymbol n ξ - (-1)‖ := by
  have h1 := Complex.re_le_norm (laplaceSymbol n ξ - (-1))
  have hs : (laplaceSymbol n ξ).re = (2 * Real.pi * ‖ξ‖) ^ 2 := by
    unfold laplaceSymbol; exact Complex.ofReal_re _
  rw [Complex.sub_re, hs] at h1
  simp only [Complex.neg_re, Complex.one_re] at h1
  nlinarith [sq_nonneg (2 * Real.pi * ‖ξ‖)]

lemma mres_cont : Continuous fun ξ : E => (laplaceSymbol n ξ - (-1))⁻¹ :=
  (FHAux.continuous_symb.sub continuous_const).inv₀ fun ξ h => by
    have h' : laplaceSymbol n ξ - (-1) = 0 := h
    have := symb_add_one_bound ξ; rw [h', norm_zero] at this; linarith

lemma mres_bound (ξ : E) : ‖(laplaceSymbol n ξ - (-1))⁻¹‖ ≤ (1 : ℝ)⁻¹ := by
  rw [norm_inv]; exact inv_anti₀ one_pos (symb_add_one_bound ξ)

/-- The free resolvent `R₀(-1) = (H₀ + 1)⁻¹`. -/
noncomputable def R0 (n : ℕ) : L2 n →L[ℂ] L2 n :=
  ((fourierL2 n).symm : L2 n →L[ℂ] L2 n) ∘L
    FHAux.mulCLM (mres_cont (n := n)).aestronglyMeasurable mres_bound ∘L
      (fourierL2 n : L2 n →L[ℂ] L2 n)

lemma R0_isResolvent : TeschlQM.Shared.IsResolventAt (freeHamiltonian n) (-1) (R0 n) :=
  FHAux.isResolventAt_mul (-1) one_pos symb_add_one_bound mres_cont mres_bound

lemma norm_mulCLM_apply_le {m : E → ℂ} (hm : AEStronglyMeasurable m volume) {C : ℝ}
    (hC : ∀ ξ, ‖m ξ‖ ≤ C) (f : L2 n) : ‖FHAux.mulCLM hm hC f‖ ≤ C * ‖f‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [FHAux.mulCLM_ae hm hC f] with ξ h
  rw [h, norm_mul]; gcongr; exact hC ξ

lemma norm_R0_apply_le (φ : L2 n) : ‖R0 n φ‖ ≤ ‖φ‖ := by
  simp only [R0, ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [show ∀ f : L2 n, ‖((fourierL2 n).symm : L2 n →L[ℂ] L2 n) f‖ = ‖f‖ from fun f =>
    (fourierL2 n).symm.norm_map f]
  refine (norm_mulCLM_apply_le _ _ _).trans ?_
  rw [inv_one, one_mul]
  exact le_of_eq ((fourierL2 n).norm_map φ)

/-- A criterion for compactness: approximation in operator norm by compact operators. -/
lemma cpt_of_approx (T : L2 n →L[ℂ] L2 n)
    (h : ∀ ε > 0, ∃ S : L2 n →L[ℂ] L2 n, IsCompactOperator S ∧ ‖T - S‖ ≤ ε) :
    IsCompactOperator T := by
  have hcl := isClosed_setOfPred_isCompactOperator (𝕜₁ := ℂ) (𝕜₂ := ℂ)
    (σ₁₂ := RingHom.id ℂ) (M₁ := L2 n) (M₂ := L2 n)
  refine hcl.closure_subset (Metric.mem_closure_iff.mpr fun ε hε => ?_)
  obtain ⟨S, hS, hTS⟩ := h (ε / 2) (half_pos hε)
  exact ⟨S, hS, by rw [dist_eq_norm]; linarith⟩


lemma memLp_of_bdd_supp {f : E → ℂ} (hf : AEStronglyMeasurable f volume) {B ρ : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ B) (hs : ∀ x, ρ < ‖x‖ → f x = 0) : MemLp f 2 volume := by
  have hg : MemLp ((Metric.closedBall (0 : E) ρ).indicator fun _ => (B : ℂ)) 2 volume :=
    memLp_indicator_const 2 Metric.isClosed_closedBall.measurableSet _
      (Or.inr measure_closedBall_lt_top.ne)
  refine hg.of_le hf (Eventually.of_forall fun x => ?_)
  by_cases hx : ‖x‖ ≤ ρ
  · rw [Set.indicator_of_mem (by simpa using hx)]
    refine (hb x).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
  · push Not at hx
    rw [hs x hx, norm_zero]; exact norm_nonneg _

lemma symb_add_one_bound' (ξ : E) : 1 + (2 * Real.pi * ‖ξ‖) ^ 2 ≤ ‖laplaceSymbol n ξ - (-1)‖ := by
  have h1 := Complex.re_le_norm (laplaceSymbol n ξ - (-1))
  have hs : (laplaceSymbol n ξ).re = (2 * Real.pi * ‖ξ‖) ^ 2 := by
    unfold laplaceSymbol; exact Complex.ofReal_re _
  rw [Complex.sub_re, hs] at h1
  simp only [Complex.neg_re, Complex.one_re] at h1
  linarith

lemma mres_tail {M : ℝ} (hM : 1 ≤ M) (ξ : E) (hξ : M < ‖ξ‖) :
    ‖(laplaceSymbol n ξ - (-1))⁻¹‖ ≤ 1 / (1 + M) := by
  rw [norm_inv, one_div]
  refine inv_anti₀ (by linarith) ((le_trans ?_ (symb_add_one_bound' ξ)))
  have hpi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have h1 : ‖ξ‖ ≤ 2 * Real.pi * ‖ξ‖ := by nlinarith [norm_nonneg ξ]
  have h2 : ‖ξ‖ ≤ (2 * Real.pi * ‖ξ‖) ^ 2 := by nlinarith
  linarith

open FHAux in
/-- `W(x) (H₀+1)⁻¹` is compact for bounded `W` with bounded support. -/
lemma cpt_cs {W : E → ℂ} {B ρ : ℝ} (hWm : AEStronglyMeasurable W volume)
    (hWb : ∀ x, ‖W x‖ ≤ B) (hWs : ∀ x, ρ < ‖x‖ → W x = 0) :
    IsCompactOperator (mulCLM hWm hWb ∘L R0 n) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hWb 0)
  have hW2 := memLp_of_bdd_supp hWm hWb hWs
  refine cpt_of_approx _ fun ε hε => ?_
  set M : ℝ := max 1 (B / ε) with hMdef
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMB : B ≤ ε * M := by
    have := le_max_right 1 (B / ε)
    rw [div_le_iff₀ hε] at this; linarith
  set m : E → ℂ := fun ξ => (laplaceSymbol n ξ - (-1))⁻¹ with hmdef
  set g : E → ℂ := (Metric.closedBall (0 : E) M).indicator m with hgdef
  have hgm : AEStronglyMeasurable g volume :=
    (mres_cont (n := n)).aestronglyMeasurable.indicator Metric.isClosed_closedBall.measurableSet
  have hgb : ∀ ξ, ‖g ξ‖ ≤ (1 : ℝ)⁻¹ := fun ξ =>
    (norm_indicator_le_norm_self _ _).trans (mres_bound ξ)
  have hgs : ∀ ξ, M < ‖ξ‖ → g ξ = 0 := fun ξ hξ =>
    Set.indicator_of_notMem (by simpa using hξ) _
  have hg2 := memLp_of_bdd_supp hgm hgb hgs
  refine ⟨mulCLM hWm hWb ∘L ((fourierL2 n).symm : L2 n →L[ℂ] L2 n) ∘L
      mulCLM hgm hgb ∘L (fourierL2 n : L2 n →L[ℂ] L2 n),
    cpt_core hWm hWb hW2 hWs hgm hgb hg2 (by linarith) hgs, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ hε.le fun φ => ?_
  set f := fourierL2 n φ
  have hdiff : ‖mulCLM (mres_cont (n := n)).aestronglyMeasurable mres_bound f -
      mulCLM hgm hgb f‖ ≤ 1 / (1 + M) * ‖f‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [Lp.coeFn_sub (mulCLM (mres_cont (n := n)).aestronglyMeasurable mres_bound f)
      (mulCLM hgm hgb f), mulCLM_ae (mres_cont (n := n)).aestronglyMeasurable mres_bound f,
      mulCLM_ae hgm hgb f] with ξ h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, ← sub_mul, norm_mul]
    by_cases hξ : ‖ξ‖ ≤ M
    · rw [hgdef, Set.indicator_of_mem (by simpa using hξ), sub_self, norm_zero, zero_mul]
      positivity
    · push Not at hξ
      rw [hgs ξ hξ, sub_zero]
      gcongr
      exact mres_tail hM1 ξ hξ
  have heq : (mulCLM hWm hWb ∘L R0 n - mulCLM hWm hWb ∘L
      ((fourierL2 n).symm : L2 n →L[ℂ] L2 n) ∘L mulCLM hgm hgb ∘L
        (fourierL2 n : L2 n →L[ℂ] L2 n)) φ =
      mulCLM hWm hWb ((fourierL2 n).symm
        (mulCLM (mres_cont (n := n)).aestronglyMeasurable mres_bound f - mulCLM hgm hgb f)) := by
    simp only [R0, ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, map_sub]
    rfl
  rw [heq]
  refine (norm_mulCLM_apply_le _ _ _).trans ?_
  rw [LinearIsometryEquiv.norm_map]
  calc B * ‖mulCLM (mres_cont (n := n)).aestronglyMeasurable mres_bound f - mulCLM hgm hgb f‖
      ≤ B * (1 / (1 + M) * ‖f‖) := by gcongr
    _ = B / (1 + M) * ‖φ‖ := by rw [LinearIsometryEquiv.norm_map]; ring
    _ ≤ ε * ‖φ‖ := by
        gcongr
        rw [div_le_iff₀ (by linarith)]; linarith

open FHAux in
/-- `W(x) (H₀+1)⁻¹` is compact for bounded `W` vanishing at infinity. -/
lemma cpt_bvi {W : E → ℂ} {B : ℝ} (hWm : AEStronglyMeasurable W volume)
    (hWb : ∀ x, ‖W x‖ ≤ B) (hWt : Tendsto W (cocompact E) (𝓝 0)) :
    IsCompactOperator (mulCLM hWm hWb ∘L R0 n) := by
  refine cpt_of_approx _ fun ε hε => ?_
  obtain ⟨t, ht, hts⟩ := Filter.mem_cocompact.mp (hWt (Metric.ball_mem_nhds 0 hε))
  obtain ⟨N, hN⟩ := ht.isBounded.subset_closedBall 0
  set WN : E → ℂ := (Metric.closedBall (0 : E) N).indicator W with hWNdef
  have hWNm : AEStronglyMeasurable WN volume :=
    hWm.indicator Metric.isClosed_closedBall.measurableSet
  have hWNb : ∀ x, ‖WN x‖ ≤ B := fun x => (norm_indicator_le_norm_self _ _).trans (hWb x)
  have hWNs : ∀ x, N < ‖x‖ → WN x = 0 := fun x hx =>
    Set.indicator_of_notMem (by simpa using hx) _
  refine ⟨mulCLM hWNm hWNb ∘L R0 n, cpt_cs hWNm hWNb hWNs, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ hε.le fun φ => ?_
  set f := R0 n φ
  have heq : (mulCLM hWm hWb ∘L R0 n - mulCLM hWNm hWNb ∘L R0 n) φ =
      mulCLM hWm hWb f - mulCLM hWNm hWNb f := rfl
  rw [heq]
  calc ‖mulCLM hWm hWb f - mulCLM hWNm hWNb f‖ ≤ ε * ‖f‖ := by
        refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
        filter_upwards [Lp.coeFn_sub (mulCLM hWm hWb f) (mulCLM hWNm hWNb f),
          mulCLM_ae hWm hWb f, mulCLM_ae hWNm hWNb f] with x h1 h2 h3
        rw [h1, Pi.sub_apply, h2, h3, ← sub_mul, norm_mul]
        by_cases hx : ‖x‖ ≤ N
        · rw [hWNdef, Set.indicator_of_mem (by simpa using hx), sub_self, norm_zero, zero_mul]
          positivity
        · push Not at hx
          rw [hWNs x hx, sub_zero]
          gcongr
          have hxt : x ∉ t := fun h => by
            have := hN h; simp at this; linarith
          have := hts hxt
          simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at this
          exact this.le
    _ ≤ ε * ‖φ‖ := by gcongr; exact norm_R0_apply_le φ

lemma memLp_mres (hn : n ≤ 3) : MemLp (fun ξ : E => (laplaceSymbol n ξ - (-1))⁻¹) 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm (mres_cont (n := n)).aestronglyMeasurable).2 ?_
  have h := SobAux.integrable_wt_inv_sq (n := n) hn le_rfl
  refine h.congr (Eventually.of_forall fun ξ => ?_)
  have : laplaceSymbol n ξ - (-1) = ((SobAux.wt 1 ξ : ℝ) : ℂ) := by
    unfold laplaceSymbol SobAux.wt; push_cast; ring
  simp only
  rw [this, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (SobAux.wt_pos one_pos ξ)]

open FHAux in
/-- For `n ≤ 3`, `(H₀+1)⁻¹` maps `L²` boundedly into `L^∞`. -/
lemma R0_sup (hn : n ≤ 3) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ φ : L2 n, ∀ᵐ x ∂volume, ‖(R0 n φ : E → ℂ) x‖ ≤ K * ‖φ‖ := by
  refine ⟨L2c (fun ξ : E => (laplaceSymbol n ξ - (-1))⁻¹), L2c_nonneg _, fun φ => ?_⟩
  set G := mulCLM (mres_cont (n := n)).aestronglyMeasurable mres_bound (fourierL2 n φ)
  have hGae : (G : E → ℂ) =ᵐ[volume]
      fun ξ => (laplaceSymbol n ξ - (-1))⁻¹ * (fourierL2 n φ) ξ := mulCLM_ae _ _ _
  have hGint : Integrable (G : E → ℂ) :=
    ((memLp_mres hn).integrable_mul (Lp.memLp (fourierL2 n φ))).congr hGae.symm
  have hGL1 : ∫ ξ, ‖(G : E → ℂ) ξ‖ ≤
      L2c (fun ξ : E => (laplaceSymbol n ξ - (-1))⁻¹) * ‖φ‖ := by
    calc ∫ ξ, ‖(G : E → ℂ) ξ‖ = ∫ ξ, ‖(laplaceSymbol n ξ - (-1))⁻¹‖ * ‖(fourierL2 n φ) ξ‖ := by
          apply integral_congr_ae
          filter_upwards [hGae] with ξ h
          rw [h, norm_mul]
      _ ≤ _ := int_mul_le _ (memLp_mres hn) _
      _ = _ := by rw [LinearIsometryEquiv.norm_map]
  have hR : R0 n φ = (fourierL2 n).symm G := rfl
  filter_upwards [SobAux.fourierInv_L2_ae_eq G hGint] with x hx
  rw [hR, fourierL2_symm_eq, hx]
  exact (norm_fourierInv_le _ x).trans hGL1

end RCAux

open MeasureTheory TeschlQM.OneParticle Filter Topology

namespace RCAux

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

lemma memLp_mul_R0 {W : E → ℂ} (hW : MemLp W 2 volume) {K : ℝ}
    (hK : ∀ φ : L2 n, ∀ᵐ x ∂volume, ‖(R0 n φ : E → ℂ) x‖ ≤ K * ‖φ‖) (φ : L2 n) :
    MemLp (fun x => W x * (R0 n φ : E → ℂ) x) 2 volume := by
  refine (hW.const_mul ((K * ‖φ‖ : ℝ) : ℂ)).of_le
    (hW.1.mul (Lp.aestronglyMeasurable _)) ?_
  filter_upwards [hK φ] with x hx
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
  gcongr
  exact hx.trans (le_abs_self _)

/-- The operator `φ ↦ W · (H₀+1)⁻¹ φ` for `W ∈ L²`, given an `L^∞` bound on `(H₀+1)⁻¹`. -/
noncomputable def mulL2 {W : E → ℂ} (hW : MemLp W 2 volume) {K : ℝ}
    (hK : ∀ φ : L2 n, ∀ᵐ x ∂volume, ‖(R0 n φ : E → ℂ) x‖ ≤ K * ‖φ‖) : L2 n →L[ℂ] L2 n :=
  LinearMap.mkContinuous
    { toFun := fun φ => (memLp_mul_R0 hW hK φ).toLp _
      map_add' := fun f g => by
        ext1
        filter_upwards [(memLp_mul_R0 hW hK (f + g)).coeFn_toLp,
          Lp.coeFn_add ((memLp_mul_R0 hW hK f).toLp _) ((memLp_mul_R0 hW hK g).toLp _),
          (memLp_mul_R0 hW hK f).coeFn_toLp, (memLp_mul_R0 hW hK g).coeFn_toLp,
          Lp.coeFn_add (R0 n f) (R0 n g)] with x h1 h2 h3 h4 h5
        rw [h1, h2, Pi.add_apply, h3, h4, map_add, h5, Pi.add_apply, mul_add]
      map_smul' := fun c f => by
        ext1
        filter_upwards [(memLp_mul_R0 hW hK (c • f)).coeFn_toLp,
          Lp.coeFn_smul c ((memLp_mul_R0 hW hK f).toLp _),
          (memLp_mul_R0 hW hK f).coeFn_toLp, Lp.coeFn_smul c (R0 n f)] with x h1 h2 h3 h4
        rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, map_smul, h4, Pi.smul_apply,
          smul_eq_mul, smul_eq_mul]
        ring }
    (K * ‖hW.toLp W‖) fun φ => by
      change ‖(memLp_mul_R0 hW hK φ).toLp _‖ ≤ _
      calc ‖(memLp_mul_R0 hW hK φ).toLp _‖ ≤ (K * ‖φ‖) * ‖hW.toLp W‖ := by
            refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
            filter_upwards [(memLp_mul_R0 hW hK φ).coeFn_toLp, hW.coeFn_toLp, hK φ]
              with x h1 h2 h3
            rw [h1, h2, norm_mul, mul_comm]
            gcongr
        _ = K * ‖hW.toLp W‖ * ‖φ‖ := by ring

lemma mulL2_ae {W : E → ℂ} (hW : MemLp W 2 volume) {K : ℝ}
    (hK : ∀ φ : L2 n, ∀ᵐ x ∂volume, ‖(R0 n φ : E → ℂ) x‖ ≤ K * ‖φ‖) (φ : L2 n) :
    (mulL2 hW hK φ : E → ℂ) =ᵐ[volume] fun x => W x * (R0 n φ : E → ℂ) x :=
  (memLp_mul_R0 hW hK φ).coeFn_toLp

open FHAux in
/-- `W (H₀+1)⁻¹` is compact for `W ∈ L²` (given the `L^∞` bound on the resolvent). -/
lemma cpt_mulL2 {W : E → ℂ} (hW : MemLp W 2 volume) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ φ : L2 n, ∀ᵐ x ∂volume, ‖(R0 n φ : E → ℂ) x‖ ≤ K * ‖φ‖) :
    IsCompactOperator (mulL2 hW hK) := by
  refine cpt_of_approx _ fun ε hε => ?_
  set δ := ε / (K + 1) with hδ
  have hδ0 : 0 < δ := div_pos hε (by linarith)
  obtain ⟨g, hgc, hgW, hgcont, hg2⟩ := hW.exists_hasCompactSupport_eLpNorm_sub_le
    (by norm_num) (ε := ENNReal.ofReal δ) (by simpa using hδ0)
  obtain ⟨B, hB⟩ := hgcont.bounded_above_of_compact_support hgc
  obtain ⟨N, hN⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  have hgs : ∀ x, N < ‖x‖ → g x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport
    fun h => by have := hN h; simp at this; linarith
  have hgm : AEStronglyMeasurable g volume := hgcont.aestronglyMeasurable
  refine ⟨mulCLM hgm hB ∘L R0 n, cpt_cs hgm hB hgs, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ hε.le fun φ => ?_
  have hd := hW.sub hg2
  have hdn : ‖hd.toLp (W - g)‖ ≤ δ := by
    rw [Lp.norm_toLp]; exact ENNReal.toReal_le_of_le_ofReal hδ0.le hgW
  calc ‖(mulL2 hW hK - mulCLM hgm hB ∘L R0 n) φ‖
      ≤ (K * ‖φ‖) * ‖hd.toLp (W - g)‖ := by
        refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
        filter_upwards [Lp.coeFn_sub (mulL2 hW hK φ) (mulCLM hgm hB (R0 n φ)),
          mulL2_ae hW hK φ, mulCLM_ae hgm hB (R0 n φ), hd.coeFn_toLp, hK φ]
          with x h1 h2 h3 h4 h5
        change ‖((mulL2 hW hK φ - mulCLM hgm hB (R0 n φ) : L2 n) : E → ℂ) x‖ ≤ _
        rw [h1, Pi.sub_apply, h2, h3, h4, ← sub_mul, norm_mul, mul_comm, Pi.sub_apply]
        gcongr
    _ ≤ (K * ‖φ‖) * δ := by gcongr
    _ ≤ ε * ‖φ‖ := by
        have : K * δ ≤ ε := by
          rw [hδ, mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
        nlinarith [norm_nonneg φ]

end RCAux

open MeasureTheory TeschlQM.OneParticle Filter Topology

namespace RCAux

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

open FHAux in
lemma main_of (V V1 V2 : E → ℝ) (hV : V = V1 + V2) (h1 : IsBoundedVanishingAtInfinity V1)
    (C2 : L2 n →L[ℂ] L2 n) (hC2 : IsCompactOperator C2)
    (hC2ae : ∀ φ, (C2 φ : E → ℂ) =ᵐ[volume] fun x => (V2 x : ℂ) * (R0 n φ : E → ℂ) x) :
    TeschlQM.Shared.IsRelativelyCompact (multOp (fun x => (V x : ℂ))) (freeHamiltonian n) := by
  obtain ⟨hm, ⟨C, hC⟩, ht⟩ := h1
  set W1 : E → ℂ := fun x => (V1 x : ℂ)
  have hW1m : AEStronglyMeasurable W1 volume :=
    (Complex.measurable_ofReal.comp hm).aestronglyMeasurable
  have hW1b : ∀ x, ‖W1 x‖ ≤ C := fun x => by
    simp only [W1, Complex.norm_real, Real.norm_eq_abs]; exact hC x
  have hW1t : Tendsto W1 (cocompact E) (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp ht
    rw [Complex.ofReal_zero] at this
    exact this
  refine ⟨-1, R0 n, R0_isResolvent, mulCLM hW1m hW1b ∘L R0 n + C2,
    (cpt_bvi hW1m hW1b hW1t).add hC2, fun φ => ?_⟩
  have hae : ((mulCLM hW1m hW1b ∘L R0 n + C2) φ : E → ℂ) =ᵐ[volume]
      fun x => (V x : ℂ) * (R0 n φ : E → ℂ) x := by
    filter_upwards [Lp.coeFn_add (mulCLM hW1m hW1b (R0 n φ)) (C2 φ),
      mulCLM_ae hW1m hW1b (R0 n φ), hC2ae φ] with x h1 h2 h3
    change ((mulCLM hW1m hW1b (R0 n φ) + C2 φ : L2 n) : E → ℂ) x = _
    rw [h1, Pi.add_apply, h2, h3, hV, Pi.add_apply]
    simp only [W1]; push_cast; ring
  have hmem : MemLp (fun x => (V x : ℂ) * (R0 n φ : E → ℂ) x) 2 volume :=
    (Lp.memLp _).ae_eq hae
  refine ⟨hmem, ?_⟩
  ext1
  filter_upwards [hmem.coeFn_toLp, hae] with x h1 h2
  exact h1.trans h2.symm

theorem potential_relativelyCompact (n : ℕ) (V : EuclideanSpace ℝ (Fin n) → ℝ)
    (hV_large : 3 < n → IsBoundedVanishingAtInfinity V)
    (hV_small : n ≤ 3 → ∃ V₁ V₂ : EuclideanSpace ℝ (Fin n) → ℝ,
      IsBoundedVanishingAtInfinity V₁ ∧ MemLp V₂ 2 volume ∧ V = V₁ + V₂) :
    TeschlQM.Shared.IsRelativelyCompact (multOp (fun x => (V x : ℂ))) (freeHamiltonian n) := by
  by_cases h3 : 3 < n
  · refine main_of V V 0 (by simp) (hV_large h3) 0 isCompactOperator_zero fun φ => ?_
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))] with x hx
    simp
  · obtain ⟨V1, V2, h1, h2, hV⟩ := hV_small (by omega)
    obtain ⟨K, hK0, hK⟩ := R0_sup (n := n) (by omega)
    have hW2 : MemLp (fun x => (V2 x : ℂ)) 2 volume := h2.ofReal
    exact main_of V V1 V2 hV h1 (mulL2 hW2 hK) (cpt_mulL2 hW2 hK0 hK) (mulL2_ae hW2 hK)

end RCAux

open TeschlQM.OneParticle in
theorem solution (n : ℕ) (hn : 1 ≤ n) (V : EuclideanSpace ℝ (Fin n) → ℝ)
    (hV_large : 3 < n → IsBoundedVanishingAtInfinity V)
    (hV_small : n ≤ 3 → ∃ V₁ V₂ : EuclideanSpace ℝ (Fin n) → ℝ,
      IsBoundedVanishingAtInfinity V₁ ∧ MemLp V₂ 2 volume ∧ V = V₁ + V₂) :
    TeschlQM.Shared.IsRelativelyCompact (multOp (fun x => (V x : ℂ))) (freeHamiltonian n) :=
  RCAux.potential_relativelyCompact n V hV_large hV_small

