-- Prove2me | solution 1 for RHInBoxAnalytic.zeta_blaschke_split_ball
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:33:20.298512+00:00
-- url     : https://prove2.me/submissions/ac965e27-f855-4eab-8d98-20a48881bec6

import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Mathlib
/- Task 2 (parameterized RH-in-a-box): generalize the zeta Blaschke split + box argument
   principle from the merged FIXED ball `ball cB 13` / fixed corners to an ARBITRARY box
   `[sigma0, sigma1] x [T0, T1]` with a VARIABLE Blaschke ball `(c, R)`, the geometry entering
   only as hypotheses `hRpos`, `hbox_ball`, `hs1` (and the box-ordering `hsig`, `hT`).

   This file reproduces, over variable corners and a variable ball, the three merged atoms
     - the per-pole interior winding `Bd((z-ρ)^{-1}) = 2*pi*I` (branch-split primitive),
     - the residue-sum linearity `Bd(∑ d/(z-ρ)) = 2*pi*I*∑ d`,
     - the analytic E-arg-principle `Bd(E) = 0` (Mathlib `integral_boundary_rect_eq_zero...`),
   and the KERNEL-DERIVED local Blaschke split of `logDeriv riemannZeta` over the variable ball
   (`MeromorphicOn.extract_zeros_poles`, E-holomorphicity in-kernel), then composes them into
     `RHInBoxAnalytic.zeta_count_eq_winding_generic`:
   the actual divisor of `riemannZeta` over `ball c R` is nonneg, captures every box zero, and its
   total equals the Arb winding integer `N` (derived from `hwind` via the argument principle).

   Divisor-support finiteness is obtained from `IsCompact.inter_riemannZetaZeros_finite`
   (compact `closedBall c R` meets `riemannZetaZeros` finitely), NOT from meromorphy on the closed
   ball -- so no assumption is needed about the pole `1` on the closed-ball boundary; only
   `1 ∉ ball c R` (open) enters, exactly as the brief requires.

   conjecture1_proved = False.  This is a kernel derivation of a parameterized argument-principle
   count; it does NOT prove RH. -/


open Complex Filter MeasureTheory Real
open scoped Topology

namespace RHInBoxAnalytic

/-! ## Part A: function-agnostic log-derivative transfer across a codiscrete equality.
    (Verbatim from the merged `BlaschkeBox.lean`; pure Mathlib, function-agnostic.) -/

/-- Log-derivatives agree wherever the functions agree on a NEIGHBORHOOD. -/
theorem logDeriv_congr_nhds {f₁ f₂ : ℂ → ℂ} {z : ℂ} (h : f₁ =ᶠ[nhds z] f₂) :
    logDeriv f₁ z = logDeriv f₂ z := by
  rw [logDeriv_apply, logDeriv_apply, h.deriv_eq, h.eq_of_nhds]

/-- Log-derivatives agree at any point of an OPEN set on which the functions agree. -/
theorem logDeriv_congr_eqOn_open {f₁ f₂ : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U) (h : Set.EqOn f₁ f₂ U) :
    logDeriv f₁ z = logDeriv f₂ z :=
  logDeriv_congr_nhds (Filter.eventuallyEq_of_mem (hU.mem_nhds hz) h)

/-- **Codiscrete transfer.** -/
theorem logDeriv_congr_of_codiscrete {f₁ f₂ : ℂ → ℂ} {U : Set ℂ} {z₀ z : ℂ}
    (hf₁ : AnalyticOnNhd ℂ f₁ U) (hf₂ : AnalyticOnNhd ℂ f₂ U)
    (hU : IsOpen U) (hUc : IsPreconnected U) (hz₀ : z₀ ∈ U) (hz : z ∈ U)
    (h : f₁ =ᶠ[Filter.codiscreteWithin U] f₂) :
    logDeriv f₁ z = logDeriv f₂ z := by
  have hmem : {x | f₁ x = f₂ x} ∪ Uᶜ ∈ 𝓝[≠] z₀ :=
    (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp h) z₀ hz₀
  have hU_nhds : U ∈ 𝓝[≠] z₀ := mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hz₀)
  have hev : ∀ᶠ x in 𝓝[≠] z₀, f₁ x = f₂ x := by
    filter_upwards [hmem, hU_nhds] with x hx hxU
    rcases hx with h1 | h2
    · exact h1
    · exact absurd hxU h2
  exact logDeriv_congr_eqOn_open hU hz
    (hf₁.eqOn_of_preconnected_of_frequently_eq hf₂ hUc hz₀ hev.frequently)

/-! ## Part B: log-derivative of the factorized-rational product.  (Verbatim.) -/

theorem logDeriv_factor {u z : ℂ} (d : ℤ) (_hzu : z - u ≠ 0) :
    logDeriv (fun w : ℂ => (w - u) ^ d) z = (d : ℂ) / (z - u) := by
  have hdiff : DifferentiableAt ℂ (fun w : ℂ => w - u) z := by fun_prop
  rw [logDeriv_fun_zpow hdiff d]
  have : logDeriv (fun w : ℂ => w - u) z = 1 / (z - u) := by
    rw [logDeriv_apply]
    have hderiv : deriv (fun w : ℂ => w - u) z = 1 := by
      simp [deriv_sub_const (f := fun w : ℂ => w) u (x := z)]
    rw [hderiv]
  rw [this]; ring

theorem logDeriv_finset_prod {T : Finset ℂ} (D : ℂ → ℤ) (z : ℂ)
    (hz : ∀ u ∈ T, z - u ≠ 0) :
    logDeriv (fun w : ℂ => ∏ u ∈ T, (w - u) ^ (D u)) z
      = ∑ u ∈ T, (D u : ℂ) / (z - u) := by
  have hne : ∀ u ∈ T, ((fun w : ℂ => (w - u) ^ (D u)) z) ≠ 0 :=
    fun u hu => zpow_ne_zero _ (hz u hu)
  have hdiff : ∀ u ∈ T, DifferentiableAt ℂ (fun w : ℂ => (w - u) ^ (D u)) z := by
    intro u hu
    have hbase : DifferentiableAt ℂ (fun w : ℂ => w - u) z := by fun_prop
    exact (differentiableAt_zpow.2 (Or.inl (hz u hu))).comp z hbase
  set F : ℂ → ℂ → ℂ := fun u w => (w - u) ^ (D u) with hF
  have hfun : (fun w : ℂ => ∏ u ∈ T, (w - u) ^ (D u)) = fun w : ℂ => ∏ u ∈ T, F u w := rfl
  rw [hfun, logDeriv_prod (s := T) (f := F) (x := z) hne hdiff]
  exact Finset.sum_congr rfl (fun u hu => logDeriv_factor (D u) (hz u hu))

/-! ## Part C: `riemannZeta` meromorphic-order facts on `{1}ᶜ`.  (Verbatim from merged.) -/

theorem meromorphicOrderAt_zeta_ne_top :
    ∀ u ∈ ({1}ᶜ : Set ℂ), meromorphicOrderAt riemannZeta u ≠ ⊤ := by
  have hconn : IsConnected ({1}ᶜ : Set ℂ) :=
    isConnected_compl_singleton_of_one_lt_rank (by simp) 1
  have hMero : MeromorphicOn riemannZeta ({1}ᶜ : Set ℂ) := analyticOn_riemannZeta.meromorphicOn
  have h2mem : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  have hz2 : AnalyticAt ℂ riemannZeta 2 := analyticOn_riemannZeta 2 h2mem
  have hne2 : riemannZeta 2 ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by norm_num)
  have hord2 : meromorphicOrderAt riemannZeta 2 ≠ ⊤ := by
    rw [hz2.meromorphicOrderAt_eq, hz2.analyticOrderAt_eq_zero.mpr hne2]; simp
  intro u hu
  exact hMero.meromorphicOrderAt_ne_top_of_isPreconnected hconn.isPreconnected h2mem hu hord2

/-! ## Part D: generic per-pole interior winding and residue-sum atoms over variable corners.

    Generalizes `WindingCount.winding_lambda_five_rect_winding` and
    `BoxArgPrinciple.box_residue_sum_lambda` from the fixed corners `2/5,3/5,10,35` to variable
    `sigma0 < ρ.re < sigma1`, `T0 < ρ.im < T1`. -/











/-! ## Part E: variable-ball local Blaschke split of `logDeriv riemannZeta`.

    Generalizes `BlaschkeBox.zeta_blaschke_split_box` to an arbitrary ball `(c, R)` whose interior
    avoids `1` (`hs1`) and whose box `[σ0,σ1]x[T0,T1] ⊆ ball c R` (`hbox_ball`).  Divisor
    finiteness comes from `IsCompact.inter_riemannZetaZeros_finite`. -/





theorem mem_zeroFinset {c : ℂ} {R : ℝ} (hs1 : (1 : ℂ) ∉ Metric.ball c R) {ρ : ℂ} :
    ρ ∈ zeroFinset c R hs1 ↔
      ρ ∈ (MeromorphicOn.divisor riemannZeta (Metric.ball c R)).support := by
  rw [zeroFinset, Set.Finite.mem_toFinset]



/-! ## Part F: the parameterized capstone. -/



end RHInBoxAnalytic


/- Task 2 (parameterized RH-in-a-box): generalize the zeta Blaschke split + box argument
   principle from the merged FIXED ball `ball cB 13` / fixed corners to an ARBITRARY box
   `[sigma0, sigma1] x [T0, T1]` with a VARIABLE Blaschke ball `(c, R)`, the geometry entering
   only as hypotheses `hRpos`, `hbox_ball`, `hs1` (and the box-ordering `hsig`, `hT`).

   This file reproduces, over variable corners and a variable ball, the three merged atoms
     - the per-pole interior winding `Bd((z-ρ)^{-1}) = 2*pi*I` (branch-split primitive),
     - the residue-sum linearity `Bd(∑ d/(z-ρ)) = 2*pi*I*∑ d`,
     - the analytic E-arg-principle `Bd(E) = 0` (Mathlib `integral_boundary_rect_eq_zero...`),
   and the KERNEL-DERIVED local Blaschke split of `logDeriv riemannZeta` over the variable ball
   (`MeromorphicOn.extract_zeros_poles`, E-holomorphicity in-kernel), then composes them into
     `RHInBoxAnalytic.zeta_count_eq_winding_generic`:
   the actual divisor of `riemannZeta` over `ball c R` is nonneg, captures every box zero, and its
   total equals the Arb winding integer `N` (derived from `hwind` via the argument principle).

   Divisor-support finiteness is obtained from `IsCompact.inter_riemannZetaZeros_finite`
   (compact `closedBall c R` meets `riemannZetaZeros` finitely), NOT from meromorphy on the closed
   ball -- so no assumption is needed about the pole `1` on the closed-ball boundary; only
   `1 ∉ ball c R` (open) enters, exactly as the brief requires.

   conjecture1_proved = False.  This is a kernel derivation of a parameterized argument-principle
   count; it does NOT prove RH. -/


open Complex Filter MeasureTheory Real
open scoped Topology

section
namespace RHInBoxAnalytic
end RHInBoxAnalytic
open RHInBoxAnalytic

/-! ## Part A: function-agnostic log-derivative transfer across a codiscrete equality.
    (Verbatim from the merged `BlaschkeBox.lean`; pure Mathlib, function-agnostic.) -/







/-! ## Part B: log-derivative of the factorized-rational product.  (Verbatim.) -/





/-! ## Part C: `riemannZeta` meromorphic-order facts on `{1}ᶜ`.  (Verbatim from merged.) -/



/-! ## Part D: generic per-pole interior winding and residue-sum atoms over variable corners.

    Generalizes `WindingCount.winding_lambda_five_rect_winding` and
    `BoxArgPrinciple.box_residue_sum_lambda` from the fixed corners `2/5,3/5,10,35` to variable
    `sigma0 < ρ.re < sigma1`, `T0 < ρ.im < T1`. -/











/-! ## Part E: variable-ball local Blaschke split of `logDeriv riemannZeta`.

    Generalizes `BlaschkeBox.zeta_blaschke_split_box` to an arbitrary ball `(c, R)` whose interior
    avoids `1` (`hs1`) and whose box `[σ0,σ1]x[T0,T1] ⊆ ball c R` (`hbox_ball`).  Divisor
    finiteness comes from `IsCompact.inter_riemannZetaZeros_finite`. -/







theorem solution
    (sigma0 sigma1 T0 T1 : ℝ) (c : ℂ) (R : ℝ)
    (hRpos : 0 < R)
    (hbox_ball : ∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R)
    (hs1 : (1 : ℂ) ∉ Metric.ball c R) :
    ∃ (E : ℂ → ℂ),
      DifferentiableOn ℂ E (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) ∧
      (∀ ρ ∈ zeroFinset c R hs1,
        (1 : ℤ) ≤ (MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ) ∧
      (∀ ρ ∈ Metric.ball c R, riemannZeta ρ = 0 → ρ ∈ zeroFinset c R hs1) ∧
      (∀ z ∈ Metric.ball c R, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ zeroFinset c R hs1,
          ((MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ : ℂ) / (z - ρ)) + E z) := by
  set U := Metric.ball c R with hUdef
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hUconn : IsPreconnected U := (convex_ball c R).isPreconnected
  have hUsub : U ⊆ ({1}ᶜ : Set ℂ) := by
    intro z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl; exact hs1 hz
  have hbox_sub : (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) ⊆ U := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    exact hbox_ball z hz.1 hz.2
  have hζU : AnalyticOnNhd ℂ riemannZeta U := analyticOn_riemannZeta.mono hUsub
  have hMeroU : MeromorphicOn riemannZeta U := hζU.meromorphicOn
  -- Divisor support is finite: it sits inside `closedBall c R ∩ riemannZetaZeros`.
  set D : ℂ → ℤ := fun u => (MeromorphicOn.divisor riemannZeta U : ℂ → ℤ) u with hDdef
  have hDnn : ∀ x, 0 ≤ D x := fun x => MeromorphicOn.AnalyticOnNhd.divisor_nonneg hζU x
  -- support point ⇒ zero of zeta.
  have hsupp_zero : ∀ u, u ∈ Function.support D → riemannZeta u = 0 := by
    intro u hu
    rw [Function.mem_support] at hu
    have huU : u ∈ U := (MeromorphicOn.divisor riemannZeta U).supportWithinDomain
      (by rw [Function.mem_support]; exact hu)
    by_contra hne
    apply hu
    simp only [hDdef]
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hζU huU,
      (hζU u huU).analyticOrderAt_eq_zero.mpr hne]; simp
  have hZfin : ((Metric.closedBall c R) ∩ riemannZetaZeros).Finite :=
    (isCompact_closedBall c R).inter_riemannZetaZeros_finite
  have hDfin : (Function.support D).Finite := by
    apply hZfin.subset
    intro u hu
    have huU : u ∈ U := (MeromorphicOn.divisor riemannZeta U).supportWithinDomain
      (by rw [Function.mem_support]; rw [Function.mem_support] at hu; exact hu)
    exact ⟨Metric.ball_subset_closedBall huU, hsupp_zero u hu⟩
  have h₃f : (MeromorphicOn.divisor riemannZeta U).support.Finite := hDfin
  have h₂f : ∀ u : U, meromorphicOrderAt riemannZeta u ≠ ⊤ :=
    fun u => meromorphicOrderAt_zeta_ne_top u.1 (hUsub u.2)
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := hMeroU.extract_zeros_poles h₂f h₃f
  set T : Finset ℂ := zeroFinset c R hs1 with hTdef
  -- `T = h₃f.toFinset`: both are `Set.Finite.toFinset` of the same support set.
  have hTmem : ∀ u, u ∈ T ↔ u ∈ (MeromorphicOn.divisor riemannZeta U).support := by
    intro u; rw [hTdef]; exact mem_zeroFinset hs1
  have hTsetEq : (T : Set ℂ) = Function.support D := by
    ext u; rw [Finset.mem_coe, hTmem u]
  -- Factorized-rational product reduced to a Finset product (verbatim structure from merged).
  have hPf_finset : (∏ᶠ u, (· - u) ^ (MeromorphicOn.divisor riemannZeta U u))
      = fun w : ℂ => ∏ u ∈ T, (w - u) ^ (D u) := by
    rw [Function.FactorizedRational.finprod_eq_fun (d := D) hDfin]
    ext w
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := T) ?_]
    · intro u hu
      rw [Finset.mem_coe, hTmem u]
      by_contra hc
      rw [Function.mem_support, not_not] at hc
      rw [Function.mem_mulSupport] at hu
      exact hu (by rw [show D u = (MeromorphicOn.divisor riemannZeta U) u from rfl, hc, zpow_zero])
  set Pf : ℂ → ℂ := fun w : ℂ => ∏ u ∈ T, (w - u) ^ (D u) with hPfdef
  have hPf_an : AnalyticOnNhd ℂ Pf U := by
    rw [← hPf_finset]; intro x _; exact Function.FactorizedRational.analyticAt (hDnn x)
  set P : ℂ → ℂ := fun z => Pf z * g z with hPdef
  have hP_an : AnalyticOnNhd ℂ P U := fun x hx => (hPf_an x hx).mul (hg_an x hx)
  have hg_eqP : riemannZeta =ᶠ[Filter.codiscreteWithin U] P := by
    have hPeq : ((∏ᶠ u, (· - u) ^ (MeromorphicOn.divisor riemannZeta U u)) • g) = P := by
      rw [hPf_finset]; ext w; simp [hPdef, hPfdef]
    rw [← hPeq]; exact hg_eq
  have hT_zero : ∀ u ∈ T, riemannZeta u = 0 := by
    intro u hu
    rw [hTmem u, Function.mem_support] at hu
    exact hsupp_zero u (by rw [Function.mem_support]; exact hu)
  -- Provide the existential witness `E := logDeriv g`.
  refine ⟨logDeriv g, ?_, ?_, ?_, ?_⟩
  · -- E holomorphic on the box (subset of U).
    have hE_an : AnalyticOnNhd ℂ (logDeriv g) U := by
      intro x hx
      have : logDeriv g = fun z => deriv g z / g z := by
        ext z; rw [logDeriv_apply]
      rw [this]
      exact (hg_an x hx).deriv.div (hg_an x hx) (hg_ne ⟨x, hx⟩)
    exact (hE_an.mono hbox_sub).differentiableOn
  · -- multiplicity `d ρ ≥ 1` at every support point.
    intro ρ hρ
    rw [hTmem ρ, Function.mem_support] at hρ
    have hρU : ρ ∈ U := (MeromorphicOn.divisor riemannZeta U).supportWithinDomain
      (by rw [Function.mem_support]; exact hρ)
    have hρzero : riemannZeta ρ = 0 := hsupp_zero ρ (by rw [Function.mem_support]; exact hρ)
    have hAtρ : AnalyticAt ℂ riemannZeta ρ := hζU ρ hρU
    have hord_ne : analyticOrderAt riemannZeta ρ ≠ 0 :=
      hAtρ.analyticOrderAt_ne_zero.mpr hρzero
    have hfin : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
      intro hcontra
      exact meromorphicOrderAt_zeta_ne_top ρ (hUsub hρU)
        (by rw [hAtρ.meromorphicOrderAt_eq, hcontra]; rfl)
    have hDeq : (MeromorphicOn.divisor riemannZeta U : ℂ → ℤ) ρ
        = (analyticOrderNatAt riemannZeta ρ : ℤ) := by
      have hda : (MeromorphicOn.divisor riemannZeta U : ℂ → ℤ) ρ
          = ((analyticOrderAt riemannZeta ρ).map (Nat.cast)).untop₀ :=
        MeromorphicOn.AnalyticOnNhd.divisor_apply hζU hρU
      rw [hda, ← Nat.cast_analyticOrderNatAt hfin]; rfl
    have hnat_ne : analyticOrderNatAt riemannZeta ρ ≠ 0 := by
      rw [Ne, ← Nat.cast_analyticOrderNatAt hfin] at hord_ne
      simpa using hord_ne
    show (1 : ℤ) ≤ (MeromorphicOn.divisor riemannZeta U : ℂ → ℤ) ρ
    rw [hDeq]
    have : 1 ≤ analyticOrderNatAt riemannZeta ρ := Nat.one_le_iff_ne_zero.mpr hnat_ne
    exact_mod_cast this
  · -- every zeta zero in U lies in the support.
    intro ρ hρU hρzero
    rw [hTmem ρ, Function.mem_support]
    have hAtρ : AnalyticAt ℂ riemannZeta ρ := hζU ρ hρU
    have hord_ne : analyticOrderAt riemannZeta ρ ≠ 0 :=
      hAtρ.analyticOrderAt_ne_zero.mpr hρzero
    have hfin : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
      intro hcontra
      exact meromorphicOrderAt_zeta_ne_top ρ (hUsub hρU)
        (by rw [hAtρ.meromorphicOrderAt_eq, hcontra]; rfl)
    have hDeq : (MeromorphicOn.divisor riemannZeta U : ℂ → ℤ) ρ
        = (analyticOrderNatAt riemannZeta ρ : ℤ) := by
      have hda : (MeromorphicOn.divisor riemannZeta U : ℂ → ℤ) ρ
          = ((analyticOrderAt riemannZeta ρ).map (Nat.cast)).untop₀ :=
        MeromorphicOn.AnalyticOnNhd.divisor_apply hζU hρU
      rw [hda, ← Nat.cast_analyticOrderNatAt hfin]; rfl
    have hnat_ne : analyticOrderNatAt riemannZeta ρ ≠ 0 := by
      rw [Ne, ← Nat.cast_analyticOrderNatAt hfin] at hord_ne
      simpa using hord_ne
    rw [hDeq]
    exact_mod_cast hnat_ne
  · -- the split at each z ∈ U off the zeros.
    intro z hz hznz
    have hzroots : ∀ u ∈ T, z - u ≠ 0 := by
      intro u hu hcontra
      rw [sub_eq_zero] at hcontra
      exact hznz (by rw [hcontra]; exact hT_zero u hu)
    have hPfz : Pf z ≠ 0 := by
      rw [hPfdef]
      exact Finset.prod_ne_zero_iff.mpr (fun u hu => zpow_ne_zero _ (hzroots u hu))
    have hgz : g z ≠ 0 := hg_ne ⟨z, hz⟩
    have hPf_diff : DifferentiableAt ℂ Pf z := (hPf_an z hz).differentiableAt
    have hg_diff : DifferentiableAt ℂ g z := (hg_an z hz).differentiableAt
    have htrans : logDeriv riemannZeta z = logDeriv P z :=
      logDeriv_congr_of_codiscrete hζU hP_an hUopen hUconn hz hz hg_eqP
    -- The goal sum ranges over `zeroFinset c R hs1 = T` with divisor `= D`.
    rw [htrans, hPdef, logDeriv_mul z hPfz hgz hPf_diff hg_diff, hPfdef]
    rw [logDeriv_finset_prod D z hzroots]
