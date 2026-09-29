-- Prove2me | solution 1 for Zeta23.Analytic.rectangleIntegralPrime_mul_logDeriv_of_poles
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:37:02.873759+00:00
-- url     : https://prove2.me/submissions/26550a14-2964-4528-9fba-60fa4b864d78

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Definitions.Def_Zeta23_Analytic_RectangleLogDeriv
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Definitions.Def_Extra_Zeta23_Analytic_RectangleLogDeriv
import Theorems.Thm_Zeta23_Analytic_residueTheorem_finset

-- from Zeta23.FromPNTPlus.Rectangle
section
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/Rectangle.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint tooling (import Architect,
@[blueprint ...] attributes).
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

namespace Rectangle



end Rectangle




@[simp]
theorem preimage_equivRealProdCLM_reProdIm (s t : Set ℝ) :
    equivRealProdCLM.symm ⁻¹' (s ×ℂ t) = s ×ˢ t :=
  rfl

@[simp]
theorem ContinuousLinearEquiv.coe_toLinearEquiv_symm {R : Type*} {S : Type*} [Semiring R]
    [Semiring S] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] (e : M ≃SL[σ] M₂) :
    ⇑e.toLinearEquiv.symm = e.symm :=
  rfl



















lemma rectangle_mem_nhds_iff {z w p : ℂ} :
    Rectangle z w ∈ 𝓝 p ↔ p ∈ (Set.uIoo z.re w.re) ×ℂ (Set.uIoo z.im w.im) := by
  simp_rw [← mem_interior_iff_mem_nhds, Rectangle, Complex.interior_reProdIm, uIoo, uIcc,
    interior_Icc]

















end

-- from Zeta23.Analytic.RectangleLogDeriv
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Residue calculus on rectangles beyond one simple pole.
Used for the weighted contour integral ∮ H·Λ'/Λ and for the Riemann–von Mangoldt count
N(T₁,T₂) = (1/2πi)∮ Λ'/Λ.

* `residueTheorem_finset`: f holomorphic on Rectangle z w minus a finite set S of interior points, with
  f − A p/(s − p) bounded near each p ∈ S  ⟹  RectangleIntegral' f z w = Σ_{p∈S} A p.
  (Induction on S: subtract one principal part, remove the singularity, recurse.)
* `rectangleIntegral'_mul_logDeriv` (the "argument principle with weight"): f, g analytic on a
  neighbourhood of each point of Rectangle z w, f ≠ 0 on the border, Z = the (finite) zero set of
  f in the rectangle  ⟹  RectangleIntegral' (g · f'/f) z w = Σ_{ρ∈Z} ord_ρ(f) · g(ρ).
* `finite_zeros_rectangle`, `rectangleIntegral'_mul_logDeriv'`: the zero set is finite; self-contained form.
-/

open Complex Set Topology Filter Asymptotics Real

noncomputable section

namespace Zeta23
namespace Analytic



/-! ## Meromorphic version: finitely many zeros AND poles inside the rectangle

Intended for f = completedRiemannZeta (simple poles at 0 and 1, residues ∓1):
(1/2πi) ∮ g·(f'/f) = Σ_{zeros ρ} ord_ρ(f)·g(ρ) − Σ_{poles p} m_p·g(p).
A pole of order m at p is witnessed elementarily by  (s − p)^m · f(s) → c ≠ 0  (s → p, s ≠ p),
which is the shape of Mathlib's `completedRiemannZeta_residue_one` (m = 1). -/





end Analytic
end Zeta23
end
open Complex Set Topology Filter Asymptotics Real
open Zeta23
open Analytic

theorem solution {f g : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re)
    (him : z.im ≤ w.im) (Z P : Finset ℂ) (hZP : Disjoint Z P)
    (hPint : ∀ p ∈ P, Rectangle z w ∈ 𝓝 p)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w \ (P : Set ℂ)))
    (hg : AnalyticOnNhd ℂ g (Rectangle z w))
    (hborder : ∀ s ∈ RectangleBorder z w, f s ≠ 0)
    (hZ : ∀ s ∈ Rectangle z w \ (P : Set ℂ), f s = 0 ↔ s ∈ Z) (hZsub : (Z : Set ℂ) ⊆ Rectangle z w)
    (m : ℂ → ℕ)
    (hpole : ∀ p ∈ P, ∃ c : ℂ, c ≠ 0 ∧ Tendsto (fun s => (s - p) ^ m p * f s) (𝓝[≠] p) (𝓝 c)) :
    RectangleIntegral' (fun s => g s * logDeriv f s) z w
      = ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * g ρ - ∑ p ∈ P, (m p : ℂ) * g p := by
  classical
  have hZnotP : ∀ ρ ∈ Z, ρ ∉ P := fun ρ hρ hρP => Finset.disjoint_left.mp hZP hρ hρP
  have hZmem : ∀ ρ ∈ Z, ρ ∈ Rectangle z w \ (P : Set ℂ) := fun ρ hρ =>
    ⟨hZsub hρ, by simpa using hZnotP ρ hρ⟩
  -- zeros are interior points
  have hZint : ∀ ρ ∈ Z, Rectangle z w ∈ 𝓝 ρ := by
    intro ρ hρ
    have hρR : ρ ∈ Rectangle z w := hZsub hρ
    have hρB : ρ ∉ RectangleBorder z w := fun h => hborder ρ h ((hZ ρ (hZmem ρ hρ)).mpr hρ)
    obtain ⟨h1, h2⟩ := hρR
    have h1' : z.re ≤ ρ.re ∧ ρ.re ≤ w.re := by simpa [uIcc_of_le hre] using h1
    have h2' : z.im ≤ ρ.im ∧ ρ.im ≤ w.im := by simpa [uIcc_of_le him] using h2
    simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff, not_or] at hρB
    obtain ⟨⟨⟨hb1, hb2⟩, hb3⟩, hb4⟩ := hρB
    rw [rectangle_mem_nhds_iff, mem_reProdIm, uIoo_of_le hre, uIoo_of_le him]
    refine ⟨⟨lt_of_le_of_ne h1'.1 (fun h => hb2 ⟨h.symm, h2⟩),
      lt_of_le_of_ne h1'.2 (fun h => hb4 ⟨h, h2⟩)⟩,
      ⟨lt_of_le_of_ne h2'.1 (fun h => hb1 ⟨h1, h.symm⟩),
      lt_of_le_of_ne h2'.2 (fun h => hb3 ⟨h1, h⟩)⟩⟩
  -- residues: +ord·g at zeros, −m·g at poles
  let A : ℂ → ℂ := fun q => if q ∈ P then -((m q : ℂ) * g q) else (analyticOrderNatAt f q : ℂ) * g q
  have hint : ∀ q ∈ Z ∪ P, Rectangle z w ∈ 𝓝 q := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    exacts [hZint q hq, hPint q hq]
  have key := residueTheorem_finset (f := fun s => g s * logDeriv f s) hre him (Z ∪ P) A hint
    ?holo ?near
  · rw [key, Finset.sum_union hZP]
    have hZsum : ∑ q ∈ Z, A q = ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * g ρ :=
      Finset.sum_congr rfl (fun q hq => by simp [A, hZnotP q hq])
    have hPsum : ∑ q ∈ P, A q = -∑ p ∈ P, (m p : ℂ) * g p := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun q hq => by simp [A, hq])
    rw [hZsum, hPsum, sub_eq_add_neg]
  case holo =>
    intro s hs
    have hsP : s ∉ P := fun h => hs.2 (by simp [h])
    have hsZ : s ∉ Z := fun h => hs.2 (by simp [h])
    have hsRP : s ∈ Rectangle z w \ (P : Set ℂ) := ⟨hs.1, by simpa using hsP⟩
    have hfs : f s ≠ 0 := fun h => hsZ ((hZ s hsRP).mp h)
    have hfa := hf s hsRP
    have hga := hg s hs.1
    apply DifferentiableAt.differentiableWithinAt
    show DifferentiableAt ℂ (fun s => g s * (deriv f s / f s)) s
    exact hga.differentiableAt.mul (hfa.deriv.differentiableAt.div hfa.differentiableAt hfs)
  case near =>
    intro q hq
    rcases Finset.mem_union.mp hq with hρ | hp
    · ---------------- a zero ρ := q
      have hρRP := hZmem q hρ
      have hga := hg q (hZsub hρ)
      have hA : A q = (analyticOrderNatAt f q : ℂ) * g q := by simp [A, hZnotP q hρ]
      by_cases htop : analyticOrderAt f q = ⊤
      · -- f vanishes identically near q: everything is 0
        have h0 : ∀ᶠ s in 𝓝 q, f s = 0 := analyticOrderAt_eq_top.mp htop
        have hO : (fun _ : ℂ => (0 : ℂ)) =O[𝓝[≠] q] (1 : ℂ → ℂ) := isBigO_zero _ _
        refine hO.congr' ?_ EventuallyEq.rfl
        filter_upwards [mem_nhdsWithin_of_mem_nhds (h0.eventually_nhds)] with s hs
        have hs' : f =ᶠ[𝓝 s] fun _ => (0 : ℂ) := hs
        have hds : deriv f s = 0 := by
          rw [hs'.deriv_eq]; simp
        simp [hA, logDeriv_apply, hds, analyticOrderNatAt, htop]
      obtain ⟨h, hh, hh0, hfh⟩ := (hf q hρRP).analyticOrderAt_ne_top.mp htop
      have hh_ne : ∀ᶠ s in 𝓝 q, h s ≠ 0 := hh.continuousAt.eventually_ne hh0
      have h2 : ∀ᶠ s in 𝓝 q, f =ᶠ[𝓝 s] (fun s => (s - q) ^ analyticOrderNatAt f q • h s) :=
        hfh.eventually_nhds
      have h3 : ∀ᶠ s in 𝓝 q, AnalyticAt ℂ h s := hh.eventually_analyticAt
      have hexp : ∀ᶠ s in 𝓝[≠] q,
          (analyticOrderNatAt f q : ℂ) * ((g s - g q) / (s - q)) + g s * logDeriv h s
            = ((fun s => g s * logDeriv f s) - fun s => A q / (s - q)) s := by
        filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds h2,
          mem_nhdsWithin_of_mem_nhds hh_ne, mem_nhdsWithin_of_mem_nhds h3]
          with s hs hfs hhs hhas
        have hsq : s - q ≠ 0 := sub_ne_zero.mpr (by simpa using hs)
        have hld : logDeriv f s = (analyticOrderNatAt f q : ℂ) / (s - q) + logDeriv h s := by
          have e1 : logDeriv f s
              = logDeriv (fun s => (s - q) ^ analyticOrderNatAt f q * h s) s := by
            simp only [logDeriv_apply, hfs.deriv_eq, hfs.self_of_nhds, smul_eq_mul]
          rw [e1, logDeriv_mul (f := fun s : ℂ => (s - q) ^ analyticOrderNatAt f q) (g := h) s
            (pow_ne_zero _ hsq) hhs (by fun_prop) hhas.differentiableAt]
          have e2 : logDeriv (fun s : ℂ => (s - q) ^ analyticOrderNatAt f q) s
              = (analyticOrderNatAt f q : ℂ) / (s - q) := by
            rw [show (fun s : ℂ => (s - q) ^ analyticOrderNatAt f q)
                = (fun x : ℂ => x ^ analyticOrderNatAt f q) ∘ (fun s => s - q) from rfl,
              logDeriv_comp (by fun_prop) (by fun_prop), logDeriv_pow]
            simp
          rw [e2]
        simp only [Pi.sub_apply, hld, hA]
        ring
      have hslope : Tendsto (fun s => (g s - g q) / (s - q)) (𝓝[≠] q) (𝓝 (deriv g q)) := by
        have := hasDerivAt_iff_tendsto_slope.mp hga.differentiableAt.hasDerivAt
        simpa only [slope_fun_def_field] using this
      have hcont : Tendsto (fun s => g s * logDeriv h s) (𝓝[≠] q)
          (𝓝 (g q * logDeriv h q)) := by
        have : ContinuousAt (fun s => g s * logDeriv h s) q := by
          show ContinuousAt (fun s => g s * (deriv h s / h s)) q
          exact hga.continuousAt.mul (hh.deriv.continuousAt.div hh.continuousAt hh0)
        exact this.tendsto.mono_left nhdsWithin_le_nhds
      have hO : (fun s => (analyticOrderNatAt f q : ℂ) * ((g s - g q) / (s - q))
          + g s * logDeriv h s) =O[𝓝[≠] q] (1 : ℂ → ℂ) :=
        ((hslope.const_mul (analyticOrderNatAt f q : ℂ)).add hcont).isBigO_one ℂ
      exact hO.congr' hexp EventuallyEq.rfl
    · ---------------- a pole p := q
      obtain ⟨c, hc, hT⟩ := hpole q hp
      have hqR : q ∈ Rectangle z w := mem_of_mem_nhds (hPint q hp)
      have hga := hg q hqR
      have hA : A q = -((m q : ℂ) * g q) := by simp [A, hp]
      -- the regularisation G := (s − q)^m · f, extended by c at q: analytic at q, G q ≠ 0
      set F : ℂ → ℂ := fun s => (s - q) ^ m q * f s with hF
      set G : ℂ → ℂ := Function.update F q c with hG
      have hGq : G q = c := Function.update_self _ _ _
      have hGF : ∀ s, s ≠ q → G s = F s := fun s hs => Function.update_of_ne hs _ _
      have hPc : ((P : Set ℂ) \ {q})ᶜ ∈ 𝓝 q :=
        (P.finite_toSet.subset Set.diff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
      have hnear : ∀ᶠ s in 𝓝[≠] q, s ≠ q ∧ s ∈ Rectangle z w \ (P : Set ℂ) := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds (hPint q hp),
          mem_nhdsWithin_of_mem_nhds hPc, self_mem_nhdsWithin] with s h1 h2 h3
        have h3' : s ≠ q := by simpa using h3
        exact ⟨h3', h1, fun hsP => h2 ⟨hsP, by simpa using h3'⟩⟩
      have hGdiff : ∀ᶠ s in 𝓝[≠] q, DifferentiableAt ℂ G s := by
        filter_upwards [hnear] with s ⟨hsq, hsRP⟩
        have hFs : DifferentiableAt ℂ F s :=
          ((differentiableAt_id.sub_const q).pow _).mul (hf s hsRP).differentiableAt
        refine hFs.congr_of_eventuallyEq ?_
        filter_upwards [isOpen_compl_singleton.mem_nhds hsq] with x hx
        exact hGF x hx
      have hGcont : ContinuousAt G q := by
        rw [hG, continuousAt_update_same]
        exact hT
      have hGan : AnalyticAt ℂ G q :=
        analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hGdiff hGcont
      have hG0 : G q ≠ 0 := by rwa [hGq]
      have hFne : ∀ᶠ s in 𝓝[≠] q, F s ≠ 0 := hT.eventually_ne hc
      have hGan' : ∀ᶠ s in 𝓝 q, AnalyticAt ℂ G s := hGan.eventually_analyticAt
      have hexp : ∀ᶠ s in 𝓝[≠] q,
          g s * logDeriv G s - (m q : ℂ) * ((g s - g q) / (s - q))
            = ((fun s => g s * logDeriv f s) - fun s => A q / (s - q)) s := by
        filter_upwards [hnear, hFne, mem_nhdsWithin_of_mem_nhds hGan'] with s ⟨hsq, hsRP⟩ hFs hGs
        have hsq' : s - q ≠ 0 := sub_ne_zero.mpr hsq
        have hfs : f s ≠ 0 := fun h => hFs (by simp [hF, h])
        have hfd : DifferentiableAt ℂ f s := (hf s hsRP).differentiableAt
        have hldF : logDeriv F s = (m q : ℂ) / (s - q) + logDeriv f s := by
          rw [hF, logDeriv_mul (f := fun s : ℂ => (s - q) ^ m q) (g := f) s
            (pow_ne_zero _ hsq') hfs (by fun_prop) hfd]
          have e2 : logDeriv (fun s : ℂ => (s - q) ^ m q) s = (m q : ℂ) / (s - q) := by
            rw [show (fun s : ℂ => (s - q) ^ m q) = (fun x : ℂ => x ^ m q) ∘ (fun s => s - q)
                from rfl, logDeriv_comp (by fun_prop) (by fun_prop), logDeriv_pow]
            simp
          rw [e2]
        have hGFs : G =ᶠ[𝓝 s] F := by
          filter_upwards [isOpen_compl_singleton.mem_nhds hsq] with x hx
          exact hGF x hx
        have hldG : logDeriv G s = logDeriv F s := by
          simp only [logDeriv_apply, hGFs.deriv_eq, hGFs.self_of_nhds]
        simp only [Pi.sub_apply, hA, hldG, hldF]
        ring
      have hslope : Tendsto (fun s => (g s - g q) / (s - q)) (𝓝[≠] q) (𝓝 (deriv g q)) := by
        have := hasDerivAt_iff_tendsto_slope.mp hga.differentiableAt.hasDerivAt
        simpa only [slope_fun_def_field] using this
      have hcont : Tendsto (fun s => g s * logDeriv G s) (𝓝[≠] q)
          (𝓝 (g q * logDeriv G q)) := by
        have : ContinuousAt (fun s => g s * logDeriv G s) q := by
          show ContinuousAt (fun s => g s * (deriv G s / G s)) q
          exact hga.continuousAt.mul (hGan.deriv.continuousAt.div hGan.continuousAt hG0)
        exact this.tendsto.mono_left nhdsWithin_le_nhds
      have hO : (fun s => g s * logDeriv G s - (m q : ℂ) * ((g s - g q) / (s - q)))
          =O[𝓝[≠] q] (1 : ℂ → ℂ) :=
        (hcont.sub (hslope.const_mul (m q : ℂ))).isBigO_one ℂ
      exact hO.congr' hexp EventuallyEq.rfl
