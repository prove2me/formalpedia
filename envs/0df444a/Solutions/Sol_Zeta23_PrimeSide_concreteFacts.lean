-- Prove2me | solution 1 for Zeta23.PrimeSide.concreteFacts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T02:32:21.319505+00:00
-- url     : https://prove2.me/submissions/5e31973a-b64f-4d68-9df5-7b3d13b54312

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Mertens
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Definitions.Def_Zeta23_PrimeSideA_EndsCore
import Definitions.Def_Zeta23_PrimeSideA_EndsE1
import Definitions.Def_Zeta23_PrimeSideA_EndsE2
import Definitions.Def_Zeta23_PrimeSideA_EndsNu
import Definitions.Def_Zeta23_PrimeSideB
import Definitions.Def_Zeta23_PrimeSideB_Concrete
import Definitions.Def_Zeta23_PrimeSideB_PP
import Definitions.Def_Zeta23_PrimeSideB_PPKernel
import Definitions.Def_Zeta23_PrimeSideB_Traces
import Definitions.Def_Zeta23_PrimeSideTemp
import Theorems.Thm_Zeta23_PrimeSide_LocalHyps_toCore
import Theorems.Thm_Zeta23_PrimeSide_eq_Msplit
import Theorems.Thm_Zeta23_PrimeSide_evBound_of_eventuallyAt
import Theorems.Thm_Zeta23_PrimeSide_lem_ends
import Theorems.Thm_Zeta23_PrimeSide_prop_PP
import Theorems.Thm_Zeta23_PrimeSide_prop_cross_PPi
import Theorems.Thm_Zeta23_PrimeSide_prop_cross_PiPi
import Theorems.Thm_Zeta23_PrimeSide_prop_cross_muP
import Theorems.Thm_Zeta23_PrimeSide_prop_cross_muPi
import Theorems.Thm_Zeta23_PrimeSide_prop_mumu
import Theorems.Thm_Zeta23_PrimeSide_prop_trace
import Theorems.Thm_Zeta23_PrimeSide_rvm_evBound
import Theorems.Thm_Zeta23_PrimeSide_sum_a2g_lowerPrime
import Theorems.Thm_Zeta23_PrimeSide_sum_a2g_upperPrime

-- from Zeta23.PrimeSideB
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization of the paper
"More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/

/-!
# Prime side, part B: [prop:PP] and the assembly of Theorem [thm:traces]

Paper §5 ("The prime side: magnitude"), subsections "Evaluation of 𝓜" and "Summary".

Contents
* §0 glue between the explicit-constant interface shape `EvBound` and Mathlib's `IsBigO`.
* §1 `Zeta23.PaperParams`: elementary facts about the scalar parameters `l, ℓ₁, L, X, λ₁, 𝓔_T`
  of `Defs.lean` (growth, positivity, `𝓔_T → 0`).  Pure real analysis, no hypotheses.
* §2 `Zeta23.PrimeSide.Facts` / `Zeta23.PrimeSide.tracesBounds_of_facts`: the proof of [thm:traces]
  ([eq:tr1], [eq:tr2], [eq:ratio], second forms) from the five sub-results of §5 + [eq:muints] (H-Γ)
  + [eq:RvM] (H-RvM) + [eq:abdef] (Taper), all taken as hypotheses on abstract real functions of `T`.
  This is where the paper's constants `ℓ₁² + L²/3` and `F(λ₁)` are checked.
* §3 [prop:PP]: `𝓜[P_X,P_X] = (T/π) Σ_{n≤X} Λ(n)²/n · g(log n) + O(L² X)` and the sandwich
  `(L−2w)³/6 + O(L²) ≤ Σ a_n² g(y_n) ≤ L³/6 + O(L²)` — over the concrete definitions of `Defs.lean`
  and `Mform`.
-/

noncomputable section

open Real Filter Asymptotics Topology

namespace Zeta23

/-! ## §0.  Explicit-constant ↔ `IsBigO` glue -/

namespace EvBound






/-- An eventual pointwise bound with an explicit constant gives an `EvBound`. -/
lemma of_eventually_le {f g : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ T in atTop, |f T| ≤ c * g T) : EvBound f g := by
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp h
  exact ⟨c, hc, T₀, hT₀⟩

lemma eventually_le {f g : ℝ → ℝ} (h : EvBound f g) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T in atTop, |f T| ≤ C * g T := by
  obtain ⟨C, hC, T₀, hT⟩ := h
  exact ⟨C, hC, eventually_atTop.mpr ⟨T₀, hT⟩⟩




/-- Change `f` up to eventual pointwise domination. -/
lemma of_abs_le {f f' g : ℝ → ℝ} (h : EvBound f g) (h' : ∀ᶠ T in atTop, |f' T| ≤ |f T|) :
    EvBound f' g := by
  obtain ⟨C, hC, h⟩ := h.eventually_le
  refine of_eventually_le hC ?_
  filter_upwards [h, h'] with T a b using b.trans a

lemma congr_left {f f' g : ℝ → ℝ} (h : EvBound f g) (h' : ∀ᶠ T in atTop, f' T = f T) :
    EvBound f' g := h.of_abs_le (h'.mono fun T hT => by rw [hT])


end EvBound

/-! ## §1.  The scalar parameters of `Defs.lean` -/

namespace PaperParams

lemma l_tendsto_atTop : Tendsto l atTop atTop := by
  unfold l
  exact Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))





variable (P : Params)



lemma L_tendsto_atTop (hP : 0 < P.lam) : Tendsto P.L atTop atTop := by
  unfold Params.L
  exact l_tendsto_atTop.const_mul_atTop hP

lemma log_l_tendsto_atTop : Tendsto (fun T => Real.log (l T)) atTop atTop :=
  Real.tendsto_log_atTop.comp l_tendsto_atTop

lemma eventually_l_ge (c : ℝ) : ∀ᶠ T in atTop, c ≤ l T := l_tendsto_atTop.eventually_ge_atTop c

lemma eventually_log_l_ge (c : ℝ) : ∀ᶠ T in atTop, c ≤ Real.log (l T) :=
  log_l_tendsto_atTop.eventually_ge_atTop c

lemma eventually_L_ge (hlam : 0 < P.lam) (c : ℝ) : ∀ᶠ T in atTop, c ≤ P.L T :=
  (L_tendsto_atTop P hlam).eventually_ge_atTop c







lemma eventually_one_le_X (hlam : 0 < P.lam) : ∀ᶠ T in atTop, 1 ≤ P.X T := by
  filter_upwards [eventually_L_ge P hlam 0] with T hL
  simpa [Params.X] using Real.one_le_exp hL


variable {P}







end PaperParams

/-! ## §2.  Assembly of Theorem [thm:traces] from the §5 sub-results

All quantities are real functions of `T` at fixed `P = (ϱ, λ, w)`.  The hypotheses below are exactly
the conclusions of [prop:trace], [lem:ends], [eq:Msplit], [prop:mumu], [prop:PP], [prop:cross]
(the paper §5), [eq:muints] (from H-Γ), [eq:RvM] (H-RvM) and [eq:abdef] (Taper), each in the
explicit-constant form `EvBound`. -/

namespace PrimeSide

open PaperParams


variable {P : Params} (D : Data P)


/-! ### The assembly -/

section assembly
variable {D} (h : Facts D)
include h













end assembly

end PrimeSide

/-! ## §3.  [prop:PP]

Statement over `Mform` and `Defs.lean`'s `PX, PhiR, g`,
via the 𝒟 / 𝒪₁ / 𝒪₂ decomposition [eq:MPP]. -/

end Zeta23

end
end

-- from Zeta23.PrimeSideA.Basic
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization of
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/


-- Contains: LocalHyps, EventuallyAt, the 𝓜-bilinearity/sup-bound lemmas, the large-T regime
-- lemmas, and all per-grid-point lemmas for [prop:trace].

/-!
# Prime side, part A — paper §5 [sec:prime]:  [prop:trace], [lem:ends], [eq:Msplit], [prop:mumu], [prop:cross]

Seam with `PrimeSideB.lean` ([prop:PP], [thm:traces]): see the header of
`Zeta23/PrimeSideA/Defs.lean`.  Everything here is ζ-free: the zeros never
appear in §5 ("In this section the zeros play no role", §5); `N(T,2T)` enters [prop:trace]
only through [eq:muints] + [eq:RvM], which we take as hypotheses on an abstract real `N`.

## Shape of the results
All error terms are explicit inequalities, uniform in `T`:
  `∃ C, EventuallyAt cϱ lam (fun p F => |lhs p F − main p F| ≤ C * err p)`
where `EventuallyAt cϱ lam P` means: there is `T₀` such that `P p F` holds for every parameter set
`p` with `p.lam = lam`, `T₀ ≤ p.T` and every taper datum `F` satisfying `LocalHyps cϱ p F`.
So `C` and `T₀` may depend on `c_ϱ`, on the constants inside H-Γ/H-cheb, and on `λ` — the paper
has `C` depending on ϱ only and `T₀ = T₀(λ)` (§5.5); ours is the (weaker, sufficient at fixed λ)
reading.  This is a deviation from the paper.

## Hypotheses consumed (all proved elsewhere in the repository; none is a Lean axiom)
* `Zeta23.GammaFacts` (H-Γ [eq:mufacts]+[eq:muints]) and `Zeta23.ChebyshevMertens` (H-cheb
  [lem:cheb]) — Zeta23/Hypotheses.lean, verbatim (fields of `PaperInputs`).
* `LocalHyps cϱ p F` — taper/test-family facts [eq:psidef], [eq:abdef], [eq:gbounds], [eq:Phi2FT],
                      `∫φ̂² = 2πaL`, `Φ(0) = aL`, `∫Φ² = 2πbL`;
                      [lem:poisson] (★); [eq:PiPfacts] for Π_X;
                      parameter regime [eq:wrange], `0<λ≤1`.
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction

namespace Zeta23
namespace PrimeSide

/-! ## Hypothesis packages

H-Γ and H-cheb are Zeta23/Hypotheses.lean's `Zeta23.GammaFacts` and `Zeta23.ChebyshevMertens` (about the
concrete `Zeta23.mu` and Λ-sums), taken verbatim.  The taper/test-family facts are packaged here: -/




/-! ### Bilinearity and symmetry of 𝓜[·,·] (§5.4: "a symmetric bilinear form (Φ² is even)") -/

section MformLemmas
variable {Φ : ℝ → ℝ} {T : ℝ}








end MformLemmas


/-! ### The "insert sup bounds" estimate for 𝓜[·,·]  (§5.4) -/

section SupBound
variable {Φ : ℝ → ℝ} {T : ℝ}



end SupBound


/-! ### The large-T regime: elementary consequences of the hypotheses -/

section Regime
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}






lemma LocalHyps.eight_le_L (hF : LocalHyps cϱ p F) : 8 ≤ p.L := by
  linarith [hF.one_le_w, hF.w_le]

lemma LocalHyps.L_pos (hF : LocalHyps cϱ p F) : 0 < p.L := by linarith [hF.eight_le_L]





/-! ### Window-generic core of the taper hypotheses (paper §7.1 [subsec:MT])

"Nothing in Sections 4–5 used that φ is flat-topped" — except the [eq:gbounds] plateau lower
bound and the [eq:abdef] lower bound on b.  LocalHypsCore is LocalHyps minus exactly those two
facts, with the window-generic replacements g_nonneg and b_ge_half (both hold for the
Montgomery–Taylor window of [thm:D], which does not satisfy LocalHyps).  Surviving field names
are identical to LocalHyps'.  The window-generic §5 results can be re-typed over this
structure; the structure itself is purely additive. -/





theorem EventuallyAtCore.to_eventuallyAt {cϱ lam : ℝ} {P : Setting → LocalFun → Prop}
    (h : EventuallyAtCore cϱ lam P) : EventuallyAt cϱ lam P := by
  obtain ⟨T₀, hT₀⟩ := h
  exact ⟨T₀, fun p F hl hT hF => hT₀ p F hl hT hF.toCore⟩

/-! Core copies of the LocalHyps helper lemmas (same names under the Core namespace). -/






















end Regime

/-! ### Elementary lemmas for [prop:trace] -/

section TraceLemmas




variable {cϱ : ℝ} {p : Setting} {F : LocalFun}




end TraceLemmas

/-! ### Analytic lemmas for [prop:trace]: growth and increments of μ, decay of Π_X -/

section TraceAnalytic
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}






















end TraceAnalytic

end PrimeSide
end Zeta23
end
end

-- from Zeta23.PrimeSideB.Concrete
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
  Part of the Zeta23 formalization of the paper
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/

/-!
# The concrete prime-side data as an instance of the abstract layer
Small, dependency-light file (imports only `PrimeSideA.Basic` and `PrimeSideTemp`):

* `Params.toSetting P T = ⟨T, λ, w⟩`, `Params.localFun P T = ⟨φ̂|_ℝ, Φ|_ℝ, A_φ, g, a, b⟩(T)` and the
  `rfl` bridges (`trGtA (P.toSetting T) (P.localFun T) = P.trGtilde T`, …);
* `PrimeSide.LocalHypsEventually cϱ P` — "the taper facts `LocalHyps` hold for the concrete data for
  all large `T`" (proved in `Zeta23/PrimeSideA/Bridge.lean`);
* `PrimeSide.evBound_of_eventuallyAt` — an `EventuallyAt`-form result specialised to the concrete
  data is an `EvBound` in `T`.
-/

noncomputable section

open Real Filter Topology MeasureTheory
open scoped BigOperators ArithmeticFunction

namespace Zeta23

namespace Params
variable (P : Params) (T : ℝ)



@[simp] lemma toSetting_T : (P.toSetting T).T = T := rfl
@[simp] lemma toSetting_lam : (P.toSetting T).lam = P.lam := rfl
@[simp] lemma toSetting_w : (P.toSetting T).w = P.w := rfl
@[simp] lemma toSetting_L : (P.toSetting T).L = P.L T := rfl
@[simp] lemma toSetting_X : (P.toSetting T).X = P.X T := rfl
@[simp] lemma toSetting_l : (P.toSetting T).l = l T := rfl
@[simp] lemma toSetting_ell1 : (P.toSetting T).ell1 = ell1 T := rfl
@[simp] lemma toSetting_d : (P.toSetting T).d = P.d T := rfl
@[simp] lemma toSetting_tau (k : ℤ) : (P.toSetting T).tau k = P.tau T k := rfl
@[simp] lemma localFun_a : (P.localFun T).a = P.a T := rfl
@[simp] lemma localFun_b : (P.localFun T).b = P.b T := rfl
@[simp] lemma localFun_Phi : (P.localFun T).Phi = P.PhiR T := rfl
@[simp] lemma localFun_g : (P.localFun T).g = P.g T := rfl
@[simp] lemma localFun_phiHat : (P.localFun T).phiHat = P.phiHatR T := rfl

end Params

namespace PrimeSide

variable (P : Params) (T : ℝ)


/-- `tr G̃` of the abstract layer on the concrete data is `Params.trGtilde`. -/
lemma trGtA_concrete : trGtA (P.toSetting T) (P.localFun T) = P.trGtilde T := rfl

/-- `tr G̃²` of the abstract layer on the concrete data is `Params.trGtildeSq`. -/
lemma trGt2A_concrete : trGt2A (P.toSetting T) (P.localFun T) = P.trGtildeSq T := rfl


variable {P}




end PrimeSide

end Zeta23

end
end

-- from Zeta23.PrimeSideB.PP
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Prime side, part B/PP — paper §5 [prop:PP] (§5.4): the term 𝓜[P_X,P_X]

Consumed by `Zeta23/PrimeSideB.lean` ([thm:traces]) through the three results at the bottom of
this file:

* `prop_PP`        [prop:PP] first form (§5.4):
      𝓜[P_X,P_X] = (T/π) Σ_{n≤X} Λ(n)²/n · g(log n) + O(L²X);
* `sum_a2g_lower`, `sum_a2g_upper`  (§5.4, the "Finally" step, from [eq:gbounds]+[eq:cheb2]):
      (L−2w)³/6 − C·L² ≤ Σ_{n≤X} Λ(n)²/n · g(log n) ≤ L³/6 + C·L²,
  which give the paper's second form  𝓜[P_X,P_X] = (TL³/6π)(1+O(w/L)) + O(L²X).

Everything is stated in the abstract prime-side layer (Zeta23/PrimeSideA/Defs.lean +
`LocalHyps`/`EventuallyAt` of Zeta23/PrimeSideA.lean): `p : Setting` = (T, λ, w), `F : LocalFun` =
the taper data (φ̂, Φ, A_φ, g, a, b) subject to `LocalHyps cϱ p F` (the facts [eq:psidef],
[eq:abdef], [eq:gbounds], [eq:Phi2FT], …, each a proof obligation of Zeta23/Taper.lean, not an
axiom).  `P_X` is `Zeta23.PX` [eq:Pdef] of Zeta23/Defs.lean and 𝓜[·,·] is
`Zeta23.PrimeSide.Mform` (§5.4).  Analytic inputs: H-cheb = `Zeta23.ChebyshevMertens` [lem:cheb]
and H-MV = `Zeta23.MVHilbert` [lem:MV] from Zeta23/Hypotheses.lean (fields of `PaperInputs`).

## Proof route (paper §5.4, reorganised for Lean; labels as in the paper)
1. Bilinearity:  𝓜[P_X,P_X] = π⁻² Σ_{n,m≤X} a_n a_m 𝓜[cos(·y_n), cos(·y_m)],  a_n = Λ(n)/√n, y_n = log n.
2. Shear `(τ,τ') ↦ (x,τ') := (τ−τ',τ')` (measure-preserving on ℝ²) + Fubini  (§5.4 "Substituting
   τ = τ'+x … τ' ranges over I∩(I−x) = [T+x⁻, 2T−x⁺]"):
      𝓜[u,v] = ∫_{|x|≤T} Φ(x)² ∫_{max(T,T−x)}^{min(2T,2T−x)} u(τ'+x) v(τ') dτ' dx.
3. cos A cos B = ½cos(A−B) + ½cos(A+B): inner integral = ½J(xy_n, y_n−y_m) + ½J(xy_n, y_n+y_m),
   J(c,θ) := ∫_α^β cos(c+θτ')dτ' = (β−α)cos c (θ=0), = [sin(c+θβ)−sin(c+θα)]/θ (θ≠0), |J| ≤ 2/|θ|.
4. 𝒟 (n=m, "−"):  ½∫_{|x|≤T}Φ²(T−|x|)cos(xy_n) = πT g(y_n) + O(∫Φ²|x|)   by [eq:Phi2FT];
   𝒪₂ (all n,m, "+"):  ≤ (∫Φ²)(Σa_n)²/(2π² log 2) ≪ XL                        by [eq:cheb1];
   𝒪₁ (n≠m, "−"):  an explicit combination of 8 sums Σ_{n≠m} x_n conj(z_m)/(y_n−y_m) with
   |x_n| = a_n, |z_m| ≤ a_m ∫Φ², each ≤ C_MV·(∫Φ²)·Σ a_n²/δ_n with δ_n = 1/(2n) [eq:deltan] ≪ L²X by H-MV
   and [eq:cheb1] (Σ Λ(n)² ≪ X log X).
Constants: the paper's O(L²X) constant (and the λ=1 "18/L" sharpness) is not load-bearing;
we prove ∃ C.
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction

namespace Zeta23
namespace PrimeSide

variable {cϱ lam : ℝ}

/-! ## The main-term sum  Σ_{n≤X} a_n² g(y_n) = Σ_{n≤X} Λ(n)²/n · g(log n)   (§5.4) -/



/-! ## Elementary facts about the index range and `X = e^L` -/

section Basics
variable {p : Setting} {F : LocalFun}





end Basics

/-! ## The g-sandwich  (§5.4)

"Finally, by [eq:gbounds] and [eq:cheb2] (note a_n² = Λ(n)²/n),
  (L−2w)³/6 + O(L²) = Σ_{n≤Xe^{−2w}} a_n²(L−2w−y_n) ≤ Σ_{n≤X} a_n² g(y_n) ≤ Σ_{n≤X} a_n²(L−y_n) = L³/6+O(L²)". -/

section Sandwich
variable {p : Setting} {F : LocalFun}



end Sandwich

/-! ## Assembly of [prop:PP]  (§5.4) -/

section Assembly
variable {Φ : ℝ → ℝ} {T : ℝ}





end Assembly

/-! ## Results consumed by PrimeSideB.lean -/

section Results


/-- **[prop:PP], the g-sandwich, lower half** (§5.4, verbatim):
"(L−2w)³/6 + O(L²) = Σ_{n≤Xe^{−2w}} a_n²(L−2w−y_n) ≤ Σ_{n≤X} a_n² g(y_n)",
"by [eq:gbounds] and [eq:cheb2] (note a_n² = Λ(n)²/n)".  One-sided, explicit-slack form. -/
theorem sum_a2g_lower (hcheb : Zeta23.ChebyshevMertens) (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAt cϱ lam (fun p F =>
      (p.L - 2 * p.w) ^ 3 / 6 - C * p.L ^ 2 ≤ sumA2g p.X F.g) :=
  sum_a2g_lowerPrime hcheb hlam

/-- **[prop:PP], the g-sandwich, upper half** (§5.4, verbatim):
"Σ_{n≤X} a_n² g(y_n) ≤ Σ_{n≤X} a_n²(L−y_n) = L³/6 + O(L²)". -/
theorem sum_a2g_upper (hcheb : Zeta23.ChebyshevMertens) (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
      sumA2g p.X F.g ≤ p.L ^ 3 / 6 + C * p.L ^ 2) :=
  sum_a2g_upperPrime hcheb hlam

end Results


end PrimeSide
end Zeta23
end
end

-- from Zeta23.PrimeSideB.Traces
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
  Part of the Zeta23 formalization of the paper
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/

/-!
# [thm:traces] for the concrete data — instantiating the abstract assembly
`Zeta23/PrimeSideB.lean` proves [thm:traces] for abstract real functions of `T`
(`PrimeSide.Facts D → TracesBounds …`).  This file plugs in the concrete objects:

* `Params.toSetting P T = ⟨T, λ, w⟩` and `Params.localFun P T = ⟨φ̂, Φ, A_φ, g, a, b⟩(T)` turn
  (`P : Params`, `T`) into the abstract prime-side layer (`Setting`, `LocalFun`), and
  `trGtA (P.toSetting T) (P.localFun T) = P.trGtilde T` etc. hold by `rfl`;
* `PrimeSide.concreteData P Z` is the `Data P` record of the actual traces / 𝓜-terms / ∫μ² / Σa_n²g;
* `PrimeSide.concreteFacts` derives `Facts (concreteData P Z)` from `P.Valid`, `PaperInputs Z`
  (H-RvM, H-Γ, H-cheb, H-MV), [prop:trace]/[lem:ends]/[eq:Msplit]/[prop:mumu]/[prop:cross],
  [prop:PP] + sandwich, and `LocalHypsEventually cϱ P` (the taper facts [eq:psidef],
  [eq:abdef], [eq:gbounds], [eq:Phi2FT], [lem:poisson] … for the concrete φ — proved in
  `Zeta23/PrimeSideA/Bridge.lean` from Taper.lean / Poisson.lean);
* `thm_traces_of_localHyps : … → ThmTracesHyp P Z`.
-/

noncomputable section

open Real Filter Topology MeasureTheory
open scoped BigOperators ArithmeticFunction

namespace Zeta23

namespace PrimeSide

open PaperParams

variable (P : Params)


variable {P}




end PrimeSide

end Zeta23

end
open Real Filter Topology MeasureTheory
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide
open PaperParams
variable (P : Params)
variable {P}

theorem solution {cϱ : ℝ} {Z : ZeroConfig} (hP : P.Valid) (inp : PaperInputs Z)
    (hLoc : LocalHypsEventually cϱ P) : Facts (concreteData P Z) := by
  have hlam : 0 < P.lam ∧ P.lam ≤ 1 := ⟨hP.lam_pos, hP.lam_le_one⟩
  have hΓ := inp.Gamma
  have hcheb := inp.cheb
  -- the regime, for majorant nonnegativity
  have hreg : ∀ᶠ T in atTop, 0 ≤ T ∧ 0 ≤ l T ∧ 0 ≤ Real.log (l T) ∧ 0 ≤ P.L T ∧ 0 ≤ P.X T := by
    filter_upwards [eventually_ge_atTop 1, eventually_l_ge 1, eventually_log_l_ge 1,
      eventually_L_ge P hP.lam_pos 1, eventually_one_le_X P hP.lam_pos] with T h1 h2 h3 h4 h5
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨T₀, hT₀⟩ := id hLoc
  -- the §5 sub-results, specialised to the concrete data (EventuallyAt → EvBound)
  have e_ends := evBound_of_eventuallyAt hLoc ((PrimeSide.lem_ends cϱ P.lam hΓ hcheb hlam).imp fun _ h => h.to_eventuallyAt) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg (mul_nonneg (mul_nonneg hL hl) hlog) (add_nonneg (sq_nonneg _) hX))
  have e_mumu := evBound_of_eventuallyAt hLoc ((PrimeSide.prop_mumu cϱ P.lam hΓ hcheb hlam).imp fun _ h => h.to_eventuallyAt) (by
    filter_upwards [hreg, eventually_L_ge P hP.lam_pos 1] with T ⟨hT, hl, hlog, hL, hX⟩ hL1
    exact mul_nonneg (sq_nonneg _) (Real.log_nonneg hL1))
  have e_PP := evBound_of_eventuallyAt hLoc
    ((PrimeSide.prop_PP (cϱ := cϱ) (lam := P.lam) hcheb inp.MV hlam).imp fun _ h => h.to_eventuallyAt) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg (sq_nonneg _) hX)
  have e_muP := evBound_of_eventuallyAt hLoc ((PrimeSide.prop_cross_muP cϱ P.lam hΓ hcheb hlam).imp fun _ h => h.to_eventuallyAt) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg hl (Real.sqrt_nonneg _))
  have e_muPi := evBound_of_eventuallyAt hLoc ((PrimeSide.prop_cross_muPi cϱ P.lam hΓ hcheb hlam).imp fun _ h => h.to_eventuallyAt) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg (mul_nonneg hl hL) (Real.sqrt_nonneg _))
  have e_PPi := evBound_of_eventuallyAt hLoc ((PrimeSide.prop_cross_PPi cϱ P.lam hΓ hcheb hlam).imp fun _ h => h.to_eventuallyAt) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg hL hX)
  have e_PiPi := evBound_of_eventuallyAt hLoc ((PrimeSide.prop_cross_PiPi cϱ P.lam hΓ hcheb hlam).imp fun _ h => h.to_eventuallyAt) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact div_nonneg (mul_nonneg hL hX) hT)
  refine ⟨hP.lam_pos, hP.lam_le_one, hP.one_le_w, ?abdef, rvm_evBound inp.RvM, ?muints2,
    ?prop_trace, ?lem_ends, ?Msplit, ?prop_mumu, ?prop_PP, ?sum_lower, ?sum_upper,
    ?cross_muP, ?cross_muPi, ?cross_PPi, ?cross_PiPi⟩
  case abdef =>
    filter_upwards [eventually_ge_atTop T₀] with T hT
    have hF := hT₀ T hT
    exact ⟨hF.b_lower, hF.b_le_a, hF.a_le_one⟩
  case muints2 =>
    obtain ⟨C, T₁, hC⟩ := hΓ.int_mu_sq
    refine ⟨max C 1, by positivity, max T₁ 0, fun T hT =>
      (hC T ((le_max_left _ _).trans hT)).trans ?_⟩
    have hT0 : 0 ≤ T := (le_max_right _ _).trans hT
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_right (le_max_left _ _) ?_
    exact div_nonneg (div_nonneg (mul_nonneg hT0 (sq_nonneg _)) (by positivity)) (sq_nonneg _)
  case prop_trace =>
    obtain ⟨A, hA, T₁, hN⟩ := rvm_evBound inp.RvM
    obtain ⟨C, T₂, hC⟩ := PrimeSide.prop_trace cϱ P.lam hΓ hcheb hlam A
    refine ⟨max C 1, by positivity, max T₀ (max T₁ T₂), fun T hT => ?_⟩
    have h0 : T₀ ≤ T := (le_max_left _ _).trans hT
    have h1 : T₁ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
    have h2 : T₂ ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT
    have hF := hT₀ T h0
    have := hC (P.toSetting T) (P.localFun T) rfl h2 hF.toCore (Z.N T (2 * T) : ℝ) (hN T h1)
    rw [trGtA_concrete] at this
    refine this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    exact mul_nonneg hF.L_pos.le (Real.sqrt_nonneg _)
  case lem_ends =>
    exact e_ends.congr_left (Eventually.of_forall fun T => by
      show P.trGtildeSq T - _ = _; rw [← trGt2A_concrete]; rfl)
  case Msplit =>
    filter_upwards [eventually_ge_atTop T₀] with T hT
    exact eq_Msplit cϱ hΓ (P.toSetting T) (P.localFun T) (hT₀ T hT).toCore
  case prop_mumu => exact e_mumu
  case prop_PP => exact e_PP
  case sum_lower =>
    obtain ⟨C, T₁, hC⟩ := PrimeSide.sum_a2g_lower (cϱ := cϱ) (lam := P.lam) hcheb hlam
    refine ⟨max C 1, by positivity, max T₀ T₁, fun T hT => ?_⟩
    have h0 : T₀ ≤ T := (le_max_left _ _).trans hT
    have h1 : T₁ ≤ T := (le_max_right _ _).trans hT
    have key := hC (P.toSetting T) (P.localFun T) rfl h1 (hT₀ T h0)
    simp only [Params.toSetting_L, Params.toSetting_X, Params.toSetting_w, Params.localFun_g] at key
    show |min (sumA2g (P.X T) (P.g T) - (P.L T - 2 * P.w) ^ 3 / 6) 0| ≤ max C 1 * P.L T ^ 2
    rw [abs_of_nonpos (min_le_right _ _)]
    have hCL : C * P.L T ^ 2 ≤ max C 1 * P.L T ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    have hpos : 0 ≤ max C 1 * P.L T ^ 2 := by positivity
    rcases min_cases (sumA2g (P.X T) (P.g T) - (P.L T - 2 * P.w) ^ 3 / 6) 0 with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; linarith
    · rw [h]; simpa using hpos
  case sum_upper =>
    obtain ⟨C, T₁, hC⟩ := PrimeSide.sum_a2g_upper (cϱ := cϱ) (lam := P.lam) hcheb hlam
    refine ⟨max C 1, by positivity, max T₀ T₁, fun T hT => ?_⟩
    have h0 : T₀ ≤ T := (le_max_left _ _).trans hT
    have h1 : T₁ ≤ T := (le_max_right _ _).trans hT
    have key := hC (P.toSetting T) (P.localFun T) rfl h1 (hT₀ T h0).toCore
    simp only [Params.toSetting_L, Params.toSetting_X, Params.localFun_g] at key
    show |max (sumA2g (P.X T) (P.g T) - P.L T ^ 3 / 6) 0| ≤ max C 1 * P.L T ^ 2
    rw [abs_of_nonneg (le_max_right _ _)]
    have hCL : C * P.L T ^ 2 ≤ max C 1 * P.L T ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    have hpos : 0 ≤ max C 1 * P.L T ^ 2 := by positivity
    exact max_le (by linarith) hpos
  case cross_muP => exact e_muP
  case cross_muPi => exact e_muPi
  case cross_PPi => exact e_PPi
  case cross_PiPi => exact e_PiPi
