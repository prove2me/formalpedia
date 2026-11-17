-- Prove2me | solution 1 for XiHadamardPortPublished.concrete_xi_no_real_zeros
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T10:25:45.775913+00:00
-- url     : https://prove2.me/submissions/72faafa5-80cd-47cd-8b93-cc3e456e0ae2

import Mathlib
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Complex/LogBounds.lean -/
section PntFile0
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Logarithm estimates for Weierstrass products

This file develops the finite truncation and tail estimates for the logarithm series
`-log (1 - z)`.  These estimates are the local analytic input for bounding Weierstrass
factors and canonical products.
-/

section
open scoped BigOperators

namespace Real


end Real

namespace Complex


/-- The truncation of `-log (1 - z)`, expressed via `Complex.logTaylor`. -/
noncomputable
def partialLogSum (m : ℕ) (z : ℂ) : ℂ :=
  -logTaylor (m + 1) (-z)


/-- The tail `∑_{k>m} z^k / k`, as `∑' k, z^(m+1+k)/(m+1+k)`. -/
noncomputable
def logTail (m : ℕ) (z : ℂ) : ℂ :=
  ∑' k, z ^ (m + 1 + k) / (m + 1 + k)


end Complex

end
end PntFile0


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/Norm.lean -/
section PntFile1
/-!
# Norm estimates for complex analysis

Elementary norm estimates used in Cartan-style product bounds and Gamma/zeta growth arguments.
-/

section
noncomputable section

namespace Complex

variable {z : ℂ}


end Complex

end
end
end PntFile1


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/WeierstrassFactor.lean -/
section PntFile2
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Weierstrass elementary factors

We define the Weierstrass elementary factors
`E_m(z) = (1 - z) * exp (∑_{k=1}^m z^k / k)` (as `Complex.weierstrassFactor`) and prove basic
properties and estimates

## Main definitions

* `Complex.partialLogSum m z`: the truncation of `-log (1 - z)`, defined via `Complex.logTaylor`
* `Complex.logTail m z`: the tail `∑_{k>m} z^k / k` as a `tsum` starting at `m + 1`
* `Complex.weierstrassFactor m z`: the elementary factor `E_m(z)`

## Main results

* `Complex.weierstrassFactor_sub_one_pow_bound`: `‖E_m(z) - 1‖ ≤ 4‖z‖^(m+1)` for `‖z‖ ≤ 1 / 2`
* `Complex.weierstrassFactor_eq_exp_neg_tail`: on `‖z‖ < 1` with `z ≠ 1`,
  `E_m z = exp (-logTail m z)`
* `Complex.norm_partialLogSum_le_nat_mul_max_one_norm_pow`: a crude bound on the truncated
  logarithm series
* `Complex.log_norm_weierstrassFactor_ge_log_norm_one_sub_nat_mul_max_one_norm_pow`: a crude lower
  bound for `log ‖E_m(z)‖` used in minimum-modulus arguments
-/

section
noncomputable section

open scoped BigOperators
open Set

namespace Complex

/-! ## The Weierstrass factor -/

/-- The Weierstrass elementary factor `E_m`. -/
def weierstrassFactor (m : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * exp (partialLogSum m z)


/-! ## Power bound -/


/-!
## Lower bounds on `Real.log ‖weierstrassFactor m z‖`

Auxiliary inequalities for minimum-modulus / Cartan-type arguments in Hadamard factorization.
-/


/-! ## Locally uniform convergence of products of scaled factors -/


end Complex

end
end
end PntFile2


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/CanonicalProduct.lean -/
section PntFile3
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Canonical products

This file defines canonical products attached to a sequence `a : ℕ → ℂ`:

`canonicalProduct m a z := ∏' n, weierstrassFactor m (z / a n)`.

The convergence results specialize the locally uniform product API for scaled Weierstrass factors
developed in `Mathlib.Analysis.Complex.WeierstrassFactor`.
-/

section
noncomputable section

open Filter Topology

namespace Complex

/-- The canonical product `∏' n, E_m(z / a_n)` for a sequence `a`. -/
def canonicalProduct (m : ℕ) (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∏' n : ℕ, weierstrassFactor m (z / a n)


end Complex

end
end
end PntFile3


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Meromorphic/DivisorSupport.lean -/
section PntFile4
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Support of the divisor of a meromorphic function

This file contains topological properties of the support of `MeromorphicOn.divisor`.
In particular, the support is discrete, and in hereditarily Lindelöf spaces it is countable.
It is also locally finite within the domain, hence meets compact subsets of the domain in finitely
many points.

## Main results

* `MeromorphicOn.divisor_support_discrete`: the divisor support is discrete.
* `MeromorphicOn.divisor_support_countable`: in a hereditarily Lindelöf space, the support is
  countable.
* `MeromorphicOn.divisor_support_inter_compact_finite`: a compact set meets the support in finitely
  many points.
* `MeromorphicOn.exists_ball_inter_divisor_support_eq_singleton`: isolating balls around support
  points.
-/

section
open Filter Topology Set

namespace MeromorphicOn

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U K : Set 𝕜} {z : 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
## Discreteness and countability of the divisor support
-/


/-!
## Finiteness of the divisor support on compact subsets of the domain
-/

lemma divisor_support_inter_compact_finite (f : 𝕜 → E) {U K : Set 𝕜}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    (K ∩ (MeromorphicOn.divisor f U).support).Finite := by
  classical
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have hloc :
      ∀ x ∈ K, ∃ V : Set 𝕜, V ∈ 𝓝 x ∧ Set.Finite (V ∩ D.support) := by
    intro x hxK
    rcases D.supportLocallyFiniteWithinDomain x (hKU hxK) with ⟨V, hV, hfin⟩
    exact ⟨V, hV, hfin⟩
  choose V hVnhds hVfin using hloc
  rcases hK.elim_nhds_subcover' (U := fun x hx => V x hx) (hU := fun x hx => hVnhds x hx) with
    ⟨t, ht⟩
  have hsub :
      K ∩ D.support ⊆ ⋃ x ∈ t, (V (x : 𝕜) x.2 ∩ D.support) := by
    intro y hy
    rcases hy with ⟨hyK, hyS⟩
    have hycov : y ∈ ⋃ x ∈ t, V (x : 𝕜) x.2 := ht hyK
    rcases Set.mem_iUnion.1 hycov with ⟨x, hycov'⟩
    rcases Set.mem_iUnion.1 hycov' with ⟨hxT, hyV⟩
    refine Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ?_⟩
    exact ⟨hxT, ⟨hyV, hyS⟩⟩
  have hfinU : Set.Finite (⋃ x ∈ t, (V (x : 𝕜) x.2 ∩ D.support)) := by
    classical
    refine (t.finite_toSet).biUnion ?_
    intro x hx
    simpa using (hVfin (x : 𝕜) x.2)
  exact hfinU.subset hsub

/-!
## Local singleton balls and enumerations of the divisor support
-/


end MeromorphicOn

end
end PntFile4


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/DivisorIndex.lean -/
section PntFile5
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Indexing zeros via the divisor

This file defines index types that enumerate zeros of a meromorphic function (with multiplicity)
using `MeromorphicOn.divisor`.

The main use is in Hadamard/Weierstrass factorization, where these indices are used to build
canonical products.

## Main definitions

* `Complex.Hadamard.divisorZeroIndex`, `Complex.Hadamard.divisorZeroIndex₀`: index types for zeros
  with multiplicity.
* `Complex.Hadamard.divisorCanonicalProduct`: the canonical product indexed by `divisorZeroIndex₀`.
-/

section
open Set

namespace Complex.Hadamard

/-!
## Index types
-/

/-- Index type enumerating zeros (with multiplicity) via the divisor. -/
def divisorZeroIndex (f : ℂ → ℂ) (U : Set ℂ) : Type :=
  Σ z : ℂ, Fin (Int.toNat (MeromorphicOn.divisor f U z))

/-- The nonzero part of `divisorZeroIndex`. -/
abbrev divisorZeroIndex₀ (f : ℂ → ℂ) (U : Set ℂ) : Type :=
  {p : divisorZeroIndex f U // p.1 ≠ 0}

/-- The underlying point of a (nonzero) divisor index. -/
abbrev divisorZeroIndex₀_val {f : ℂ → ℂ} {U : Set ℂ} (p : divisorZeroIndex₀ f U) : ℂ :=
  p.1.1

@[simp]
lemma divisorZeroIndex₀_val_ne_zero {f : ℂ → ℂ} {U : Set ℂ} (p : divisorZeroIndex₀ f U) :
    divisorZeroIndex₀_val p ≠ 0 := p.2

/-- A (nonzero) divisor index has nonzero multiplicity at its underlying point. -/
@[simp]
lemma divisorZeroIndex₀_val_mem_divisor_support {f : ℂ → ℂ} {U : Set ℂ}
    (p : divisorZeroIndex₀ f U) :
    MeromorphicOn.divisor f U (divisorZeroIndex₀_val p) ≠ 0 := by
  have hn :
      Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀_val p)) ≠ 0 := by
    intro h0
    have q0 : Fin 0 := by
      simpa [divisorZeroIndex₀_val, h0] using p.1.2
    exact Fin.elim0 q0
  intro hdiv
  have : Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀_val p)) = 0 := by
    simp [hdiv]
  exact hn this

lemma divisorZeroIndex₀_val_mem_divisor_support' {f : ℂ → ℂ} {U : Set ℂ}
    (p : divisorZeroIndex₀ f U) :
    divisorZeroIndex₀_val p ∈ (MeromorphicOn.divisor f U).support := by
  simp [Function.mem_support]


/-- The canonical product attached to the (nonzero) divisor of `f` on `U`. -/
noncomputable def divisorCanonicalProduct (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) (z : ℂ) : ℂ :=
  ∏' p : divisorZeroIndex₀ f U, weierstrassFactor m (z / divisorZeroIndex₀_val p)


end Complex.Hadamard

end
end PntFile5


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/LocallyUniformLimit.lean -/
section PntFile6
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Locally uniform limits and bounded multiplication

Uniform convergence on a set is preserved under multiplication by a function that is bounded
on that set.  This is a basic estimate for locally uniform products.
-/

section
namespace Complex

section UniformMul

/-- On `K`, uniform convergence is preserved when multiplying on the left by a bounded function. -/
theorem _root_.TendstoUniformlyOn.mul_left_bounded {ι : Type*} {p : Filter ι} {K : Set ℂ}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {h : ℂ → ℂ}
    (hF : TendstoUniformlyOn F f p K) (hh : ∃ C, ∀ z ∈ K, ‖h z‖ ≤ C) :
    TendstoUniformlyOn (fun n z => h z * F n z) (fun z => h z * f z) p K := by
  intro u hu
  rcases Metric.mem_uniformity_dist.1 hu with ⟨ε, hεpos, hεu⟩
  rcases hh with ⟨C, hC⟩
  set C' : ℝ := max C 1
  have hC'pos : 0 < C' := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hC' : ∀ z ∈ K, ‖h z‖ ≤ C' := fun z hz => le_trans (hC z hz) (le_max_left _ _)
  have hv : {p : ℂ × ℂ | dist p.1 p.2 < ε / C'} ∈ uniformity ℂ :=
    Metric.mem_uniformity_dist.2 ⟨ε / C', div_pos hεpos hC'pos, fun _ _ hab => hab⟩
  have hF' : ∀ᶠ n in p, ∀ z : ℂ, z ∈ K → dist (f z) (F n z) < ε / C' := hF _ hv
  filter_upwards [hF'] with n hn z hzK
  have hn' : ‖f z - F n z‖ < ε / C' := by simpa [dist_eq_norm] using hn z hzK
  have hle : ‖h z‖ * ‖f z - F n z‖ ≤ C' * ‖f z - F n z‖ :=
    mul_le_mul_of_nonneg_right (hC' z hzK) (norm_nonneg _)
  have hlt : C' * ‖f z - F n z‖ < C' * (ε / C') := mul_lt_mul_of_pos_left hn' hC'pos
  have hnorm :
      ‖h z * f z - h z * F n z‖ = ‖h z‖ * ‖f z - F n z‖ := by
    calc
      ‖h z * f z - h z * F n z‖ = ‖h z * (f z - F n z)‖ := by simp [mul_sub]
      _ = ‖h z‖ * ‖f z - F n z‖ := by simp
  have hdist : dist (h z * f z) (h z * F n z) < ε := by
    rw [dist_eq_norm, hnorm]
    have hlt' : ‖h z‖ * ‖f z - F n z‖ < ε := by
      calc
        ‖h z‖ * ‖f z - F n z‖ ≤ C' * ‖f z - F n z‖ := hle
        _ < C' * (ε / C') := hlt
        _ = ε := by field_simp [hC'pos.ne']
    exact hlt'
  exact hεu hdist

end UniformMul

end Complex

end
end PntFile6


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/DivisorConvergence.lean -/
section PntFile7
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Convergence and holomorphy of divisor-indexed canonical products

This file proves uniform convergence on compacts, locally uniform convergence, holomorphy, and the
genus-one logarithmic-derivative identity for the divisor-indexed canonical product
`Complex.Hadamard.divisorCanonicalProduct`, under the standard summability hypothesis.

It also provides finiteness lemmas for subsets of the divisor index type cut out by a norm bound.
-/

section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set

namespace Complex.Hadamard

/-!
## Finiteness of “small” divisor indices
-/

lemma finite_divisorZeroIndex₀_subtype_norm_le {f : ℂ → ℂ} {U : Set ℂ} (B : ℝ)
    (hBU : Metric.closedBall (0 : ℂ) B ⊆ U) :
    Finite {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ B} := by
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have hK : IsCompact (Metric.closedBall (0 : ℂ) B) := isCompact_closedBall _ _
  have hpts0 : ((Metric.closedBall (0 : ℂ) B) ∩ D.support).Finite :=
    MeromorphicOn.divisor_support_inter_compact_finite (f := f) (U := U)
      (K := Metric.closedBall (0 : ℂ) B) hK hBU
  set pts : Set ℂ := ((Metric.closedBall (0 : ℂ) B) ∩ D.support) \ {0}
  have hpts : pts.Finite := hpts0.sdiff
  let : Fintype pts := hpts.fintype
  let T : Type := Σ z : pts, Fin (Int.toNat (D z.1))
  have : Finite T := by infer_instance
  let F :
      {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ B} → T := fun p =>
    ⟨⟨divisorZeroIndex₀_val p.1, by
        have hball : divisorZeroIndex₀_val p.1 ∈ Metric.closedBall (0 : ℂ) B := by
          simpa [Metric.mem_closedBall, dist_zero_right] using p.2
        have hsupport : divisorZeroIndex₀_val p.1 ∈ D.support := by
          have hne_toNat :
              Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀_val p.1)) ≠ 0 := by
            intro h0
            have hpfin :
                Fin (Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀_val p.1))) := by
              simpa [D] using p.1.1.2
            have : Fin 0 := by simpa [h0] using hpfin
            exact Fin.elim0 this
          have hne_D : D (divisorZeroIndex₀_val p.1) ≠ 0 := by
            intro hD0
            apply hne_toNat
            simp [D, hD0]
          simp [D, Function.locallyFinsuppWithin.support, Function.support]
        have hne0 : divisorZeroIndex₀_val p.1 ≠ 0 := divisorZeroIndex₀_val_ne_zero p.1
        exact ⟨⟨hball, hsupport⟩, by simp [Set.mem_singleton_iff]⟩⟩,
      p.1.1.2⟩
  refine Finite.of_injective F ?_
  intro p q hpq
  apply Subtype.ext
  apply Subtype.ext
  have h' := (Sigma.mk.inj_iff.1 hpq)
  have hz : divisorZeroIndex₀_val p.1 = divisorZeroIndex₀_val q.1 := congrArg Subtype.val h'.1
  apply (Sigma.mk.inj_iff).2
  refine ⟨hz, ?_⟩
  exact h'.2

lemma divisorZeroIndex₀_norm_le_finite {f : ℂ → ℂ} {U : Set ℂ} (B : ℝ)
    (hBU : Metric.closedBall (0 : ℂ) B ⊆ U) :
    ({p : divisorZeroIndex₀ f U | ‖divisorZeroIndex₀_val p‖ ≤ B} : Set _).Finite := by
  let s : Set (divisorZeroIndex₀ f U) := {p | ‖divisorZeroIndex₀_val p‖ ≤ B}
  have : Finite (↥s) :=
    finite_divisorZeroIndex₀_subtype_norm_le (f := f) (U := U) B hBU
  exact Set.toFinite s

/-!
## Uniform convergence on compact sets
-/


/-!
## Entire-ness (holomorphy) of the divisor-indexed canonical product
-/


/-!
## Logarithmic derivative of the genus-one divisor product
-/


end Complex.Hadamard

end
end PntFile7


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/DivisorUnits.lean -/
section PntFile8
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Local nonvanishing for divisor-indexed Weierstrass factors

This file provides local nonvanishing statements for the factors
`weierstrassFactor m (z / a)` indexed by `divisorZeroIndex₀`, on punctured balls that isolate a
single divisor-support point.
-/

section
open Set

namespace Complex.Hadamard


end Complex.Hadamard

end
end PntFile8


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/DivisorFiber.lean -/
section PntFile9
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Fibers of the divisor index type

This file studies the fiber `{p : divisorZeroIndex₀ f univ | divisorZeroIndex₀_val p = z₀}`.
It provides a canonical `Finset` for this fiber and identifies its cardinality with the divisor
multiplicity and (for holomorphic functions) with `analyticOrderNatAt`.
-/

section
noncomputable section

open Set
open scoped Topology BigOperators

namespace Complex.Hadamard

/-!
## Divisor values vs analytic order (holomorphic functions)
-/


/-!
## The multiplicity fiber is finite and has the expected cardinality
-/

theorem divisorZeroIndex₀_fiber_finite (f : ℂ → ℂ) (z₀ : ℂ) :
    ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | divisorZeroIndex₀_val p = z₀} :
      Set _).Finite := by
  have hsub :
      ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | divisorZeroIndex₀_val p = z₀} : Set _)
        ⊆ ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ ‖z₀‖} :
          Set _) := by
    intro p hp
    have : divisorZeroIndex₀_val p = z₀ := hp
    simp [this]
  have hfin :
      ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ ‖z₀‖} :
        Set _).Finite := by
    have : Metric.closedBall (0 : ℂ) ‖z₀‖ ⊆ (Set.univ : Set ℂ) := by simp
    simpa using (divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ))
      (B := ‖z₀‖) this)
  exact hfin.subset hsub

/-- The finite fiber over `z₀` in the divisor-index type `divisorZeroIndex₀`. -/
def divisorZeroIndex₀_fiberFinset (f : ℂ → ℂ) (z₀ : ℂ) :
    Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
  (divisorZeroIndex₀_fiber_finite (f := f) z₀).toFinset


end Complex.Hadamard

end
end
end PntFile9


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/DivisorComplement.lean -/
section PntFile10
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Fiber/complement splitting for divisor-indexed partial products

This file defines finitary “partial products” of Weierstrass factors indexed by the divisor, and
develops the corresponding fiber/complement splitting. It also defines the complement canonical
product (replacing fiber factors by `1`) and proves its convergence/holomorphy properties.
-/

section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set

namespace Complex.Hadamard

/-!
## Complement factors

For a fixed point `z₀`, the complement factor agrees with the usual Weierstrass factor away from
the fiber over `z₀`, and is `1` on that fiber.
-/

/-- The factor used in complement products. -/
noncomputable def divisorComplementFactor
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ then (1 : ℂ)
    else weierstrassFactor m (z / divisorZeroIndex₀_val p)


/-!
## Partial products as a named function

These finite products are the approximants to the divisor-indexed canonical product.
-/

/-- Finite partial product of Weierstrass factors indexed by a finset of divisor indices. -/
noncomputable def divisorPartialProduct (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) : ℂ :=
  ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p)


/-!
## Splitting finite partial products into fiber vs complement

This is the finitary “fiber × complement” split.
-/

/-- The partial product over indices *not* in the fiber over `z₀`. -/
noncomputable def divisorComplementPartialProduct
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) : ℂ :=
  ∏ p ∈ s, divisorComplementFactor m f z₀ p z


/-!
## Complement canonical product (fiber factors removed)

For a fixed point `z₀`, one often wants to split the infinite product into a finite “fiber part”
(`val = z₀`, accounting for the multiplicity) and an infinite “complement part” (all other indices).

The complement product is written as a total product by inserting the neutral element `1` on the
fiber indices.
-/

/-- The infinite product over indices *not* in the fiber over `z₀` (the “complement” canonical
product). -/
noncomputable def divisorComplementCanonicalProduct
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) (z : ℂ) : ℂ :=
  ∏' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), divisorComplementFactor m f z₀ p z

/-!
## Convergence/holomorphy of the complement canonical product

This is the same M-test argument as for `divisorCanonicalProduct`, but with finitely many factors
replaced by `1`. We keep the same summability hypothesis.
-/


end Complex.Hadamard

end
end PntFile10


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/DivisorPartialProductFactor.lean -/
section PntFile11
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Local factorization of finite divisor-indexed products

This file packages the finite-order computation for partial products of Weierstrass factors indexed
by `divisorZeroIndex₀`, and deduces a local factorization at a point `z₀` once the finset contains
the full fiber over `z₀`.
-/

section
noncomputable section

open Complex Filter Function Finset Topology
open scoped Topology BigOperators
open Set

namespace Complex.Hadamard

/-!
## Finite product multiplicity at a point

For a finite product of elementary factors indexed by divisor-indices, the analytic order at `z₀`
equals the number of indices whose value is exactly `z₀`.
-/


end Complex.Hadamard

end
end
end PntFile11


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/DivisorQuotientConvergence.lean -/
section PntFile12
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Quotient convergence for divisor-indexed canonical products

This file develops the convergence of quotients of finite partial products and of the
divisor-indexed canonical product by powers `(z - z₀)^k` away from `z₀`. It also proves the key
local identity on a punctured ball used later in removable-singularity arguments.
-/

section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set

namespace Complex.Hadamard


/-!
## Quotient convergence on compacts avoiding `z₀`

If `K` is compact and avoids `z₀`, then multiplying by `((z - z₀)^k)⁻¹` preserves uniform
convergence on `K`. -/


/-!
## Quotient locally uniform convergence on the punctured plane `ℂ \ {z₀}`
-/


/-!
## Passing the fiber/complement factorization to the infinite product (punctured neighborhood)

This is the local factorization used for removability: near `z₀`, the quotient
`divisorCanonicalProduct / (z - z₀)^k` agrees (on a punctured ball) with the product of
`divisorComplementCanonicalProduct` and the analytic factor `u` coming from the fiber-only product.
-/

open Filter


/-!
## Boundedness of the quotient on a punctured ball

We only need boundedness of the analytic factor `u` near `z₀`, so `ContinuousAt` at `z₀` suffices.
-/


/-!
## Nonvanishing of the complement canonical product near `z₀`

Pointwise, the complement canonical product is an infinite product of factors of the form `1 + aₚ`
with `∑ ‖aₚ‖` summable, hence the product is nonzero.
-/


/-!
## Eventually: partial products factor at `z₀` with the fiber multiplicity

Along `atTop`, sufficiently large partial products contain the fiber, hence each such partial
product is locally divisible by `(z - z₀)^k`, where `k` is the fiber cardinality.
-/


/-!
## On `𝓝[≠] z₀`, large partial product quotients agree with an analytic function

This is the punctured-neighborhood version of
`eventually_exists_analyticAt_eq_pow_smul_divisorPartialProduct`,
obtained by dividing the factorization by `(z - z₀)^k` away from `z₀`.
-/


end Complex.Hadamard

end
end PntFile12


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/DivisorQuotientRemovable.lean -/
section PntFile13
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Removable singularities and multiplicities for divisor-indexed canonical products

Building on quotient convergence and boundedness on punctured balls, this file proves removable
singularity results and identifies the exact zero multiplicity of `divisorCanonicalProduct`.
-/

section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set

namespace Complex.Hadamard

/-!
## Differentiability of the quotient on `ℂ \ {z₀}`

The quotient of the infinite product by `(z - z₀)^k` is holomorphic on the punctured plane.
-/


/-!
## Removable singularity for the quotient at `z₀`

Using punctured-ball boundedness and punctured differentiability, we obtain a holomorphic extension
of the quotient at `z₀` via `Mathlib.Analysis.Complex.RemovableSingularity`.
-/


/-!
## Exact multiplicity of the divisor canonical product

At each `z₀`, the zero multiplicity of `divisorCanonicalProduct` equals the fiber cardinality
`card (divisorZeroIndex₀_fiberFinset z₀)`.
-/


/-!
## Canonical product has the same analytic order as `f` away from the origin

Away from `0`, the analytic order of the divisor-indexed canonical product agrees with that of `f`
(for differentiable `f`), assuming the standard summability hypothesis.
-/


end Complex.Hadamard

end
end PntFile13


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/Divisor.lean -/
section PntFile14
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

/-!
# Hadamard factorization (preliminaries)

This file develops preliminary lemmas towards Hadamard factorization for entire functions on `ℂ`.
Zeros are indexed with multiplicity using `MeromorphicOn.divisor`, then assembled into the
corresponding canonical product.

## Main definitions

- `Complex.Hadamard.divisorZeroIndex`, `Complex.Hadamard.divisorZeroIndex₀`: index types enumerating
  zeros with multiplicity.
- `Complex.Hadamard.divisorCanonicalProduct`: the canonical product indexed by `divisorZeroIndex₀`.
- `Complex.Hadamard.divisorComplementCanonicalProduct`: the canonical product with the fiber over a
  fixed point `z₀` removed.

## Main results

- The support of the divisor is discrete and countable, and meets compact sets in finitely many
  points.
- Under the standard summability hypothesis, the canonical product converges uniformly on compact
  sets, and its analytic order agrees with the expected multiplicity away from `0`.
-/

section
namespace Complex.Hadamard

/-!
## Nonvanishing helpers for Weierstrass factors
-/

open scoped Topology
open Set

/-!
## Local finiteness on compact sets

For `D : Function.locallyFinsuppWithin U ℤ`, the support is *locally finite within `U`*.
Hence any compact `K ⊆ U` meets `D.support` only finitely often.

This yields “eventually in `cofinite`” bounds for divisor-indexed products.
-/

/-!
## Entire functions are never locally zero (under a global nontriviality witness)

If `f` is differentiable on `ℂ` and not identically zero, then it is not locally zero anywhere,
hence `analyticOrderAt f z ≠ ⊤` for all `z`.
-/


/-!
## Avoiding zeros on a circle

If `f` is entire and not identically zero, and if a radius `r > 0` is different from the norms of
all (nonzero) divisor-indexed zeros inside an ambient bound `B`, then `f` has no zeros on the circle
`‖z‖ = r`.
-/


/-!
## The divisor canonical product vanishes at indexed zeros

If one of the factors is `0` at `z`, then the infinite product is `0`.
-/


/-!
## The fiber finite product has the expected order at `z₀`

This packages the finite multiplicity calculation for the specific finset corresponding to the fiber
`{p | divisorZeroIndex₀_val p = z₀}`.
-/


/-!
## Exact multiplicity of the divisor canonical product

The infinite canonical product has precisely the zero multiplicities encoded by the divisor index.
The proof is supplied by the quotient/removable-singularity layer, and the
statements here record the multiplicity theorem at the level where the product is introduced.
-/


/-!
## Refining the factorization: factoring out `(z - z₀)^k` using the fiber-only product

When `s` contains the fiber finset, we can write the partial product as

`divisorPartialProduct s = (z - z₀)^k • (divisorComplementPartialProduct s * u)`

where `u` is the analytic quotient coming from the fiber-only product.
-/


end Hadamard
end Complex

end
end PntFile14


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Topology/MetricSpace/Annulus.lean -/
section PntFile15
/-
Copyright (c) 2024 James Sundstrom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Sundstrom
-/
/-!
# Annulus

In this file we define annuli in (pseudo)(e)metric spaces.

For a point `x` and radii `r R`, the set `Metric.annulusIoo x r R` consists of all `y` such that
`dist y x ∈ Set.Ioo r R`. We provide analogous definitions for `Ioc`, `Ico`, `Icc`, and also for the
half-infinite intervals `Ioi`, `Ici` (these are complements of `closedBall`/`ball`).

We also define `Metric.eannulusIxx` using `edist` (hence radii in `ℝ≥0∞`), and relate these to
`Metric.annulusIxx` via `ENNReal.ofReal` when `edist = ENNReal.ofReal ∘ dist`.

## Tags

annulus
-/

section
open Set

open scoped ENNReal

namespace Metric

variable {X : Type*} [PseudoMetricSpace X]

/-! ### Annulus defined using `dist` -/

/-- The annulus `{y | dist y x ∈ Set.Ioo r R}` in a pseudo metric space. -/
def annulusIoo (x : X) (r R : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Ioo r R

/-- The annulus `{y | dist y x ∈ Set.Ioc r R}` in a pseudo metric space. -/
def annulusIoc (x : X) (r R : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Ioc r R

/-- The annulus `{y | dist y x ∈ Set.Ico r R}` in a pseudo metric space. -/
def annulusIco (x : X) (r R : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Ico r R

/-- The annulus `{y | dist y x ∈ Set.Icc r R}` in a pseudo metric space. -/
def annulusIcc (x : X) (r R : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Icc r R

/-- The exterior `{y | dist y x ∈ Set.Ioi r}` (complement of `closedBall x r`). -/
def annulusIoi (x : X) (r : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Ioi r

/-- The exterior `{y | dist y x ∈ Set.Ici r}` (complement of `ball x r`). -/
def annulusIci (x : X) (r : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Ici r

variable {x : X} {r R : ℝ}


/-! ### Pairwise disjoint annuli over succ orders -/

open scoped Function -- required for scoped `on` notation

variable {ι : Type*} [LinearOrder ι] [SuccOrder ι]


end Metric

namespace Metric

variable {X : Type*} [PseudoEMetricSpace X]

/-! ### Annulus defined using `edist` -/

/-- The annulus `{y | edist y x ∈ Set.Ioo r R}` in a pseudo emetric space. -/
def eannulusIoo (x : X) (r R : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Ioo r R

/-- The annulus `{y | edist y x ∈ Set.Ioc r R}` in a pseudo emetric space. -/
def eannulusIoc (x : X) (r R : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Ioc r R

/-- The annulus `{y | edist y x ∈ Set.Ico r R}` in a pseudo emetric space. -/
def eannulusIco (x : X) (r R : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Ico r R

/-- The annulus `{y | edist y x ∈ Set.Icc r R}` in a pseudo emetric space. -/
def eannulusIcc (x : X) (r R : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Icc r R

/-- The exterior `{y | edist y x ∈ Set.Ioi r}`. -/
def eannulusIoi (x : X) (r : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Ioi r

/-- The exterior `{y | edist y x ∈ Set.Ici r}`. -/
def eannulusIci (x : X) (r : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Ici r


/-! ### Pairwise disjoint eannuli over succ orders -/

open scoped Function -- required for scoped `on` notation

variable {ι : Type*} [LinearOrder ι] [SuccOrder ι]


end Metric

namespace Metric

/-! ### `ENNReal.ofReal` bridge lemmas in a pseudo metric space -/

variable {X : Type*} [PseudoMetricSpace X]
variable {x : X} {r R : ℝ}


end Metric

end
end PntFile15


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/HadamardFactorization.lean -/
section PntFile16
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# The Hadamard quotient

If `f` is entire, nontrivial, and the divisor-indexed canonical product of genus `m` converges,
then there is an entire zero-free function `H` with

`f z = H z * z ^ (ord₀ f) * divisorCanonicalProduct m f univ z`.

The quotient `H` is obtained as the meromorphic normal form of
`f / (z ^ (ord₀ f) * divisorCanonicalProduct ...)`.

The quotient construction here is centered at `0`.  General-center API is derived downstream by
translating the function; see `hadamard_factorization_of_order_centered`.

## Main results

* `exists_entire_nonzero_hadamardQuotient` : existence of `H`
* `hadamardDenom`, `differentiable_hadamardDenom`

Downstream: `HadamardFactorization/Summability` (Jensen counting), `Growth`, and `Order`
assemble the full factorization `hadamard_factorization_of_order`.

## References

* [tao246bComplexAnalysis], Theorem 22 for the finite-order Hadamard factorization strategy
* [boas1954] and [levin1980] for Weierstrass factors, canonical products, and the classical
  Hadamard product theorem
-/

section
namespace Complex.Hadamard

open Filter Topology Set Complex

open scoped BigOperators Topology

/-- The denominator in the Hadamard quotient construction. -/
noncomputable def hadamardDenom (m : ℕ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z ^ (analyticOrderNatAt f 0) * divisorCanonicalProduct m f (Set.univ : Set ℂ) z

/-- The denominator in the Hadamard quotient construction, centered at `c`. -/
noncomputable def centeredHadamardDenom (m : ℕ) (c : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (z - c) ^ (analyticOrderNatAt f c) *
    divisorCanonicalProduct m (fun w : ℂ => f (w + c)) (Set.univ : Set ℂ) (z - c)

/-- The Hadamard quotient construction, centered at `c`. -/
noncomputable def centeredHadamardQuotient (m : ℕ) (c : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z / centeredHadamardDenom m c f z


/-!
## Boundedness on compact annuli (away from `z₀`)

On any compact set separated from `z₀`, the quotient by `(z - z₀)^k` is bounded.
-/


end Complex.Hadamard

end
end PntFile16


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Basic.lean -/
section PntFile17
/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus, Matteo Cipollina
-/
/-!
# Extra logarithmic counting API

This file collects basic logarithmic-counting identities used by the Hadamard factorization API.
-/

section
open Filter Function MeromorphicOn Metric Real Set

namespace Function.locallyFinsuppWithin

variable {E : Type*} [NormedAddCommGroup E]

/-!
### Support of `toClosedBall`

On the closed ball of radius `|r|`, evaluation agrees with the original function; support points
lie in that ball and correspond bijectively with support points of the original function inside it.
-/


/-- Total multiplicity of nonzero support points inside the closed ball of radius `|R|`. -/
noncomputable def massClosedBall₀ {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (D : locallyFinsupp E ℤ) (R : ℝ) : ℝ := by
  classical
  exact
    (((finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).toFinset).filter
      (fun z => z ≠ (0 : E))).sum fun z => (D z : ℝ)


end Function.locallyFinsuppWithin

namespace Function.locallyFinsuppWithin


end Function.locallyFinsuppWithin

end
end PntFile17


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Log/PosLog.lean -/
section PntFile18
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Positive-log estimates

Small estimates for `Real.log⁺` and for converting logarithmic growth bounds into exponential
bounds.
-/

section
namespace Real


end Real

end
end PntFile18


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Exp.lean -/
section PntFile19
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Elementary exponential estimates

Small real exponential inequalities used to absorb polynomial and product factors into
finite-order growth bounds.
-/

section
namespace Real


end Real

end
end PntFile19


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Log/ExpGrowth.lean -/
section PntFile20
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Exponential bounds from logarithmic growth

Pointwise comparisons between `log (1 + ‖f x‖)`, `‖f x‖`, and `exp (C * r(x)^τ)` for
`r(x) ≥ 1`. Used in finite-order entire function theory and Hadamard factorization.

Also includes the real floor midpoint lemma used to match Weierstrass genus `⌊ρ⌋`.

## Main results

* `Real.log_norm_le_log_one_add_norm`, `Real.log_nonneg_mul_inv_norm_of_norm_le` : norm/log
  comparisons for growth bounds
* `Real.norm_le_exp_mul_rpow_of_log_growth`, `Real.log_growth_of_norm_le_exp_mul_rpow` :
  convert between log-growth and exp bounds
* `Real.sq_le_exp_const_mul_rpow` : absorb a quadratic factor into any positive exponential
  `rpow` margin
* `Real.exists_between_self_and_floor_add_one_same_floor` : genus-preserving midpoint exponent
* `Real.log_norm_le_of_log_one_add_growth_on_sphere` : sphere log-growth bound for Jensen's formula

## Tags

logarithm, exponential growth, finite order, Hadamard factorization
-/

section
namespace Real

variable {α E : Type*} [SeminormedAddCommGroup E]


variable {F : Type*} [NormedAddCommGroup F]


open Metric Complex


end Real

end
end PntFile20


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Growth.lean -/
section PntFile21
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Logarithmic counting from entire-function growth

Bounds on `logCounting` of the zero divisor from a logarithmic growth hypothesis on an entire
function. Used in Hadamard divisor summability and finite-order factorization.

## Main results

* `Function.locallyFinsuppWithin.logCounting_divisor_le_of_log_growth` : log-growth of order `ρ`
  controls log-counting on disks
* `Function.locallyFinsuppWithin.massClosedBall₀`, `log_two_mul_massClosedBall₀_le_logCounting` :
  compare zero mass in a ball with log-counting at twice the radius

## Tags

logarithmic counting, Jensen's formula, finite order, Hadamard factorization
-/

section
open Filter Function MeromorphicOn Metric Real Set

namespace Function.locallyFinsuppWithin


variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]


end Function.locallyFinsuppWithin

end
end PntFile21


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Meromorphic/DivisorHolomorphic.lean -/
section PntFile22
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Divisors of holomorphic functions

Holomorphic functions on `ℂ` have non-negative divisors, since zeros contribute non-negative
multiplicity and poles cannot occur.

## Main results

* `Differentiable.divisor_nonneg` : the divisor of an entire function is non-negative
-/

section
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The divisor of an entire function is non-negative. -/
theorem Differentiable.divisor_nonneg {f : ℂ → E} (hf : Differentiable ℂ f) :
    0 ≤ MeromorphicOn.divisor f (univ : Set ℂ) :=
  MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hf.differentiableOn.analyticOnNhd isOpen_univ)

end
end PntFile22


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Log/Dyadic.lean -/
section PntFile23
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Dyadic estimates from logarithms

This file records elementary estimates for dyadic radii selected by `⌊logb 2 x⌋₊`.
The estimates are used to decompose growth bounds into summable geometric shells.
-/

section
noncomputable section

open scoped BigOperators
open Filter

namespace Real


end Real

end
end
end PntFile23


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/HadamardFactorization/Summability.lean -/
section PntFile24
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Divisor summability from logarithmic growth

Dyadic shell summability for the zero divisor of an entire function with a logarithmic growth
bound. This is the zero-counting input for Tao's finite-order Hadamard theorem, not the
factorization conclusion itself.  It is step 1 of the intrinsic Hadamard pipeline
(`divisorCanonicalProduct`, `hadamard_factorization_of_growth`, `hadamard_factorization_of_order`).

## Main results

* `divisorMassClosedBall₀_le_of_growth` : zero mass in a ball is `O((1 + R)^ρ)` under
  log-growth of order `ρ`
* `summable_norm_inv_pow_divisorZeroIndex₀_of_growth` : growth implies convergence of the
  canonical product
* `jensen_formula_logCounting_eq_circleAverage_sub_log_trailingCoeff` : Hadamard alias for Jensen's
  formula (see also
  `Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const_of_differentiable`)

Jensen's formula and log-counting growth bounds live in
`Analysis.Complex.ValueDistribution.LogCounting`.

Tao Notes 1 enters here through Theorem 2 (Jensen's formula), Proposition 8 (zero counting from
growth), and the convergence input corresponding to Exercise 19 for the genus `⌊ρ⌋` canonical
product.

## References

* [tao246bComplexAnalysis], Theorem 2 and Proposition 8 (disk formulation; compare
  `divisorMassClosedBall₀` and `logCounting`)
* [MR886677], §1 for disk automorphisms and disk canonical factors used in the counting background
* [boas1954] and [levin1980] for the Jensen/counting estimates feeding the classical Hadamard
  product theorem
-/

section
noncomputable section

open Filter Topology Set Complex
open scoped BigOperators Topology

namespace Complex.Hadamard

/-!
### Lindelöf summability

A bound on `log (1 + ‖f z‖)` controls `logCounting` of the divisor and yields summability of
`‖a‖⁻¹^(m+1)` for the divisor-indexed canonical product.
-/

open scoped Real

/-- The total multiplicity of the nonzero divisor of `f` in the closed ball of radius `R`. -/
noncomputable def divisorMassClosedBall₀ (f : ℂ → ℂ) (R : ℝ) : ℝ :=
  Function.locallyFinsuppWithin.massClosedBall₀ (MeromorphicOn.divisor f (Set.univ : Set ℂ)) R


/-!
### Dyadic-shell summability for divisor-indexed zeros
-/

open scoped BigOperators


end Complex.Hadamard

end
end
end PntFile24


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/AbsMax.lean -/
section PntFile25
/-!
# Maximum-modulus bounds on disks

This file records a disk bound from a boundary bound on the sphere, in the form needed by
growth estimates for holomorphic functions.
-/

section
namespace Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]


end Complex

end
end PntFile25


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/CartanBound.lean -/
section PntFile26
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Cartan bounds for Hadamard factorization

Probabilistic-radius and averaging lemmas for the minimum-modulus step in the intrinsic Hadamard
pipeline. The basic pointwise input is

`log⁺ (1 / |1 - t|) ≤ √(2 / |1 - t|)`,

which majorizes the logarithmic singularity on dyadic intervals.

## References

* [tao246bComplexAnalysis] for the disk and averaging viewpoint
* [MR886677] for disk automorphisms and canonical factors on the unit disk
* [boas1954] and [levin1980] for the minimum-modulus estimates used in Hadamard factorization
-/

section
namespace Complex
namespace CartanBound

open Real MeasureTheory intervalIntegral
open scoped Topology ENNReal

/-!
### Pointwise bound for the logarithmic singularity

Used as an integrable majorant when averaging `log⁺ (1 / |1 - t|)` on dyadic intervals.
-/


/-! ### A radial majorant for the logarithmic singularity on a circle -/


/-! ### A coarse dyadic-interval bound for the singularity average -/

/-- The one-dimensional logarithmic singularity used in the Cartan/dyadic averaging argument. -/
noncomputable def φ (t : ℝ) : ℝ :=
  log⁺ (1 / |1 - t|)


/-!
### Bridge lemma: from the 1D singularity `φ` to a complex lower bound

On a circle `‖u‖ = r`, the quantity `log ‖1 - u/a‖` is bounded below in terms of `φ(r/‖a‖)`.
This is the local estimate in the probabilistic-radius argument.
-/


/-- The integral of the square-root majorant for `φ` on `[1/4, 4]`. -/
noncomputable def K : ℝ :=
  ∫ (t : ℝ) in (1 / 4 : ℝ)..(4 : ℝ), Real.sqrt (2 / |1 - t|) ∂volume


/-- A convenient explicit constant controlling dyadic averages of `φ`. -/
noncomputable def Cφ : ℝ :=
  Real.log 2 + 4 * K + 1


/-!
### A “good radius” lemma (probabilistic-radius / Cartan averaging)

This is the abstract selection principle used in the dyadic averaging: if an averaged singularity
kernel has controlled integral on `[R,2R]`, then there exists a radius `r ∈ (R,2R]` where the
pointwise sum is controlled.
-/

open scoped BigOperators


end CartanBound
end Complex

end
end PntFile26


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/CartanInverseFactorBound.lean -/
section PntFile27
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
## Pointwise inverse bounds for Weierstrass factors in Cartan-type arguments

This file bundles two pointwise estimates used in Cartan/minimum-modulus arguments for Hadamard
factorization:

- a bound in the “near regime”, combining `Complex.CartanBound.log_norm_one_sub_div_ge_neg_phi` with
  the general lower bound `Complex.log_norm_weierstrassFactor_ge_log_norm_one_sub_sub`;
- a bound in the “far regime” (`‖u / a‖ ≤ 1 / 2`), based on
  `Complex.log_norm_weierstrassFactor_ge_neg_two_pow`.

The results are stated in a form convenient for divisor-indexed zero enumerations.
-/

section
noncomputable section

namespace Complex.Hadamard

open Complex Real

/-!
### Auxiliary: bound `max 1 (‖u/a‖^m)` by `1 + (r/‖a‖)^τ`

This is the small “exponent comparison” lemma that occurs everywhere in the near regime.
-/


/-!
### Near regime: `‖(E_m(u/a))⁻¹‖` controlled by `φ(r/‖a‖)` plus an exponent term.
-/


/-!
### Far regime: if `‖u/a‖ ≤ 1/2` then `‖(E_m(u/a))⁻¹‖ ≤ exp(2*(r/‖a‖)^τ)`
-/


end Complex.Hadamard

end
end
end PntFile27


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/CartanMajorantBound.lean -/
section PntFile28
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
## Cartan bookkeeping: bound finite sums of the majorant

This file isolates the finite-sum estimate used in the Cartan/minimum-modulus argument:
we bound finite partial sums `∑_{p∈s} b p` of the majorant exponent `b` by
`Cprod * (1+r)^τ`, where `Cprod` depends only on `τ`, `m`, and the τ-sum `Sτ`.
-/

section
noncomputable section

namespace Complex.Hadamard

open scoped BigOperators
open Filter Finset Real Topology

section CartanFiniteSum

variable {α : Type*}


end CartanFiniteSum

/-- The Cartan product constant used in the Hadamard minimum-modulus bounds. -/
noncomputable def cartanProductConstant (m : ℕ) (τ Sτ : ℝ) : ℝ :=
  ((CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 3) * (Sτ + 1)


end Complex.Hadamard

end
end
end PntFile28


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/CartanProductBound.lean -/
section PntFile29
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
## Reusable product bounds by exponentials

This file collects small reusable algebra and infinite-product lemmas:

- bounding finite products by exponentials of finite sums;
- turning a uniform bound on finite partial products into a bound on the `HasProd` limit.
-/

section
noncomputable section

open scoped BigOperators
open Filter Finset Real Topology

/-!
### Finite products bounded by `exp(sum)`
-/

lemma Finset.prod_le_exp_sum {α : Type} (s : Finset α) (a : α → ℝ) (b : α → ℝ)
    (ha : ∀ x ∈ s, 0 ≤ a x) (hab : ∀ x ∈ s, a x ≤ Real.exp (b x)) :
    (∏ x ∈ s, a x) ≤ Real.exp (∑ x ∈ s, b x) := by
  calc
    (∏ x ∈ s, a x) ≤ ∏ x ∈ s, Real.exp (b x) := Finset.prod_le_prod ha hab
    _ = Real.exp (∑ x ∈ s, b x) := by
      simpa using (Real.exp_sum (s := s) (f := b)).symm

/-!
### Infinite products: pass a bound on all partial products to the limit
-/


end
end
end PntFile29


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/BorelCaratheodory.lean -/
section PntFile30
/-!
# Borel-Carathéodory estimates on closed balls

This file gives a closed-ball variant of Borel-Carathéodory for functions normalized at the
origin.  The form is convenient for growth estimates in finite-order complex analysis.
-/

section
open Metric

namespace Complex

/-- Variant of `borelCaratheodory_zero` for a uniform bound on a closed ball and `‖z‖ ≤ r`. -/
public theorem borelCaratheodory_zero_closedBall {f : ℂ → ℂ} {M r R : ℝ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    (hr : 0 < r) (hlt : r < R) (hM : 0 < M) (hf0 : f 0 = 0)
    (hf_re : ∀ w, ‖w‖ ≤ R → (f w).re ≤ M) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖f z‖ ≤ 2 * M * r / (R - r) := by
  have hR : 0 < R := lt_trans hr hlt
  have hz_ball : z ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hz.trans_lt hlt
  have hf_diff : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R) := by
    intro w hw
    have hw' : w ∈ Metric.closedBall (0 : ℂ) R := ball_subset_closedBall hw
    exact (hf w hw').differentiableAt.differentiableWithinAt
  have hf_map : Set.MapsTo f (Metric.ball (0 : ℂ) R) {w | w.re ≤ M} := by
    intro w hw
    simp only [Set.mem_ofPred_eq]
    have hw' : ‖w‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hw
    exact hf_re w hw'.le
  have hbc :=
    borelCaratheodory_zero hM hf_diff hf_map hR hz_ball hf0
  have hzR : ‖z‖ < R := by
    rw [Metric.mem_ball, dist_zero_right] at hz_ball
    exact hz_ball
  have hmono : ‖z‖ / (R - ‖z‖) ≤ r / (R - r) := by
    have hrden : 0 < R - r := sub_pos.mpr hlt
    have hden : 0 < R - ‖z‖ := sub_pos.mpr hzR
    rw [div_le_div_iff₀ hden hrden]
    nlinarith [hz, norm_nonneg z]
  have hM' : 0 ≤ 2 * M := mul_nonneg (by norm_num) (le_of_lt hM)
  calc ‖f z‖
      ≤ 2 * M * ‖z‖ / (R - ‖z‖) := hbc
    _ ≤ 2 * M * (r / (R - r)) := by
        simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hmono hM'
    _ = 2 * M * r / (R - r) := by ring

end Complex

end
end PntFile30


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/ExpPoly.lean -/
section PntFile31
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

/-!
## Zero-free entire functions of polynomial growth are `exp` of a polynomial

This is the final “exp(poly)” step in Hadamard factorization:
if `H` is entire and has no zeros, then a polynomial-type growth bound of the form
`‖H z‖ ≤ exp (C * (1 + ‖z‖) ^ n)` forces `H = exp (P)` for a polynomial `P` with `P.natDegree ≤ n`.

## Main results

* `Complex.Hadamard.zero_free_polynomial_growth_is_exp_poly`

-/

section
noncomputable section

namespace Complex
namespace Hadamard

open Complex Real BigOperators Finset Set Filter Topology Metric

open scoped Topology

/-!
### Main lemma: `H = exp(P)` with degree control
-/


end Hadamard
end Complex

end
end
end PntFile31


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/ExpPoly/Growth.lean -/
section PntFile32
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

/-!
## Growth of functions of the form `exp (P.eval z)`

This file contains auxiliary estimates used in “degree integrality” arguments: if `exp (P.eval)`
satisfies a growth bound with exponent `ρ`, then `P.natDegree ≤ ⌊ρ⌋`.


## Main results

* `Complex.Hadamard.natDegree_le_floor_of_growth_exp_eval`
* `Complex.Hadamard.natDegree_le_floor_of_exp_eval_norm_bound` : exponential norm bound implies
  degree bound

-/

section
noncomputable section

namespace Complex
namespace Hadamard

open Complex Real BigOperators Finset Set Filter Topology Metric

open scoped Topology

open Polynomial

/-!
### Integer-order obstruction for `exp (P.eval)`

If `exp (P.eval)` satisfied a growth bound with exponent `ρ < natDegree P`, then along a suitable
ray we get `log (1 + ‖exp (P z)‖) ≳ ‖z‖ ^ natDegree P`, contradicting the assumed exponent `ρ`.
This is the “degree is an integer” upgrade used to get `≤ ⌊ρ⌋` rather than a ceiling-type bound.
-/


-- The proof uses a reasonably heavy asymptotic/estimates argument; we raise the heartbeat limit.


end Hadamard
end Complex

end
end
end PntFile32


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/HadamardFactorization/Growth.lean -/
section PntFile33
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Hadamard factorization from a logarithmic growth bound

Assembles the Hadamard quotient, divisor summability, Cartan bounds, and exponential-polynomial
growth into `hadamard_factorization_of_growth`. The pipeline is:

1. `Summability` — Jensen / `logCounting` bounds imply divisor-indexed product convergence
2. `HadamardFactorization` — entire zero-free Hadamard quotient `H = f / (z^k · ∏ E_m)`
3. This file — Cartan circle bounds on `H`, then `zero_free_polynomial_growth_is_exp_poly`
4. `Order` — upgrade to `EntireOfOrderAtMost` and genus `⌊ρ⌋`

All products use `divisorCanonicalProduct` centered at `0` with multiplicities from
`MeromorphicOn.divisor`.

Compared with Tao's proof of the finite-order Hadamard theorem, this file replaces the
good-circle averaging argument by Cartan radius and product bounds.  The purpose is the same:
obtain sufficiently many circles on which the canonical product is not too small, so the zero-free
Hadamard quotient has polynomial exponential growth.  Thus the route is:
Jensen/zero counting (Tao Theorem 2 and Proposition 8) → canonical-product convergence (forward
Exercise 19 input) → Cartan minimum-modulus alternative to the good-circle step → finite-order
Hadamard (Theorem 22).

## Main results

* `hadamard_factorization_of_growth` : entire `f` with log-growth of order `ρ` is a Weierstrass
  product times `exp(P)`
* `zero_free_polynomial_growth_is_exp_poly` (in `ExpPoly`) : the Hadamard quotient is `exp(P)`
* Cartan bounds use `Complex.norm_le_of_mem_ball_of_forall_sphere_norm_le` from `AbsMax`

## References

* [tao246bComplexAnalysis], Theorem 22 for the finite-order Hadamard factorization strategy
* [boas1954] and [levin1980] for Weierstrass factors, canonical products, and the classical
  Hadamard product theorem
-/

section
noncomputable section

open Set Filter Asymptotics
open scoped Topology BigOperators

namespace Complex.Hadamard


end Complex.Hadamard

end
end
end PntFile33


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/HadamardFactorization/Order.lean -/
section PntFile34
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Hadamard factorization for finite-order entire functions

Upgrades `hadamard_factorization_of_growth` to the finite-order formulation via
`EntireOfOrderAtMost` and sequence- or divisor-indexed canonical products.

The growth input is routed through a midpoint exponent `τ` with `⌊τ⌋ = ⌊ρ⌋` so genus
`⌊ρ⌋` matches Tao's Weierstrass factor degree.

This file proves the finite-order Hadamard factorization theorem, corresponding to
[tao246bComplexAnalysis], Theorem 22.  The sequence-indexed theorem below packages the same
factorization after choosing an enumeration of the nonzero divisor indices.

## Main results

* `hadamard_factorization_of_order` : `f = exp(P) · z^k · ∏' E_m(z/a)`
* `hadamard_factorization_of_order_sequence` : sequence-indexed reindexing of the zero divisor
* `hadamard_factorization_of_order_centered` : arbitrary-center form, derived by translation
* `EntireOfOrderAtMost` : order at most `ρ` in the `ε`-family sense

## References

* [tao246bComplexAnalysis], Theorem 22
* [boas1954] and [levin1980] for the classical finite-order Hadamard product theorem, including
  genus `⌊ρ⌋` for functions of order at most `ρ`
-/

section
noncomputable section

open Set Filter Asymptotics
open scoped Topology BigOperators

namespace Complex.Hadamard


/-- An entire function has order at most `ρ` if it satisfies the `ε`-family growth bound used in
this formalization.

For every `ε > 0`, the norm is bounded by an exponential of order `ρ + ε`. This formulation is
the convenient finite-order input for the Jensen/counting estimates used in the Hadamard
factorization pipeline. -/
def EntireOfOrderAtMost (ρ : ℝ) (f : ℂ → ℂ) : Prop :=
    Differentiable ℂ f ∧ ∀ ε : ℝ, 0 < ε →
  ∃ C > 0, ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (ρ + ε))

namespace EntireOfOrderAtMost


end EntireOfOrderAtMost


end Complex.Hadamard

end
end
end PntFile34


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Calculus/Deriv/Polynomial.lean -/
section PntFile35
/-!
# Polynomial derivatives and logarithmic derivatives

Auxiliary derivative identities for exponential polynomials, used in the polynomial factor
appearing in Hadamard products.
-/

section
namespace Polynomial


end Polynomial

end
end PntFile35


/- SOURCE PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/ZetaFunctionalEquation.lean -/
section PntFile36
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
Completed zeta functional equation in product form.

We restate mathlib's completedRiemannZeta_one_sub as an equality of
(π^{-s/2} Γ(s/2) ζ(s)) with the corresponding (1-s) expression, matching
the form used by the ξ functional equation derivation.
-/

noncomputable section

section
open Complex

namespace Complex


/- Product-form functional equation matching `π^{−s/2} Γ(s/2) · ζ(s)` can be
   derived locally when needed via:
   `simpa [completedRiemannZeta, mul_comm, mul_left_comm, mul_assoc] using
     (completedRiemannZeta_one_sub s).symm`.
   Kept as a comment to avoid Hurwitz aliasing at call sites. -/

end Complex

end
end
end PntFile36


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/CompletedXi.lean -/
section PntFile37
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Local API for Mathlib's completed Riemann zeta and xi functions

This file records basic local facts about Mathlib's `completedRiemannZeta`

`Λ(s) = Γ_ℝ(s) * ζ(s)`.

It also defines the classical entire Riemann xi function
`ξ(s) = s * (s - 1) * Λ(s) / 2` via the pole-removed expression
`(s * (s - 1) * Λ₀(s) + 1) / 2`.  This is the object whose genus-one Hadamard product is used in
Kadiri-style zero-free region arguments.  This file only supplies the elementary bridge facts; the
Hadamard product is specialized in `Mathlib.NumberTheory.LSeries.RiemannZetaHadamard`, while the
xi logarithmic-derivative zero-sum bridge is also recorded there under explicit convergence,
nonvanishing, and point-not-a-zero hypotheses.

## References

* [kadiri2005] for the explicit zero-free-region context motivating the xi/log-derivative bridge
-/

section
noncomputable section

open Complex

namespace Complex

/-! ## The entire Riemann xi function -/

/-- The classical entire Riemann xi function, defined using the pole-removed completed zeta
function `Λ₀`.

Away from `0` and `1`, this agrees with `s * (s - 1) * completedRiemannZeta s / 2`; see
`riemannXi_eq_mul_completedRiemannZeta`. -/
noncomputable def riemannXi (s : ℂ) : ℂ :=
  (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2


/-- Away from the poles of `completedRiemannZeta`, `riemannXi` is the classical product
`s * (s - 1) * completedRiemannZeta s / 2`. -/
theorem riemannXi_eq_mul_completedRiemannZeta {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s = s * (s - 1) * completedRiemannZeta s / 2 := by
  rw [riemannXi, completedRiemannZeta_eq]
  have h1ms : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  field_simp [hs0, h1ms]
  ring

/-- Functional equation for the Riemann xi function. -/
theorem riemannXi_one_sub (s : ℂ) : riemannXi (1 - s) = riemannXi s := by
  rw [riemannXi, riemannXi, completedRiemannZeta₀_one_sub]
  ring

end Complex

end
end
end PntFile37


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/Basic.lean -/
section PntFile38
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Elementary complex-analysis API

Small algebraic and metric lemmas for complex half-planes and basic rational expressions.
-/

section
namespace Complex


/-- If `a < re z`, nested open balls around `z` stay in the half-plane `re · ≥ a`. -/
theorem exists_pos_radius_forall_mem_ball_re_ge {z₀ : ℂ} {a : ℝ} (ha : a < z₀.re) :
    ∃ δ > 0, ∀ (x y : ℂ), dist x z₀ < δ → dist y x < δ → a ≤ y.re := by
  set δ : ℝ := (z₀.re - a) / 2 with hδdef
  have hpos : 0 < z₀.re - a := sub_pos.mpr ha
  have hδpos : 0 < δ := by simpa [hδdef] using half_pos hpos
  refine ⟨δ, hδpos, ?_⟩
  intro x y hx hy
  have htri : dist y z₀ ≤ dist y x + dist x z₀ := dist_triangle y x z₀
  have hsumlt : dist y x + dist x z₀ < δ + δ := add_lt_add hy hx
  have hnorm_lt : ‖y - z₀‖ < δ + δ := by simpa [dist_eq_norm] using lt_of_le_of_lt htri hsumlt
  have hdeltaSum : δ + δ = z₀.re - a := by simp [hδdef, add_halves]
  have hnorm_lt_re : ‖y - z₀‖ < z₀.re - a := by simpa [hdeltaSum] using hnorm_lt
  have h_eps_lt : a < z₀.re - ‖y - z₀‖ := by
    have hsum' : a + ‖y - z₀‖ < z₀.re := by
      simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using
        (add_lt_add_left hnorm_lt_re a)
    simpa [lt_sub_iff_add_lt] using hsum'
  have hre_lower : -‖y - z₀‖ ≤ (y - z₀).re := (abs_le.mp (abs_re_le_norm (y - z₀))).1
  have hyge : z₀.re - ‖y - z₀‖ ≤ y.re := by
    have h' : z₀.re + (-‖y - z₀‖) ≤ z₀.re + (y - z₀).re := add_le_add_right hre_lower z₀.re
    have h'' : z₀.re + (y - z₀).re = y.re := by
      simp [sub_eq_add_neg]
    simpa [sub_eq_add_neg, h''] using h'
  exact le_of_lt (lt_of_lt_of_le h_eps_lt hyge)

end Complex

end
end PntFile38


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/Trigonometric.lean -/
section PntFile39
/-!
# Complex trigonometric bounds

Elementary exponential bounds for complex trigonometric functions.
-/

section
namespace Complex


end Complex

end
end PntFile39


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Gamma/IntegralBounds.lean -/
section PntFile40
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Gamma bounds from the Euler integral

Pointwise bounds for `Real.Gamma` and `Complex.Gamma` used in finite-order estimates for
completed zeta functions. These follow from the Euler integral representation and convexity on
`[1, 2]`, without Binet's kernel.

## Main results

* `Real.Gamma.le_one_of_mem_Icc` : `Γ(x) ≤ 1` for `x ∈ [1, 2]`
* `Complex.Gamma.norm_le_Gamma_re` : `‖Γ z‖ ≤ Γ (re z)` for `0 < re z`
* `Complex.Gamma.norm_le_one` : `‖Γ z‖ ≤ 1` for `1 ≤ re z ≤ 2`

## References

* [DLMF], §5.2.1 for the Euler integral representation
-/

open Real Complex Set MeasureTheory

section
noncomputable section

namespace Real
namespace Gamma


end Gamma
end Real

namespace Complex
namespace Gamma


end Gamma
end Complex

end

end
end PntFile40


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/GammaBounds.lean -/
section PntFile41
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Bounds for `Complex.Gammaℝ`

Cauchy bounds for derivatives of Deligne's real Gamma factor.
-/

section
noncomputable section

open Complex Real Set Metric
open Real Set MeasureTheory Filter Asymptotics
open scoped Real Topology

namespace Real
namespace Gamma

-- On `[1 / 2, 1]`, convexity bounds `Γ` by its value at `1 / 2`.


end Gamma
end Real

open Gamma Real

-- Tail bound for Euler's Gamma integral on `1 / 2 ≤ a ≤ 1`.


namespace Complex
namespace Gamma


end Gamma
end Complex

end

end
end PntFile41


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Gamma/GammaStirlingAux.lean -/
section PntFile42
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Auxiliary lemmas for Gamma strip bounds

This file contains the shared algebraic and geometric lemmas used to shift `Γ(s)` into a
vertical strip by the functional equation.

## References

* [DLMF], §5.11 for Stirling expansions around the Gamma function
* [whittakerWatson1927], Chapter XII for the classical Gamma-function background
* The functional equation Γ(z+1) = z·Γ(z) (Mathlib: `Complex.Gamma_add_one`)

## Main results

* `norm_sub_real_le`: subtracting a positive real smaller than `re s` does not increase `‖s‖`
* `prod_norm_le_pow`: the shifted Gamma product has norm at most `‖s‖ ^ m`
* `Gamma_iterate`: the iterated Gamma functional equation
-/

section
open Complex
open scoped Topology BigOperators

namespace Stirling.GammaAux

/-! ## Geometry of the shifted product -/


/-! ## Iterated functional equation -/


end Stirling.GammaAux

end
end PntFile42


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Gamma/StripBounds.lean -/
section PntFile43
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Gamma bounds in half-planes

Bounds for `Complex.Gamma` and Deligne's real Gamma factor `Complex.Gammaℝ`, used
in finite-order estimates for completed zeta functions.
-/

section
noncomputable section

open Complex Real Set Metric


/-! ## Stirling-type bounds for the complex Gamma function

This section provides Stirling-type bounds on `Complex.Gamma` and the archimedean factor `Gammaℝ`
in regions of the complex plane that arise naturally in the analytic theory of
the completed zeta function, Hadamard factorization, and the Selberg class.
-/

namespace Real.Stirling


/-- Absorbs the `s ↦ s/2 + 1` shift in half-plane Stirling bounds. -/
noncomputable def half_shift_log_constant : ℝ :=
  (3 / 2 : ℝ) * (Real.log 3 / Real.log 2 + 1)


end Real.Stirling

namespace Complex.Gamma

open Real


end Complex.Gamma

namespace Complex.Gammaℝ.Stirling

open Real


end Complex.Gammaℝ.Stirling
end

end
end PntFile43


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean -/
section PntFile44
/-!
# Real-power estimates

Elementary logarithmic and real-power inequalities used in decay and growth estimates.
-/
section
namespace Real

/-- For `1 < u` and `ε > 0`, `log u * u^(-1-ε) ≤ (2/ε) * u^(-1-ε/2)`. -/
theorem log_mul_rpow_neg_le_two_div_mul_rpow_neg {ε : ℝ} (hε : 0 < ε) {u : ℝ} (hu : 1 < u) :
    Real.log u * u ^ (-1 - ε) ≤ (2 / ε) * u ^ (-1 - ε / 2) := by
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hpos_coeff : 0 < 2 / ε := by
    simpa [one_div, div_eq_mul_inv] using mul_pos (by norm_num : (0 : ℝ) < 2) (inv_pos.mpr hε)
  have hle_exp : (ε / 2) * Real.log u ≤ Real.exp ((ε / 2) * Real.log u) :=
    le_trans (by linarith) (Real.add_one_le_exp ((ε / 2) * Real.log u))
  have hlog_bound : Real.log u ≤ (2 / ε) * Real.exp ((ε / 2) * Real.log u) := by
    calc
      Real.log u = (2 / ε) * ((ε / 2) * Real.log u) := by field_simp [hεne]
      _ ≤ (2 / ε) * Real.exp ((ε / 2) * Real.log u) :=
        mul_le_mul_of_nonneg_left hle_exp (le_of_lt hpos_coeff)
  have hexp_rpow : Real.exp ((ε / 2) * Real.log u) = u ^ (ε / 2) := by
    simp [Real.rpow_def_of_pos hu0, mul_comm]
  have hmul : Real.log u * u ^ (-1 - ε) ≤ ((2 / ε) * u ^ (ε / 2)) * u ^ (-1 - ε) :=
    mul_le_mul_of_nonneg_right (by simpa [hexp_rpow] using hlog_bound)
      (le_of_lt (Real.rpow_pos_of_pos hu0 _))
  have hpow_mul : u ^ (ε / 2) * u ^ (-1 - ε) = u ^ (-1 - ε / 2) := by
    rw [← Real.rpow_add hu0, show ε / 2 + (-1 - ε) = -1 - ε / 2 by ring]
  calc
    Real.log u * u ^ (-1 - ε)
        ≤ ((2 / ε) * u ^ (ε / 2)) * u ^ (-1 - ε) := hmul
    _ = (2 / ε) * u ^ (-1 - ε / 2) := by rw [mul_assoc, hpow_mul]

end Real

namespace Complex


end Complex

end
end PntFile44


/- SOURCE PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/RiemannZeta.lean -/
section PntFile45
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Extra Riemann zeta API

Vertical lines, prime-power bounds, and Euler-product identities supporting strip
and convexity bounds in `RiemannZetaConvexity`.

## Main results

* `verticalLine`, `verticalLine_re`, `verticalLine_add_const`
* `Nat.Primes.norm_one_sub_cpow_neg_vertical_le` and companions
* `riemannZeta_div_riemannZeta_eq_tprod_inv_one_add`, `norm_riemannZeta_div_riemannZeta`
* `norm_riemannZeta_eulerProduct`, `tprod_inv_one_add_real_le_riemannZeta_norm_on_verticalLine`
-/

section
open scoped BigOperators Topology
open Complex Filter Real Set

/-- The point `σ + it` on the vertical line with real part `σ`. -/
def verticalLine (σ t : ℝ) : ℂ := σ + t * Complex.I


namespace Nat.Primes


end Nat.Primes

section RiemannZetaEulerProduct

open Nat.Primes


end RiemannZetaEulerProduct

/-- `1 / (n : ℂ) ^ s` rewrites to `(n : ℂ) ^ (-s)` away from `n = 0`. -/
theorem one_div_natCast_cpow_eq_ite_cpow_neg (s : ℂ) (hs : s ≠ 0) (n : ℕ) :
    1 / (n : ℂ) ^ s = if n = 0 then 0 else (n : ℂ) ^ (-s) := by
  by_cases h : n = 0
  · simp [h, Complex.zero_cpow hs]
  · simp [h, one_div, Complex.cpow_neg]

end


end PntFile45


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/Convex.lean -/
section PntFile46
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Path-connected half-planes

This file proves that a right half-plane remains path-connected after removing one point.
The lemma is used to choose logarithms on punctured half-planes in complex-analysis arguments.
-/

section
namespace Complex

theorem isPathConnected_halfSpace_re_gt_diff_singleton (a : ℝ) (p : ℂ) (hp : a < p.re) :
    IsPathConnected ({z : ℂ | a < z.re} \ ({p} : Set ℂ)) := by
  classical
  let S1 : Set ℂ := {z : ℂ | a < z.re ∧ z.im < p.im}
  let S2 : Set ℂ := {z : ℂ | a < z.re ∧ z.re < p.re}
  let S3 : Set ℂ := {z : ℂ | a < z.re ∧ p.im < z.im}
  let S4 : Set ℂ := {z : ℂ | p.re < z.re}
  have hS1conv : Convex ℝ S1 := by
    have h1 : Convex ℝ {z : ℂ | a < z.re} := convex_halfSpace_re_gt (r := a)
    have h2 : Convex ℝ {z : ℂ | z.im < p.im} := convex_halfSpace_im_lt (r := p.im)
    simpa [S1, Set.ofPred_and] using h1.inter h2
  have hS2conv : Convex ℝ S2 := by
    have h1 : Convex ℝ {z : ℂ | a < z.re} := convex_halfSpace_re_gt (r := a)
    have h2 : Convex ℝ {z : ℂ | z.re < p.re} := convex_halfSpace_re_lt (r := p.re)
    simpa [S2, Set.ofPred_and] using h1.inter h2
  have hS3conv : Convex ℝ S3 := by
    have h1 : Convex ℝ {z : ℂ | a < z.re} := convex_halfSpace_re_gt (r := a)
    have h2 : Convex ℝ {z : ℂ | p.im < z.im} := convex_halfSpace_im_gt (r := p.im)
    simpa [S3, Set.ofPred_and] using h1.inter h2
  have hS4conv : Convex ℝ S4 := by
    simpa [S4] using (convex_halfSpace_re_gt (r := p.re))
  have hS1ne : S1.Nonempty := by
    refine ⟨((max a p.re) + 1 : ℝ) + (p.im - 1) * Complex.I, ?_⟩
    have h1 : a < (max a p.re) + 1 := by
      have : a ≤ max a p.re := le_max_left _ _
      exact lt_of_le_of_lt this (by linarith)
    have h2 : (p.im - 1) < p.im := by linarith
    simpa [S1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      using And.intro h1 h2
  have hS2ne : S2.Nonempty := by
    refine ⟨((a + p.re) / 2 : ℝ) + (p.im : ℝ) * Complex.I, ?_⟩
    have h1 : a < (a + p.re) / 2 := by linarith
    have h2 : (a + p.re) / 2 < p.re := by linarith
    simpa [S2, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      using And.intro h1 h2
  have hS3ne : S3.Nonempty := by
    refine ⟨((max a p.re) + 1 : ℝ) + (p.im + 1) * Complex.I, ?_⟩
    have h1 : a < (max a p.re) + 1 := by
      have : a ≤ max a p.re := le_max_left _ _
      exact lt_of_le_of_lt this (by linarith)
    have h2 : p.im < (p.im + 1) := by linarith
    simpa [S3, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      using And.intro h1 h2
  have hS4ne : S4.Nonempty := by
    refine ⟨(p.re + 1 : ℝ) + (0 : ℝ) * Complex.I, ?_⟩
    have : p.re < p.re + 1 := by linarith
    simp [S4, Complex.add_re]
  have hS1pc : IsPathConnected S1 := (hS1conv.isPathConnected hS1ne)
  have hS2pc : IsPathConnected S2 := (hS2conv.isPathConnected hS2ne)
  have hS3pc : IsPathConnected S3 := (hS3conv.isPathConnected hS3ne)
  have hS4pc : IsPathConnected S4 := (hS4conv.isPathConnected hS4ne)
  let A : Set ℂ := S1 ∪ S2
  let B : Set ℂ := S3 ∪ S4
  have hS1S2_int : (S1 ∩ S2).Nonempty := by
    refine ⟨((a + p.re) / 2 : ℝ) + (p.im - (1/2)) * Complex.I, ?_⟩
    have h1a : a < (a + p.re) / 2 := by linarith
    have h1b : (p.im - (1/2)) < p.im := by linarith
    have h2a : a < (a + p.re) / 2 := by linarith
    have h2b : (a + p.re) / 2 < p.re := by linarith
    constructor
    · simpa [S1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h1a h1b
    · simpa [S2, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h2a h2b
  have hApc : IsPathConnected A :=
    IsPathConnected.union (U := S1) (V := S2) hS1pc hS2pc (by
      rcases hS1S2_int with ⟨z, hz⟩; exact ⟨z, hz⟩)
  have hS3S4_int : (S3 ∩ S4).Nonempty := by
    refine ⟨(p.re + 1 : ℝ) + (p.im + 1) * Complex.I, ?_⟩
    have h3a : a < p.re + 1 := lt_trans hp (by linarith)
    have h3b : p.im < p.im + 1 := by linarith
    have h4 : p.re < p.re + 1 := by linarith
    constructor
    · simpa [S3, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h3a h3b
    · simp [S4, Complex.add_re, Complex.mul_re]
  have hBpc : IsPathConnected B :=
    IsPathConnected.union (U := S3) (V := S4) hS3pc hS4pc (by
      rcases hS3S4_int with ⟨z, hz⟩; exact ⟨z, hz⟩)
  have hABint : (A ∩ B).Nonempty := by
    refine ⟨(p.re + 1 : ℝ) + (p.im - 1) * Complex.I, ?_⟩
    constructor
    · refine Or.inl ?_
      have h1 : a < p.re + 1 := lt_trans hp (by linarith)
      have h2 : (p.im - 1) < p.im := by linarith
      simpa [S1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h1 h2
    · refine Or.inr ?_
      have h4 : p.re < p.re + 1 := by linarith
      simp [S4, Complex.add_re, Complex.mul_re]
  have hUnionPC : IsPathConnected (A ∪ B) :=
    IsPathConnected.union (U := A) (V := B) hApc hBpc (by
      rcases hABint with ⟨z, hz⟩; exact ⟨z, hz⟩)
  have hcover : ({z : ℂ | a < z.re} \ ({p} : Set ℂ)) = A ∪ B := by
    ext z; constructor
    · intro hz
      rcases hz with ⟨hzH, hznot⟩
      rcases lt_trichotomy z.re p.re with hlt | heq | hgt
      · exact Or.inl (Or.inr ⟨hzH, hlt⟩)
      · rcases lt_trichotomy z.im p.im with himlt | himeq | himgt
        · exact Or.inl (Or.inl ⟨hzH, himlt⟩)
        · have hz_eq : z = p := by
            have hzdecomp : (z.re : ℂ) + (z.im : ℝ) * Complex.I = z := by simp
            have hpdecomp : (p.re : ℂ) + (p.im : ℝ) * Complex.I = p := by simp
            have : (z.re : ℂ) + (z.im : ℝ) * Complex.I = (p.re : ℂ) + (p.im : ℝ) * Complex.I := by
              simp [heq, himeq]
            simpa [hzdecomp, hpdecomp] using this
          have : z ∈ ({p} : Set ℂ) := by simp [Set.mem_singleton_iff, hz_eq]
          exact (hznot this).elim
        · exact Or.inr (Or.inl ⟨hzH, himgt⟩)
      · exact Or.inr (Or.inr hgt)
    · intro hz
      have hzH : a < z.re := by
        rcases hz with hA | hB
        · rcases hA with hS1 | hS2
          · exact hS1.1
          · exact hS2.1
        · rcases hB with hS3 | hS4
          · exact hS3.1
          · exact lt_trans hp hS4
      have hzneq : z ≠ p := by
        rcases hz with hA | hB
        · rcases hA with hS1 | hS2
          · intro h
            have : z.im = p.im := by simp [h]
            have : z.im < z.im := by simpa [this] using hS1.2
            exact lt_irrefl _ this
          · intro h
            have : z.re = p.re := by simp [h]
            exact (ne_of_lt hS2.2) this
        · rcases hB with hS3 | hS4
          · intro h
            have : p.im = z.im := by simp [h]
            have : z.im < z.im := by simpa [this] using hS3.2
            exact lt_irrefl _ this
          · intro h
            have : p.re = z.re := by simp [h]
            exact (ne_of_gt hS4) this.symm
      exact And.intro hzH (by intro hzmem; exact hzneq (by simpa [Set.mem_singleton_iff] using hzmem))
  simpa [hcover] using hUnionPC


end Complex

end
end PntFile46


/- SOURCE PrimeNumberTheoremAnd/Mathlib/MeasureTheory/Integral/IntegrableOn.lean -/
section PntFile47
/-!
# Domination for `IntegrableOn`

A small `IntegrableOn` wrapper for a.e. norm domination on a restricted measure.
-/

section
namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
variable {μ : Measure α} {s : Set α}

/-- If `‖f x‖ ≤ g x` a.e. on `s` and `g` is integrable on `s`, then so is `f`. -/
lemma IntegrableOn.mono' {f : α → E} {g : α → ℝ} (hg : IntegrableOn g s μ)
    (hf : AEStronglyMeasurable f (μ.restrict s))
    (h : ∀ᵐ x ∂μ.restrict s, ‖f x‖ ≤ g x) : IntegrableOn f s μ := by
  exact Integrable.mono' hg hf h

end MeasureTheory

end
end PntFile47


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean -/
section PntFile48
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Improper-integral estimates

Elementary power-integral evaluations and convergence criteria for interval integrals on
half-lines.
-/

section
open Real Set Filter MeasureTheory intervalIntegral
open scoped Topology


theorem intervalIntegral.tendsto_integral_Ioi_of_ae_norm_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (g : ℝ → ℝ) (c : ℝ)
    (hfm : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict (Ioi c)))
    (hbound : ∀ᵐ u ∂MeasureTheory.volume.restrict (Ioi c), ‖f u‖ ≤ g u)
    (hg : MeasureTheory.IntegrableOn g (Ioi c) MeasureTheory.volume) :
    Tendsto (fun N : ℕ => ∫ u in c..N, f u) atTop (𝓝 (∫ u in Ioi c, f u)) :=
  intervalIntegral_tendsto_integral_Ioi c (MeasureTheory.IntegrableOn.mono' hg hfm hbound)
    tendsto_natCast_atTop_atTop


end
end PntFile48


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Algebra/Order/Floor/Ring.lean -/
section PntFile49
/-!
# Floor and fractional-part estimates

Small floor-ring lemmas used by summation and Abel-continuation arguments.
-/

section
namespace Int

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R] [FloorRing R]

theorem fract_abs_le_one (a : R) : |fract a| ≤ 1 := by
  rw [abs_fract]
  exact (fract_lt_one a).le

end Int

end
end PntFile49


/- SOURCE PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean -/
section PntFile50
/-!
# Derivatives of complex powers

Derivative identities for functions of the form `w ↦ a * (u : ℂ) ^ (-w - 1)`.
-/
section
namespace Complex

/-- `(u : ℂ) ^ r` is continuous on `[a, b]` when `a > 0`. -/
theorem continuousOn_ofReal_cpow {r : ℂ} {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun u : ℝ => (u : ℂ) ^ r) (Set.Icc a b) :=
  (continuous_ofReal.continuousOn.cpow continuousOn_const
    (fun _ hu => (ofReal_mem_slitPlane).2 (lt_of_lt_of_le ha hu.1))).mono Set.Subset.rfl

theorem deriv_ofReal_cpow_neg (s : ℂ) {x : ℝ} (hx : 0 < x) :
    deriv (fun (t : ℝ) => (t : ℂ) ^ (-s)) x = -s * (x : ℂ) ^ (-s - 1) := by
  by_cases hs : s = 0
  · simp [hs, deriv_const, cpow_zero, sub_eq_add_neg]
  · simpa [sub_eq_add_neg] using deriv_ofReal_cpow_const hx.ne' (neg_ne_zero.mpr hs)

theorem continuousOn_deriv_ofReal_cpow_neg (s : ℂ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (deriv (fun (t : ℝ) => (t : ℂ) ^ (-s))) (Set.Icc a b) :=
    ((continuousOn_const : ContinuousOn (fun (_ : ℝ) => (-s : ℂ)) (Set.Icc a b)).mul
      (continuousOn_ofReal_cpow (r := -s - 1) ha)).congr fun _ ht =>
    deriv_ofReal_cpow_neg s (lt_of_lt_of_le ha ht.1)

theorem ofReal_cpow_mul_cpow_neg_sub_one (s : ℂ) {u : ℝ} (hu : 0 < u) :
    (u : ℂ) * (u : ℂ) ^ (-s - 1) = (u : ℂ) ^ (-s) := by
  have hx : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.ne'
  calc
    (u : ℂ) * (u : ℂ) ^ (-s - 1) = (u : ℂ) ^ (1 : ℂ) * (u : ℂ) ^ (-s - 1) := by simp [cpow_one]
    _ = (u : ℂ) ^ (-s) := by rw [← cpow_add _ _ hx]; ring_nf

theorem natCast_mul_cpow_neg_eq_cpow_one_sub (N : ℕ) (s : ℂ) (hN : N ≠ 0) :
    (N : ℂ) * (N : ℂ) ^ (-s) = (N : ℂ) ^ (1 - s) := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  calc
    (N : ℂ) * (N : ℂ) ^ (-s) = (N : ℂ) ^ (1 : ℂ) * (N : ℂ) ^ (-s) := by simp [cpow_one]
    _ = (N : ℂ) ^ (1 - s) := by rw [← cpow_add _ _ hN']; ring_nf

theorem HasDerivAt.const_mul_ofReal_cpow_neg_sub_one (a : ℂ) {u : ℝ} (hu : 0 < u) (z : ℂ) :
    HasDerivAt (fun w => a * (u : ℂ) ^ (-w - 1))
      (-a * (Complex.log u) * (u : ℂ) ^ (-z - 1)) z := by
  set huC : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.ne'
  have hf : HasDerivAt (fun w => -w - 1) (-1) z := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (hasDerivAt_id z).neg.sub_const (1 : ℂ)
  have hbase : HasDerivAt (fun w => (u : ℂ) ^ (-w - 1))
      ((u : ℂ) ^ (-z - 1) * Complex.log (u : ℂ) * (-1)) z :=
    HasDerivAt.const_cpow (c := (u : ℂ)) hf (Or.inl huC)
  have hbase' : HasDerivAt (fun w => (u : ℂ) ^ (-w - 1))
      (-(Complex.log (u : ℂ)) * (u : ℂ) ^ (-z - 1)) z := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbase
  have hlog : (Real.log u : ℂ) = Complex.log (u : ℂ) := by
    simpa using (ofReal_log (x := u) (hx := le_of_lt hu))
  simpa [hlog, mul_comm, mul_left_comm, mul_assoc] using hbase'.const_mul a

end Complex

end
end PntFile50


/- SOURCE PrimeNumberTheoremAnd/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean -/
section PntFile51
/-!
# Interval-integral congruence lemmas

Congruence for interval integrals when the integrands agree on the oriented interval.
-/

section
open Set MeasureTheory

namespace intervalIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f g : ℝ → E} {μ : Measure ℝ}

/-- If two functions agree on `Ioc a b`, their interval integrals agree. -/
theorem integral_congr_Ioc_of_le {a b : ℝ} (hab : a ≤ b)
    (h : ∀ u ∈ Ioc a b, f u = g u) :
    ∫ u in a..b, f u ∂μ = ∫ u in a..b, g u ∂μ := by
  refine integral_congr_ae' (Filter.Eventually.of_forall ?_) (Filter.Eventually.of_forall ?_) <;>
    intro u hu
  · exact h u hu
  · have hempty : Ioc b a = ∅ := Ioc_eq_empty hab.not_gt
    exact (hempty ▸ hu).elim

end intervalIntegral

end
end PntFile51


/- SOURCE PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/RiemannZetaAbelKernel.lean -/
section PntFile52
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Fractional-part kernel for the Abel zeta formula

`K_s(u) = {u} · u^{-s-1}` and its integrability / domination lemmas, used in
`RiemannZetaPartialSum` and `RiemannZetaAbelContinuation`.

## Main results

* `zetaAbelFractKernel`, `norm_zetaAbelFractKernel_le`
* `ZetaAbelFractKernel.intervalIntegrable`, `integrableOn_Ioi`, `tendsto_integral_Ioi`
* `ZetaAbelFractKernel.hasDerivAt_in_param`, `kernel_deriv_norm_bound_on_ball`
* `ZetaAbelFractKernel.integral_analytic`
-/

section
open scoped Topology
open Real Set Filter Topology MeasureTheory Complex

/-- Fractional-part kernel `{u} · u^{-s-1}` (`K_s` in the Abel formula). -/
noncomputable def zetaAbelFractKernel (s : ℂ) (u : ℝ) : ℂ :=
  ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)

/-- `{u} · u^{-s-1}` is dominated by `u^{- re s - 1}` for `u ≥ 1`. -/
theorem norm_zetaAbelFractKernel_le (u : ℝ) (hu : 1 ≤ u) (s : ℂ) :
    ‖zetaAbelFractKernel s u‖ ≤ u ^ (-s.re - 1) := by
  have hu0 : 0 < u := one_pos.trans_le hu
  have hfract_le1 : ‖((Int.fract u : ℝ) : ℂ)‖ ≤ 1 := by simpa using Int.fract_abs_le_one u
  have hle : ‖zetaAbelFractKernel s u‖ ≤ ‖(u : ℂ) ^ (-s - 1)‖ := by
    calc
      _ = ‖((Int.fract u : ℝ) : ℂ)‖ * ‖(u : ℂ) ^ (-s - 1)‖ := by rw [zetaAbelFractKernel, norm_mul]
      _ ≤ 1 * ‖(u : ℂ) ^ (-s - 1)‖ := by
        exact mul_le_mul_of_nonneg_right hfract_le1 (norm_nonneg _)
      _ = ‖(u : ℂ) ^ (-s - 1)‖ := one_mul _
  have hb : ‖(u : ℂ) ^ (-s - 1)‖ = u ^ (-s.re - 1) := by
    have hre : (-s - 1).re = -s.re - 1 := by
      simp [sub_eq_add_neg]
    simpa [hre] using Complex.norm_cpow_eq_rpow_re_of_pos hu0 (-s - 1)
  exact hle.trans_eq hb

namespace ZetaAbelFractKernel

lemma aestronglyMeasurable (s : ℂ) (S : Set ℝ) (_ : MeasurableSet S) :
    AEStronglyMeasurable (fun u => zetaAbelFractKernel s u) (volume.restrict S) := by
  refine (measurable_fract.complex_ofReal.mul ?_).aestronglyMeasurable
  simpa using Complex.measurable_ofReal.pow_const (-s - 1)

lemma ae_bound_Ioi (s : ℂ) :
    ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))),
      ‖zetaAbelFractKernel s u‖ ≤ u ^ (-s.re - 1) :=
  ae_restrict_iff' measurableSet_Ioi |>.2 <| ae_of_all _ fun u hu =>
    norm_zetaAbelFractKernel_le u (le_of_lt hu) s

lemma intervalIntegrable (s : ℂ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u => zetaAbelFractKernel s u) volume a b := by
  let μ := volume.restrict (Icc a b)
  set g : ℝ → ℝ := fun u => ‖(u : ℂ) ^ (-s - 1)‖
  have hmeas := aestronglyMeasurable s (Icc a b) measurableSet_Icc
  have hbound_ae : ∀ᵐ u ∂μ, ‖zetaAbelFractKernel s u‖ ≤ g u := by
    refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ ?_)
    intro u huIcc
    have hu0 : 0 < u := lt_of_lt_of_le one_pos (ha.trans huIcc.1)
    have hg_eq : g u = u ^ (-s.re - 1) := by
      simp [g, Complex.norm_cpow_eq_rpow_re_of_pos hu0, sub_eq_add_neg]
    exact (norm_zetaAbelFractKernel_le u (ha.trans huIcc.1) s).trans (le_of_eq hg_eq.symm)
  have hg : Integrable g μ := by
    simpa [μ, g] using!
      (Complex.continuousOn_ofReal_cpow (ha := one_pos.trans_le ha)).norm.integrableOn_compact
        isCompact_Icc
  have hf0 : Integrable (fun _ : ℝ => (0 : ℂ)) μ := by simp [μ]
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 <|
    integrable_of_norm_sub_le hmeas hf0 hg
      (hbound_ae.mono fun u hu => by simpa [sub_eq_add_neg, μ, g] using hu)

theorem tendsto_integral_Ioi (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u) atTop
      (𝓝 (∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u)) :=
  intervalIntegral.tendsto_integral_Ioi_of_ae_norm_le (f := fun u => zetaAbelFractKernel s u)
    (g := fun u => u ^ (-s.re - 1)) 1
    (aestronglyMeasurable s (Ioi (1 : ℝ)) measurableSet_Ioi) (ae_bound_Ioi s)
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos)

theorem integrableOn_Ioi (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun u => zetaAbelFractKernel s u) (volume.restrict (Ioi (1 : ℝ))) := by
  set ε : ℝ := s.re / 2
  set g : ℝ → ℝ := fun u => u ^ (-1 - ε)
  have hfm := aestronglyMeasurable s (Ioi (1 : ℝ)) measurableSet_Ioi
  have hε : 0 < ε := half_pos hs
  have hεle : ε ≤ s.re := half_le_self (le_of_lt hs)
  have hbound : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), ‖zetaAbelFractKernel s u‖ ≤ g u :=
    ae_restrict_iff' measurableSet_Ioi |>.2 <| ae_of_all _ fun u hu =>
      (norm_zetaAbelFractKernel_le u (le_of_lt hu) s).trans
        (Real.rpow_le_rpow_of_exponent_le (le_of_lt hu) (by linarith [hεle]))
  simpa [IntegrableOn] using
    IntegrableOn.mono' (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos) hfm hbound

lemma aestronglyMeasurable_param_deriv (z : ℂ) :
    AEStronglyMeasurable (fun u : ℝ => -((Real.log u) : ℂ) * zetaAbelFractKernel z u)
      (volume.restrict (Ioi (1 : ℝ))) := by
  have hmeas : Measurable (fun u : ℝ => zetaAbelFractKernel z u) :=
    (measurable_fract.complex_ofReal.mul <| by simpa using Complex.measurable_ofReal.pow_const (-z - 1))
  simpa only [neg_mul] using
    (Real.measurable_log.complex_ofReal.fun_mul hmeas).fun_neg.aestronglyMeasurable

lemma eventually_aestronglyMeasurable_param (s : ℂ) :
    ∀ᶠ z in 𝓝 s,
      AEStronglyMeasurable (fun u : ℝ => zetaAbelFractKernel z u) (volume.restrict (Ioi (1 : ℝ))) :=
  Eventually.of_forall fun z => aestronglyMeasurable z (Ioi (1 : ℝ)) measurableSet_Ioi

theorem hasDerivAt_in_param (u : ℝ) (hu : 1 < u) (z : ℂ) :
    HasDerivAt (fun w => zetaAbelFractKernel w u)
      (-((Real.log u) : ℂ) * zetaAbelFractKernel z u) z := by
  have h := HasDerivAt.const_mul_ofReal_cpow_neg_sub_one ((Int.fract u : ℝ) : ℂ)
    (lt_trans zero_lt_one hu) z
  have hfun : (fun w => zetaAbelFractKernel w u) = fun w => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-w - 1) := by
    ext w; simp [zetaAbelFractKernel]
  exact (h.congr_of_eventuallyEq (EventuallyEq.of_eq hfun)).congr_deriv (by
    simp [zetaAbelFractKernel, Complex.ofReal_log (x := u) (hx := le_of_lt (lt_trans zero_lt_one hu)),
      mul_comm, mul_assoc, mul_left_comm])

theorem kernel_deriv_norm_bound_on_ball (ε : ℝ) (u : ℝ) (hu : 1 < u) (x : ℂ) (hx : ε ≤ x.re) :
    ‖-((Real.log u) : ℂ) * zetaAbelFractKernel x u‖ ≤ Real.log u * u ^ (-1 - ε) := by
  have hu1 : (1 : ℝ) ≤ u := le_of_lt hu
  have hinner : ‖zetaAbelFractKernel x u‖ ≤ u ^ (-1 - ε) :=
    (norm_zetaAbelFractKernel_le u hu1 x).trans (Real.rpow_le_rpow_of_exponent_le hu1 (by linarith))
  have hlognorm : ‖-((Real.log u) : ℂ)‖ = Real.log u := by
    have hnonneg : 0 ≤ Real.log u := le_of_lt (Real.log_pos hu)
    simp [norm_neg, Complex.norm_real, abs_of_nonneg hnonneg]
  calc
    ‖-((Real.log u) : ℂ) * zetaAbelFractKernel x u‖
        = Real.log u * ‖zetaAbelFractKernel x u‖ := by rw [norm_mul, hlognorm]
    _ ≤ Real.log u * u ^ (-1 - ε) := mul_le_mul_of_nonneg_left hinner (le_of_lt (Real.log_pos hu))

private lemma pnt52_ae_on_Ioi_of_all {p : ℝ → Prop} (h : ∀ u ∈ Ioi (1 : ℝ), p u) :
    ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), p u :=
  ae_restrict_iff' measurableSet_Ioi |>.2 (ae_of_all _ fun u hu => h u hu)

private lemma pnt52_dist_lt_of_mem_ball_half {z s : ℂ} {δ : ℝ} (hz : z ∈ Metric.ball s (δ / 2)) (hδ : 0 < δ) :
    dist z s < δ :=
  lt_trans (Metric.mem_ball.mp hz) (half_lt_self hδ)

/-- Dominated differentiation under `∫_{(1,∞)} F z`. -/
lemma hasDerivAt_integral_param_dominated_Ioi
  (F F' : ℂ → ℝ → ℂ) (s : ℂ) (δ : ℝ) (hδ : 0 < δ)
  (hmeas : ∀ᶠ z in 𝓝 s, AEStronglyMeasurable (F z) (volume.restrict (Ioi (1 : ℝ))))
  (hFint : Integrable (F s) (volume.restrict (Ioi (1 : ℝ))))
  (hF'meas : AEStronglyMeasurable (F' s) (volume.restrict (Ioi (1 : ℝ))))
  (bound : ℝ → ℝ) (hbound_int : Integrable bound (volume.restrict (Ioi (1 : ℝ))))
  (hbound : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), ∀ z ∈ Metric.ball s δ, ‖F' z u‖ ≤ bound u)
  (hderiv : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), ∀ z ∈ Metric.ball s δ,
    HasDerivAt (fun w => F w u) (F' z u) z) :
  HasDerivAt (fun z => ∫ u in Ioi (1 : ℝ), F z u) (∫ u in Ioi (1 : ℝ), F' s u) s := by
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Ioi (1 : ℝ))) (F := F) (F' := F') (x₀ := s)
      (s := Metric.ball s δ) (bound := bound) (Metric.ball_mem_nhds s hδ)
      (hF_meas := hmeas) (hF_int := hFint) (hF'_meas := hF'meas)
      (h_bound := hbound) (bound_integrable := hbound_int) (h_diff := hderiv)
  rcases h with ⟨_, hDeriv⟩
  exact hDeriv

/-- `∫_{(1,∞)} K_z` is analytic in `z` for `re z > 0`. -/
theorem integral_analytic (s : ℂ) (hs : 0 < s.re) :
    AnalyticAt ℂ (fun z => ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel z u) s := by
  set ε : ℝ := s.re / 2
  have hεpos : 0 < ε := half_pos hs
  obtain ⟨δ, hδpos, hδprop⟩ :=
    Complex.exists_pos_radius_forall_mem_ball_re_ge (z₀ := s) (a := ε) (half_lt_self hs)
  set F : ℂ → ℝ → ℂ := zetaAbelFractKernel
  set F' : ℂ → ℝ → ℂ := fun z u => -((Real.log u) : ℂ) * F z u
  set bound : ℝ → ℝ := fun u => (2 / ε) * u ^ (-1 - ε / 2)
  have hbound_int : Integrable bound (volume.restrict (Ioi (1 : ℝ))) := by
    simpa [bound, IntegrableOn] using
      (integrableOn_Ioi_rpow_of_lt (by linarith [half_pos hεpos]) one_pos).const_mul (2 / ε)
  have hDiff : ∀ᶠ z in 𝓝 s, DifferentiableAt ℂ (fun z0 => ∫ u in Ioi (1 : ℝ), F z0 u) z := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds s (half_pos hδpos)) ?_
    intro z hz
    set δ' : ℝ := δ / 2
    have hz_lt : dist z s < δ := pnt52_dist_lt_of_mem_ball_half hz hδpos
    have hRe : ∀ y ∈ Metric.ball z δ', ε ≤ y.re := fun y hy =>
      hδprop z y hz_lt (pnt52_dist_lt_of_mem_ball_half hy hδpos)
    have hzRe : ε ≤ z.re := hδprop s z (by simpa [dist_self] using hδpos) hz_lt
    exact (hasDerivAt_integral_param_dominated_Ioi F F' z δ' (half_pos hδpos)
      (eventually_aestronglyMeasurable_param z)
      (by simpa using integrableOn_Ioi z (lt_of_lt_of_le hεpos hzRe))
      (by simpa [F, F'] using aestronglyMeasurable_param_deriv z)
      bound hbound_int
      (pnt52_ae_on_Ioi_of_all fun u hu w hw =>
        (kernel_deriv_norm_bound_on_ball ε u hu w (hRe w hw)).trans
          (by simpa [bound] using Real.log_mul_rpow_neg_le_two_div_mul_rpow_neg hεpos hu))
      (pnt52_ae_on_Ioi_of_all fun u hu w hw => by simpa [F, F'] using hasDerivAt_in_param u hu w)).differentiableAt
  exact (Complex.analyticAt_iff_eventually_differentiableAt
    (f := fun z => ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel z u)).2 hDiff

end ZetaAbelFractKernel

end
end PntFile52


/- SOURCE PrimeNumberTheoremAnd/Mathlib/NumberTheory/AbelSummation.lean -/
section PntFile53
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Finite-sum reindexing for Abel summation

Elementary reindexing lemmas for sums over initial intervals, used when passing between
floor sums and range sums.
-/

section
open Finset
open scoped BigOperators

variable {𝕜 : Type*} [AddCommGroup 𝕜]

/-- Reindex `∑ k ∈ Icc 1 N, f k` as `∑ n ∈ range N, f (n + 1)`. -/
theorem _root_.Finset.sum_Icc_one_eq_sum_range {N : ℕ} (f : ℕ → 𝕜) :
    ∑ k ∈ Icc 1 N, f k = ∑ n ∈ range N, f (n + 1) := by
  symm
  refine sum_bij (s := range N) (t := Icc 1 N)
    (f := fun n => f (n + 1)) (g := fun k => f k)
    (i := fun n _ => n + 1)
    ?hi ?hinj ?hsurj ?hcongr
  · intro n hn
    have hlt : n < N := mem_range.mp hn
    exact mem_Icc.mpr ⟨Nat.succ_le_succ (Nat.zero_le n), Nat.succ_le_of_lt hlt⟩
  · intro a ha b hb h
    exact Nat.succ_injective h
  · intro k hk
    rcases mem_Icc.mp hk with ⟨hk1, hk2⟩
    refine ⟨k - 1, mem_range.mpr ?_, ?_⟩
    · have hsucc : (k - 1) + 1 = k := Nat.sub_add_cancel hk1
      exact lt_of_lt_of_le (Nat.lt_succ_self _) (by simpa [hsucc] using hk2)
    · simp [Nat.sub_add_cancel hk1]
  · intro n hn
    rfl

/-- If `f 0 = 0`, the term at `0` in `Icc 0 N` is redundant. -/
theorem _root_.Finset.sum_Icc_zero_eq_sum_Icc_one {N : ℕ} {f : ℕ → 𝕜} (h0 : f 0 = 0) :
    ∑ k ∈ Icc 0 N, f k = ∑ k ∈ Icc 1 N, f k := by
  have hdecomp : insert 0 (Icc 1 N) = Icc 0 N := by
    simpa [Nat.succ_eq_add_one] using
      insert_Icc_succ_left_eq_Icc (a := 0) (b := N) (h := Nat.zero_le N)
  have hnotmem : (0 : ℕ) ∉ Icc 1 N := by
    intro h
    exact (not_le.mpr (Nat.lt_succ_self 0)) (mem_Icc.mp h).1
  calc
    ∑ k ∈ Icc 0 N, f k = ∑ k ∈ insert 0 (Icc 1 N), f k := by simp [hdecomp]
    _ = f 0 + ∑ k ∈ Icc 1 N, f k := by simp
    _ = ∑ k ∈ Icc 1 N, f k := by simp [h0]

/-- If `f 0 = 0`, summing over `Icc 0 m` equals summing `f (n + 1)` over `range m`. -/
theorem _root_.Finset.sum_Icc_zero_eq_sum_range_succ {m : ℕ} {f : ℕ → 𝕜} (h0 : f 0 = 0) :
    ∑ k ∈ Icc 0 m, f k = ∑ n ∈ range m, f (n + 1) := by
  rw [sum_Icc_zero_eq_sum_Icc_one h0, sum_Icc_one_eq_sum_range]

/-- Floor-summation reindexing for sequences with `c 0 = 0`. -/
theorem _root_.sum_Icc_zero_floor_eq_sum_range {c : ℕ → 𝕜} (hc0 : c 0 = 0) (t : ℝ) :
    ∑ k ∈ Icc 0 ⌊t⌋₊, c k = ∑ n ∈ range ⌊t⌋₊, c (n + 1) :=
  Finset.sum_Icc_zero_eq_sum_range_succ (m := ⌊t⌋₊) (f := c) hc0

end
end PntFile53


/- SOURCE PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/RiemannZetaPartialSum.lean -/
section PntFile54
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Abel-summation partial sums for the Riemann zeta function

For `re s > 1`, the partial Dirichlet sum `∑_{n<N} (n+1)^{-s}` satisfies the classical
Abel tail identity in `ZetaPartialSum.abel_formula`, and converges to `riemannZeta s`.

Used in `RiemannZetaAbelContinuation` to match the Abel integral formula for `re s > 1`.
-/

section
open scoped BigOperators Topology
open Real Set Filter Topology MeasureTheory Complex Nat ZetaAbelFractKernel

/-- Partial sum of the Dirichlet series defining `ζ` for `re s > 1`. -/
noncomputable def zetaPartialSum (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, (n + 1 : ℂ) ^ (-s)

namespace ZetaPartialSum

private lemma pnt54_natCast_floor_eq_sub_fract (u : ℝ) (hu : 0 ≤ u) :
    (Nat.floor u : ℂ) = (u : ℂ) - ((Int.fract u : ℝ) : ℂ) := by
  have hfloorR : (Nat.floor u : ℝ) = (Int.floor u : ℝ) := by
    simpa using natCast_floor_eq_intCast_floor (R := ℝ) (a := u) hu
  have hfloorC : (Nat.floor u : ℂ) = ((Int.floor u : ℝ) : ℂ) := congrArg (fun x : ℝ => (x : ℂ)) hfloorR
  have hIFR : (Int.floor u : ℝ) = u - Int.fract u := (eq_sub_iff_add_eq).2 (Int.floor_add_fract u)
  have hIFC : ((Int.floor u : ℝ) : ℂ) = ((u - Int.fract u : ℝ) : ℂ) := congrArg (fun x : ℝ => (x : ℂ)) hIFR
  exact hfloorC.trans (by simpa [sub_eq_add_neg] using hIFC)

private lemma pnt54_intervalIntegrable_mul_cpow_id (s : ℂ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) volume a b := by
  have hcont : ContinuousOn (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) (Icc a b) :=
    Complex.continuous_ofReal.continuousOn.mul
      (Complex.continuousOn_ofReal_cpow (r := -s - 1) (ha := one_pos.trans_le ha))
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := volume) (a := a) (b := b)
    (f := fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) hab).2
    (hcont.integrableOn_compact isCompact_Icc)

private lemma pnt54_abel_summation (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) * (N : ℂ) ^ (-s)
        - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
  set f : ℝ → ℂ := fun u => (u : ℂ) ^ (-s)
  let c : ℕ → ℂ := fun k => if k = 0 then 0 else (1 : ℂ)
  have hle : (1 : ℝ) ≤ N := mod_cast hN
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) N, DifferentiableAt ℝ f t := fun t ht => by
    by_cases hs : s = 0; · simp [f, hs]
    simpa [f] using (hasDerivAt_ofReal_cpow_const (lt_of_lt_of_le zero_lt_one ht.1).ne'
      (neg_ne_zero.mpr hs)).differentiableAt
  have hint : IntegrableOn (deriv f) (Set.Icc (1 : ℝ) (N : ℝ)) :=
    (Complex.continuousOn_deriv_ofReal_cpow_neg (s := s) (a := (1 : ℝ)) (b := (N : ℝ)) zero_lt_one).integrableOn_compact
      isCompact_Icc
  have habel :=
    sum_mul_eq_sub_integral_mul₀' (c := c) (f := f) (m := N)
      (hc := by simp [c]) (hf_diff := hdiff) (hf_int := hint)
  have hLHS : (∑ k ∈ Finset.Icc 0 N, f k * c k) = zetaPartialSum s N := by
    rw [Finset.sum_Icc_zero_eq_sum_range_succ (by simp [c])]
    simp [zetaPartialSum, f, c]
  have hInt_congr :
      (∫ u in (1 : ℝ)..N, deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k)
        = ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
    apply intervalIntegral.integral_congr_Ioc_of_le hle
    intro u hu
    rw [sum_Icc_zero_floor_eq_sum_range (hc0 := by simp [c]) u, Complex.deriv_ofReal_cpow_neg s (lt_trans zero_lt_one hu.1)]
    simp [c, Finset.sum_const, Finset.card_range, mul_comm, mul_left_comm]
  calc
    zetaPartialSum s N
        = f N * (∑ k ∈ Finset.Icc 0 N, c k)
            - ∫ u in (1 : ℝ)..N, deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k := by
          simpa [hLHS] using habel.trans (by rw [← intervalIntegral.integral_of_le hle])
    _ = f N * (∑ k ∈ Finset.Icc 0 N, c k)
            - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
          rw [hInt_congr]
    _ = (N : ℂ) * (N : ℂ) ^ (-s)
            - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
          have hMain : f N * (∑ k ∈ Finset.Icc 0 N, c k) = (N : ℂ) * f N := by
            rw [Finset.sum_Icc_zero_eq_sum_range_succ (by simp [c])]
            simp [c, f, Finset.sum_const, Finset.card_range, mul_comm]
          rw [hMain]; simp [f]

private lemma pnt54_abel_split (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N = (N : ℂ) ^ (1 - s) + s * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1) := by
  rw [pnt54_abel_summation s N hN]
  have hInt :
      ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1))
        = (-s) * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1) := by
    rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_congr_Ioc_of_le (mod_cast hN)]
    intro u _; simp [neg_mul, mul_left_comm]
  rw [hInt, sub_eq_add_neg, neg_mul, neg_neg]
  simp [Complex.natCast_mul_cpow_neg_eq_cpow_one_sub N s (Nat.ne_of_gt (Nat.succ_le_iff.mp hN))]

private lemma pnt54_integral_split_fract (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1)
      = (∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s))
        - ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u := by
  have hab : (1 : ℝ) ≤ N := mod_cast hN
  have hI1 := pnt54_intervalIntegrable_mul_cpow_id s le_rfl hab
  have hI2 := ZetaAbelFractKernel.intervalIntegrable s le_rfl hab
  calc
    ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1)
        = ∫ u in (1 : ℝ)..N, ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1) := by
          apply intervalIntegral.integral_congr_Ioc_of_le hab
          intro u hu
          simp [pnt54_natCast_floor_eq_sub_fract u (le_trans zero_le_one (le_of_lt hu.1)), sub_eq_add_neg]
    _ = (∫ u in (1 : ℝ)..N, (u : ℂ) * (u : ℂ) ^ (-s - 1))
          - ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u := by
          rw [← intervalIntegral.integral_sub hI1 hI2]
          apply intervalIntegral.integral_congr_Ioc_of_le hab
          intro u _; simp [sub_mul, zetaAbelFractKernel]
    _ = (∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s))
          - ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u := by
          congr 1
          apply intervalIntegral.integral_congr_Ioc_of_le hab
          intro u hu
          exact Complex.ofReal_cpow_mul_cpow_neg_sub_one (s := s) (hu := lt_trans zero_lt_one hu.1)

private lemma pnt54_cpow_integral (s : ℂ) (hs : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s) = s / (1 - s) * ((N : ℂ) ^ (1 - s) - 1) := by
  have h01leN : (1 : ℝ) ≤ (N : ℝ) := mod_cast hN
  have hint : ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s)
      = ((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1) := by
    have hrne : -s ≠ (-1 : ℂ) := fun h => hs (neg_inj.mp h)
    simpa using integral_cpow (a := (1 : ℝ)) (b := (N : ℝ)) (r := -s)
      (Or.inr ⟨hrne, by simp [uIcc_of_le h01leN]⟩)
  calc s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s)
      = s * (((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1)) := by
        simpa using congrArg (s * ·) hint
      _ = s * (((N : ℂ) ^ (1 - s) - 1) / (1 - s)) := by
        rw [one_cpow, show (1 : ℂ) - s = -s + 1 from by ring]
      _ = s / (1 - s) * ((N : ℂ) ^ (1 - s) - 1) := by field_simp

private lemma pnt54_abel_sub_fract (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) ^ (1 - s)
        + (s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s))
        - (s * ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u) := by
  rw [pnt54_abel_split s N hN, pnt54_integral_split_fract s N hN, mul_sub, add_sub_assoc]

/-- Abel tail formula for `re s > 1`. -/
theorem abel_formula (s : ℂ) (hs : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) ^ (1 - s) / (1 - s) + 1 + 1 / (s - 1)
        - s * ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u := by
  have hstep := pnt54_abel_sub_fract s N hN
  rw [pnt54_cpow_integral s hs N hN] at hstep
  let A := (N : ℂ) ^ (1 - s)
  have halg : A + s / (1 - s) * (A - 1) = A / (1 - s) + 1 + 1 / (s - 1) := by
    field_simp [sub_ne_zero.mpr hs, sub_ne_zero.mpr hs.symm]; ring
  rwa [halg] at hstep

lemma tendsto_natCast_cpow_zero_of_neg_re (w : ℂ) (hw : w.re < 0) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ w) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : (fun N : ℕ => (N : ℝ) ^ w.re) =ᶠ[atTop] fun N : ℕ => ‖(N : ℂ) ^ w‖ := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [Complex.norm_natCast_cpow_of_pos hN w]
  rw [tendsto_congr' (EventuallyEq.symm h1)]
  rw [show w.re = -(-w.re) from by ring]
  exact (tendsto_rpow_neg_atTop (neg_pos.mpr hw)).comp tendsto_natCast_atTop_atTop

/-- `zetaPartialSum` converges to `riemannZeta` for `re s > 1`. -/
theorem tendsto_riemannZeta (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => zetaPartialSum s N) atTop (𝓝 (riemannZeta s)) := by
  set g : ℕ → ℂ := fun n => if n = 0 then 0 else (n : ℂ) ^ (-s)
  set h : ℕ → ℂ := fun n => (n + 1 : ℂ) ^ (-s)
  have hsne : s ≠ 0 := by
    intro h0
    have : (0 : ℝ) < s.re := lt_trans (show (0 : ℝ) < 1 by norm_num) hs
    simpa [h0] using ne_of_gt this
  have hgSumm : Summable g := by
    simpa [g, one_div_natCast_cpow_eq_ite_cpow_neg s hsne] using
      (Complex.summable_one_div_nat_cpow (p := s)).2 hs
  have hhSumm : Summable h := by
    have : Summable (fun n => g (n + 1)) := (summable_nat_add_iff (f := g) (k := 1)).2 hgSumm
    simpa [Function.comp_apply, h, g] using this
  have hg0 : g 0 = 0 := by simp [g]
  have h_tsum_eq : (∑' n, h n) = ∑' n, g n := by
    have : (∑' n, g n) = ∑' n, g (n + 1) := by simpa [hg0, add_comm] using Summable.tsum_eq_zero_add hgSumm
    simpa [h, g] using this.symm
  have hzeta : riemannZeta s = ∑' n, g n := by
    simpa [g, one_div_natCast_cpow_eq_ite_cpow_neg s hsne] using
      zeta_eq_tsum_one_div_nat_cpow (s := s) hs
  simpa [zetaPartialSum, h, h_tsum_eq.trans hzeta.symm] using Summable.tendsto_sum_tsum_nat hhSumm

end ZetaPartialSum

end
end PntFile54


/- SOURCE PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/RiemannZetaAbelContinuation.lean -/
section PntFile55
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Abel-summation continuation of the Riemann zeta function

For `s ≠ 1` in the half-plane `{re s > σ₀}` with `σ₀ = 1/10`, the Riemann zeta function equals the
Abel-summation tail formula from [`Mathlib.NumberTheory.AbelSummation`]: writing `{u}` for the
fractional part of `u > 0` and `K_s(u) = {u} · u^{-s-1}`, one has

`ζ(s) = 1 + (s - 1)⁻¹ - s ∫_{(1,∞)} K_s(u) du`.

The threshold `σ₀`, the domain, the kernel, and the renormalized integral are bundled in
`zetaAbelContinuationReLower`, `zetaAbelContinuationDomain`, `zetaAbelFractKernel`, and
`zetaAbelContinuationFormula`. The equality with `riemannZeta` on that domain is proved by analytic
continuation from `re s > 1`, where the formula is the classical Abel partial-sum limit.

Kernel and partial-sum input live in `RiemannZetaAbelKernel` and `RiemannZetaPartialSum`.

## Main results

* `zetaAbelContinuationDomain`, `zetaAbelContinuationFormula`
* `riemannZeta_eq_zetaAbelContinuationFormula`
* `norm_zetaAbelContinuationFormula_le`, `analyticOn_zetaAbelContinuationFormula`
-/

section
open scoped Topology
open Real Set Filter Topology MeasureTheory Complex ZetaPartialSum ZetaAbelFractKernel

/-- Lower threshold on `re s` for the Abel integral continuation of `ζ`. -/
noncomputable def zetaAbelContinuationReLower : ℝ := 1 / 10

theorem zetaAbelContinuationReLower_pos : 0 < zetaAbelContinuationReLower := by
  change 0 < (1 / 10 : ℝ)
  norm_num

theorem one_lt_zetaAbelContinuationReLower : zetaAbelContinuationReLower < (1 : ℝ) := by
  change (1 / 10 : ℝ) < 1
  norm_num


/-- Domain `{s : ℂ | s ≠ 1 ∧ re s > 1/10}` where the Abel continuation of `ζ` is proved. -/
def zetaAbelContinuationDomain : Set ℂ :=
  {s | s ≠ (1 : ℂ) ∧ zetaAbelContinuationReLower < s.re}

theorem isOpen_zetaAbelContinuationDomain : IsOpen zetaAbelContinuationDomain := by
  change IsOpen ({s : ℂ | s ≠ 1} ∩ {s : ℂ | zetaAbelContinuationReLower < s.re})
  exact isOpen_compl_singleton.inter (isOpen_lt continuous_const Complex.continuous_re)

theorem isPreconnected_zetaAbelContinuationDomain : IsPreconnected zetaAbelContinuationDomain := by
  convert (Complex.isPathConnected_halfSpace_re_gt_diff_singleton
      (a := zetaAbelContinuationReLower) (p := (1 : ℂ)) one_lt_zetaAbelContinuationReLower).isConnected.isPreconnected using 1
  ext z; simp [zetaAbelContinuationDomain, and_comm]

theorem two_mem_zetaAbelContinuationDomain : (2 : ℂ) ∈ zetaAbelContinuationDomain := by
  refine ⟨by norm_num, ?_⟩
  change (1 / 10 : ℝ) < (2 : ℂ).re
  norm_num


/-- Abel renormalization `1 + (s-1)⁻¹ - s ∫_{(1,∞)} K_s`. -/
noncomputable def zetaAbelContinuationFormula (s : ℂ) : ℂ :=
  1 + 1 / (s - 1) - s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u

theorem riemannZeta_abel_integral (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s = zetaAbelContinuationFormula s := by
  have hsne : s ≠ 1 := by
    intro h
    have hre : s.re = 1 := by simp [h]
    linarith
  set G : ℕ → ℂ := fun N =>
    (N : ℂ) ^ (1 - s) / (1 - s) + 1 + 1 / (s - 1)
      - s * ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u
  have hEv : ∀ᶠ N in atTop, zetaPartialSum s N = G N :=
    (eventually_ge_atTop 1).mono fun N hN => (abel_formula s hsne N hN).trans rfl
  have hG_to_zeta := (tendsto_congr' hEv).mp (tendsto_riemannZeta s hs)
  have hA : Tendsto (fun N : ℕ => (N : ℂ) ^ (1 - s) / (1 - s)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (Tendsto.const_mul (1 / (1 - s))
        (tendsto_natCast_cpow_zero_of_neg_re (1 - s)
          (by rw [Complex.sub_re, Complex.one_re]; linarith)))
  have hK : Tendsto (fun _ : ℕ => (1 + 1 / (s - 1) : ℂ)) atTop
      (𝓝 (1 + 1 / (s - 1))) := tendsto_const_nhds
  have hIntMul := (tendsto_integral_Ioi s hs).const_mul s
  set Aseq : ℕ → ℂ := fun N => (N : ℂ) ^ (1 - s) / (1 - s)
  set Kseq : ℕ → ℂ := fun _ => (1 + 1 / (s - 1) : ℂ)
  set Iseq : ℕ → ℂ := fun N => s * ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u
  have hSum : Tendsto (fun N => Aseq N + Kseq N) atTop (𝓝 (1 + 1 / (s - 1))) := by
    simpa using! ((continuous_fst.add continuous_snd).tendsto _).comp (hA.prodMk_nhds hK)
  have hG_limit : Tendsto G atTop
      (𝓝 ((1 + 1 / (s - 1)) - s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u)) := by
    have hSub : Tendsto (fun N => Aseq N + Kseq N - Iseq N) atTop
        (𝓝 ((1 + 1 / (s - 1)) - s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u)) := by
      simpa [Function.comp_apply, Function.comp_def, sub_eq_add_neg] using
        ((continuous_fst.add continuous_snd).tendsto _).comp (hSum.prodMk_nhds hIntMul.neg)
    have hGdef : (fun N => Aseq N + Kseq N - Iseq N) = G := by
      funext N
      simp [Aseq, Kseq, Iseq, G, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
    simpa [hGdef] using hSub
  have huniq := tendsto_nhds_unique hG_to_zeta hG_limit
  simpa [zetaAbelContinuationFormula, sub_eq_add_neg] using huniq


/-- The Abel continuation formula is analytic on `zetaAbelContinuationDomain`. -/
theorem analyticOn_zetaAbelContinuationFormula :
    AnalyticOn ℂ zetaAbelContinuationFormula zetaAbelContinuationDomain := by
  simp only [AnalyticOn, zetaAbelContinuationDomain, Set.mem_ofPred_eq]
  intro s ⟨hs_ne, hs_re⟩
  apply AnalyticAt.analyticWithinAt
  refine analyticAt_const.add (analyticAt_const.div (analyticAt_id.sub analyticAt_const) ?_) |>.sub
    (analyticAt_id.mul (integral_analytic s (lt_trans zetaAbelContinuationReLower_pos hs_re)))
  exact sub_ne_zero.mpr hs_ne

/-- The Abel integral formula agrees with `ζ` on `zetaAbelContinuationDomain`. -/
theorem riemannZeta_eq_zetaAbelContinuationFormula (s : ℂ) (hs : s ∈ zetaAbelContinuationDomain) :
    riemannZeta s = zetaAbelContinuationFormula s := by
  have hUo := isOpen_zetaAbelContinuationDomain
  have hζ : AnalyticOnNhd ℂ riemannZeta zetaAbelContinuationDomain := by
    rw [← hUo.analyticOn_iff_analyticOnNhd]
    have h : AnalyticOn ℂ riemannZeta ({1} : Set ℂ)ᶜ :=
      isOpen_compl_singleton.analyticOn_iff_analyticOnNhd.mpr analyticOn_riemannZeta
    exact AnalyticOn.mono h fun _ hz => hz.1
  have hF : AnalyticOnNhd ℂ zetaAbelContinuationFormula zetaAbelContinuationDomain := by
    rw [← hUo.analyticOn_iff_analyticOnNhd]
    exact analyticOn_zetaAbelContinuationFormula
  have hEq : riemannZeta =ᶠ[𝓝 (2 : ℂ)] zetaAbelContinuationFormula := by
    have hopen : IsOpen {w : ℂ | 1 < w.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with w hw
      using riemannZeta_abel_integral w hw
  exact (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    hζ hF isPreconnected_zetaAbelContinuationDomain two_mem_zetaAbelContinuationDomain hEq) hs

end
end PntFile55


/- SOURCE PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/RiemannZetaConvexity.lean -/
section PntFile56
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Bounds for the Riemann zeta function

Strip bounds for `riemannZeta`, used in `ZetaFiniteOrder`. Euler-product input is in
`PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZeta`.

## Main results

* `norm_riemannZeta_le`, `norm_riemannZeta_shift_le` : strip bounds for the Λ₀ pipeline
* `norm_riemannZeta_ratio_le_on_verticalLine`, `norm_riemannZeta_ratio_le_on_vertical_line` :
  convexity input on vertical lines
* `norm_riemannZeta_lt_linear_im_on_strip` : linear bound in the strip `1/2 ≤ re < 3`
-/

section
open scoped BigOperators Topology
open Real Set Filter Topology MeasureTheory Complex

/-!
### Vertical-line ratio bound
-/


/-!
### Abel strip bounds
-/


namespace StripBounds


end StripBounds

open StripBounds


end
end PntFile56


/- SOURCE PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/RiemannZetaStripBound.lean -/
section PntFile57
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Strip bounds for the Riemann zeta function

Summary of strip bounds on `riemannZeta` used in `ZetaFiniteOrder` (finite order of
`completedRiemannZeta₀`). Proofs are in `RiemannZetaConvexity` and
`RiemannZetaAbelContinuation`.

## Main results

* `norm_riemannZeta_le`, `norm_zetaAbelContinuationFormula_le` :
  strip bounds on `zetaAbelContinuationDomain`
* `zetaAbelContinuationDomain`, `riemannZeta_eq_zetaAbelContinuationFormula` : Abel continuation API
* `norm_riemannZeta_shift_le` : linear bound for `ζ (s + 3/2 + it)` with `‖s‖ ≤ 1`
* `norm_riemannZeta_ratio_le_on_verticalLine`, `norm_riemannZeta_ratio_le_on_vertical_line` :
  vertical-line lower bounds via Euler products (see also `RiemannZeta`)
-/


end PntFile57


/- SOURCE PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/ZetaFiniteOrder.lean -/
section PntFile58
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Analytic continuation and finite order for the Riemann zeta function

This file gives growth bounds for `completedRiemannZeta₀` (Λ₀) and the removable
extension of `(s - 1)ζ(s)`.

Note: Mathlib distinguishes between:
- `completedRiemannZeta₀` : the entire function Λ₀(s)
- `completedRiemannZeta` : Λ(s) = Λ₀(s) - 1/s - 1/(1-s), which has simple poles at 0 and 1

The key ingredients are:
* Mathlib's `differentiable_completedZeta₀` for entirety of Λ₀
* The functional equation `completedRiemannZeta₀_one_sub`
* Stirling-type bounds for `Complex.Gammaℝ`
* `norm_riemannZeta_le` from `RiemannZetaStripBound` for strip bounds on `ζ`

## Main results

* `completedRiemannZeta₀_order_one` : growth bound implying order at most one for
  `completedRiemannZeta₀`
* `completedRiemannZeta₀_entireOfOrderAtMost_one` (in `RiemannZetaHadamard`) : packaged as
  `Complex.Hadamard.EntireOfOrderAtMost`
* `zeta_minus_pole_entire_growth` : a coarse global bound for the removable extension of
  `(s - 1)ζ(s)`.

## References

* [tao246bComplexAnalysis], Theorem 22 and Exercise 23, for the order-one growth input used in
  the finite-order Hadamard strategy for completed zeta functions
* [titchmarsh1986] and [edwards1974] for the classical completed-zeta and ξ-function growth
  background; the formalized object here is the additive pole-removal `Λ₀`, not Riemann's `ξ`

## Tags

Riemann zeta function, completed zeta function, finite order, Hadamard factorization
-/

section
open Complex Set Filter Topology Metric
open scoped Real

namespace Complex

/-! ### Finite order of the completed zeta function -/


/-- The removable extension of `(s - 1)ζ(s)`.

The value at `1` is set to the residue of `ζ` at its simple pole; away from `1` this is the
ordinary product `(s - 1)ζ(s)`. -/
noncomputable def zetaTimesSMinusOne_entire (s : ℂ) : ℂ :=
  Function.update (fun s : ℂ => (s - 1) * riemannZeta s) 1 1 s


end Complex

end
end PntFile58


/- SOURCE PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/RiemannZetaValues.lean -/
section PntFile59
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
## Special values of the completed Riemann zeta function

This file records elementary special values used by applications of the completed zeta function,
including the value at `2` and the functional-equation relation `Λ₀(0) = Λ₀(1)`.  The explicit
Euler-Mascheroni formula for `Λ₀(1)` is in `Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean`.

## References

* [titchmarsh1986] and [edwards1974] for completed-zeta special values and the functional equation
-/

section
open Complex Set

open scoped BigOperators


end
end PntFile59


/- SOURCE PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/RiemannZetaHadamard.lean -/
section PntFile60
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-!
# Hadamard factorization for the completed Riemann zeta function

This file specializes Tao's finite-order Hadamard factorization theorem
([tao246bComplexAnalysis], Thm. 22)
to the entire completed zeta function `completedRiemannZeta₀` (Λ₀) and to Riemann's entire
`riemannXi`. The analytic input is the order-one bound `completedRiemannZeta₀_order_one` from
`ZetaFiniteOrder`; the product is the divisor-indexed canonical Weierstrass product at genus
`⌊ρ⌋ = 1`, with multiplicities from `MeromorphicOn.divisor`.

Note: `completedRiemannZeta` (Λ with simple poles at `0` and `1`) is a different object; Hadamard
applies to Λ₀.  The negative even integers are the trivial zeros of `riemannZeta`, not zeros of
Λ₀.  Accordingly, the divisor indices in this file remain generic zeros of Λ₀ rather than a
separate enumeration of the trivial zeros of ζ.

`RiemannZetaValues` proves `completedRiemannZeta₀_zero_ne_zero`, using the Euler-Mascheroni
formula for `Λ₀(1)` together with explicit numerical bounds.  Therefore the origin monomial in the
Λ₀ Hadamard product is also removable.

## Main results

* `completedRiemannZeta₀_entireOfOrderAtMost_one` : Λ₀ has order at most one
* `riemannXi_entireOfOrderAtMost_one` : Riemann's entire `ξ` has order at most one
* `analyticOrderNatAt_riemannXi_zero` : the origin monomial in `ξ`'s Hadamard product is absent
* `analyticOrderNatAt_completedRiemannZeta₀_zero` : the origin monomial in Λ₀'s Hadamard product
  is absent
* `completedRiemannZeta₀_hadamard_factorization` : canonical product form over divisor indices
* `completedRiemannZeta₀_hadamard_factorization_no_monomial` : Λ₀ product with the origin monomial
  removed
* `riemannXi_hadamard_factorization` : canonical product form for Riemann's entire `ξ`
* `riemannXi_hadamard_factorization_no_monomial`, `_reindex_no_monomial`,
  `_sequence_no_monomial` : xi products with the origin monomial removed
* `summable_riemannXi_divisorZeroIndex₀_norm_inv_sq` : genus-one summability of xi's nonzero
  zero divisor
* `logDeriv_riemannXi_divisorCanonicalProduct_one_eq_tsum` and
  `logDeriv_riemannXi_eq_polynomial_derivative_add_tsum` : xi-specialized zero-sum identities
* `riemannXi_hadamard_polynomial_derivative_eval_zero_eq` and
  `existsUnique_riemannXi_hadamard_polynomial_derivative_eval_zero` : theorem-level uniqueness
  of the xi Hadamard derivative constant
* `exists_riemannXi_logDeriv_eq_polynomial_derivative_add_tsum` : logarithmic derivative formula
  obtained from the xi no-monomial factorization
* `completedRiemannZeta₀_hadamard_factorization_reindex`, `_sequence` : reindexed enumerations

The order-one estimate from `ZetaFiniteOrder` is the finite-order input to
`hadamard_factorization_of_order`.

## References

* [tao246bComplexAnalysis], Theorem 22 for the finite-order Hadamard factorization strategy
* [titchmarsh1986] and [edwards1974] for the classical completed-zeta and ξ-function background
* [boas1954] and [levin1980] for the general finite-order Hadamard product theorem
* [kadiri2005] for the explicit zero-free-region use of the xi logarithmic derivative

## Tags

Riemann zeta function, Hadamard factorization, canonical product, entire function of finite order
-/

section
noncomputable section

open Complex Set

open scoped BigOperators


/-! ### Logarithmic-derivative identities -/


end
end
end PntFile60


namespace XiCenteredPort
open Complex Set MeasureTheory
open scoped BigOperators


noncomputable def centered (z : ℂ) : ℂ := riemannXi (z+1/2)


end XiCenteredPort

namespace XiCenteredPort
open Complex Set
open Complex.Hadamard
open scoped BigOperators


end XiCenteredPort

section ProjectXiGeometry


set_option maxRecDepth 4000

open scoped BigOperators
open Filter Topology

namespace EtaQBridge

-- This definition includes the removable values at s = 0 and s = 1.
noncomputable def xi (s : ℂ) : ℂ :=
  (1 + s * (s-1) * completedRiemannZeta₀ s) / 2


theorem xi_functional_equation (s : ℂ) : xi (1-s) = xi s := by
  simp only [xi, completedRiemannZeta₀_one_sub]
  ring


theorem xi_eq_completed (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xi s = s * (s-1) * completedRiemannZeta s / 2 := by
  rw [completedRiemannZeta_eq]
  unfold xi
  have h : 1-s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp
  <;> ring

theorem xi_eq_zeta (s : ℂ) (hr : 0 < s.re) (h1 : s ≠ 1) :
    xi s = s * (s-1) * Complex.Gammaℝ s * riemannZeta s / 2 := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hr
  rw [xi_eq_completed s h0 h1, riemannZeta_def_of_ne_zero h0]
  have hg := Complex.Gammaℝ_ne_zero_of_re_pos hr
  field_simp


end EtaQBridge

namespace XiZeroGeometry
open EtaQBridge Set


theorem xi_one_value : xi 1 = 1/2 := by simp [xi]

theorem xi_ne_zero_right (s : ℂ) (hs : 1 ≤ s.re) : xi s ≠ 0 := by
  by_cases h1 : s = 1
  · rw [h1, xi_one_value]; norm_num
  have hr : 0 < s.re := by linarith
  have h0 : s ≠ 0 := by intro h; simp [h] at hr
  rw [xi_eq_zeta s hr h1]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h0
    (sub_ne_zero.mpr h1)) (Complex.Gammaℝ_ne_zero_of_re_pos hr))
    (riemannZeta_ne_zero_of_one_le_re hs)) (by norm_num)

theorem xi_ne_zero_left (s : ℂ) (hs : s.re ≤ 0) : xi s ≠ 0 := by
  rw [← xi_functional_equation s]
  apply xi_ne_zero_right
  simp only [Complex.sub_re, Complex.one_re]
  linarith


end XiZeroGeometry


end ProjectXiGeometry
namespace XiRealPort
open Complex Set MeasureTheory

lemma xi_agrees (s : ℂ) : Complex.riemannXi s = EtaQBridge.xi s := by
  unfold Complex.riemannXi EtaQBridge.xi
  ring

theorem zeta_real_re_neg {s : ℝ} (hs : 1/2 ≤ s) (hs1 : s < 1) :
    (riemannZeta (s : ℂ)).re < 0 := by
  have hs0 : 0 < s := by linarith
  have hInt := ZetaAbelFractKernel.integrableOn_Ioi (s : ℂ) (by simpa using hs0)
  have hnonneg : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))),
      0 ≤ (zetaAbelFractKernel (s : ℂ) u).re := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := le_trans zero_le_one (le_of_lt hu)
    have hp : (u : ℂ)^(-(s : ℂ)-1) = ((u^(-s-1) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hu0]
      simp
    rw [zetaAbelFractKernel, hp]
    simpa using mul_nonneg (Int.fract_nonneg u) (Real.rpow_nonneg hu0 _)
  have hi : 0 ≤ (∫ u in Ioi (1 : ℝ), zetaAbelFractKernel (s : ℂ) u).re := by
    have heq : (∫ u in Ioi (1 : ℝ), (zetaAbelFractKernel (s : ℂ) u).re) =
        (∫ u in Ioi (1 : ℝ), zetaAbelFractKernel (s : ℂ) u).re := integral_re hInt
    rw [← heq]
    exact integral_nonneg_of_ae hnonneg
  have hdom : (s : ℂ) ∈ zetaAbelContinuationDomain := by
    constructor
    · intro h
      have : s = 1 := by exact_mod_cast h
      linarith
    · change (1/10 : ℝ) < s
      linarith
  have hfrac : (1 : ℂ)/((s : ℂ)-1) = ((1/(s-1) : ℝ) : ℂ) := by push_cast; rfl
  have h := congrArg Complex.re (riemannZeta_eq_zetaAbelContinuationFormula (s : ℂ) hdom)
  simp only [zetaAbelContinuationFormula, hfrac, Complex.sub_re, Complex.add_re,
    Complex.one_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  have hbase : 1+1/(s-1) < 0 := by
    have heq : 1+1/(s-1) = s/(s-1) := by
      field_simp [sub_ne_zero.mpr (ne_of_lt hs1)]
      ring
    rw [heq]
    exact div_neg_of_pos_of_neg hs0 (sub_neg.mpr hs1)
  have hprod := mul_nonneg hs0.le hi
  linarith

theorem xi_real_ne_half_to_one {s : ℝ} (hs : 1/2 ≤ s) (hs1 : s < 1) :
    Complex.riemannXi (s : ℂ) ≠ 0 := by
  have hs0 : 0 < s := by linarith
  have hc0 : (s : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hs0)
  have hc1 : (s : ℂ) ≠ 1 := by exact_mod_cast (ne_of_lt hs1)
  have hz : riemannZeta (s : ℂ) ≠ 0 := by
    intro h
    have := zeta_real_re_neg hs hs1
    rw [h] at this
    norm_num at this
  have hΛ : completedRiemannZeta (s : ℂ) ≠ 0 := by
    intro h
    apply hz
    rw [riemannZeta_def_of_ne_zero hc0, h, zero_div]
  rw [riemannXi_eq_mul_completedRiemannZeta hc0 hc1]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hc0 (sub_ne_zero.mpr hc1)) hΛ) (by norm_num)

theorem xi_real_ne_zero (s : ℝ) : Complex.riemannXi (s : ℂ) ≠ 0 := by
  by_cases h1 : 1 ≤ s
  · rw [xi_agrees]
    exact XiZeroGeometry.xi_ne_zero_right (s : ℂ) (by simpa using h1)
  by_cases h0 : s ≤ 0
  · rw [xi_agrees]
    exact XiZeroGeometry.xi_ne_zero_left (s : ℂ) (by simpa using h0)
  by_cases hh : 1/2 ≤ s
  · exact xi_real_ne_half_to_one hh (lt_of_not_ge h1)
  have hf := xi_real_ne_half_to_one (s := 1-s) (by linarith) (by linarith)
  simpa only [Complex.ofReal_sub, Complex.ofReal_one, Complex.riemannXi_one_sub] using hf

end XiRealPort

open scoped BigOperators


open scoped BigOperators


open scoped BigOperators
theorem solution (s : ℝ) :
    (1+(s : ℂ)*((s : ℂ)-1)*completedRiemannZeta₀ (s : ℂ))/2 ≠ 0 := by
  change EtaQBridge.xi (s : ℂ) ≠ 0
  rw [← XiRealPort.xi_agrees]
  exact XiRealPort.xi_real_ne_zero s

