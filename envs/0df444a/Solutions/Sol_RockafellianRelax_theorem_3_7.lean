-- Prove2me | solution 1 for RockafellianRelax.theorem_3_7
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T09:40:31.640775+00:00
-- url     : https://prove2.me/submissions/6efa74ec-0846-45c5-b4f6-331b5503dde8

import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Bases
import Theorems.Thm_RockafellianRelax_tilt_epiConverges
import Theorems.Thm_RockafellianRelax_eq_A2_clusterPt_mem_argmin
import Theorems.Thm_RockafellianRelax_proposition_3_3_c
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_RockafellianRelax_IsExact
import Definitions.Def_RockafellianRelax_IsStrictlyLimitExact
import Definitions.Def_RockafellianRelax_argmin
import Definitions.Def_RockafellianRelax_tilt
import Definitions.Def_PerspEpi_SeqEpiConv

open Filter Topology RockafellianRelax


/-- **Theorem 3.7 (convergence under limiting exactness).** Royset, Chen & Eckstrand,
arXiv:2204.04762v4, Theorem 3.7, p.9: "For the problem (3.1) of minimizing φ : ℝⁿ → R̄, suppose
that dom φ ≠ ∅ and that {fν : ℝᵐ × ℝⁿ → R̄, ν ∈ ℕ} are strictly limit-exact Rockafellians, supported
by ȳ ∈ ℝᵐ. Let yν → ȳ, εν ↘ 0, and (uν, xν) ∈ εν-argmin_{u,x} {fν(u, x) − ⟨yν, u⟩}. Then, every
cluster point (û, x̂) of {(uν, xν), ν ∈ ℕ} satisfies x̂ ∈ argmin_x φ(x). If strict limiting
exactness is replaced by limiting exactness, then (û, x̂) satisfies the necessary optimality
condition (3.5) with f : ℝᵐ × ℝⁿ → R̄ being furnished by the limit of {fν, ν ∈ ℕ}."

Conclusion (1): under strict limiting exactness, `û = 0` and `x̂ ∈ argmin φ` (`û = 0` is the last
line of the proof, p.37). Conclusion (2): for the exact epi-limit `f`, supported by `ȳ`,
`(û, x̂) ∈ argmin_{u,x} f(u, x) − ⟨ȳ, u⟩`, the right-hand side of (3.5) with `u⋆ = û`.

**Formalization Note.** `ℝᵐ × ℝⁿ` is `(Fin m → ℝ) × (Fin n → ℝ)` (product topology), `R̄` is
`EReal`, `⟨y, u⟩` is `y ⬝ᵥ u`, epi-convergence is the sequential (3.8)–(3.9)
(`PerspEpi.SeqEpiConv`), `εν ↘ 0` is relaxed to `εν ≥ 0 ∧ εν → 0` (the paper does not define `↘`; its use in
`lim_{α ↘ 0}`, p.15, is a limit from above, and every reading implies this relaxed form), every
`argmin` / `ε-argmin` carries the domain condition of p.6, and a cluster point is
`MapClusterPt (û, x̂) atTop (fun ν => (uν, xν))`. `ν` runs over Lean's `ℕ` from `0`. -/
theorem solution {m n : ℕ} (φ : (Fin n → ℝ) → EReal)
    (hdom : (AubinLipschitz.effDom φ).Nonempty)
    (F : ℕ → (Fin m → ℝ) × (Fin n → ℝ) → EReal) (ybar : Fin m → ℝ) (y : ℕ → Fin m → ℝ)
    (hy : Tendsto y atTop (𝓝 ybar)) (ε : ℕ → ℝ) (hε0 : ∀ ν, 0 ≤ ε ν)
    (hε : Tendsto ε atTop (𝓝 0)) (z : ℕ → (Fin m → ℝ) × (Fin n → ℝ))
    (hz : ∀ ν, z ν ∈ epsArgmin (tilt (F ν) (y ν)) (ε ν))
    (zhat : (Fin m → ℝ) × (Fin n → ℝ)) (hzhat : MapClusterPt zhat atTop z) :
    (IsStrictlyLimitExact F φ ybar → zhat.1 = 0 ∧ zhat.2 ∈ argmin φ) ∧
      (∀ f : (Fin m → ℝ) × (Fin n → ℝ) → EReal, IsExact f φ ybar →
        PerspEpi.SeqEpiConv F f → zhat ∈ argmin (tilt f ybar))  := by
  have hcluster (f : (Fin m → ℝ) × (Fin n → ℝ) → EReal)
      (hrock : IsRockafellian f φ) (hepi : PerspEpi.SeqEpiConv F f) :
      zhat ∈ argmin (tilt f ybar) := by
    have htiltdom : (AubinLipschitz.effDom (tilt f ybar)).Nonempty := by
      rcases hdom with ⟨x, hx⟩
      refine ⟨(0, x), ?_⟩
      change φ x ≠ ⊤ at hx
      change tilt f ybar (0, x) ≠ ⊤
      simpa [tilt, hrock x] using hx
    exact eq_A2_clusterPt_mem_argmin
      (fun ν => tilt (F ν) (y ν)) (tilt f ybar)
      (tilt_epiConverges F f ybar y hy hepi)
      htiltdom ε hε0 hε z hz zhat hzhat
  constructor
  · rintro ⟨f, hsx, hepi⟩
    exact proposition_3_3_c f φ ybar hsx zhat.1 zhat.2
      (hcluster f hsx.1 hepi)
  · intro f hexact hepi
    exact hcluster f hexact.1 hepi

#print axioms solution
