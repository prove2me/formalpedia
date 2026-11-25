-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns.admissibleImaginary_eq_halfspaces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:58:36.874411+00:00
-- url     : https://prove2.me/submissions/005536bd-b39d-481f-9f94-ba9d7e487d53

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_EmbeddingHermitianPairs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_AdmissibleHermitianColumns
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_AdmissibleHermitianColumns_leadingMinor_add_rankOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
theorem _root_.solution {ξ : Fin r → E} (x : Frame X.Ψ r) (hx : x ∈ X.dom) :
    ∃ a b : X.Ψ → Fin (r + 1) → ℝ, admissibleImaginary X ξ x = {y | ∀ τ i, 0 < a τ i + y τ * b τ i} := by
  have hL : ∀ τ : X.Ψ, ∀ i : Fin (r + 1), lminor (gram τ.1 X.Gm (mat x τ)) i ≠ 0 := by
    intro τ i h
    have h1 := (hx τ).2 i
    simp only [dmin, h, Complex.zero_re, mul_zero, lt_irrefl] at h1
  have hk : ∀ τ : X.Ψ, ∀ i : Fin (r + 1), ∃ κ : ℂ, ∀ t : ℂ,
      lminor (gram τ.1 X.Gm (mat x τ) + t • rk1 X ξ τ (mat x τ)) i =
        lminor (gram τ.1 X.Gm (mat x τ)) i * (1 + t * κ) :=
    fun τ i => leadingMinor_add_rankOne _ _ _ i (hL τ i)
  choose κ hκ using hk
  have hre : ∀ (L k : ℂ) (t : ℝ), (L * (1 + (t : ℂ) * k)).re = L.re + t * (L * k).re := by
    intro L k t
    rw [show L * (1 + (t : ℂ) * k) = L + (t : ℂ) * (L * k) by ring, Complex.add_re,
      Complex.re_ofReal_mul]
  refine ⟨fun τ i => psgn X.p0 i * (lminor (gram τ.1 X.Gm (mat x τ)) i).re,
    fun τ i => psgn X.p0 i * (2 * X.c τ) * (lminor (gram τ.1 X.Gm (mat x τ)) i * κ τ i).re, ?_⟩
  ext y
  simp only [admissibleImaginary, Set.mem_setOf_eq, hκ, hre]
  refine forall_congr' fun τ => forall_congr' fun i => ?_
  apply iff_of_eq
  congr 1
  ring
end ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
