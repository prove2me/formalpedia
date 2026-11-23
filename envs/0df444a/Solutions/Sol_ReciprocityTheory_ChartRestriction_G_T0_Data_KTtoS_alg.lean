-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.KTtoS_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:07.56039+00:00
-- url     : https://prove2.me/submissions/c4d9a6a2-5825-415d-8260-ccc823282890

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SacSuccAbove

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
variable (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) (pt : TVar d.D d.N → ℂ)
  (hpt : ∀ q : MvPolynomial (TVar d.D d.N) K, q ≠ 0 → eval₂ sg pt q ≠ 0)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (q : KTp K d.D d.N) :
    d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) q) = d.sH c q := by
  rw [KTtoS, IsFractionRing.lift_algebraMap]
  rfl
end ReciprocityTheory.ChartRestriction.G.T0.Data
