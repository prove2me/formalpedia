-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.emb_sH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:12.195598+00:00
-- url     : https://prove2.me/submissions/92c193ca-2671-4a30-9b5a-9f7b3a31d2c0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SacSuccAbove
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_tauPev_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_KTtoS_alg

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
include hpt
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (σ : OmS (Ω c) d.D d.N →+* ℂ) (hσ : σ.comp (d.KTtoS h c) = tauPev sg pt hpt)
    (q : MvPolynomial (TVar d.D d.N) K) : σ (d.sH c q) = eval₂ sg pt q := by
  rw [← d.KTtoS_alg h c q, ← RingHom.comp_apply, hσ, tauPev_apply]
end ReciprocityTheory.ChartRestriction.G.T0.Data
