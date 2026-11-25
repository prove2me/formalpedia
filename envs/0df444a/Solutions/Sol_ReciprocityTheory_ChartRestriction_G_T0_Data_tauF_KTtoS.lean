-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.tauF_KTtoS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:44:36.419888+00:00
-- url     : https://prove2.me/submissions/faab73dd-aef4-431e-b429-5720c0bff102

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_tauF_sHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (NumberField.RingOfIntegers K) (A c)]
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (h : d.S1) (c : ι) (b : Fin (d.D + 1)) (hb : b ≠ 0) (u : Kˣ)
    (z : KTf K d.D d.N) :
    tauF (Ω := Ω c) b u (d.KTtoS h c z) = d.KTtoS h c (sigF b u z) := by
  have hl : ∀ G : KTp K d.D d.N,
      d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) G) = d.sH c G := by
    intro G
    first
      | exact IsFractionRing.lift_algebraMap _ _
      | exact IsFractionRing.lift_algebraMap _
      | simp [Data.KTtoS]
  have key : ∀ F : KTp K d.D d.N,
      tauF (Ω := Ω c) b u (d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F)) =
        d.KTtoS h c (sigF b u (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F)) := by
    intro F
    rw [hl, sigF, IsFractionRing.ringEquivOfRingEquiv_algebraMap, hl]
    exact tauF_sHom b hb u (d.jc c) (d.x c) F
  obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective (A := KTp K d.D d.N) z
  simp only [map_div₀, key]
end ReciprocityTheory.ChartRestriction.G.T0.Data
