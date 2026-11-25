-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.sigF_normG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:55:28.996273+00:00
-- url     : https://prove2.me/submissions/56b5d76f-31b3-45eb-ac5c-6ec5280a938a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockDegOfScale
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_tauFG_KTtoS

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
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (h : d.S1) (c : ι) (b : Fin (d.D + 1)) (u : Kˣ) (z : OmS (Ω c) d.D d.N) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    sigF b u (Algebra.norm (KTf K d.D d.N) z) =
      Algebra.norm (KTf K d.D d.N) (tauFG (Ω := Ω c) b u z) := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  have he : (algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N)).comp
      (sigF (K := K) (D := d.D) (N := d.N) b u : KTf K d.D d.N →+* KTf K d.D d.N) =
      (tauFG (Ω := Ω c) (K := K) (D := d.D) (N := d.N) b u :
        OmS (Ω c) d.D d.N →+* OmS (Ω c) d.D d.N).comp
        (algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N)) := by
    ext1 z
    exact (d.tauFG_KTtoS h c b u z).symm
  rw [Algebra.norm_eq_of_equiv_equiv (sigF (K := K) (D := d.D) (N := d.N) b u)
    (tauFG (Ω := Ω c) (K := K) (D := d.D) (N := d.N) b u) he z]
  exact RingEquiv.apply_symm_apply _ _
end ReciprocityTheory.ChartRestriction.G.T0.Data
