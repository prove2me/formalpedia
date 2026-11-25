-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.sigF_norm_w0rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:46:54.123668+00:00
-- url     : https://prove2.me/submissions/5451ceee-c309-4942-8691-d9cc9b237c16

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockDegOfScale
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_sigF_normG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_KTtoS_algebraMap_K
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_tauFG_w0rat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_omS_finite


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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (b : Fin (d.D + 1)) (u : Kˣ) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    sigF b u (Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c)) =
      algebraMap K (KTf K d.D d.N) ((if b = 0 then (u : K) else 1) ^ d.delc c) *
        Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  rw [d.sigF_normG h c b u, d.tauFG_w0rat c b u]
  have e : algebraMap K (OmS (Ω c) d.D d.N) (if b = 0 then (u : K) else 1) =
      algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N)
        (algebraMap K (KTf K d.D d.N) (if b = 0 then (u : K) else 1)) :=
    (d.KTtoS_algebraMap_K h c _).symm
  rw [e, map_mul, Algebra.norm_algebraMap, (d.omS_finite hd h c).2, map_pow]
end ReciprocityTheory.ChartRestriction.G.T0.Data
