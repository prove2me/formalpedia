-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.sigF_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:55:16.863254+00:00
-- url     : https://prove2.me/submissions/417eb5b1-e5c9-4c6f-b349-3f28aca0af7f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_tauF_algebraMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_tauF_KTtoS

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
theorem _root_.solution (h : d.S1) (c : ι) (b : Fin (d.D + 1)) (hb : b ≠ 0) (u : Kˣ) (r : Ω c) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    sigF b u (Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) r)) =
      Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) r) := by
  try intro _
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  have he : (algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N)).comp
      ((sigF (N := d.N) b u : KTf K d.D d.N ≃+* KTf K d.D d.N) : KTf K d.D d.N →+* KTf K d.D d.N) =
      ((tauF (Ω := Ω c) (D := d.D) (N := d.N) b u :
          OmS (Ω c) d.D d.N ≃+* OmS (Ω c) d.D d.N) : OmS (Ω c) d.D d.N →+* OmS (Ω c) d.D d.N).comp
        (algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N)) := by
    refine RingHom.ext fun z => ?_
    exact (tauF_KTtoS d h c b hb u z).symm
  have hn := Algebra.norm_eq_of_equiv_equiv (sigF (N := d.N) b u)
    (tauF (Ω := Ω c) (D := d.D) (N := d.N) b u) he (algebraMap (Ω c) (OmS (Ω c) d.D d.N) r)
  rw [tauF_algebraMap] at hn
  have h2 := congrArg (sigF (N := d.N) b u) hn
  rw [RingEquiv.apply_symm_apply] at h2
  exact h2
end ReciprocityTheory.ChartRestriction.G.T0.Data
