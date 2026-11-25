-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.SpecialFibreFactorization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:26:12.686512+00:00
-- url     : https://prove2.me/submissions/808672e0-2118-41bd-860b-67bb3d12eae9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormGenericRatioSpec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SubstRowZeroFixOfDegreeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_X4v4RatioSpec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SpecialFibreFactorization
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_norm_generic_ratio_spec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_norm_ratio_pi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_pi_free
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c)
    (x : Fin (d.N + 1) → K) (hx : d.wx x c ≠ 0) :
    ∃ κ : K, κ ≠ 0 ∧
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N)
        (MvPolynomial.aeval (fun v : TVar d.D d.N =>
          if v.1 = 0 then MvPolynomial.C (x v.2) else MvPolynomial.X v) F) =
      algebraMap K (KTf K d.D d.N) κ *
        ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.wx x c) p := by
  classical
  obtain ⟨P, Q, hQ0, hQx, hPQ, hspec⟩ := d.norm_generic_ratio_spec hd h c
  obtain ⟨Pp, Pm, hPm0, hPpx, hPmx, hPi⟩ := d.pi_free hd h c (d.w (d.jc c) c)
  obtain ⟨κ, hκ, hκeq⟩ := d.norm_ratio_pi hd h c x hx
  refine ⟨κ, hκ, ?_⟩
  have hφinj := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
  have hpoly : Q * F * Pm = P * Pp := by
    apply hφinj
    simp only [map_mul]
    rw [hF, hPi, hPQ]
    simp only [fZ]
    ring
  have hsub := congrArg (d.sub0 x) hpoly
  simp only [map_mul, hQx, hPmx, hPpx] at hsub
  have hφ := congrArg (algebraMap (KTp K d.D d.N) (KTf K d.D d.N)) hsub
  simp only [map_mul] at hφ
  rw [hspec x hx, hPi] at hφ
  have hQ' : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Q ≠ 0 :=
    (map_ne_zero_iff _ hφinj).mpr hQ0
  have hPm' : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Pm ≠ 0 :=
    (map_ne_zero_iff _ hφinj).mpr hPm0
  rw [← hκeq]
  apply mul_left_cancel₀ (mul_ne_zero hQ' hPm')
  calc _ = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Q *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.sub0 x F) *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Pm := by ring
    _ = _ := hφ
    _ = _ := by ring
end ReciprocityTheory.ChartRestriction.G.T0.Data
