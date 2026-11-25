-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.norm_at_la_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:18:13.547348+00:00
-- url     : https://prove2.me/submissions/5fe7fc14-ab5c-40a5-939c-ccec0dd39799

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OpIsDVR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormPtsA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPA_op_isFractionRing
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPA_op_irreducible
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPA_opToKT_C
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_opToS_alg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_omS_finite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Op_isDVR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_norm_eq_places
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_placesOver_iff_loc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsLocalRing
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (ϖ : 𝓞 K) (hϖ : ϖ ∈ la.asIdeal) (hϖ2 : ϖ ∉ la.asIdeal ^ 2)
    (y : OmS (Ω c) d.D d.N) (hy : y ≠ 0) :
    ∃ u : Op d.D d.N la, IsUnit u ∧
      letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
      Algebra.norm (KTf K d.D d.N) y =
        (algebraMap K (KTf K d.D d.N) (ϖ : K)) ^
          (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.PlOver la c),
            (d.fze h c w : ℤ) * WithTop.untopD 0 (w y)) * OpToKT d.D d.N la u := by
  letI iF : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  letI iO : Algebra (Op d.D d.N la) (KTf K d.D d.N) := (OpToKT d.D d.N la).toAlgebra
  letI iOL : Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := (d.OpToS h la c).toAlgebra
  haveI : IsScalarTower (Op d.D d.N la) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsDiscreteValuationRing (Op d.D d.N la) := Op_isDVR d.D d.N la
  haveI : IsFractionRing (Op d.D d.N la) (KTf K d.D d.N) := NPA.op_isFractionRing d.D d.N la
  haveI : FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.omS_finite hd h c).1
  haveI : CharZero (KTf K d.D d.N) :=
    charZero_of_injective_algebraMap (algebraMap K (KTf K d.D d.N)).injective
  haveI : Algebra.IsSeparable (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := inferInstance
  haveI : IsDedekindDomain (integralClosure (Op d.D d.N la) (OmS (Ω c) d.D d.N)) :=
    integralClosure.isDedekindDomain (Op d.D d.N la) (KTf K d.D d.N) _
  haveI : IsFractionRing (integralClosure (Op d.D d.N la) (OmS (Ω c) d.D d.N)) (OmS (Ω c) d.D d.N) :=
    integralClosure.isFractionRing_of_finite_extension (KTf K d.D d.N) _
  obtain ⟨u, hu, hn⟩ := ValPl.norm_eq_places (O := Op d.D d.N la) (F := KTf K d.D d.N) y hy
    (NPA.op_irreducible d.D d.N la ϖ hϖ hϖ2)
  letI iT : Algebra (OT K d.D d.N) (OmS (Ω c) d.D d.N) := (d.OTtoS c).toAlgebra
  haveI : IsScalarTower (OT K d.D d.N) (Op d.D d.N la) (OmS (Ω c) d.D d.N) :=
    IsScalarTower.of_algebraMap_eq (fun x => (d.opToS_alg h la c x).symm)
  have hpl : ValPl.PlacesOver (Op d.D d.N la) (OmS (Ω c) d.D d.N) = d.PlOver la c := by
    ext w
    simp only [ValPl.PlacesOver, Data.PlOver, Set.mem_setOf_eq]
    rw [← ValPl.placesOver_iff_loc (R := OT K d.D d.N) (laT d.D d.N la) w]
    rfl
  refine ⟨u, hu, ?_⟩
  rw [hn, hpl]
  rw [show algebraMap (Op d.D d.N la) (KTf K d.D d.N)
      (algebraMap (OT K d.D d.N) (Op d.D d.N la) (MvPolynomial.C ϖ)) =
      algebraMap K (KTf K d.D d.N) (ϖ : K) from NPA.opToKT_C d.D d.N la ϖ]
  rfl
end ReciprocityTheory.ChartRestriction.G.T0.Data
