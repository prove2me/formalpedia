-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.omS_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:17:35.736909+00:00
-- url     : https://prove2.me/submissions/487a27d2-de0d-4401-bd9e-9e0504413ea3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_KTtoS_fieldRange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_KT_finiteDimensional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) ∧
      Module.finrank (KTf K d.D d.N) (OmS (Ω c) d.D d.N) = d.delc c := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  haveI := d.KT_finiteDimensional hd c
  have hfr := d.KTtoS_fieldRange h c
  let e : (KTf K d.D d.N) ≃+* (d.KT c) :=
    ((d.KTtoS h c).rangeRestrictFieldEquiv).trans (RingEquiv.subfieldCongr hfr)
  have he : ∀ z, ((e z : d.KT c) : (OmS (Ω c) d.D d.N)) = d.KTtoS h c z := fun z => rfl
  have hc : (algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N)).comp e.symm.toRingHom =
      (RingEquiv.refl (OmS (Ω c) d.D d.N)).toRingHom.comp (algebraMap (d.KT c) (OmS (Ω c) d.D d.N)) := by
    refine RingHom.ext fun y => ?_
    show d.KTtoS h c (e.symm y) = (y : (OmS (Ω c) d.D d.N))
    rw [← he, RingEquiv.apply_symm_apply]
  refine ⟨Module.Finite.of_equiv_equiv e.symm (RingEquiv.refl _) hc, ?_⟩
  rw [show d.delc c = Module.finrank (d.KT c) (OmS (Ω c) d.D d.N) from rfl]
  exact (Algebra.finrank_eq_of_equiv_equiv e.symm (RingEquiv.refl _) hc).symm
end ReciprocityTheory.ChartRestriction.G.T0.Data
