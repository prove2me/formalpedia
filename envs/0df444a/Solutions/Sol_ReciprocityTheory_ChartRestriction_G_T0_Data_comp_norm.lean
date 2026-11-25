-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.comp_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:27:20.85074+00:00
-- url     : https://prove2.me/submissions/e0421f57-5c4a-4142-9685-c610516977ff

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_comp_facts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_plOver_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Op_isDVR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_norm_eq_places
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_unifOp_irreducible


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (la : HeightOneSpectrum (𝓞 K)) (c : ι)
    {g : OmS (Ω c) d.D d.N} (hg0 : g ≠ 0) (n : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ) → ℤ)
    (hg : ∀ w ∈ d.PlOver la c, w g = n w) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    ∃ u : Op d.D d.N la, IsUnit u ∧ Algebra.norm (KTf K d.D d.N) g =
      OpToKT d.D d.N la (unifOp d.D d.N la) ^
        (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.PlOver la c),
          (d.fze h c w : ℤ) * n w) * OpToKT d.D d.N la u := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  letI : Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := d.algOp h la c
  letI := algOpKT (K := K) d.D d.N la
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := d.comp_facts hd h la c
  haveI := Op_isDVR (K := K) d.D d.N la
  obtain ⟨u, hu, hN⟩ := ValPl.norm_eq_places (O := Op d.D d.N la) (F := KTf K d.D d.N) g hg0
    (unifOp_irreducible d.D d.N la)
  refine ⟨u, hu, ?_⟩
  rw [hN]
  have hg' : ∀ w ∈ ValPl.PlacesOver (Op d.D d.N la) (OmS (Ω c) d.D d.N), w g = n w := by
    rw [← d.plOver_eq h la c]
    exact hg
  rw [d.plOver_eq h la c]
  congr 2
  refine finsum_congr fun w => finsum_congr fun hw => ?_
  rw [hg' w hw, WithTop.untopD_coe]
  rfl
end ReciprocityTheory.ChartRestriction.G.T0.Data
