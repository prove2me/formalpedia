-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.comp_g
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:16:45.830289+00:00
-- url     : https://prove2.me/submissions/678c6b61-bd36-4c40-96ed-061c17b632d9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_comp_facts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_plOver_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HDiscVal_exists_val_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HDiscVal_mem_integralClosure_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Op_isDVR


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
    (n : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ) → ℤ) :
    letI : Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := d.algOp h la c
    ∃ g : OmS (Ω c) d.D d.N, g ≠ 0 ∧ (∀ w ∈ d.PlOver la c, w g = n w) ∧
      ∀ y, (∀ w ∈ d.PlOver la c, 0 ≤ w y + (n w : WithTop ℤ)) ↔
        g * y ∈ integralClosure (Op d.D d.N la) (OmS (Ω c) d.D d.N) := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  letI : Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := d.algOp h la c
  letI := algOpKT (K := K) d.D d.N la
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := d.comp_facts hd h la c
  haveI := Op_isDVR (K := K) d.D d.N la
  obtain ⟨g, hg0, hg⟩ := HDiscVal.exists_val_eq (Op d.D d.N la) (KTf K d.D d.N) n
  rw [d.plOver_eq h la c]
  refine ⟨g, hg0, hg, fun y => ?_⟩
  rw [HDiscVal.mem_integralClosure_iff (Op d.D d.N la) (KTf K d.D d.N)]
  refine forall₂_congr fun w hw => ?_
  rw [AddValuation.map_mul, hg w hw, add_comm]
end ReciprocityTheory.ChartRestriction.G.T0.Data
