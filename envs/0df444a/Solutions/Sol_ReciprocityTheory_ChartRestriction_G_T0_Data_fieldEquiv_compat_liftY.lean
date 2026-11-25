-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.fieldEquiv_compat_liftY
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:10:42.285281+00:00
-- url     : https://prove2.me/submissions/ef1c5776-0911-4cb5-a5a6-9e06782adbf1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OffBaseSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FracFieldPositiveRowsOmega
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_eLX4_algebraMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_algLE_algebraMap

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
theorem _root_.solution (h : d.S1) (c : ι) (q : KTf K d.D d.N) :
    letI := d.algLE h c
    d.eEX4 c (d.KTtoS h c q) = VariableBasisExtension.liftY (L := d.FracFieldPositiveRowsBase) (E := d.FracFieldPositiveRowsOmega c) (σ := Fin (d.N + 1)) (d.eLX4 q) := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := KTp K d.D d.N) q
  simp only [map_div₀]
  congr 1
  all_goals
    rw [show ∀ P : KTp K d.D d.N, d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) P) =
      d.sH c P from fun P => IsFractionRing.lift_algebraMap _ _]
    rw [d.compat0 c, d.eLX4_algebraMap]
    unfold FractionFieldVariableLift.toFracY VariableBasisExtension.liftY
    rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap, RingHom.comp_apply, MvPolynomial.map_map]
    rw [show (@algebraMap d.FracFieldPositiveRowsBase (d.FracFieldPositiveRowsOmega c) _ _ (d.algLE h c)).comp (algebraMap d.PolyRingPositiveRowsBase d.FracFieldPositiveRowsBase) =
      d.psiE c from RingHom.ext fun p => d.algLE_algebraMap h c p]
end ReciprocityTheory.ChartRestriction.G.T0.Data
