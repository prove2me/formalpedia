-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.KTtoS_fieldRange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:36:09.362391+00:00
-- url     : https://prove2.me/submissions/4855326b-4d6b-4788-adb7-e5e83c720e15

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional

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
theorem _root_.solution (h : d.S1) (c : ι) :
    (d.KTtoS h c).fieldRange = (d.KT c).toSubfield := by
  have hval : ∀ p : (KTp K d.D d.N), d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) p) =
      MvPolynomial.aeval (sImg (d.jc c) (d.x c)) p := by
    intro p
    simp only [KTtoS]
    rw [IsFractionRing.lift_algebraMap]
    rfl
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := (KTp K d.D d.N)) z
    have hmem : ∀ p : (KTp K d.D d.N), d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) p) ∈ (d.KT c).toSubfield := by
      intro p
      rw [hval]
      show _ ∈ IntermediateField.adjoin K (Set.range (sImg (d.jc c) (d.x c)))
      apply IntermediateField.algebra_adjoin_le_adjoin
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨p, rfl⟩
    rw [map_div₀]
    exact (d.KT c).toSubfield.div_mem (hmem a) (hmem b)
  · intro y hy
    have hE : IntermediateField.adjoin K (Set.range (sImg (d.jc c) (d.x c))) ≤
        { (d.KTtoS h c).fieldRange with
          algebraMap_mem' := fun k => (d.KTtoS h c).mem_fieldRange.2
            ⟨algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (MvPolynomial.C k), by rw [hval, MvPolynomial.aeval_C]⟩ } := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨v, rfl⟩
      exact (d.KTtoS h c).mem_fieldRange.2
        ⟨algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (MvPolynomial.X v), by rw [hval, MvPolynomial.aeval_X]⟩
    exact hE hy
end ReciprocityTheory.ChartRestriction.G.T0.Data
