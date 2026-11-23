-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.HCFR.isOpen_ker
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:03.690797+00:00
-- url     : https://prove2.me/submissions/e4ac933d-5b53-43d1-bf1e-51b2ecbcb5be

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipB
import Theorems.Thm_Neutral_B1_abRestrict_mk


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge ReciprocityTheory.Neutral.Bridge.HCFR
variable (K : Type) [Field K] [NumberField K]
namespace ReciprocityTheory.Neutral.Bridge.HCFR
theorem _root_.solution (Art : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K)
    (hc : Continuous Art) (E : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K E) :
    IsOpen ((((abRestrict K E h).comp Art).comp (QuotientGroup.mk' (diagUnits K).range)).ker :
      Set (Ideles K)) := by
  haveI := h.finiteDimensional
  haveI := h.isGalois
  have hk : ∀ g' : Field.absoluteGaloisGroup K,
      abRestrict K E h (QuotientGroup.mk g') = AlgEquiv.restrictNormalHom E g' :=
    fun g' => abRestrict_mk K E h g'

  have hS : ((abRestrict K E h).ker : Set (Field.absoluteGaloisGroupAbelianization K)) =
      (QuotientGroup.mk : Field.absoluteGaloisGroup K → Field.absoluteGaloisGroupAbelianization K) ''
        (SetLike.coe E.fixingSubgroup) := by
    ext y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_image]
    constructor
    · intro hy
      refine ⟨g, ?_, rfl⟩
      have hg : g ∈ (AlgEquiv.restrictNormalHom E).ker := MonoidHom.mem_ker.mpr ((hk g).symm.trans hy)
      rw [IntermediateField.restrictNormalHom_ker E] at hg
      exact hg
    · rintro ⟨g', hg', he⟩
      rw [← he, hk]
      have hg : g' ∈ (AlgEquiv.restrictNormalHom E).ker := by
        rw [IntermediateField.restrictNormalHom_ker E]
        exact hg'
      exact MonoidHom.mem_ker.mp hg
  have hopen : IsOpen ((abRestrict K E h).ker : Set (Field.absoluteGaloisGroupAbelianization K)) := by
    rw [hS]
    exact QuotientGroup.isOpenMap_coe _ (IntermediateField.fixingSubgroup_isOpen E)
  exact hopen.preimage (hc.comp continuous_quot_mk)
end ReciprocityTheory.Neutral.Bridge.HCFR
