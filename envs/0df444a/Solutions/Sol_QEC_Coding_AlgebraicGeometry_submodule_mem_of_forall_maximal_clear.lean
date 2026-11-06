-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.submodule_mem_of_forall_maximal_clear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:10:03.249456+00:00
-- url     : https://prove2.me/submissions/d2800169-d7d6-4e07-9379-7643cbc557af

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_KaehlerMapImage
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.LocalProperties.Submodule
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ValuationCentres
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerImage

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (A W : Type*) [CommRing A] [AddCommGroup W] [Module A W]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (U : Submodule A W) (omega : W)
    (h : ∀ (P : Ideal A) [P.IsMaximal], ∃ s : A, s ∉ P ∧ s • omega ∈ U) :
    omega ∈ U := by
  classical
  let I : Ideal A := U.comap (LinearMap.toSpanSingleton A W omega)
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨P,hP,hIP⟩ := I.exists_le_maximal hne
    let : P.IsMaximal := hP
    obtain ⟨s,hs,hu⟩ := h P
    apply hs
    apply hIP
    change s • omega ∈ U
    exact hu
  simpa only [I,Submodule.mem_comap,LinearMap.toSpanSingleton_apply,one_smul] using
    (I.eq_top_iff_one.mp hI)
end QEC.Coding.AlgebraicGeometry
