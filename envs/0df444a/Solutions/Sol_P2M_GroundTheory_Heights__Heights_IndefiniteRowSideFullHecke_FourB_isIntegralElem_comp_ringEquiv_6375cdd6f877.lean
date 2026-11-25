-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_isIntegralElem_comp_ringEquiv_6375cdd6f877
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:43:25.581916+00:00
-- url     : https://prove2.me/submissions/8b9345e5-5071-469a-9d82-d0b1832acb8c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_NormLeOneIffIsIntegralElemOfEquiv
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open IsDedekindDomain NumberField Polynomial Rat.HeightOneSpectrum
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
theorem _root_.solution {A B S : Type*} [CommRing A] [CommRing B] [CommRing S]
    (φ : A ≃+* B) (f : B →+* S) (x : S) :
    (f.comp (φ : A →+* B)).IsIntegralElem x ↔ f.IsIntegralElem x := by
  constructor
  · rintro ⟨q, hq, hx⟩
    exact ⟨q.map (φ : A →+* B), hq.map _, by rwa [eval₂_map]⟩
  · rintro ⟨q, hq, hx⟩
    refine ⟨q.map (φ.symm : B →+* A), hq.map _, ?_⟩
    rw [eval₂_map, RingHom.comp_assoc]
    have : (φ : A →+* B).comp (φ.symm : B →+* A) = RingHom.id B :=
      RingHom.ext fun b => by simp
    rwa [this, RingHom.comp_id]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
