-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localized_eq_of_le_39c21971b573
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:42:20.448405+00:00
-- url     : https://prove2.me/submissions/c96c94f2-041c-4f09-9bc2-a15495193385

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
variable {A : Type*} [CommRing A]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {J J'' W : Ideal A} [W.IsPrime] (hle : J ≤ J'')
    (h : ∀ x ∈ J'', ∃ t ∉ W, t * x ∈ J) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J'')) := by
  let q : (A ⧸ J) →ₗ[A] (A ⧸ J'') := Submodule.factor hle
  let f := LocalizedModule.mkLinearMap W.primeCompl (A ⧸ J)
  let g := LocalizedModule.mkLinearMap W.primeCompl (A ⧸ J'')
  let m := IsLocalizedModule.map W.primeCompl f g q
  have hinj : Function.Injective m := by
    apply IsLocalizedModule.injective_of_map_zero W.primeCompl f
    intro x hx
    rw [IsLocalizedModule.map_apply] at hx
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective J x
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff W.primeCompl g).mp hx
    have hsy : (s : A) * y ∈ J'' := by
      have : (s : A) • (Submodule.mkQ J'' y) = 0 := hs
      rwa [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        smul_eq_mul] at this
    obtain ⟨t, ht, hty⟩ := h _ hsy
    refine (IsLocalizedModule.eq_zero_iff W.primeCompl f).mpr ⟨⟨t * s, W.primeCompl.mul_mem ht s.2⟩, ?_⟩
    show ((t * s : A)) • (Submodule.mkQ J y) = 0
    rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul,
      mul_assoc]
    exact hty
  have hsurj : Function.Surjective m :=
    IsLocalizedModule.map_surjective W.primeCompl f g q (Submodule.factor_surjective hle)
  exact ((LinearEquiv.ofBijective m ⟨hinj, hsurj⟩).extendScalarsOfIsLocalization W.primeCompl
    (Localization.AtPrime W)).length_eq
end GroundTheory.Heights₂.Heights.NumbersDVR
