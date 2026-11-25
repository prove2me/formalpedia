-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionCycle_length_localized_eq_9df2ed0bc3a3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:15:23.323927+00:00
-- url     : https://prove2.me/submissions/09b285ef-0ebd-4dc5-b135-512efac6a199

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LiftOldChartMonomialMemPrimeCompl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SectionCycle
variable {S : Type*} [CommRing S]
namespace GroundTheory.Heights₂.Heights.SectionCycle
theorem _root_.solution {J J₁ W : Ideal S} [W.IsPrime] (hJ : J ≤ J₁) {t : S} (ht : t ∉ W)
    (hmul : ∀ x ∈ J₁, t * x ∈ J) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (S ⧸ J)) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (S ⧸ J₁)) := by
  let q : (S ⧸ J) →ₗ[S] (S ⧸ J₁) := Submodule.mapQ J J₁ LinearMap.id hJ
  let φ := IsLocalizedModule.map W.primeCompl (LocalizedModule.mkLinearMap W.primeCompl (S ⧸ J))
    (LocalizedModule.mkLinearMap W.primeCompl (S ⧸ J₁)) q
  have hφ : ∀ (x : S) (s : W.primeCompl), φ (LocalizedModule.mk (Submodule.Quotient.mk x) s) =
      LocalizedModule.mk (Submodule.Quotient.mk x) s := by
    intro x s
    rw [IsLocalizedModule.map_LocalizedModules]
    rfl
  have htW : t ∈ W.primeCompl := ht
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y
    refine LocalizedModule.induction_on (fun m s hy ↦ ?_) y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective J m
    rw [hφ, ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at hy
    obtain ⟨u, hu⟩ := hy
    simp only [smul_zero, one_smul] at hu
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      smul_eq_mul] at hu
    rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq]
    refine ⟨⟨t, htW⟩ * u, ?_⟩
    simp only [smul_zero, one_smul]
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      smul_eq_mul, Submonoid.coe_mul, mul_assoc]
    exact hmul _ hu
  have hsurj : Function.Surjective φ := by
    intro y
    refine LocalizedModule.induction_on (fun m s ↦ ?_) y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective J₁ m
    exact ⟨LocalizedModule.mk (Submodule.Quotient.mk x) s, hφ x s⟩
  exact ((LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).extendScalarsOfIsLocalization W.primeCompl
    (Localization.AtPrime W)).length_eq
end GroundTheory.Heights₂.Heights.SectionCycle
