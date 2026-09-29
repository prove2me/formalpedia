-- Prove2me | solution 1 for ResidualGaloisRep.exists_unipotent_model_and_linearEquiv_localFlatClassesAd_of_isLocalRing_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/6cae5a13-b199-567e-8d46-feae89630bed

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_ExtCitation_KummerBridge
import Theorems.Thm_ResidualGaloisRep_exists_dualTwist_linearEquiv_dual
import Theorems.Thm_ResidualGaloisRep_exists_unipotent_model_dualTwist_of_isLocalRing_baseChange
import Theorems.Thm_ResidualGaloisRep_finrank_invariants_adRep_eq_of_dualTwist
import Theorems.Thm_ResidualGaloisRep_nonempty_localFlatClassesAd_linearEquiv_of_dualTwist
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_exists_unipotent_model_and_linearEquiv_localFlatClassesAd_of_isLocalRing_baseChange

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem solution
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    [Algebra ℤ_[p] (ZMod p)] (hker : RingHom.ker (algebraMap ℤ_[p] (ZMod p)) = Ideal.span {(p : ℤ_[p])})
    (ρbar : ResidualGaloisRep k)
    (hconn : ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      IsLocalRing (TensorProduct ℤ_[p] (ZMod p) H) ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V × ρbar.V,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
          (∀ h : H, g h = ResidualGaloisRep.localAut p σ (f h)) →
            e g = ρbar.dualLiftModuleActAd p 0 σ (e f)) :
    ∃ ρbar' : ResidualGaloisRep k,
      (∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      IsLocalRing (CartierDual (ZMod p) (TensorProduct ℤ_[p] (ZMod p) H)) ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar'.V × ρbar'.V,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
          (∀ h : H, g h = ResidualGaloisRep.localAut p σ (f h)) →
            e g = ρbar'.dualLiftModuleActAd p 0 σ (e f)) ∧
      Nonempty ((ρbar.localFlatClassesAd p) ≃ₗ[k] (ρbar'.localFlatClassesAd p)) ∧
      Module.finrank k (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)).ρ.invariants =
        Module.finrank k (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar'.adRep)).ρ.invariants := by
  obtain ⟨ρbar', η, hη⟩ := ResidualGaloisRep.exists_dualTwist_linearEquiv_dual p ρbar
  exact ⟨ρbar',
    ResidualGaloisRep.exists_unipotent_model_dualTwist_of_isLocalRing_baseChange p hp2 hker ρbar hconn ρbar' η hη,
    ResidualGaloisRep.nonempty_localFlatClassesAd_linearEquiv_of_dualTwist p hp2 hker ρbar ρbar' η hη,
    ResidualGaloisRep.finrank_invariants_adRep_eq_of_dualTwist p ρbar ρbar' η hη⟩

end S_ResidualGaloisRep_exists_unipotent_model_and_linearEquiv_localFlatClassesAd_of_isLocalRing_baseChange
end P2MW
export P2MW.S_ResidualGaloisRep_exists_unipotent_model_and_linearEquiv_localFlatClassesAd_of_isLocalRing_baseChange (solution)
