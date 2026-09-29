-- Prove2me | solution 1 for ResidualGaloisRep.finite_of_isLocallyFlatCocycleAd_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c79c7abf-6bc5-5808-bfb4-a28c45205bb3

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_finite_of_isLocallyFlatCocycleAd_zero

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem solution
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (ρbar : ResidualGaloisRep k)
    (hflat : ρbar.IsLocallyFlatCocycleAd p 0) : Finite k := by
  obtain ⟨H, _, _, hfin, hfl, hcc, e, he_add, he_act⟩ := hflat
  haveI : Module.Free ℤ_[p] H := Module.free_of_flat_of_isLocalRing
  haveI : Finite (H →ₐ[ℤ_[p]] PadicAlgCl p) := Finite.algHom ℤ_[p] H (PadicAlgCl p)
  haveI : Finite (WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)) :=
    Finite.of_equiv _ (WithConv.equiv (H →ₐ[ℤ_[p]] PadicAlgCl p)).symm
  haveI : Finite (ρbar.V × ρbar.V) := Finite.of_equiv _ e
  haveI : Finite ρbar.V :=
    Finite.of_injective (fun v : ρbar.V => (v, (0 : ρbar.V))) fun a b h => (Prod.mk.inj h).1
  haveI : Nontrivial ρbar.V := Module.nontrivial_of_finrank_pos (R := k) (by rw [ρbar.finrank_eq]; omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : ρbar.V)
  exact Finite.of_injective (fun c : k => c • v) (smul_left_injective k hv)

end S_ResidualGaloisRep_finite_of_isLocallyFlatCocycleAd_zero
end P2MW
export P2MW.S_ResidualGaloisRep_finite_of_isLocallyFlatCocycleAd_zero (solution)
