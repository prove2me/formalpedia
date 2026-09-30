-- Prove2me | solution 1 for WeierstrassEllipticZeta.projective_extension_group_with_regular_operations
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-24T04:51:55.1631+00:00
-- url     : https://prove2.me/submissions/158217b8-3414-46fa-a78b-c08aeb0cfd33

import Theorems.Thm_WeierstrassEllipticZeta_projective_extension_addition_regular
import Theorems.Thm_WeierstrassEllipticZeta_projective_extension_group_with_regular_negation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open TranscendenceTheory
namespace WeierstrassEllipticZeta

/-- The concrete extension has a compatible commutative group structure and
both of its group operations are regular. -/
theorem projective_extension_group_with_regular_operations_implementation
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ) (hη : ∀ ω : L.lattice, η ω = zetaQuasiPeriod L ω) :
    ∃ group : AddCommGroup (ProjectiveExtensionChartLocus L.g₂ L.g₃),
      letI := group
      ∃ e : GraphQuotientExtension L.lattice η ≃+ ProjectiveExtensionChartLocus L.g₂ L.g₃,
        (∀ z u : ℂ, ∃ hv :
            ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
          (e ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
            ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv) ∧
        PhilipponMultiplicity.MultiProjectiveSpace.IsRegularAlong
          (PhilipponMultiplicity.projectiveSquare ℂ 4) (PhilipponMultiplicity.projectiveSpace ℂ 4)
          (fun xy : ProjectiveExtensionChartLocus L.g₂ L.g₃ × ProjectiveExtensionChartLocus L.g₂ L.g₃ =>
            fun i => if i.val = 0 then xy.1.val.val else xy.2.val.val)
          (fun xy => fun _ => (xy.1 + xy.2).val.val) ∧
        PhilipponMultiplicity.MultiProjectiveSpace.IsRegularAlong
          (PhilipponMultiplicity.projectiveSpace ℂ 4) (PhilipponMultiplicity.projectiveSpace ℂ 4)
          (fun x : ProjectiveExtensionChartLocus L.g₂ L.g₃ => fun _ => x.val.val)
          (fun x : ProjectiveExtensionChartLocus L.g₂ L.g₃ => fun _ => (-x).val.val) := by
  obtain ⟨group, e, he, hneg⟩ :=
    projective_extension_group_with_regular_negation L D S hS hS_value hS_ne η hη
  letI := group
  exact ⟨group, e, he,
    projective_extension_addition_regular L D S hS hS_value hS_ne η e he, hneg⟩

end WeierstrassEllipticZeta
open WeierstrassEllipticZeta TranscendenceTheory PhilipponMultiplicity
theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ) (hη : ∀ ω : L.lattice, η ω = zetaQuasiPeriod L ω) :
    ∃ group : AddCommGroup (ProjectiveExtensionChartLocus L.g₂ L.g₃),
      letI := group
      ∃ e : GraphQuotientExtension L.lattice η ≃+ ProjectiveExtensionChartLocus L.g₂ L.g₃,
        (∀ z u : ℂ, ∃ hv :
            ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
          (e ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
            ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv) ∧
        PhilipponMultiplicity.MultiProjectiveSpace.IsRegularAlong
          (PhilipponMultiplicity.projectiveSquare ℂ 4) (PhilipponMultiplicity.projectiveSpace ℂ 4)
          (fun xy : ProjectiveExtensionChartLocus L.g₂ L.g₃ × ProjectiveExtensionChartLocus L.g₂ L.g₃ =>
            fun i => if i.val = 0 then xy.1.val.val else xy.2.val.val)
          (fun xy => fun _ => (xy.1 + xy.2).val.val) ∧
        PhilipponMultiplicity.MultiProjectiveSpace.IsRegularAlong
          (PhilipponMultiplicity.projectiveSpace ℂ 4) (PhilipponMultiplicity.projectiveSpace ℂ 4)
          (fun x : ProjectiveExtensionChartLocus L.g₂ L.g₃ => fun _ => x.val.val)
          (fun x : ProjectiveExtensionChartLocus L.g₂ L.g₃ => fun _ => (-x).val.val) := by
  exact WeierstrassEllipticZeta.projective_extension_group_with_regular_operations_implementation L D S hS hS_value hS_ne η hη
