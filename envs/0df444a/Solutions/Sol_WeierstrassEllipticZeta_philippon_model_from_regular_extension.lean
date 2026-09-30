-- Prove2me | solution 1 for WeierstrassEllipticZeta.philippon_model_from_regular_extension
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-24T07:14:05.985255+00:00
-- url     : https://prove2.me/submissions/eb420842-dfb1-493b-b191-7f842867ef7a

import Theorems.Thm_WeierstrassEllipticZeta_philippon_model_from_hilbert_and_dense_extension
import Theorems.Thm_PhilipponMultiplicity_additive_projective_hilbert_polynomial
import Theorems.Thm_WeierstrassEllipticZeta_projective_extension_hilbert_polynomial
import Theorems.Thm_WeierstrassEllipticZeta_projective_extension_curve_zariski_dense
set_option autoImplicit false
open WeierstrassEllipticZeta TranscendenceTheory PhilipponMultiplicity

theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ) (hη : ∀ ω : L.lattice, η ω = zetaQuasiPeriod L ω)
    [AddCommGroup (ProjectiveExtensionChartLocus L.g₂ L.g₃)]
    (e : GraphQuotientExtension L.lattice η ≃+ ProjectiveExtensionChartLocus L.g₂ L.g₃)
    (he : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (e ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)


    (hadd : MultiProjectiveSpace.IsRegularAlong (projectiveSquare ℂ 4) (projectiveSpace ℂ 4)
      (fun xy : ProjectiveExtensionChartLocus L.g₂ L.g₃ × ProjectiveExtensionChartLocus L.g₂ L.g₃ =>
        fun i => if i.val = 0 then xy.1.val.val else xy.2.val.val)
      (fun xy => fun _ => (xy.1 + xy.2).val.val))
    (hneg : MultiProjectiveSpace.IsRegularAlong (projectiveSpace ℂ 4) (projectiveSpace ℂ 4)
      (fun x : ProjectiveExtensionChartLocus L.g₂ L.g₃ => fun _ => x.val.val)
      (fun x => fun _ => (-x).val.val)) :
    Nonempty (WeierstrassEllipticZeta.PhilipponApplication.Model S) := by
  exact WeierstrassEllipticZeta.philippon_model_from_hilbert_and_dense_extension
    L D S hS hS_value hS_ne η hη e he hadd hneg
    (PhilipponMultiplicity.additive_projective_hilbert_polynomial ℂ)
    (WeierstrassEllipticZeta.projective_extension_hilbert_polynomial
      L D S hS hS_value hS_ne η e he)
    (WeierstrassEllipticZeta.projective_extension_curve_zariski_dense
      L D S hS hS_value hS_ne η e he)
