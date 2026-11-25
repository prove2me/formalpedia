-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_phi_eq_eval__9a32e9bc08e4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:33:19.044023+00:00
-- url     : https://prove2.me/submissions/84fa88d2-1da1-4418-a2f6-b5c42e0d0f2f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_AffineChartIdealPrimeAndSaturated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict
theorem _root_.solution (Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) [Q.IsPrime]
    (f : MvPolynomial (Σ k, ι k) ℂ) :
    phi Q f = eval₂ ((phi Q).comp C) (fun q => phi Q (X q)) f := by
  have : phi Q = eval₂Hom ((phi Q).comp C) (fun q => phi Q (X q)) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro q; simp
  exact DFunLike.congr_fun this f
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict
