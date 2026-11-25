-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_theta_symm_bind__207343eb3d12
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:58:53.673072+00:00
-- url     : https://prove2.me/submissions/d7392588-dbac-4c7c-b8f1-a64397fe941f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_AffineChartIdealPrimeAndSaturated
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_phi_eq_zero_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_theta_X
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm


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
    (p : (k : K) → ι k) (hp : ∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q)
    (f : MvPolynomial (Σ k, ι k) ℂ) :
    theta Q p ((renR (Σ k, ι k)).symm (bind₁ (SncRes.lift p) f)) = theta Q p f := by
  classical
  have hx : ∀ k, phi Q (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ≠ 0 := fun k h =>
    hp k ((phi_eq_zero_iff Q _).1 h)
  have hren : ∀ g : MvPolynomial (Σ k, ι k) ℂ,
      (renR (Σ k, ι k)).symm (renR (Σ k, ι k) g) = g := (renR (Σ k, ι k)).symm_apply_apply
  have : ((theta Q p).comp ((renR (Σ k, ι k)).symm : _ →+* _)).comp
      (bind₁ (SncRes.lift p)).toRingHom = theta Q p := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have e : (renR (Σ k, ι k)) (C r) = C r := by simp [renameEquiv_apply]
      have e2 : (bind₁ (SncRes.lift p)) (C r : MvPolynomial (Σ k, ι k) ℂ) = C r := by simp
      show theta Q p ((renR (Σ k, ι k)).symm (bind₁ (SncRes.lift p) (C r))) = _
      rw [e2, ← e, hren]
    · intro q
      show theta Q p ((renR (Σ k, ι k)).symm (bind₁ (SncRes.lift p) (X q))) = _
      rw [bind₁_X_right, SncRes.lift]
      split_ifs with h
      · obtain ⟨k, i⟩ := q
        simp only at h
        subst h
        rw [map_one, map_one, theta_X, div_self (hx k)]
      · have e : X (Fintype.equivFin (Σ k, ι k) q) = renR (Σ k, ι k) (X q) := by
          simp [renameEquiv_apply]
        rw [e, hren]
  exact DFunLike.congr_fun this f
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict
