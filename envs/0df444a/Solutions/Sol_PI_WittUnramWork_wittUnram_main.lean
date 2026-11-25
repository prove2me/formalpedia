-- Prove2me | solution 1 for PI.WittUnramWork.wittUnram_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:42:20.358456+00:00
-- url     : https://prove2.me/submissions/c7089e1c-db06-423d-9b0b-edb608db25d6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WittUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittUnramified_GhostComponentG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittUnramified_PsiStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittUnramified_WittUnramMain
import Theorems.Thm_PI_WittUnramWork_psi_injective
import Theorems.Thm_PI_WittUnramWork_psi_surjective
import Theorems.Thm_PI_WittUnramWork_sHom_coeff_zero
import Theorems.Thm_PI_WittUnramWork_sHom_frob
import Theorems.Thm_PI_WittUnramWork_sigW_lift
import Theorems.Thm_PI_WittUnramWork_sigW_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.WittUnramWork
open WittVector
private theorem map_frobenius' {p : ℕ} [Fact p.Prime] {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (x : WittVector p R) :
    WittVector.map g (WittVector.frobenius x) = WittVector.frobenius (WittVector.map g x) := by
  ext n
  simp only [WittVector.map_coeff, WittVector.coeff_frobenius, MvPolynomial.aeval_def,
    MvPolynomial.eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _
end PI.WittUnramWork
end
end

set_option autoImplicit false
noncomputable section
open PI PI.WittUnramWork
open WittVector
namespace PI.WittUnramWork
theorem _root_.solution : PI.WittUnram := by
  intro p f _ W Qq _ _ _ _ _ σ hfrac hirr hcard hcomp hσ
  have hinj : Function.Injective (algebraMap W Qq) := IsFractionRing.injective W Qq
  have hF : ∀ x : W, ∃ y : W, sigW hinj σ hσ x = x ^ p + (p : W) * y := sigW_lift hinj σ hσ
  set I : Ideal W := Ideal.span {(p : W)} with hI
  haveI hmax : I.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hirr
  letI : Field (W ⧸ I) := Ideal.Quotient.field I
  have hp0 : ((p : ℕ) : W ⧸ I) = 0 := by
    have h : Ideal.Quotient.mk I (p : W) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    rwa [map_natCast] at h
  haveI hchar : CharP (W ⧸ I) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp0
  haveI hfin : Finite (W ⧸ I) := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  obtain ⟨e⟩ : Nonempty ((W ⧸ I) ≃+* GaloisField p f) := by
    letI : Algebra (ZMod p) (W ⧸ I) := (ZMod.castHom (dvd_refl p) (W ⧸ I)).toAlgebra
    exact ⟨(GaloisField.algEquivGaloisField p f hcard).toRingEquiv⟩
  have hpQ : ((p : ℕ) : Qq) ≠ 0 := by
    rw [← map_natCast (algebraMap W Qq) p]
    exact fun h => hirr.ne_zero (hinj (h.trans (map_zero _).symm))
  letI : Invertible ((p : ℕ) : Qq) := invertibleOfNonzero hpQ
  let ψ : W →+* WittVector p (W ⧸ I) :=
    (WittVector.map (Ideal.Quotient.mk I)).comp (sHom p Qq (sigW hinj σ hσ) hF hinj)
  have h0 : ∀ x, (ψ x).coeff 0 = Ideal.Quotient.mk I x := by
    intro x
    show (WittVector.map (Ideal.Quotient.mk I) (sHom p Qq (sigW hinj σ hσ) hF hinj x)).coeff 0 = _
    rw [WittVector.map_coeff, sHom_coeff_zero]
  have hψi : Function.Injective ψ := psi_injective ψ hirr
  have hψs : Function.Surjective ψ :=
    psi_surjective ψ (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective h0 hcomp
  let χ : W →+* WittVector p (GaloisField p f) := (WittVector.map (e : (W ⧸ I) →+* GaloisField p f)).comp ψ
  have hχ : Function.Bijective χ :=
    ⟨(WittVector.map_injective _ e.injective).comp hψi, (WittVector.map_surjective _ e.surjective).comp hψs⟩
  have hφ : ∀ w, (RingEquiv.ofBijective χ hχ).symm (χ w) = w := by
    intro w
    have h := (RingEquiv.ofBijective χ hχ).symm_apply_apply w
    rwa [RingEquiv.ofBijective_apply] at h
  have hfrob : ∀ w, WittVector.frobenius (χ w) = χ (sigW hinj σ hσ w) := by
    intro w
    show _ = WittVector.map (e : (W ⧸ I) →+* GaloisField p f)
      (WittVector.map (Ideal.Quotient.mk I) (sHom p Qq (sigW hinj σ hσ) hF hinj (sigW hinj σ hσ w)))
    rw [sHom_frob, map_frobenius', map_frobenius']
    rfl
  refine ⟨(RingEquiv.ofBijective χ hχ).symm, ?_⟩
  intro x
  obtain ⟨w, rfl⟩ := hχ.2 x
  rw [hfrob, hφ, hφ]
  exact (sigW_spec hinj σ hσ w).symm
end PI.WittUnramWork
