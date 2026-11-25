-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_incAC_isLocalHom_02e2103e1a9e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:56:43.768+00:00
-- url     : https://prove2.me/submissions/2f52a13d-196a-45fb-a9c0-99121d3a69fc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpFibreDegreeCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleHomLocLaurent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_exists_frac_9c6adeb809ef

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
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
open GroundTheory.Heights₂.Heights.NumbersDVR.HomLocLaurent
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
variable [Fintype K] {P W : Ideal (MRing ι R)} [P.IsPrime] [W.IsPrime]
variable (T : ∀ k, ι k) (hPW : P ≤ W) (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι R) ∉ W)
include hT
namespace GroundTheory.Heights₂.Heights.NumbersDVR.HomLocLaurent
theorem _root_.solution : IsLocalHom (incAC hPW) := by
  letI := (algQC hPW).toAlgebra
  haveI := wbar_isPrime hPW
  haveI := locC_isLocalization hPW
  refine ⟨fun a ha => ?_⟩
  obtain ⟨b, f, g, hf, hg, hgW, hag⟩ := exists_frac hPW a.2
  have hne : ∀ {g : MRing ι R}, g ∉ W → fr P g ≠ 0 := fun hg => fr_ne_zero fun h => hg (hPW h)
  have hgu : IsUnit (algQC hPW (Ideal.Quotient.mk P g)) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (locC hPW) (W.map (Ideal.Quotient.mk P)) _).mpr
      fun h => hgW ((Ideal.mem_quotient_iff_mem hPW).mp h)
  have hfe : algQC hPW (Ideal.Quotient.mk P f) =
      incAC hPW a * algQC hPW (Ideal.Quotient.mk P g) := by
    apply Subtype.ext
    change fr P f = (a : FractionRing (MRing ι R ⧸ P)) * fr P g
    rw [hag, div_mul_cancel₀ _ (hne hgW)]
  have hfW : f ∉ W := by
    intro hfW
    have hfu : IsUnit (algQC hPW (Ideal.Quotient.mk P f)) := by
      rw [hfe]; exact ha.mul hgu
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (locC hPW) (W.map (Ideal.Quotient.mk P)) _).mp hfu
      (Ideal.mem_map_of_mem _ hfW)
  refine IsUnit.of_mul_eq_one (⟨fr P g / fr P f, frac_mem hg hf hfW⟩ : homLocRing P W) ?_
  apply Subtype.ext
  have h1 := hne hgW
  have h2 := hne hfW
  simp only [MulMemClass.coe_mul, OneMemClass.coe_one, hag]
  field_simp
end GroundTheory.Heights₂.Heights.NumbersDVR.HomLocLaurent
