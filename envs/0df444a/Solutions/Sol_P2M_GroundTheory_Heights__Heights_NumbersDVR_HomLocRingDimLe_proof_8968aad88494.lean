-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_proof_8968aad88494
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:14:28.55081+00:00
-- url     : https://prove2.me/submissions/d3e9085b-eaae-45b8-bfc4-7ed690f0b770

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultiHomogPrimeCriterion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingDimLe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_primeAbove_isPrime_bad04a5b82d8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_le_primeAbove_e4ed4df29902
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_primeAbove_le_3a76e9500592
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_primeAbove_strictMono_946debd1cd96

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
universe u
open HomLocRingDimLe
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace HomLocRingDimLe
theorem _root_.solution (h₁ : HomLocRingMem.Statement.{u})
    (h₂ : HomLocRingIsLocal.Statement.{u}) : HomLocRingDimLe.Statement.{u} := by
  intro R _ K _ _ ι _ P W _ hP hW hrel hPW
  haveI := hW
  let Φ : PrimeSpectrum (homLocRing P W) → PrimeSpectrum (MRing ι R ⧸ P) := fun q =>
    haveI := primeAbove_isPrime hPW hW hrel q.asIdeal
    ⟨(primeAbove hPW hW hrel q.asIdeal).map (Ideal.Quotient.mk P),
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact le_primeAbove hP hPW hW hrel q.asIdeal)⟩
  have hΦ : StrictMono Φ := by
    intro q q' hlt
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hlt ⊢
    have hlt' := primeAbove_strictMono h₁ hPW hW hrel hlt
    have hPq := le_primeAbove hP hPW hW hrel q.asIdeal
    have hPq' := le_primeAbove hP hPW hW hrel q'.asIdeal
    change (primeAbove hPW hW hrel q.asIdeal).map (Ideal.Quotient.mk P) <
      (primeAbove hPW hW hrel q'.asIdeal).map (Ideal.Quotient.mk P)
    refine lt_of_le_of_ne (Ideal.map_mono hlt'.le) fun heq => hlt'.ne ?_
    have := congrArg (Ideal.comap (Ideal.Quotient.mk P)) heq
    rwa [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
      Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.mpr hPq, sup_eq_left.mpr hPq'] at this
  haveI hWq : (W.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hPW)
  let w : PrimeSpectrum (MRing ι R ⧸ P) := ⟨W.map (Ideal.Quotient.mk P), hWq⟩
  have hΦw : ∀ q, Φ q ≤ w := fun q => by
    rw [← PrimeSpectrum.asIdeal_le_asIdeal]
    exact Ideal.map_mono (primeAbove_le h₂ hPW hW hrel q.asIdeal)
  rw [show (W.map (Ideal.Quotient.mk P)).height = Order.height w from
    PrimeSpectrum.height_eq_orderHeight w]
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun l => ?_
  have h1 : ((l.map Φ hΦ).length : ℕ∞) ≤ Order.height ((l.map Φ hΦ).last) :=
    Order.length_le_height_last
  rw [LTSeries.last_map] at h1
  have h2 := h1.trans (Order.height_mono (hΦw l.last))
  have h3 : (l.map Φ hΦ).length = l.length := rfl
  rw [h3] at h2
  exact_mod_cast h2
end HomLocRingDimLe
end GroundTheory.Heights₂.Heights.NumbersDVR
