-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionComponents_proof_closed_c75def8ba395
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:08:43.612037+00:00
-- url     : https://prove2.me/submissions/b2c7400b-54d4-4011-b726-128b44d57567

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSectionComponents
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSectionComponents
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionComponents_exists_ringKrullDim_quotient_eq_187ebdf244d9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionComponents_ringKrullDim_quotient_add_one_le_of_lt_9c8b67d8c5d7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionComponents_ringKrullDim_quotient_add_one_eq_4d0eaf04e3ea

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
open SectionComponents
namespace GroundTheory.Heights₂.Heights
namespace SectionComponents
theorem _root_.solution : SectionComponents.Statement := by
  intro F _ n J f hequi hf

  have fwd : ∀ P ∈ J.minimalPrimes, ∀ W : Ideal (MvPolynomial (Fin n) F),
      W ∈ (P ⊔ Ideal.span {f}).minimalPrimes → W ∈ (J ⊔ Ideal.span {f}).minimalPrimes := by
    intro P hP W hW
    have _ : P.IsPrime := hP.1.1
    have _ : W.IsPrime := hW.1.1
    refine ⟨⟨hW.1.1, sup_le_sup_right hP.1.2 _ |>.trans hW.1.2⟩, ?_⟩
    rintro Q ⟨hQ, hJQ⟩ hQW
    obtain ⟨P', hP', hP'Q⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hJQ)
    have _ : P'.IsPrime := hP'.1.1
    obtain ⟨W', hW', hW'Q⟩ := Ideal.exists_minimalPrimes_le
      (sup_le hP'Q (le_sup_right.trans hJQ) : P' ⊔ Ideal.span {f} ≤ Q)
    have _ : W'.IsPrime := hW'.1.1
    have hW'W : W' ≤ W := hW'Q.trans hQW
    suffices W' = W by rw [← this]; exact hW'Q
    by_contra hne
    have hlt := ringKrullDim_quotient_add_one_le_of_lt (lt_of_le_of_ne hW'W hne)
    rw [ringKrullDim_quotient_add_one_eq (hf P hP) hW, hequi P hP P' hP',
      ← ringKrullDim_quotient_add_one_eq (hf P' hP') hW'] at hlt
    obtain ⟨m, hm⟩ := exists_ringKrullDim_quotient_eq W'
    rw [hm] at hlt
    have : m + 1 ≤ m := by exact_mod_cast hlt
    omega
  intro P hP W
  refine ⟨fun hW => ⟨fwd P hP W hW, le_sup_left.trans hW.1.2⟩, ?_⟩
  rintro ⟨hW, hPW⟩
  have _ : W.IsPrime := hW.1.1
  obtain ⟨W', hW', hW'W⟩ := Ideal.exists_minimalPrimes_le
    (sup_le hPW (le_sup_right.trans hW.1.2) : P ⊔ Ideal.span {f} ≤ W)
  have heq : W = W' := le_antisymm (hW.2 (fwd P hP W' hW').1 hW'W) hW'W
  rwa [heq]
end SectionComponents
end GroundTheory.Heights₂.Heights
