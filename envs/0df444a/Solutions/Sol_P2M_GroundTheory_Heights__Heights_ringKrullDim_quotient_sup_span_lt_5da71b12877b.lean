-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_sup_span_lt_5da71b12877b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:51.207249+00:00
-- url     : https://prove2.me/submissions/fb05f3e1-c927-4409-b31b-7e437d92bccb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGoodPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameGraphGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegularOffHypersurface
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RingKrullDimQuotientMinimalPrimeAddOne

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
open MvPolynomial Filter Topology ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {R : Type*} [CommRing R] {L : Ideal R} {f : R} {d : ℕ}
    (hf : ∀ W ∈ L.minimalPrimes, f ∉ W) (hd : ∀ W ∈ L.minimalPrimes, ringKrullDim (R ⧸ W) = d) :
    ringKrullDim (R ⧸ (L ⊔ Ideal.span {f})) < d := by
  rw [ringKrullDim_quotient, Order.krullDim_lt_coe_iff]
  intro l
  have hLP : L ≤ l.head.1.asIdeal := fun x hx => l.head.2 (Ideal.mem_sup_left hx)
  have hfP : f ∈ l.head.1.asIdeal := l.head.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  obtain ⟨W, hW, hWP⟩ := Ideal.exists_minimalPrimes_le hLP
  let W' : PrimeSpectrum R := ⟨W, hW.1.1⟩
  have hlt : W' < l.head.1 := lt_of_le_of_ne hWP fun h => hf W hW (by rw [← h] at hfP; exact hfP)
  have h1 : (l.length : ℕ∞) ≤ Order.coheight l.head.1 := by
    exact Order.length_le_coheight_head (p := l.map Subtype.val (fun _ _ => id))
  have h2 : Order.coheight l.head.1 + 1 ≤ Order.coheight W' := Order.coheight_add_one_le hlt
  have hIci : Set.Ici W' = PrimeSpectrum.zeroLocus (R := R) (W : Set R) := by
    ext p
    exact Iff.rfl
  have h3 : ((Order.coheight W' : ℕ∞) : WithBot ℕ∞) = (d : WithBot ℕ∞) := by
    rw [Order.coheight_eq_krullDim_Ici, hIci, ← ringKrullDim_quotient]
    exact hd W hW
  have h3' : Order.coheight W' = (d : ℕ∞) := by exact_mod_cast h3
  have h4 : ((l.length + 1 : ℕ) : ℕ∞) ≤ (d : ℕ∞) := by
    rw [← h3']
    push_cast
    calc (l.length : ℕ∞) + 1 ≤ Order.coheight l.head.1 + 1 := by gcongr
      _ ≤ Order.coheight W' := h2
  have h5 : l.length + 1 ≤ d := by exact_mod_cast h4
  omega
end GroundTheory.Heights₂.Heights
