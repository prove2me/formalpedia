-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_QuotientHeightAddOne_proof_4b05c001e684
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:07:06.822559+00:00
-- url     : https://prove2.me/submissions/6423c589-7067-4474-aaca-e7d507f1c2c7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsDimensionInequalitySteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PQuotientHeightAddOne

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
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace QuotientHeightAddOne
theorem _root_.solution : QuotientHeightAddOne.Statement := by
  intro R _ _ I hI P _
  let φ : PrimeSpectrum (R ⧸ I) → PrimeSpectrum R := PrimeSpectrum.comap (Ideal.Quotient.mk I)
  have hφ : StrictMono φ := RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective
  let z : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩

  have hz : ∀ q : PrimeSpectrum (R ⧸ I), z < φ q := by
    intro q
    refine lt_of_le_of_ne (show z.asIdeal ≤ (φ q).asIdeal from bot_le) fun h => hI ?_
    have hle : I ≤ (φ q).asIdeal := by
      intro x hx
      change Ideal.Quotient.mk I x ∈ q.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact q.asIdeal.zero_mem
    rw [← h] at hle
    exact le_bot_iff.mp hle
  let p : PrimeSpectrum (R ⧸ I) := ⟨P, ‹_›⟩
  have h1 : P.height = Order.height p := PrimeSpectrum.height_eq_orderHeight p
  have h2 : (P.comap (Ideal.Quotient.mk I)).height = Order.height (φ p) :=
    PrimeSpectrum.height_eq_orderHeight (φ p)
  have hne : Nonempty { l : LTSeries (PrimeSpectrum (R ⧸ I)) // l.last = p } :=
    ⟨⟨RelSeries.singleton _ p, rfl⟩⟩
  rw [h1, h2, Order.height_eq_iSup_last_eq p, iSup_subtype', ENat.iSup_add, iSup_le_iff]
  rintro ⟨l, hl⟩
  let l' : LTSeries (PrimeSpectrum R) :=
    (l.map φ hφ).cons z (by simpa using hz l.head)
  have hlast : l'.last = φ p := by simp [l', hl]
  have := Order.length_le_height (p := l') hlast.le
  simpa [l'] using this
end QuotientHeightAddOne
end GroundTheory.Heights₂.Heights.NumbersDVR
