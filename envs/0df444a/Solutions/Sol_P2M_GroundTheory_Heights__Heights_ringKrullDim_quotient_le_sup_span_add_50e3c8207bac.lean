-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_le_sup_span_add_50e3c8207bac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:39:12.604665+00:00
-- url     : https://prove2.me/submissions/e23d3b7c-a479-4940-b30e-36e63ebb4c93

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLocalDimGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLocalDimUpperZariski
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalDimDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceReducedAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceLocalDimGeneral

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
open MvPolynomial Matrix ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R)
    (hI : I ≠ ⊤) {d : ℕ} (t : Fin d → R) (ht : ∀ i, t i ∈ IsLocalRing.maximalIdeal R) :
    ringKrullDim (R ⧸ I) ≤ ringKrullDim (R ⧸ (I ⊔ Ideal.span (Set.range t))) + (d : ℕ) := by
  classical
  let s : Finset (R ⧸ I) := Finset.univ.image fun i => Ideal.Quotient.mk I (t i)
  have hs : Ideal.span (s : Set (R ⧸ I)) = (Ideal.span (Set.range t)).map (Ideal.Quotient.mk I) := by
    rw [Ideal.map_span]
    congr 1
    ext x
    simp [s]
  have hjac : (Ideal.span (Set.range t)).map (Ideal.Quotient.mk I) ≤ Ring.jacobson (R ⧸ I) := by
    rw [← Ideal.jacobson_bot, ← Ideal.map_quotient_self I,
      ← Ideal.map_jacobson_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]),
      IsLocalRing.jacobson_eq_maximalIdeal I hI]
    refine Ideal.map_mono ?_
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact ht i
  have hkey := ringKrullDim_le_ringKrullDim_quotient_add_card s
    fun x hx => hjac (hs ▸ Ideal.subset_span hx)
  rw [hs, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup I _)] at hkey
  refine hkey.trans ?_
  gcongr
  exact_mod_cast Finset.card_image_le.trans (by simp)
end GroundTheory.Heights₂.Heights
