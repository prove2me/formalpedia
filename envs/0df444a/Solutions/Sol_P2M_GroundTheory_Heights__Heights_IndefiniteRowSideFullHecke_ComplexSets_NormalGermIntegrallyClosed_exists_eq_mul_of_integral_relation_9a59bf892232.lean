-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalGermIntegrallyClosed_exists_eq_mul_of_integral_relation_9a59bf892232
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:31:58.734044+00:00
-- url     : https://prove2.me/submissions/4ef7e2d5-a718-48ac-9dca-500ad75766b3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalGermIntegrallyClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiAnalyticNormality
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRueckertNullstellensatz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalGermIntegrallyClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Topology Filter
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.NormalGermIntegrallyClosed
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.NormalGermIntegrallyClosed
theorem _root_.solution {S : Type*} [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    {d : ℕ} (f g : S) (a : Fin d → S) (hg : g ≠ 0)
    (hrel : f ^ d + ∑ j, a j * f ^ (j : ℕ) * g ^ (d - (j : ℕ)) = 0) : ∃ y, f = g * y := by
  let K := FractionRing S
  have hinj : Function.Injective (algebraMap S K) := IsFractionRing.injective S K
  have hrelK : algebraMap S K f ^ d + ∑ j, algebraMap S K (a j) * algebraMap S K f ^ (j : ℕ) *
      algebraMap S K g ^ (d - (j : ℕ)) = 0 := by
    have h2 := congrArg (algebraMap S K) hrel
    simp only [map_add, map_sum, map_mul, map_pow, map_zero] at h2
    exact h2
  have hg0 : algebraMap S K g ≠ 0 := fun h0 => hg (hinj (by rw [h0, map_zero]))
  generalize hfK : algebraMap S K f = fK at hrelK
  generalize hgK : algebraMap S K g = gK at hrelK hg0
  have hint : IsIntegral S (fK / gK) := by
    refine ⟨Polynomial.X ^ d + ∑ j : Fin d, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ),
      Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _), ?_⟩
    have hterm : ∀ j : Fin d, algebraMap S K (a j) * (fK / gK) ^ (j : ℕ) =
        algebraMap S K (a j) * fK ^ (j : ℕ) * gK ^ (d - (j : ℕ)) / gK ^ d := by
      intro j
      rw [eq_div_iff (pow_ne_zero _ hg0), div_pow,
        show gK ^ d = gK ^ (j : ℕ) * gK ^ (d - (j : ℕ)) by rw [← pow_add, Nat.add_sub_cancel' j.2.le]]
      have hj : gK ^ (j : ℕ) ≠ 0 := pow_ne_zero _ hg0
      rw [show algebraMap S K (a j) * (fK ^ (j : ℕ) / gK ^ (j : ℕ)) * (gK ^ (j : ℕ) * gK ^ (d - (j : ℕ))) =
          algebraMap S K (a j) * fK ^ (j : ℕ) * gK ^ (d - (j : ℕ)) * (gK ^ (j : ℕ) / gK ^ (j : ℕ)) by ring,
        div_self hj, mul_one]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
      Polynomial.eval₂_mul, Polynomial.eval₂_C]
    rw [Finset.sum_congr rfl fun j _ => hterm j, div_pow, ← Finset.sum_div, ← add_div, hrelK, zero_div]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  refine ⟨y, hinj ?_⟩
  rw [map_mul, hy, hfK, hgK, mul_div_assoc', eq_div_iff hg0, mul_comm]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.NormalGermIntegrallyClosed
