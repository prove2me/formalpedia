-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalGermIntegrallyClosed_proof_ac597e3f4f2c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:03:41.947399+00:00
-- url     : https://prove2.me/submissions/00a2b380-dac5-43d7-8937-a91785b3ed9a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalGermIntegrallyClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiAnalyticNormality
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRueckertNullstellensatz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalGermIntegrallyClosed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalGermIntegrallyClosed_analyticAt_of_differentiableOn_71078bf4599b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalGermIntegrallyClosed_toGerm_surjective_5df4007014f9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalGermIntegrallyClosed_toGerm_eq_iff_6da30c5633ae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalGermIntegrallyClosed_vanish_of_mem_map_7d7b72ea45e9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalGermIntegrallyClosed_exists_eq_mul_of_integral_relation_9a59bf892232

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
theorem _root_.solution (hRueckert : RueckertNullstellensatz.Statement)
    (hZariski : ZariskiAnalyticNormality.Statement) : NormalGermIntegrallyClosed.Statement := by
  intro σ _ I w N F G d a hI hIc hw hN hwN hF hG ha hGnz hrel
  have hFa : AnalyticAt ℂ F w := analyticAt_of_differentiableOn hN hF hwN
  have hGa : AnalyticAt ℂ G w := analyticAt_of_differentiableOn hN hG hwN
  have haa : ∀ j, AnalyticAt ℂ (a j) w := fun j => analyticAt_of_differentiableOn hN (ha j) hwN

  obtain ⟨k, p, hp⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian I)
  have hpI : ∀ i, p i ∈ I := fun i => hp ▸ Submodule.subset_span ⟨i, rfl⟩
  have hZp : ∀ z, (∀ i, eval z (p i) = 0) → z ∈ zeroSetIn I := by
    intro z hz q hq
    have hle : I ≤ RingHom.ker (eval z) := by
      rw [← hp]
      exact Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hz i)
    exact RingHom.mem_ker.1 (hle hq)

  obtain ⟨hJ, hJc⟩ := hZariski σ I w hI hIc hw
  let J := I.map (polyGerm w)
  have : J.IsPrime := hJ
  let S := holGerms w ⧸ J
  have : IsIntegrallyClosed S := hJc
  let π : anFun w →+* S := (Ideal.Quotient.mk J).comp (toGerm w)
  have hπ0 : ∀ u : anFun w, π u = 0 → ∀ᶠ z in 𝓝[zeroSetIn I] w, (u : (σ → ℂ) → ℂ) z = 0 :=
    fun u hu => vanish_of_mem_map (Ideal.Quotient.eq_zero_iff_mem.1 hu)
  have hπpoly : ∀ q ∈ I, π ⟨fun z => eval z q, analyticAt_eval_polynomial w q⟩ = 0 := fun q hq =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hq)
  have hπeq : ∀ u v : anFun w, (u : (σ → ℂ) → ℂ) =ᶠ[𝓝 w] v → π u = π v := fun u v h => by
    simp only [π, RingHom.comp_apply, toGerm_eq_iff.2 h]

  let FA : anFun w := ⟨F, hFa⟩
  let GA : anFun w := ⟨G, hGa⟩
  let aA : Fin d → anFun w := fun j => ⟨a j, haa j⟩
  let PA : anFun w := FA ^ d + ∑ j, aA j * FA ^ (j : ℕ) * GA ^ (d - (j : ℕ))
  have hPA : ∀ z, (PA : (σ → ℂ) → ℂ) z =
      F z ^ d + ∑ j, a j z * F z ^ (j : ℕ) * G z ^ (d - (j : ℕ)) := by
    intro z
    simp [PA, FA, GA, aA, Finset.sum_apply]

  have hGS : π GA ≠ 0 := by
    intro h
    exact hGnz (eventually_nhdsWithin_iff.1 (hπ0 GA h))

  have hvan : ∀ᶠ z in 𝓝 w, (∀ i, eval z (p i) = 0) → (PA : (σ → ℂ) → ℂ) z * G z = 0 := by
    filter_upwards [hN.mem_nhds hwN] with z hzN hz
    by_cases hG0 : G z = 0
    · rw [hG0, mul_zero]
    · rw [hPA, hrel z ⟨⟨hZp z hz, hzN⟩, hG0⟩, zero_mul]
  obtain ⟨m, h, hm, hh, hgm⟩ := hRueckert σ w k (fun i z => eval z (p i))
    (fun z => (PA : (σ → ℂ) → ℂ) z * G z) (fun i => analyticAt_eval_polynomial w (p i))
    (PA.2.mul hGa) hvan
  let hA : Fin k → anFun w := fun i => ⟨h i, hh i⟩
  let pA : Fin k → anFun w := fun i => ⟨fun z => eval z (p i), analyticAt_eval_polynomial w (p i)⟩
  have hprod : π ((PA * GA) ^ m) = π (∑ i, hA i * pA i) := by
    apply hπeq
    filter_upwards [hgm] with z hz
    simpa [hA, pA, GA, Finset.sum_apply, mul_pow] using hz
  have hPS : π PA = 0 := by
    have h1 : (π PA * π GA) ^ m = 0 := by
      rw [← map_mul, ← map_pow, hprod, map_sum]
      exact Finset.sum_eq_zero fun i _ => by rw [map_mul, hπpoly _ (hpI i), mul_zero]
    exact (mul_eq_zero.1 ((pow_eq_zero_iff (Nat.pos_iff_ne_zero.1 hm)).1 h1)).resolve_right hGS

  have : IsDomain S := Ideal.Quotient.isDomain J
  obtain ⟨y, hy⟩ := exists_eq_mul_of_integral_relation (π FA) (π GA) (fun j => π (aA j)) hGS (by
    rw [← hPS]
    simp only [PA, map_add, map_sum, map_mul, map_pow])
  obtain ⟨φ, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨HA, rfl⟩ := toGerm_surjective w φ
  have hdiff : π (FA - GA * HA) = 0 := by
    rw [map_sub, map_mul, hy]
    exact sub_self _
  have hv := eventually_nhdsWithin_iff.1 (hπ0 _ hdiff)
  obtain ⟨V, hV, hVo, hwV⟩ := eventually_nhds_iff.1 (hv.and HA.2.eventually_analyticAt)
  refine ⟨V, hVo, hwV, HA, fun z hz => (hV z hz).2.differentiableAt.differentiableWithinAt, ?_⟩
  rintro z ⟨hzZ, hzV⟩
  have h3 := (hV z hzV).1 hzZ
  change F z - G z * (HA : (σ → ℂ) → ℂ) z = 0 at h3
  exact sub_eq_zero.1 h3
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.NormalGermIntegrallyClosed
