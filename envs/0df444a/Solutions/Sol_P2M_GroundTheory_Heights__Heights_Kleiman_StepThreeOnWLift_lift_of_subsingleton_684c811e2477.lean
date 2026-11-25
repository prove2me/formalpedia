-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_lift_of_subsingleton_684c811e2477
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:53:07.617873+00:00
-- url     : https://prove2.me/submissions/34a5a33a-86b5-4cf4-bae0-b5a5b9932090

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnWLift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsClaimSeq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSurjectiveClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWLift
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_mem_bdry_of_subsingleton_9fd4ef684c7c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_sgn_mul_self_cf0b42db396f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_sum_sgn_smul_sub_968772844063
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_sum_sgn_sum_sgn_548ea4db533a


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.StepThreeOnWLift
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.StepThreeOnWLift
theorem _root_.solution (Qc K : SubSystem S x Ω) (hKQ : ∀ I, K.sub I ≤ Qc.sub I)
    (hsub : Subsingleton (K.H 1)) (s : Chart x → Ω) (hs : ∀ I, s I ∈ Qc.sub I)
    (hcompat : ∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ K.sub I₂) :
    ∃ t ∈ Qc.secs, ∀ I, t - s I ∈ K.sub I := by

  have hmem : ∀ J : Cech.Idx (support x) 1,
      (∑ j : J.1.1, Cech.sgn J.1.1 j • (s (Cech.face J j).1 - s J.1)) ∈ K.sub J.1 :=
    fun J => Submodule.sum_mem _ fun j _ => zsmul_mem (hcompat _ _ (Cech.face_subset J j)) _
  let w : Cech.Cochain (fun I => K.sub I) 1 := fun J => ⟨_, hmem J⟩
  have hres : ∀ (I J : Chart x) (h : I.1 ⊆ J.1) (y : K.sub I), ((K.res I J h y : K.sub J) : Ω) = y :=
    fun _ _ _ _ => rfl
  have hw : w ∈ LinearMap.ker (Cech.d (fun I => K.sub I) K.res 1) := by
    rw [LinearMap.mem_ker]
    funext L
    apply Subtype.ext
    rw [Cech.d_apply]
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, hres, w,
      SurjectiveClosed.sum_sgn_smul_sub s, Pi.zero_apply, ZeroMemClass.coe_zero]
    exact SurjectiveClosed.sum_sgn_sum_sgn s L

  have hb : w ∈ Cech.bdry (fun I => K.sub I) K.res 1 :=
    SurjectiveClosed.mem_bdry_of_subsingleton hsub w hw
  obtain ⟨v, hv⟩ := LinearMap.mem_range.mp
    (show w ∈ LinearMap.range (Cech.d (fun I => K.sub I) K.res 0) from hb)

  classical
  let ψ : Finset (Fin (N + 1)) → Ω := fun T =>
    if h : (T.Nonempty ∧ T ⊆ support x) ∧ T.card = 0 + 1 then s ⟨T, h.1⟩ - (v ⟨⟨T, h.1⟩, h.2⟩ : Ω)
    else 0
  have hψ : ∀ I : Cech.Idx (support x) 0, ψ I.1.1 = s I.1 - (v I : Ω) := fun I => by
    simp only [ψ]
    rw [dif_pos ⟨I.1.2, I.2⟩]
  have hpair : ∀ J : Cech.Idx (support x) 1,
      ∑ j : J.1.1, Cech.sgn J.1.1 j • ψ (J.1.1.erase j) = 0 := by
    intro J
    have e := congrArg (fun z : Cech.Cochain (fun I => K.sub I) 1 => ((z J : K.sub J.1) : Ω)) hv
    rw [Cech.d_apply] at e
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, hres, w,
      SurjectiveClosed.sum_sgn_smul_sub s] at e
    have hj : ∀ j : J.1.1, ψ (J.1.1.erase j) = s (Cech.face J j).1 - (v (Cech.face J j) : Ω) :=
      fun j => hψ (Cech.face J j)
    simp only [hj, smul_sub, Finset.sum_sub_distrib]
    rw [e, sub_self]

  have hconst : ∀ a b : Fin (N + 1), x a ≠ 0 → x b ≠ 0 → ψ {a} = ψ {b} := by
    intro a b ha hb
    by_cases hab : a = b
    · rw [hab]
    have hsupp : ({a, b} : Finset (Fin (N + 1))) ⊆ support x := by
      rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨(mem_support x).mpr ha, (mem_support x).mpr hb⟩
    let J : Cech.Idx (support x) 1 :=
      ⟨⟨{a, b}, Finset.insert_nonempty _ _, hsupp⟩, Finset.card_pair hab⟩
    have e := hpair J
    have e2 := Cech.sum_sgn_of_card_two (J := ({a, b} : Finset (Fin (N + 1)))) (Finset.card_pair hab)
    rw [Finset.sum_coe_sort ({a, b} : Finset (Fin (N + 1)))
      (fun j => Cech.sgn {a, b} j • ψ (({a, b} : Finset (Fin (N + 1))).erase j))] at e
    rw [Finset.sum_pair hab] at e e2
    have ea : ({a, b} : Finset (Fin (N + 1))).erase a = {b} :=
      Finset.erase_insert (by simpa using hab)
    have eb : ({a, b} : Finset (Fin (N + 1))).erase b = {a} := by
      rw [Finset.pair_comm]
      exact Finset.erase_insert (by simpa using Ne.symm hab)
    rw [ea, eb, eq_neg_of_add_eq_zero_right e2, neg_smul, ← sub_eq_add_neg, ← smul_sub] at e
    have := congrArg (fun z => Cech.sgn {a, b} a • z) e
    simp only [smul_smul, SurjectiveClosed.sgn_mul_self, one_smul, smul_zero, sub_eq_zero] at this
    exact this.symm
  obtain ⟨t, ht⟩ : ∃ t : Ω, ∀ a, x a ≠ 0 → t = ψ {a} := by
    by_cases hne : ∃ i, x i ≠ 0
    · obtain ⟨i₀, hi₀⟩ := hne
      exact ⟨ψ {i₀}, fun a ha => hconst i₀ a hi₀ ha⟩
    · simp only [not_exists, not_not] at hne
      exact ⟨0, fun a ha => absurd (hne a) ha⟩

  have hdiff : ∀ I : Chart x, t - s I ∈ K.sub I := by
    intro I
    obtain ⟨a, haI⟩ := I.2.1
    have ha : x a ≠ 0 := (mem_support x).mp (I.2.2 haI)
    let c1 : Cech.Idx (support x) 0 :=
      ⟨⟨{a}, Finset.singleton_nonempty a, Finset.singleton_subset_iff.mpr (I.2.2 haI)⟩,
        Finset.card_singleton a⟩
    have hsub1 : c1.1.1 ⊆ I.1 := Finset.singleton_subset_iff.mpr haI
    rw [ht a ha, show ψ {a} = s c1.1 - (v c1 : Ω) from hψ c1,
      show s c1.1 - (v c1 : Ω) - s I = (s c1.1 - s I) - (v c1 : Ω) by ring]
    exact Submodule.sub_mem _ (hcompat c1.1 I hsub1) (K.mono c1.1 I hsub1 _ (v c1).2)
  refine ⟨t, ?_, hdiff⟩
  rw [SubSystem.secs, Submodule.mem_iInf]
  intro I
  have : t = s I + (t - s I) := by ring
  rw [this]
  exact Submodule.add_mem _ (hs I) (hKQ I (hdiff I))
end GroundTheory.Heights₂.Heights.Kleiman.StepThreeOnWLift
