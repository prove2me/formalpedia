-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ParametrisationSheetsConnected_proof_962625c367da
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:59:58.552942+00:00
-- url     : https://prove2.me/submissions/5a722b3b-98c3-4b8e-b6fe-e97a6d1761ff

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParametrisationSheetsConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetPieceProductAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetPieceReachesCentre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PParametrisationSheetsConnected
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_clm_ne_zero_of_countable_ac1430d3ce4d

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
open Topology Filter MeasureTheory
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace ParametrisationSheetsConnected
theorem _root_.solution (h₁ : SheetPieceProductAnalytic.Statement)
    (h₂ : SheetPieceReachesCentre.Statement) : ParametrisationSheetsConnected.Statement := by
  classical
  intro σ _ X w B d A D δ N hP hirr
  obtain ⟨hB, hwXB, hD, -, hmaps, -, -, -, -, hcard, -, hdense⟩ := id hP
  set S := {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} with hS
  by_contra hnc
  rw [IsPreconnected] at hnc
  push Not at hnc
  obtain ⟨u, v, hu, hv, hSuv, hSu, hSv, hdisj⟩ := hnc
  have hdisj' : S ∩ (v ∩ u) = ∅ := by rwa [Set.inter_comm v u]
  have hSvu : S ⊆ v ∪ u := by rwa [Set.union_comm]
  have hwu := h₂ σ X w B d A D δ N u v hP hu hv hSuv hdisj hSu
  have hwv := h₂ σ X w B d A D δ N v u hP hv hu hSvu hdisj' hSv
  obtain ⟨p, hpS, hpw⟩ := mem_closure_iff_seq_limit.1 hwu
  obtain ⟨q, hqS, hqw⟩ := mem_closure_iff_seq_limit.1 hwv

  have hfin : ∀ (U' : Set (σ → ℂ)), ∀ x ∈ S, {x' | x' ∈ X ∩ B ∧ x' ∈ U' ∧ A x' = A x}.Finite :=
    fun U' x hx => (Set.finite_of_encard_eq_coe (hcard (A x) (hmaps hx.1) hx.2)).subset
      fun x' hx' => ⟨hx'.1, hx'.2.2⟩
  set T : Set (σ → ℂ) :=
    (⋃ n, (fun x' => p n - x') '' {x' | x' ∈ X ∩ B ∧ x' ∈ v ∧ A x' = A (p n)}) ∪
      ⋃ n, (fun x' => q n - x') '' {x' | x' ∈ X ∩ B ∧ x' ∈ u ∧ A x' = A (q n)} with hT
  have hTc : T.Countable :=
    (Set.countable_iUnion fun n => ((hfin v (p n) (hpS n).1).image _).countable).union
      (Set.countable_iUnion fun n => ((hfin u (q n) (hqS n).1).image _).countable)
  have hT0 : (0 : σ → ℂ) ∉ T := by
    have key : ∀ (r : σ → ℂ) (U₁ U₂ : Set (σ → ℂ)), r ∈ S ∩ U₁ → S ∩ (U₁ ∩ U₂) = ∅ →
        ∀ x' ∈ {x' | x' ∈ X ∩ B ∧ x' ∈ U₂ ∧ A x' = A r}, r - x' ≠ 0 := by
      intro r U₁ U₂ hr hd x' hx' h0
      have hrx : r = x' := sub_eq_zero.1 h0
      have hx'S : x' ∈ S := ⟨hx'.1, by rw [hx'.2.2]; exact hr.1.2⟩
      exact (Set.eq_empty_iff_forall_notMem.1 hd x') ⟨hx'S, hrx ▸ hr.2, hx'.2.1⟩
    rintro (h | h) <;> obtain ⟨n, x', hx', hx0⟩ := Set.mem_iUnion.1 h
    · exact key (p n) u v (hpS n) hdisj x' hx' hx0
    · exact key (q n) v u (hqS n) hdisj' x' hx' hx0
  obtain ⟨ℓ, hℓ⟩ := exists_clm_ne_zero_of_countable hTc hT0
  obtain ⟨f, hfan, hfeq⟩ := h₁ σ X w B d A D δ N u v ℓ hP hu hv hSuv hdisj
  obtain ⟨g, hgan, hgeq⟩ := h₁ σ X w B d A D δ N v u ℓ hP hv hu hSvu hdisj'

  have hzero : ∀ (U' : Set (σ → ℂ)) (F : (σ → ℂ) → ℂ),
      (∀ z, A z ∈ D → δ (A z) ≠ 0 →
        F z = ∏ᶠ x ∈ {x | x ∈ X ∩ B ∧ x ∈ U' ∧ A x = A z}, (ℓ z - ℓ x)) →
      ∀ x ∈ S, x ∈ U' → F x = 0 := by
    intro U' F hF x hx hxU
    rw [hF x (hmaps hx.1) hx.2, finprod_mem_eq_finite_toFinset_prod _ (hfin U' x hx)]
    exact Finset.prod_eq_zero ((hfin U' x hx).mem_toFinset.2 ⟨hx.1, hxU, rfl⟩) (sub_self _)

  have hne : ∀ (U' : Set (σ → ℂ)) (F : (σ → ℂ) → ℂ) (r : σ → ℂ),
      (∀ z, A z ∈ D → δ (A z) ≠ 0 →
        F z = ∏ᶠ x ∈ {x | x ∈ X ∩ B ∧ x ∈ U' ∧ A x = A z}, (ℓ z - ℓ x)) → r ∈ S →
      (∀ x' ∈ {x' | x' ∈ X ∩ B ∧ x' ∈ U' ∧ A x' = A r}, r - x' ∈ T) → F r ≠ 0 := by
    intro U' F r hF hr hrT
    rw [hF r (hmaps hr.1) hr.2, finprod_mem_eq_finite_toFinset_prod _ (hfin U' r hr)]
    refine Finset.prod_ne_zero_iff.2 fun x' hx' => ?_
    rw [← map_sub]
    exact hℓ _ (hrT x' ((hfin U' r hr).mem_toFinset.1 hx'))
  have hfq : ∀ n, f (q n) ≠ 0 := fun n => hne u f (q n) hfeq (hqS n).1
    fun x' hx' => Or.inr (Set.mem_iUnion.2 ⟨n, x', hx', rfl⟩)
  have hgp : ∀ n, g (p n) ≠ 0 := fun n => hne v g (p n) hgeq (hpS n).1
    fun x' hx' => Or.inl (Set.mem_iUnion.2 ⟨n, x', hx', rfl⟩)

  have hprod : ∀ z ∈ X ∩ B, f z * g z = 0 := by
    intro z hz
    have hc : ContinuousAt (fun z => f z * g z) z :=
      (hfan z (hmaps hz)).continuousAt.mul (hgan z (hmaps hz)).continuousAt
    have := mem_closure_iff_nhdsWithin_neBot.1 (hdense hz)
    have h2 : (fun z => f z * g z) =ᶠ[𝓝[S] z] fun _ => 0 :=
      eventually_nhdsWithin_of_forall fun x hx => by
        rcases hSuv hx with hxu | hxv
        · simp [hzero u f hfeq x hx hxu]
        · simp [hzero v g hgeq x hx hxv]
    exact tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' h2.symm)
  have hw : A w ∈ D := hmaps hwXB
  have hev : ∀ᶠ z in 𝓝 w, z ∈ X → f z * g z = 0 := by
    filter_upwards [hB.mem_nhds hwXB.2] with z hzB hzX using hprod z ⟨hzX, hzB⟩
  rcases hirr.2 f g (hfan w hw) (hgan w hw) hev with hf0 | hg0
  · obtain ⟨n, hn⟩ := (hqw.eventually hf0).exists
    exact hfq n (hn (hqS n).1.1.1)
  · obtain ⟨n, hn⟩ := (hpw.eventually hg0).exists
    exact hgp n (hn (hpS n).1.1.1)
end ParametrisationSheetsConnected
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
