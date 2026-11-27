-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitivePresentationCover_proof_d876565c9151
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:59:49.119815+00:00
-- url     : https://prove2.me/submissions/65326b6e-6cfe-40c9-bc23-68bfbe43f35b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitivePresentationCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSeparateWeierstrassDivision
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PevEqZeroOfPresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitivePresentationCover
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_centred_clear_b016ba46592f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_prod_pow_clear_c9bb2f9a0e22
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_clm_apply_eq_sum_87e002e356bd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsGermCombination_generator_24a5cec3a116
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsGermCombination_pow_sub_pow_644ead9187f5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsGermCombination_prod_sub_prod_8bb61e4934c0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsGermCombination_sub_3625d3b8717d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsGermCombination_sum_1b3054654731
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticAt_pev_comp_d9a9192a1847
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_evalAt_apply_3dcf9480b1b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_C_84d2b4612e3e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_X_1c14eb6f22af
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_eq_zero_of_presentation_ffd9ef385cba
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_roots_near_of_centred_22c697db77d1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_evalAt_apply_3dcf9480b1b3
attribute [local simp] P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_C_84d2b4612e3e
attribute [local simp] P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_X_1c14eb6f22af



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Polynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace PrimitivePresentationCover
theorem _root_.solution (hdiv : SeparateWeierstrassDivision.Statement) :
    PrimitivePresentationCover.Statement := by
  intro σ _ w k p d A ℓ N c δ hp hP W hW
  classical
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact Eventually.of_forall fun y _ => ⟨Fin.elim0, fun j => j.elim0, fun a => a.elim0⟩
  obtain ⟨hc, hδ, -, -, h3, h4, h5⟩ := id hP
  have hcoord : ∀ m : σ, AnalyticAt ℂ (fun z : σ → ℂ => z m) w := fun m =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) m).analyticAt w
  have hδA : AnalyticAt ℂ (fun z => δ (A z)) w := hδ.comp (A.analyticAt w)
  choose Mm a ha hga using fun m => h4 (fun z => z m) (hcoord m)
  choose n b hb hgb hb0 using fun m => h5 (fun z => z m) (hcoord m)
  set M : ℕ := ∑ m, Mm m with hMdef
  have hMm : ∀ m, Mm m ≤ M := fun m =>
    Finset.single_le_sum (fun i _ => Nat.zero_le (Mm i)) (Finset.mem_univ m)

  let δ' : analyticSubring (A w) := ⟨δ, hδ⟩
  let qp : σ → (analyticSubring (A w))[X] := fun m =>
    C (δ' ^ (M - Mm m)) * ∑ j : Fin N, C (⟨a m j, ha m j⟩ : analyticSubring (A w)) * X ^ (j : ℕ)
  have hqp : ∀ m y t, pev y t (qp m) = δ y ^ (M - Mm m) * ∑ j : Fin N, a m j y * t ^ (j : ℕ) := by
    intro m y t
    simp [qp, δ', map_sum]
  have hQan : ∀ m, AnalyticAt ℂ (fun z => pev (A z) (ℓ z) (qp m)) w := fun m =>
    analyticAt_pev_comp w A ℓ (qp m)
  have hDan : ∀ m, AnalyticAt ℂ (fun z => δ (A z) ^ M * z m) w := fun m => (hδA.pow M).mul (hcoord m)
  have hQD : ∀ m, IsGermCombination w p (fun z => pev (A z) (ℓ z) (qp m) - δ (A z) ^ M * z m) := by
    intro m
    refine (IsGermCombination.mul_left (hδA.pow (M - Mm m)) (hga m)).neg.congr
      (Eventually.of_forall fun z => ?_)
    have e : δ (A z) ^ M = δ (A z) ^ (M - Mm m) * δ (A z) ^ Mm m := by
      rw [← pow_add, Nat.sub_add_cancel (hMm m)]
    simp only [Pi.pow_apply]
    rw [hqp, e]
    ring

  let H1 : σ → (analyticSubring (A w))[X] := fun m =>
    qp m ^ n m + ∑ j : Fin (n m),
      C ((⟨b m j, hb m j⟩ : analyticSubring (A w)) * δ' ^ (M * (n m - j))) * qp m ^ (j : ℕ)
  have hpevH1 : ∀ m y t, pev y t (H1 m) = pev y t (qp m) ^ n m +
      ∑ j : Fin (n m), b m j y * δ y ^ (M * (n m - j)) * pev y t (qp m) ^ (j : ℕ) := by
    intro m y t
    simp [H1, δ', map_sum]
  have hE1 : ∀ m, ∀ᶠ y in 𝓝 (A w), ∀ t : ℂ, t ^ N + ∑ j, c j y * t ^ (j : ℕ) = 0 →
      pev y t (H1 m) = 0 := by
    intro m
    refine pev_eq_zero_of_presentation hP (H1 m) ?_
    have e1 := IsGermCombination.mul_left (hδA.pow (M * n m)) (hgb m)
    have e2 := IsGermCombination.pow_sub_pow (hQan m) (hDan m) (hQD m) (n m)
    have e3 : IsGermCombination w p (fun z => ∑ j : Fin (n m), b m j (A z) * δ (A z) ^ (M * (n m - j)) *
        (pev (A z) (ℓ z) (qp m) ^ (j : ℕ) - (δ (A z) ^ M * z m) ^ (j : ℕ))) :=
      IsGermCombination.sum _ fun j _ => IsGermCombination.mul_left
        (((hb m j).comp (A.analyticAt w)).mul (hδA.pow _))
        (IsGermCombination.pow_sub_pow (hQan m) (hDan m) (hQD m) j)
    refine ((e1.add e2).add e3).congr (Eventually.of_forall fun z => ?_)
    have hc := centred_clear (fun j => b m j (A z)) M (δ (A z)) (z m)
    simp only [Pi.pow_apply]
    rw [hpevH1, ← hc]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring

  let ev : σ → σ → ℂ := fun m j => if m = j then 1 else 0
  let Hlin : ((σ → ℂ) →L[ℂ] ℂ) → (analyticSubring (A w))[X] → (analyticSubring (A w))[X] :=
    fun lam L => ∑ m, C (⟨fun _ => lam (ev m), analyticAt_const⟩ : analyticSubring (A w)) * qp m -
      C (δ' ^ M) * L
  have hpevHlin : ∀ lam L y t, pev y t (Hlin lam L) =
      ∑ m, lam (ev m) * pev y t (qp m) - δ y ^ M * pev y t L := by
    intro lam L y t
    simp [Hlin, δ', map_sum]
  have hElin : ∀ (lam : (σ → ℂ) →L[ℂ] ℂ) (L : (analyticSubring (A w))[X]),
      (∀ z, pev (A z) (ℓ z) L = lam z) →
      ∀ᶠ y in 𝓝 (A w), ∀ t : ℂ, t ^ N + ∑ j, c j y * t ^ (j : ℕ) = 0 → pev y t (Hlin lam L) = 0 := by
    intro lam L hL
    refine pev_eq_zero_of_presentation hP _ ?_
    have e : IsGermCombination w p (fun z => ∑ m, lam (ev m) *
        (pev (A z) (ℓ z) (qp m) - δ (A z) ^ M * z m)) :=
      IsGermCombination.sum _ fun m _ => IsGermCombination.mul_left analyticAt_const (hQD m)
    refine e.congr (Eventually.of_forall fun z => ?_)
    rw [hpevHlin, hL, clm_apply_eq_sum lam z, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  let coordP : Fin d → (analyticSubring (A w))[X] := fun r =>
    C (⟨fun y => y r, (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) r).analyticAt _⟩ :
      analyticSubring (A w))
  have hE2 : ∀ r : Fin d, ∀ᶠ y in 𝓝 (A w), ∀ t : ℂ, t ^ N + ∑ j, c j y * t ^ (j : ℕ) = 0 →
      pev y t (Hlin ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) r).comp A) (coordP r)) = 0 :=
    fun r => hElin _ _ fun z => by simp [coordP]
  have hE3 : ∀ᶠ y in 𝓝 (A w), ∀ t : ℂ, t ^ N + ∑ j, c j y * t ^ (j : ℕ) = 0 → pev y t (Hlin ℓ X) = 0 :=
    hElin ℓ X fun z => by simp

  choose v r hv hr hev using fun i => hdiv σ d (A w) w n b (fun q => p i q.2) hb hb0
    ((hp i).comp analyticAt_snd)
  set Ntot : ℕ := ∑ m, n m with hNtot
  have hα : ∀ α : (m : σ) → Fin (n m), ∑ m, (α m : ℕ) ≤ Ntot := fun α =>
    Finset.sum_le_sum fun m _ => (α m).2.le
  let H4 : Fin k → (analyticSubring (A w))[X] := fun i =>
    ∑ α : (m : σ) → Fin (n m), C ((⟨r i α, hr i α⟩ : analyticSubring (A w)) *
      δ' ^ (M * (Ntot - ∑ m, (α m : ℕ)))) * ∏ m, qp m ^ (α m : ℕ)
  have hpevH4 : ∀ i y t, pev y t (H4 i) = ∑ α : (m : σ) → Fin (n m),
      r i α y * δ y ^ (M * (Ntot - ∑ m, (α m : ℕ))) * ∏ m, pev y t (qp m) ^ (α m : ℕ) := by
    intro i y t
    simp [H4, δ', map_sum, map_prod]
  have hrem : ∀ i (y : Fin d → ℂ) (e : ℂ) (x : σ → ℂ), ∑ α : (m : σ) → Fin (n m),
      r i α y * e ^ (M * (Ntot - ∑ m, (α m : ℕ))) * ∏ m, (e ^ M * x m) ^ (α m : ℕ) =
      e ^ (M * Ntot) * ∑ α : (m : σ) → Fin (n m), r i α y * ∏ m, x m ^ (α m : ℕ) := by
    intro i y e x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [prod_pow_clear, mul_assoc, ← mul_assoc (e ^ _), ← pow_add, ← mul_add,
      Nat.sub_add_cancel (hα α)]
    ring
  have hdiag : Tendsto (fun z : σ → ℂ => (A z, z)) (𝓝 w) (𝓝 (A w, w)) :=
    (A.continuous.prodMk continuous_id).tendsto w
  have hdiagA : AnalyticAt ℂ (fun z : σ → ℂ => (A z, z)) w := (A.analyticAt w).prod analyticAt_id
  have hE4 : ∀ i, ∀ᶠ y in 𝓝 (A w), ∀ t : ℂ, t ^ N + ∑ j, c j y * t ^ (j : ℕ) = 0 →
      pev y t (H4 i) = 0 := by
    intro i
    refine pev_eq_zero_of_presentation hP (H4 i) ?_

    have hR : IsGermCombination w p (fun z => ∑ α : (m : σ) → Fin (n m),
        r i α (A z) * ∏ m, z m ^ (α m : ℕ)) := by
      have hG : IsGermCombination w p (fun z => ∑ m, v i m (A z, z) *
          (z m ^ n m + ∑ j, b m j (A z) * z m ^ (j : ℕ))) :=
        IsGermCombination.sum _ fun m _ => IsGermCombination.mul_left
          (AnalyticAt.comp (g := v i m) (f := fun z : σ → ℂ => (A z, z)) (hv i m) hdiagA) (hgb m)
      refine ((IsGermCombination.generator i).sub hG).congr ?_
      filter_upwards [hdiag.eventually (hev i)] with z hz
      rw [hz]
      ring
    have e1 := IsGermCombination.mul_left (hδA.pow (M * Ntot)) hR
    have e2 : IsGermCombination w p (fun z => ∑ α : (m : σ) → Fin (n m),
        r i α (A z) * δ (A z) ^ (M * (Ntot - ∑ m, (α m : ℕ))) *
          (∏ m, pev (A z) (ℓ z) (qp m) ^ (α m : ℕ) - ∏ m, (δ (A z) ^ M * z m) ^ (α m : ℕ))) :=
      IsGermCombination.sum _ fun α _ => IsGermCombination.mul_left
        (((hr i α).comp (A.analyticAt w)).mul (hδA.pow _))
        (IsGermCombination.prod_sub_prod _ (fun m => (hQan m).pow _) (fun m => (hDan m).pow _)
          fun m => IsGermCombination.pow_sub_pow (hQan m) (hDan m) (hQD m) _)
    refine (e1.add e2).congr (Eventually.of_forall fun z => ?_)
    simp only [Pi.pow_apply]
    rw [hpevH4, ← hrem i (A z) (δ (A z)) z]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring

  choose U hU V hV hUV using fun i => mem_nhds_prod_iff.1 (hev i)
  have hW' : W ∩ ⋂ i, V i ∈ 𝓝 w := inter_mem hW (iInter_mem.2 hV)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hW'
  have hroots : ∀ m, ∀ᶠ y in 𝓝 (A w), ∀ x : ℂ, x ^ n m + ∑ j, b m j y * x ^ (j : ℕ) = 0 →
      ‖x - w m‖ < ε := fun m =>
    roots_near_of_centred (b m) (A w) (w m) (fun j => (hb m j).continuousAt) (hb0 m) hε
  filter_upwards [h3, eventually_all.2 hroots, eventually_all.2 hE1, eventually_all.2 hE2, hE3,
    eventually_all.2 hE4, eventually_all.2 hU] with y h3y hry hE1y hE2y hE3y hE4y hUy hδy

  set Fy := monicOfCoeffs fun j => c j y with hFy
  have hsep := h3y hδy
  have hFy0 : Fy ≠ 0 := hsep.ne_zero
  have hdeg : Fy.natDegree = N := by
    rw [hFy, monicOfCoeffs, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
    rw [degree_X_pow]
    exact degree_sum_fin_lt _
  have hcard : Fy.roots.toFinset.card = N := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree, hdeg]
  let eq := Fy.roots.toFinset.equivFin.trans (finCongr hcard)
  let t : Fin N → ℂ := fun j => (eq.symm j : ℂ)
  have ht_inj : Function.Injective t := Subtype.val_injective.comp eq.symm.injective
  have ht_root : ∀ j, t j ^ N + ∑ i, c i y * t j ^ (i : ℕ) = 0 := by
    intro j
    have hm : t j ∈ Fy.roots := Multiset.mem_toFinset.1 (eq.symm j).2
    have := (mem_roots hFy0).1 hm
    simpa [hFy, monicOfCoeffs, eval_finsetSum] using this

  let x : Fin N → σ → ℂ := fun j m => pev y (t j) (qp m) / δ y ^ M
  have hδM : δ y ^ M ≠ 0 := pow_ne_zero _ hδy
  have hQx : ∀ j m, pev y (t j) (qp m) = δ y ^ M * x j m := fun j m => by
    simp only [x]; field_simp
  have hG : ∀ j m, x j m ^ n m + ∑ i, b m i y * x j m ^ (i : ℕ) = 0 := by
    intro j m
    have h := hE1y m (t j) (ht_root j)
    rw [hpevH1] at h
    simp only [hQx] at h
    rw [centred_clear (fun i => b m i y) M (δ y) (x j m)] at h
    exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ hδy)
  have hlinx : ∀ (lam : (σ → ℂ) →L[ℂ] ℂ) L j, pev y (t j) (Hlin lam L) = 0 → lam (x j) = pev y (t j) L := by
    intro lam L j h
    rw [hpevHlin] at h
    simp only [hQx] at h
    rw [clm_apply_eq_sum lam (x j)]
    have h' : δ y ^ M * (∑ m, x j m * lam (ev m) - pev y (t j) L) = 0 := by
      rw [← h, mul_sub, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun m _ => by ring
    exact sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_left hδM)
  have hAx : ∀ j, A (x j) = y := by
    intro j
    funext r
    have := hlinx _ _ j (hE2y r (t j) (ht_root j))
    simpa [coordP] using this
  have hℓx : ∀ j, ℓ (x j) = t j := fun j => by
    simpa using hlinx ℓ X j (hE3y (t j) (ht_root j))
  have hxW : ∀ j, x j ∈ W ∩ ⋂ i, V i := by
    intro j
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hε]
    exact fun m => hry m _ (hG j m)
  have hpx : ∀ j i, p i (x j) = 0 := by
    intro j i
    have hmem := hUV i (Set.mk_mem_prod (hUy i) (Set.mem_iInter.1 (hxW j).2 i))
    simp only [Set.mem_ofPred_eq] at hmem
    rw [hmem]
    have h := hE4y i (t j) (ht_root j)
    rw [hpevH4] at h
    simp only [hQx] at h
    rw [hrem i y (δ y) (x j)] at h
    rw [(mul_eq_zero.1 h).resolve_left (pow_ne_zero _ hδy), add_zero]
    exact Finset.sum_eq_zero fun m _ => by rw [hG j m, mul_zero]
  refine ⟨x, fun j => ⟨(hxW j).1, fun i => hpx j i, hAx j⟩, fun j₁ j₂ h => ht_inj ?_⟩
  simpa [hℓx] using h
end PrimitivePresentationCover
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
