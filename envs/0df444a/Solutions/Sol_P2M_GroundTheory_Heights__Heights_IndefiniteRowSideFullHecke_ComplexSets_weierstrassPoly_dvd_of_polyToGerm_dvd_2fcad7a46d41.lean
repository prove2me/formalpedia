-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrassPoly_dvd_of_polyToGerm_dvd_2fcad7a46d41
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:38.916127+00:00
-- url     : https://prove2.me/submissions/7be938e0-cb4f-47ad-9325-146af97ccac9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_WeierstrassRemainderUnique
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticGermsNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHolGermsDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_WeierstrassPolynomialRing
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrassPoly_monic_2d2bc204a188
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_polyToGerm_finPoly_d448074637f3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_polyToGerm_weierstrassPoly_6ea9dc83e5cd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrass_remainder_eq_zero_e4d63f335f60


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
open Topology Filter Polynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {σ : Type} [Fintype σ] {d : ℕ} (c : Fin d → (σ → ℂ) → ℂ)
    (hc : ∀ j, AnalyticAt ℂ (c j) 0) (hc0 : ∀ j, c j 0 = 0) (p : (holGerms (0 : σ → ℂ))[X])
    (h : polyToGerm σ (weierstrassPoly c hc) ∣ polyToGerm σ p) : weierstrassPoly c hc ∣ p := by
  have hm := weierstrassPoly_monic c hc
  have hdeg : (weierstrassPoly c hc).natDegree = d := by
    rw [weierstrassPoly, finPoly, natDegree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact degree_sum_fin_lt _),
      natDegree_X_pow]
  rw [← modByMonic_eq_zero_iff_dvd hm]
  have hrdeg : (p %ₘ weierstrassPoly c hc).degree < d := by
    have := degree_modByMonic_lt p hm
    rwa [degree_eq_natDegree hm.ne_zero, hdeg] at this
  choose a ha hae using fun j : Fin d => ((p %ₘ weierstrassPoly c hc).coeff j).2
  have hcoeff : ∀ j : Fin d, (p %ₘ weierstrassPoly c hc).coeff j = mkGerm (a j) (ha j) :=
    fun j => Subtype.ext (hae j).symm
  have hr : p %ₘ weierstrassPoly c hc = finPoly fun j => mkGerm (a j) (ha j) := by
    conv_lhs => rw [← sum_C_mul_X_pow_eq (p %ₘ weierstrassPoly c hc)]
    rw [← sum_fin (fun n b => C b * X ^ n) (by simp) hrdeg, finPoly]
    exact Finset.sum_congr rfl fun j _ => by rw [hcoeff j]

  obtain ⟨Q, hQ⟩ := h
  have himg : polyToGerm σ (p %ₘ weierstrassPoly c hc) =
      polyToGerm σ (weierstrassPoly c hc) * (Q - polyToGerm σ (p /ₘ weierstrassPoly c hc)) := by
    have e := congrArg (polyToGerm σ) (modByMonic_add_div p (weierstrassPoly c hc))
    rw [map_add, map_mul] at e
    rw [mul_sub, ← hQ, ← e]; ring
  obtain ⟨m, hmA, hmQ⟩ := (Q - polyToGerm σ (p /ₘ weierstrassPoly c hc)).2
  have hgerm := congrArg (fun φ : holGerms (0 : Option σ → ℂ) => (φ : Germ (𝓝 (0 : Option σ → ℂ)) ℂ)) himg
  simp only [Subring.coe_mul] at hgerm
  rw [hr, polyToGerm_finPoly, polyToGerm_weierstrassPoly, ← hmQ] at hgerm
  have hev : ∀ᶠ x in 𝓝 (0 : Option σ → ℂ),
      ∑ j : Fin d, a j (fun i => x (some i)) * x none ^ (j : ℕ) = m x * weierstrassPolynomial c x := by
    have := Germ.coe_eq.1 (hgerm.trans (Germ.coe_mul _ _).symm)
    filter_upwards [this] with x hx
    rw [hx]; exact mul_comm _ _
  have hzero := weierstrass_remainder_eq_zero c (fun j => (hc j).continuousAt) hc0 a m hmA hev
  rw [hr]
  refine Finset.sum_eq_zero fun j _ => ?_
  have : mkGerm (a j) (ha j) = 0 := Subtype.ext (Germ.coe_eq.2 (hzero j))
  show C (mkGerm (a j) (ha j)) * X ^ (j : ℕ) = 0
  rw [this, C_0, zero_mul]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
