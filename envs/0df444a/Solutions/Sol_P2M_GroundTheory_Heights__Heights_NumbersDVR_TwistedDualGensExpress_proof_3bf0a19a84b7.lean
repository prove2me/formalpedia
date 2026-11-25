-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExpress_proof_3bf0a19a84b7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:26:05.335559+00:00
-- url     : https://prove2.me/submissions/fc5af515-8fea-4449-a660-e4cbddb4ebb1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExpress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwistedDualGensExpress
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExpress_sum_mul_mem_localized_a133a3e4872d

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace TwistedDualGensExpress
theorem _root_.solution : TwistedDualGensExpress.Statement := by
  unfold TwistedDualGensExpress.Statement
  intro R _ ϖ Ω _ _ K _ ι y N E _ _ B B' hsame a a' M M' φ φ' hφ hφ' c hc m
  set A := chartRing R (segreVec y) c with hA
  set w : Ω := algebraMap R Ω ϖ with hw
  have hwA : w ∈ A := Subalgebra.algebraMap_mem _ ϖ
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc k (Finset.mem_univ k)
  set ψ : Module.Dual Ω E := (∏ k, y ⟨k, c k⟩ ^ (-a' k)) • φ' m with hψ
  have hψA : ∀ v ∈ B'.lat c, ψ v ∈ A := by
    intro v hv
    obtain ⟨s, hs, hsv⟩ := hφ'.sections c hc m v hv
    have : ψ v = s := by
      rw [hψ, LinearMap.smul_apply, hsv, smul_eq_mul, mul_comm s, ← mul_assoc,
        ← Finset.prod_mul_distrib, Finset.prod_eq_one (fun k _ => by
          rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (hy k))]), one_mul]
    rw [this]
    exact hs
  obtain ⟨k0, f, cc, hf, hcc, hsum, hb⟩ := B.frame c hc
  choose b hli hsp hiff using hb
  have hbq : ∀ l q, ∃ n : ℕ, f l ≠ 0 → ∃ e : ℕ, f l ^ e * (w ^ n * ψ (b l q)) ∈ A := by
    intro l q
    by_cases hl : f l = 0
    · exact ⟨0, fun h => (h hl).elim⟩
    obtain ⟨e, he⟩ := (hiff l (b l q)).2 ⟨Pi.single q 1, fun q' => ⟨0, by
        by_cases h : q' = q
        · subst h; simp
        · simp [h]⟩, by simp [Pi.single_apply]⟩
    obtain ⟨n, hn⟩ := (hsame c hc).1 _ he
    refine ⟨n, fun _ => ⟨e, ?_⟩⟩
    have h := hψA _ hn
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
    rw [show f l ^ e * (w ^ n * ψ (b l q)) = w ^ n * (f l ^ e * ψ (b l q)) by ring]
    exact h
  choose nb hnb using hbq
  set n := Finset.univ.sup (fun p : Fin k0 × Fin N => nb p.1 p.2) with hn
  have hle : ∀ l q, nb l q ≤ n := fun l q =>
    Finset.le_sup (f := fun p : Fin k0 × Fin N => nb p.1 p.2) (Finset.mem_univ (l, q))
  have hmain : ∀ v ∈ B.lat c, (w ^ n • ψ) v ∈ A := by
    intro v hv
    rw [LinearMap.smul_apply, smul_eq_mul]
    refine Subalgebra.mem_of_finsetSum_eq_one_of_pow_smul_mem _ Finset.univ f cc hsum hf hcc _ ?_
    intro l
    by_cases hl : f l = 0
    · exact ⟨1, by simp [hl]⟩
    obtain ⟨a'', ha'', hrep⟩ := (hiff l v).1 ⟨0, by simpa using hv⟩
    obtain ⟨e, he⟩ := TwistedDualGensExpress.sum_mul_mem_localized A (hf l) a''
      (fun q => w ^ n * ψ (b l q)) ha'' (fun q => by
        obtain ⟨e, he⟩ := hnb l q hl
        refine ⟨e, ?_⟩
        rw [← pow_sub_mul_pow w (hle l q)]
        rw [show f l ^ e * (w ^ (n - nb l q) * w ^ nb l q * ψ (b l q)) =
          w ^ (n - nb l q) * (f l ^ e * (w ^ nb l q * ψ (b l q))) by ring]
        exact mul_mem (pow_mem hwA _) he)
    refine ⟨e, ?_⟩
    have : w ^ n * ψ v = ∑ q, a'' q * (w ^ n * ψ (b l q)) := by
      rw [hrep, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_smul, smul_eq_mul]
      ring
    rw [smul_eq_mul, this]
    exact he
  obtain ⟨u, hu, hsum'⟩ := hφ.generate c hc (w ^ n • ψ) hmain
  refine ⟨n, u, hu, ?_⟩
  have hY : (∏ k, y ⟨k, c k⟩ ^ a' k) * ∏ k, y ⟨k, c k⟩ ^ (-a' k) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => by rw [zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ (hy k))]
  have h1 : w ^ n • φ' m = (∏ k, y ⟨k, c k⟩ ^ a' k) • (w ^ n • ψ) := by
    rw [hψ, smul_comm (w ^ n) (∏ k, y ⟨k, c k⟩ ^ (-a' k)), smul_smul, hY, one_smul]
  rw [h1, hsum', Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_smul]
  congr 1
  rw [mul_left_comm, ← Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl fun k _ => by rw [← zpow_add₀ (hy k), sub_eq_add_neg]
end TwistedDualGensExpress
end GroundTheory.Heights₂.Heights.NumbersDVR
