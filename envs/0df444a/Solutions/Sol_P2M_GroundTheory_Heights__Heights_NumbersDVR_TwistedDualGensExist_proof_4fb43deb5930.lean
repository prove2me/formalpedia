-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_proof_4fb43deb5930
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:07:06.759892+00:00
-- url     : https://prove2.me/submissions/a3f076e6-6790-4173-b46e-c3e8b435c655

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwistedDualGensExist
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_pow_mul_mem_mono_b099b0e3fb7e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_exists_dual_gens_8da4bdc2b4a2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_exists_twist_2d8884ecf098
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_ratio_mem_bfdbef1de55d

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
variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
  {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace TwistedDualGensExist
theorem _root_.solution : TwistedDualGensExist.Statement := by
  classical
  intro O _ _ Ω _ _ K _ ι _ y N E _ _ B
  have hG : ∀ c : {c : ∀ k, ι k // segreVec y c ≠ 0}, ∃ S : Finset (Module.Dual Ω E),
      (∀ ψ ∈ S, ∀ v ∈ B.lat c.1, ψ v ∈ chartRing O (segreVec y) c.1) ∧
      ∀ ψ' : Module.Dual Ω E, (∀ v ∈ B.lat c.1, ψ' v ∈ chartRing O (segreVec y) c.1) →
        ∃ u : Module.Dual Ω E → Ω, (∀ ψ, u ψ ∈ chartRing O (segreVec y) c.1) ∧
          ∑ ψ ∈ S, u ψ • ψ = ψ' :=
    fun c => TwistedDualGensExist.exists_dual_gens B c.2
  choose G hGmem hGgen using hG
  have hT : ∀ (c : {c : ∀ k, ι k // segreVec y c ≠ 0}) (ψ : Module.Dual Ω E), ∃ n : ℕ, ψ ∈ G c →
      ∀ c', segreVec y c' ≠ 0 → ∀ v ∈ B.lat c',
        (segreVec y c.1 / segreVec y c') ^ n * ψ v ∈ chartRing O (segreVec y) c' := by
    intro c ψ
    by_cases h : ψ ∈ G c
    · obtain ⟨n, hn⟩ := TwistedDualGensExist.exists_twist B c.2 (hGmem c ψ h)
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun h' => (h h').elim⟩
  choose nn hnn using hT
  set n : ℕ := ∑ c, ∑ ψ ∈ G c, nn c ψ with hn
  have hle : ∀ c ψ, ψ ∈ G c → nn c ψ ≤ n := by
    intro c ψ hψ
    exact le_trans (Finset.single_le_sum (f := nn c) (fun _ _ => Nat.zero_le _) hψ)
      (Finset.single_le_sum (f := fun c => ∑ ψ ∈ G c, nn c ψ) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ c))
  refine ⟨fun _ => (n : ℤ), fun a ha => ?_⟩
  obtain ⟨b, hab⟩ : ∃ b : K → ℕ, ∀ k, a k = (n : ℤ) + (b k : ℤ) :=
    ⟨fun k => (a k - n).toNat, fun k => by have h := ha k; dsimp only at h ⊢; omega⟩
  have hy : ∀ c : ∀ k, ι k, segreVec y c ≠ 0 → ∀ k, y ⟨k, c k⟩ ≠ 0 :=
    fun c hc k => (Finset.prod_ne_zero_iff.1 hc) k (Finset.mem_univ _)
  have hprod : ∀ c : ∀ k, ι k, segreVec y c ≠ 0 →
      ∏ k, y ⟨k, c k⟩ ^ a k = segreVec y c ^ n * ∏ k, y ⟨k, c k⟩ ^ b k := by
    intro c hc
    rw [segreVec, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hab k, zpow_add₀ (hy c hc k), zpow_natCast, zpow_natCast]
  set T : Finset (Module.Dual Ω E) := Finset.univ.biUnion G with hTdef
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : {c : ∀ k, ι k // segreVec y c ≠ 0} × T × (∀ k, ι k) → Module.Dual Ω E,
      ∀ c ψ d, Φ (c, ψ, d) = if (ψ : Module.Dual Ω E) ∈ G c then
        (segreVec y c.1 ^ n * ∏ k, y ⟨k, d k⟩ ^ b k) • (ψ : Module.Dual Ω E) else 0 :=
    ⟨fun i => if (i.2.1 : Module.Dual Ω E) ∈ G i.1 then
      (segreVec y i.1.1 ^ n * ∏ k, y ⟨k, i.2.2 k⟩ ^ b k) • (i.2.1 : Module.Dual Ω E) else 0,
      fun _ _ _ => rfl⟩
  obtain ⟨M, ⟨e⟩⟩ : ∃ M : ℕ,
      Nonempty ({c : ∀ k, ι k // segreVec y c ≠ 0} × T × (∀ k, ι k) ≃ Fin M) :=
    ⟨_, ⟨Fintype.equivFin _⟩⟩
  refine ⟨M, fun l => Φ (e.symm l), ⟨?_, ?_⟩⟩
  · intro c' hc' l v hv
    obtain ⟨c, ψ, d⟩ := e.symm l
    rw [hΦ]
    split_ifs with hψ
    · refine ⟨((segreVec y c.1 / segreVec y c') ^ n * (ψ : Module.Dual Ω E) v) *
          ∏ k, (y ⟨k, d k⟩ / y ⟨k, c' k⟩) ^ b k,
        mul_mem (TwistedDualGensExist.pow_mul_mem_mono (hnn c ψ hψ c' hc' v hv) (hle c ψ hψ))
          (prod_mem fun k _ => pow_mem (TwistedDualGensExist.ratio_mem y hc' k (d k)) _), ?_⟩
      rw [LinearMap.smul_apply, smul_eq_mul, hprod c' hc',
        Finset.prod_congr rfl (fun k _ => div_pow _ _ _), Finset.prod_div_distrib, div_pow]
      have h1 : segreVec y c' ^ n ≠ 0 := pow_ne_zero _ hc'
      have h2 : ∏ k, y ⟨k, c' k⟩ ^ b k ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy c' hc' k)
      field_simp
    · exact ⟨0, zero_mem _, by simp⟩
  · intro c' hc' ψ' hψ'
    obtain ⟨u, hu, hsum⟩ := hGgen ⟨c', hc'⟩ ψ' hψ'
    set c'' : {c : ∀ k, ι k // segreVec y c ≠ 0} := ⟨c', hc'⟩ with hc''
    obtain ⟨U, hU⟩ : ∃ U : {c : ∀ k, ι k // segreVec y c ≠ 0} × T × (∀ k, ι k) → Ω,
        ∀ c ψ d, U (c, ψ, d) = if c = c'' ∧ d = c' then u ψ else 0 :=
      ⟨fun i => if i.1 = c'' ∧ i.2.2 = c' then u i.2.1 else 0, fun _ _ _ => rfl⟩
    refine ⟨fun l => U (e.symm l), fun l => ?_, ?_⟩
    · dsimp only
      obtain ⟨c, ψ, d⟩ := e.symm l
      rw [hU]
      split_ifs
      exacts [hu _, zero_mem _]
    have hYX : (∏ k, y ⟨k, c' k⟩ ^ (-a k)) * (segreVec y c' ^ n * ∏ k, y ⟨k, c' k⟩ ^ b k) = 1 := by
      rw [← hprod c' hc', ← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun k _ => by rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (hy c' hc' k))]
    have hterm : ∀ c ψ d, (U (c, ψ, d) * ∏ k, y ⟨k, c' k⟩ ^ (-a k)) • Φ (c, ψ, d) =
        if c = c'' ∧ d = c' then
          (if (ψ : Module.Dual Ω E) ∈ G c'' then u ψ • (ψ : Module.Dual Ω E) else 0) else 0 := by
      intro c ψ d
      rw [hU, hΦ]
      by_cases h : c = c'' ∧ d = c'
      · rw [if_pos h, if_pos h]
        obtain ⟨h1, h2⟩ := h
        rw [h1, h2]
        split_ifs with hψ
        · rw [smul_smul, mul_assoc, hYX, mul_one]
        · rw [smul_zero]
      · rw [if_neg h, if_neg h, zero_mul, zero_smul]
    have hre := Equiv.sum_comp e.symm (fun i => (U i * ∏ k, y ⟨k, c' k⟩ ^ (-a k)) • Φ i)
    refine Eq.trans ?_ hre.symm
    rw [Fintype.sum_prod_type, Fintype.sum_eq_single c'']
    · rw [Fintype.sum_prod_type]
      simp only [hterm, true_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [Finset.sum_coe_sort T (fun ψ => if ψ ∈ G c'' then u ψ • ψ else 0), Finset.sum_ite_mem,
        Finset.inter_eq_right.2 (Finset.subset_biUnion_of_mem G (Finset.mem_univ c'')), hsum]
    · intro c hc
      refine Finset.sum_eq_zero fun p _ => ?_
      obtain ⟨ψ, d⟩ := p
      rw [hterm, if_neg fun h => hc h.1]
end TwistedDualGensExist
end GroundTheory.Heights₂.Heights.NumbersDVR
