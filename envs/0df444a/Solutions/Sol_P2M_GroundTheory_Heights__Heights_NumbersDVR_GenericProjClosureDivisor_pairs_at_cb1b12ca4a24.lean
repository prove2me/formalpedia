-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_pairs_at_cb1b12ca4a24
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:56:38.065293+00:00
-- url     : https://prove2.me/submissions/2cabc9a4-99a4-4d04-822f-8591f7912e9f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericProjClosureDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExpress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDivisor
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_mem_of_homog_344f22dd36be
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_chartMonoZ_homog_94b18e153b90
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_express_forms_e96e5190c062
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_val_pair_5c72587972df

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
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {N M M' : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]
  {Φ : Type} [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
variable [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
theorem _root_.solution (hexp : TwistedDualGensExpress.Statement) {ϖ : O} (y : (Σ k, ι k) → Ω)
    (B B' : ChartBundle O (segreVec y) N E) (hB : SameGenericFibre ϖ B B') (a₀ a₀' : K → ℤ)
    (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E)
    (hφ : IsTwistedDualGens y B a₀ φ) (hφ' : IsTwistedDualGens y B' a₀' φ')
    (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ)
    (W : Ideal (MRing (bundleIdx (bundleIdx ι M) M') O)) (hW : W.IsPrime)
    (hPW : pointIdeal O (pairProjCoord y e φ φ' t) ≤ W) (hWr : IsRelevant W)
    (hϖW : (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ W) :
    (∃ f g, IsZPair a₀ a₀' (pairProjCoord y e φ φ' t) f g ∧ g ∉ W) ∧
      (∃ f g, IsZPair a₀ a₀' (pairProjCoord y e φ φ' t) f g ∧ f ∉ W) := by
  choose c hc using fun k : K => hWr (some (some k))
  obtain ⟨l₀, hl₀⟩ := hWr (some none)
  obtain ⟨m₁, hm₁⟩ := hWr none
  have nz : ∀ p, (X p : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ W → pairProjCoord y e φ φ' t p ≠ 0 := by
    intro p hp h0
    exact hp (hPW (mem_of_homog (isWeightedHomogeneous_X O _ p) (by rw [aeval_X]; exact h0)))
  have hyc : segreVec y c ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun k _ h0 => nz _ (hc k) ?_
    show algebraMap Ω Φ (y ⟨k, c k⟩) = 0
    rw [h0, map_zero]
  have hmono : ∀ (n : ℕ) (α : K → ℕ), (C (ϖ ^ n) * chartMonoZ O M M' c α) ∉ W := by
    intro n α hm
    rcases hW.mem_or_mem hm with h | h
    · rw [map_pow] at h
      exact hϖW (hW.mem_of_pow_mem n h)
    · have := hW
      obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
      exact hc k (hW.mem_of_pow_mem _ hk)
  constructor
  · obtain ⟨n, r, hr, hx⟩ := hexp O ϖ Ω K ι y N E B B' hB a₀ a₀' M M' φ φ' hφ hφ' c hyc m₁
    obtain ⟨bG, bH, G, hG, hdeg, hval⟩ :=
      express_forms (M := M) (M' := M') y e φ φ' t c hyc ϖ φ (φ' m₁) a₀ a₀' n r hr hx
    refine ⟨∑ l, X ⟨some none, l⟩ * G l, X ⟨none, m₁⟩ * (C (ϖ ^ n) * chartMonoZ O M M' c bH),
      ⟨⟨Pi.single (some none) 1 + vdeg bG, Pi.single none 1 + vdeg bH, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
    · exact IsWeightedHomogeneous.sum _ _ _ fun l _ =>
        IsWeightedHomogeneous.mul (isWeightedHomogeneous_X O _ _) (hG l)
    · have := IsWeightedHomogeneous.mul
        (isWeightedHomogeneous_X O (blockWeight (bundleIdx (bundleIdx ι M) M')) ⟨none, m₁⟩)
        (IsWeightedHomogeneous.mul (isWeightedHomogeneous_C _ (ϖ ^ n))
          (chartMonoZ_homog (O := O) (M := M) (M' := M') c bH))
      rwa [zero_add] at this
    · funext o
      rcases o with _ | _ | k
      · simp [vdeg, zetaFirst, zetaSecond]
      · simp [vdeg, zetaFirst, zetaSecond]
      · simp [vdeg, zetaFirst, zetaSecond]
        linarith [hdeg k]
    · exact val_pair (z := pairProjCoord y e φ φ' t) (v := fun l => genVal e t (φ l))
        (w := genVal e t (φ' m₁)) (fun l => aeval_X _ _) G (aeval_X _ _) _ hval
    · intro hm
      rcases hW.mem_or_mem hm with h | h
      · exact hm₁ h
      · exact hmono n bH h
  · obtain ⟨n, r, hr, hx⟩ := hexp O ϖ Ω K ι y N E B' B (fun c hc => ⟨(hB c hc).2, (hB c hc).1⟩)
      a₀' a₀ M' M φ' φ hφ' hφ c hyc l₀
    obtain ⟨bG, bH, G, hG, hdeg, hval⟩ :=
      express_forms (M := M) (M' := M') y e φ φ' t c hyc ϖ φ' (φ l₀) a₀' a₀ n r hr hx
    refine ⟨X ⟨some none, l₀⟩ * (C (ϖ ^ n) * chartMonoZ O M M' c bH), ∑ m, X ⟨none, m⟩ * G m,
      ⟨⟨Pi.single (some none) 1 + vdeg bH, Pi.single none 1 + vdeg bG, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
    · have := IsWeightedHomogeneous.mul
        (isWeightedHomogeneous_X O (blockWeight (bundleIdx (bundleIdx ι M) M')) ⟨some none, l₀⟩)
        (IsWeightedHomogeneous.mul (isWeightedHomogeneous_C _ (ϖ ^ n))
          (chartMonoZ_homog (O := O) (M := M) (M' := M') c bH))
      rwa [zero_add] at this
    · exact IsWeightedHomogeneous.sum _ _ _ fun m _ =>
        IsWeightedHomogeneous.mul (isWeightedHomogeneous_X O _ _) (hG m)
    · funext o
      rcases o with _ | _ | k
      · simp [vdeg, zetaFirst, zetaSecond]
      · simp [vdeg, zetaFirst, zetaSecond]
      · simp [vdeg, zetaFirst, zetaSecond]
        linarith [hdeg k]
    · exact (val_pair (z := pairProjCoord y e φ φ' t) (v := fun m => genVal e t (φ' m))
        (w := genVal e t (φ l₀)) (fun m => aeval_X _ _) G (aeval_X _ _) _ hval).symm
    · intro hm
      rcases hW.mem_or_mem hm with h | h
      · exact hl₀ h
      · exact hmono n bH h
end GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
