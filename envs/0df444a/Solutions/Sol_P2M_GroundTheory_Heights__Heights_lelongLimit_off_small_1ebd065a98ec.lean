-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_lelongLimit_off_small_1ebd065a98ec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:56:45.007994+00:00
-- url     : https://prove2.me/submissions/43adcddc-fd80-4d1d-9f2c-d424b2f5473a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimitOnZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimitOffZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimitGoodPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongMassNearSmall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarIntAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LocalLimitGlueOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongLimitOnZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_minimalPrimes_sup_linForm_39b08eae98d4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_lelongSides_add_4039a094c087
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_tendsto_of_forall_local_on_tsupport_b40b82da17eb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_varInt_eq_zero_of_vanish_87c7772e6a98


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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets Function
open scoped ContDiff
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (hOff : LelongLimitOffZero.Statement) (hAdd : VarIntAdd.Statement)
    {n d : ℕ} {J I : Ideal (MvPolynomial (Fin n) ℂ)} {u : Fin n → ℂ} {φ : Fin d → (Fin n → ℂ) → ℝ}
    (hJ : J.IsPrime) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ))
    (hu : linForm u ∉ J) (hφ : ∀ i, SmoothNear (zeroSet J) (φ i))
    (hloc : ∀ q ∈ zeroSet J, linEval u q = 0 → q ∉ zeroSet I →
      ∃ N ∈ 𝓝 q, ∀ f : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ N →
        Tendsto (fun ε => varInt J (d + 1) f (vecCons (logReg u ε) φ)) (𝓝[>] 0)
          (𝓝 (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
              (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
            (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d f φ)))
    (g : (Fin n → ℂ) → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hgI : Disjoint (tsupport g) (zeroSet I)) :
    Tendsto (fun ε => varInt J (d + 1) g (vecCons (logReg u ε) φ)) (𝓝[>] 0)
      (𝓝 (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
          (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
        (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g φ)) := by
  classical
  have hclosed : IsClosed (zeroSet J ∩ {x | linEval u x = 0}) := by
    refine IsClosed.inter ?_ (isClosed_eq ?_ continuous_const)
    · have : zeroSet J = ⋂ q ∈ J, {x : Fin n → ℂ | MvPolynomial.eval x q = 0} := by
        ext x; simp [zeroSet]
      rw [this]
      exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const
    · exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
  refine tendsto_of_forall_local_on_tsupport
    (fun ε g => varInt J (d + 1) g (vecCons (logReg u ε) φ))
    (fun g => ∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
      (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
      (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g φ)
    (fun g₁ g₂ h1 h1c h2 h2c => (lelongSides_add hAdd hJ hφ g₁ g₂ h1 h1c h2 h2c).1)
    (fun g₁ g₂ h1 h1c h2 h2c => (lelongSides_add hAdd (u := u) hJ hφ g₁ g₂ h1 h1c h2 h2c).2)
    g hg hgc fun q hq => ?_
  by_cases hq0 : q ∈ zeroSet J ∩ {x | linEval u x = 0}
  · exact hloc q hq0.1 hq0.2 (Set.disjoint_left.1 hgI hq)
  · refine ⟨_, hclosed.isOpen_compl.mem_nhds hq0, fun g' hg' hg'c hg'N => ?_⟩
    have h0 : (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
        (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
        (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g' φ) = 0 := by
      refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
      rw [finsum_eq_dif]
      by_cases hWm : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes
      · obtain ⟨-, hWJ, hWu⟩ := mem_minimalPrimes_sup_linForm hWm
        rw [dif_pos hWm, varInt_eq_zero_of_vanish W g' φ fun x hx =>
          image_eq_zero_of_notMem_tsupport fun hxs => hg'N hxs ⟨hWJ hx, hWu x hx⟩, mul_zero]
      · rw [dif_neg hWm]
    simp only [h0]
    exact hOff n d J u g' φ hJ hdim hu hg' hg'c hφ
      (Set.disjoint_left.2 fun x hx hx' => hg'N hx hx')
end GroundTheory.Heights₂.Heights
