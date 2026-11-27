-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_GenFibreChartDeg_proof_66ceb0eb0f3f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:11:05.429927+00:00
-- url     : https://prove2.me/submissions/b26d9e32-ade1-493c-81a2-0994f5d9adcf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GenFibreChartDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartScalingIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StAdjoinIndepRelfinrank
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFinrankAdjoinRange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGenFibreChartDeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_GenFibreChartDeg_isMultiHomogIdeal_ker_rat_b437d4a65265
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexAt_algebraMap_apply_de37bb391a59
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeTrdeg_proof_69ca55d428ae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordConeArithVar_proof_c88814975c4f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_FinrankAdjoinRange_proof_0c9eb8015d67
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_GenericPointExists_proof_ea6d93ea06df
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_FibreCurve_charZero_5d26261f436b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace GroundTheory.Heights₂.Heights.Targets
namespace GenFibreChartDeg
theorem _root_.solution (hT : GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep.Statement)
    (hC : GroundTheory.Heights₂.Heights.Inter.AdjoinIndepRelfinrank.Statement) : GenFibreChartDeg.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' G _ c i hv hP hc hi
  have : CharZero G.Φ := (algebraMap G.Φ G.Φ').charZero
  have hx'0 : ∀ k, G.x' (v ⟨k, c k⟩) ≠ 0 := fun k => by
    rw [G.compat]
    exact (map_ne_zero _).2 (hc k)

  have hex : ∀ k', ∃ j : ι' k', G.x' ⟨k', j⟩ ≠ 0 := by
    intro k'
    by_cases hk : k' ∈ Set.range κ
    · obtain ⟨k, rfl⟩ := hk
      have key : ∀ q : Σ k', ι' k', q.1 = κ k → G.x' q ≠ 0 → ∃ j : ι' (κ k), G.x' ⟨κ k, j⟩ ≠ 0 := by
        rintro ⟨a, j⟩ rfl h
        exact ⟨j, h⟩
      exact key _ (hv.2.2.1 _) (hx'0 k)
    · exact ⟨i ⟨k', hk⟩, hi ⟨k', hk⟩⟩
  choose i' hi' using hex

  let t : K → G.Φ' := fun k => G.x' ⟨κ k, i' (κ k)⟩
  let Φ₁ := (IsScalarTower.toAlgHom ℚ G.Φ G.Φ').fieldRange
  let F₁ := blockFnField G.x'
  let F₀ := blockFnField (G.x' ∘ v)
  let E := IntermediateField.adjoin ℚ (Set.range t)
  let S := Set.range fun q : Σ k : FibreBlock κ, fibreIdx ι' κ k => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩
  have hF : ∀ p q : Σ k', ι' k', p.1 = q.1 → G.x' p / G.x' q ∈ F₁ :=
    fun p q h => IntermediateField.subset_adjoin _ _ ⟨p, q, h, rfl⟩
  have hF0 : ∀ p q : Σ k, ι k, p.1 = q.1 → G.x' (v p) / G.x' (v q) ∈ F₀ :=
    fun p q h => IntermediateField.subset_adjoin _ _ ⟨p, q, h, rfl⟩
  have hF01 : F₀ ≤ F₁ := IntermediateField.adjoin_le_iff.2 (by
    rintro _ ⟨p, q, h, rfl⟩
    exact hF (v p) (v q) (by rw [hv.2.2.1, hv.2.2.1, h]))
  have hmem : ∀ c, algebraMap G.Φ G.Φ' c ∈ Φ₁ := fun c => AlgHom.mem_fieldRange.2 ⟨c, rfl⟩

  have hchart : ∀ k, ∃ p₀ : Σ k, ι k, p₀.1 = k ∧ v p₀ = ⟨κ k, i' (κ k)⟩ := fun k => by
    obtain ⟨p₀, h⟩ := hv.2.2.2 ⟨κ k, i' (κ k)⟩ ⟨k, rfl⟩
    exact ⟨p₀, hv.1 ((hv.2.2.1 p₀).symm.trans (congrArg Sigma.fst h)), h⟩
  have ht1 : ∀ k, t k ∈ Φ₁ := fun k => by
    obtain ⟨p₀, -, h⟩ := hchart k
    show G.x' ⟨κ k, i' (κ k)⟩ ∈ Φ₁
    rw [← h, G.compat]
    exact hmem _
  have hrat : ∀ p : Σ k, ι k, G.x' (v p) / t p.1 ∈ F₀ := fun p => by
    obtain ⟨p₀, h1, h⟩ := hchart p.1
    show G.x' (v p) / G.x' ⟨κ p.1, i' (κ p.1)⟩ ∈ F₀
    rw [← h]
    exact hF0 p p₀ h1.symm

  have hΦ₁ : F₀ ⊔ E = Φ₁ := by
    refine le_antisymm (sup_le (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin_le_iff.2 ?_)) ?_
    · rintro _ ⟨p, q, -, rfl⟩
      show G.x' (v p) / G.x' (v q) ∈ Φ₁
      rw [G.compat, G.compat]
      exact div_mem (hmem _) (hmem _)
    · rintro _ ⟨k, rfl⟩
      exact ht1 k
    · intro z hz
      obtain ⟨c, rfl⟩ := AlgHom.mem_fieldRange.1 hz
      obtain ⟨f, g, -, rfl⟩ := G.gen c
      have hpoly : ∀ f : MRing ι, algebraMap G.Φ G.Φ' (aeval G.x f) ∈ F₀ ⊔ E := by
        intro f
        induction f using MvPolynomial.induction_on with
        | C a =>
          rw [aeval_C, ← IsScalarTower.algebraMap_apply, algebraMap_int_eq, eq_intCast]
          exact intCast_mem _ a
        | add f g hf hg =>
          rw [map_add, map_add]
          exact add_mem hf hg
        | mul_X f q hf =>
          rw [map_mul, map_mul, aeval_X, ← G.compat]
          refine mul_mem hf ?_
          rw [← div_mul_cancel₀ (G.x' (v q)) (hi' (κ q.1))]
          exact mul_mem ((le_sup_left : F₀ ≤ F₀ ⊔ E) (hrat q))
            ((le_sup_right : E ≤ F₀ ⊔ E) (IntermediateField.subset_adjoin _ _ ⟨q.1, rfl⟩))
      show IsScalarTower.toAlgHom ℚ G.Φ G.Φ' (aeval G.x f / aeval G.x g) ∈ F₀ ⊔ E
      rw [map_div₀]
      exact div_mem (hpoly f) (hpoly g)

  have hΦS : Φ₁ ⊔ IntermediateField.adjoin ℚ S = F₁ ⊔ E := by
    refine le_antisymm (sup_le ?_ ?_) (sup_le ?_ ?_)
    · rw [← hΦ₁]
      exact sup_le_sup_right hF01 E
    · refine (IntermediateField.adjoin_le_iff.2 ?_).trans le_sup_left
      rintro _ ⟨q, rfl⟩
      exact hF _ _ rfl
    · refine IntermediateField.adjoin_le_iff.2 ?_
      rintro _ ⟨⟨a, j⟩, ⟨b, l⟩, hab, rfl⟩
      dsimp only at hab
      subst hab
      by_cases ha : a ∈ Set.range κ
      · obtain ⟨k, rfl⟩ := ha
        obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, j⟩ ⟨k, rfl⟩
        obtain ⟨q, hq⟩ := hv.2.2.2 ⟨κ k, l⟩ ⟨k, rfl⟩
        have hpq : p.1 = q.1 := hv.1 ((hv.2.2.1 p).symm.trans
          ((congrArg Sigma.fst hp).trans ((congrArg Sigma.fst hq).symm.trans (hv.2.2.1 q))))
        rw [← hp, ← hq]
        exact (le_sup_left : Φ₁ ≤ _) (hΦ₁.le ((le_sup_left : F₀ ≤ F₀ ⊔ E) (hF0 p q hpq)))
      · rw [← div_div_div_cancel_right₀ (hi ⟨a, ha⟩) (G.x' ⟨a, j⟩) (G.x' ⟨a, l⟩)]
        refine (le_sup_right : IntermediateField.adjoin ℚ S ≤ _) (div_mem ?_ ?_)
        · exact IntermediateField.subset_adjoin _ _ ⟨⟨⟨a, ha⟩, j⟩, rfl⟩
        · exact IntermediateField.subset_adjoin _ _ ⟨⟨⟨a, ha⟩, l⟩, rfl⟩
    · rw [← hΦ₁]
      exact le_sup_right.trans le_sup_left

  have hy : IntermediateField.adjoin ℚ (Set.range fun q : Σ k', ι' k' => G.x' q / G.x' ⟨q.1, i' q.1⟩) = F₁ := by
    refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin_le_iff.2 ?_)
    · rintro _ ⟨q, rfl⟩
      exact hF _ _ rfl
    · rintro _ ⟨⟨a, j⟩, ⟨b, l⟩, hab, rfl⟩
      dsimp only at hab
      subst hab
      rw [← div_div_div_cancel_right₀ (hi' a) (G.x' ⟨a, j⟩) (G.x' ⟨a, l⟩)]
      exact div_mem (IntermediateField.subset_adjoin _ _ ⟨⟨a, j⟩, rfl⟩)
        (IntermediateField.subset_adjoin _ _ ⟨⟨a, l⟩, rfl⟩)
  have hker := GenFibreChartDeg.isMultiHomogIdeal_ker_rat G.x' (by rw [G.genericFibre_ker_target]; exact hP)
  have hindep : AlgebraicIndependent F₁ t := by
    have key : ∀ L : IntermediateField ℚ G.Φ', L = F₁ → AlgebraicIndependent L t →
        AlgebraicIndependent F₁ t := by
      rintro L rfl h
      exact h
    exact key _ hy ((hT ℚ G.Φ' K' ι' G.x' i' hi' hker).comp κ hv.1)

  refine (GroundTheory.Heights₂.Heights.Inter.FinrankAdjoinRange.proof ℚ G.Φ G.Φ' S).trans ?_
  change IntermediateField.relfinrank Φ₁ (Φ₁ ⊔ IntermediateField.adjoin ℚ S) = _
  rw [hΦS, ← hΦ₁]
  exact hC ℚ G.Φ' F₀ F₁ K t hF01 hindep
end GenFibreChartDeg
end GroundTheory.Heights₂.Heights.Targets
