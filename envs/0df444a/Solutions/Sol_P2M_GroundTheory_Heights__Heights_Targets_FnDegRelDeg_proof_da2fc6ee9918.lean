-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_proof_da2fc6ee9918
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:10:58.936518+00:00
-- url     : https://prove2.me/submissions/a68f7102-009f-4a8b-947d-e1ac7b8ba17d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsFnDegRelDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PFnDegRelDeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_exists_div_of_mem_adjoin_ec9f4957fb2e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_finrank_eq_relfinrank_9ba6a3c067f1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_dehom_mem_homFracDegZero_2b17e515c6a8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_div_eq_dehom_div_53c373175551
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_contractFracMap_comp_dehom_643f296b3106
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_dehom_eq_zero_of_mem_chartIdeal_c19722018421
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_mem_chartIdeal_of_dehom_eq_zero_3eb777d45518


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Targets.FnDegRelDeg
namespace GroundTheory.Heights₂.Heights.Targets.FnDegRelDeg
theorem _root_.solution : FnDegRelDeg.Statement.{u} := by
  intro F _ K K' _ _ _ _ ι _ ι' _ κ v hκv P' hP' i' hi
  have := hP'.isPrime
  set j : K ↪ K' := ⟨κ, hκv.1⟩

  have hu : ∀ q : Σ k, ι k, ∃ r : ι' (j q.1), blockIncl j ι' ⟨q.1, r⟩ = v q := by
    intro q
    have h := hκv.2.2.1 q
    revert h
    generalize v q = q'
    obtain ⟨k', r⟩ := q'
    rintro (h : k' = κ q.1)
    subst h
    exact ⟨r, rfl⟩
  let ucoord : (Σ k, ι k) → (Σ k, ι' (j k)) := fun q => ⟨q.1, (hu q).choose⟩
  have hucoord : blockIncl j ι' ∘ ucoord = v := funext fun q => (hu q).choose_spec
  have hw : ∀ r : Σ k, ι' (j k), ∃ q, v q = blockIncl j ι' r := fun r => hκv.2.2.2 _ ⟨r.1, rfl⟩
  let wcoord : (Σ k, ι' (j k)) → (Σ k, ι k) := fun r => (hw r).choose
  have hwcoord : v ∘ wcoord = blockIncl j ι' := funext fun r => (hw r).choose_spec
  have hi0 : ∀ k, (X ⟨k, i' (j k)⟩ : MRing (fun k => ι' (j k)) F) ∉ contractPrime j P' := by
    intro k h
    have h' := Ideal.mem_comap.1 h
    rw [rename_X] at h'
    exact hi (j k) h'

  let ρ := Ideal.Quotient.liftₐ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal P' i') (IntNumPoint.dehom P' i')
    (fun a ha => IntNumPoint.dehom_eq_zero_of_mem_chartIdeal i' hi hP'.multiHomog ha)
  have hρ : ∀ f, ρ (Ideal.Quotient.mk _ f) = IntNumPoint.dehom P' i' f := fun f => rfl
  have hρinj : Function.Injective ρ := by
    refine (injective_iff_map_eq_zero ρ).2 fun a ha => ?_
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [hρ] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.2 (IntNumPoint.mem_chartIdeal_of_dehom_eq_zero i' hi ha)
  let _ := (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i').toAlgebra
  have hτ : ∀ p : MRing ι F, ρ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i' (Ideal.Quotient.mk _ p)) =
      IntNumPoint.dehom P' i' (rename v p) := fun p => rfl
  have key : ∀ p : MRing ι F, IntNumPoint.dehom P' i' (rename v p) =
      contractFracMap j P' (IntNumPoint.dehom (contractPrime j P') (fun k => i' (j k))
        (rename ucoord p)) := by
    intro p
    have e : rename v p = rename (blockIncl j ι') (rename ucoord p) := by
      rw [rename_rename, hucoord]
    rw [e]
    exact (AlgHom.congr_fun (contractFracMap_comp_dehom j P' i') _).symm
  have key2 : ∀ f, contractFracMap j P' (IntNumPoint.dehom (contractPrime j P')
      (fun k => i' (j k)) f) =
      ρ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i' (Ideal.Quotient.mk _ (rename wcoord f))) := by
    intro f
    rw [hτ, rename_rename, hwcoord]
    exact AlgHom.congr_fun (contractFracMap_comp_dehom j P' i') f
  have hρH : ∀ x, ρ x ∈ homFracDegZero P' := by
    intro x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact dehom_mem_homFracDegZero P' i' hi f
  have hτE : ∀ x, ρ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i' x) ∈
      (homFracDegZero (contractPrime j P')).map (contractFracMap j P') := by
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hτ, key]
    exact (IntermediateField.mem_map _).2 ⟨_, dehom_mem_homFracDegZero _ _ hi0 _, rfl⟩
  have hHq : ∀ z ∈ homFracDegZero P', ∃ x y, z = ρ x / ρ y := by
    intro z hz
    refine exists_div_of_mem_adjoin ρ.toRingHom (fun c => ⟨algebraMap F _ c, ρ.commutes c⟩) ?_
    revert z
    show homFracDegZero P' ≤ _
    unfold homFracDegZero
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨b, f, g, hf, hg, hgP, rfl⟩
    rw [div_eq_dehom_div P' i' hi hf hg]
    exact div_mem (IntermediateField.subset_adjoin _ _ ⟨Ideal.Quotient.mk _ f, rfl⟩)
      (IntermediateField.subset_adjoin _ _ ⟨Ideal.Quotient.mk _ g, rfl⟩)
  have hEq : ∀ z ∈ (homFracDegZero (contractPrime j P')).map (contractFracMap j P'),
      ∃ x y, z = ρ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i' x) /
        ρ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i' y) := by
    intro z hz
    refine exists_div_of_mem_adjoin (ρ.toRingHom.comp (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i'))
      (fun c => ⟨Ideal.Quotient.mk _ (C c), ?_⟩) ?_
    · show ρ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i' (Ideal.Quotient.mk _ (C c))) = _
      rw [hτ, rename_C]
      exact (IntNumPoint.dehom P' i').commutes c
    revert z
    show (homFracDegZero (contractPrime j P')).map (contractFracMap j P') ≤ _
    unfold homFracDegZero
    rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
    rintro _ ⟨_, ⟨d, f, g, hf, hg, hgP, rfl⟩, rfl⟩
    rw [div_eq_dehom_div _ _ hi0 hf hg, map_div₀, key2, key2]
    exact div_mem (IntermediateField.subset_adjoin _ _ ⟨Ideal.Quotient.mk _ (rename wcoord f), rfl⟩)
      (IntermediateField.subset_adjoin _ _ ⟨Ideal.Quotient.mk _ (rename wcoord g), rfl⟩)
  have hEH : (homFracDegZero (contractPrime j P')).map (contractFracMap j P') ≤
      homFracDegZero P' := by
    intro z hz
    obtain ⟨x, y, rfl⟩ := hEq z hz
    exact div_mem (hρH _) (hρH _)
  unfold ReciprocityTheory.ChartRestriction.G.AI.I1.fnDeg relDeg
  exact finrank_eq_relfinrank ρ.toRingHom hρinj _ _ hEH
    (fun a b h => Ideal.quotientMap_injective (hρinj h)) hτE hρH hEq hHq
end GroundTheory.Heights₂.Heights.Targets.FnDegRelDeg
