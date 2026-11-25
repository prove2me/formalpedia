-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SemilocRankFrac_proof_10770169632e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:15:49.405692+00:00
-- url     : https://prove2.me/submissions/c9f5a462-f57b-443f-aa79-e20d707259fe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocRankFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRankFracDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocChartRatio
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocRankFrac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocRankFrac_aeval_scale_div_83e03c384ca6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocRankFrac_aeval_mem_7e0632d6d4b1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocRankFrac_fracEval_algebraMap_cf6041a4f59e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_X_cf870dae9c4f
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isMultiHomog_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open SemilocRankFrac
namespace GroundTheory.Heights₂.Heights.Inter
namespace SemilocRankFrac
theorem _root_.solution (hR : RankFracDegree.Statement) (hF : SemilocFinite.Statement)
    (hC : SemilocChartRatio.Statement) : SemilocRankFrac.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G s α W i' hv hP' _ hQ hs hsQ hW hi'
  have := hP'.2.1.1
  have := imageZ_isPrime_of_prime v P'
  let _ := (locToSemiloc hv P' W).toAlgebra
  have hx : ∀ k', G.x' ⟨k', i' k'⟩ ≠ 0 := fun k' h0 =>
    hi' k' (by rw [← G.genericFibre_ker_target, RingHom.mem_ker, aeval_X, h0])
  have hch : ∀ {a b : K'}, a = b → G.x' ⟨a, i' a⟩ = G.x' ⟨b, i' b⟩ := by
    rintro a b rfl
    rfl
  let ψ := fracEval G.x' P' G.genericFibre_ker_target
  let y' : (Σ k', ι' k') → G.Φ' := fun q => G.x' q / G.x' ⟨q.1, i' q.1⟩
  let L₀ := IntermediateField.adjoin ℚ (Set.range (y' ∘ v))
  let L := IntermediateField.adjoin ℚ (Set.range y')
  have hx' : G.x' = fun q => y' q * G.x' ⟨q.1, i' q.1⟩ := funext fun q => (div_mul_cancel₀ _ (hx q.1)).symm
  have hxv : G.x' ∘ v = fun p => (y' ∘ v) p * G.x' ⟨κ p.1, i' (κ p.1)⟩ := funext fun p => by
    show G.x' (v p) = G.x' (v p) / G.x' ⟨(v p).1, i' (v p).1⟩ * G.x' ⟨κ p.1, i' (κ p.1)⟩
    rw [hch (hv.2.2.1 p), div_mul_cancel₀ _ (hx _)]
  have hψ : ∀ u w : MRing ι', (hw : Ideal.Quotient.mk P' w ∈ nonZeroDivisors (MRing ι' ⧸ P')) →
      ψ (IsLocalization.mk' _ (Ideal.Quotient.mk P' u) ⟨_, hw⟩) = aeval G.x' u / aeval G.x' w := fun u w hw => by
    rw [IsFractionRing.mk'_eq_div, map_div₀, fracEval_algebraMap, fracEval_algebraMap]
  let f := ψ.comp ((fracMapZ v P').comp (locRing (imageZ v P') W).subtype)
  let g := ψ.comp (semiLocRing P' (fibreOver v P' W)).subtype
  have hf : ∀ u w : MRing ι, (hw : Ideal.Quotient.mk (imageZ v P') w ∈ nonZeroDivisors (MRing ι ⧸ imageZ v P')) →
      ψ (fracMapZ v P' (IsLocalization.mk' _ (Ideal.Quotient.mk _ u) ⟨_, hw⟩)) =
        aeval (G.x' ∘ v) u / aeval (G.x' ∘ v) w := fun u w hw => by
    rw [IsFractionRing.mk'_eq_div, map_div₀, map_div₀, fracMapZ_algebraMap, fracMapZ_algebraMap,
      fracEval_algebraMap, fracEval_algebraMap, aeval_rename, aeval_rename]

  have hfL : ∀ a, f a ∈ L₀ := by
    have hle : locRing (imageZ v P') W ≤ (L₀.toSubalgebra.toSubring.comap ψ).comap (fracMapZ v P') := by
      rw [locRing, Subring.closure_le]
      rintro _ ⟨u, w, a, hw, -, hu, hwa, rfl⟩
      show ψ (fracMapZ v P' _) ∈ L₀
      rw [hf, hxv, aeval_scale_div _ (fun k => hx _) hu hwa]
      exact div_mem (aeval_mem L₀ (fun p => IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩) u)
        (aeval_mem L₀ (fun p => IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩) w)
    exact fun a => hle a.2
  have hgL : ∀ b, g b ∈ L := by
    have hle : semiLocRing P' (fibreOver v P' W) ≤ L.toSubalgebra.toSubring.comap ψ := by
      rw [semiLocRing, Subring.closure_le]
      rintro _ ⟨u, w, a, hw, -, hu, hwa, rfl⟩
      show ψ _ ∈ L
      have e := aeval_scale_div y' hx hu hwa
      rw [← hx'] at e
      rw [hψ, e]
      exact div_mem (aeval_mem L (fun q => IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩) u)
        (aeval_mem L (fun q => IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩) w)
    exact fun b => hle b.2

  have hgen : ∀ (T : Set G.Φ') (S : Subfield G.Φ'), T ⊆ S →
      (IntermediateField.adjoin ℚ T).toSubfield ≤ S := fun T S hT z hz =>
    (IntermediateField.adjoin_le_iff (F := ℚ) (T := S.toIntermediateField fun r => by
      rw [eq_ratCast]; exact SubfieldClass.ratCast_mem S r)).2 hT hz
  have hL₀ : L₀.toSubfield ≤ Subfield.closure (Set.range f) := by
    refine hgen _ _ ?_
    rintro _ ⟨⟨k, i⟩, rfl⟩
    obtain ⟨j, hj⟩ := hW.2 k
    obtain ⟨⟨k0, i0⟩, hp0⟩ := hv.2.2.2 ⟨κ k, i' (κ k)⟩ ⟨k, rfl⟩
    obtain rfl : k0 = k := hv.1 ((hv.2.2.1 ⟨k0, i0⟩).symm.trans (congrArg Sigma.fst hp0))
    have hjQ : (X ⟨k0, j⟩ : MRing ι) ∉ imageZ v P' := fun h0 => hj (hW.1.1.2 (Ideal.mem_sup_left h0))
    have hw : Ideal.Quotient.mk (imageZ v P') (X ⟨k0, j⟩) ∈ nonZeroDivisors _ :=
      mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    have hx0 : G.x' (v ⟨k0, j⟩) ≠ 0 := fun h0 => hjQ (by
      rw [imageZ, Ideal.mem_comap, ← G.genericFibre_ker_target, RingHom.mem_ker]
      simpa [aeval_rename] using h0)
    classical
    have mem : ∀ i₁ : ι k0, IsLocalization.mk' (FractionRing (MRing ι ⧸ imageZ v P'))
        (Ideal.Quotient.mk _ (X ⟨k0, i₁⟩)) ⟨_, hw⟩ ∈ locRing (imageZ v P') W := fun i₁ =>
      Subring.subset_closure ⟨_, _, Pi.single k0 1, hw, hj, AvoidRing.isMultiHomog_X k0 i₁,
        AvoidRing.isMultiHomog_X k0 j, rfl⟩
    have e : (y' ∘ v) ⟨k0, i⟩ = f ⟨_, mem i⟩ / f ⟨_, mem i0⟩ := by
      show G.x' (v ⟨k0, i⟩) / G.x' ⟨(v ⟨k0, i⟩).1, i' (v ⟨k0, i⟩).1⟩ =
        ψ (fracMapZ v P' (IsLocalization.mk' _ (Ideal.Quotient.mk _ (X ⟨k0, i⟩)) ⟨_, hw⟩)) /
          ψ (fracMapZ v P' (IsLocalization.mk' _ (Ideal.Quotient.mk _ (X ⟨k0, i0⟩)) ⟨_, hw⟩))
      rw [hf, hf, hch (hv.2.2.1 _)]
      simp only [aeval_X, Function.comp, hp0]
      rw [div_div_div_cancel_right₀ hx0]
    rw [e]
    exact div_mem (Subfield.subset_closure ⟨_, rfl⟩) (Subfield.subset_closure ⟨_, rfl⟩)
  have hL : L.toSubfield ≤ Subfield.closure (Set.range g) := by
    refine hgen _ _ ?_
    rintro _ ⟨q, rfl⟩
    obtain ⟨b, b', hb', e⟩ := hC K ι K' ι' κ v P' n s α W i' hv hP' hQ hs hsQ hW hi' q
    have e' := congrArg ψ e
    rw [map_mul, map_mul, fracEval_algebraMap, fracEval_algebraMap, aeval_X, aeval_X] at e'
    have hψb' : g b' ≠ 0 := (map_ne_zero ψ).2 hb'
    have : y' q = g b / g b' := by
      rw [div_eq_div_iff (hx _) hψb']
      show G.x' q * ψ b' = ψ b * G.x' ⟨q.1, i' q.1⟩
      rw [e']
      exact mul_comm _ _
    rw [this]
    exact div_mem (Subfield.subset_closure ⟨_, rfl⟩) (Subfield.subset_closure ⟨_, rfl⟩)
  exact hR ℚ G.Φ' _ _ L₀ L f g (ψ.injective.comp ((fracMapZ v P').injective.comp Subtype.val_injective))
    (ψ.injective.comp Subtype.val_injective) (fun _ => rfl) hfL hgL hL₀ hL
    (hF K ι K' ι' κ v P' n s α W hv hP' hQ hs hsQ hW).1
end SemilocRankFrac
end GroundTheory.Heights₂.Heights.Inter
