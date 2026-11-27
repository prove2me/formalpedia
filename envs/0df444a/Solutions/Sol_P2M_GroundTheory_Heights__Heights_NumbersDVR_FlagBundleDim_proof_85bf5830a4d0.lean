-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleDim_proof_85bf5830a4d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:05:06.626976+00:00
-- url     : https://prove2.me/submissions/4819f088-802e-4bc6-89d4-4402f74bc698

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensSpan
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSpanBundleDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleDim

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
namespace FlagBundleDim
theorem _root_.solution (hspan : TwistedDualGensSpan.Statement)
    (hdim : SpanBundleDim.Statement) : FlagBundleDim.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hV hdimV N E _ _ B w b hflag M a φ hφ Φ _ _ t ht i hi1 hiN

  have hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0 := fun k => by
    obtain ⟨j, hj⟩ := hV.relevant k
    refine ⟨j, fun h0 => hj ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    simp [pointConeMap, h0]
  choose c hc using hne
  have hyc : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hsp := hspan F Ω K ι y N E B a M φ hφ c hyc

  have hv : ∀ m : Fin N, ∃ v ∈ B.lat c, (∀ j, m < j → w.repr v j = 0) ∧
      w.repr v m = ∏ k, y ⟨k, c k⟩ ^ b m k := by
    intro m
    have hmem : (∏ k, y ⟨k, c k⟩ ^ b m k) ∈ degLat F y (b m) c := ⟨1, one_mem _, (one_mul _).symm⟩
    rw [← hflag.graded c hyc m] at hmem
    exact hmem
  choose v hvl hvz hvd using hv
  obtain ⟨ι', hι'⟩ : ∃ ι' : Fin i → Fin N, ι' = Fin.castLE hiN := ⟨_, rfl⟩
  have hsum : ∀ {β : Type} [AddCommMonoid β] (f : Fin N → β), (∀ j : Fin N, i ≤ (j : ℕ) → f j = 0) →
      ∑ j, f j = ∑ j : Fin i, f (ι' j) := by
    intro β _ f hf
    have hm : ∑ j : Fin i, f (ι' j) = ∑ j ∈ Finset.univ.map (Fin.castLEEmb hiN), f j := by
      rw [Finset.sum_map, hι']
      rfl
    rw [hm]
    refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => hf j ?_).symm
    by_contra h
    exact hj (Finset.mem_map.mpr ⟨⟨j, by omega⟩, Finset.mem_univ _, rfl⟩)
  obtain ⟨G, hG⟩ : ∃ G : Fin M → Fin i → Ω, G = fun l j => φ l (w (ι' j)) := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : Matrix (Fin i) (Fin i) Ω, H = Matrix.of fun j m => w.repr (v (ι' m)) (ι' j) :=
    ⟨_, rfl⟩
  have hinj : Function.Injective ι' := by
    rw [hι']
    exact Fin.castLE_injective hiN
  have hval : ∀ m : Fin i, ((ι' m : Fin N) : ℕ) = m := fun m => by
    rw [hι', Fin.val_castLE]
  have hlt : ∀ m j : Fin i, m < j → ι' m < ι' j := fun m j h => by
    rw [Fin.lt_def, hval, hval]
    exact Fin.lt_def.mp h
  have hGH : ∀ l m, (Matrix.of G * H) l m = φ l (v (ι' m)) := by
    intro l m
    conv_rhs => rw [← w.sum_repr (v (ι' m))]
    rw [map_sum, hsum]
    · simp [Matrix.mul_apply, hG, hH, mul_comm]
    · intro j hj
      have hm := m.isLt
      rw [map_smul, hvz _ j (by rw [Fin.lt_def, hval]; omega), zero_smul]
  have hdet : IsUnit H.det := by
    rw [Matrix.det_of_isUpperTriangular (M := H) fun j m hjm => by
      rw [hH, Matrix.of_apply]
      exact hvz _ _ (hlt m j hjm)]
    refine isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun m _ => ?_)
    simp only [hH, Matrix.of_apply, hvd]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  have hlin : LinearIndependent Ω (fun j l => G l j) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hall : ∀ ψ ∈ Submodule.span Ω (Set.range φ), ψ (∑ j, g j • w (ι' j)) = 0 := by
      intro ψ hψ
      induction hψ using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨l, rfl⟩ := hx
        have := congrFun hg l
        simpa [hG, map_sum, Finset.sum_apply, mul_comm] using this
      | zero => simp
      | add x z _ _ hx hz => rw [LinearMap.add_apply, hx, hz, add_zero]
      | smul r x _ hx => rw [LinearMap.smul_apply, hx, smul_zero]
    rw [hsp] at hall
    have hw := (Module.forall_dual_apply_eq_zero_iff Ω _).mp fun ψ => hall ψ Submodule.mem_top
    exact Fintype.linearIndependent_iff.mp (w.linearIndependent.comp ι' hinj) g hw
  have hcoord : projCoord y w φ (truncCoord t i) =
      projCoord y (Pi.basisFun Ω (Fin i)) (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) (t ∘ ι') := by
    funext p
    rcases p with ⟨_ | k, l⟩
    · show ∑ j, truncCoord t i j * _ = ∑ j, _
      rw [hsum]
      · refine Finset.sum_congr rfl fun j _ => ?_
        have hj : ((ι' j : Fin N) : ℕ) < i := by rw [hval]; exact j.isLt
        simp only [truncCoord, hj, if_true, hG, Function.comp_apply, Pi.basisFun_apply]
        rw [LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
        rfl
      · intro j hj
        simp [truncCoord, not_lt.mpr hj]
    · rfl
  have hproj : projIdeal F y w φ (truncCoord t i) = projIdeal F y (Pi.basisFun Ω (Fin i))
      (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) (t ∘ ι') := by
    unfold projIdeal
    rw [hcoord]
  rw [hproj]
  exact hdim F Ω K ι y e hV hdimV M i G (by omega) hlin c a H hyc hdet
    (fun l m => by rw [hGH]; exact hφ.sections c hyc l _ (hvl _)) Φ (t ∘ ι')
    (ht.comp ι' hinj)
end FlagBundleDim
end GroundTheory.Heights₂.Heights.NumbersDVR
