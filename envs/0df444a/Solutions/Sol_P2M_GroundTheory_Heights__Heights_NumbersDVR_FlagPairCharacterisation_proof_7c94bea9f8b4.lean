-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_proof_7c94bea9f8b4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:13:25.230716+00:00
-- url     : https://prove2.me/submissions/c1b7e0f0-cbf3-4c40-a4ad-ad2cd7d34937

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinVertDivIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinGradedFrameIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinFlagPairIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_finrank_flag_cd1463bfacd3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_flag_eq_74c67895a811
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_flag_mono_135fd2cc50e5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_mem_flag_iff_fab23907a0d5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_linearIndependent_gen_14b256204798
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_eval_ne_zero_c36d901ca082
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FlagTypings_triangular_flip_c64dc765f2e4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_CutByForm_proof_b44260dcf444
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_proof_fb2253ef6956
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_repr_of_sub_mem_5ce60ba3d5bd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MinimalPrimeMultiHomog_proof_00f169244e2b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Representative_proof_61b56da860aa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_UniformiserCase_proof_3d83087b97ab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorCharacterisation_proof_037b62304aa2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_VocabMultiHomogIdeal_proof_6afd59a7e16a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_VocabMultiHomog_proof_8751c6dffe37


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
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
universe u v w
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairCharacterisation
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairCharacterisation
theorem _root_.solution : Statement.{u, v, w} := by
  intro O _ _ _ Ω _ _ K _ _ ι _ y N E _ _ B B' ϖ hϖ hP
  have hV : ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor (pointIdeal O y) ϖ b f g ↔
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O y) b f g :=
    fun b f g => (VerticalDivisorCharacterisation.proof O K ι (pointIdeal O y) ϖ b f g hϖ hP).symm
  have hG := fun (B₀ : ChartBundle O (segreVec y) N E) (w₀ : Module.Basis (Fin N) Ω E)
      (b : Fin N → K → ℤ) => GradedFrameCharacterisation.proof O Ω K ι y N E B₀ w₀ b
  refine ⟨fun w w' x x' f g => ⟨fun h => ?_, ?_⟩, fun hc F => ?_⟩
  · have hvert := fun i => (hV _ _ _).1 (h.vertical i)
    have hgy : ∀ i, aeval y (g i) ≠ 0 := fun i => eval_ne_zero (hvert i)
    have hflip := FlagTypings.triangular_flip w w' h.sameFlag
    have hspan : (fun i : Fin (N + 1) => Submodule.span Ω (w' '' {j : Fin N | (j : ℕ) < i})) =
        fun i : Fin (N + 1) => Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i}) := by
      funext i
      refine flag_eq w (flag_mono w') (finrank_flag w') (fun j => ?_) i
      rw [mem_flag_iff]
      intro q hq
      exact hflip.1 j q (Fin.lt_def.mpr (by simp at hq; omega))
    refine ⟨{ Vs := fun i : Fin (N + 1) => Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i})
              mono := flag_mono w
              dim := finrank_flag w
              top := ?_
              deg := x
              gen := w
              gen_mem := fun i => ?_
              frame := (hG B w x).1 h.flag
              deg' := x'
              gen' := w'
              gen'_mem := fun i => ?_
              frame' := ?_
              f := f
              g := g
              rel := fun i => ?_
              vert := hvert }, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · show Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < (Fin.last N : ℕ)}) = ⊤
      have hu : {j : Fin N | (j : ℕ) < (Fin.last N : ℕ)} = Set.univ := by
        ext j
        simp
      rw [hu, Set.image_univ, w.span_eq]
    · show w i ∈ Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < (i.succ : ℕ)})
      rw [mem_flag_iff]
      intro q hq
      rw [w.repr_self, Finsupp.single_apply, if_neg]
      rintro rfl
      simp at hq
    · show w' i ∈ Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < (i.succ : ℕ)})
      rw [mem_flag_iff]
      intro q hq
      exact h.sameFlag i q (Fin.lt_def.mpr (by simp at hq; omega))
    · have := (hG B' w' x').1 h.flag'
      rwa [hspan] at this
    · show _ ∈ Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < (i.castSucc : ℕ)})
      rw [mem_flag_iff]
      intro q hq
      rw [map_sub, map_smul, w.repr_self, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
        Finsupp.single_apply]
      by_cases hiq : i = q
      · subst hiq
        rw [if_pos rfl, mul_one, h.generic i, mul_div_cancel_right₀ _ (hgy i), sub_self]
      · rw [if_neg hiq, mul_zero, sub_zero]
        exact h.sameFlag i q (lt_of_le_of_ne (Fin.le_def.mpr (by simpa using hq)) hiq)
  · rintro ⟨F, hgen, hgen', rfl, rfl, rfl, rfl⟩
    have hVs : F.Vs = fun i : Fin (N + 1) => Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i}) :=
      funext (flag_eq w F.mono F.dim fun j => by rw [← hgen]; exact F.gen_mem j)
    have hVs' : F.Vs = fun i : Fin (N + 1) => Submodule.span Ω (w' '' {j : Fin N | (j : ℕ) < i}) :=
      funext (flag_eq w' F.mono F.dim fun j => by rw [← hgen']; exact F.gen'_mem j)
    refine ⟨(hG B w F.deg).2 ?_, (hG B' w' F.deg').2 ?_, fun i j hij => ?_,
      fun i => (hV _ _ _).2 (F.vert i), fun i => ?_⟩
    · have := F.frame
      rwa [hVs, hgen] at this
    · have := F.frame'
      rwa [hVs', hgen'] at this
    · have := F.gen'_mem i
      rw [hVs, hgen'] at this
      exact (mem_flag_iff w _ _).1 this j (by simp; omega)
    · have := F.rel i
      rw [hVs, hgen, hgen'] at this
      have h2 := (GradedFrameCharacterisation.repr_of_sub_mem w this).2
      rw [h2, div_mul_cancel₀ _ (eval_ne_zero (F.vert i))]
  · obtain ⟨c, hc⟩ := hc
    exact ⟨linearIndependent_gen F.mono F.dim F.gen_mem F.frame hc,
      linearIndependent_gen F.mono F.dim F.gen'_mem F.frame' hc⟩
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairCharacterisation
