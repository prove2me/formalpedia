-- Prove2me | solution 1 for PI.TOW.stepPure_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:39:20.943976+00:00
-- url     : https://prove2.me/submissions/c1ad6dd8-43fe-48f8-81e0-d978fa3e3d02

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FockLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FilterConcatWLength
import Theorems.Thm_PI_TOW_mem_concatW
import Theorems.Thm_PI_TOW_filter_concatW_length
import Theorems.Thm_PI_TOW_prod_smul_eq
import Theorems.Thm_PI_TOW_partS_mem
import Theorems.Thm_PI_TOW_bilin_ext_restrict
import Theorems.Thm_PI_TOW_blockSubstitution_blockInclusion
import Theorems.Thm_PI_TOW_fockB_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.TOW
open PI.TO
namespace PI.TOW
theorem _root_.solution (hL : StepLift) (hM : StepMonoFactor) : StepPure := by
  unfold StepPure
  intro hFB hOP K _ _ n' m hm vec TT d c ν hν hνc hν0 B S hB hS
  classical
  have hex : ∀ t : Fin n', ∃ (L : Finset (List (Fin (m + 1) × Fin (m + 1))))
      (a : List (Fin (m + 1) × Fin (m + 1)) → K),
      (∀ l ∈ L, l.length ≤ (if t ∈ TT then c else 0)) ∧
      ∀ P ∈ Hd K (m + 1) (d t), ∀ Q ∈ Hd K (m + 1) (d t),
        fockR (theta K m (vec t) P * S t) (theta K m (vec t) Q * B t) =
          fockR (theta K m (vec t) (∑ l ∈ L, a l • word1 l P)) (theta K m (vec t) Q) := by
    intro t
    refine hOP K m hm (vec t) (d t) (if t ∈ TT then c else 0) (ν t) (hν t) ?_ (B t) (hB t)
      (S t) (hS t)
    split_ifs with ht
    · exact hνc t ht
    · simp [hν0 t ht]
  choose L a hLlen hLfock using hex
  let f : List (Fin n' × (Fin (m + 1) × Fin (m + 1))) →₀ K :=
    ∑ w ∈ Fintype.piFinset L, Finsupp.single (concatW w) (∏ t, a t (w t))
  unfold Ok
  refine ⟨f, ?_, ?_⟩
  · intro l hl
    have hl' := Finsupp.support_finsetSum hl
    rw [Finset.mem_biUnion] at hl'
    obtain ⟨w, hw, hlw⟩ := hl'
    have hlw' := Finsupp.support_single_subset hlw
    rw [Finset.mem_singleton] at hlw'
    subst hlw'
    rw [Fintype.mem_piFinset] at hw
    unfold WordOK
    constructor
    · intro z hz
      rw [mem_concatW] at hz
      by_contra hzT
      have hlen := hLlen z.1 (w z.1) (hw z.1)
      rw [if_neg hzT] at hlen
      cases hwz : w z.1 with
      | nil => simp [hwz] at hz
      | cons _ _ => simp [hwz] at hlen
    · intro t
      rw [filter_concatW_length]
      have hlen := hLlen t (w t) (hw t)
      split_ifs at hlen <;> omega
  · have hcombo : ∀ G, combo f G =
        ∑ w ∈ Fintype.piFinset L, (∏ t, a t (w t)) • opWord (concatW w) G := by
      intro G
      simp only [combo, f]
      rw [← Finsupp.sum_finsetSum_index (fun l => zero_smul K (opWord l G))
        (fun l b₁ b₂ => add_smul b₁ b₂ (opWord l G))]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [Finsupp.sum_single_index (zero_smul K (opWord (concatW w) G))]
    have hTh : ∀ F : Fin n' → MvPolynomial (Fin (m + 1)) K,
        Th0 K m vec (∏ t, embS K t (F t)) = ∏ t, blockEmb K t (theta K m (vec t) (F t)) := by
      intro F
      rw [map_prod]
      exact Finset.prod_congr rfl fun t _ => blockSubstitution_blockInclusion vec t (F t)
    have main : ∀ P Q : Fin n' → MvPolynomial (Fin (m + 1)) K,
        (∀ t, P t ∈ Hd K (m + 1) (d t)) → (∀ t, Q t ∈ Hd K (m + 1) (d t)) →
        fockR (Th0 K m vec (∏ t, embS K t (P t)) * ∏ t, blockEmb K t (S t))
            (Th0 K m vec (∏ t, embS K t (Q t)) * ∏ t, blockEmb K t (B t)) =
          fockR (Th0 K m vec (combo f (∏ t, embS K t (P t))))
            (Th0 K m vec (∏ t, embS K t (Q t))) := by
      intro P Q hP hQ
      have hc : combo f (∏ t, embS K t (P t)) =
          ∏ t, embS K t (∑ l ∈ L t, a t l • word1 l (P t)) := by
        rw [hcombo]
        simp only [map_sum, map_smul]
        rw [Finset.prod_univ_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [prod_smul_eq, hL K n' (m + 1) w P]
      rw [hc, hTh, hTh, hTh, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      simp only [← map_mul]
      rw [hFB K (Fin n') (m + 1) (m + 1), hFB K (Fin n') (m + 1) (m + 1)]
      exact Finset.prod_congr rfl fun t _ => hLfock t (P t) (hP t) (Q t) (hQ t)
    let Φ : MvPolynomial (Fin n' × Fin (m + 1)) K →ₗ[K] MvPolynomial (Fin n' × Fin (m + 1)) K →ₗ[K] K :=
      (fockB (Fin n' × (Fin (m + 1) × Fin (m + 1))) K).compl₁₂
        ((LinearMap.mulRight K (∏ t, blockEmb K t (S t))).comp (Th0 K m vec).toLinearMap)
        ((LinearMap.mulRight K (∏ t, blockEmb K t (B t))).comp (Th0 K m vec).toLinearMap)
    let Ψ : MvPolynomial (Fin n' × Fin (m + 1)) K →ₗ[K] MvPolynomial (Fin n' × Fin (m + 1)) K →ₗ[K] K :=
      (fockB (Fin n' × (Fin (m + 1) × Fin (m + 1))) K).compl₁₂
        ((Th0 K m vec).toLinearMap.comp (comboL f)) (Th0 K m vec).toLinearMap
    have key := bilin_ext_restrict {μ | ∀ i, multideg μ i = d i} Φ Ψ (by
      intro μ hμ μ' hμ'
      show fockB _ K (Th0 K m vec (monomial μ 1) * ∏ t, blockEmb K t (S t))
          (Th0 K m vec (monomial μ' 1) * ∏ t, blockEmb K t (B t)) =
        fockB _ K (Th0 K m vec (combo f (monomial μ 1))) (Th0 K m vec (monomial μ' 1))
      rw [fockB_apply, fockB_apply, hM K n' (m + 1) μ, hM K n' (m + 1) μ']
      exact main _ _ (fun t => partS_mem μ hμ t) (fun t => partS_mem μ' hμ' t))
    intro G hG H hH
    rw [← fockB_apply, ← fockB_apply]
    exact key G hG H hH
end PI.TOW
