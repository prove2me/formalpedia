-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_WeierstrassFiniteness_proof_3564ffd91f19
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:05:47.185271+00:00
-- url     : https://prove2.me/submissions/4112a17f-38ea-4eae-a514-a2e9fa00ea95

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeierstrassFiniteness
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteModuloIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteModuloEliminate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PWeierstrassFiniteness
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_zeroCoordinate_apply_d48952ae67a2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace WeierstrassFiniteness
theorem _root_.solution (hE : FiniteModuloEliminate.Statement)
    (hI : FiniteModuloIntegral.Statement) : WeierstrassFiniteness.Statement := by
  intro σ _ x k f d A hf hpow g hg
  classical

  let L : Finset σ → (σ → ℂ) →L[ℂ] (Fin d ⊕ σ → ℂ) := fun S =>
    ContinuousLinearMap.pi (Sum.elim (fun j => (ContinuousLinearMap.proj j).comp A)
      (fun l => if l ∈ S then ContinuousLinearMap.proj l else 0))
  have hL : ∀ S z c, L S z c = Sum.elim (fun j => A z j) (fun l => if l ∈ S then z l else 0) c := by
    intro S z c
    rcases c with j | l
    · simp [L]
    · by_cases hl : l ∈ S <;> simp [L, hl]
  have key : ∀ T : Finset σ, IsFiniteModuloOver x f (L (Finset.univ \ T)) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      rw [Finset.sdiff_empty]
      let P : (Fin d ⊕ σ → ℂ) →L[ℂ] (σ → ℂ) :=
        ContinuousLinearMap.pi fun l => ContinuousLinearMap.proj (Sum.inr l)
      have hPL : ∀ z, P (L Finset.univ z) = z := fun z => by
        funext l; simp [P, hL]
      refine ⟨1, fun _ _ => 1, fun _ => analyticAt_const, fun g hg => ?_⟩
      refine ⟨fun _ y => g (P y), fun _ _ => 0, fun _ => ?_, fun _ => analyticAt_const,
        Eventually.of_forall fun z => by simp only [hPL]; simp⟩
      have hg' : AnalyticAt ℂ g (P (L Finset.univ x)) := by rw [hPL]; exact hg
      exact hg'.comp (P.analyticAt _)
    | insert l T hl ih =>
      have heq : L (Finset.univ \ insert l T) = (zeroCoordinate (Sum.inr l)).comp (L (Finset.univ \ T)) := by
        ext z c
        rw [ContinuousLinearMap.comp_apply, zeroCoordinate_apply, hL, hL]
        rcases c with j | l'
        · simp
        · by_cases h1 : l' = l
          · subst h1; simp
          · by_cases h2 : l' ∈ T <;> simp [h1, h2]
      rw [heq]
      obtain ⟨r, h, h', hh, hh', hev⟩ := hpow l
      refine hE σ (Fin d ⊕ σ) x k f _ (Sum.inr l) hf ih
        ⟨r, h, Sum.elim h' (fun _ _ => 0), hh, ?_, ?_⟩
      · rintro (j | l')
        · exact hh' j
        · exact analyticAt_const
      · filter_upwards [hev] with z hz
        simp only [zeroCoordinate_apply, hL, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
          Finset.mem_sdiff, Finset.mem_univ, hl, not_false_eq_true, and_self, if_true,
          reduceCtorEq, if_false, zero_mul, Finset.sum_const_zero, add_zero]
        exact hz
  have hfin := key Finset.univ
  obtain ⟨N, a, h, ha, hh, hev⟩ := hI σ (Fin d ⊕ σ) x k f _ hf hfin g hg

  let J : (Fin d → ℂ) →L[ℂ] (Fin d ⊕ σ → ℂ) :=
    ContinuousLinearMap.pi (Sum.elim (fun j => ContinuousLinearMap.proj j) (fun _ => 0))
  have hJ : ∀ z, J (A z) = L (Finset.univ \ Finset.univ) z := fun z => by
    funext c; rcases c with j | l <;> simp [J, hL]
  refine ⟨N, fun j w => a j (J w), h, fun j => ?_, hh, ?_⟩
  · have haj : AnalyticAt ℂ (a j) (J (A x)) := by rw [hJ]; exact ha j
    exact haj.comp (J.analyticAt _)
  · filter_upwards [hev] with z hz
    simpa only [hJ] using hz
end WeierstrassFiniteness
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
