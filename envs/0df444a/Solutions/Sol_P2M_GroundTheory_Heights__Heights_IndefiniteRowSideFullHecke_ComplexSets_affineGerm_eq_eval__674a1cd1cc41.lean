-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_affineGerm_eq_eval__674a1cd1cc41
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:31:31.368084+00:00
-- url     : https://prove2.me/submissions/b3c67ddf-fbb4-4c7a-86de-87f2e351efb8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermProjectionStep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermGeneralCoordinates
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermProjectionStep

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
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {σ : Type} [Fintype σ] {d : ℕ} (w : σ → ℂ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (L : (σ → ℂ) →L[ℂ] ℂ) (c : ℂ) :
    ∃ F : MvPolynomial σ (holGerms (A w)),
      MvPolynomial.eval₂ (germPull A (A.analyticAt w) rfl) (coordGerm w) F = affineGerm w L c := by
  classical
  let k : ℂ → holGerms (A w) := fun a => ⟨↑(fun _ : Fin d → ℂ => a), fun _ => a, analyticAt_const, rfl⟩
  have hk : ∀ a, ((germPull A (A.analyticAt w) rfl (k a) : holGerms w) : Germ (𝓝 w) ℂ) =
      ↑((fun _ : Fin d → ℂ => a) ∘ A) := fun a => germPull_coe _ _ rfl (k a) _ rfl
  refine ⟨∑ i, MvPolynomial.C (k (L (fun j => if i = j then 1 else 0))) * MvPolynomial.X i +
    MvPolynomial.C (k c), ?_⟩
  simp only [MvPolynomial.eval₂_add, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
    MvPolynomial.eval₂_X]
  apply Subtype.ext
  rw [Subring.coe_add, AddSubmonoidClass.coe_finsetSum]
  simp only [Subring.coe_mul, hk]
  change ∑ i, Germ.coeRingHom _ ((fun _ : Fin d → ℂ => L (fun j => if i = j then 1 else 0)) ∘ A) *
      Germ.coeRingHom _ (fun z : σ → ℂ => z i) + Germ.coeRingHom _ ((fun _ : Fin d → ℂ => c) ∘ A) =
    Germ.coeRingHom _ (fun z : σ → ℂ => L z + c)
  simp only [← map_mul, ← map_sum, ← map_add]
  congr 1
  funext z
  have hL := (L : (σ → ℂ) →ₗ[ℂ] ℂ).pi_apply_eq_sum_univ z
  simp only [ContinuousLinearMap.coe_coe] at hL
  simp [hL, Finset.sum_apply, mul_comm]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
