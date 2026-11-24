-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_polyToGerm_finPoly_d448074637f3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:49.503916+00:00
-- url     : https://prove2.me/submissions/5e1b0cda-5e52-4142-8002-5b5f9270f176

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_WeierstrassRemainderUnique
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticGermsNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHolGermsDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_WeierstrassPolynomialRing

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
open Topology Filter Polynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {σ : Type} [Fintype σ] {d : ℕ} (a : Fin d → (σ → ℂ) → ℂ)
    (ha : ∀ j, AnalyticAt ℂ (a j) 0) :
    ((polyToGerm σ (finPoly fun j => mkGerm (a j) (ha j)) : holGerms (0 : Option σ → ℂ)) :
      Germ (𝓝 (0 : Option σ → ℂ)) ℂ) =
      ↑(fun x : Option σ → ℂ => ∑ j : Fin d, a j (fun i => x (some i)) * x none ^ (j : ℕ)) := by
  have hι : ∀ j, ((germLift σ (mkGerm (a j) (ha j)) : holGerms (0 : Option σ → ℂ)) :
      Germ (𝓝 (0 : Option σ → ℂ)) ℂ) = ↑(a j ∘ lastProj σ) :=
    fun j => germPull_coe _ _ _ (mkGerm (a j) (ha j)) (a j) rfl
  simp only [finPoly, polyToGerm, map_sum, map_mul, map_pow, coe_eval₂RingHom, eval₂_C, eval₂_X]
  rw [AddSubmonoidClass.coe_finsetSum]
  simp only [Subring.coe_mul, Subring.coe_pow, hι]
  change ∑ j : Fin d, Germ.coeRingHom _ (a j ∘ lastProj σ) *
      Germ.coeRingHom _ (fun x : Option σ → ℂ => x none) ^ (j : ℕ) = Germ.coeRingHom _ _
  simp only [← map_mul, ← map_pow, ← map_sum]
  congr 1
  funext x
  simp [Finset.sum_apply, lastProj]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
