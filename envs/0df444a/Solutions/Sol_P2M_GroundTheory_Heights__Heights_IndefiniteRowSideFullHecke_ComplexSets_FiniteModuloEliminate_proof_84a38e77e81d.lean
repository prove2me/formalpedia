-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteModuloEliminate_proof_84a38e77e81d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:58:18.001975+00:00
-- url     : https://prove2.me/submissions/95ee92bc-393a-41b9-a60e-05ffc7b2be92

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteModuloEliminate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteModuloGeneralEquation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeierstrassDivisionAtPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteModuloEliminate

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
namespace FiniteModuloEliminate
theorem _root_.solution (hG : FiniteModuloGeneralEquation.Statement)
    (hW : WeierstrassDivisionAtPoint.Statement) : FiniteModuloEliminate.Statement := by
  intro σ τ _ _ _ x k f L c hf hfin hpow
  obtain ⟨d, F, hF, hFan, hhF, hFev, hord⟩ := hG σ τ x k f L c hf hfin hpow
  obtain ⟨n, e, he, hgen⟩ := hfin

  set t : (σ → ℂ) → ℂ := fun z => L z c - L x c with ht_def
  have ht : AnalyticAt ℂ t x :=
    (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : τ => ℂ) c).comp L).analyticAt x).sub analyticAt_const
  let ix : Fin (n * d) → Fin n × Fin d := fun p => finProdFinEquiv.symm p
  refine ⟨n * d, fun p z => t z ^ ((ix p).2 : ℕ) * e (ix p).1 z, fun p => (ht.pow _).mul (he _), ?_⟩
  intro g hg
  obtain ⟨b, h, hb, hh, hev⟩ := hgen g hg
  choose q a hq ha hdiv using fun m => hW τ (L x) c d F (b m) hFan (hb m) hord
  have hLt : Tendsto L (𝓝 x) (𝓝 (L x)) := L.continuous.tendsto x
  refine ⟨fun p y => a (ix p).1 (ix p).2 y, fun i z => h i z + ∑ m, q m (L z) * e m z * hF i z,
    fun p => by simpa using ha (ix p).1 (ix p).2, fun i => ?_, ?_⟩
  · refine (hh i).add (Finset.univ.analyticAt_fun_sum fun m _ => ?_)
    have hqL : AnalyticAt ℂ (fun z => q m (L z)) x := (hq m).comp (L.analyticAt x)
    exact (hqL.mul (he m)).mul (hhF i)
  · have hdivL : ∀ᶠ z in 𝓝 x, ∀ m, b m (L z) = q m (L z) * F (L z) +
        ∑ j : Fin d, a m j (zeroCoordinate c (L z)) * (L z c - L x c) ^ (j : ℕ) :=
      eventually_all.2 fun m => hLt.eventually (hdiv m)
    filter_upwards [hev, hdivL, hFev] with z hz hzd hzF
    rw [hz]
    simp only [hzd, hzF, ContinuousLinearMap.comp_apply]
    have hre : ∀ φ : Fin n × Fin d → ℂ, ∑ p : Fin (n * d), φ (ix p) = ∑ m, ∑ j, φ (m, j) := fun φ => by
      rw [← Fintype.sum_prod_type']
      exact finProdFinEquiv.symm.sum_comp φ
    rw [hre (fun mj => a mj.1 mj.2 (zeroCoordinate c (L z)) * (t z ^ (mj.2 : ℕ) * e mj.1 z))]
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, ht_def]
    have h1 : ∑ m, (q m (L z) * ∑ i, hF i z * f i z) * e m z =
        ∑ i, ∑ m, q m (L z) * e m z * hF i z * f i z := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring
    have h2 : ∀ m (j : Fin d), a m j (zeroCoordinate c (L z)) * (L z c - L x c) ^ (j : ℕ) * e m z =
        a m j (zeroCoordinate c (L z)) * ((L z c - L x c) ^ (j : ℕ) * e m z) := fun m j => by ring
    simp only [h2]
    rw [h1]
    ring
end FiniteModuloEliminate
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
