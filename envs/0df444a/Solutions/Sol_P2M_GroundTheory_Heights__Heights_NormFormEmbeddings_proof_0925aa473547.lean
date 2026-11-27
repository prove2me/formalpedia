-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormFormEmbeddings_proof_0925aa473547
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:04:29.996364+00:00
-- url     : https://prove2.me/submissions/9d0d5da5-e488-4c18-9200-d7723da98238

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PNormFormEmbeddings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace NormFormEmbeddings
theorem _root_.solution (h : NormFormEval.Statement) : NormFormEmbeddings.Statement := by
  intro K L Ω _ _ _ _ _ _ _ _ _ n η
  have hs : ∀ _ : Fin n, (Set.range (algebraMap K Ω)).Infinite :=
    fun _ => Set.infinite_range_of_injective (algebraMap K Ω).injective
  refine MvPolynomial.funext_set (fun _ => Set.range (algebraMap K Ω)) hs ?_
  intro x hx
  choose u hu using fun m => hx m (Set.mem_univ m)
  obtain rfl : x = algebraMap K Ω ∘ u := funext fun m => (hu m).symm
  have hl : eval (algebraMap K Ω ∘ u) (map (algebraMap K Ω) (normForm K L η)) =
      algebraMap K Ω (eval u (normForm K L η)) := by
    rw [eval_map]
    change _ = algebraMap K Ω (eval₂ (RingHom.id K) u (normForm K L η))
    rw [eval₂_comp_left]
    rfl
  rw [hl, h K L n η u, Algebra.norm_eq_prod_embeddings]
  simp only [map_prod, map_sum, map_mul, eval_X, eval_C, Function.comp_apply]
  refine Finset.prod_congr rfl fun σ _ => Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, Algebra.smul_def]
end NormFormEmbeddings
end GroundTheory.Heights₂.Heights
