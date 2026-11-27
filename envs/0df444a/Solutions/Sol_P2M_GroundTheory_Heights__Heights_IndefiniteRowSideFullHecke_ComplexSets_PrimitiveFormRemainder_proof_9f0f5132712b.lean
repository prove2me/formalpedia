-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormRemainder_proof_9f0f5132712b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:59:13.033297+00:00
-- url     : https://prove2.me/submissions/fe3d073e-eeb5-438e-85ee-49ca23b2b658

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormRemainder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSeparateWeierstrassDivision
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveFormRemainder

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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace PrimitiveFormRemainder
theorem _root_.solution (hSWD : SeparateWeierstrassDivision.Statement) :
    PrimitiveFormRemainder.Statement := by
  classical
  intro σ _ w d A ℓ N δ q n c f hδ hq hc hW hf
  obtain ⟨v, r, -, hr, hev⟩ := hSWD σ d (A w) w n c (fun x => f x.2) hc hW
    (hf.comp (analyticAt_snd (p := (A w, w))))
  set S := PrimitiveFormRemainder.analyticSubring d (A w)

  let s : ((i : σ) → Fin (n i)) → ℕ := fun α => ∑ i, (α i : ℕ)
  let M : ℕ := ∑ i, n i
  have hsM : ∀ α, s α ≤ M := fun α => Finset.sum_le_sum fun i _ => (α i).isLt.le
  let Q : σ → Polynomial ((Fin d → ℂ) → ℂ) := fun i => ∑ j, C (q i j) * X ^ (j : ℕ)
  let R : Polynomial ((Fin d → ℂ) → ℂ) :=
    ∑ α, C (r α * δ ^ (M - s α)) * ∏ i, Q i ^ (α i : ℕ)
  refine ⟨M, R, ?_, ?_⟩
  ·
    have hC : ∀ g : (Fin d → ℂ) → ℂ, AnalyticAt ℂ g (A w) → C g ∈ lifts S.subtype := fun g hg =>
      C_mem_lifts S.subtype ⟨g, hg⟩
    have hR : R ∈ lifts S.subtype := by
      refine Subsemiring.sum_mem _ fun α _ => Subsemiring.mul_mem _ (hC _ ((hr α).mul (hδ.pow _)))
        (Subsemiring.prod_mem _ fun i _ => Subsemiring.pow_mem _ ?_ _)
      exact Subsemiring.sum_mem _ fun j _ =>
        Subsemiring.mul_mem _ (hC _ (hq i j)) (X_pow_mem_lifts _ _)
    intro k
    obtain ⟨g, hg⟩ := (lifts_iff_coeff_lifts R).1 hR k
    rw [← hg]
    exact g.2
  ·
    have hcont : Continuous fun z : σ → ℂ => (A z, z) := A.continuous.prodMk continuous_id
    filter_upwards [(hcont.tendsto w).eventually hev] with z hz hWz hqz
    have hf' : f z = ∑ α, r α (A z) * ∏ i, z i ^ (α i : ℕ) := by
      rw [hz]; simp [hWz]
    have hQ : ∀ i, (Q i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) (A z)) (ℓ z) = δ (A z) * z i := by
      intro i
      simp [Q, eval₂_finsetSum, hqz i]
    simp only [R, eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_finsetProd, eval₂_pow, hQ, hf', Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    simp only [Pi.evalRingHom_apply, Pi.mul_apply, Pi.pow_apply, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
    rw [← pow_mul_pow_sub (δ (A z)) (hsM α)]
    ring
end PrimitiveFormRemainder
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
