-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SeparateWeierstrassDivision_proof_1e785939e369
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:58:50.694907+00:00
-- url     : https://prove2.me/submissions/a8c5483d-058d-42fb-81c2-61507a252050

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSeparateWeierstrassDivision
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeierstrassPolynomialDivision
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CoeffEqZeroOfForallEvalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSeparateWeierstrassDivision
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticAt_coord_b04ec3e87b93
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrassDivision_in_coordinate_41c122d1492a


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
namespace SeparateWeierstrassDivision
theorem _root_.solution (h : WeierstrassPolynomialDivision.Statement) :
    SeparateWeierstrassDivision.Statement := by
  suffices H : ∀ (N : ℕ) (σ : Type) [Fintype σ] [DecidableEq σ], Fintype.card σ = N →
      ∀ (d : ℕ) (y₀ : Fin d → ℂ) (u₀ : σ → ℂ) (n : σ → ℕ)
        (b : (m : σ) → Fin (n m) → (Fin d → ℂ) → ℂ) (f : (Fin d → ℂ) × (σ → ℂ) → ℂ),
        (∀ m j, AnalyticAt ℂ (b m j) y₀) →
        (∀ m (T : ℂ), T ^ n m + ∑ j, b m j y₀ * T ^ (j : ℕ) = (T - u₀ m) ^ n m) →
        AnalyticAt ℂ f (y₀, u₀) →
        ∃ (v : σ → (Fin d → ℂ) × (σ → ℂ) → ℂ) (r : ((m : σ) → Fin (n m)) → (Fin d → ℂ) → ℂ),
          (∀ m, AnalyticAt ℂ (v m) (y₀, u₀)) ∧ (∀ α, AnalyticAt ℂ (r α) y₀) ∧
          ∀ᶠ x in 𝓝 (y₀, u₀),
            f x = ∑ m, v m x * (x.2 m ^ n m + ∑ j, b m j x.1 * x.2 m ^ (j : ℕ)) +
              ∑ α, r α x.1 * ∏ m, x.2 m ^ (α m : ℕ) by
    intro σ _ _ d y₀ u₀ n b f hb hG hf
    exact H _ σ rfl d y₀ u₀ n b f hb hG hf
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro σ _ _ hN d y₀ u₀ n b f hb hG hf
  rcases isEmpty_or_nonempty σ with hσ | ⟨⟨k⟩⟩
  ·
    refine ⟨fun _ _ => 0, fun _ y => f (y, u₀), fun _ => analyticAt_const,
      fun _ => hf.comp_of_eq (analyticAt_id.prod analyticAt_const) rfl, Eventually.of_forall fun x => ?_⟩
    have hx : x = (x.1, u₀) := Prod.ext rfl (Subsingleton.elim _ _)
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Finset.prod_empty, mul_one, zero_add,
      Fintype.sum_unique]
    rw [← hx]
  · obtain ⟨q, e, hq, he, hev⟩ :=
      weierstrassDivision_in_coordinate h k d y₀ u₀ (n k) (b k) f (hb k) (hG k) hf
    have hlt : Fintype.card {m // m ≠ k} < N :=
      hN ▸ Fintype.card_subtype_lt (p := fun m => m ≠ k) (x := k) (by simp)
    have IH := fun i => ih _ hlt {m // m ≠ k} rfl d y₀ (fun m => u₀ m) (fun m => n m)
      (fun m => b m) (e i) (fun m j => hb m j) (fun m T => hG m T) (he i)
    choose V R hV hR hVR using IH
    have hπ : AnalyticAt ℂ (fun x : (Fin d → ℂ) × (σ → ℂ) => (x.1, fun m : {m // m ≠ k} => x.2 m)) (y₀, u₀) :=
      analyticAt_fst.prod (AnalyticAt.pi (f := fun (m : {m // m ≠ k}) (x : (Fin d → ℂ) × (σ → ℂ)) => x.2 m)
        fun m => (analyticAt_coord _ _).comp analyticAt_snd)
    refine ⟨fun m x => if hm : m = k then q x else
        ∑ i, V i ⟨m, hm⟩ (x.1, fun m' => x.2 m') * x.2 k ^ (i : ℕ),
      fun α y => R (α k) (fun m' => α m') y, fun m => ?_, fun α => hR _ _, ?_⟩
    · by_cases hm : m = k
      · simpa [hm] using hq
      · simp only [hm, dite_false]
        exact Finset.analyticAt_fun_sum _ fun i _ =>
          ((hV i ⟨m, hm⟩).comp_of_eq hπ rfl).fun_mul
            (((analyticAt_coord k _).comp analyticAt_snd).fun_pow _)
    · have hT : Tendsto (fun x : (Fin d → ℂ) × (σ → ℂ) => (x.1, fun m' : {m // m ≠ k} => x.2 m'))
          (𝓝 (y₀, u₀)) (𝓝 (y₀, fun m' => u₀ m')) := hπ.continuousAt.tendsto
      filter_upwards [hev, hT.eventually (Filter.eventually_all.2 hVR)] with x hx hx'
      rw [hx, Fintype.sum_eq_add_sum_subtype_ne _ k,
        ← (Equiv.piSplitAt k (fun m => Fin (n m))).symm.sum_comp, Fintype.sum_prod_type]
      have hne : ∀ m : {m // m ≠ k}, ¬ ((m : σ) = k) := fun m => m.2
      simp_rw [Fintype.prod_eq_mul_prod_subtype_ne _ k]
      simp only [Equiv.piSplitAt_symm_apply, dite_true, hne, dite_false, Subtype.coe_eta, hx']
      simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
      rw [add_assoc]
      congr 1
      congr 1
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => by ring
      · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun α _ => by ring
end SeparateWeierstrassDivision
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
