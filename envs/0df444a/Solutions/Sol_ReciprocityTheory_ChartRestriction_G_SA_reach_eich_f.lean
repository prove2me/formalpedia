-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.reach_eich_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:27:15.81897+00:00
-- url     : https://prove2.me/submissions/addf4358-eb24-42b6-8dce-f0f3eb9cbcde

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ConjMemEichSet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ReachableFixingAddSmulSecond
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_good_of_closure
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) {e f : ι → K} (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1) {s : ℕ} {a : Fin s → ι → K}
  (hae : ∀ j, hf σ J (a j) e = 0) (haf : ∀ j, hf σ J (a j) f = 0)
include hσ hJ he hff hef
include hae haf
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution {u : ι → K} {c : K} (hue : hf σ J u e = 0) (huf : hf σ J u f = 0)
    (hc : c + σ c + hf σ J u u = 0) (hua : ∀ j, hf σ J u (a j) = 0) (b : ι → K) :
    Reach σ J e f a b (eich σ J f u c *ᵥ b) := by
  have hvmv : ∀ x y v : ι → K, vecMulVec x y *ᵥ v = (y ⬝ᵥ v) • x := by
    intro x y v
    ext i
    simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hdot : ∀ g v : ι → K, (J *ᵥ (σ ∘ g)) ⬝ᵥ v = hf σ J v g := by
    intro g v
    simp only [dotProduct, mulVec, hf, Function.comp, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hE : ∀ (g w v : ι → K) (d : K), eich σ J g w d *ᵥ v =
      v + hf σ J v g • w - hf σ J v w • g + (d * hf σ J v g) • g := by
    intro g w v d
    simp only [eich, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, hvmv, hdot, smul_smul]
  refine ⟨eich σ J f u c,
    (by apply good_of_closure <;> first
      | exact Submonoid.subset_closure (Or.inr ⟨u, c, huf, hue, hc, rfl⟩) | assumption),
    fun j => ?_, rfl⟩
  rw [hE, haf j, ← hf_symm hσ hJ u (a j), hua j, map_zero]
  simp
end ReciprocityTheory.ChartRestriction.G.SA
