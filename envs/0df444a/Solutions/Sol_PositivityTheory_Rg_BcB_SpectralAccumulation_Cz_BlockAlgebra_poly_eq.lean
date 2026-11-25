-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra.poly_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:30:08.302976+00:00
-- url     : https://prove2.me/submissions/f2bbbe09-7c56-4a81-aabb-277d78af1c3e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PBlocksAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.Cz PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra
variable {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra
theorem _root_.solution (n : ℕ) (a : ℕ → Module.End ℂ M) (ha : a n = 1) (σ : Multiset ℂ) (hσ : σ.Nodup)
    (hc : Multiset.card σ = n) (h : ∀ x ∈ σ, (∑ k ∈ Finset.range (n + 1), (-x) ^ k • a k) = 0) (u : ℂ) :
    (∑ k ∈ Finset.range (n + 1), u ^ k • a k) = (σ.map (u + ·)).prod • (1 : Module.End ℂ M) := by
  classical
  set P : ℂ[X] := (σ.map fun x => X + C x).prod with hP
  have hPm : P.Monic := monic_multiset_prod_of_monic _ _ fun x _ => monic_X_add_C x
  have hPd : P.natDegree = n := by
    rw [hP, natDegree_multiset_prod_of_monic _ fun x hx => by
      obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hx; exact monic_X_add_C y]
    simp [hc]
  have hPe : ∀ w : ℂ, P.eval w = (σ.map (w + ·)).prod := fun w => by
    simp [hP, eval_multiset_prod, Multiset.map_map]
  have hPsum : ∀ w : ℂ, P.eval w = ∑ k ∈ Finset.range (n + 1), P.coeff k * w ^ k := fun w => by
    rw [eval_eq_sum_range, hPd]
  have hPn : P.coeff n = 1 := by rw [← hPd]; exact hPm.coeff_natDegree
  refine LinearMap.ext fun y => ?_
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun f => ?_
  set g : ℂ[X] := ∑ i : Fin n, C (f (a i y) - f y * P.coeff i) * X ^ (i : ℕ) with hg
  have hge : ∀ w : ℂ, g.eval w = f ((∑ k ∈ Finset.range (n + 1), w ^ k • a k) y) - f y * P.eval w := by
    intro w
    rw [hPsum, hg, eval_finsetSum, Finset.sum_range_succ, Finset.sum_range_succ, hPn, ha,
      LinearMap.add_apply, map_add, LinearMap.sum_apply, map_sum, ← Fin.sum_univ_eq_sum_range (fun k => f ((w ^ k • a k) y)),
      ← Fin.sum_univ_eq_sum_range (fun k => P.coeff k * w ^ k)]
    simp only [eval_mul, eval_C, eval_pow, eval_X, LinearMap.smul_apply, map_smul, smul_eq_mul, Module.End.one_apply,
      mul_add, Finset.mul_sum]
    simp only [sub_mul, Finset.sum_sub_distrib, one_mul]
    have h1 : ∑ x : Fin n, f (a x y) * w ^ (x : ℕ) = ∑ x : Fin n, w ^ (x : ℕ) * f (a x y) :=
      Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have h2 : ∑ x : Fin n, f y * P.coeff x * w ^ (x : ℕ) = ∑ i : Fin n, f y * (P.coeff i * w ^ (i : ℕ)) :=
      Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _
    rw [h1, h2]
    ring
  have hg0 : g = 0 := by
    by_contra hne
    have hdeg : g.natDegree < n := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        exact absurd (by simp [hg]) hne
      · rw [natDegree_lt_iff_degree_lt hne]
        exact degree_sum_fin_lt _
    refine hne (eq_zero_of_natDegree_lt_card_of_eval_eq_zero' g (σ.map Neg.neg).toFinset (fun w hw => ?_) ?_)
    · obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_toFinset.1 hw)
      rw [hge, h x hx, LinearMap.zero_apply, map_zero, hPe]
      have : (σ.map (-x + ·)).prod = 0 := Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨x, hx, by ring⟩)
      rw [this, mul_zero, sub_zero]
    · rw [Multiset.toFinset_card_of_nodup (hσ.map neg_injective), Multiset.card_map, hc]
      exact hdeg
  have := hge u
  rw [hg0, eval_zero, hPe] at this
  rw [map_sub, LinearMap.smul_apply, Module.End.one_apply, map_smul, smul_eq_mul]
  linear_combination -this
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra
