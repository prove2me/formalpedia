-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_window_of_signs_and_count
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T17:07:41.907463+00:00
-- url     : https://prove2.me/submissions/0a37e908-3842-41aa-9333-886d82466c1c

import Definitions.Def_TaoFivePrimes_RHBatch01HeightBracketInterface
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_bracket_tree_sound
import Theorems.Thm_TaoFivePrimes_rh_high_height_sign_count_bridge
import Theorems.Thm_TaoFivePrimes_rh_high_height_window_finite
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 0
attribute [local irreducible] RHBatch01HeightBracketInterface.leaves
namespace RHBatch01HeightSignClosureProof
open RHBatch01HeightBracketData RHBatch01HeightBracketInterface
lemma closure {l r n : Nat} (t : Tree l r n)
    (hsigns : ∀ p ∈ leaves t,
      RHHighHeight.normalized (point p.l)*RHHighHeight.normalized (point p.r)<0)
    (hcount : (RHHighHeight.windowZeros 3289999744 3289999872).ncard ≤ n) :
    ∀ s ∈ RHHighHeight.windowZeros 3289999744 3289999872, s.re=1/2 := by
  classical
  have ht := TaoFivePrimes.rh_batch01_height_bracket_tree_sound t
  let p : Fin n → Bracket := fun i => (leaves t).get (Fin.cast ht.1.symm i)
  have hmem (i : Fin n) : p i ∈ leaves t := List.get_mem _ _
  let L : Fin n → ℝ := fun i => point (p i).l
  let R : Fin n → ℝ := fun i => point (p i).r
  have hpoint {i j : Nat} (hij : i≤j) : point i≤point j := by
    have h : (i:ℝ)≤(j:ℝ) := by exact_mod_cast hij
    unfold point
    linarith
  have hb : ∀ i, (3289999744:ℝ)≤L i ∧ L i<R i ∧ R i≤3289999872 := by
    intro i
    have hli : 0≤((p i).l:ℝ) := Nat.cast_nonneg _
    have hlt : ((p i).l:ℝ)<((p i).r:ℝ) := by exact_mod_cast (p i).bound.1
    have hr : ((p i).r:ℝ)≤4096 := by exact_mod_cast (p i).bound.2
    dsimp [L,R,point]
    constructor
    · linarith
    constructor <;> linarith
  have hd : ∀ i j, i≠j → Disjoint (Set.Ioo (L i) (R i)) (Set.Ioo (L j) (R j)) := by
    intro i j hij
    have hs := List.pairwise_iff_get.mp ht.2.1
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have ho : (p i).r≤(p j).l := hs (Fin.cast ht.1.symm i) (Fin.cast ht.1.symm j) hlt
      have hv : R i≤L j := hpoint ho
      exact Set.disjoint_left.mpr (fun x hi hj => by linarith [hi.2,hj.1])
    · have ho : (p j).r≤(p i).l := hs (Fin.cast ht.1.symm j) (Fin.cast ht.1.symm i) hlt
      have hv : R j≤L i := hpoint ho
      exact Set.disjoint_left.mpr (fun x hi hj => by linarith [hi.1,hj.2])
  have hs : ∀ i, RHHighHeight.normalized (L i)*RHHighHeight.normalized (R i)<0 :=
    fun i => hsigns (p i) (hmem i)
  exact TaoFivePrimes.rh_high_height_sign_count_bridge L R hb hd hs
    (TaoFivePrimes.rh_high_height_window_finite _ _) hcount
end RHBatch01HeightSignClosureProof

theorem solution
    (hsigns : ∀ p ∈ RHBatch01HeightBracketInterface.leaves RHBatch01HeightBracketData.certificate,
      RHHighHeight.normalized (RHBatch01HeightBracketInterface.point p.l)*
      RHHighHeight.normalized (RHBatch01HeightBracketInterface.point p.r)<0)
    (hcount : (RHHighHeight.windowZeros 3289999744 3289999872).ncard ≤ 409) :
    ∀ s ∈ RHHighHeight.windowZeros 3289999744 3289999872, s.re=1/2 :=
  RHBatch01HeightSignClosureProof.closure RHBatch01HeightBracketData.certificate hsigns hcount
#print axioms solution
