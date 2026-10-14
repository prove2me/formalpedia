-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_window_of_contains_and_count
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T10:30:11.468194+00:00
-- url     : https://prove2.me/submissions/25d8b4a3-3c5b-40b0-845d-5b2a2e1f5200

import Definitions.Def_TaoFivePrimes_RHHighHeightBracketInterface
import Theorems.Thm_TaoFivePrimes_rh_high_height_bracket_tree_sound
import Theorems.Thm_TaoFivePrimes_rh_high_height_sign_count_bridge
import Theorems.Thm_TaoFivePrimes_rh_high_height_window_finite
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 0
attribute [local irreducible] RHHighHeightBracketInterface.leaves
namespace RHHighHeightClosureProof
open RHHighHeightBracketData RHHighHeightBracketInterface
lemma closure {l r n : Nat} (t : Tree l r n)
    (hcontains : ∀ p ∈ leaves t,
      (p.llo:ℝ)/scale ≤ RHHighHeight.normalized (point p.l) ∧
      RHHighHeight.normalized (point p.l) ≤ (p.lhi:ℝ)/scale ∧
      (p.rlo:ℝ)/scale ≤ RHHighHeight.normalized (point p.r) ∧
      RHHighHeight.normalized (point p.r) ≤ (p.rhi:ℝ)/scale)
    (hcount : (RHHighHeight.windowZeros 3289999872 3290000000).ncard ≤ n) :
    ∀ s ∈ RHHighHeight.windowZeros 3289999872 3290000000, s.re=1/2 := by
  classical
  have ht := TaoFivePrimes.rh_high_height_bracket_tree_sound t
  let p : Fin n → Bracket := fun i => (leaves t).get (Fin.cast ht.1.symm i)
  have hmem (i : Fin n) : p i ∈ leaves t := List.get_mem _ _
  let L : Fin n → ℝ := fun i => point (p i).l
  let R : Fin n → ℝ := fun i => point (p i).r
  have hpoint {i j : Nat} (hij : i≤j) : point i≤point j := by
    have h : (i:ℝ)≤(j:ℝ) := by exact_mod_cast hij
    unfold point
    linarith
  have hb : ∀ i, (3289999872:ℝ)≤L i ∧ L i<R i ∧ R i≤3290000000 := by
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
  have hscale : 0<scale := by norm_num [scale]
  have hs : ∀ i, RHHighHeight.normalized (L i)*RHHighHeight.normalized (R i)<0 := by
    intro i
    have he := hcontains (p i) (hmem i)
    rcases (p i).signs with hsign | hsign
    · have hn : (p i).lhi<0 := hsign.1
      have hp : 0<(p i).rlo := hsign.2
      have hn' : ((p i).lhi:ℝ)<0 := by exact_mod_cast hn
      have hp' : 0<((p i).rlo:ℝ) := by exact_mod_cast hp
      have hl : RHHighHeight.normalized (L i)<0 :=
        he.2.1.trans_lt (div_neg_of_neg_of_pos hn' hscale)
      have hr : 0<RHHighHeight.normalized (R i) :=
        (div_pos hp' hscale).trans_le he.2.2.1
      exact mul_neg_of_neg_of_pos hl hr
    · have hn : (p i).rhi<0 := hsign.1
      have hp : 0<(p i).llo := hsign.2
      have hn' : ((p i).rhi:ℝ)<0 := by exact_mod_cast hn
      have hp' : 0<((p i).llo:ℝ) := by exact_mod_cast hp
      have hr : RHHighHeight.normalized (R i)<0 :=
        he.2.2.2.trans_lt (div_neg_of_neg_of_pos hn' hscale)
      have hl : 0<RHHighHeight.normalized (L i) :=
        (div_pos hp' hscale).trans_le he.1
      exact mul_neg_of_pos_of_neg hl hr
  exact TaoFivePrimes.rh_high_height_sign_count_bridge L R hb hd hs
    (TaoFivePrimes.rh_high_height_window_finite _ _) hcount
end RHHighHeightClosureProof

theorem solution
    (hcontains : RHHighHeightBracketInterface.proposalContains)
    (hcount : (RHHighHeight.windowZeros 3289999872 3290000000).ncard ≤ 409) :
    ∀ s ∈ RHHighHeight.windowZeros 3289999872 3290000000, s.re=1/2 :=
  RHHighHeightClosureProof.closure RHHighHeightBracketData.certificate hcontains hcount
