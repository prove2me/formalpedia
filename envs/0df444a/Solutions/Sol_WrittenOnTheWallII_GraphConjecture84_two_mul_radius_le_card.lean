-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.two_mul_radius_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:32:13.769324+00:00
-- url     : https://prove2.me/submissions/3005f02e-de57-4f4f-b10f-b6023037810c

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_dist_add_dist_eq_of_mem_geodesic

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} (hG : G.Connected) :
    2 * G.radius.toNat ≤ Fintype.card α := by
  classical
  haveI : Nonempty α := hG.nonempty
  by_cases hr : G.radius.toNat = 0
  · simp [hr]
  have hfin : G.radius ≠ ⊤ := G.radius_ne_top_iff.mpr hG
  obtain ⟨c, hc⟩ := G.exists_eccent_eq_radius
  have hcenter (z : α) : G.dist c z ≤ G.radius.toNat := by
    exact ENat.toNat_le_toNat (hc ▸ (G.edist_le_eccent (u := c) (v := z))) hfin
  obtain ⟨a, ha⟩ := G.exists_edist_eq_eccent_of_finite c
  have hca : G.dist c a = G.radius.toNat := congrArg ENat.toNat (ha.trans hc)
  obtain ⟨p, hp, hplen⟩ := hG.exists_path_of_dist c a
  cases p with
  | nil => simp only [Walk.length_nil, dist_self] at hplen hca; omega
  | @cons c n a hcn p =>
    have hplen' : p.length = G.dist n a :=
      length_eq_dist_of_subwalk hplen (Walk.isSubwalk_cons p hcn)
    have hpr : p.length + 1 = G.radius.toNat := by
      simpa only [Walk.length_cons, hca] using hplen
    obtain ⟨b, hb⟩ := G.exists_edist_eq_eccent_of_finite n
    have hnb : G.radius.toNat ≤ G.dist n b := by
      apply ENat.toNat_le_toNat (hb ▸ G.radius_le_eccent)
      exact edist_ne_top_iff_reachable.mpr (hG n b)
    obtain ⟨q, hq, hqlen⟩ := hG.exists_path_of_dist c b
    have hdis : Disjoint p.support.toFinset q.support.toFinset := by
      apply Finset.disjoint_left.mpr
      intro z hzp hzq
      have hzp' : z ∈ p.support := by simpa using hzp
      have hzq' : z ∈ q.support := by simpa using hzq
      have hpa := dist_add_dist_eq_of_mem_geodesic p hplen' hzp'
      have hqb := dist_add_dist_eq_of_mem_geodesic q hqlen hzq'
      have htri := hG.dist_triangle (u := c) (v := z) (w := a)
      have hntri := hG.dist_triangle (u := n) (v := z) (w := b)
      have hcb := hcenter b
      omega
    have hp' : p.IsPath := (Walk.cons_isPath_iff hcn p).mp hp |>.1
    have hpcard : p.support.toFinset.card = p.length + 1 := by
      rw [List.toFinset_card_of_nodup hp'.support_nodup, p.length_support]
    have hqcard : q.support.toFinset.card = q.length + 1 := by
      rw [List.toFinset_card_of_nodup hq.support_nodup, q.length_support]
    have htri := hG.dist_triangle (u := n) (v := c) (w := b)
    have hnc : G.dist n c = 1 := dist_eq_one_iff_adj.mpr hcn.symm
    have hcard := Finset.card_le_univ (p.support.toFinset ∪ q.support.toFinset)
    rw [Finset.card_union_of_disjoint hdis, hpcard, hqcard] at hcard
    omega
end WrittenOnTheWallII.GraphConjecture84
