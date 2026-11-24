-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.chung_bound_of_unique_farthest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:34:12.894825+00:00
-- url     : https://prove2.me/submissions/fd17b550-0c6f-4b94-b760-535e776f0094

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_dist_add_dist_eq_of_mem_geodesic
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_induce_union_geodesic_isTree
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_dist_on_geodesic_tail
public import Theorems.Thm_SimpleGraph_IsTree_induce_insert_of_unique_adj
public import Theorems.Thm_SimpleGraph_Walk_induce_support_isTree_of_length_eq_dist
public import Theorems.Thm_SimpleGraph_card_le_largestInducedTreeSize


set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
set_option maxHeartbeats 800000
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} (hG : G.Connected)
    {c x : α} (hr : 3 ≤ G.radius.toNat) (hcx : G.dist c x = G.radius.toNat)
    (hother : ∀ z : α, z ≠ x → G.dist c z ≤ G.radius.toNat - 1) :
    2 * G.radius.toNat ≤ largestInducedTreeSize G + 1 := by
  classical
  obtain ⟨q, hq, hqlen⟩ := hG.exists_path_of_dist c x
  cases q with
  | nil => simp only [dist_self] at hcx; omega
  | @cons c a x hca q =>
    cases q with
    | nil => simp only [Walk.length_cons, Walk.length_nil] at hqlen; omega
    | @cons a b x hab q =>
      have hqalen : (q.cons hab).length = G.dist a x :=
        length_eq_dist_of_subwalk hqlen (Walk.isSubwalk_cons (q.cons hab) hca)
      have hqblen : q.length = G.dist b x :=
        length_eq_dist_of_subwalk hqalen (Walk.isSubwalk_cons q hab)
      have hqrad : q.length + 2 = G.radius.toNat := by
        simpa only [Walk.length_cons, hcx] using hqlen
      obtain ⟨w, hw⟩ := G.exists_edist_eq_eccent_of_finite b
      have hbw : G.radius.toNat ≤ G.dist b w :=
        ENat.toNat_le_toNat (hw ▸ G.radius_le_eccent)
          (edist_ne_top_iff_reachable.mpr (hG b w))
      have hwx : w ≠ x := by intro h; subst w; omega
      obtain ⟨p, hp, hplen⟩ := hG.exists_path_of_dist c w
      have hplower : G.radius.toNat - 2 ≤ p.length := by
        have htri := hG.dist_triangle (u := b) (v := c) (w := w)
        have hbc : G.dist b c ≤ 2 := by
          have hwalk := G.dist_le ((Walk.nil.cons hab).cons hca).reverse
          simpa using hwalk
        omega
      have hpupper : p.length ≤ G.radius.toNat - 1 := by
        rw [hplen]
        exact hother w hwx
      have hdistc (z : α) (hz : z ∈ p.support) : G.dist c z + 1 ≤ G.dist b z := by
        have hsum := dist_add_dist_eq_of_mem_geodesic p hplen hz
        have htri := hG.dist_triangle (u := b) (v := z) (w := w)
        omega
      have hqdist (z : α) (hz : z ∈ q.support) : G.dist c z = G.dist b z + 2 := by
        have hza := dist_on_geodesic_tail hG hca (q.cons hab) hqlen (z := z) (by simp [hz])
        have hzb := dist_on_geodesic_tail hG hab q hqalen hz
        omega
      have hinter : ∀ z ∈ p.support, z ∈ ((q.cons hab).cons hca).support → z = c := by
        intro z hzp hzq
        simp only [Walk.support_cons, List.mem_cons] at hzq
        rcases hzq with hzc | hza | hzq
        · exact hzc
        · subst z
          have hd := hdistc a hzp
          have hda : G.dist c a = 1 := dist_eq_one_iff_adj.mpr hca
          have hdb : G.dist b a = 1 := dist_eq_one_iff_adj.mpr hab.symm
          omega
        · have hd := hdistc z hzp
          have heq := hqdist z hzq
          omega
      cases p with
      | nil => simp only [Walk.length_nil] at hplower; omega
      | @cons c d w hcd p =>
        have hptail : p.length = G.dist d w :=
          length_eq_dist_of_subwalk hplen (Walk.isSubwalk_cons p hcd)
        have hcnotp : c ∉ p.support := (List.nodup_cons.mp hp.support_nodup).1
        have hcnotq : c ∉ (q.cons hab).support := (List.nodup_cons.mp hq.support_nodup).1
        have hpPath : p.IsPath := p.isPath_of_length_eq_dist hptail
        have hqPath : (q.cons hab).IsPath := (q.cons hab).isPath_of_length_eq_dist hqalen
        have hpmem {z : α} (hz : z ∈ p.support) : z ∈ (p.cons hcd).support := by
          simp only [Walk.support_cons, List.mem_cons]
          exact Or.inr hz
        have hqmem {z : α} (hz : z ∈ (q.cons hab).support) :
            z ∈ ((q.cons hab).cons hca).support := by
          simp only [Walk.support_cons, List.mem_cons]
          exact Or.inr (by simpa only [Walk.support_cons, List.mem_cons] using hz)
        have hcross : ∀ z ∈ (p.cons hcd).support, z ≠ c →
            ∀ y ∈ ((q.cons hab).cons hca).support, G.Adj z y →
              y = c ∨ (z = d ∧ y = a) := by
          intro z hzp hzc y hy hzy
          simp only [Walk.support_cons, List.mem_cons] at hy
          rcases hy with hyc | hya | hy
          · exact Or.inl hyc
          · subst y
            right
            have hd := hdistc z hzp
            have htri := hG.dist_triangle (u := b) (v := a) (w := z)
            have hba : G.dist b a = 1 := dist_eq_one_iff_adj.mpr hab.symm
            have haz : G.dist a z = 1 := dist_eq_one_iff_adj.mpr hzy.symm
            have hzp' : z ∈ p.support := by
              simpa only [Walk.support_cons, List.mem_cons, or_iff_right hzc] using hzp
            have heq := dist_on_geodesic_tail hG hcd p hplen hzp'
            have hdz : G.dist d z = 0 := by omega
            exact ⟨(hG.dist_eq_zero_iff.mp hdz).symm, rfl⟩
          · have hd := hdistc z hzp
            have heq := hqdist y hy
            have htri := hG.dist_triangle (u := b) (v := y) (w := z)
            have htri' := hG.dist_triangle (u := c) (v := z) (w := y)
            have hzydist : G.dist z y = 1 := dist_eq_one_iff_adj.mpr hzy
            have hyzdist : G.dist y z = 1 := dist_eq_one_iff_adj.mpr hzy.symm
            omega
        by_cases hda : G.Adj d a
        · have hpmax : (p.cons hcd).length = G.radius.toNat - 1 := by
            have htri := hG.dist_triangle (u := b) (v := d) (w := w)
            have hbd : G.dist b d ≤ 2 := by
              have hwalk := G.dist_le ((Walk.nil.cons hda.symm).cons hab.symm)
              simpa using hwalk
            simp only [Walk.length_cons] at hpupper ⊢
            omega
          let s := (q.cons hab).support.toFinset
          have hT : (G.induce (s : Set α)).IsTree :=
            (q.cons hab).induce_support_isTree_of_length_eq_dist hqalen
          have hdnot : d ∉ s := by
            intro hd
            have hdc := hinter d (by simp) (hqmem (by simpa only [s, List.mem_toFinset] using hd))
            exact hcd.ne hdc.symm
          have hTa := hT.induce_insert_of_unique_adj hdnot (by simp [s]) hda (by
            intro y hy hdy
            rcases hcross d (by simp) hcd.ne.symm y
                (hqmem (by simpa only [s, List.mem_toFinset] using hy)) hdy with hyc | ⟨_, hya⟩
            · exact (hcnotq (by simpa [hyc, s] using hy)).elim
            · exact hya)
          have hprev : p.reverse.length = G.dist w d := by
            simpa only [Walk.length_reverse, SimpleGraph.dist_comm] using hptail
          have hTfull := induce_union_geodesic_isTree hG p.reverse hprev (insert d s) hTa
            (by simp) (by
              intro z hz hzs
              rcases Finset.mem_insert.mp hzs with rfl | hzs
              · rfl
              · have hzp : z ∈ p.support := by
                  simpa only [Walk.support_reverse, List.mem_reverse] using hz
                have hzc := hinter z (hpmem hzp)
                  (hqmem (by simpa only [s, List.mem_toFinset] using hzs))
                exact (hcnotp (hzc ▸ hzp)).elim) (by
              intro z hz hzd y hy hzy
              rcases Finset.mem_insert.mp hy with rfl | hy
              · rfl
              · have hzp : z ∈ p.support := by
                  simpa only [Walk.support_reverse, List.mem_reverse] using hz
                rcases hcross z (hpmem hzp)
                  (by intro hzc; exact hcnotp (hzc ▸ hzp)) y
                  (hqmem (by simpa only [s, List.mem_toFinset] using hy)) hzy with hyc | ⟨hzd', _⟩
                · exact (hcnotq (by simpa [hyc, s] using hy)).elim
                · exact (hzd hzd').elim)
          have hset : p.reverse.support.toFinset ∪ insert d s = p.support.toFinset ∪ s := by
            ext z
            simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset,
              Walk.support_reverse, List.mem_reverse]
            have hd : d ∈ p.support := by simp
            aesop
          rw [hset] at hTfull
          have hdis : Disjoint p.support.toFinset s := by
            apply Finset.disjoint_left.mpr
            intro z hz hzs
            have hzc := hinter z (hpmem (by simpa only [List.mem_toFinset] using hz))
              (hqmem (by simpa only [s, List.mem_toFinset] using hzs))
            exact hcnotp (by simpa [hzc] using hz)
          have hpcard : p.support.toFinset.card = p.length + 1 := by
            rw [List.toFinset_card_of_nodup hpPath.support_nodup, p.length_support]
          have hqcard : s.card = q.length + 2 := by
            change (q.cons hab).support.toFinset.card = q.length + 2
            rw [List.toFinset_card_of_nodup hqPath.support_nodup, Walk.length_support,
              Walk.length_cons]
          have hbound := card_le_largestInducedTreeSize hTfull
          rw [Finset.card_union_of_disjoint hdis, hpcard, hqcard] at hbound
          simp only [Walk.length_cons] at hpmax
          omega
        · have hprev : (p.cons hcd).reverse.length = G.dist w c := by
            simpa only [Walk.length_reverse, SimpleGraph.dist_comm] using hplen
          let s := ((q.cons hab).cons hca).support.toFinset
          have hT : (G.induce (s : Set α)).IsTree :=
            ((q.cons hab).cons hca).induce_support_isTree_of_length_eq_dist hqlen
          have hTfull := induce_union_geodesic_isTree hG (p.cons hcd).reverse hprev s hT
            (by simp [s]) (by
              intro z hz hzs
              exact hinter z (by simpa only [Walk.support_reverse, List.mem_reverse] using hz)
                (by simpa only [s, List.mem_toFinset] using hzs)) (by
              intro z hz hzc y hy hzy
              rcases hcross z (by simpa only [Walk.support_reverse, List.mem_reverse] using hz)
                  hzc y (by simpa only [s, List.mem_toFinset] using hy) hzy with
                hyc | ⟨hzd, hya⟩
              · exact hyc
              · exact (hda (by simpa [hzd, hya] using hzy)).elim)
          have hset : (p.cons hcd).reverse.support.toFinset ∪ s = p.support.toFinset ∪ s := by
            ext z
            simp only [Finset.mem_union, List.mem_toFinset, Walk.support_reverse,
              List.mem_reverse, Walk.support_cons, List.mem_cons]
            have hc : c ∈ s := by simp [s]
            aesop
          rw [hset] at hTfull
          have hdis : Disjoint p.support.toFinset s := by
            apply Finset.disjoint_left.mpr
            intro z hz hzs
            have hzc := hinter z (hpmem (by simpa only [List.mem_toFinset] using hz))
              (by simpa only [s, List.mem_toFinset] using hzs)
            exact hcnotp (by simpa [hzc] using hz)
          have hpcard : p.support.toFinset.card = p.length + 1 := by
            rw [List.toFinset_card_of_nodup hpPath.support_nodup, p.length_support]
          have hqcard : s.card = q.length + 3 := by
            change ((q.cons hab).cons hca).support.toFinset.card = q.length + 3
            rw [List.toFinset_card_of_nodup hq.support_nodup, Walk.length_support]
            simp only [Walk.length_cons]
          have hbound := card_le_largestInducedTreeSize hTfull
          rw [Finset.card_union_of_disjoint hdis, hpcard, hqcard] at hbound
          simp only [Walk.length_cons] at hplower
          omega
end WrittenOnTheWallII.GraphConjecture84
