-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.radius_drop_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:26:39.048584+00:00
-- url     : https://prove2.me/submissions/3a11326a-5c50-4df5-ac0c-f6a452b8536d

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} (hG : G.Connected) (x : α)
    (hH : (G.induce ({x}ᶜ : Set α)).Connected)
    (hr : 1 ≤ G.radius.toNat)
    (hdrop : (G.induce ({x}ᶜ : Set α)).radius.toNat ≤ G.radius.toNat - 1) :
    ∃ c : α, c ≠ x ∧ G.eccent c = G.radius ∧ G.dist c x = G.radius.toNat ∧
      ∀ z : α, z ≠ x → G.dist c z ≤ G.radius.toNat - 1 := by
  classical
  let H := G.induce ({x}ᶜ : Set α)
  haveI : Nonempty ↥({x}ᶜ : Set α) := hH.nonempty
  haveI : Nonempty α := ⟨x⟩
  obtain ⟨c, hc⟩ := H.exists_eccent_eq_radius
  have hHfin : H.radius ≠ ⊤ := H.radius_ne_top_iff.mpr hH
  have hGfin : G.radius ≠ ⊤ := G.radius_ne_top_iff.mpr hG
  have hother : ∀ z : α, z ≠ x → G.dist c z ≤ G.radius.toNat - 1 := by
    intro z hzx
    let z' : ↥({x}ᶜ : Set α) := ⟨z, by simpa using hzx⟩
    obtain ⟨p, hp⟩ := hH.exists_walk_length_eq_dist c z'
    have hmap : G.dist c z ≤ H.dist c z' := by
      have hm := G.dist_le (p.map (SimpleGraph.Embedding.induce ({x}ᶜ : Set α)).toHom)
      rw [Walk.length_map] at hm
      change G.dist (c : α) z ≤ p.length at hm
      exact hm.trans_eq hp
    have hcenter : H.dist c z' ≤ H.radius.toNat := by
      apply ENat.toNat_le_toNat _ hHfin
      exact hc ▸ (H.edist_le_eccent (u := c) (v := z'))
    exact hmap.trans (hcenter.trans hdrop)
  have hcx : (c : α) ≠ x := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using c.property
  obtain ⟨p⟩ := hG x c
  have hp : ¬ p.Nil := p.not_nil_of_ne hcx.symm
  have hxn : G.Adj x p.snd := p.adj_snd hp
  have hnx : p.snd ≠ x := hxn.ne.symm
  have hdistx : G.dist c x ≤ G.radius.toNat := by
    have htri := hG.dist_triangle (u := (c : α)) (v := p.snd) (w := x)
    have hdistn : G.dist p.snd x = 1 := dist_eq_one_iff_adj.mpr hxn.symm
    have hn := hother p.snd hnx
    omega
  have hecc : G.eccent c ≤ (G.radius.toNat : ℕ∞) := by
    rw [G.eccent_le_iff]
    intro z
    rw [← (hG c z).coe_dist_eq_edist]
    apply ENat.natCast_le_natCast.mpr
    exact (show G.dist c z ≤ G.radius.toNat from by
      by_cases hzx : z = x
      · simpa [hzx] using hdistx
      · exact (hother z hzx).trans (Nat.sub_le _ _))
  have heq : G.eccent c = G.radius :=
    le_antisymm (by simpa only [ENat.natCast_toNat hGfin] using hecc) G.radius_le_eccent
  have hdistxeq : G.dist c x = G.radius.toNat := by
    obtain ⟨z, hz⟩ := G.exists_edist_eq_eccent_of_finite (c : α)
    have hdz : G.dist c z = G.radius.toNat := congrArg ENat.toNat (hz.trans heq)
    have hzx : z = x := by
      by_contra hzx
      have := hother z hzx
      omega
    simpa only [hzx] using hdz
  exact ⟨c, hcx, heq, hdistxeq, hother⟩
end WrittenOnTheWallII.GraphConjecture84
