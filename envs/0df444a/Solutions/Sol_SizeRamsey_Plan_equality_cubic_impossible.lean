-- Prove2me | solution 1 for SizeRamsey.Plan.equality_cubic_impossible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:30:43.560093+00:00
-- url     : https://prove2.me/submissions/f27766f7-6217-4ed6-8fa4-bc1cf36f5782

module
public import Definitions.Def_SizeRamsey_Equality_Common
public import Definitions.Def_SizeRamsey_Equality_Cubic
public import Theorems.Thm_SizeRamsey_Plan_two_squares_matching_transversal
public import Theorems.Thm_SizeRamsey_Plan_cubic_chordless_reduction
public import Theorems.Thm_SizeRamsey_Plan_erase_card
public import Theorems.Thm_SizeRamsey_Plan_tau4_eq_zero_iff
public import Theorems.Thm_SizeRamsey_Plan_tight_subcubic_chordless
public import Theorems.Thm_SizeRamsey_tau4_le_card

section
@[expose] public section
namespace SizeRamsey.Plan
universe u
attribute [local instance] Classical.propDecidable
private theorem cubic_chordless_adjacency_r1
    {V : Type u} (G : SimpleGraph V) (f : Fin 4 → V)
    (hf : IsC4Map G f)
    (h02 : ¬ G.Adj (f 0) (f 2)) (h13 : ¬ G.Adj (f 1) (f 3)) :
    ∀ i j, G.Adj (f i) (f j) ↔ (SimpleGraph.cycleGraph 4).Adj i j := by
  obtain ⟨hi, h01, h12, h23, h30⟩ := hf
  have h10 := h01.symm
  have h21 := h12.symm
  have h32 := h23.symm
  have h03 := h30.symm
  have h20 : ¬ G.Adj (f 2) (f 0) := fun h => h02 h.symm
  have h31 : ¬ G.Adj (f 3) (f 1) := fun h => h13 h.symm
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp_all [SimpleGraph.cycleGraph_adj] <;> decide
private theorem cubic_third_neighbor_r1
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (v a b : V) (hd : G.degree v = 3)
    (ha : G.Adj v a) (hb : G.Adj v b) (hab : a ≠ b) :
    ∃! w, G.Adj v w ∧ w ≠ a ∧ w ≠ b := by
  classical
  let S := ((G.neighborFinset v).erase a).erase b
  have ha' : a ∈ G.neighborFinset v := by simpa using ha
  have hb' : b ∈ (G.neighborFinset v).erase a := by
    simp [hb, hab.symm]
  have hcard : S.card = 1 := by
    dsimp only [S]
    rw [Finset.card_erase_of_mem hb', Finset.card_erase_of_mem ha',
      G.card_neighborFinset_eq_degree, hd]
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard
  have hmem (x : V) : x ∈ S ↔ G.Adj v x ∧ x ≠ a ∧ x ≠ b := by
    simp only [S, Finset.mem_erase, SimpleGraph.mem_neighborFinset]
    tauto
  refine ⟨w, (hmem w).mp ?_, ?_⟩
  · rw [hw]
    exact Finset.mem_singleton_self w
  · intro y hy
    have hy' := (hmem y).mpr hy
    simpa [hw] using hy'
private theorem cubic_square_unique_cross_r1
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (l r : Fin 4 → V)
    (hl : Function.Injective l) (hr : Function.Injective r)
    (hd : ∀ v, G.degree v = 3)
    (hdisj : ∀ i j, l i ≠ r j)
    (hcover : ∀ v, (∃ i, l i = v) ∨ ∃ j, r j = v)
    (hleft : ∀ i j, G.Adj (l i) (l j) ↔
      (SimpleGraph.cycleGraph 4).Adj i j) :
    ∀ i, ∃! j, G.Adj (l i) (r j) := by
  intro i
  have hnext : (SimpleGraph.cycleGraph 4).Adj i (i + 1) := by
    fin_cases i <;> decide
  have hprev : (SimpleGraph.cycleGraph 4).Adj i (i + 3) := by
    fin_cases i <;> decide
  have hne : l (i + 1) ≠ l (i + 3) := by
    intro he
    have := hl he
    fin_cases i <;> contradiction
  obtain ⟨w, hw, huniq⟩ := cubic_third_neighbor_r1 G (l i)
    (l (i + 1)) (l (i + 3)) (hd _) ((hleft _ _).mpr hnext)
    ((hleft _ _).mpr hprev) hne
  have hwleft : ∀ k, l k ≠ w := by
    intro k hk
    have hik := (hleft i k).mp (hk.symm ▸ hw.1)
    have hkp : k = i + 1 ∨ k = i + 3 := by
      exact (show ∀ i k : Fin 4, (SimpleGraph.cycleGraph 4).Adj i k →
        k = i + 1 ∨ k = i + 3 by decide) i k hik
    rcases hkp with hk' | hk'
    · exact hw.2.1 (hk.symm.trans (congrArg l hk'))
    · exact hw.2.2 (hk.symm.trans (congrArg l hk'))
  obtain ⟨j, hj⟩ := (hcover w).resolve_left (by
    rintro ⟨k, hk⟩
    exact hwleft k hk)
  refine ⟨j, ?_, ?_⟩
  · simpa only [hj] using hw.1
  · intro k hk
    apply hr
    apply Eq.trans _ hj.symm
    apply huniq
    exact ⟨hk, (hdisj (i + 1) k).symm, (hdisj (i + 3) k).symm⟩
end SizeRamsey.Plan
end
end

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
universe u
attribute [local instance] Classical.propDecidable
namespace SizeRamsey.Plan
theorem _root_.solution
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hc : G.Connected)
    (hp : 0 < edgeCount G)
    (hm : edgeCount G ≤ 16)
    (ht : Tight G)
    (ih : SmallerClassified G)
    (h3 : ∀ v, G.degree v = 3) :
    False := by
  classical
  have hhand : 3 * Fintype.card V = 2 * edgeCount G := by
    simpa only [h3, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Nat.mul_comm, edgeCount] using G.sum_degrees_eq_twice_card_edges
  have ht' := ht
  unfold Tight at ht'
  have hm12 : edgeCount G = 12 := by omega
  have hn8 : Fintype.card V = 8 := by omega
  have ht3 : tau4 G = 3 := by omega
  have hmax : ∀ v, G.degree v ≤ 3 := fun v => by rw [h3]
  have hsquare : HasC4 G := by
    by_contra h
    have := (tau4_eq_zero_iff G).mpr h
    omega
  obtain ⟨l, hl⟩ := hsquare
  obtain ⟨hl02, hl13⟩ := tight_subcubic_chordless G ht hmax l hl
  let D : Finset V := Finset.univ.image l
  have hD : D.card = 4 := by
    simp [D, Finset.card_image_of_injective _ hl.1]
  obtain ⟨hred, hcount⟩ := cubic_chordless_reduction G l
    (fun i => h3 (l i)) hl hl02 hl13
  change tau4 G ≤ tau4 (erase G D) + 2 at hred
  have hres : HasC4 (erase G D) := by
    by_contra h
    have := (tau4_eq_zero_iff (erase G D)).mpr h
    omega
  obtain ⟨q, hq⟩ := hres
  have hcard : Fintype.card {v : V // v ∉ D} = 4 := by
    have := erase_card D
    omega
  have hqbij : Function.Bijective q :=
    (Fintype.bijective_iff_injective_and_card q).mpr
      ⟨hq.1, by simp [hcard]⟩
  let r : Fin 4 → V := fun i => (q i).val
  have hr : Function.Injective r := by
    intro i j hij
    exact hq.1 (Subtype.ext hij)
  have hdisj : ∀ i j, l i ≠ r j := by
    intro i j hij
    apply (q j).property
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hij⟩
  have hcover : ∀ v, (∃ i, l i = v) ∨ ∃ j, r j = v := by
    intro v
    by_cases hv : v ∈ D
    · left
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
      exact ⟨i, hi⟩
    · right
      obtain ⟨j, hj⟩ := hqbij.2 ⟨v, hv⟩
      exact ⟨j, congrArg Subtype.val hj⟩
  have hrmap : IsC4Map G r := ⟨hr, hq.2⟩
  obtain ⟨hr02, hr13⟩ := tight_subcubic_chordless G ht hmax r hrmap
  have hleft := cubic_chordless_adjacency_r1 G l hl hl02 hl13
  have hright := cubic_chordless_adjacency_r1 G r hrmap hr02 hr13
  have huniqL := cubic_square_unique_cross_r1 G l r hl.1 hr h3
    hdisj hcover hleft
  have huniqR := cubic_square_unique_cross_r1 G r l hr hl.1 h3
    (fun i j => (hdisj j i).symm) (fun v => (hcover v).symm) hright
  let m : Fin 4 → Fin 4 := fun i => Classical.choose (huniqL i).exists
  have hmAdj : ∀ i, G.Adj (l i) (r (m i)) :=
    fun i => Classical.choose_spec (huniqL i).exists
  have hminj : Function.Injective m := by
    intro i j hij
    apply (huniqR (m i)).unique
    · exact (hmAdj i).symm
    · rw [hij]
      exact (hmAdj j).symm
  let μ : Fin 4 ≃ Fin 4 := Equiv.ofBijective m
    ((Fintype.bijective_iff_injective_and_card m).mpr ⟨hminj, rfl⟩)
  have hcross : ∀ i j, G.Adj (l i) (r j) ↔ μ i = j := by
    intro i j
    constructor
    · intro hij
      exact (huniqL i).unique (hmAdj i) hij
    · intro hij
      subst j
      exact hmAdj i
  have htrans := two_squares_matching_transversal G l r μ hl.1 hr
    hdisj hcover hleft hright hcross
  have hbound := tau4_le_card htrans
  have hcardle : ({l 0, r (μ 2)} : Finset V).card ≤ 2 :=
    Finset.card_le_two
  omega
end SizeRamsey.Plan
