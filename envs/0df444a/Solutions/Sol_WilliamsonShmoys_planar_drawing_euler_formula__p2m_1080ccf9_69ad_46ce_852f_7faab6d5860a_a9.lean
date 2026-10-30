-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_formula__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:06:54.78564+00:00
-- url     : https://prove2.me/submissions/faa18b39-7e0a-4828-a19b-1f8b0de8aa19
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingFaces__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Theorems.Thm_SimpleGraph_euler_from_edge_increments__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12
import Theorems.Thm_WilliamsonShmoys_drawing_carrier_components__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12
import Theorems.Thm_compact_planar_arc_face_increment__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-!
Reduction by edge insertion. The open children separate finite graph arithmetic,
carrier connectivity, and a graph-independent compact planar arc-attachment law.
The edgeless base and the verification of the attachment hypotheses are proved here.

Independent route for the topological child:
Apply compact-set Cech Mayer-Vietoris to K and the arc image A, whose intersection
is exactly the two distinct endpoints. In degree zero the restriction map to
Z squared has diagonal image if the endpoints are in one component of K,
and is onto otherwise (compact Hausdorff components are quasicomponents).
Its cokernel therefore has rank one or zero. Since H1(A) and H1(K intersect A)
vanish, exactness gives the corresponding split extension of H1(K).
Alexander duality, applied after adjoining the point at infinity, identifies
these ranks with the number of plane-complement components minus one.
This is a written argument to formalize, not an existing imported Lean proof.
Framework source: John Pardon, The Hilbert-Smith conjecture for three-manifolds,
revised 2013, Lemmas 3.2 and 3.3:
https://www.math.stonybrook.edu/~jpardon/manuscripts/08_hilbertsmith.pdf
-/

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (ha : ∀ u v, u < v → G.Adj u v →
      ContinuousOn (arc u v) (Set.Icc 0 1) ∧
      Set.InjOn (arc u v) (Set.Icc 0 1) ∧
      arc u v 0 = p u ∧ arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w)
    (hi : ∀ u v x y, u < v → x < y → G.Adj u v → G.Adj x y →
      (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Icc (0 : ℝ) 1, arc u v t = arc x y s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) :
    Finite (WilliamsonShmoys_PlanarDrawingFaces__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9 G p arc) ∧
      Fintype.card V + Nat.card (WilliamsonShmoys_PlanarDrawingFaces__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9 G p arc) =
        G.edgeSet.ncard + Nat.card G.ConnectedComponent + 1 := by
  classical
  let K : SimpleGraph V → Set (ℝ × ℝ) :=
    fun H => WilliamsonShmoys_DrawingCarrier__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12 H p arc
  let F : SimpleGraph V → Type :=
    fun H => ConnectedComponents ↥((K H)ᶜ)
  have hface (H : SimpleGraph V) :
      F H = WilliamsonShmoys_PlanarDrawingFaces__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9 H p arc := by
    have hs : (K H)ᶜ =
        {z : ℝ × ℝ |
          (∀ w : V, z ≠ p w) ∧
          (∀ u v : V, u < v → H.Adj u v →
            ∀ t ∈ Set.Icc (0 : ℝ) 1, z ≠ arc u v t)} := by
      ext z
      simp only [K, WilliamsonShmoys_DrawingCarrier__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12,
        Set.mem_compl_iff, Set.mem_setOf_eq, not_or, not_exists, not_and]
    change ConnectedComponents ↥((K H)ᶜ) =
      ConnectedComponents ↥{z : ℝ × ℝ |
        (∀ w : V, z ≠ p w) ∧
        (∀ u v : V, u < v → H.Adj u v →
          ∀ t ∈ Set.Icc (0 : ℝ) 1, z ≠ arc u v t)}
    rw [hs]
  have hKzero : K ⊥ = Set.range p := by
    ext z
    simp [K, WilliamsonShmoys_DrawingCarrier__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12, eq_comm]
  have hdim : 1 < Module.rank ℝ (ℝ × ℝ) := by
    apply Module.one_lt_rank_of_one_lt_finrank
    norm_num [Module.finrank_prod]
  have hconn : IsConnected ((Set.range p)ᶜ : Set (ℝ × ℝ)) :=
    (Set.finite_range p).countable.isConnected_compl_of_one_lt_rank hdim
  letI : ConnectedSpace ↥((Set.range p)ᶜ) :=
    isConnected_iff_connectedSpace.mp hconn
  have hbase :
      Finite (ConnectedComponents ↥((Set.range p)ᶜ)) ∧
      Nat.card (ConnectedComponents ↥((Set.range p)ᶜ)) = 1 :=
    ⟨inferInstance, Nat.card_unique⟩
  have hzero : Finite (F ⊥) ∧ Nat.card (F ⊥) = 1 := by
    change Finite (ConnectedComponents ↑((K ⊥)ᶜ)) ∧
      Nat.card (ConnectedComponents ↑((K ⊥)ᶜ)) = 1
    rw [hKzero]
    exact hbase
  have hadd : ∀ (H : SimpleGraph V), H ≤ G →
      ∀ u v : V, u < v → G.Adj u v → ¬ H.Adj u v →
      Finite (F H) →
        Finite (F (H ⊔ SimpleGraph.edge u v)) ∧
        (H.Reachable u v →
          Nat.card (F (H ⊔ SimpleGraph.edge u v)) = Nat.card (F H) + 1) ∧
        (¬ H.Reachable u v →
          Nat.card (F (H ⊔ SimpleGraph.edge u v)) = Nat.card (F H)) := by
    intro H hHG u v huv hGuv hHuv hFH
    have hgeometry := WilliamsonShmoys.drawing_carrier_components__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12
      H p arc hp
      (fun x y hxy hHxy => ha x y hxy (hHG hHxy))
      (fun x y x' y' hxy hx'y' hHxy hHx'y' hne t ht s hs heq =>
        hi x y x' y' hxy hx'y' (hHG hHxy) (hHG hHx'y') hne t ht s hs heq)
    rcases ha u v huv hGuv with ⟨hc, hinj, h0, h1, havoid⟩
    have hstart : arc u v 0 ∈ K H := by
      rw [h0]
      exact Or.inl ⟨u, rfl⟩
    have hend : arc u v 1 ∈ K H := by
      rw [h1]
      exact Or.inl ⟨v, rfl⟩
    have hinterior : ∀ t ∈ Set.Ioo (0 : ℝ) 1, arc u v t ∉ K H := by
      intro t ht hz
      rcases hz with ⟨w, hw⟩ | ⟨x, y, hxy, hHxy, s, hs, heq⟩
      · exact havoid t ht w hw
      · have hpair : (u, v) ≠ (x, y) := by
          intro he
          have hx : u = x := congrArg Prod.fst he
          have hy : v = y := congrArg Prod.snd he
          exact hHuv (by simpa only [hx, hy] using hHxy)
        have hboundary := (hi u v x y huv hxy hGuv (hHG hHxy)
          hpair t ⟨le_of_lt ht.1, le_of_lt ht.2⟩ s hs heq).1
        rcases hboundary with ht0 | ht1
        · exact (ne_of_gt ht.1) ht0
        · exact (ne_of_lt ht.2) ht1
    have hcarrier :
        K (H ⊔ SimpleGraph.edge u v) =
          K H ∪ arc u v '' Set.Icc (0 : ℝ) 1 := by
      ext z
      dsimp only [K, WilliamsonShmoys_DrawingCarrier__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12]
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_image]
      constructor
      · intro hz
        rcases hz with hv | ⟨x, y, hxy, hadj, t, ht, heq⟩
        · exact Or.inl (Or.inl hv)
        · rcases (SimpleGraph.sup_adj H (SimpleGraph.edge u v) x y).mp hadj with
            hOld | hEdge
          · exact Or.inl (Or.inr ⟨x, y, hxy, hOld, t, ht, heq⟩)
          · rcases (SimpleGraph.edge_adj u v x y).mp hEdge with ⟨hends, _⟩
            rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inr ⟨t, ht, heq.symm⟩
            · exact (lt_asymm huv hxy).elim
      · intro hz
        rcases hz with hz | ⟨t, ht, heq⟩
        · rcases hz with hv | ⟨x, y, hxy, hadj, t, ht, heq⟩
          · exact Or.inl hv
          · exact Or.inr ⟨x, y, hxy, Or.inl hadj, t, ht, heq⟩
        · exact Or.inr ⟨u, v, huv,
            Or.inr ((SimpleGraph.edge_adj u v u v).mpr
              ⟨Or.inl ⟨rfl, rfl⟩, ne_of_lt huv⟩),
            t, ht, heq.symm⟩
    have htop := compact_planar_arc_face_increment__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12
      (K H) hgeometry.1 (arc u v) hc hinj hstart hend hinterior hFH
    rw [← hcarrier] at htop
    refine ⟨htop.1, ?_, ?_⟩
    · intro hr
      apply htop.2.1
      rw [h0, h1]
      exact (hgeometry.2 u v).mpr hr
    · intro hr
      apply htop.2.2
      intro hs
      apply hr
      apply (hgeometry.2 u v).mp
      simpa only [h0, h1] using hs
  have hresult := SimpleGraph.euler_from_edge_increments__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12
    G (fun H => Finite (F H)) (fun H => Nat.card (F H)) hzero hadd
  simpa only [hface G] using hresult
