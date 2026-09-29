-- Prove2me | solution 1 for Problem97.CGN.CGN4g1_capBlock_of_supportCap
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T05:48:01.500306+00:00
-- url     : https://prove2.me/submissions/88ef4b2f-6154-42f0-8e45-c20731ff030a

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.CGN.CGN4g:21244:26996. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_CGN_CGN
import Definitions.Def_Erdos9796Counting_CGN_CGN4g
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin

section Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN4g

open Problem97 Problem97.CGN

/- Fragment from Erdos9796Proof.P97.CGN.CGN4g; source SHA-256 c412b95ca627805e0db3a1f0d192f80b93891249e4eb1369844d4f8206dcba79 -/


/-!
# CGN4g: ordered-cap block packaging

This file adds the closure-plan data carrier for the ordered-cap block cut out
of a global convex-boundary enumeration, together with the theorem wrappers
that are pure packaging.

The geometric producers for the block (`CGN4g1`, `CGN4g3`, `CGN4g4`) remain
separate. The declarations here are the sanctioned interfaces consumed by the
existing CGN6 / CGN7 layers.
-/

open scoped EuclideanGeometry
open scoped InnerProductSpace












variable {A C : Finset ℝ²}










































theorem solution
    {A C : Finset ℝ²} {n : ℕ} {phi : Fin n → ℝ²}
    (hphi_inj : Function.Injective phi)
    (hphi_image : Finset.univ.image phi = A)
    {lo hi : Fin n} (hlohi : lo < hi)
    (hC_interval : ∀ x : ℝ²,
      x ∈ C ↔ ∃ q : Fin n, lo ≤ q ∧ q ≤ hi ∧ phi q = x)
    (center : ℝ²) (radius : ℝ)
    (hradius_nonneg : 0 ≤ radius)
    (hdisk_C : ∀ x, x ∈ C → dist x center ≤ radius)
    (hlo_circle : dist (phi lo) center = radius)
    (hhi_circle : dist (phi hi) center = radius)
    (hcap_side : ∀ x, x ∈ C ->
      0 ≤ Problem97.signedArea2 (phi lo) (phi hi) x)
    (hcenter_side :
      Problem97.signedArea2 (phi lo) (phi hi) center ≤ 0) :
    ∃ m, ∃ L : OrderedCap m,
      ∃ Packet : MecCapPacket A L,
      ∃ _Hside : MinorCapSideHypotheses Packet,
      ∃ _Block : BoundaryCapBlock A C phi L,
        _Block.lo = lo ∧ _Block.hi = hi := by
  let I : Finset (Fin n) := Finset.Icc lo hi
  have hlo_mem : lo ∈ I := by
    simp [I, Finset.mem_Icc, hlohi.le]
  have hhi_mem : hi ∈ I := by
    simp [I, Finset.mem_Icc, hlohi.le]
  have hIpos : 0 < I.card := Finset.card_pos.mpr ⟨lo, hlo_mem⟩
  have hm : 2 ≤ I.card := by
    simp [I, Fin.card_Icc]
    omega
  let idx : Fin I.card ↪o Fin n := I.orderEmbOfFin rfl
  let L : OrderedCap I.card := {
    points := fun t => phi (idx t)
    injective := by
      intro i j hij
      apply idx.injective
      exact hphi_inj hij
  }
  have hidx_first : idx (firstIndex hm) = lo := by
    calc
      idx (firstIndex hm) = I.orderEmbOfFin rfl ⟨0, hIpos⟩ := by
        rfl
      _ = I.min' ⟨lo, hlo_mem⟩ := Finset.orderEmbOfFin_zero rfl hIpos
      _ = lo := by
        refine (Finset.min'_eq_iff (s := I) (H := ⟨lo, hlo_mem⟩) (a := lo)).2 ?_
        constructor
        · exact hlo_mem
        · intro q hq
          exact (Finset.mem_Icc.mp hq).1
  have hidx_last : idx (lastIndex hm) = hi := by
    calc
      idx (lastIndex hm) = I.orderEmbOfFin rfl
          ⟨I.card - 1, Nat.sub_lt hIpos (by decide : 0 < (1 : ℕ))⟩ := by
        rfl
      _ = I.max' ⟨hi, hhi_mem⟩ := Finset.orderEmbOfFin_last rfl hIpos
      _ = hi := by
        refine (Finset.max'_eq_iff (s := I) (H := ⟨hi, hhi_mem⟩) (a := hi)).2 ?_
        constructor
        · exact hhi_mem
        · intro q hq
          exact (Finset.mem_Icc.mp hq).2
  have hidx_range_exact : ∀ q : Fin n, (lo ≤ q ∧ q ≤ hi) ↔ ∃ t : Fin I.card, idx t = q := by
    intro q
    constructor
    · intro hq
      have hqI : q ∈ I := by simpa [I, Finset.mem_Icc] using hq
      rw [← Finset.image_orderEmbOfFin_univ (s := I) (h := rfl)] at hqI
      rcases Finset.mem_image.mp hqI with ⟨t, _, ht⟩
      exact ⟨t, ht⟩
    · rintro ⟨t, ht⟩
      have htI : idx t ∈ I := Finset.orderEmbOfFin_mem I rfl t
      simpa [ht, I, Finset.mem_Icc] using htI
  have hpoints_eq : ∀ t : Fin I.card, L.points t = phi (idx t) := by
    intro t
    rfl
  have hcap_image : Finset.univ.image L.points = C := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨t, _, rfl⟩
      have hidx_bounds : lo ≤ idx t ∧ idx t ≤ hi :=
        (hidx_range_exact (idx t)).2 ⟨t, rfl⟩
      refine (hC_interval _).2 ?_
      exact ⟨idx t, hidx_bounds.1, hidx_bounds.2, rfl⟩
    · intro hx
      rcases (hC_interval _).1 hx with ⟨q, hloq, hqhi, hqeq⟩
      have hqI : q ∈ I := by simpa [I, Finset.mem_Icc] using And.intro hloq hqhi
      rw [← Finset.image_orderEmbOfFin_univ (s := I) (h := rfl)] at hqI
      rcases Finset.mem_image.mp hqI with ⟨t, _, ht⟩
      have ht' : q = idx t := ht.symm
      have hphi_tx : phi (idx t) = x := by
        simpa [ht'] using hqeq
      refine Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ?_⟩
      simpa [hpoints_eq t] using hphi_tx
  have hcap_subset_A : C ⊆ A := by
    intro x hxC
    rcases (hC_interval _).1 hxC with ⟨q, _, _, rfl⟩
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ q)
  let Block : BoundaryCapBlock A C phi L := {
    hm := hm
    lo := lo
    hi := hi
    hlohi := hlohi
    idx := idx
    idx_strict := (I.orderEmbOfFin rfl).strictMono
    idx_first := hidx_first
    idx_last := hidx_last
    idx_range_exact := hidx_range_exact
    points_eq := hpoints_eq
    cap_image := hcap_image
    cap_subset_A := hcap_subset_A
    phi_image := hphi_image
  }
  let Packet : MecCapPacket A L := {
    hm := hm
    center := center
    radius := radius
    radius_nonneg := hradius_nonneg
    mem_A := by
      intro t
      have htC : L.points t ∈ C := by
        rw [← Block.cap_image]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ t)
      exact Block.cap_subset_A htC
    disk_mem := by
      intro t
      exact hdisk_C (L.points t) <| by
        rw [← Block.cap_image]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ t)
    first_on_circle := by
      simpa [Block.points_eq, Block.idx_first] using hlo_circle
    last_on_circle := by
      simpa [Block.points_eq, Block.idx_last] using hhi_circle
  }
  let Hside : MinorCapSideHypotheses Packet := {
    cap_side_nonneg := by
      intro t
      have htC : L.points t ∈ C := by
        rw [← Block.cap_image]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ t)
      simpa [Block.points_eq, Block.idx_first, Block.idx_last] using
        hcap_side (L.points t) htC
    center_side_nonpos := by
      simpa [Block.idx_first, Block.idx_last, Block.points_eq] using hcenter_side
  }
  exact ⟨I.card, L, Packet, Hside, Block, rfl, rfl⟩

end Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN4g
