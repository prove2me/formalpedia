-- Prove2me | solution 1 for QuantumBipartiteTesting.Bipartiteness.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:38:40.393315+00:00
-- url     : https://prove2.me/submissions/f12878f7-5528-40e4-a370-1ffe5dfb140b

import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_local_oracle_algorithm_compilation
import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_lemma_3_16
import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_constant_gap_query_lower_bound
import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_colored_tester_center_gap
namespace QuantumBipartiteTesting.Bipartiteness.MainProof
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable Classical.decEq
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
private def LiftEdge {n N : ℕ} (h : n≤N) (e : Edge n) : Edge N :=
  (Fin.castLE h e.1,Fin.castLE h e.2)
private lemma liftEdge_injective {n N : ℕ} (h : n≤N) : Function.Injective (LiftEdge h) := by
  intro a b hh
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg (fun e => e.1.val) hh
  · exact congrArg (fun e => e.2.val) hh
private def LiftGraph {n N : ℕ} (h : n≤N) (G : Finset (Edge n)) : Finset (Edge N) := G.image (LiftEdge h)
private lemma lift_graph {n N : ℕ} (h : n≤N) (G : Finset (Edge n)) (hG : IsGraph G) :
    IsGraph (LiftGraph h G) := by
  intro e he
  obtain ⟨f,hf,rfl⟩ := mem_image.mp he
  exact hG f hf
private lemma lift_neighbors {n N : ℕ} (h : n≤N) (G : Finset (Edge n)) (u : Fin n) :
    Neighbors (LiftGraph h G) (Fin.castLE h u) = (Neighbors G u).image (Fin.castLE h) := by
  ext v
  constructor
  · intro hv
    obtain h'|h' := (mem_filter.mp hv).2
    · obtain ⟨e,he,hh⟩ := mem_image.mp h'
      have hu : e.1=u := Fin.ext (congrArg (fun p => p.1.val) hh)
      have hv : Fin.castLE h e.2=v := congrArg Prod.snd hh
      exact mem_image.mpr ⟨e.2,mem_filter.mpr ⟨mem_univ _,Or.inl (hu ▸ he)⟩,hv⟩
    · obtain ⟨e,he,hh⟩ := mem_image.mp h'
      have hu : e.2=u := Fin.ext (congrArg (fun p => p.2.val) hh)
      have hv : Fin.castLE h e.1=v := congrArg Prod.fst hh
      exact mem_image.mpr ⟨e.1,mem_filter.mpr ⟨mem_univ _,Or.inr (hu ▸ he)⟩,hv⟩
  · intro hv
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hv
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rcases (mem_filter.mp hz).2 with hh|hh
    · exact Or.inl (mem_image.mpr ⟨(u,z),hh,rfl⟩)
    · exact Or.inr (mem_image.mpr ⟨(z,u),hh,rfl⟩)
private lemma outside_neighbors {n N : ℕ} (h : n≤N) (G : Finset (Edge n)) (u : Fin N) (hu : n≤u.val) :
    Neighbors (LiftGraph h G) u = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain hv|hv := (mem_filter.mp hv).2
  · obtain ⟨e,he,hh⟩ := mem_image.mp hv
    have hh := congrArg (fun p => p.1.val) hh
    have he := e.1.isLt
    change e.1.val=u.val at hh
    omega
  · obtain ⟨e,he,hh⟩ := mem_image.mp hv
    have hh := congrArg (fun p => p.2.val) hh
    have he := e.2.isLt
    change e.2.val=u.val at hh
    omega
private lemma lift_degree {n N d : ℕ} (h : n≤N) (G : Finset (Edge n)) (hG : DegreeBound d G) :
    DegreeBound d (LiftGraph h G) := by
  intro u
  by_cases hu : u.val<n
  · have heq : u = Fin.castLE h ⟨u.val,hu⟩ := Fin.ext rfl
    rw [heq,lift_neighbors]
    exact (card_image_le).trans (hG _)
  · rw [outside_neighbors h G u (by omega),card_empty]
    omega
private lemma lift_bipartite {n N : ℕ} (h : n≤N) (G : Finset (Edge n)) (hG : Bipartite G) :
    Bipartite (LiftGraph h G) := by
  obtain ⟨x,hx⟩ := hG
  refine ⟨fun u => if hu : u.val<n then x ⟨u.val,hu⟩ else false,?_⟩
  intro e he
  obtain ⟨f,hf,rfl⟩ := mem_image.mp he
  simpa [LiftEdge] using hx f hf
private def Bad {n : ℕ} (G : Finset (Edge n)) (x : Fin n → Bool) : Finset (Edge n) :=
  G.filter fun e => x e.1 = x e.2

private lemma edit_eq_deletion {n : ℕ} (G : Finset (Edge n)) (hG : IsGraph G) :
    EditDistance G = DeletionDistance G := by
  have hDn : Set.Nonempty {k | ∃ T ⊆ G, Bipartite T ∧ k = (G \ T).card} := by
    exact ⟨G.card, ∅, empty_subset _, ⟨fun _ => false, by simp⟩, by simp⟩
  have hEn : Set.Nonempty {k | ∃ T : Finset (Edge n), IsGraph T ∧ Bipartite T ∧
      k = (G \ T).card + (T \ G).card} := by
    exact ⟨G.card, ∅, by simp [IsGraph], ⟨fun _ => false, by simp⟩, by simp⟩
  apply le_antisymm
  · obtain ⟨T,hTG,hTb,hcard⟩ := Nat.sInf_mem hDn
    change sInf _ ≤ _
    apply Nat.sInf_le
    refine ⟨T,fun e he => hG e (hTG he),hTb,?_⟩
    rw [sdiff_eq_empty_iff_subset.mpr hTG, card_empty, add_zero]
    exact hcard
  · obtain ⟨T,hTg,hTb,hcard⟩ := Nat.sInf_mem hEn
    change sInf _ ≤ _
    apply le_trans (Nat.sInf_le (s := {k | ∃ T ⊆ G, Bipartite T ∧ k = (G \ T).card})
      (show (G \ (G ∩ T)).card ∈ _ from ⟨G ∩ T,inter_subset_left,
        ⟨hTb.choose,fun e he => hTb.choose_spec e (mem_inter.mp he).2⟩,rfl⟩))
    change (G \ (G ∩ T)).card ≤ sInf {k | ∃ T : Finset (Edge n), IsGraph T ∧ Bipartite T ∧ k = (G \ T).card + (T \ G).card}
    rw [hcard, sdiff_inter_self_left]
    omega

private lemma deletion_eq_bad {n : ℕ} (G : Finset (Edge n)) :
    DeletionDistance G = sInf {k | ∃ x : Fin n → Bool, k = (Bad G x).card} := by
  have hDn : Set.Nonempty {k | ∃ T ⊆ G, Bipartite T ∧ k = (G \ T).card} := by
    exact ⟨G.card, ∅, empty_subset _, ⟨fun _ => false, by simp⟩, by simp⟩
  have hBn : Set.Nonempty {k | ∃ x : Fin n → Bool, k = (Bad G x).card} :=
    ⟨_,fun _ => false,rfl⟩
  apply le_antisymm
  · obtain ⟨x,hx⟩ := Nat.sInf_mem hBn
    have hsub : G.filter (fun e => x e.1 ≠ x e.2) ⊆ G := filter_subset _ _
    have hB : Bipartite (G.filter fun e => x e.1 ≠ x e.2) :=
      ⟨x,fun e he => (mem_filter.mp he).2⟩
    apply Nat.sInf_le
    refine ⟨G.filter (fun e => x e.1 ≠ x e.2),hsub,hB,?_⟩
    rw [hx]
    congr 1
    ext e
    simp only [Bad, mem_filter, mem_sdiff]
    tauto
  · obtain ⟨T,hTG,⟨x,hx⟩,hcard⟩ := Nat.sInf_mem hDn
    apply le_trans (Nat.sInf_le (s := {k | ∃ x : Fin n → Bool, k = (Bad G x).card})
      (show (Bad G x).card ∈ _ from ⟨x,rfl⟩))
    change (Bad G x).card ≤ sInf {k | ∃ T ⊆ G, Bipartite T ∧ k = (G \ T).card}
    rw [hcard]
    apply card_le_card
    intro e he
    obtain ⟨heG,hebad⟩ := mem_filter.mp he
    exact mem_sdiff.mpr ⟨heG, fun heT => hx e heT hebad⟩


private lemma lift_bad {n N : ℕ} (h : n≤N) (G : Finset (Edge n)) (y : Fin N→Bool) :
    Bad (LiftGraph h G) y = (Bad G (y ∘ Fin.castLE h)).image (LiftEdge h) := by
  ext e
  simp only [Bad,LiftGraph,mem_filter,mem_image,Function.comp_apply]
  constructor
  · rintro ⟨⟨a,ha,rfl⟩,hh⟩
    exact ⟨a,⟨ha,hh⟩,rfl⟩
  · rintro ⟨a,⟨ha,hh⟩,rfl⟩
    exact ⟨⟨a,ha,rfl⟩,hh⟩
private lemma lift_edit_lower {n N : ℕ} (h : n≤N) (G : Finset (Edge n)) (hG : IsGraph G) :
    EditDistance G ≤ EditDistance (LiftGraph h G) := by
  rw [edit_eq_deletion G hG,edit_eq_deletion _ (lift_graph h G hG),deletion_eq_bad,deletion_eq_bad]
  obtain ⟨y,hy⟩ := Nat.sInf_mem (show Set.Nonempty {k | ∃ y : Fin N→Bool, k=(Bad (LiftGraph h G) y).card} from ⟨_,fun _=>false,rfl⟩)
  rw [hy,lift_bad,card_image_of_injective _ (liftEdge_injective h)]
  exact Nat.sInf_le ⟨y ∘ Fin.castLE h,rfl⟩

private def PackedD {N d : ℕ} (G : Finset (Edge N)) (a : Fin N×Fin d) : Option (Fin N) :=
  ((Neighbors G a.1).sort (·≤·))[a.2.val]?
private lemma packed_represents {N d : ℕ} (G : Finset (Edge N)) (hG : DegreeBound d G) :
    Represents G (PackedD (d:=d) G) := by
  refine ⟨?_,?_,?_⟩
  · intro u v
    constructor
    · rintro ⟨i,hi⟩
      exact (Finset.mem_sort (·≤·)).mp (List.mem_of_getElem? hi)
    · intro hv
      have hv' : v∈(Neighbors G u).sort (·≤·) := (Finset.mem_sort (·≤·)).mpr hv
      obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hv'
      have hid : i<d := lt_of_lt_of_le (by simpa using hi) (hG u)
      refine ⟨⟨i,hid⟩,?_⟩
      exact List.getElem?_eq_some_iff.mpr ⟨hi,he⟩
  · intro u i j v hi hj
    apply Fin.ext
    obtain ⟨hi',hi''⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hj',hj''⟩ := List.getElem?_eq_some_iff.mp hj
    exact (List.Nodup.getElem_inj_iff (Finset.sort_nodup (Neighbors G u) (·≤·))).mp (hi''.trans hj''.symm)
  · intro u i
    exact (List.getElem?_eq_none_iff).trans (by rw [Finset.length_sort])
private def PathEdges {n : ℕ} (e : ColoredEdge n) (b : Bool) : Finset (Edge (7*n)) :=
  if b then {UEdge (Original e.1) (AuxiliaryA e.1 e.2.2),
    UEdge (AuxiliaryA e.1 e.2.2) (AuxiliaryP e.1 e.2.2),
    UEdge (AuxiliaryP e.1 e.2.2) (Original e.2.1)}
  else {UEdge (Original e.1) (AuxiliaryA e.1 e.2.2),
    UEdge (AuxiliaryA e.1 e.2.2) (Original e.2.1)}

private lemma original_lt_A {n : ℕ} (u v : Fin n) (j : Fin 3) :
    Original u < AuxiliaryA v j := by
  change u.val < n + 6*v.val + 2*j.val
  omega
private lemma original_lt_P {n : ℕ} (u v : Fin n) (j : Fin 3) :
    Original u < AuxiliaryP v j := by
  change u.val < n + 6*v.val + 2*j.val + 1
  omega
private lemma A_lt_P {n : ℕ} (u : Fin n) (j : Fin 3) :
    AuxiliaryA u j < AuxiliaryP u j := by
  change n+6*u.val+2*j.val < n+6*u.val+2*j.val+1
  omega
private lemma A_injective {n : ℕ} (u v : Fin n) (i j : Fin 3)
    (h : AuxiliaryA u i = AuxiliaryA v j) : u = v ∧ i = j := by
  have hv := congrArg Fin.val h
  simp only [AuxiliaryA] at hv
  have h1 := i.isLt
  have h2 := j.isLt
  constructor <;> apply Fin.ext <;> omega
private lemma P_injective {n : ℕ} (u v : Fin n) (i j : Fin 3)
    (h : AuxiliaryP u i = AuxiliaryP v j) : u = v ∧ i = j := by
  have hv := congrArg Fin.val h
  simp only [AuxiliaryP] at hv
  have h1 := i.isLt
  have h2 := j.isLt
  constructor <;> apply Fin.ext <;> omega
private lemma A_ne_P {n : ℕ} (u v : Fin n) (i j : Fin 3) :
    AuxiliaryA u i ≠ AuxiliaryP v j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [AuxiliaryA, AuxiliaryP] at hv
  omega

private lemma uedge_lt {n : ℕ} (u v : Fin n) (h : u ≠ v) :
    (UEdge u v).1 < (UEdge u v).2 := by
  simp only [UEdge]
  exact min_lt_max.mpr h

private lemma gadget_graph {n : ℕ} (F : Finset (ColoredEdge n))
    (b : ColoredEdge n → Bool) : IsGraph (Gadget F b) := by
  intro a ha
  obtain ⟨e, he, ha⟩ := mem_biUnion.mp ha
  change a ∈ PathEdges e (b e) at ha
  cases hb : b e <;> simp only [PathEdges, hb, Bool.false_eq_true, ↓reduceIte,
    mem_insert, mem_singleton] at ha
  · rcases ha with rfl | rfl
    · exact uedge_lt _ _ (ne_of_lt (original_lt_A _ _ _))
    · exact uedge_lt _ _ (ne_of_gt (original_lt_A _ _ _))
  · rcases ha with rfl | rfl | rfl
    · exact uedge_lt _ _ (ne_of_lt (original_lt_A _ _ _))
    · exact uedge_lt _ _ (ne_of_lt (A_lt_P _ _))
    · exact uedge_lt _ _ (ne_of_gt (original_lt_P _ _ _))

private lemma proper_uedge {n : ℕ} (x : Fin n → Bool) (u v : Fin n) :
    x (UEdge u v).1 ≠ x (UEdge u v).2 ↔ x u ≠ x v := by
  by_cases h : u ≤ v
  · simp [UEdge, min_eq_left h, max_eq_right h]
  · have h' := le_of_not_ge h
    simp [UEdge, min_eq_right h', max_eq_left h', ne_comm]

private lemma path_parity {n : ℕ} (x : Fin (7*n) → Bool) (e : ColoredEdge n) (b : Bool)
    (h : ∀ a ∈ PathEdges e b, x a.1 ≠ x a.2) :
    xor (x (Original e.1)) (x (Original e.2.1)) = b := by
  cases b
  · have h1 := h (UEdge (Original e.1) (AuxiliaryA e.1 e.2.2)) (by simp [PathEdges])
    have h2 := h (UEdge (AuxiliaryA e.1 e.2.2) (Original e.2.1)) (by simp [PathEdges])
    rw [proper_uedge] at h1 h2
    cases hx : x (Original e.1) <;> cases ha : x (AuxiliaryA e.1 e.2.2) <;>
      cases hy : x (Original e.2.1) <;> simp_all
  · have h1 := h (UEdge (Original e.1) (AuxiliaryA e.1 e.2.2)) (by simp [PathEdges])
    have h2 := h (UEdge (AuxiliaryA e.1 e.2.2) (AuxiliaryP e.1 e.2.2)) (by simp [PathEdges])
    have h3 := h (UEdge (AuxiliaryP e.1 e.2.2) (Original e.2.1)) (by simp [PathEdges])
    rw [proper_uedge] at h1 h2 h3
    cases hx : x (Original e.1) <;> cases ha : x (AuxiliaryA e.1 e.2.2) <;>
      cases hp : x (AuxiliaryP e.1 e.2.2) <;> cases hy : x (Original e.2.1) <;> simp_all

private def Extend {n : ℕ} (x : Fin n → Bool) (v : Fin (7*n)) : Bool :=
  if h : v.val < n then x ⟨v.val,h⟩
  else if h' : (v.val-n)/6 < n then
    if (v.val-n)%2 = 0 then !(x ⟨(v.val-n)/6,h'⟩) else x ⟨(v.val-n)/6,h'⟩
  else false

private lemma extend_original {n : ℕ} (x : Fin n → Bool) (u : Fin n) :
    Extend x (Original u) = x u := by simp [Extend, Original, u.isLt]
private lemma extend_A {n : ℕ} (x : Fin n → Bool) (u : Fin n) (j : Fin 3) :
    Extend x (AuxiliaryA u j) = !(x u) := by
  have hu := u.isLt
  have hj := j.isLt
  have hdiv : (6*u.val+2*j.val)/6 = u.val := by omega
  have hmod : (6*u.val+2*j.val)%2 = 0 := by omega
  have hn : ¬ n+6*u.val+2*j.val < n := by omega
  have hs : n+6*u.val+2*j.val-n = 6*u.val+2*j.val := by omega
  simp [Extend, AuxiliaryA, hn, hs, hdiv, hmod, hu]
private lemma extend_P {n : ℕ} (x : Fin n → Bool) (u : Fin n) (j : Fin 3) :
    Extend x (AuxiliaryP u j) = x u := by
  have hu := u.isLt
  have hj := j.isLt
  have hdiv : (6*u.val+2*j.val+1)/6 = u.val := by omega
  have hmod : (6*u.val+2*j.val+1)%2 = 1 := by omega
  have hn : ¬ n+6*u.val+2*j.val+1 < n := by omega
  have hs : n+6*u.val+2*j.val+1-n = 6*u.val+2*j.val+1 := by omega
  simp [Extend, AuxiliaryP, hn, hs, hdiv, hmod, hu]

private lemma extend_path {n : ℕ} (x : Fin n → Bool) (e : ColoredEdge n) (b : Bool)
    (h : xor (x e.1) (x e.2.1) = b) :
    ∀ a ∈ PathEdges e b, Extend x a.1 ≠ Extend x a.2 := by
  intro a ha
  cases b <;> simp only [PathEdges, Bool.false_eq_true, ↓reduceIte,
    mem_insert, mem_singleton] at ha
  · rcases ha with rfl | rfl <;> rw [proper_uedge]
    · simp [extend_original, extend_A]
    · rw [extend_A, extend_original]
      cases hx : x e.1 <;> cases hy : x e.2.1 <;> simp_all
  · rcases ha with rfl | rfl | rfl <;> rw [proper_uedge]
    · simp [extend_original, extend_A]
    · simp [extend_A, extend_P]
    · rw [extend_P, extend_original]
      cases hx : x e.1 <;> cases hy : x e.2.1 <;> simp_all

private lemma gadget_bipartite {n : ℕ} (F : Finset (ColoredEdge n))
    (b : ColoredEdge n → Bool) : Bipartite (Gadget F b) ↔ Balanced F b := by
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨fun u => x (Original u), fun e he => path_parity x e (b e) ?_⟩
    intro a ha
    exact hx a (mem_biUnion.mpr ⟨e,he,ha⟩)
  · rintro ⟨x,hx⟩
    refine ⟨Extend x, ?_⟩
    intro a ha
    obtain ⟨e,he,ha⟩ := mem_biUnion.mp ha
    exact extend_path x e (b e) (hx e he) a ha

private def Owner {n : ℕ} (v : Fin (7*n)) : ℕ × ℕ :=
  ((v.val-n)/6, ((v.val-n)%6)/2)

private lemma owner_A {n : ℕ} (u : Fin n) (j : Fin 3) :
    Owner (AuxiliaryA u j) = (u.val,j.val) := by
  have hj := j.isLt
  simp only [Owner, AuxiliaryA]
  congr 1 <;> omega
private lemma owner_P {n : ℕ} (u : Fin n) (j : Fin 3) :
    Owner (AuxiliaryP u j) = (u.val,j.val) := by
  have hj := j.isLt
  simp only [Owner, AuxiliaryP]
  congr 1 <;> omega

private lemma path_normal {n : ℕ} (e : ColoredEdge n) (b : Bool) :
    PathEdges e b = if b then
      {(Original e.1, AuxiliaryA e.1 e.2.2),
       (AuxiliaryA e.1 e.2.2, AuxiliaryP e.1 e.2.2),
       (Original e.2.1, AuxiliaryP e.1 e.2.2)}
    else {(Original e.1, AuxiliaryA e.1 e.2.2),
       (Original e.2.1, AuxiliaryA e.1 e.2.2)} := by
  have h1 := le_of_lt (original_lt_A e.1 e.1 e.2.2)
  have h2 := le_of_lt (original_lt_A e.2.1 e.1 e.2.2)
  have h3 := le_of_lt (original_lt_P e.2.1 e.1 e.2.2)
  have h4 := le_of_lt (A_lt_P e.1 e.2.2)
  simp [PathEdges, UEdge, min_eq_left h1, max_eq_right h1,
    min_eq_right h2, max_eq_left h2, min_eq_right h3, max_eq_left h3,
    min_eq_left h4, max_eq_right h4]

private lemma path_owner {n : ℕ} (e : ColoredEdge n) (b : Bool) (a : Edge (7*n))
    (ha : a ∈ PathEdges e b) : Owner a.2 = (e.1.val,e.2.2.val) := by
  rw [path_normal] at ha
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, mem_insert, mem_singleton] at ha
  · rcases ha with rfl | rfl <;> exact owner_A _ _
  · rcases ha with rfl | rfl | rfl
    · exact owner_A _ _
    · exact owner_P _ _
    · exact owner_P _ _

private lemma path_disjoint {n : ℕ} (F : Finset (ColoredEdge n)) (hF : Consistent F)
    (b : ColoredEdge n → Bool) : (F : Set (ColoredEdge n)).PairwiseDisjoint (fun e => PathEdges e (b e)) := by
  intro e he f hf hne
  apply Finset.disjoint_left.mpr
  intro a hae haf
  have hh := (path_owner e (b e) a hae).symm.trans (path_owner f (b f) a haf)
  have hu : e.1 = f.1 := Fin.ext (congrArg Prod.fst hh)
  have hj : e.2.2 = f.2.2 := Fin.ext (congrArg Prod.snd hh)
  exact hne (hF.2 e he f hf hj ⟨e.1,Or.inl rfl,Or.inl hu.symm⟩)


private lemma original_inj {n : ℕ} {u v : Fin n} (h : Original u = Original v) : u = v := by
  apply Fin.ext
  exact congrArg (fun a : Fin (7*n) => a.val) h

private def FirstNbr {n : ℕ} (e : ColoredEdge n) (u : Fin n) (b : Bool) : Fin (7*n) :=
  if e.1 = u then AuxiliaryA e.1 e.2.2
  else if b then AuxiliaryP e.1 e.2.2 else AuxiliaryA e.1 e.2.2

private lemma original_neighbor_path {n : ℕ} (e : ColoredEdge n) (b : Bool)
    (he : e.1 < e.2.1) (u : Fin n) (v : Fin (7*n))
    (h : (Original u,v) ∈ PathEdges e b ∨ (v,Original u) ∈ PathEdges e b) :
    Incident e u ∧ v = FirstNbr e u b := by
  have hA : ∀ a j, Original u ≠ AuxiliaryA a j := fun a j => ne_of_lt (original_lt_A u a j)
  have hP : ∀ a j, Original u ≠ AuxiliaryP a j := fun a j => ne_of_lt (original_lt_P u a j)
  rw [path_normal] at h
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, mem_insert, mem_singleton,
    Prod.mk.injEq] at h
  · rcases h with (⟨h,rfl⟩ | ⟨h,rfl⟩) | (⟨_,h⟩ | ⟨_,h⟩)
    · have hu := original_inj h
      subst u
      simp [Incident, FirstNbr]
    · have hu := original_inj h
      subst u
      simp [Incident, FirstNbr, ne_of_lt he]
    · exact (hA _ _ h).elim
    · exact (hA _ _ h).elim
  · rcases h with (⟨h,rfl⟩ | ⟨h,_⟩ | ⟨h,rfl⟩) | (⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩)
    · have hu := original_inj h
      subst u
      simp [Incident, FirstNbr]
    · exact (hA _ _ h).elim
    · have hu := original_inj h
      subst u
      simp [Incident, FirstNbr, ne_of_lt he]
    · exact (hA _ _ h).elim
    · exact (hP _ _ h).elim
    · exact (hP _ _ h).elim


private lemma auxiliary_owner {n : ℕ} (e : ColoredEdge n) (b : Bool)
    (v z : Fin (7*n)) (hv : ∀ u : Fin n, v ≠ Original u)
    (hz : (v,z) ∈ PathEdges e b ∨ (z,v) ∈ PathEdges e b) :
    Owner v = (e.1.val,e.2.2.val) := by
  rw [path_normal] at hz
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, mem_insert, mem_singleton,
    Prod.mk.injEq] at hz
  · rcases hz with (⟨h,_⟩ | ⟨h,_⟩) | (⟨_,rfl⟩ | ⟨_,rfl⟩)
    · exact (hv _ h).elim
    · exact (hv _ h).elim
    · exact owner_A _ _
    · exact owner_A _ _
  · rcases hz with (⟨h,_⟩ | ⟨rfl,_⟩ | ⟨h,_⟩) | (⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩)
    · exact (hv _ h).elim
    · exact owner_A _ _
    · exact (hv _ h).elim
    · exact owner_A _ _
    · exact owner_P _ _
    · exact owner_P _ _

private lemma neighbor_witness {n : ℕ} (F : Finset (ColoredEdge n))
    (b : ColoredEdge n → Bool) (v z : Fin (7*n)) (hz : z ∈ Neighbors (Gadget F b) v) :
    ∃ e ∈ F, (v,z) ∈ PathEdges e (b e) ∨ (z,v) ∈ PathEdges e (b e) := by
  rcases (mem_filter.mp hz).2 with hz | hz
  · obtain ⟨e,he,hz⟩ := mem_biUnion.mp hz
    exact ⟨e,he,Or.inl hz⟩
  · obtain ⟨e,he,hz⟩ := mem_biUnion.mp hz
    exact ⟨e,he,Or.inr hz⟩


private def BaseVertex {n : ℕ} (v : Fin (7*n)) : Fin n :=
  if h : v.val < n then ⟨v.val,h⟩ else ⟨(v.val-n)/6, by have hv := v.isLt; omega⟩

private lemma base_original {n : ℕ} (u : Fin n) : BaseVertex (Original u) = u := by
  simp [BaseVertex, Original, u.isLt]

private lemma base_incident {n : ℕ} (e : ColoredEdge n) (b : Bool) (he : e.1 < e.2.1)
    (v z : Fin (7*n))
    (hz : (v,z) ∈ PathEdges e b ∨ (z,v) ∈ PathEdges e b) :
    Incident e (BaseVertex v) := by
  by_cases ho : ∃ u : Fin n, v = Original u
  · obtain ⟨u,rfl⟩ := ho
    rw [base_original]
    exact (original_neighbor_path e b he u z hz).1
  · have hv : ∀ u : Fin n, v ≠ Original u := by simpa only [not_exists] using ho
    have hown := congrArg Prod.fst (auxiliary_owner e b v z hv hz)
    have hn : ¬ v.val < n := by
      intro hn
      apply hv ⟨v.val,hn⟩
      apply Fin.ext
      rfl
    have hb : BaseVertex v = e.1 := by
      apply Fin.ext
      simpa [BaseVertex,hn,Owner] using hown
    exact Or.inl hb.symm

private def Other {n : ℕ} (e : ColoredEdge n) (u : Fin n) : Fin n :=
  if e.1 = u then e.2.1 else e.1

private lemma reconstruct {n : ℕ} (e : ColoredEdge n) (u : Fin n)
    (he : e.1 < e.2.1) (hu : Incident e u) :
    e = (min u (Other e u),max u (Other e u),e.2.2) := by
  rcases hu with h | h
  · subst u
    simp [Other,min_eq_left (le_of_lt he),max_eq_right (le_of_lt he)]
  · subst u
    simp [Other,ne_of_lt he,min_eq_right (le_of_lt he),max_eq_left (le_of_lt he)]

private lemma response_some {n : ℕ} (F : Finset (ColoredEdge n)) (hF : Consistent F)
    (b : ColoredEdge n → Bool) (u v : Fin n) (j : Fin 3) (s : Bool) :
    SignedResponse F b (u,j) = some (v,s) ↔
      ∃ e ∈ F, e.2.2 = j ∧ Incident e u ∧ Other e u = v ∧ b e = s := by
  unfold SignedResponse
  split_ifs with h
  · have hc := h.choose_spec
    constructor
    · intro hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      exact ⟨h.choose,hc.1,hc.2.1,hc.2.2,hs.1,hs.2⟩
    · rintro ⟨e,he,hj,hu,hv,hb⟩
      have hh : h.choose = e := hF.2 h.choose hc.1 e he (hc.2.1.trans hj.symm)
        ⟨u,hc.2.2,hu⟩
      simp only [hh, Option.some.injEq, Prod.mk.injEq]
      exact ⟨hv,hb⟩
  · constructor
    · simp
    · rintro ⟨e,he,hj,hu,_,_⟩
      exact (h ⟨e,he,hj,hu⟩).elim

private lemma same_response_edge {n : ℕ} (F F' : Finset (ColoredEdge n))
    (hF : Consistent F) (hF' : Consistent F') (b b' : ColoredEdge n → Bool)
    (u : Fin n) (h : ∀ j, SignedResponse F b (u,j) = SignedResponse F' b' (u,j))
    (e : ColoredEdge n) (he : e ∈ F) (hu : Incident e u) : e ∈ F' ∧ b e = b' e := by
  have hr : SignedResponse F b (u,e.2.2) = some (Other e u,b e) :=
    (response_some F hF b u (Other e u) e.2.2 (b e)).mpr ⟨e,he,rfl,hu,rfl,rfl⟩
  rw [h] at hr
  obtain ⟨f,hf,hj,hfu,hfo,hfb⟩ := (response_some F' hF' b' u _ _ _).mp hr
  have hef : e = f := by
    calc e = (min u (Other e u),max u (Other e u),e.2.2) := reconstruct e u (hF.1 e he) hu
         _ = (min u (Other f u),max u (Other f u),f.2.2) := by rw [hfo,hj]
         _ = f := (reconstruct f u (hF'.1 f hf) hfu).symm
  subst f
  exact ⟨hf,hfb.symm⟩

private lemma same_responses_neighbors {n : ℕ} (F F' : Finset (ColoredEdge n))
    (hF : Consistent F) (hF' : Consistent F') (b b' : ColoredEdge n → Bool)
    (v : Fin (7*n)) (h : ∀ j, SignedResponse F b (BaseVertex v,j) =
      SignedResponse F' b' (BaseVertex v,j)) :
    Neighbors (Gadget F b) v = Neighbors (Gadget F' b') v := by
  have hsub : ∀ (F F' : Finset (ColoredEdge n)) (b b' : ColoredEdge n → Bool),
      Consistent F → Consistent F' →
      (∀ j, SignedResponse F b (BaseVertex v,j) = SignedResponse F' b' (BaseVertex v,j)) →
      Neighbors (Gadget F b) v ⊆ Neighbors (Gadget F' b') v := by
    intro F F' b b' hF hF' h z hz
    obtain ⟨e,he,hepath⟩ := neighbor_witness F b v z hz
    have hinc := base_incident e (b e) (hF.1 e he) v z hepath
    obtain ⟨he',hb⟩ := same_response_edge F F' hF hF' b b' (BaseVertex v) h e he hinc
    rw [hb] at hepath
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rcases hepath with hp | hp
    · exact Or.inl (mem_biUnion.mpr ⟨e,he',hp⟩)
    · exact Or.inr (mem_biUnion.mpr ⟨e,he',hp⟩)
  exact subset_antisymm (hsub F F' b b' hF hF' h) (hsub F' F b' b hF' hF fun j => (h j).symm)


private def QueryAtPadded {n N d : ℕ} (l : Address N d) (j : Fin 3) : Address n 3 :=
  match l.1 with
  | none => (none,j)
  | some v => if hv : v.val<7*n then (some (BaseVertex ⟨v.val,hv⟩),j) else (none,j)

private def LocalValuePadded {n N d kS kT : ℕ} (h : 7*n≤N) (ES : Encoding (Fin n×Bool) kS)
    (ET : Encoding (Fin N) kT) (l : Address N d) (c : Fin 3→Bits kS) : Bits kT :=
  if hc : ∃ P : Finset (ColoredEdge n)×(ColoredEdge n→Bool), Consistent P.1 ∧
      ∀ j, ES.code (LiftOracle (SignedResponse P.1 P.2) (QueryAtPadded l j))=c j then
    ET.code (LiftOracle (PackedD (d:=d) (LiftGraph h (Gadget hc.choose.1 hc.choose.2))) l)
  else 0

private lemma localValue_padded_correct {n N d kS kT : ℕ} (h : 7*n≤N)
    (ES : Encoding (Fin n×Bool) kS) (ET : Encoding (Fin N) kT)
    (F : Finset (ColoredEdge n)) (hF : Consistent F) (b : ColoredEdge n→Bool) (l : Address N d) :
    LocalValuePadded h ES ET l (fun j => ES.code (LiftOracle (SignedResponse F b) (QueryAtPadded l j))) =
      ET.code (LiftOracle (PackedD (d:=d) (LiftGraph h (Gadget F b))) l) := by
  unfold LocalValuePadded
  split_ifs with hc
  · have hG := hc.choose_spec.1
    have he := hc.choose_spec.2
    rcases l with ⟨v,i⟩
    cases v with
    | none => rfl
    | some v =>
      change ET.code (PackedD _ (v,i)) = ET.code (PackedD _ (v,i))
      by_cases hv : v.val<7*n
      · let u : Fin (7*n) := ⟨v.val,hv⟩
        have hcast : v=Fin.castLE h u := Fin.ext rfl
        have hn : Neighbors (Gadget hc.choose.1 hc.choose.2) u = Neighbors (Gadget F b) u := by
          apply same_responses_neighbors _ _ hG hF _ _ u
          intro j
          have hh := ES.injective (he j)
          simpa only [QueryAtPadded,hv,dif_pos,LiftOracle] using hh
        simp only [PackedD,hcast,lift_neighbors,hn]
      · simp only [PackedD,outside_neighbors h _ v (by omega)]
  · exact (hc ⟨(F,b),hF,fun _=>rfl⟩).elim

private def BinaryEncoding (S : Type) [Fintype S] [DecidableEq S] : Encoding S (Fintype.card S) where
  code z := match z with
    | none => 0
    | some s => fun i => if Fintype.equivFin S s = i then 1 else 0
  injective := by
    intro x y h
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some t =>
        have hh := congrFun h (Fintype.equivFin S t)
        norm_num at hh
    | some s =>
      cases y with
      | none =>
        have hh := congrFun h (Fintype.equivFin S s)
        norm_num at hh
      | some t =>
        congr 1
        by_contra hn
        have he : Fintype.equivFin S t ≠ Fintype.equivFin S s := fun h => hn ((Fintype.equivFin S).injective h).symm
        have hh := congrFun h (Fintype.equivFin S s)
        simp only [ite_true,he,if_false] at hh
        norm_num at hh
  null := rfl

private lemma scale_padding {n N : ℕ} (hn : 2≤n) (hnN : n≤N) (hN : N≤8*n) :
    LowerBoundScale N ≤ 2*LowerBoundScale n := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hN0 : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hlog : (0:ℝ)<Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hlogN : Real.log n≤Real.log N := Real.log_le_log hn0 (by exact_mod_cast hnN)
  have hp : (N:ℝ)^(1/3:ℝ) ≤ 2*(n:ℝ)^(1/3:ℝ) := by
    calc
      _ ≤ ((8:ℝ)*n)^(1/3:ℝ) := Real.rpow_le_rpow hN0.le (by exact_mod_cast hN) (by norm_num)
      _ = (8:ℝ)^(1/3:ℝ)*(n:ℝ)^(1/3:ℝ) := Real.mul_rpow (by norm_num) hn0.le
      _ = _ := by
        have h8 : (8:ℝ)^(1/3:ℝ)=2 := by
          convert Real.pow_rpow_inv_natCast (x:=(2:ℝ)) (n:=3) (by norm_num) (by norm_num) using 1 <;> norm_num
        rw [h8]
  unfold LowerBoundScale
  rw [← mul_div_assoc]
  exact div_le_div₀ (by positivity) hp hlog hlogN

private lemma tester_reduction {n N d k w q : ℕ} (h7 : 7*n≤N) (hN : N≤8*n) (hd : 3≤d)
    (ε : ℝ) (hε : 0<ε) (E : Encoding (Fin N) k) (A : Algorithm (Address N d) k w q)
    (out : (Address N d×Bits k)×Fin w→Bool) (htest : BipartiteTester ε E A out) :
    ∃ kS wS qS : ℕ, ∃ ES : Encoding (Fin n×Bool) kS, ∃ AS : Algorithm (Address n 3) kS wS qS,
    ∃ outs : (Address n 3×Bits kS)×Fin wS→Bool, qS≤6*q ∧
      ∀ F : Finset (ColoredEdge n), Consistent F → ∀ b : ColoredEdge n→Bool,
        (Balanced F b → 2/3≤Accept ES AS outs (LiftOracle (SignedResponse F b))) ∧
        ((ε*8*d/3)*n*3≤(Frustration F b:ℝ) → Accept ES AS outs (LiftOracle (SignedResponse F b))≤1/3) := by
  let ES := BinaryEncoding (Fin n×Bool)
  obtain ⟨wS,qS,AS,outs,hcount,heffect⟩ := local_oracle_algorithm_compilation
    (Fintype.card (Fin n×Bool)) k w q ((none,⟨0,by norm_num⟩) : Address n 3)
    QueryAtPadded (LocalValuePadded h7 ES E) A out
  refine ⟨_,wS,qS,ES,AS,outs,hcount,?_⟩
  intro F hF b
  have heq : Accept ES AS outs (LiftOracle (SignedResponse F b)) =
      Accept E A out (LiftOracle (PackedD (d:=d) (LiftGraph h7 (Gadget F b)))) := by
    have hh := heffect (ES.code ∘ LiftOracle (SignedResponse F b))
    have hlocal : (fun l => LocalValuePadded h7 ES E l
        (fun j => (ES.code ∘ LiftOracle (SignedResponse F b)) (QueryAtPadded l j))) =
        E.code ∘ LiftOracle (PackedD (d:=d) (LiftGraph h7 (Gadget F b))) := by
      funext l
      exact localValue_padded_correct h7 ES E F hF b l
    simpa only [hlocal,Accept] using hh
  rw [heq]
  obtain ⟨hg,hdeg,hbip,hdel,hedit⟩ := lemma_3_16.1 n F hF b
  have hG := lift_graph h7 _ hg
  have hD : DegreeBound d (LiftGraph h7 (Gadget F b)) :=
    fun u => (lift_degree h7 _ hdeg u).trans hd
  have ht := htest _ hG hD _ (packed_represents _ hD)
  refine ⟨fun hb => ht.1 (lift_bipartite h7 _ (hbip.mpr hb)),?_⟩
  intro hf
  apply ht.2
  have hNr : (N:ℝ)≤8*n := by exact_mod_cast hN
  have hdist : (Frustration F b:ℝ)≤EditDistance (LiftGraph h7 (Gadget F b)) := by
    rw [← hedit]
    exact_mod_cast lift_edit_lower h7 _ hg
  unfold Far
  apply le_trans _ hdist
  apply le_trans _ hf
  have hd0 : (0:ℝ)≤d := Nat.cast_nonneg _
  nlinarith [mul_nonneg (mul_nonneg hε.le hd0) (sub_nonneg.mpr hNr)]

end
end QuantumBipartiteTesting.Bipartiteness.MainProof

open QuantumBipartiteTesting.Bipartiteness
open QuantumBipartiteTesting.Bipartiteness.MainProof

theorem solution (d : ℕ) (hd : 3 ≤ d) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ k w q : ℕ,
    ∀ E : Encoding (Fin N) k, ∀ A : Algorithm (Address N d) k w q,
    ∀ out : (Address N d × Bits k) × Fin w → Bool,
      BipartiteTester ε E A out → c * LowerBoundScale N ≤ (q : ℝ) := by
  have hdR : (3:ℝ)≤d := by exact_mod_cast hd
  refine ⟨1/(800*(d:ℝ)),by positivity,by apply (div_lt_one (by positivity)).mpr; linarith,?_⟩
  intro ε hε hεmax
  obtain ⟨c,hc,Ng,hNg,hgap⟩ := constant_gap_query_lower_bound
  obtain ⟨Nh,hNh,hfamily⟩ := colored_tester_center_gap
  let n0 := max (max Ng Nh) 6
  refine ⟨c/12,by positivity,7*n0,by dsimp [n0]; omega,?_⟩
  intro N hNN k w q E A out htest
  let n := N/7
  have hn0 : n0≤n := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
  have hn6 : 6≤n := (le_max_right _ _).trans hn0
  have hnNg : Ng≤n := (le_max_left _ _).trans ((le_max_left _ _).trans hn0)
  have hnNh : Nh≤n := (le_max_right _ _).trans ((le_max_left _ _).trans hn0)
  have h7 : 7*n≤N := by dsimp [n]; omega
  have hN8 : N≤8*n := by have hh := Nat.mod_lt N (by norm_num : 0<7); have he := Nat.mod_add_div N 7; dsimp [n] at *; omega
  obtain ⟨kS,wS,qS,ES,AS,outs,hcount,ht⟩ := tester_reduction h7 hN8 hd ε hε E A out htest
  have hη : 0<ε*8*d/3 := by positivity
  have hηmax : ε*8*d/3≤1/300 := by
    have hh := (le_div_iff₀ (by positivity : (0:ℝ)<800*d)).mp hεmax
    nlinarith
  have hg := hfamily n hnNh (ε*8*d/3) hη hηmax kS wS qS ES AS outs ht
  have hl := hgap n hnNg kS wS qS ES AS outs hg
  have hscale := scale_padding (by omega : 2≤n) (by omega : n≤N) hN8
  have hcountR : (qS:ℝ)≤6*q := by exact_mod_cast hcount
  nlinarith [mul_le_mul_of_nonneg_left hscale hc.le]
