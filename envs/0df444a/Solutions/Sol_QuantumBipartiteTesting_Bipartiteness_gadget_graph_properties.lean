-- Prove2me | solution 1 for QuantumBipartiteTesting.Bipartiteness.gadget_graph_properties
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T13:20:17.646031+00:00
-- url     : https://prove2.me/submissions/74f7f8a8-c425-4534-be6a-94c57dfd3d76

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction

open Finset
namespace QuantumBipartiteTesting.Bipartiteness
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000

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

private def Terminal {n : ℕ} (e : ColoredEdge n) (b : Bool) : Edge (7*n) :=
  (Original e.2.1, if b then AuxiliaryP e.1 e.2.2 else AuxiliaryA e.1 e.2.2)

private lemma terminal_mem {n : ℕ} (e : ColoredEdge n) (b : Bool) :
    Terminal e b ∈ PathEdges e b := by
  rw [path_normal]
  cases b <;> simp [Terminal]

private lemma terminal_inj {n : ℕ} (F : Finset (ColoredEdge n)) (hF : Consistent F)
    (b : ColoredEdge n → Bool) : Set.InjOn (fun e => Terminal e (b e)) (F : Set _) := by
  intro e he f hf h
  by_contra hne
  apply (Finset.disjoint_left.mp (path_disjoint F hF b he hf hne)) (terminal_mem e (b e))
  change Terminal e (b e) ∈ PathEdges f (b f)
  change Terminal e (b e) = Terminal f (b f) at h
  rw [h]
  exact terminal_mem f (b f)

private lemma bad_extend_path {n : ℕ} (x : Fin n → Bool) (e : ColoredEdge n) (b : Bool) :
    Bad (PathEdges e b) (Extend x) =
      if xor (x e.1) (x e.2.1) = b then ∅ else {Terminal e b} := by
  rw [path_normal]
  cases b <;> cases hx : x e.1 <;> cases hy : x e.2.1 <;>
    simp [Bad, filter_insert, filter_singleton, Terminal, hx, hy, extend_original, extend_A, extend_P]

private lemma bad_extend_gadget {n : ℕ} (F : Finset (ColoredEdge n))
    (b : ColoredEdge n → Bool) (x : Fin n → Bool) :
    Bad (Gadget F b) (Extend x) =
      (F.filter fun e => xor (x e.1) (x e.2.1) ≠ b e).image (fun e => Terminal e (b e)) := by
  ext a
  rw [show a ∈ Bad (Gadget F b) (Extend x) ↔
    a ∈ Gadget F b ∧ Extend x a.1 = Extend x a.2 from mem_filter]
  simp only [Gadget, mem_biUnion, mem_image, mem_filter]
  constructor
  · rintro ⟨⟨e,he,ha⟩,hbad⟩
    have hh : a ∈ Bad (PathEdges e (b e)) (Extend x) := mem_filter.mpr ⟨ha,hbad⟩
    rw [bad_extend_path] at hh
    split_ifs at hh with hs
    · simp at hh
    · exact ⟨e,⟨he,hs⟩,(mem_singleton.mp hh).symm⟩
  · rintro ⟨e,⟨he,hs⟩,rfl⟩
    have hh : Terminal e (b e) ∈ Bad (PathEdges e (b e)) (Extend x) := by
      rw [bad_extend_path, if_neg hs]
      exact mem_singleton_self _
    exact ⟨⟨e,he,(mem_filter.mp hh).1⟩,(mem_filter.mp hh).2⟩

private lemma bad_extend_card {n : ℕ} (F : Finset (ColoredEdge n)) (hF : Consistent F)
    (b : ColoredEdge n → Bool) (x : Fin n → Bool) :
    (Bad (Gadget F b) (Extend x)).card =
      (F.filter fun e => xor (x e.1) (x e.2.1) ≠ b e).card := by
  rw [bad_extend_gadget]
  apply card_image_of_injOn
  exact (terminal_inj F hF b).mono (filter_subset _ _)

private lemma bad_gadget_lower {n : ℕ} (F : Finset (ColoredEdge n)) (hF : Consistent F)
    (b : ColoredEdge n → Bool) (y : Fin (7*n) → Bool) :
    (F.filter fun e => xor (y (Original e.1)) (y (Original e.2.1)) ≠ b e).card ≤
      (Bad (Gadget F b) y).card := by
  let V := F.filter fun e => xor (y (Original e.1)) (y (Original e.2.1)) ≠ b e
  have hex : ∀ e ∈ V, ∃ a, a ∈ PathEdges e (b e) ∧ y a.1 = y a.2 := by
    intro e he
    have hv := (mem_filter.mp he).2
    by_contra hn
    push Not at hn
    exact hv (path_parity y e (b e) hn)
  let f : V → Bad (Gadget F b) y := fun e =>
    ⟨(hex e.val e.property).choose, mem_filter.mpr
      ⟨mem_biUnion.mpr ⟨e.val,(mem_filter.mp e.property).1,(hex e.val e.property).choose_spec.1⟩,
        (hex e.val e.property).choose_spec.2⟩⟩
  apply card_le_card_of_injective (f := f)
  intro e g hh
  apply Subtype.ext
  by_contra hne
  have hd := Finset.disjoint_left.mp (path_disjoint F hF b
    (mem_filter.mp e.property).1 (mem_filter.mp g.property).1 hne)
  have heq : (hex e.val e.property).choose = (hex g.val g.property).choose :=
    congrArg Subtype.val hh
  apply hd (hex e.val e.property).choose_spec.1
  rw [heq]
  exact (hex g.val g.property).choose_spec.1

private lemma gadget_distance {n : ℕ} (F : Finset (ColoredEdge n)) (hF : Consistent F)
    (b : ColoredEdge n → Bool) :
    DeletionDistance (Gadget F b) = Frustration F b := by
  rw [deletion_eq_bad]
  have hBn : Set.Nonempty {k | ∃ y : Fin (7*n) → Bool, k = (Bad (Gadget F b) y).card} :=
    ⟨_,fun _ => false,rfl⟩
  have hFn : Set.Nonempty {k | ∃ x : Fin n → Bool,
      k = (F.filter fun e => xor (x e.1) (x e.2.1) ≠ b e).card} :=
    ⟨_,fun _ => false,rfl⟩
  apply le_antisymm
  · obtain ⟨x,hx⟩ := Nat.sInf_mem hFn
    change _ ≤ sInf _
    rw [hx]
    rw [← bad_extend_card F hF b x]
    exact Nat.sInf_le ⟨Extend x,rfl⟩
  · obtain ⟨y,hy⟩ := Nat.sInf_mem hBn
    rw [hy]
    apply le_trans (Nat.sInf_le (s := {k | ∃ x : Fin n → Bool,
      k = (F.filter fun e => xor (x e.1) (x e.2.1) ≠ b e).card})
      (show (F.filter fun e => xor (y (Original e.1)) (y (Original e.2.1)) ≠ b e).card ∈ _ from
        ⟨fun u => y (Original u),rfl⟩))
    exact bad_gadget_lower F hF b y

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

private lemma original_degree {n : ℕ} (F : Finset (ColoredEdge n)) (hF : Consistent F)
    (b : ColoredEdge n → Bool) (u : Fin n) :
    (Neighbors (Gadget F b) (Original u)).card ≤ 3 := by
  let I := F.filter fun e => Incident e u
  have hj : Set.InjOn (fun e : ColoredEdge n => e.2.2) (I : Set _) := by
    intro e he f hf hh
    exact hF.2 e (mem_filter.mp he).1 f (mem_filter.mp hf).1 hh
      ⟨u,(mem_filter.mp he).2,(mem_filter.mp hf).2⟩
  have hcard : I.card ≤ 3 := by
    calc I.card = (I.image fun e => e.2.2).card := (card_image_of_injOn hj).symm
         _ ≤ (univ : Finset (Fin 3)).card := card_le_card (subset_univ _)
         _ = 3 := by simp
  apply le_trans (card_le_card (t := I.image fun e => FirstNbr e u (b e)) ?_)
    ((card_image_le).trans hcard)
  intro v hv
  have hv' : (Original u,v) ∈ Gadget F b ∨ (v,Original u) ∈ Gadget F b := (mem_filter.mp hv).2
  have hex : ∃ e ∈ F, (Original u,v) ∈ PathEdges e (b e) ∨ (v,Original u) ∈ PathEdges e (b e) := by
    rcases hv' with hv' | hv'
    · obtain ⟨e,he,ha⟩ := mem_biUnion.mp hv'
      exact ⟨e,he,Or.inl ha⟩
    · obtain ⟨e,he,ha⟩ := mem_biUnion.mp hv'
      exact ⟨e,he,Or.inr ha⟩
  obtain ⟨e,he,ha⟩ := hex
  obtain ⟨hi,hv⟩ := original_neighbor_path e (b e) (hF.1 e he) u v ha
  exact mem_image.mpr ⟨e,mem_filter.mpr ⟨he,hi⟩,hv.symm⟩

private lemma three_path_degree {m : ℕ} (a b c d w : Fin m) (hbc : b ≠ c) :
    (Neighbors {(a,b),(b,c),(d,c)} w).card ≤ 2 := by
  have hpair : ∀ a b : Fin m, ({a,b} : Finset (Fin m)).card ≤ 2 := by
    intro a b
    exact (card_insert_le _ _).trans (by simp)
  by_cases hw : w = b
  · subst w
    apply le_trans (card_le_card (t := {a,c}) ?_) (hpair _ _)
    intro v hv
    simp only [Neighbors, mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
      Prod.mk.injEq] at hv
    simp only [mem_insert, mem_singleton]
    aesop
  · by_cases hw' : w = c
    · subst w
      apply le_trans (card_le_card (t := {b,d}) ?_) (hpair _ _)
      intro v hv
      simp only [Neighbors, mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
        Prod.mk.injEq] at hv
      simp only [mem_insert, mem_singleton]
      aesop
    · apply le_trans (card_le_card (t := {b,c}) ?_) (hpair _ _)
      intro v hv
      simp only [Neighbors, mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
        Prod.mk.injEq] at hv
      simp only [mem_insert, mem_singleton]
      aesop

private lemma two_path_degree {m : ℕ} (a b c w : Fin m) :
    (Neighbors {(a,b),(c,b)} w).card ≤ 2 := by
  have hpair : ({a,c} : Finset (Fin m)).card ≤ 2 := (card_insert_le _ _).trans (by simp)
  by_cases hw : w = b
  · subst w
    apply le_trans (card_le_card (t := {a,c}) ?_) hpair
    intro v hv
    simp only [Neighbors, mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
      Prod.mk.injEq] at hv
    simp only [mem_insert, mem_singleton]
    aesop
  · apply le_trans (card_le_card (t := {b}) ?_) (by simp)
    intro v hv
    simp only [Neighbors, mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
      Prod.mk.injEq] at hv
    simp only [mem_singleton]
    aesop

private lemma path_degree {n : ℕ} (e : ColoredEdge n) (b : Bool) (v : Fin (7*n)) :
    (Neighbors (PathEdges e b) v).card ≤ 2 := by
  rw [path_normal]
  cases b
  · exact two_path_degree _ _ _ _
  · exact three_path_degree _ _ _ _ _ (ne_of_lt (A_lt_P _ _))

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

private lemma auxiliary_degree {n : ℕ} (F : Finset (ColoredEdge n)) (hF : Consistent F)
    (b : ColoredEdge n → Bool) (v : Fin (7*n)) (hv : ∀ u : Fin n, v ≠ Original u) :
    (Neighbors (Gadget F b) v).card ≤ 2 := by
  by_cases hn : (Neighbors (Gadget F b) v).Nonempty
  · obtain ⟨z,hz⟩ := hn
    obtain ⟨e,he,hepath⟩ := neighbor_witness F b v z hz
    apply le_trans (card_le_card (t := Neighbors (PathEdges e (b e)) v) ?_) (path_degree e (b e) v)
    intro z' hz'
    obtain ⟨f,hf,hfpath⟩ := neighbor_witness F b v z' hz'
    have ho := (auxiliary_owner e (b e) v z hv hepath).symm.trans
      (auxiliary_owner f (b f) v z' hv hfpath)
    have hu : e.1 = f.1 := Fin.ext (congrArg Prod.fst ho)
    have hj : e.2.2 = f.2.2 := Fin.ext (congrArg Prod.snd ho)
    have hef := hF.2 e he f hf hj ⟨e.1,Or.inl rfl,Or.inl hu.symm⟩
    subst f
    exact mem_filter.mpr ⟨mem_univ _,hfpath⟩
  · rw [not_nonempty_iff_eq_empty.mp hn]
    simp

private lemma gadget_degree {n : ℕ} (F : Finset (ColoredEdge n)) (hF : Consistent F)
    (b : ColoredEdge n → Bool) : DegreeBound 3 (Gadget F b) := by
  intro v
  by_cases hv : ∃ u : Fin n, v = Original u
  · obtain ⟨u,rfl⟩ := hv
    exact original_degree F hF b u
  · push Not at hv
    exact (auxiliary_degree F hF b v hv).trans (by omega)

end
end QuantumBipartiteTesting.Bipartiteness

open QuantumBipartiteTesting.Bipartiteness

theorem solution (n : ℕ) (F : Finset (ColoredEdge n)) (hF : Consistent F)
    (b : ColoredEdge n → Bool) :
    IsGraph (Gadget F b) ∧ DegreeBound 3 (Gadget F b) ∧
    (Bipartite (Gadget F b) ↔ Balanced F b) ∧
    DeletionDistance (Gadget F b) = Frustration F b ∧
    EditDistance (Gadget F b) = Frustration F b := by
  exact ⟨gadget_graph F b, gadget_degree F hF b, gadget_bipartite F b,
    gadget_distance F hF b, (edit_eq_deletion _ (gadget_graph F b)).trans (gadget_distance F hF b)⟩
