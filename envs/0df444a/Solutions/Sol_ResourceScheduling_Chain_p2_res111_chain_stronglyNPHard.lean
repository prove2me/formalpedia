-- Prove2me | solution 1 for ResourceScheduling.Chain.p2_res111_chain_stronglyNPHard
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-06T22:50:26.779682+00:00
-- url     : https://prove2.me/submissions/27e1527a-2a3c-4330-a211-355695f2ad80

import Mathlib
import Definitions.Def_ResourceScheduling_Chain_Complexity
import Definitions.Def_ResourceScheduling_Chain_ThreePartition
import Definitions.Def_ResourceScheduling_Chain_Problems
import Definitions.Def_ResourceScheduling_Chain_Constructions
import Definitions.Def_ResourceScheduling_Chain_Model
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_CookPvsNP_comp_machine
import Definitions.Def_CookPvsNP_CompFrames
import Definitions.Def_CookPvsNP_CompSecondFrame
import Definitions.Def_CookPvsNP_CompConversion
import Definitions.Def_CookPvsNP_CompCleanup
import Definitions.Def_CookPvsNP_StackModel
import Definitions.Def_CookPvsNP_StackCompiler
import Definitions.Def_CookPvsNP_StackRepresentation
import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_CookPvsNP_StackMacros
import Definitions.Def_CookPvsNP_StackLookup
import Definitions.Def_CookPvsNP_StackMapTransfer
import Definitions.Def_CookPvsNP_StackRepeat
import Definitions.Def_CookPvsNP_StackSpecification
import Definitions.Def_CookPvsNP_StackCompare
import Definitions.Def_ResourceScheduling_Graph_RAMCode
import Definitions.Def_ResourceScheduling_Graph_Complexity
import Definitions.Def_ResourceScheduling_Graph_Codec
import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_ResourceScheduling_Graph_GraphPartition
import Definitions.Def_ResourceScheduling_Graph_Decoder
import Definitions.Def_ResourceScheduling_Graph_Model
import Definitions.Def_ResourceScheduling_Graph_ResDot11
import Definitions.Def_ResourceScheduling_Graph_Construction
import Definitions.Def_ResourceScheduling_Graph_WordReduction
import Definitions.Def_ResourceScheduling_Graph_WordProgram
import Definitions.Def_ResourceScheduling_Graph_RAM
import Definitions.Def_ResourceScheduling_Graph_StackEmit
import Definitions.Def_ResourceScheduling_Graph_RAMOps
import Definitions.Def_ResourceScheduling_Graph_RAMArithmetic
import Definitions.Def_ResourceScheduling_Graph_StackPrefix
import Definitions.Def_ResourceScheduling_Graph_RAMParse
import Definitions.Def_ResourceScheduling_Graph_RAMBudget
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
import Definitions.Def_ResourceScheduling_Graph_RAMFields

set_option autoImplicit false

/- Complete checked body: AttributedForward -/
section

-- Prove2me | solution 1 for ResourceScheduling.Chain.chainSchedule_of_threePartition
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:22:06.070258+00:00
-- url     : https://prove2.me/submissions/845ded84-34e8-4cfb-b055-4910b2d88930


namespace ResourceScheduling.Chain

open ThreePartition

theorem aux_cs_flatten_getElem? {α : Type*} :
    ∀ (Ls : List (List α)) (k c : ℕ) (l : List α), Ls[k]? = some l → c < l.length →
      Ls.flatten[((Ls.take k).map List.length).sum + c]? = l[c]?
  | [], k, c, l, h, _ => by simp at h
  | l0 :: rest, 0, c, l, h, hc => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [List.getElem?_append_left hc]
  | l0 :: rest, k + 1, c, l, h, hc => by
      simp only [List.getElem?_cons_succ] at h
      have ih := aux_cs_flatten_getElem? rest k c l h hc
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatten_cons]
      rw [List.getElem?_append_right (by omega)]
      rw [show l0.length + ((rest.take k).map List.length).sum + c - l0.length
          = ((rest.take k).map List.length).sum + c by omega]
      exact ih

theorem aux_cs_mem_chainArcsFrom :
    ∀ (ls : List ℕ) (off x y : ℕ), (x, y) ∈ chainArcsFrom ls off →
      ∃ k len c, ls[k]? = some len ∧ c + 1 < len ∧ x = off + (ls.take k).sum + c ∧ y = x + 1
  | [], off, x, y, h => by simp [chainArcsFrom] at h
  | len :: rest, off, x, y, h => by
      simp only [chainArcsFrom, List.mem_append, List.mem_map, List.mem_range,
        Prod.mk.injEq] at h
      rcases h with ⟨c, hc, rfl, rfl⟩ | h
      · exact ⟨0, len, c, by simp, by omega, by simp, rfl⟩
      · obtain ⟨k, len', c, h1, h2, h3, h4⟩ := aux_cs_mem_chainArcsFrom rest (off + len) x y h
        refine ⟨k + 1, len', c, by simpa using h1, h2, ?_, h4⟩
        simp only [List.take_succ_cons, List.sum_cons]
        omega

abbrev aux_cs_Desc (P : ThreePartition) := ℕ ⊕ (Fin (3 * P.t) × ℕ)

def aux_cs_D (P : ThreePartition) : List (aux_cs_Desc P) :=
  (List.range (2 * P.t * P.b)).map Sum.inl ++
    (List.ofFn fun j => (List.range (2 * P.a j)).map
      fun c => (Sum.inr (j, c) : aux_cs_Desc P)).flatten

def aux_cs_req (P : ThreePartition) : aux_cs_Desc P → ℕ
  | Sum.inl p => if p / P.b % 2 = 0 then 1 else 0
  | Sum.inr (j, c) => if c < P.a j then 0 else 1

def aux_cs_e (P : ThreePartition) (s : Fin (3 * P.t) → Fin P.t) (j : Fin (3 * P.t)) : ℕ :=
  ∑ j' ∈ Finset.univ.filter (fun j' => j' < j ∧ s j' = s j), P.a j'

def aux_cs_start (P : ThreePartition) (s : Fin (3 * P.t) → Fin P.t) : aux_cs_Desc P → ℕ
  | Sum.inl p => p
  | Sum.inr (j, c) =>
      2 * (s j : ℕ) * P.b + aux_cs_e P s j + (if c < P.a j then c else P.b + (c - P.a j))

def aux_cs_mach (P : ThreePartition) : aux_cs_Desc P → Fin 2
  | Sum.inl _ => 0
  | Sum.inr _ => 1

def aux_cs_ok (P : ThreePartition) : aux_cs_Desc P → Prop
  | Sum.inl p => p < 2 * P.t * P.b
  | Sum.inr (j, c) => c < 2 * P.a j

theorem aux_cs_ok_of_mem (P : ThreePartition) (d : aux_cs_Desc P) (h : d ∈ aux_cs_D P) :
    aux_cs_ok P d := by
  simp only [aux_cs_D, List.mem_append, List.mem_map, List.mem_range, List.mem_flatten,
    List.mem_ofFn] at h
  rcases h with ⟨p, hp, rfl⟩ | ⟨l, ⟨j, rfl⟩, hl⟩
  · exact hp
  · simp only [List.mem_map, List.mem_range] at hl
    obtain ⟨c, hc, rfl⟩ := hl
    exact hc

theorem aux_cs_nodup (P : ThreePartition) : (aux_cs_D P).Nodup := by
  unfold aux_cs_D
  rw [List.nodup_append]
  refine ⟨List.nodup_range.map Sum.inl_injective, ?_, ?_⟩
  · rw [List.nodup_flatten]
    refine ⟨?_, ?_⟩
    · intro l hl
      rw [List.mem_ofFn] at hl
      obtain ⟨j, rfl⟩ := hl
      exact List.nodup_range.map (fun c c' h => by simpa using h)
    · rw [List.pairwise_ofFn]
      intro i j hij
      rw [List.disjoint_left]
      intro x hx hx'
      simp only [List.mem_map, List.mem_range] at hx hx'
      obtain ⟨c, _, rfl⟩ := hx
      obtain ⟨c', _, h⟩ := hx'
      simp only [Sum.inr.injEq, Prod.mk.injEq] at h
      exact absurd h.1 (ne_of_gt hij)
  · intro a ha b hb hab
    simp only [List.mem_map, List.mem_range, List.mem_flatten, List.mem_ofFn] at ha hb
    obtain ⟨p, _, rfl⟩ := ha
    obtain ⟨l, ⟨j, rfl⟩, hl⟩ := hb
    simp only [List.mem_map, List.mem_range] at hl
    obtain ⟨c, _, rfl⟩ := hl
    exact Sum.inl_ne_inr hab

theorem aux_cs_range_blocks (b : ℕ) (hb : 0 < b) (f : ℕ → ℕ) :
    ∀ m : ℕ, (List.range (m * b)).map (fun p => f (p / b)) =
      (List.range m).flatMap (fun k => List.replicate b (f k))
  | 0 => by simp
  | m + 1 => by
      rw [show (m + 1) * b = m * b + b by ring, List.range_add, List.map_append,
        aux_cs_range_blocks b hb f m, List.range_succ, List.flatMap_append]
      congr 1
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map]
      rw [List.eq_replicate_iff]
      refine ⟨by simp, ?_⟩
      intro x hx
      simp only [List.mem_map, List.mem_range, Function.comp] at hx
      obtain ⟨c, hc, rfl⟩ := hx
      congr 1
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hc, zero_add]

theorem aux_cs_map_req (P : ThreePartition) (hb : 0 < P.b) :
    (aux_cs_D P).map (aux_cs_req P) = P.chainReqs := by
  unfold aux_cs_D chainReqs chainLReqs chainKReqs
  rw [List.map_append]
  congr 1
  · rw [List.map_map]
    rw [← aux_cs_range_blocks P.b hb (fun k => if k % 2 = 0 then 1 else 0) (2 * P.t)]
    rfl
  · rw [List.map_flatten, List.map_ofFn]
    congr 2
    funext j
    simp only [Function.comp, List.map_map]
    rw [two_mul, List.range_add, List.map_append]
    congr 1
    · rw [List.eq_replicate_iff]
      refine ⟨by simp, ?_⟩
      intro x hx
      simp only [List.mem_map, List.mem_range, Function.comp] at hx
      obtain ⟨c, hc, rfl⟩ := hx
      simp [aux_cs_req, hc]
    · rw [List.eq_replicate_iff]
      refine ⟨by simp, ?_⟩
      intro x hx
      simp only [List.map_map, List.mem_map, List.mem_range, Function.comp] at hx
      obtain ⟨c, hc, rfl⟩ := hx
      simp [aux_cs_req]

theorem aux_cs_length (P : ThreePartition) :
    (aux_cs_D P).length = 2 * P.t * P.b + ∑ j, 2 * P.a j := by
  simp [aux_cs_D, List.length_flatten, List.map_ofFn, Function.comp, List.sum_ofFn]

theorem aux_cs_e_add_le (P : ThreePartition) (s : Fin (3 * P.t) → Fin P.t)
    (hs : P.IsSolution s) (j : Fin (3 * P.t)) : aux_cs_e P s j + P.a j ≤ P.b := by
  have hsub : insert j (Finset.univ.filter (fun j' => j' < j ∧ s j' = s j)) ⊆
      Finset.univ.filter (fun j' => s j' = s j) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with rfl | ⟨_, h⟩
    · rfl
    · exact h
  have hnot : j ∉ Finset.univ.filter (fun j' => j' < j ∧ s j' = s j) := by simp
  calc aux_cs_e P s j + P.a j
      = ∑ j' ∈ insert j (Finset.univ.filter (fun j' => j' < j ∧ s j' = s j)), P.a j' := by
        rw [Finset.sum_insert hnot, add_comm]; rfl
    _ ≤ ∑ j' ∈ Finset.univ.filter (fun j' => s j' = s j), P.a j' :=
        Finset.sum_le_sum_of_subset hsub
    _ = P.b := (hs (s j)).2

theorem aux_cs_e_lt (P : ThreePartition) (s : Fin (3 * P.t) → Fin P.t)
    (j j' : Fin (3 * P.t)) (hjj : j < j') (hsj : s j = s j') :
    aux_cs_e P s j + P.a j ≤ aux_cs_e P s j' := by
  have hsub : insert j (Finset.univ.filter (fun j'' => j'' < j ∧ s j'' = s j)) ⊆
      Finset.univ.filter (fun j'' => j'' < j' ∧ s j'' = s j') := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with rfl | ⟨h1, h2⟩
    · exact ⟨hjj, hsj⟩
    · exact ⟨lt_trans h1 hjj, h2.trans hsj⟩
  have hnot : j ∉ Finset.univ.filter (fun j'' => j'' < j ∧ s j'' = s j) := by simp
  calc aux_cs_e P s j + P.a j
      = ∑ j'' ∈ insert j (Finset.univ.filter (fun j'' => j'' < j ∧ s j'' = s j)), P.a j'' := by
        rw [Finset.sum_insert hnot, add_comm]; rfl
    _ ≤ ∑ j'' ∈ Finset.univ.filter (fun j'' => j'' < j' ∧ s j'' = s j'), P.a j'' :=
        Finset.sum_le_sum_of_subset hsub
    _ = aux_cs_e P s j' := rfl

theorem aux_cs_same_part (P : ThreePartition) (s : Fin (3 * P.t) → Fin P.t)
    (j j' : Fin (3 * P.t)) (hsj : s j = s j') (u u' : ℕ) (hu : u < P.a j) (hu' : u' < P.a j')
    (h : aux_cs_e P s j + u = aux_cs_e P s j' + u') : j = j' := by
  rcases lt_trichotomy j j' with hlt | heq | hgt
  · have := aux_cs_e_lt P s j j' hlt hsj
    omega
  · exact heq
  · have := aux_cs_e_lt P s j' j hgt hsj.symm
    omega

theorem aux_cs_off_lt (P : ThreePartition) (s : Fin (3 * P.t) → Fin P.t)
    (hs : P.IsSolution s) (j : Fin (3 * P.t)) (c : ℕ) (hc : c < 2 * P.a j) :
    aux_cs_e P s j + (if c < P.a j then c else P.b + (c - P.a j)) < 2 * P.b := by
  have := aux_cs_e_add_le P s hs j
  split_ifs <;> omega

theorem aux_cs_div2b (s s' b x x' : ℕ) (h : 2 * s * b + x = 2 * s' * b + x')
    (hx : x < 2 * b) (hx' : x' < 2 * b) : s = s' ∧ x = x' := by
  have hss : s = s' := by
    rcases lt_trichotomy s s' with hlt | heq | hgt
    · exfalso
      have : 2 * (s + 1) * b ≤ 2 * s' * b := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    · exact heq
    · exfalso
      have : 2 * (s' + 1) * b ≤ 2 * s * b := Nat.mul_le_mul_right _ (by omega)
      nlinarith
  subst hss
  exact ⟨rfl, by omega⟩

theorem aux_cs_start_lt (P : ThreePartition) (s : Fin (3 * P.t) → Fin P.t)
    (hs : P.IsSolution s) (d : aux_cs_Desc P) (hd : aux_cs_ok P d) :
    aux_cs_start P s d < 2 * P.t * P.b := by
  rcases d with p | ⟨j, c⟩
  · exact hd
  · simp only [aux_cs_ok] at hd
    simp only [aux_cs_start]
    have h1 := aux_cs_off_lt P s hs j c hd
    have h2 : (s j : ℕ) + 1 ≤ P.t := (s j).isLt
    have h3 : 2 * ((s j : ℕ) + 1) * P.b ≤ 2 * P.t * P.b := Nat.mul_le_mul_right _ (by omega)
    nlinarith

theorem aux_cs_inj (P : ThreePartition) (s : Fin (3 * P.t) → Fin P.t)
    (hs : P.IsSolution s) (d d' : aux_cs_Desc P) (hd : aux_cs_ok P d) (hd' : aux_cs_ok P d')
    (hm : aux_cs_mach P d = aux_cs_mach P d')
    (hst : aux_cs_start P s d = aux_cs_start P s d') : d = d' := by
  rcases d with p | ⟨j, c⟩ <;> rcases d' with p' | ⟨j', c'⟩
  · simp only [aux_cs_start] at hst
    rw [hst]
  · simp [aux_cs_mach] at hm
  · simp [aux_cs_mach] at hm
  · simp only [aux_cs_ok] at hd hd'
    simp only [aux_cs_start] at hst
    have e1 := aux_cs_e_add_le P s hs j
    have e2 := aux_cs_e_add_le P s hs j'
    have hst' : 2 * (s j : ℕ) * P.b + (aux_cs_e P s j + (if c < P.a j then c else P.b + (c - P.a j)))
        = 2 * (s j' : ℕ) * P.b +
          (aux_cs_e P s j' + (if c' < P.a j' then c' else P.b + (c' - P.a j'))) := by
      rw [← add_assoc, ← add_assoc]; exact hst
    obtain ⟨h1, h2⟩ := aux_cs_div2b _ _ _ _ _ hst' (aux_cs_off_lt P s hs j c hd)
      (aux_cs_off_lt P s hs j' c' hd')
    have hsj : s j = s j' := Fin.ext h1
    split_ifs at h2 with hc hc'
    · have := aux_cs_same_part P s j j' hsj c c' hc hc' h2
      subst this
      simp only [Sum.inr.injEq, Prod.mk.injEq, true_and]
      omega
    · omega
    · omega
    · have := aux_cs_same_part P s j j' hsj (c - P.a j) (c' - P.a j') (by omega) (by omega)
        (by omega)
      subst this
      simp only [Sum.inr.injEq, Prod.mk.injEq, true_and]
      omega

theorem aux_cs_quot (b s e u : ℕ) (hb : 0 < b) (h : e + u < b) :
    (2 * s * b + e + (b + u)) / b = 2 * s + 1 := by
  rw [show 2 * s * b + e + (b + u) = (e + u) + (2 * s + 1) * b by ring,
    Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt h, zero_add]

theorem aux_cs_clash_aux (P : ThreePartition) (s : Fin (3 * P.t) → Fin P.t)
    (hs : P.IsSolution s) (hb : 0 < P.b) (p : ℕ) (j : Fin (3 * P.t)) (c : ℕ)
    (hc : c < 2 * P.a j)
    (hst : p = aux_cs_start P s (Sum.inr (j, c))) (hr : aux_cs_req P (Sum.inl p) ≠ 0)
    (hr' : aux_cs_req P (Sum.inr (j, c)) ≠ 0) : False := by
  simp only [aux_cs_req] at hr hr'
  simp only [aux_cs_start] at hst
  have e1 := aux_cs_e_add_le P s hs j
  split_ifs at hr' with hc'
  · exact hr' rfl
  · rw [if_neg hc'] at hst
    apply hr
    rw [if_neg]
    rw [hst, aux_cs_quot _ _ _ _ hb (by omega)]
    omega

theorem aux_cs_clash (P : ThreePartition) (s : Fin (3 * P.t) → Fin P.t)
    (hs : P.IsSolution s) (hb : 0 < P.b) (d d' : aux_cs_Desc P) (hd : aux_cs_ok P d)
    (hd' : aux_cs_ok P d')
    (hst : aux_cs_start P s d = aux_cs_start P s d') (hr : aux_cs_req P d ≠ 0)
    (hr' : aux_cs_req P d' ≠ 0) : d = d' := by
  rcases d with p | ⟨j, c⟩ <;> rcases d' with p' | ⟨j', c'⟩
  · simp only [aux_cs_start] at hst
    rw [hst]
  · exact (aux_cs_clash_aux P s hs hb p j' c' hd' hst hr hr').elim
  · exact (aux_cs_clash_aux P s hs hb p' j c hd hst.symm hr' hr).elim
  · exact aux_cs_inj P s hs _ _ hd hd' (by simp [aux_cs_mach]) hst

theorem aux_cs_sum_le_one {ι : Type*} (S : Finset ι) (f : ι → ℕ) (hf : ∀ i, f i ≤ 1)
    (h : ∀ p ∈ S, ∀ q ∈ S, f p ≠ 0 → f q ≠ 0 → p = q) : ∑ i ∈ S, f i ≤ 1 := by
  rw [← Finset.sum_filter_ne_zero]
  have hcard : (S.filter (fun i => f i ≠ 0)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    exact h a ha.1 b hb.1 ha.2 hb.2
  calc ∑ i ∈ S.filter (fun i => f i ≠ 0), f i ≤ ∑ i ∈ S.filter (fun i => f i ≠ 0), 1 :=
        Finset.sum_le_sum (fun i _ => hf i)
    _ = (S.filter (fun i => f i ≠ 0)).card := by simp
    _ ≤ 1 := hcard

theorem aux_cs_req_le (P : ThreePartition) (d : aux_cs_Desc P) : aux_cs_req P d ≤ 1 := by
  rcases d with p | ⟨j, c⟩ <;> simp only [aux_cs_req] <;> split_ifs <;> omega

theorem aux_cs_arcK (P : ThreePartition) (s : Fin (3 * P.t) → Fin P.t)
    (hs : P.IsSolution s) (j : Fin (3 * P.t)) (c : ℕ) (_hc : c + 1 < 2 * P.a j) :
    aux_cs_start P s (Sum.inr (j, c)) + 1 ≤ aux_cs_start P s (Sum.inr (j, c + 1)) := by
  have e1 := aux_cs_e_add_le P s hs j
  simp only [aux_cs_start]
  split_ifs <;> omega

theorem aux_cs_D_L (P : ThreePartition) (c : ℕ) (hc : c < 2 * P.t * P.b) :
    (aux_cs_D P)[c]? = some (Sum.inl c) := by
  unfold aux_cs_D
  rw [List.getElem?_append_left (by simpa using hc)]
  simp [hc]

theorem aux_cs_D_K (P : ThreePartition) (k : ℕ) (hk : k < 3 * P.t) (c : ℕ)
    (hc : c < 2 * P.a ⟨k, hk⟩) :
    (aux_cs_D P)[2 * P.t * P.b + ((List.ofFn fun j => 2 * P.a j).take k).sum + c]? =
      some (Sum.inr (⟨k, hk⟩, c)) := by
  unfold aux_cs_D
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_map, List.length_range]
  rw [show 2 * P.t * P.b + ((List.ofFn fun j => 2 * P.a j).take k).sum + c - 2 * P.t * P.b
      = ((List.ofFn fun j => 2 * P.a j).take k).sum + c by omega]
  have hlen : (List.ofFn fun j => (List.range (2 * P.a j)).map
      fun c => (Sum.inr (j, c) : aux_cs_Desc P)).map List.length =
      List.ofFn fun j => 2 * P.a j := by
    rw [List.map_ofFn]
    congr 1
    funext i
    simp
  have key := aux_cs_flatten_getElem? (List.ofFn fun j => (List.range (2 * P.a j)).map
      fun c => (Sum.inr (j, c) : aux_cs_Desc P)) k c
      ((List.range (2 * P.a ⟨k, hk⟩)).map fun c => (Sum.inr (⟨k, hk⟩, c) : aux_cs_Desc P))
      (by simp [hk]) (by simpa using hc)
  rw [List.map_take, hlen] at key
  rw [key]
  simp [hc]

end ResourceScheduling.Chain

open ResourceScheduling.Chain

theorem checked_chainSchedule_of_threePartition (P : ThreePartition) (hP : P.Valid)
    (hS : P.HasSolution) :
    ∃ σ : Schedule P.chainInstance, σ.Feasible ∧ σ.cmax = ((2 * P.t * P.b : ℕ) : ℝ) := by
  obtain ⟨s, hs⟩ := hS
  obtain ⟨hb, hsum, ha⟩ := hP
  have hmap : (aux_cs_D P).map (aux_cs_req P) = P.chainReqs := aux_cs_map_req P hb
  have hn : P.chainInstance.n = (aux_cs_D P).length := by
    show P.chainReqs.length = _
    rw [← hmap, List.length_map]
  have hDlen : (aux_cs_D P).length = 4 * (P.t * P.b) := by
    rw [aux_cs_length, ← Finset.mul_sum, hsum]
    ring
  let dOf : Fin P.chainInstance.n → aux_cs_Desc P := fun p => (aux_cs_D P).getD p.val (Sum.inl 0)
  have hdOf : ∀ p : Fin P.chainInstance.n, (aux_cs_D P)[p.val]? = some (dOf p) := by
    intro p
    have hp : p.val < (aux_cs_D P).length := hn ▸ p.isLt
    rw [List.getElem?_eq_getElem hp]
    simp [dOf, List.getD, List.getElem?_eq_getElem hp]
  have hok : ∀ p, aux_cs_ok P (dOf p) := fun p =>
    aux_cs_ok_of_mem P _ (List.mem_of_getElem? (hdOf p))
  have hinj : ∀ p q : Fin P.chainInstance.n, dOf p = dOf q → p = q := by
    intro p q h
    have hp : p.val < (aux_cs_D P).length := hn ▸ p.isLt
    apply Fin.ext
    exact (List.getElem?_inj hp (aux_cs_nodup P)).1 ((hdOf p).trans ((congrArg some h).trans
      (hdOf q).symm))
  have hreq : ∀ (h : Fin P.chainInstance.l) (p : Fin P.chainInstance.n),
      P.chainInstance.r h p = aux_cs_req P (dOf p) := by
    intro h p
    show P.chainReqs[(p : ℕ)]'(by exact p.isLt) = _
    have h1 : P.chainReqs[p.val]? = some (aux_cs_req P (dOf p)) := by
      rw [← hmap, List.getElem?_map, hdOf p]
      rfl
    exact (List.getElem_eq_iff _).2 h1
  have harc : ∀ p q : Fin P.chainInstance.n, P.chainInstance.Arc p q →
      aux_cs_start P s (dOf p) + 1 ≤ aux_cs_start P s (dOf q) := by
    intro p q h
    have h' : (p, q) ∈ (chainArcsFrom P.chainLengths 0).filterMap
        (toFinArc P.chainReqs.length) := h
    obtain ⟨⟨x, y⟩, hmem, hfin⟩ := List.mem_filterMap.1 h'
    have hxy : x = p.val ∧ y = q.val := by
      unfold toFinArc at hfin
      split_ifs at hfin with hh
      obtain ⟨rfl, rfl⟩ := hfin
      exact ⟨rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := hxy
    obtain ⟨k, len, c, hk, hc, hx, hy⟩ := aux_cs_mem_chainArcsFrom _ _ _ _ hmem
    rcases k with _ | k
    · simp only [ThreePartition.chainLengths, List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      simp only [List.take_zero, List.sum_nil, add_zero, zero_add] at hx
      have hp := (hdOf p).symm.trans (hx ▸ aux_cs_D_L P c (by omega))
      have hq := (hdOf q).symm.trans (hy ▸ hx ▸ aux_cs_D_L P (c + 1) (by omega))
      simp only [Option.some.injEq] at hp hq
      rw [hp, hq]
      show (p : ℕ) + 1 ≤ (q : ℕ)
      omega
    · simp only [ThreePartition.chainLengths, List.getElem?_cons_succ, List.getElem?_ofFn] at hk
      split_ifs at hk with hjk
      simp only [Option.some.injEq] at hk
      subst hk
      simp only [ThreePartition.chainLengths, List.take_succ_cons, List.sum_cons, zero_add] at hx
      have hq' : (q : ℕ) = 2 * P.t * P.b + ((List.ofFn fun j => 2 * P.a j).take k).sum
          + (c + 1) := by
        rw [hy, hx]; ring
      have hp := hdOf p
      rw [hx, aux_cs_D_K P k hjk c (by omega)] at hp
      have hq := hdOf q
      rw [hq', aux_cs_D_K P k hjk (c + 1) hc] at hq
      simp only [Option.some.injEq] at hp hq
      rw [← hp, ← hq]
      exact aux_cs_arcK P s hs _ c hc
  refine ⟨⟨fun p => aux_cs_mach P (dOf p), fun p => (aux_cs_start P s (dOf p) : ℝ)⟩,
    ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro p
    exact Nat.cast_nonneg _
  · intro p q hpq hm
    simp only [Schedule.completion]
    have hne : dOf p ≠ dOf q := fun h => hpq (hinj p q h)
    have hst : aux_cs_start P s (dOf p) ≠ aux_cs_start P s (dOf q) := fun h =>
      hne (aux_cs_inj P s hs _ _ (hok p) (hok q) hm h)
    rcases Nat.lt_or_gt_of_ne hst with h | h
    · left
      exact_mod_cast Nat.succ_le_of_lt h
    · right
      exact_mod_cast Nat.succ_le_of_lt h
  · intro p q h
    simp only [Schedule.completion]
    induction h with
    | single hab => exact_mod_cast harc _ _ hab
    | tail _ hbc ih =>
      have := harc _ _ hbc
      have h2 : ((aux_cs_start P s (dOf _) + 1 : ℕ) : ℝ) ≤ (aux_cs_start P s (dOf _) : ℕ) :=
        Nat.cast_le.mpr this
      push_cast at h2
      linarith
  · intro t h
    show _ ≤ 1
    rw [Finset.sum_congr rfl (fun p _ => hreq h p)]
    refine aux_cs_sum_le_one _ _ (fun p => aux_cs_req_le P _) ?_
    intro p hp q hq hrp hrq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    obtain ⟨hp1, hp2⟩ := hp
    obtain ⟨hq1, hq2⟩ := hq
    have hp1' : (aux_cs_start P s (dOf p) : ℝ) ≤ t := hp1
    have hp2' : t < (aux_cs_start P s (dOf p) : ℝ) + 1 := hp2
    have hq1' : (aux_cs_start P s (dOf q) : ℝ) ≤ t := hq1
    have hq2' : t < (aux_cs_start P s (dOf q) : ℝ) + 1 := hq2
    have e : aux_cs_start P s (dOf p) = aux_cs_start P s (dOf q) := by
      have h1 : (aux_cs_start P s (dOf p) : ℝ) < aux_cs_start P s (dOf q) + 1 := by linarith
      have h2 : (aux_cs_start P s (dOf q) : ℝ) < aux_cs_start P s (dOf p) + 1 := by linarith
      have h1' : aux_cs_start P s (dOf p) < aux_cs_start P s (dOf q) + 1 := by exact_mod_cast h1
      have h2' : aux_cs_start P s (dOf q) < aux_cs_start P s (dOf p) + 1 := by exact_mod_cast h2
      omega
    exact hinj p q (aux_cs_clash P s hs hb _ _ (hok p) (hok q) e hrp hrq)
  · unfold Schedule.cmax
    split_ifs with hpos
    · apply le_antisymm
      · apply Finset.sup'_le
        intro p _
        show (aux_cs_start P s (dOf p) : ℝ) + 1 ≤ _
        have := aux_cs_start_lt P s hs _ (hok p)
        exact_mod_cast this
      · have htb : 0 < P.t * P.b := by
          have : 0 < (aux_cs_D P).length := hn ▸ hpos
          rw [hDlen] at this
          omega
        have hlt : 2 * P.t * P.b - 1 < P.chainInstance.n := by
          rw [hn, hDlen, mul_assoc]; omega
        refine Finset.le_sup'_of_le _ (Finset.mem_univ ⟨2 * P.t * P.b - 1, hlt⟩) (le_of_eq ?_)
        show _ = (aux_cs_start P s (dOf ⟨2 * P.t * P.b - 1, hlt⟩) : ℝ) + 1
        have hd := (hdOf ⟨2 * P.t * P.b - 1, hlt⟩).symm.trans
          (aux_cs_D_L P (2 * P.t * P.b - 1) (by rw [mul_assoc]; omega))
        simp only [Option.some.injEq] at hd
        rw [hd]
        simp only [aux_cs_start]
        have : 2 * P.t * P.b - 1 + 1 = 2 * P.t * P.b := by rw [mul_assoc]; omega
        exact_mod_cast this.symm
    · have h0 : (aux_cs_D P).length = 0 := by rw [← hn]; omega
      rw [hDlen] at h0
      have : 2 * P.t * P.b = 0 := by rw [mul_assoc]; omega
      simp [this]

end

/- Complete checked body: ChainJobs -/
section

set_option autoImplicit false

namespace ResourceScheduling.ChainProof

open ResourceScheduling.Chain ResourceScheduling.Chain.ThreePartition

abbrev ChainJob (P : ThreePartition) :=
  Fin (2 * P.t * P.b) ⊕ (Σ j : Fin (3 * P.t), Fin (2 * P.a j))

def jobPos (P : ThreePartition) : ChainJob P → ℕ
  | .inl c => c
  | .inr ⟨j, c⟩ => 2 * P.t * P.b + ((List.ofFn fun i => 2 * P.a i).take j.val).sum + c

def jobDesc (P : ThreePartition) : ChainJob P → aux_cs_Desc P
  | .inl c => .inl c
  | .inr ⟨j, c⟩ => .inr (j, c)

theorem job_get (P : ThreePartition) (d : ChainJob P) :
    (aux_cs_D P)[jobPos P d]? = some (jobDesc P d) := by
  cases d with
  | inl c => exact aux_cs_D_L P c c.isLt
  | inr d => exact aux_cs_D_K P d.1 d.1.isLt d.2 d.2.isLt

theorem chain_n_eq (P : ThreePartition) (hb : 0 < P.b) :
    P.chainInstance.n = (aux_cs_D P).length := by
  change P.chainReqs.length = _
  rw [← aux_cs_map_req P hb, List.length_map]

def jobFin (P : ThreePartition) (hb : 0 < P.b) (d : ChainJob P) : Fin P.chainInstance.n :=
  ⟨jobPos P d, by rw [chain_n_eq P hb]; exact (List.getElem?_eq_some_iff.mp (job_get P d)).choose⟩

theorem jobDesc_injective (P : ThreePartition) : Function.Injective (jobDesc P) := by
  intro d e h
  cases d with
  | inl c =>
    cases e with
    | inl c' => exact congrArg Sum.inl (Fin.ext (Sum.inl.inj h))
    | inr e => cases h
  | inr d =>
    cases e with
    | inl c => cases h
    | inr e =>
      obtain ⟨j, c⟩ := d
      obtain ⟨j', c'⟩ := e
      have hh : j = j' ∧ (c : ℕ) = (c' : ℕ) := Prod.mk.inj (Sum.inr.inj h)
      obtain ⟨rfl, he⟩ := hh
      exact congrArg Sum.inr (congrArg (Sigma.mk j) (Fin.ext he))

theorem jobFin_injective (P : ThreePartition) (hb : 0 < P.b) :
    Function.Injective (jobFin P hb) := by
  intro d e h
  apply jobDesc_injective P
  have hp : jobPos P d = jobPos P e := congrArg Fin.val h
  exact Option.some.inj ((job_get P d).symm.trans (hp ▸ job_get P e))

theorem card_chainJob (P : ThreePartition) (hb : 0 < P.b) :
    Fintype.card (ChainJob P) = Fintype.card (Fin P.chainInstance.n) := by
  rw [Fintype.card_fin, chain_n_eq P hb, aux_cs_length]
  simp only [ChainJob, Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma]

noncomputable def jobEquiv (P : ThreePartition) (hb : 0 < P.b) :
    ChainJob P ≃ Fin P.chainInstance.n :=
  Equiv.ofBijective (jobFin P hb) ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨jobFin_injective P hb, card_chainJob P hb⟩)

theorem job_req (P : ThreePartition) (hb : 0 < P.b) (d : ChainJob P)
    (h : Fin P.chainInstance.l) :
    P.chainInstance.r h (jobFin P hb d) = aux_cs_req P (jobDesc P d) := by
  change P.chainReqs[jobPos P d]'_ = _
  apply (List.getElem_eq_iff _).mpr
  rw [← aux_cs_map_req P hb, List.getElem?_map, job_get]
  rfl

theorem chainArc_mem : ∀ (ls : List ℕ) (off k len c : ℕ),
    ls[k]? = some len → c + 1 < len →
    (off + (ls.take k).sum + c, off + (ls.take k).sum + c + 1) ∈ chainArcsFrom ls off
  | [], off, k, len, c, hk, _ => by simp at hk
  | a :: ls, off, 0, len, c, hk, hc => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst len
      apply List.mem_append_left
      apply List.mem_map.mpr
      exact ⟨c, by simp; omega, by simp⟩
  | a :: ls, off, k + 1, len, c, hk, hc => by
      simp only [List.getElem?_cons_succ] at hk
      have ih := chainArc_mem ls (off + a) k len c hk hc
      apply List.mem_append_right
      simpa only [List.take_succ_cons, List.sum_cons, Nat.add_assoc] using ih

theorem chain_arc_of_raw (P : ThreePartition) (j k : Fin P.chainInstance.n)
    (h : ((j : ℕ), (k : ℕ)) ∈ chainArcsFrom P.chainLengths 0) :
    P.chainInstance.Arc j k := by
  apply List.mem_filterMap.mpr
  refine ⟨((j : ℕ), (k : ℕ)), h, ?_⟩
  unfold toFinArc
  rw [dif_pos (show j.val < P.chainReqs.length ∧ k.val < P.chainReqs.length from
    ⟨j.isLt, k.isLt⟩)]
  rfl

theorem job_arc_L (P : ThreePartition) (hb : 0 < P.b) (c : ℕ)
    (hc : c + 1 < 2 * P.t * P.b) :
    P.chainInstance.Arc (jobFin P hb (.inl ⟨c, by omega⟩))
      (jobFin P hb (.inl ⟨c + 1, hc⟩)) := by
  apply chain_arc_of_raw
  simpa only [jobFin, jobPos, List.take_zero, List.sum_nil, Nat.zero_add] using
    chainArc_mem P.chainLengths 0 0 (2 * P.t * P.b) c (by rfl) hc

theorem job_arc_K (P : ThreePartition) (hb : 0 < P.b) (j : Fin (3 * P.t))
    (c : ℕ) (hc : c + 1 < 2 * P.a j) :
    P.chainInstance.Arc (jobFin P hb (.inr ⟨j, ⟨c, by omega⟩⟩))
      (jobFin P hb (.inr ⟨j, ⟨c + 1, hc⟩⟩)) := by
  apply chain_arc_of_raw
  have hh := chainArc_mem P.chainLengths 0 (j.val + 1) (2 * P.a j) c
    (by simp [chainLengths]) hc
  simpa only [chainLengths, List.take_succ_cons, List.sum_cons, zero_add, jobFin, jobPos,
    Nat.add_assoc]
    using hh

theorem chain_arc_successor (P : ThreePartition) {j k : Fin P.chainInstance.n}
    (h : P.chainInstance.Arc j k) : (k : ℕ) = j + 1 := by
  obtain ⟨⟨x, y⟩, hmem, hf⟩ := List.mem_filterMap.mp h
  have hxy : x = j.val ∧ y = k.val := by
    unfold toFinArc at hf
    split_ifs at hf with hh
    · obtain ⟨rfl, rfl⟩ := Option.some.inj hf
      exact ⟨rfl, rfl⟩
  obtain ⟨rfl, rfl⟩ := hxy
  exact (aux_cs_mem_chainArcsFrom _ _ _ _ hmem).choose_spec.choose_spec.choose_spec.2.2.2

theorem chain_instance_class (P : ThreePartition) (hP : P.Valid) :
    IsP2Res111Chain P.chainInstance := by
  classical
  refine ⟨rfl, rfl, fun _ => rfl, ?_, ?_, ?_⟩
  · intro h j
    obtain ⟨d, rfl⟩ := (jobEquiv P hP.1).surjective j
    rw [show jobEquiv P hP.1 d = jobFin P hP.1 d from rfl, job_req]
    exact aux_cs_req_le P _
  · intro v
    constructor <;> apply Finset.card_le_one.mpr
    · intro j hj k hk
      have hj' := chain_arc_successor P (Finset.mem_filter.mp hj).2
      have hk' := chain_arc_successor P (Finset.mem_filter.mp hk).2
      apply Fin.ext
      omega
    · intro j hj k hk
      have hj' := chain_arc_successor P (Finset.mem_filter.mp hj).2
      have hk' := chain_arc_successor P (Finset.mem_filter.mp hk).2
      apply Fin.ext
      omega
  · intro j hj
    have hlt : ∀ {u v : Fin P.chainInstance.n}, P.chainInstance.Prec u v → u.val < v.val := by
      intro u v huv
      induction huv with
      | single h => have := chain_arc_successor P h; omega
      | tail _ h ih => have := chain_arc_successor P h; omega
    exact (Nat.lt_irrefl j.val) (hlt hj)

end ResourceScheduling.ChainProof

end

/- Complete checked body: FloorSchedule -/
section

set_option autoImplicit false

open Set

namespace ResourceScheduling.ChainProof

open ResourceScheduling.Chain

noncomputable def floorSchedule {I : Instance} (σ : Schedule I) : Schedule I where
  machine := σ.machine
  start := fun j => (⌊σ.start j⌋₊ : ℝ)

theorem floor_separation {x y : ℝ} (hx : 0 ≤ x) (h : x + 1 ≤ y) :
    (⌊x⌋₊ : ℝ) + 1 ≤ (⌊y⌋₊ : ℝ) := by
  have hh := Nat.floor_mono h
  rw [Nat.floor_add_one hx] at hh
  exact_mod_cast hh

theorem integer_intervals_same_start {a b : ℕ} {t : ℝ}
    (ha : (a : ℝ) ≤ t ∧ t < (a : ℝ) + 1)
    (hb : (b : ℝ) ≤ t ∧ t < (b : ℝ) + 1) : a = b := by
  have hab : a < b + 1 := by exact_mod_cast ha.1.trans_lt hb.2
  have hba : b < a + 1 := by exact_mod_cast hb.1.trans_lt ha.2
  omega

theorem floorSchedule_feasible {I : Instance} (σ : Schedule I) (hσ : σ.Feasible) :
    (floorSchedule σ).Feasible := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    exact Nat.cast_nonneg _
  · intro j k hjk hmach
    obtain h | h := hσ.2.1 j k hjk hmach
    · exact Or.inl (floor_separation (hσ.1 j) h)
    · exact Or.inr (floor_separation (hσ.1 k) h)
  · intro j k hjk
    exact floor_separation (hσ.1 j) (hσ.2.2.1 j k hjk)
  · intro t h
    let A : Finset (Fin I.n) := Finset.univ.filter (fun j => (floorSchedule σ).IsExecutedAt j t)
    change (∑ j ∈ A, I.r h j) ≤ I.s h
    by_cases hA : A.Nonempty
    · obtain ⟨j, hj, hmax⟩ := A.exists_max_image σ.start hA
      have hjt : (floorSchedule σ).IsExecutedAt j t := (Finset.mem_filter.mp hj).2
      have hsub : A ⊆ Finset.univ.filter (fun k => σ.IsExecutedAt k (σ.start j)) := by
        intro k hk
        have hkt : (floorSchedule σ).IsExecutedAt k t := (Finset.mem_filter.mp hk).2
        have he : ⌊σ.start j⌋₊ = ⌊σ.start k⌋₊ := integer_intervals_same_start hjt hkt
        have hlo := Nat.floor_le (hσ.1 k)
        have hup := Nat.lt_floor_add_one (σ.start j)
        rw [he] at hup
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ k, hmax k hk, ?_⟩
        linarith
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)).trans
        (hσ.2.2.2 (σ.start j) h)
    · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
      simp only [he, Finset.sum_empty]
      exact Nat.zero_le _

theorem floorSchedule_cmax_le {I : Instance} (σ : Schedule I)
    (hσ : ∀ j, 0 ≤ σ.start j) : (floorSchedule σ).cmax ≤ σ.cmax := by
  classical
  unfold Schedule.cmax
  split_ifs with hn
  · apply Finset.sup'_le
    intro j _
    have hc : (floorSchedule σ).completion j ≤ σ.completion j := by
      change (⌊σ.start j⌋₊ : ℝ) + 1 ≤ σ.start j + 1
      linarith [Nat.floor_le (hσ j)]
    exact hc.trans (Finset.le_sup'_of_le _ (Finset.mem_univ j) le_rfl)
  · exact le_rfl

theorem exists_integer_schedule {I : Instance} {T : ℕ} (h : I.HasScheduleWithin T) :
    ∃ q : Fin I.n → ℕ, ∃ machine : Fin I.n → Fin I.m,
      (⟨machine, fun j => (q j : ℝ)⟩ : Schedule I).Feasible ∧
      (⟨machine, fun j => (q j : ℝ)⟩ : Schedule I).cmax ≤ (T : ℝ) := by
  obtain ⟨σ, hσ, hc⟩ := h
  exact ⟨fun j => ⌊σ.start j⌋₊, σ.machine, floorSchedule_feasible σ hσ,
    (floorSchedule_cmax_le σ hσ.1).trans hc⟩

end ResourceScheduling.ChainProof

end

/- Complete checked body: IntegerRuns -/
section

set_option autoImplicit false

namespace ResourceScheduling.ChainProof

open ResourceScheduling.Chain ResourceScheduling.Chain.ThreePartition

structure ChainRun (P : ThreePartition) where
  time : ChainJob P → Fin (2 * P.t * P.b)
  machine : ChainJob P → Fin 2
  separate : ∀ d e, time d = time e → machine d = machine e → d = e
  resource : ∀ d e, time d = time e → aux_cs_req P (jobDesc P d) = 1 →
    aux_cs_req P (jobDesc P e) = 1 → d = e
  nextL : ∀ (c : ℕ) (hc : c + 1 < 2 * P.t * P.b),
    time (.inl ⟨c, by omega⟩) < time (.inl ⟨c + 1, hc⟩)
  nextK : ∀ (j : Fin (3 * P.t)) (c : ℕ) (hc : c + 1 < 2 * P.a j),
    time (.inr ⟨j, ⟨c, by omega⟩⟩) < time (.inr ⟨j, ⟨c + 1, hc⟩⟩)

theorem completion_le_cmax {I : Instance} (σ : Schedule I) (j : Fin I.n) :
    σ.completion j ≤ σ.cmax := by
  classical
  unfold Schedule.cmax
  rw [dif_pos (by have := j.isLt; omega : 0 < I.n)]
  exact Finset.le_sup' σ.completion (Finset.mem_univ j)

theorem resource_pair_eq {I : Instance} (q : Fin I.n → ℕ)
    (mach : Fin I.n → Fin I.m) (hf : (⟨mach, fun j => (q j : ℝ)⟩ : Schedule I).Feasible)
    (h : Fin I.l) (hh : I.s h = 1) (j k : Fin I.n) (hq : q j = q k)
    (hj : I.r h j = 1) (hk : I.r h k = 1) : j = k := by
  classical
  by_contra hne
  let A := Finset.univ.filter (fun i =>
    (⟨mach, fun j => (q j : ℝ)⟩ : Schedule I).IsExecutedAt i (q j : ℝ))
  have hjA : j ∈ A := by simp [A, Schedule.IsExecutedAt]
  have hkA : k ∈ A := by simp [A, Schedule.IsExecutedAt, hq]
  have hs : ({j, k} : Finset (Fin I.n)) ⊆ A := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hjA
    · obtain rfl := Finset.mem_singleton.mp hi
      exact hkA
  have hsum := Finset.sum_le_sum_of_subset (f := I.r h) hs
  have hb := hf.2.2.2 (q j : ℝ) h
  change (∑ i ∈ A, I.r h i) ≤ I.s h at hb
  rw [hh] at hb
  simp [hne, hj, hk] at hsum
  omega

theorem exists_chainRun (P : ThreePartition) (hb : 0 < P.b)
    (h : P.chainInstance.HasScheduleWithin (2 * P.t * P.b)) : Nonempty (ChainRun P) := by
  obtain ⟨q, mach, hf, hc⟩ := exists_integer_schedule h
  let σ : Schedule P.chainInstance := ⟨mach, fun j => (q j : ℝ)⟩
  have hq : ∀ j, q j < 2 * P.t * P.b := by
    intro j
    have hh := (completion_le_cmax σ j).trans hc
    change (q j : ℝ) + 1 ≤ (2 * P.t * P.b : ℕ) at hh
    have hn : q j + 1 ≤ 2 * P.t * P.b := by exact_mod_cast hh
    omega
  let time : ChainJob P → Fin (2 * P.t * P.b) := fun d =>
    ⟨q (jobFin P hb d), hq _⟩
  refine ⟨⟨time, fun d => mach (jobFin P hb d), ?_, ?_, ?_, ?_⟩⟩
  · intro d e he hm
    apply jobFin_injective P hb
    by_contra hne
    have ht : q (jobFin P hb d) = q (jobFin P hb e) := congrArg Fin.val he
    obtain hh | hh := hf.2.1 _ _ hne hm
    · change (q (jobFin P hb d) : ℝ) + 1 ≤ (q (jobFin P hb e) : ℝ) at hh
      rw [ht] at hh
      linarith
    · change (q (jobFin P hb e) : ℝ) + 1 ≤ (q (jobFin P hb d) : ℝ) at hh
      rw [ht] at hh
      linarith
  · intro d e he hd hr
    apply jobFin_injective P hb
    apply resource_pair_eq q mach hf (⟨0, by change 0 < 1; decide⟩ : Fin P.chainInstance.l) rfl _ _
      (congrArg Fin.val he)
    · rwa [job_req]
    · rwa [job_req]
  · intro c hc'
    have hh := hf.2.2.1 _ _ (Relation.TransGen.single (job_arc_L P hb c hc'))
    change (q (jobFin P hb (.inl ⟨c, by omega⟩)) : ℝ) + 1 ≤
      (q (jobFin P hb (.inl ⟨c + 1, hc'⟩)) : ℝ) at hh
    change q (jobFin P hb (.inl ⟨c, by omega⟩)) < q (jobFin P hb (.inl ⟨c + 1, hc'⟩))
    have hn : q (jobFin P hb (.inl ⟨c, by omega⟩)) + 1 ≤
        q (jobFin P hb (.inl ⟨c + 1, hc'⟩)) := by exact_mod_cast hh
    omega
  · intro j c hc'
    have hh := hf.2.2.1 _ _ (Relation.TransGen.single (job_arc_K P hb j c hc'))
    change (q (jobFin P hb (.inr ⟨j, ⟨c, by omega⟩⟩)) : ℝ) + 1 ≤
      (q (jobFin P hb (.inr ⟨j, ⟨c + 1, hc'⟩⟩)) : ℝ) at hh
    change q (jobFin P hb (.inr ⟨j, ⟨c, by omega⟩⟩)) <
      q (jobFin P hb (.inr ⟨j, ⟨c + 1, hc'⟩⟩))
    have hn : q (jobFin P hb (.inr ⟨j, ⟨c, by omega⟩⟩)) + 1 ≤
        q (jobFin P hb (.inr ⟨j, ⟨c + 1, hc'⟩⟩)) := by exact_mod_cast hh
    omega

theorem strictMono_fin_of_next {n : ℕ} {β : Type*} [Preorder β]
    (f : Fin n → β) (hf : ∀ c (hc : c + 1 < n), f ⟨c, by omega⟩ < f ⟨c + 1, hc⟩) :
    StrictMono f := by
  cases n with
  | zero => exact fun i => Fin.elim0 i
  | succ n => exact Fin.strictMono_iff_lt_succ.mpr (fun i => hf i (by have := i.isLt; omega))

theorem ChainRun.timeL {P : ThreePartition} (R : ChainRun P) (c : Fin (2 * P.t * P.b)) :
    R.time (.inl c) = c := by
  have he := (strictMono_fin_of_next (fun c => R.time (.inl c)) R.nextL).eq_id
  exact congrFun he c

theorem ChainRun.timeK_strictMono {P : ThreePartition} (R : ChainRun P)
    (j : Fin (3 * P.t)) : StrictMono (fun c : Fin (2 * P.a j) => R.time (.inr ⟨j, c⟩)) :=
  strictMono_fin_of_next _ (R.nextK j)

theorem ChainRun.timeK_injective {P : ThreePartition} (R : ChainRun P) :
    Function.Injective (fun d : Σ j : Fin (3 * P.t), Fin (2 * P.a j) => R.time (.inr d)) := by
  intro d e he
  let c := R.time (.inr d)
  have hd : R.machine (.inr d) ≠ R.machine (.inl c) := by
    intro hm
    have hh := R.separate (.inr d) (.inl c) (R.timeL c).symm hm
    cases hh
  have he' : R.machine (.inr e) ≠ R.machine (.inl c) := by
    intro hm
    have hh := R.separate (.inr e) (.inl c) (he.symm.trans (R.timeL c).symm) hm
    cases hh
  have hm : R.machine (.inr d) = R.machine (.inr e) := by
    apply Fin.ext
    have hdv := (R.machine (.inr d)).isLt
    have hev := (R.machine (.inr e)).isLt
    have hcv := (R.machine (.inl c)).isLt
    have hd' : (R.machine (.inr d)).val ≠ (R.machine (.inl c)).val := fun h => hd (Fin.ext h)
    have he'' : (R.machine (.inr e)).val ≠ (R.machine (.inl c)).val := fun h => he' (Fin.ext h)
    omega
  exact Sum.inr.inj (R.separate _ _ he hm)

end ResourceScheduling.ChainProof

end

/- Complete checked body: SlotArithmetic -/
section

set_option autoImplicit false

namespace ResourceScheduling.ChainProof

def slotCoord {t b : ℕ} (hb : 0 < b) (q : Fin (2 * t * b)) : Fin t × Fin b :=
  (⟨q.val / b / 2, by
    have hdiv : q.val / b < 2 * t := (Nat.div_lt_iff_lt_mul hb).mpr q.isLt
    exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr (by omega)⟩,
   ⟨q.val % b, Nat.mod_lt _ hb⟩)

theorem slot_reconstruct {t b : ℕ} (hb : 0 < b) (q : Fin (2 * t * b)) :
    q.val = (2 * ((slotCoord hb q).1 : ℕ) + q.val / b % 2) * b +
      ((slotCoord hb q).2 : ℕ) := by
  have h₁ := Nat.mod_add_div q.val b
  have h₂ := Nat.mod_add_div (q.val / b) 2
  change q.val = (2 * (q.val / b / 2) + q.val / b % 2) * b + q.val % b
  calc
    q.val = q.val % b + b * (q.val / b) := h₁.symm
    _ = q.val % b + b * ((q.val / b % 2) + 2 * (q.val / b / 2)) := by rw [h₂]
    _ = _ := by ring

theorem slotCoord_injective_on_parity {t b : ℕ} (hb : 0 < b)
    {q q' : Fin (2 * t * b)} (hp : q.val / b % 2 = q'.val / b % 2)
    (he : slotCoord hb q = slotCoord hb q') : q = q' := by
  apply Fin.ext
  rw [slot_reconstruct hb q, slot_reconstruct hb q', he, hp]

def slotValue {t b : ℕ} (e : Fin 2) (z : Fin t × Fin b) : Fin (2 * t * b) :=
  ⟨(2 * z.1.val + e.val) * b + z.2.val, by
    have hr := z.1.isLt
    have he := e.isLt
    have hc := z.2.isLt
    have hq : 2 * z.1.val + e.val + 1 ≤ 2 * t := by omega
    have hh := Nat.mul_le_mul_right b hq
    nlinarith⟩

theorem slotValue_div {t b : ℕ} (hb : 0 < b) (e : Fin 2) (z : Fin t × Fin b) :
    (slotValue e z).val / b = 2 * z.1.val + e.val := by
  change ((2 * z.1.val + e.val) * b + z.2.val) / b = _
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt z.2.isLt, zero_add]

theorem slotValue_parity {t b : ℕ} (hb : 0 < b) (e : Fin 2) (z : Fin t × Fin b) :
    (slotValue e z).val / b % 2 = e.val := by
  rw [slotValue_div hb]
  omega

theorem slotCoord_slotValue {t b : ℕ} (hb : 0 < b) (e : Fin 2)
    (z : Fin t × Fin b) : slotCoord hb (slotValue e z) = z := by
  apply Prod.ext <;> apply Fin.ext
  · change (slotValue e z).val / b / 2 = z.1.val
    rw [slotValue_div hb]
    omega
  · change ((2 * z.1.val + e.val) * b + z.2.val) % b = z.2.val
    simp [Nat.mod_eq_of_lt z.2.isLt]

theorem slotValue_slotCoord {t b : ℕ} (hb : 0 < b) (e : Fin 2)
    (q : Fin (2 * t * b)) (he : q.val / b % 2 = e.val) :
    slotValue e (slotCoord hb q) = q := by
  apply Fin.ext
  have hh := slot_reconstruct hb q
  rw [he] at hh
  exact hh.symm

theorem slotCoord_mono {t b : ℕ} (hb : 0 < b) {q q' : Fin (2 * t * b)}
    (h : q.val ≤ q'.val) : (slotCoord hb q).1 ≤ (slotCoord hb q').1 :=
  Nat.div_le_div_right (Nat.div_le_div_right h)

end ResourceScheduling.ChainProof

end

/- Complete checked body: SlotBalance -/
section

set_option autoImplicit false

namespace ResourceScheduling.ChainProof

open ResourceScheduling.Chain

theorem equal_sum_sandwich {α : Type*} [Fintype α]
    (f g h : α → ℕ) (hfg : ∀ x, f x ≤ g x) (hgh : ∀ x, g x ≤ h x)
    (hs : ∑ x, f x = ∑ x, h x) : ∀ x, f x = g x ∧ g x = h x := by
  have he : ∀ x, f x = h x := by
    intro x
    exact (Finset.sum_eq_sum_iff_of_le (fun y _ => (hfg y).trans (hgh y))).mp hs x
      (Finset.mem_univ x)
  intro x
  have := he x
  have := hfg x
  have := hgh x
  exact ⟨by omega, by omega⟩

theorem slot_block_eq {α : Type*} [Fintype α] {t b : ℕ}
    (u v : α ≃ Fin t × Fin b) (s : α → Fin t)
    (hu : ∀ x, (u x).1 ≤ s x) (hv : ∀ x, s x ≤ (v x).1) :
    ∀ x, (u x).1 = s x ∧ s x = (v x).1 := by
  have hs : (∑ x, ((u x).1 : ℕ)) = ∑ x, ((v x).1 : ℕ) :=
    (u.sum_comp (fun z : Fin t × Fin b => (z.1 : ℕ))).trans
      (v.sum_comp (fun z : Fin t × Fin b => (z.1 : ℕ))).symm
  have he := equal_sum_sandwich (fun x => ((u x).1 : ℕ)) (fun x => (s x : ℕ))
    (fun x => ((v x).1 : ℕ)) hu hv hs
  intro x
  exact ⟨Fin.ext (he x).1, Fin.ext (he x).2⟩

theorem slot_fiber_weight {ι : Type*} [Fintype ι] [DecidableEq ι]
    {t b : ℕ} (a : ι → ℕ) (u : (Σ j, Fin (a j)) ≃ Fin t × Fin b)
    (s : ι → Fin t) (hu : ∀ x, (u x).1 = s x.1) (r : Fin t) :
    ∑ j ∈ Finset.univ.filter (fun j => s j = r), a j = b := by
  classical
  calc
    ∑ j ∈ Finset.univ.filter (fun j => s j = r), a j
        = ∑ x : Σ j, Fin (a j), if s x.1 = r then 1 else 0 := by
          rw [Fintype.sum_sigma]
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro j _
          by_cases hj : s j = r <;> simp [hj]
    _ = ∑ x : Σ j, Fin (a j), if (u x).1 = r then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          rw [hu x]
    _ = ∑ z : Fin t × Fin b, if z.1 = r then 1 else 0 :=
          u.sum_comp (fun z => if z.1 = r then 1 else 0)
    _ = b := by
          rw [Fintype.sum_prod_type]
          calc
            (∑ x : Fin t, ∑ _ : Fin b, if x = r then 1 else 0)
                = ∑ x : Fin t, if x = r then b else 0 := by
                  apply Finset.sum_congr rfl
                  intro x _
                  by_cases hx : x = r <;> simp [hx]
            _ = b := by simp

theorem three_of_weight {ι : Type*} [DecidableEq ι] (S : Finset ι) (a : ι → ℕ)
    {b : ℕ} (hb : 0 < b) (hs : ∑ j ∈ S, a j = b)
    (ha : ∀ j ∈ S, b < 4 * a j ∧ 2 * a j < b) : S.card = 3 := by
  have hne : S.Nonempty := by
    by_contra h
    have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [hzero, Finset.sum_empty] at hs
    omega
  have hlo := Finset.sum_lt_sum_of_nonempty hne (fun j hj => (ha j hj).2)
  have hhi := Finset.sum_lt_sum_of_nonempty hne (fun j hj => (ha j hj).1)
  simp only [← Finset.mul_sum, hs, Finset.sum_const, nsmul_eq_mul] at hlo hhi
  have hl : 2 < S.card := (Nat.mul_lt_mul_right hb).mp hlo
  have hh : S.card < 4 := (Nat.mul_lt_mul_right hb).mp hhi
  omega

theorem solution_of_slot_bijections (P : ThreePartition) (hP : P.Valid)
    (u v : (Σ j : Fin (3 * P.t), Fin (P.a j)) ≃ Fin P.t × Fin P.b)
    (s : Fin (3 * P.t) → Fin P.t)
    (hu : ∀ x, (u x).1 ≤ s x.1) (hv : ∀ x, s x.1 ≤ (v x).1) : P.IsSolution s := by
  classical
  have he := slot_block_eq u v (fun x => s x.1) hu hv
  intro r
  have hw := slot_fiber_weight P.a u s (fun x => (he x).1) r
  refine ⟨?_, hw⟩
  exact three_of_weight _ _ hP.1 hw (fun j _ => hP.2.2 j)

end ResourceScheduling.ChainProof

end

/- Complete checked body: SlotAssignment -/
section

set_option autoImplicit false

namespace ResourceScheduling.ChainProof

open ResourceScheduling.Chain ResourceScheduling.Chain.ThreePartition

abbrev ItemUnit (P : ThreePartition) := Σ j : Fin (3 * P.t), Fin (P.a j)

def itemPart (P : ThreePartition) (e : Bool) (d : ItemUnit P) :
    Σ j : Fin (3 * P.t), Fin (2 * P.a j) :=
  ⟨d.1, ⟨(if e then P.a d.1 else 0) + d.2.val, by split <;> have := d.2.isLt <;> omega⟩⟩

theorem itemPart_injective (P : ThreePartition) (e : Bool) :
    Function.Injective (itemPart P e) := by
  intro ⟨j, c⟩ ⟨k, d⟩ h
  have hj : j = k := congrArg Sigma.fst h
  subst k
  have hc := (Sigma.mk.inj h).2
  have hc' := congrArg Fin.val (eq_of_heq hc)
  apply congrArg (Sigma.mk j)
  apply Fin.ext
  change (if e then P.a j else 0) + c.val = (if e then P.a j else 0) + d.val at hc'
  omega

theorem itemPart_ne (P : ThreePartition) (d e : ItemUnit P) :
    itemPart P false d ≠ itemPart P true e := by
  intro h
  have hj : d.1 = e.1 := congrArg (fun x : Σ j : Fin (3 * P.t), Fin (2 * P.a j) => x.1) h
  obtain ⟨j, c⟩ := d
  obtain ⟨k, v⟩ := e
  dsimp at hj
  subst k
  have hc := congrArg Fin.val (eq_of_heq (Sigma.mk.inj h).2)
  change 0 + c.val = P.a j + v.val at hc
  have := c.isLt
  omega

def partTime {P : ThreePartition} (R : ChainRun P) (e : Bool) (d : ItemUnit P) :
    Fin (2 * P.t * P.b) := R.time (.inr (itemPart P e d))

theorem partTime_injective {P : ThreePartition} (R : ChainRun P) (e : Bool) :
    Function.Injective (partTime R e) :=
  R.timeK_injective.comp (itemPart_injective P e)

theorem primed_parity {P : ThreePartition} (R : ChainRun P) (d : ItemUnit P) :
    (partTime R true d).val / P.b % 2 = 1 := by
  have hm := Nat.mod_lt ((partTime R true d).val / P.b) (by decide : 0 < 2)
  by_contra hn
  have hz : (partTime R true d).val / P.b % 2 = 0 := by omega
  have he := R.resource (.inl (partTime R true d)) (.inr (itemPart P true d))
    (R.timeL _) (by simp [jobDesc, aux_cs_req, hz])
    (by simp [jobDesc, itemPart, aux_cs_req])
  cases he

theorem card_itemUnit (P : ThreePartition) (hP : P.Valid) :
    Fintype.card (ItemUnit P) = Fintype.card (Fin P.t × Fin P.b) := by
  simpa only [ItemUnit, Fintype.card_sigma, Fintype.card_fin, Fintype.card_prod] using hP.2.1

noncomputable def primedSlots {P : ThreePartition} (hP : P.Valid) (R : ChainRun P) :
    ItemUnit P ≃ Fin P.t × Fin P.b :=
  Equiv.ofBijective (fun d => slotCoord hP.1 (partTime R true d))
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨by
      intro d e he
      apply partTime_injective R true
      exact slotCoord_injective_on_parity hP.1 ((primed_parity R d).trans
        (primed_parity R e).symm) he, card_itemUnit P hP⟩)

theorem unprimed_parity {P : ThreePartition} (hP : P.Valid) (R : ChainRun P)
    (d : ItemUnit P) : (partTime R false d).val / P.b % 2 = 0 := by
  have hm := Nat.mod_lt ((partTime R false d).val / P.b) (by decide : 0 < 2)
  by_contra hn
  have ho : (partTime R false d).val / P.b % 2 = 1 := by omega
  obtain ⟨e, he⟩ := (primedSlots hP R).surjective (slotCoord hP.1 (partTime R false d))
  have htime : partTime R true e = partTime R false d :=
    slotCoord_injective_on_parity hP.1 ((primed_parity R e).trans ho.symm) he
  exact itemPart_ne P d e (R.timeK_injective htime.symm)

noncomputable def unprimedSlots {P : ThreePartition} (hP : P.Valid) (R : ChainRun P) :
    ItemUnit P ≃ Fin P.t × Fin P.b :=
  Equiv.ofBijective (fun d => slotCoord hP.1 (partTime R false d))
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨by
      intro d e he
      apply partTime_injective R false
      exact slotCoord_injective_on_parity hP.1 ((unprimed_parity hP R d).trans
        (unprimed_parity hP R e).symm) he, card_itemUnit P hP⟩)

theorem item_positive (P : ThreePartition) (hP : P.Valid) (j : Fin (3 * P.t)) :
    0 < P.a j := by
  have := (hP.2.2 j).1
  omega

noncomputable def assignedBlock {P : ThreePartition} (hP : P.Valid) (R : ChainRun P)
    (j : Fin (3 * P.t)) : Fin P.t :=
  (primedSlots hP R ⟨j, ⟨0, item_positive P hP j⟩⟩).1

theorem assignment_sandwich {P : ThreePartition} (hP : P.Valid) (R : ChainRun P)
    (d : ItemUnit P) :
    (unprimedSlots hP R d).1 ≤ assignedBlock hP R d.1 ∧
      assignedBlock hP R d.1 ≤ (primedSlots hP R d).1 := by
  have hmono := (R.timeK_strictMono d.1).monotone
  constructor
  · apply slotCoord_mono hP.1
    apply hmono
    change 0 + d.2.val ≤ P.a d.1 + 0
    have := d.2.isLt
    omega
  · apply slotCoord_mono hP.1
    apply hmono
    change P.a d.1 + 0 ≤ P.a d.1 + d.2.val
    omega

theorem chainRun_hasSolution {P : ThreePartition} (hP : P.Valid) (R : ChainRun P) :
    P.HasSolution := by
  refine ⟨assignedBlock hP R, solution_of_slot_bijections P hP
    (unprimedSlots hP R) (primedSlots hP R) (assignedBlock hP R) ?_ ?_⟩
  · exact fun d => (assignment_sandwich hP R d).1
  · exact fun d => (assignment_sandwich hP R d).2

theorem chain_schedule_iff (P : ThreePartition) (hP : P.Valid) :
    P.HasSolution ↔ P.chainInstance.HasScheduleWithin (2 * P.t * P.b) := by
  constructor
  · intro hs
    obtain ⟨σ, hf, hc⟩ := checked_chainSchedule_of_threePartition P hP hs
    exact ⟨σ, hf, hc.le⟩
  · intro hs
    obtain ⟨R⟩ := exists_chainRun P hP.1 hs
    exact chainRun_hasSolution hP R

end ResourceScheduling.ChainProof

end

/- Complete checked body: UnaryCode -/
section

open ResourceScheduling.Chain

namespace ResourceScheduling.ChainProof

def decodeNats : List USym → Option (List ℕ)
  | [] => some []
  | .sep :: w => (decodeNats w).map (0 :: ·)
  | .one :: w => do
      let ns ← decodeNats w
      match ns with
      | [] => none
      | n :: ns => some ((n + 1) :: ns)

theorem decodeNats_encNat (n : ℕ) (w : List USym) :
    decodeNats (encNat n ++ w) = (decodeNats w).map (n :: ·) := by
  induction n with
  | zero => simp [encNat, decodeNats]
  | succ n ih =>
      simp only [encNat, List.replicate_succ, List.cons_append, decodeNats] at ih ⊢
      rw [ih]
      cases decodeNats w <;> rfl

theorem decodeNats_encNats (ns : List ℕ) : decodeNats (encNats ns) = some ns := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
      rw [encNats, List.flatMap_cons, decodeNats_encNat]
      change (decodeNats (encNats ns)).map (n :: ·) = _
      rw [ih]
      rfl

theorem decodeNats_sound (w : List USym) (ns : List ℕ)
    (h : decodeNats w = some ns) : w = encNats ns := by
  induction w generalizing ns with
  | nil =>
      have he : ([] : List ℕ) = ns := Option.some.inj h
      subst ns
      rfl
  | cons a w ih =>
      cases a with
      | sep =>
          simp only [decodeNats, Option.map_eq_some_iff] at h
          obtain ⟨xs, hx, rfl⟩ := h
          rw [ih xs hx]
          rfl
      | one =>
          cases hw : decodeNats w with
          | none => simp [decodeNats, hw] at h
          | some xs =>
              cases xs with
              | nil => simp [decodeNats, hw] at h
              | cons n xs =>
                  have hn : (n + 1) :: xs = ns := by simpa [decodeNats, hw] using h
                  subst ns
                  rw [ih (n :: xs) hw]
                  simp [encNats, encNat, List.replicate_succ]

theorem encNats_injective : Function.Injective encNats := by
  intro a b h
  have := congrArg decodeNats h
  simpa only [decodeNats_encNats, Option.some.injEq] using this

def decodeThreePartition (w : List USym) : Option ThreePartition :=
  match decodeNats w with
  | some (t :: b :: as) =>
      if as.length = 3 * t then some ⟨t, b, fun i => as.getD i 0⟩ else none
  | _ => none

theorem decodeThreePartition_code (P : ThreePartition) :
    decodeThreePartition (encNats P.code) = some P := by
  cases P with
  | mk t b a =>
      simp [decodeThreePartition, decodeNats_encNats, ThreePartition.code]

theorem threePartition_code_injective : Function.Injective ThreePartition.code := by
  intro P Q h
  have := congrArg (fun ns => decodeThreePartition (encNats ns)) h
  simpa only [decodeThreePartition_code, Option.some.injEq] using this

theorem decodeThreePartition_sound (w : List USym) (P : ThreePartition)
    (h : decodeThreePartition w = some P) : w = encNats P.code := by
  unfold decodeThreePartition at h
  cases hd : decodeNats w with
  | none => simp [hd] at h
  | some ns =>
      rw [hd] at h
      cases ns with
      | nil => simp at h
      | cons t ns =>
          cases ns with
          | nil => simp at h
          | cons b as =>
              dsimp only at h
              split_ifs at h with hlen
              ·
                have he : ThreePartition.mk t b (fun i => as.getD i 0) = P :=
                  Option.some.inj h
                subst P
                rw [decodeNats_sound w (t :: b :: as) hd]
                congr 1
                change t :: b :: as = t :: b :: List.ofFn (fun i : Fin (3 * t) => as.getD i 0)
                congr 2
                apply List.ext_getElem
                · simpa using hlen
                · intro i hi hj
                  simp only [List.getElem_ofFn]
                  exact (List.getD_eq_getElem _ _ hi).symm

end ResourceScheduling.ChainProof

end

/- Complete checked body: ReductionMap -/
section

open ResourceScheduling.Chain

namespace ResourceScheduling.ChainProof

noncomputable def chainReduction (w : List USym) : List USym := by
  classical
  exact match decodeThreePartition w with
    | none => []
    | some P => if P.Valid then
        encNats (Instance.decisionCode (P.chainInstance, 2 * P.t * P.b)) else []

theorem chainReduction_valid (P : ThreePartition) (hP : P.Valid) :
    chainReduction (encNats P.code) =
      encNats (Instance.decisionCode (P.chainInstance, 2 * P.t * P.b)) := by
  simp [chainReduction, decodeThreePartition_code, hP]

theorem chainReduction_spec (w : List USym) :
    chainReduction w = [] ∨ ∃ P : ThreePartition, P.Valid ∧
      w = encNats P.code ∧ chainReduction w =
        encNats (Instance.decisionCode (P.chainInstance, 2 * P.t * P.b)) := by
  classical
  cases h : decodeThreePartition w with
  | none => exact Or.inl (by simp [chainReduction, h])
  | some P =>
      by_cases hv : P.Valid
      · exact Or.inr ⟨P, hv, decodeThreePartition_sound w P h,
          by simp [chainReduction, h, hv]⟩
      · exact Or.inl (by simp [chainReduction, h, hv])

end ResourceScheduling.ChainProof

end

/- Complete checked body: InstanceCode -/
section

open ResourceScheduling.Chain

namespace ResourceScheduling.ChainProof

theorem matrix_word_injective {m n : ℕ} (f g : Fin m → Fin n → ℕ)
    (h : (List.ofFn fun i => List.ofFn (f i)).flatten =
      (List.ofFn fun i => List.ofFn (g i)).flatten) : f = g := by
  induction m with
  | zero => exact Subsingleton.elim _ _
  | succ m ih =>
      simp only [List.ofFn_succ, List.flatten_cons] at h
      obtain ⟨h0, ht⟩ := List.append_inj h (by simp)
      have hhead : f 0 = g 0 := List.ofFn_injective h0
      have htail := ih (fun i => f i.succ) (fun i => g i.succ) ht
      funext i
      refine Fin.cases hhead (fun i => congrFun htail i) i

def arcWord {n : ℕ} (arcs : List (Fin n × Fin n)) : List ℕ :=
  arcs.flatMap fun e => [(e.1 : ℕ), (e.2 : ℕ)]

theorem arcWord_length {n : ℕ} (arcs : List (Fin n × Fin n)) :
    (arcWord arcs).length = 2 * arcs.length := by
  simp [arcWord, Nat.mul_comm]

theorem arcWord_injective {n : ℕ} : Function.Injective (arcWord (n := n)) := by
  intro a
  induction a with
  | nil =>
      intro b h
      cases b with
      | nil => rfl
      | cons e es => simp [arcWord] at h
  | cons e es ih =>
      intro b h
      cases b with
      | nil => simp [arcWord] at h
      | cons f fs =>
          change e.1.val :: e.2.val :: arcWord es = f.1.val :: f.2.val :: arcWord fs at h
          obtain ⟨h1, h2, ht⟩ := List.cons.inj h |>.imp_right List.cons.inj
          have he : e = f := Prod.ext (Fin.ext h1) (Fin.ext h2)
          exact congrArg₂ List.cons he (ih ht)

theorem decisionCode_injective : Function.Injective Instance.decisionCode := by
  rintro ⟨I, y⟩ ⟨J, z⟩ h
  cases I with
  | mk n m l s r arcs =>
    cases J with
    | mk n' m' l' s' r' arcs' =>
      simp only [Instance.decisionCode, Instance.code, List.append_assoc,
        List.cons_append, List.nil_append] at h
      obtain ⟨hn, h1⟩ := List.cons.inj h
      subst n'
      obtain ⟨hm, h2⟩ := List.cons.inj h1
      subst m'
      obtain ⟨hl, h3⟩ := List.cons.inj h2
      subst l'
      obtain ⟨hs, h4⟩ := List.append_inj h3 (by simp)
      have hs' : s = s' := List.ofFn_injective hs
      subst s'
      obtain ⟨hr, h5⟩ := List.append_inj h4 (by simp [Function.comp_def])
      have hr' : r = r' := matrix_word_injective r r' hr
      subst r'
      obtain ⟨ha, h6⟩ := List.cons.inj h5
      change arcWord arcs ++ [y] = arcWord arcs' ++ [z] at h6
      obtain ⟨hab, hyz⟩ := List.append_inj h6 (by simp only [arcWord_length, ha])
      have harcs : arcs = arcs' := arcWord_injective hab
      have hyz' : y = z := List.cons.inj hyz |>.1
      subst arcs'
      subst z
      rfl

theorem unary_decisionCode_injective :
    Function.Injective (fun x => encNats (Instance.decisionCode x)) :=
  encNats_injective.comp decisionCode_injective

theorem empty_not_target :
    ([] : List USym) ∉ unaryLang Instance.decisionCode P2Res111Chain := by
  rintro ⟨⟨I, y⟩, _, h⟩
  have he := congrArg decodeNats h
  rw [decodeNats_encNats] at he
  have hn : ([] : List ℕ) = Instance.decisionCode (I, y) := Option.some.inj he
  simp [Instance.decisionCode, Instance.code] at hn

end ResourceScheduling.ChainProof

end

/- Complete checked body: AttributedCook -/
section

set_option autoImplicit false

namespace CookSource_comp_setup_frame
-- Prove2me | solution 1 for CookPvsNP.comp_setup_frame
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T08:35:50.252337+00:00
-- url     : https://prove2.me/submissions/2cf7b5c6-5d41-45f7-aab1-4d90345295c1


set_option autoImplicit false

open CookPvsNP

private theorem run_add {Γ : Type} (M : TM Γ) (a b : ℕ) (c : Cfg Γ M.Q) :
    M.run (a + b) c = M.run a (M.run b c) := Function.iterate_add_apply _ _ _ _

section
variable {I S Γ₁ Γ₂ : Type} [Fintype Γ₁] [Fintype Γ₂]
    (ι : I ↪ Γ₁) (j₁ : S ↪ Γ₁) (j₂ : S ↪ Γ₂) (M₁ : TM Γ₁) (M₂ : TM Γ₂)

local notation "C" => compTM j₁ j₂ M₁ M₂
local notation "embed" => compInputEmbedding (Γ₂ := Γ₂) ι

private theorem scan (xs : List I) (left : List (Option (CompCell Γ₁ Γ₂))) :
    (C).run xs.length ⟨.setupScan, left, (xs.map (some ∘ embed)).headD none,
      (xs.map (some ∘ embed)).tail⟩ =
    ⟨.setupScan, (xs.map (some ∘ embed)).reverse ++ left, none, []⟩ := by
  induction xs generalizing left with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, TM.run, Function.iterate_succ_apply]
    have hs : (C).step ⟨.setupScan, left, some (embed x), xs.map (some ∘ embed)⟩ =
        ⟨.setupScan, some (embed x) :: left, (xs.map (some ∘ embed)).headD none,
          (xs.map (some ∘ embed)).tail⟩ := by
      simp [TM.step, TM.IsHalting, compTM, CompCell.unpack, CompCell.pack,
        compInputEmbedding]
    simp only [List.map_cons, List.headD_cons, List.tail_cons, Function.comp_apply]
    rw [hs]
    simpa [TM.run, List.reverse_cons, List.append_assoc] using ih (some (embed x) :: left)

private theorem return_step (x : I) (left right : List (Option (CompCell Γ₁ Γ₂))) :
    (C).step ⟨.setupReturn, left, some (embed x), right⟩ =
      ⟨.setupReturn, left.tail, left.headD none, some (embed x) :: right⟩ := by
  cases left <;> simp [TM.step, TM.IsHalting, compTM, CompCell.unpack, CompCell.pack,
    compInputEmbedding]

private theorem return_past (xs : List I) (origin : Option (CompCell Γ₁ Γ₂))
    (right : List (Option (CompCell Γ₁ Γ₂))) :
    (C).run xs.length ⟨.setupReturn, (xs.map (some ∘ embed) ++ [origin]).tail,
      (xs.map (some ∘ embed) ++ [origin]).headD none, right⟩ =
    ⟨.setupReturn, [], origin, (xs.map (some ∘ embed)).reverse ++ right⟩ := by
  induction xs generalizing right with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, TM.run, Function.iterate_succ_apply,
      List.map_cons, List.cons_append, List.headD_cons, List.tail_cons, Function.comp_apply]
    rw [return_step ι j₁ j₂ M₁ M₂]
    simpa [TM.run, List.reverse_cons, List.append_assoc] using ih (some (embed x) :: right)

private theorem blank_step (left : List (Option (CompCell Γ₁ Γ₂))) :
    (C).step ⟨.setupScan, left, none, []⟩ =
      ⟨.setupReturn, left.tail, left.headD none,
        [some { CompCell.blank with rightB := true }]⟩ := by
  cases left <;> simp [TM.step, TM.IsHalting, compTM, CompCell.unpack,
    CompCell.pack, CompCell.blank]

private theorem finish (x : I) (r : Option (CompCell Γ₁ Γ₂))
    (rs : List (Option (CompCell Γ₁ Γ₂)))
    (hr : CompCell.pack (CompCell.unpack r) = r) :
    (C).run 2 ⟨.setupReturn, [], some { (embed x) with setupOrigin := true }, r :: rs⟩ =
      ⟨.sim₁ M₁.q₀, [], some (embed x), r :: rs⟩ := by
  simp [TM.run, Function.iterate_succ_apply, TM.step, TM.IsHalting, compTM,
    CompCell.unpack, CompCell.pack, compInputEmbedding]
  constructor
  · rfl
  · simpa [CompCell.pack, CompCell.unpack] using hr

/-- Exact setup configuration, including the sentinel just beyond the input.
For empty input the sentinel is one cell to the right of the initial head. -/
private theorem setup_raw (w : List I) :
    (C).run (2 * max w.length 1 + 2) ((C).init (w.map embed)) =
      ⟨.sim₁ M₁.q₀, [], (w.map (some ∘ embed)).headD none,
        (w.map (some ∘ embed)).tail ++ [some { CompCell.blank with rightB := true }]⟩ := by
  cases w with
  | nil =>
    simp [TM.run, TM.init, Function.iterate_succ_apply, TM.step, TM.IsHalting,
      compTM, CompCell.unpack, CompCell.pack, CompCell.blank]
  | cons x xs =>
    let origin : Option (CompCell Γ₁ Γ₂) := some { (embed x) with setupOrigin := true }
    let marker : Option (CompCell Γ₁ Γ₂) := some { CompCell.blank with rightB := true }
    have hs : (C).run 1 ((C).init ((x :: xs).map embed)) =
        ⟨.setupScan, [origin], (xs.map (some ∘ embed)).headD none,
          (xs.map (some ∘ embed)).tail⟩ := by
      simp [TM.run, TM.init, TM.step, TM.IsHalting, compTM, origin,
        CompCell.unpack, CompCell.pack, compInputEmbedding, List.map_map, Function.comp_def]
    have hb : (C).run 1 ⟨.setupScan, (xs.map (some ∘ embed)).reverse ++ [origin], none, []⟩ =
        ⟨.setupReturn, ((xs.map (some ∘ embed)).reverse ++ [origin]).tail,
          ((xs.map (some ∘ embed)).reverse ++ [origin]).headD none, [marker]⟩ := by
      exact blank_step j₁ j₂ M₁ M₂ _
    have hr := return_past ι j₁ j₂ M₁ M₂ xs.reverse origin [marker]
    simp only [List.length_reverse, List.map_reverse, List.reverse_reverse] at hr
    have hf : (C).run 2 ⟨.setupReturn, [], origin, xs.map (some ∘ embed) ++ [marker]⟩ =
        ⟨.sim₁ M₁.q₀, [], some (embed x), xs.map (some ∘ embed) ++ [marker]⟩ := by
      cases xs with
      | nil =>
        exact finish ι j₁ j₂ M₁ M₂ x marker []
          (by simp [marker, CompCell.unpack, CompCell.pack, CompCell.blank])
      | cons y ys =>
        exact finish ι j₁ j₂ M₁ M₂ x (some (embed y)) (ys.map (some ∘ embed) ++ [marker])
          (by simp [CompCell.unpack, CompCell.pack, compInputEmbedding])
    rw [show 2 * max (x :: xs).length 1 + 2 =
        2 + (xs.length + (1 + (xs.length + 1))) by simp; omega]
    rw [run_add, run_add, run_add, run_add, hs, scan ι j₁ j₂ M₁ M₂, hb, hr]
    simpa [origin, marker] using hf

end

theorem solution {I S Γ₁ Γ₂ : Type} [Fintype Γ₁] [Fintype Γ₂]
    (ι : I ↪ Γ₁) (j₁ : S ↪ Γ₁) (j₂ : S ↪ Γ₂) (M₁ : TM Γ₁) (M₂ : TM Γ₂)
    (w : List I) :
    (compTM j₁ j₂ M₁ M₂).run (2 * max w.length 1 + 2)
      ((compTM j₁ j₂ M₁ M₂).init (w.map (compInputEmbedding ι))) =
      compFirstCfg (M₁.init (w.map ι)) := by
  rw [setup_raw ι j₁ j₂ M₁ M₂ w]
  cases w <;>
    simp [TM.init, compFirstCfg, CompCell.firstSymbol, CompCell.plain, CompCell.pack,
      compInputEmbedding, List.map_map, Function.comp_def, CompCell.rightMarker, CompCell.blank] <;> rfl

end CookSource_comp_setup_frame
namespace CookPvsNP
alias comp_setup_frame := _root_.CookSource_comp_setup_frame.solution
end CookPvsNP

namespace CookSource_comp_first_frame_step
-- Prove2me | solution 1 for CookPvsNP.comp_first_frame_step
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T08:35:48.754983+00:00
-- url     : https://prove2.me/submissions/73fe278d-ebe1-4392-8a5f-a1331690d789


set_option autoImplicit false

open CookPvsNP

private theorem unpack_first {Γ₁ Γ₂ : Type} (a : Option Γ₁) :
    CompCell.unpack (CompCell.firstSymbol (Γ₂ := Γ₂) a) =
      ⟨a, none, false, false, false, false, false⟩ := by
  cases a <;> simp [CompCell.firstSymbol, CompCell.plain, CompCell.pack,
    CompCell.unpack, CompCell.blank]

private theorem pack_first {Γ₁ Γ₂ : Type} (a : Option Γ₁) :
    CompCell.pack (⟨a, none, false, false, false, false, false⟩ : CompCell Γ₁ Γ₂) =
      CompCell.firstSymbol a := rfl

private theorem first_none {Γ₁ Γ₂ : Type} :
    CompCell.firstSymbol (Γ₁ := Γ₁) (Γ₂ := Γ₂) none = none := rfl

private theorem pack_right {Γ₁ Γ₂ : Type} :
    CompCell.pack (⟨none, none, false, false, true, false, false⟩ : CompCell Γ₁ Γ₂) =
      CompCell.rightMarker := rfl

private theorem unpack_right {Γ₁ Γ₂ : Type} :
    CompCell.unpack (CompCell.rightMarker : Option (CompCell Γ₁ Γ₂)) =
      ⟨none, none, false, false, true, false, false⟩ := rfl

private theorem unpack_none {Γ₁ Γ₂ : Type} :
    CompCell.unpack (none : Option (CompCell Γ₁ Γ₂)) =
      ⟨none, none, false, false, false, false, false⟩ := rfl

/-- The first simulation phase preserves its exact finite-list representation. -/
theorem solution {S Γ₁ Γ₂ : Type} [Fintype Γ₁] [Fintype Γ₂]
    (j₁ : S ↪ Γ₁) (j₂ : S ↪ Γ₂) (M₁ : TM Γ₁) (M₂ : TM Γ₂)
    (c : Cfg Γ₁ M₁.Q) (hn : ¬ M₁.IsHalting c) :
    (compTM j₁ j₂ M₁ M₂).run 3 (compFirstCfg c) = compFirstCfg (M₁.step c) := by
  classical
  rcases c with ⟨q, left, head, right⟩
  have hq : ¬ (q = M₁.qaccept ∨ q = M₁.qreject) := hn
  rcases hd : M₁.δ q head with ⟨q', w, move⟩
  cases move <;> cases left <;> cases right <;>
    simp [TM.run, Function.iterate_succ_apply, TM.step, TM.IsHalting, compTM,
      compFirstCfg, unpack_first, pack_first, first_none, pack_right,
      unpack_right, unpack_none, hq, hd]

end CookSource_comp_first_frame_step
namespace CookPvsNP
alias comp_first_frame_step := _root_.CookSource_comp_first_frame_step.solution
end CookPvsNP

namespace CookSource_tm_run_eq_of_halting
-- Prove2me | solution 1 for CookPvsNP.tm_run_eq_of_halting
-- status  : ACCEPTED   (prove)
-- author  : @Sneed
-- created : 2026-09-30T17:18:19.007986+00:00
-- url     : https://prove2.me/submissions/c08fa0a7-cc5c-4232-82a9-dd70c54493aa


set_option autoImplicit false

theorem solution {Γ : Type} (M : CookPvsNP.TM Γ) (c : CookPvsNP.Cfg Γ M.Q)
    (h : M.IsHalting c) (n : ℕ) : M.run n c = c := by
  unfold CookPvsNP.TM.run
  apply Function.iterate_fixed
  simp [CookPvsNP.TM.step, h]

end CookSource_tm_run_eq_of_halting
namespace CookPvsNP
alias tm_run_eq_of_halting := _root_.CookSource_tm_run_eq_of_halting.solution
end CookPvsNP

namespace CookSource_comp_first_halt
-- Prove2me | solution 1 for CookPvsNP.comp_first_halt
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T08:35:51.15698+00:00
-- url     : https://prove2.me/submissions/893ea022-608e-4471-ac03-716c82cb8fbf


set_option autoImplicit false

open CookPvsNP

private theorem run_add {Γ : Type} (M : TM Γ) (a b : ℕ) (c : Cfg Γ M.Q) :
    M.run (a + b) c = M.run a (M.run b c) := Function.iterate_add_apply _ _ _ _

private theorem blocks {A B : Type} (f : A → A) (g : B → B) (e : A → B) (H : A → Prop)
    (hs : ∀ a, ¬ H a → g^[3] (e a) = e (f a))
    (n : ℕ) (a : A) (hn : ∀ i < n, ¬ H (f^[i] a)) :
    g^[3 * n] (e a) = e (f^[n] a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ, Nat.add_comm, Function.iterate_add_apply,
      ih (fun i hi => hn i (Nat.lt_succ_of_lt hi)), hs _ (hn n (Nat.lt_succ_self n))]
    rw [Function.iterate_succ_apply']

private theorem first_run {S Γ₁ Γ₂ : Type} [Fintype Γ₁] [Fintype Γ₂]
    (j₁ : S ↪ Γ₁) (j₂ : S ↪ Γ₂) (M₁ : TM Γ₁) (M₂ : TM Γ₂)
    (c : Cfg Γ₁ M₁.Q) (n : ℕ)
    (hn : ∀ i < n, ¬ M₁.IsHalting (M₁.run i c)) :
    (compTM j₁ j₂ M₁ M₂).run (3 * n) (compFirstCfg c) = compFirstCfg (M₁.run n c) := by
  exact blocks M₁.step (compTM j₁ j₂ M₁ M₂).step compFirstCfg M₁.IsHalting
    (comp_first_frame_step j₁ j₂ M₁ M₂) n c hn

/-- If the first source machine halts by n steps, its final configuration is
reached in the first phase after 3*m composite steps for some m <= n. -/
theorem solution {S Γ₁ Γ₂ : Type} [Fintype Γ₁] [Fintype Γ₂]
    (j₁ : S ↪ Γ₁) (j₂ : S ↪ Γ₂) (M₁ : TM Γ₁) (M₂ : TM Γ₂)
    (c : Cfg Γ₁ M₁.Q) (n : ℕ) (hn : M₁.IsHalting (M₁.run n c)) :
    ∃ m ≤ n, (compTM j₁ j₂ M₁ M₂).run (3 * m) (compFirstCfg c) =
      compFirstCfg (M₁.run n c) := by
  classical
  let hex : ∃ m, M₁.IsHalting (M₁.run m c) := ⟨n, hn⟩
  let m := Nat.find hex
  have hm : m ≤ n := Nat.find_min' hex hn
  have hstop : M₁.IsHalting (M₁.run m c) := Nat.find_spec hex
  have heq : M₁.run n c = M₁.run m c := by
    conv_lhs => rw [show n = (n - m) + m by omega]
    rw [run_add, tm_run_eq_of_halting M₁ _ hstop]
  refine ⟨m, hm, ?_⟩
  rw [heq]
  exact first_run j₁ j₂ M₁ M₂ c m (fun i hi => Nat.find_min hex hi)

end CookSource_comp_first_halt
namespace CookPvsNP
alias comp_first_halt := _root_.CookSource_comp_first_halt.solution
end CookPvsNP

namespace CookSource_comp_conversion_entry
-- Prove2me | solution 1 for CookPvsNP.comp_conversion_entry
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T09:08:42.398282+00:00
-- url     : https://prove2.me/submissions/d50673cb-470c-439c-aaa2-82e1c54aefa8


set_option autoImplicit false
open CookPvsNP

/-- A halted first simulation installs the origin and left-boundary markers in two steps. -/
theorem solution {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B)
    (c : Cfg A M₁.Q) (hn : M₁.IsHalting c) :
    (compTM j₁ j₂ M₁ M₂).run 2 (compFirstCfg c) =
      ⟨.convCopy true,
        CompCell.leftMarker (c.left.headD none) :: c.left.tail.map CompCell.firstSymbol,
        CompCell.originSymbol c.head none,
        c.right.map CompCell.firstSymbol ++ [CompCell.rightMarker]⟩ := by
  rcases c with ⟨q, left, head, right⟩
  change q = M₁.qaccept ∨ q = M₁.qreject at hn
  cases head <;> cases left with
  | nil =>
    simp [TM.run, Function.iterate_succ_apply, TM.step, TM.IsHalting, compTM,
      compFirstCfg, CompCell.firstSymbol, CompCell.plain, CompCell.originSymbol,
      CompCell.leftMarker, CompCell.pack, CompCell.unpack, CompCell.blank, hn]
  | cons a left =>
    cases a <;> simp [TM.run, Function.iterate_succ_apply, TM.step, TM.IsHalting, compTM,
      compFirstCfg, CompCell.firstSymbol, CompCell.plain, CompCell.originSymbol,
      CompCell.leftMarker, CompCell.pack, CompCell.unpack, CompCell.blank, hn]

end CookSource_comp_conversion_entry
namespace CookPvsNP
alias comp_conversion_entry := _root_.CookSource_comp_conversion_entry.solution
end CookPvsNP

namespace CookSource_comp_cell_laws
-- Prove2me | solution 1 for CookPvsNP.comp_cell_laws
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T06:27:19.636439+00:00
-- url     : https://prove2.me/submissions/1075d6c6-7190-49a3-a04d-95ccf950fb83


set_option autoImplicit false

open CookPvsNP

private theorem unpack_pack {Γ₁ Γ₂ : Type} (c : CompCell Γ₁ Γ₂) :
    CompCell.unpack (CompCell.pack c) = c := by
  rcases c with ⟨one, two, setup, left, right, second, final⟩
  unfold CompCell.pack
  split
  · next h => simp_all [CompCell.unpack, CompCell.blank]
  · rfl

private theorem pack_injective {Γ₁ Γ₂ : Type} :
    Function.Injective (@CompCell.pack Γ₁ Γ₂) := by
  intro c d h
  have e := congrArg CompCell.unpack h
  simpa only [unpack_pack] using e

private theorem translate_image {Sym Γ₁ Γ₂ : Type}
    (ι₁ : Sym ↪ Γ₁) (ι₂ : Sym ↪ Γ₂) (x : Sym) :
    translateCell ι₁ ι₂ (ι₁ x) = some (ι₂ x) := by
  classical
  have h : ∃ s, ι₁ s = ι₁ x := ⟨x, rfl⟩
  unfold translateCell
  rw [dif_pos h]
  exact congrArg (fun s => some (ι₂ s)) (ι₁.injective (Classical.choose_spec h))

/-- Elementary laws for the already published concrete composition machine.
The packing map is injective, and transfer between the two symbol embeddings is exact. -/
theorem solution {Sym Γ₁ Γ₂ : Type} (ι₁ : Sym ↪ Γ₁) (ι₂ : Sym ↪ Γ₂) :
    (∀ c : CompCell Γ₁ Γ₂, CompCell.unpack (CompCell.pack c) = c) ∧
    Function.Injective (@CompCell.pack Γ₁ Γ₂) ∧
    (∀ x : Sym, translateCell ι₁ ι₂ (ι₁ x) = some (ι₂ x)) := by
  exact ⟨unpack_pack, pack_injective, translate_image ι₁ ι₂⟩

end CookSource_comp_cell_laws
namespace CookPvsNP
alias comp_cell_laws := _root_.CookSource_comp_cell_laws.solution
end CookPvsNP

namespace CookSource_comp_conversion_copy
-- Prove2me | solution 1 for CookPvsNP.comp_conversion_copy
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T09:08:43.024604+00:00
-- url     : https://prove2.me/submissions/d6719f14-dbd7-4122-b271-c42cdf4c3184


set_option autoImplicit false
open CookPvsNP

/-- Conversion copies each encoded nonblank symbol to the second track in one step. -/
theorem solution {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B) (xs : List S)
    (left right : List (Option (CompCell A B))) :
    (compTM j₁ j₂ M₁ M₂).run xs.length
      ⟨.convCopy false, left,
        (xs.map (fun x => CompCell.firstSymbol (some (j₁ x))) ++ right).headD none,
        (xs.map (fun x => CompCell.firstSymbol (some (j₁ x))) ++ right).tail⟩ =
      ⟨.convCopy false,
        (xs.map (fun x => CompCell.plain (some (j₁ x)) (some (j₂ x)))).reverse ++ left,
        right.headD none, right.tail⟩ := by
  induction xs generalizing left with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, TM.run, Function.iterate_succ_apply, List.map_cons,
      List.cons_append, List.headD_cons, List.tail_cons]
    have hs (L R : List (Option (CompCell A B))) :
        (compTM j₁ j₂ M₁ M₂).step ⟨.convCopy false, L, CompCell.firstSymbol (some (j₁ x)), R⟩ =
          ⟨.convCopy false, CompCell.plain (some (j₁ x)) (some (j₂ x)) :: L,
            R.headD none, R.tail⟩ := by
      simp [TM.step, TM.IsHalting, compTM, CompCell.firstSymbol, CompCell.plain,
        (comp_cell_laws j₁ j₂).1, (comp_cell_laws j₁ j₂).2.2]
    rw [hs]
    simpa [TM.run, List.reverse_cons, List.append_assoc] using
      ih (CompCell.plain (some (j₁ x)) (some (j₂ x)) :: left)

end CookSource_comp_conversion_copy
namespace CookPvsNP
alias comp_conversion_copy := _root_.CookSource_comp_conversion_copy.solution
end CookPvsNP

namespace CookSource_comp_conversion_return
-- Prove2me | solution 1 for CookPvsNP.comp_conversion_return
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T09:08:44.442439+00:00
-- url     : https://prove2.me/submissions/0757d80f-f00d-4073-a461-ddcbb3844da6


set_option autoImplicit false
open CookPvsNP

section
variable {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B)
local notation "C" => compTM j₁ j₂ M₁ M₂

private theorem past (xs : List (CompCell A B))
    (hx : ∀ x ∈ xs, x.secondOrigin = false) (origin : Option (CompCell A B))
    (left right : List (Option (CompCell A B))) :
    (C).run xs.length ⟨.convReturn, (xs.map CompCell.pack ++ [origin]).tail ++ left,
      (xs.map CompCell.pack ++ [origin]).headD none, right⟩ =
      ⟨.convReturn, left, origin, (xs.map CompCell.pack).reverse ++ right⟩ := by
  induction xs generalizing right with
  | nil => rfl
  | cons x xs ih =>
    have hx₀ := hx x (by simp)
    have hx₁ : ∀ a ∈ xs, a.secondOrigin = false := fun a ha => hx a (by simp [ha])
    simp only [List.length_cons, TM.run, Function.iterate_succ_apply, List.map_cons,
      List.cons_append, List.headD_cons, List.tail_cons]
    have hs (L R : List (Option (CompCell A B))) :
        (C).step ⟨.convReturn, L, CompCell.pack x, R⟩ =
          ⟨.convReturn, L.tail, L.headD none, CompCell.pack x :: R⟩ := by
      cases L <;> simp [TM.step, TM.IsHalting, compTM, (comp_cell_laws j₁ j₂).1, hx₀]
    rw [hs]
    cases xs with
    | nil => rfl
    | cons y ys =>
      simpa [TM.run, List.reverse_cons, List.append_assoc] using
        ih hx₁ (CompCell.pack x :: right)

private theorem finish (a : Option A) (b : Option B)
    (left : List (Option (CompCell A B))) (r : Option (CompCell A B))
    (rs : List (Option (CompCell A B))) (hr : CompCell.pack (CompCell.unpack r) = r) :
    (C).run 2 ⟨.convReturn, left, CompCell.originSymbol a b, r :: rs⟩ =
      ⟨.sim₂ M₂.q₀, left, CompCell.plain a b, r :: rs⟩ := by
  simp [TM.run, Function.iterate_succ_apply, TM.step, TM.IsHalting, compTM,
    CompCell.originSymbol, CompCell.unpack, CompCell.plain]
  exact hr

private theorem return_raw (xs : List (CompCell A B))
    (hx : ∀ x ∈ xs, x.secondOrigin = false) (a : Option A) (b : Option B)
    (left : List (Option (CompCell A B))) (r : Option (CompCell A B))
    (rs : List (Option (CompCell A B))) (hr : CompCell.pack (CompCell.unpack r) = r) :
    (C).run (xs.length + 2)
      ⟨.convReturn, (xs.map CompCell.pack ++ [CompCell.originSymbol a b]).tail ++ left,
        (xs.map CompCell.pack ++ [CompCell.originSymbol a b]).headD none, r :: rs⟩ =
      ⟨.sim₂ M₂.q₀, left, CompCell.plain a b, (xs.map CompCell.pack).reverse ++ r :: rs⟩ := by
  have hp := past j₁ j₂ M₁ M₂ xs hx (CompCell.originSymbol a b) left (r :: rs)
  have hf : (C).run 2
      ⟨.convReturn, left, CompCell.originSymbol a b, (xs.map CompCell.pack).reverse ++ r :: rs⟩ =
      ⟨.sim₂ M₂.q₀, left, CompCell.plain a b, (xs.map CompCell.pack).reverse ++ r :: rs⟩ := by
    rw [← List.map_reverse]
    cases xs.reverse with
    | nil => exact finish j₁ j₂ M₁ M₂ a b left r rs hr
    | cons x rest =>
      exact finish j₁ j₂ M₁ M₂ a b left (CompCell.pack x)
        (rest.map CompCell.pack ++ r :: rs) (by rw [(comp_cell_laws j₁ j₂).1])
  rw [Nat.add_comm]
  unfold TM.run at hp hf ⊢
  dsimp only [compTM] at hp hf ⊢
  rw [Function.iterate_add_apply, hp]
  exact hf

end

/-- The conversion return scan reaches its marked origin and starts the second machine. -/
theorem solution {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B)
    (xs : List (CompCell A B)) (hx : ∀ x ∈ xs, x.secondOrigin = false)
    (a : Option A) (b : Option B) (left : List (Option (CompCell A B)))
    (r : Option (CompCell A B)) (rs : List (Option (CompCell A B)))
    (hr : CompCell.pack (CompCell.unpack r) = r) :
    (compTM j₁ j₂ M₁ M₂).run (xs.length + 2)
      ⟨.convReturn, (xs.map CompCell.pack ++ [CompCell.originSymbol a b]).tail ++ left,
        (xs.map CompCell.pack ++ [CompCell.originSymbol a b]).headD none, r :: rs⟩ =
      ⟨.sim₂ M₂.q₀, left, CompCell.plain a b, (xs.map CompCell.pack).reverse ++ r :: rs⟩ := by
  exact return_raw j₁ j₂ M₁ M₂ xs hx a b left r rs hr

end CookSource_comp_conversion_return
namespace CookPvsNP
alias comp_conversion_return := _root_.CookSource_comp_conversion_return.solution
end CookPvsNP

namespace CookSource_comp_conversion_seek
-- Prove2me | solution 1 for CookPvsNP.comp_conversion_seek
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T09:08:43.844329+00:00
-- url     : https://prove2.me/submissions/fa9e9566-7b57-4fa5-82af-010e4d8af495


set_option autoImplicit false
open CookPvsNP

/-- After placing the new right boundary, conversion erases the old one beyond the padding. -/
theorem solution {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B)
    (n : ℕ) (left : List (Option (CompCell A B))) :
    (compTM j₁ j₂ M₁ M₂).run (n + 1)
      ⟨.convSeekOldRight, left,
        (List.replicate n none ++ [CompCell.rightMarker]).headD none,
        (List.replicate n none ++ [CompCell.rightMarker]).tail⟩ =
      ⟨.convReturn, (List.replicate n none ++ left).tail,
        (List.replicate n none ++ left).headD none, [none]⟩ := by
  induction n generalizing left with
  | zero =>
    cases left <;> simp [TM.run, TM.step, TM.IsHalting, compTM, CompCell.rightMarker,
      CompCell.pack, CompCell.unpack, CompCell.blank]
  | succ n ih =>
    simp only [TM.run, Function.iterate_succ_apply, List.replicate_succ, List.cons_append,
      List.headD_cons, List.tail_cons]
    have hs (L R : List (Option (CompCell A B))) :
        (compTM j₁ j₂ M₁ M₂).step ⟨.convSeekOldRight, L, none, R⟩ =
          ⟨.convSeekOldRight, none :: L, R.headD none, R.tail⟩ := by
      simp [TM.step, TM.IsHalting, compTM, CompCell.unpack, CompCell.blank, CompCell.pack]
    rw [hs]
    have he : List.replicate n (none : Option (CompCell A B)) ++ none :: left =
        none :: (List.replicate n none ++ left) := by
      calc
        _ = (List.replicate n none ++ [none]) ++ left := by simp
        _ = List.replicate (n + 1) none ++ left := by rw [List.replicate_succ']
        _ = _ := by rw [List.replicate_succ]; rfl
    simpa only [TM.run, Function.iterate_succ_apply, he, List.tail_cons, List.headD_cons]
      using ih (none :: left)

end CookSource_comp_conversion_seek
namespace CookPvsNP
alias comp_conversion_seek := _root_.CookSource_comp_conversion_seek.solution
end CookPvsNP

namespace CookSource_comp_conversion_boundary
-- Prove2me | solution 1 for CookPvsNP.comp_conversion_boundary
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T09:29:31.623413+00:00
-- url     : https://prove2.me/submissions/27185bb6-88a6-489a-b7fd-8c8628e02572


set_option autoImplicit false
open CookPvsNP

section
variable {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B)
local notation "C" => compTM j₁ j₂ M₁ M₂

private theorem boundary_raw (xs : List (CompCell A B))
    (hx : ∀ x ∈ xs, x.secondOrigin = false) (a : Option A) (b : Option B)
    (left : List (Option (CompCell A B))) (padding : ℕ) (empty : Bool) :
    (C).run (xs.length + 2 * padding + 3)
      ⟨if empty then .convEmptyRight else .convCopy false,
        xs.map CompCell.pack ++ CompCell.originSymbol a b :: left,
        (List.replicate padding none ++ [CompCell.rightMarker]).headD none,
        (List.replicate padding none ++ [CompCell.rightMarker]).tail⟩ =
      ⟨.sim₂ M₂.q₀, left, CompCell.plain a b,
        (xs.map CompCell.pack).reverse ++ CompCell.rightMarker :: List.replicate padding none⟩ := by
  let rb : CompCell A B := ⟨none, none, false, false, true, false, false⟩
  have hrb : CompCell.pack rb = CompCell.rightMarker := by
    simp [rb, CompCell.pack, CompCell.rightMarker, CompCell.blank]
  have hblank : CompCell.pack (CompCell.blank : CompCell A B) = none := rfl
  cases padding with
  | zero =>
    have hs : (C).run 1
        ⟨if empty then .convEmptyRight else .convCopy false,
          xs.map CompCell.pack ++ CompCell.originSymbol a b :: left, CompCell.rightMarker, []⟩ =
        ⟨.convReturn, (xs.map CompCell.pack ++ [CompCell.originSymbol a b]).tail ++ left,
          (xs.map CompCell.pack ++ [CompCell.originSymbol a b]).headD none, [CompCell.rightMarker]⟩ := by
      cases empty <;> cases xs <;> simp [TM.run, TM.step, TM.IsHalting, compTM,
        CompCell.rightMarker, CompCell.unpack, CompCell.pack, CompCell.blank]
    have hf := comp_conversion_return j₁ j₂ M₁ M₂ xs hx a b left CompCell.rightMarker []
      (by rw [← hrb, (comp_cell_laws j₁ j₂).1])
    simp only [List.replicate_zero, List.nil_append, List.headD_cons, List.tail_cons,
      Nat.mul_zero, Nat.add_zero] at *
    rw [show xs.length + 3 = (xs.length + 2) + 1 by omega]
    unfold TM.run at hs hf ⊢
    dsimp only [compTM] at hs hf ⊢
    rw [Function.iterate_add_apply, hs]
    exact hf
  | succ n =>
    let ys := List.replicate n (CompCell.blank : CompCell A B) ++ rb :: xs
    have hy : ∀ y ∈ ys, y.secondOrigin = false := by
      intro y h
      simp only [ys, List.mem_append, List.mem_replicate, List.mem_cons] at h
      rcases h with ⟨_, rfl⟩ | rfl | h
      · rfl
      · rfl
      · exact hx y h
    have hm : ys.map CompCell.pack = List.replicate n none ++ CompCell.rightMarker :: xs.map CompCell.pack := by
      simp [ys, hrb, hblank]
    have hs : (C).run 1
        ⟨if empty then .convEmptyRight else .convCopy false,
          xs.map CompCell.pack ++ CompCell.originSymbol a b :: left, none,
          List.replicate n none ++ [CompCell.rightMarker]⟩ =
        ⟨.convSeekOldRight, CompCell.rightMarker :: (xs.map CompCell.pack ++ CompCell.originSymbol a b :: left),
          (List.replicate n none ++ [CompCell.rightMarker]).headD none,
          (List.replicate n none ++ [CompCell.rightMarker]).tail⟩ := by
      cases empty <;> simp [TM.run, TM.step, TM.IsHalting, compTM, CompCell.unpack,
        CompCell.pack, CompCell.blank, CompCell.rightMarker]
    have hk := comp_conversion_seek j₁ j₂ M₁ M₂ n
      (CompCell.rightMarker :: (xs.map CompCell.pack ++ CompCell.originSymbol a b :: left))
    have hf := comp_conversion_return j₁ j₂ M₁ M₂ ys hy a b left none [] rfl
    have ht : (List.replicate n (none : Option (CompCell A B)) ++ CompCell.rightMarker ::
          (xs.map CompCell.pack ++ CompCell.originSymbol a b :: left)).tail =
        (ys.map CompCell.pack ++ [CompCell.originSymbol a b]).tail ++ left := by
      rw [hm]
      cases n <;> simp [List.replicate_succ, List.append_assoc]
    have hh : (List.replicate n (none : Option (CompCell A B)) ++ CompCell.rightMarker ::
          (xs.map CompCell.pack ++ CompCell.originSymbol a b :: left)).headD none =
        (ys.map CompCell.pack ++ [CompCell.originSymbol a b]).headD none := by
      rw [hm]
      cases n <;> simp [List.replicate_succ]
    rw [ht, hh] at hk
    have hlen : ys.length = n + 1 + xs.length := by simp [ys]; omega
    have hout : (ys.map CompCell.pack).reverse ++ [none] =
        (xs.map CompCell.pack).reverse ++ CompCell.rightMarker :: List.replicate (n + 1) none := by
      simp [hm, List.reverse_append, List.append_assoc, List.replicate_succ']
    rw [hout] at hf
    simp only [List.replicate_succ, List.cons_append, List.headD_cons, List.tail_cons]
    rw [show xs.length + 2 * (n + 1) + 3 = (ys.length + 2) + ((n + 1) + 1) by omega]
    unfold TM.run at hs hk hf ⊢
    dsimp only [compTM] at hs hk hf ⊢
    rw [Function.iterate_add_apply _ (ys.length + 2) ((n + 1) + 1),
      Function.iterate_add_apply _ (n + 1) 1, hs, hk]
    simpa only [List.replicate_succ] using hf

end

/-- Conversion relocates the right boundary, clears the old one, and returns to the second origin. -/
theorem solution {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B)
    (xs : List (CompCell A B)) (hx : ∀ x ∈ xs, x.secondOrigin = false)
    (a : Option A) (b : Option B) (left : List (Option (CompCell A B)))
    (padding : ℕ) (empty : Bool) :
    (compTM j₁ j₂ M₁ M₂).run (xs.length + 2 * padding + 3)
      ⟨if empty then .convEmptyRight else .convCopy false,
        xs.map CompCell.pack ++ CompCell.originSymbol a b :: left,
        (List.replicate padding none ++ [CompCell.rightMarker]).headD none,
        (List.replicate padding none ++ [CompCell.rightMarker]).tail⟩ =
      ⟨.sim₂ M₂.q₀, left, CompCell.plain a b,
        (xs.map CompCell.pack).reverse ++ CompCell.rightMarker :: List.replicate padding none⟩ := by
  exact boundary_raw j₁ j₂ M₁ M₂ xs hx a b left padding empty

end CookSource_comp_conversion_boundary
namespace CookPvsNP
alias comp_conversion_boundary := _root_.CookSource_comp_conversion_boundary.solution
end CookPvsNP

namespace CookSource_comp_conversion
-- Prove2me | solution 1 for CookPvsNP.comp_conversion
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T09:29:30.318088+00:00
-- url     : https://prove2.me/submissions/1ee0cc82-161c-4c0a-8c08-f7291d1a5661


set_option autoImplicit false
open CookPvsNP

/-- The entire conversion phase implements the intermediate alphabet translation. -/
theorem solution {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B)
    (q : M₁.Q) (left : List (Option A)) (w : List S) (padding : ℕ)
    (hn : q = M₁.qaccept ∨ q = M₁.qreject) :
    (compTM j₁ j₂ M₁ M₂).run
      (2 * (compWordCfg j₁ q left w padding).right.length + 6)
      (compFirstCfg (compWordCfg j₁ q left w padding)) =
      (compConvertedFrame j₁ j₂ M₂.q₀ left w padding).encode := by
  let C := compTM j₁ j₂ M₁ M₂
  let L := CompCell.leftMarker (left.headD none) :: left.tail.map (CompCell.firstSymbol (Γ₂ := B))
  have hblank : CompCell.firstSymbol (Γ₁ := A) (Γ₂ := B) none = none := rfl
  have he := comp_conversion_entry j₁ j₂ M₁ M₂ (compWordCfg j₁ q left w padding) hn
  cases w with
  | nil =>
    have hs : C.run 1 ⟨.convCopy true, L, CompCell.originSymbol none none,
        List.replicate padding none ++ [CompCell.rightMarker]⟩ =
        ⟨.convEmptyRight, CompCell.originSymbol none none :: L,
          (List.replicate padding none ++ [CompCell.rightMarker]).headD none,
          (List.replicate padding none ++ [CompCell.rightMarker]).tail⟩ := by
      simp [C, TM.run, TM.step, TM.IsHalting, compTM, CompCell.originSymbol,
        CompCell.pack, CompCell.unpack]
    have hb := comp_conversion_boundary j₁ j₂ M₁ M₂ [] (by simp) none none L padding true
    simp only [compWordCfg, List.map_nil, List.headD_nil, List.tail_nil, List.nil_append,
      List.map_replicate, hblank] at he
    simp only [compWordCfg, List.map_nil, List.headD_nil, List.tail_nil, List.nil_append,
      List.length_replicate]
    rw [show 2 * padding + 6 = (0 + 2 * padding + 3) + (1 + 2) by omega]
    unfold TM.run at he hs hb ⊢
    dsimp only [C, compTM] at he hs hb ⊢
    rw [Function.iterate_add_apply _ (0 + 2 * padding + 3) (1 + 2),
      Function.iterate_add_apply _ 1 2, he, hs]
    simpa only [List.length_nil, List.map_nil, List.nil_append, List.reverse_nil, List.headD_nil,
      List.tail_nil, Bool.true_eq, ↓reduceIte, compConvertedFrame, CompSecondFrame.encode,
      List.singleton_append, L] using hb
  | cons a xs =>
    let cell (x : S) : CompCell A B := ⟨some (j₁ x), some (j₂ x), false, false, false, false, false⟩
    let R := List.replicate padding (none : Option (CompCell A B)) ++ [CompCell.rightMarker]
    have hm : xs.map (fun x => CompCell.plain (some (j₁ x)) (some (j₂ x))) =
        (xs.map cell).map CompCell.pack := by rw [List.map_map]; rfl
    have hs : C.run 1
        ⟨.convCopy true, L, CompCell.originSymbol (some (j₁ a)) none,
          xs.map (fun x => CompCell.firstSymbol (some (j₁ x))) ++ R⟩ =
        ⟨.convCopy false, CompCell.originSymbol (some (j₁ a)) (some (j₂ a)) :: L,
          (xs.map (fun x => CompCell.firstSymbol (some (j₁ x))) ++ R).headD none,
          (xs.map (fun x => CompCell.firstSymbol (some (j₁ x))) ++ R).tail⟩ := by
      simp [C, TM.run, TM.step, TM.IsHalting, compTM, CompCell.originSymbol,
        CompCell.pack, CompCell.unpack, (comp_cell_laws j₁ j₂).2.2]
    have hc := comp_conversion_copy j₁ j₂ M₁ M₂ xs
      (CompCell.originSymbol (some (j₁ a)) (some (j₂ a)) :: L) R
    have hx : ∀ x ∈ (xs.map cell).reverse, x.secondOrigin = false := by
      intro x h
      simp only [List.mem_reverse, List.mem_map] at h
      obtain ⟨y, _, rfl⟩ := h
      rfl
    have hb := comp_conversion_boundary j₁ j₂ M₁ M₂ (xs.map cell).reverse hx
      (some (j₁ a)) (some (j₂ a)) L padding false
    simp only [List.length_reverse, List.length_map, List.map_reverse, List.reverse_reverse,
      Bool.false_eq_true, ↓reduceIte, ← hm] at hb
    simp only [compWordCfg, List.map_cons, List.headD_cons, List.tail_cons,
      List.map_append, List.map_replicate, List.map_map, Function.comp_def, hblank,
      List.append_assoc] at he
    simp only [compWordCfg, List.map_cons, List.headD_cons, List.tail_cons, List.length_append,
      List.length_map, List.length_replicate, Function.comp_def]
    rw [show 2 * (xs.length + padding) + 6 =
      (xs.length + 2 * padding + 3) + (xs.length + (1 + 2)) by omega]
    unfold TM.run at he hs hc hb ⊢
    dsimp only [C, compTM] at he hs hc hb ⊢
    rw [Function.iterate_add_apply _ (xs.length + 2 * padding + 3) (xs.length + (1 + 2)),
      Function.iterate_add_apply _ xs.length (1 + 2), Function.iterate_add_apply _ 1 2,
      he, hs, hc]
    have hresult := hb
    simp only [compConvertedFrame, CompSecondFrame.encode, List.map_cons, List.headD_cons,
      List.tail_cons, List.map_nil, List.nil_append, List.map_map, Function.comp_def,
      L, R] at hresult ⊢
    exact hresult

end CookSource_comp_conversion
namespace CookPvsNP
alias comp_conversion := _root_.CookSource_comp_conversion.solution
end CookPvsNP

namespace CookSource_comp_output_form
-- Prove2me | solution 1 for CookPvsNP.comp_output_form
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T09:08:46.009144+00:00
-- url     : https://prove2.me/submissions/e340a2f3-0100-4417-a46e-3898cc098cfe


set_option autoImplicit false

open CookPvsNP

private theorem leading {Γ : Type} (xs : List (Option Γ)) :
    ∃ n, xs = List.replicate n none ++ xs.dropWhile Option.isNone := by
  induction xs with
  | nil => exact ⟨0, rfl⟩
  | cons x xs ih =>
    cases x with
    | none =>
      obtain ⟨n, h⟩ := ih
      refine ⟨n + 1, ?_⟩
      simpa [List.replicate_succ] using congrArg (List.cons none) h
    | some a => exact ⟨0, by simp⟩

private theorem trailing {Γ : Type} (xs : List (Option Γ)) :
    ∃ n, xs = (xs.reverse.dropWhile Option.isNone).reverse ++ List.replicate n none := by
  obtain ⟨n, h⟩ := leading xs.reverse
  exact ⟨n, by simpa using congrArg List.reverse h⟩

/-- An output equality to an ordinary encoded word determines every cell from the
head rightwards: the word is followed only by explicitly stored trailing blanks. -/
theorem solution {I Γ : Type} (ι : I ↪ Γ) (M : TM Γ) (c : Cfg Γ M.Q) (w : List I)
    (hout : M.output c = w.map (some ∘ ι)) :
    ∃ padding, c = compWordCfg ι c.state c.left w padding := by
  obtain ⟨n, h⟩ := trailing (c.head :: c.right)
  change c.head :: c.right = M.output c ++ List.replicate n none at h
  rw [hout] at h
  rcases c with ⟨q, left, head, right⟩
  cases w with
  | nil =>
    cases n with
    | zero => simp at h
    | succ n =>
      simp [List.replicate_succ] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨n, rfl⟩
  | cons a w =>
    simp at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨n, rfl⟩

end CookSource_comp_output_form
namespace CookPvsNP
alias comp_output_form := _root_.CookSource_comp_output_form.solution
end CookPvsNP

namespace CookSource_comp_handoff
-- Prove2me | solution 1 for CookPvsNP.comp_handoff
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T09:08:40.989359+00:00
-- url     : https://prove2.me/submissions/e258321c-722c-4e72-b665-2ba21319ba10


set_option autoImplicit false
open CookPvsNP

/-- A halted ordinary output becomes the exact initial input of the second simulation. -/
theorem solution {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B)
    (c : Cfg A M₁.Q) (w : List S) (hn : M₁.IsHalting c)
    (hout : M₁.output c = w.map (some ∘ j₁)) :
    ∃ d : CompSecondFrame A B M₂.Q,
      (compTM j₁ j₂ M₁ M₂).run (2 * c.right.length + 6) (compFirstCfg c) = d.encode ∧
      d.source = M₂.init (w.map j₂) ∧ d.right.length ≤ c.right.length := by
  obtain ⟨n, h⟩ := comp_output_form j₁ M₁ c w hout
  refine ⟨compConvertedFrame j₁ j₂ M₂.q₀ c.left w n, ?_, ?_, ?_⟩
  · have hc := comp_conversion j₁ j₂ M₁ M₂ c.state c.left w n hn
    simpa only [← h] using hc
  · cases w <;> simp [compConvertedFrame, CompSecondFrame.source, TM.init,
      List.map_map, Function.comp_def]
  · have hr := congrArg (fun c : Cfg A M₁.Q => c.right.length) h
    simp only [compWordCfg, List.length_append, List.length_tail, List.length_map,
      List.length_replicate] at hr
    simp only [compConvertedFrame, List.length_tail, List.length_map]
    omega

end CookSource_comp_handoff
namespace CookPvsNP
alias comp_handoff := _root_.CookSource_comp_handoff.solution
end CookPvsNP

namespace CookSource_comp_second_frame_step
-- Prove2me | solution 1 for CookPvsNP.comp_second_frame_step
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T08:54:21.758387+00:00
-- url     : https://prove2.me/submissions/fa440ec3-dd68-4ae6-a3a9-e2b3823368f3


set_option autoImplicit false

open CookPvsNP

private theorem unpack_plain {A B : Type} (a : Option A) (b : Option B) :
    CompCell.unpack (CompCell.plain a b) = ⟨a, b, false, false, false, false, false⟩ := by
  cases a <;> cases b <;> simp [CompCell.plain, CompCell.pack, CompCell.unpack, CompCell.blank]

private theorem pack_plain {A B : Type} (a : Option A) (b : Option B) :
    CompCell.pack (⟨a, b, false, false, false, false, false⟩ : CompCell A B) =
      CompCell.plain a b := rfl

private theorem unpack_left {A B : Type} (a : Option A) :
    CompCell.unpack (CompCell.leftMarker (Γ₂ := B) a) =
      ⟨a, none, false, true, false, false, false⟩ := rfl

private theorem pack_left {A B : Type} (a : Option A) :
    CompCell.pack (⟨a, none, false, true, false, false, false⟩ : CompCell A B) =
      CompCell.leftMarker a := by simp [CompCell.pack, CompCell.leftMarker, CompCell.blank]

private theorem unpack_right {A B : Type} :
    CompCell.unpack (CompCell.rightMarker : Option (CompCell A B)) =
      ⟨none, none, false, false, true, false, false⟩ := rfl

private theorem pack_right {A B : Type} :
    CompCell.pack (⟨none, none, false, false, true, false, false⟩ : CompCell A B) =
      CompCell.rightMarker := rfl

private theorem unpack_none {A B : Type} :
    CompCell.unpack (none : Option (CompCell A B)) =
      ⟨none, none, false, false, false, false, false⟩ := rfl

private theorem plain_none {A B : Type} :
    CompCell.plain (none : Option A) (none : Option B) = none := rfl

private theorem source_step {A B : Type} (M : TM B) (c : CompSecondFrame A B M.Q) :
    (c.step M).source = M.step c.source := by
  rcases c with ⟨q, left, head, right, mark, garbage, padding⟩
  by_cases hq : q = M.qaccept ∨ q = M.qreject
  · simp [CompSecondFrame.step, CompSecondFrame.source, TM.step, TM.IsHalting, hq]
  · rcases hd : M.δ q head.2 with ⟨q', w, move⟩
    cases move <;> cases left <;> cases right <;>
      simp [CompSecondFrame.step, CompSecondFrame.source, TM.step, TM.IsHalting, hq, hd]

/-- The decorated frame follows the second source machine exactly, and each
nonhalting source step takes three transitions of the original composite machine. -/
theorem solution {S Γ₁ Γ₂ : Type} [Fintype Γ₁] [Fintype Γ₂]
    (j₁ : S ↪ Γ₁) (j₂ : S ↪ Γ₂) (M₁ : TM Γ₁) (M₂ : TM Γ₂)
    (c : CompSecondFrame Γ₁ Γ₂ M₂.Q) :
    (c.step M₂).source = M₂.step c.source ∧
    (¬ M₂.IsHalting c.source →
      (compTM j₁ j₂ M₁ M₂).run 3 c.encode = (c.step M₂).encode) := by
  refine ⟨source_step M₂ c, ?_⟩
  intro hn
  rcases c with ⟨q, left, head, right, mark, garbage, padding⟩
  have hq : ¬ (q = M₂.qaccept ∨ q = M₂.qreject) := hn
  rcases hd : M₂.δ q head.2 with ⟨q', w, move⟩
  cases move with
  | left =>
    cases left with
    | nil =>
      cases garbage <;>
        simp [CompSecondFrame.encode, CompSecondFrame.step, CompSecondFrame.source,
          TM.run, Function.iterate_succ_apply, TM.step, TM.IsHalting, compTM,
          unpack_plain, pack_plain, unpack_left, pack_left, 
          unpack_none, CompCell.firstSymbol, hq, hd]
    | cons a left =>
      simp [CompSecondFrame.encode, CompSecondFrame.step, CompSecondFrame.source,
        TM.run, Function.iterate_succ_apply, TM.step, TM.IsHalting, compTM,
        unpack_plain, pack_plain, 
        hq, hd]
  | right =>
    cases right with
    | nil =>
      cases padding <;>
        simp [CompSecondFrame.encode, CompSecondFrame.step, CompSecondFrame.source,
          TM.run, Function.iterate_succ_apply, TM.step, TM.IsHalting, compTM,
          unpack_plain, pack_plain, unpack_right, pack_right,
          unpack_none, plain_none, List.replicate_succ, hq, hd]
    | cons a right =>
      simp [CompSecondFrame.encode, CompSecondFrame.step, CompSecondFrame.source,
        TM.run, Function.iterate_succ_apply, TM.step, TM.IsHalting, compTM,
        unpack_plain, pack_plain, 
        hq, hd]

end CookSource_comp_second_frame_step
namespace CookPvsNP
alias comp_second_frame_step := _root_.CookSource_comp_second_frame_step.solution
end CookPvsNP

namespace CookSource_comp_second_halt
-- Prove2me | solution 1 for CookPvsNP.comp_second_halt
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T08:54:23.262929+00:00
-- url     : https://prove2.me/submissions/7e749a1d-4cb5-4d60-92f6-6b3d4ae2f6f5


set_option autoImplicit false

open CookPvsNP

private theorem blocks {A B : Type} (f : A → A) (g : B → B) (e : A → B) (H : A → Prop)
    (hs : ∀ a, ¬ H a → g^[3] (e a) = e (f a))
    (n : ℕ) (a : A) (hn : ∀ i < n, ¬ H (f^[i] a)) :
    g^[3 * n] (e a) = e (f^[n] a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ, Nat.add_comm, Function.iterate_add_apply,
      ih (fun i hi => hn i (Nat.lt_succ_of_lt hi)), hs _ (hn n (Nat.lt_succ_self n))]
    rw [Function.iterate_succ_apply']

private theorem right_step {A B : Type} (M : TM B) (c : CompSecondFrame A B M.Q) :
    (c.step M).right.length ≤ c.right.length + 1 := by
  by_cases h : M.IsHalting c.source
  · simp [CompSecondFrame.step, h]
  · rcases hd : M.δ c.state c.head.2 with ⟨q, w, move⟩
    cases move <;> cases hl : c.left <;> cases hr : c.right <;>
      simp [CompSecondFrame.step, h, hd, hl, hr] <;> omega

private theorem right_run {A B : Type} (M : TM B) (c : CompSecondFrame A B M.Q) (n : ℕ) :
    ((CompSecondFrame.step M)^[n] c).right.length ≤ c.right.length + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have h := right_step M ((CompSecondFrame.step M)^[n] c)
    omega

/-- Simulate the second source machine only up to its first halt, retaining a
bound on the active right list needed for the cleanup phase. -/
theorem solution {S Γ₁ Γ₂ : Type} [Fintype Γ₁] [Fintype Γ₂]
    (j₁ : S ↪ Γ₁) (j₂ : S ↪ Γ₂) (M₁ : TM Γ₁) (M₂ : TM Γ₂)
    (c : CompSecondFrame Γ₁ Γ₂ M₂.Q) (n : ℕ)
    (hn : M₂.IsHalting (M₂.run n c.source)) :
    ∃ m ≤ n, ∃ d : CompSecondFrame Γ₁ Γ₂ M₂.Q,
      (compTM j₁ j₂ M₁ M₂).run (3 * m) c.encode = d.encode ∧
      d.source = M₂.run n c.source ∧ d.right.length ≤ c.right.length + n := by
  classical
  have hs : Function.Semiconj CompSecondFrame.source (CompSecondFrame.step M₂) M₂.step :=
    fun d => (comp_second_frame_step j₁ j₂ M₁ M₂ d).1
  have hsource (k : ℕ) : ((CompSecondFrame.step M₂)^[k] c).source = M₂.run k c.source :=
    hs.iterate_right k c
  let hex : ∃ m, M₂.IsHalting (M₂.run m c.source) := ⟨n, hn⟩
  let m := Nat.find hex
  have hm : m ≤ n := Nat.find_min' hex hn
  have hstop : M₂.IsHalting (M₂.run m c.source) := Nat.find_spec hex
  have heq : M₂.run n c.source = M₂.run m c.source := by
    conv_lhs => rw [show n = (n - m) + m by omega]
    change (M₂.step)^[(n - m) + m] c.source = _
    rw [Function.iterate_add_apply]
    exact tm_run_eq_of_halting M₂ _ hstop (n - m)
  refine ⟨m, hm, (CompSecondFrame.step M₂)^[m] c, ?_, ?_, ?_⟩
  · apply blocks (CompSecondFrame.step M₂) (compTM j₁ j₂ M₁ M₂).step
      CompSecondFrame.encode (fun d => M₂.IsHalting d.source)
      (fun d hd => (comp_second_frame_step j₁ j₂ M₁ M₂ d).2 hd)
    intro i hi
    rw [hsource]
    exact Nat.find_min hex hi
  · exact (hsource m).trans heq.symm
  · have h := right_run M₂ c m
    omega

end CookSource_comp_second_halt
namespace CookPvsNP
alias comp_second_halt := _root_.CookSource_comp_second_halt.solution
end CookPvsNP

namespace CookSource_comp_cleanup
-- Prove2me | solution 1 for CookPvsNP.comp_cleanup
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T09:08:41.787811+00:00
-- url     : https://prove2.me/submissions/bae5c035-dc7f-49ce-b2f0-2679489b8175


set_option autoImplicit false

open CookPvsNP

private theorem unpack_plain {A B : Type} (a : Option A) (b : Option B) :
    CompCell.unpack (CompCell.plain a b) = ⟨a, b, false, false, false, false, false⟩ := by
  cases a <;> cases b <;> simp [CompCell.plain, CompCell.pack, CompCell.unpack, CompCell.blank]

private theorem pack_plain {A B : Type} (a : Option A) (b : Option B) :
    CompCell.pack (⟨a, b, false, false, false, false, false⟩ : CompCell A B) =
      CompCell.plain a b := rfl

private theorem plain_none {A B : Type} :
    CompCell.plain (none : Option A) (none : Option B) = none := rfl

private theorem unpack_final {A B : Type} (b : Option B) :
    CompCell.unpack (CompCell.finalMarker (Γ₁ := A) b) =
      ⟨none, b, false, false, false, false, true⟩ := rfl

private theorem pack_final {A B : Type} (b : Option B) :
    CompCell.pack (⟨none, b, false, false, false, false, true⟩ : CompCell A B) =
      CompCell.finalMarker b := by simp [CompCell.pack, CompCell.finalMarker]

private theorem unpack_right {A B : Type} :
    CompCell.unpack (CompCell.rightMarker : Option (CompCell A B)) =
      ⟨none, none, false, false, true, false, false⟩ := rfl

private theorem unpack_none {A B : Type} :
    CompCell.unpack (none : Option (CompCell A B)) =
      ⟨none, none, false, false, false, false, false⟩ := rfl

private theorem run_add {Γ : Type} (M : TM Γ) (a b : ℕ) (c : Cfg Γ M.Q) :
    M.run (a + b) c = M.run a (M.run b c) := Function.iterate_add_apply _ _ _ _

section
variable {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B)
local notation "C" => compTM j₁ j₂ M₁ M₂

private theorem clean_step (ended : Bool) (a : Option A) (b : Option B)
    (left right : List (Option (CompCell A B))) :
    (C).step ⟨.finalClean ended, left, CompCell.plain a b, right⟩ =
      ⟨.finalClean (ended || b.isNone), CompCell.secondSymbol (if ended then none else b) :: left,
        right.headD none, right.tail⟩ := by
  cases ended <;> cases b <;>
    simp [TM.step, TM.IsHalting, compTM, unpack_plain, pack_plain, plain_none, CompCell.secondSymbol]

private theorem scan (xs : List (Option A × Option B)) (ended : Bool)
    (left : List (Option (CompCell A B))) (padding : ℕ) :
    ∃ ended', (C).run xs.length
      ⟨.finalClean ended, left,
        (xs.map (fun (p : Option A × Option B) => CompCell.plain p.1 p.2) ++ CompCell.rightMarker :: List.replicate padding none).headD none,
        (xs.map (fun (p : Option A × Option B) => CompCell.plain p.1 p.2) ++ CompCell.rightMarker :: List.replicate padding none).tail⟩ =
      ⟨.finalClean ended', ((compCleanTail ended (xs.map Prod.snd)).map CompCell.secondSymbol).reverse ++ left,
        CompCell.rightMarker, List.replicate padding none⟩ := by
  induction xs generalizing ended left with
  | nil => exact ⟨ended, rfl⟩
  | cons p xs ih =>
    obtain ⟨e, h⟩ := ih (ended || p.2.isNone)
      (CompCell.secondSymbol (if ended then none else p.2) :: left)
    refine ⟨e, ?_⟩
    simp only [List.length_cons, TM.run, Function.iterate_succ_apply, List.map_cons,
      List.cons_append, List.headD_cons, List.tail_cons]
    rw [clean_step j₁ j₂ M₁ M₂]
    simpa [TM.run, compCleanTail, List.reverse_cons, List.append_assoc] using h

private theorem return_step (b : Option B) (left right : List (Option (CompCell A B))) :
    (C).step ⟨.finalReturn, left, CompCell.secondSymbol b, right⟩ =
      ⟨.finalReturn, left.tail, left.headD none, CompCell.secondSymbol b :: right⟩ := by
  cases left <;>
    simp [TM.step, TM.IsHalting, compTM, CompCell.secondSymbol, unpack_plain, pack_plain]

private theorem return_past (xs : List (Option B)) (origin : Option (CompCell A B))
    (left right : List (Option (CompCell A B))) :
    (C).run xs.length ⟨.finalReturn, (xs.map CompCell.secondSymbol ++ [origin]).tail ++ left,
      (xs.map CompCell.secondSymbol ++ [origin]).headD none, right⟩ =
      ⟨.finalReturn, left, origin, (xs.map CompCell.secondSymbol).reverse ++ right⟩ := by
  induction xs generalizing right with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, TM.run, Function.iterate_succ_apply, List.map_cons,
      List.cons_append, List.headD_cons, List.tail_cons]
    rw [return_step j₁ j₂ M₁ M₂]
    cases xs with
    | nil => rfl
    | cons y ys =>
      simpa [TM.run, List.reverse_cons, List.append_assoc] using
        ih (CompCell.secondSymbol x :: right)

private theorem finish (b : Option B) (left : List (Option (CompCell A B)))
    (r : Option (CompCell A B)) (rs : List (Option (CompCell A B)))
    (hr : CompCell.pack (CompCell.unpack r) = r) :
    (C).run 2 ⟨.finalReturn, left, CompCell.finalMarker b, r :: rs⟩ =
      ⟨.haltAccept, left, CompCell.secondSymbol b, r :: rs⟩ := by
  simp [TM.run, Function.iterate_succ_apply, TM.step, TM.IsHalting, compTM,
    unpack_final, pack_plain, CompCell.secondSymbol, hr]

/-- Exact configuration and exact transition count of the original final cleanup. -/
private theorem cleanup_raw (c : CompSecondFrame A B M₂.Q) (hn : M₂.IsHalting c.source) :
    (C).run (2 * c.right.length + 4) c.encode = compCleanCfg c := by
  let L := (CompSecondFrame.encode (Q₁ := M₁.Q) c).left
  let origin : Option (CompCell A B) := CompCell.finalMarker c.head.2
  let out := compCleanTail c.head.2.isNone (c.right.map Prod.snd)
  have hq : c.state = M₂.qaccept ∨ c.state = M₂.qreject := hn
  have hs : (C).run 1 c.encode =
      ⟨.finalClean c.head.2.isNone, origin :: L,
        (c.right.map (fun (p : Option A × Option B) => CompCell.plain p.1 p.2) ++ CompCell.rightMarker :: List.replicate c.padding none).headD none,
        (c.right.map (fun (p : Option A × Option B) => CompCell.plain p.1 p.2) ++ CompCell.rightMarker :: List.replicate c.padding none).tail⟩ := by
    simp [TM.run, TM.step, TM.IsHalting, compTM, CompSecondFrame.encode, origin, L,
      unpack_plain, pack_final, hq]
  obtain ⟨e, hscan⟩ := scan j₁ j₂ M₁ M₂ c.right c.head.2.isNone (origin :: L) c.padding
  have hb : (C).run 1 ⟨.finalClean e, (out.map CompCell.secondSymbol).reverse ++ origin :: L,
      CompCell.rightMarker, List.replicate c.padding none⟩ =
      ⟨.finalReturn, ((out.map CompCell.secondSymbol).reverse ++ [origin]).tail ++ L,
        ((out.map CompCell.secondSymbol).reverse ++ [origin]).headD none,
        List.replicate (c.padding + 1) none⟩ := by
    cases ho : (out.map (CompCell.secondSymbol (Γ₁ := A))).reverse <;>
      simp [TM.run, TM.step, TM.IsHalting, compTM, unpack_right, List.replicate_succ]
  have hr := return_past j₁ j₂ M₁ M₂ out.reverse origin L (List.replicate (c.padding + 1) none)
  have hlen : out.length = c.right.length := by
    dsimp [out]
    generalize c.head.2.isNone = b
    induction c.right generalizing b <;> simp [compCleanTail, *]
  simp only [List.length_reverse, List.map_reverse, List.reverse_reverse, hlen] at hr
  have hf : (C).run 2 ⟨.finalReturn, L, origin,
      out.map CompCell.secondSymbol ++ List.replicate (c.padding + 1) none⟩ = compCleanCfg c := by
    cases ho : out with
    | nil =>
      have h := finish j₁ j₂ M₁ M₂ c.head.2 L none (List.replicate c.padding none) rfl
      simp [compCleanCfg, out, origin, L, List.replicate_succ, ho] at h ⊢
      exact h
    | cons x xs =>
      have hp : CompCell.pack (CompCell.unpack (CompCell.secondSymbol (Γ₁ := A) x)) =
          CompCell.secondSymbol (Γ₁ := A) x := by rw [CompCell.secondSymbol, unpack_plain, pack_plain]
      have h := finish j₁ j₂ M₁ M₂ c.head.2 L (CompCell.secondSymbol x)
        (xs.map CompCell.secondSymbol ++ List.replicate (c.padding + 1) none) hp
      simp [compCleanCfg, out, origin, L, ho] at h ⊢
      exact h
  rw [show 2 * c.right.length + 4 = 2 + (c.right.length + (1 + (c.right.length + 1))) by omega]
  unfold TM.run at hs hscan hb hr hf ⊢
  dsimp only [compTM] at hs hscan hb hr hf ⊢
  rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
    Function.iterate_add_apply, hs, hscan, hb, hr]
  exact hf

end

theorem solution {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B)
    (c : CompSecondFrame A B M₂.Q) (hn : M₂.IsHalting c.source) :
    (compTM j₁ j₂ M₁ M₂).run (2 * c.right.length + 4) c.encode = compCleanCfg c := by
  exact cleanup_raw j₁ j₂ M₁ M₂ c hn

end CookSource_comp_cleanup
namespace CookPvsNP
alias comp_cleanup := _root_.CookSource_comp_cleanup.solution
end CookPvsNP

namespace CookSource_comp_cleanup_output
-- Prove2me | solution 1 for CookPvsNP.comp_cleanup_output
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T09:08:46.839433+00:00
-- url     : https://prove2.me/submissions/3f948939-8452-4dcd-856c-6953dde4f861


set_option autoImplicit false

open CookPvsNP

private theorem clean_blanks {Γ : Type} (b : Bool) (n : ℕ) :
    compCleanTail b (List.replicate n (none : Option Γ)) = List.replicate n none := by
  induction n generalizing b <;> simp [List.replicate_succ, compCleanTail, *]

private theorem clean_word {I Γ : Type} (ι : I ↪ Γ) (w : List I) (n : ℕ) :
    compCleanTail false (w.map (some ∘ ι) ++ List.replicate n none) =
      w.map (some ∘ ι) ++ List.replicate n none := by
  induction w <;> simp [compCleanTail, clean_blanks, *]

private theorem trim_blanks {Γ : Type} (xs : List (Option Γ)) (n : ℕ) :
    ((xs ++ List.replicate n none).reverse.dropWhile Option.isNone).reverse =
      (xs.reverse.dropWhile Option.isNone).reverse := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ', ← List.append_assoc]
    simp_all

private theorem trim_word {I Γ : Type} (ι : I ↪ Γ) (w : List I) :
    ((w.map (some ∘ ι)).reverse.dropWhile Option.isNone).reverse = w.map (some ∘ ι) := by
  have h (xs : List I) : (xs.map (some ∘ ι)).dropWhile Option.isNone = xs.map (some ∘ ι) := by
    cases xs <;> simp
  rw [← List.map_reverse, h, ← List.map_reverse, List.reverse_reverse]

/-- Cleanup preserves the ordinary word output, erasing the first track and markers. -/
theorem solution {I S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (ι : I ↪ B) (M₁ : TM A) (M₂ : TM B)
    (c : CompSecondFrame A B M₂.Q) (w : List I)
    (hout : M₂.output c.source = w.map (some ∘ ι)) :
    (compTM j₁ j₂ M₁ M₂).output (compCleanCfg c) =
      w.map (some ∘ compOutputEmbedding ι) := by
  obtain ⟨n, h⟩ := comp_output_form ι M₂ c.source w hout
  have hh := congrArg Cfg.head h
  have hr := congrArg Cfg.right h
  simp only [CompSecondFrame.source, compWordCfg] at hh hr
  have hn : CompCell.secondSymbol (Γ₁ := A) (none : Option B) = none := rfl
  have hs (x : I) : CompCell.secondSymbol (Γ₁ := A) (some (ι x)) =
      some (compOutputEmbedding ι x) := by
    simp [CompCell.secondSymbol, CompCell.plain, CompCell.pack, compOutputEmbedding]
    rfl
  cases w with
  | nil =>
    simp only [List.map_nil, List.headD_nil, List.tail_nil, List.nil_append] at hh hr
    simp [TM.output, compCleanCfg, hh, hr, clean_blanks, hn, List.replicate_succ
      ]
  | cons x xs =>
    simp only [List.map_cons, List.headD_cons, List.tail_cons] at hh hr
    simp only [TM.output, compCleanCfg, hh, hr]
    rw [show ((some ∘ ι) x).isNone = false from rfl, clean_word ι xs n]
    simp only [List.map_append, List.map_replicate, hn, List.map_map, Function.comp_def, hs]
    rw [List.append_assoc, ← List.replicate_add, ← List.cons_append]
    rw [trim_blanks]
    exact trim_word (compOutputEmbedding ι) (x :: xs)

end CookSource_comp_cleanup_output
namespace CookPvsNP
alias comp_cleanup_output := _root_.CookSource_comp_cleanup_output.solution
end CookPvsNP

namespace CookSource_tm_step_tape_len
-- Prove2me | solution 1 for CookPvsNP.tm_step_tape_len
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T07:35:51.239169+00:00
-- url     : https://prove2.me/submissions/7a6aa9aa-4ee2-4906-b672-0433ab445f2d


open CookPvsNP

variable {Γ : Type} {Q : Type} (M : TM Γ)

theorem solution (c : Cfg Γ M.Q) :
    (M.step c).left.length + (M.step c).right.length ≤ c.left.length + c.right.length + 1 := by
  unfold TM.step
  split
  · exact Nat.le_add_right _ _
  · obtain ⟨q', s', h⟩ := M.δ c.state c.head
    cases h with
    | right =>
        simp only [List.length_cons, List.length_tail]
        cases c.right with
        | nil => simp
        | cons b r => omega
    | left =>
        cases c.left with
        | nil => simp only [List.length_cons]; omega
        | cons a x' =>
            simp only [List.length_cons]
            omega

end CookSource_tm_step_tape_len
namespace CookPvsNP
alias tm_step_tape_len := _root_.CookSource_tm_step_tape_len.solution
end CookPvsNP

namespace CookSource_tm_run_tape_len
-- Prove2me | solution 1 for CookPvsNP.tm_run_tape_len
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T09:01:13.639985+00:00
-- url     : https://prove2.me/submissions/d304943d-03bf-4585-b79f-17a238afe2ac


open CookPvsNP

variable {Γ : Type} {Q : Type} (M : TM Γ)

theorem solution (n : ℕ) (c : Cfg Γ M.Q) :
    (M.run n c).left.length + (M.run n c).right.length ≤ n + c.left.length + c.right.length := by
  induction n generalizing c with
  | zero => simp [TM.run]
  | succ n ih =>
      have hrun : M.run (Nat.succ n) c = M.step (M.run n c) := by
        show M.step^[Nat.succ n] c = M.step (M.step^[n] c)
        exact Function.iterate_succ_apply' M.step n c
      rw [hrun]
      have hstep := tm_step_tape_len (M := M) (M.run n c)
      have ih' := ih c
      omega

end CookSource_tm_run_tape_len
namespace CookPvsNP
alias tm_run_tape_len := _root_.CookSource_tm_run_tape_len.solution
end CookPvsNP

namespace CookSource_comp_run_bound
-- Prove2me | solution 1 for CookPvsNP.comp_run_bound
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T09:12:17.972129+00:00
-- url     : https://prove2.me/submissions/ed4707f4-afd6-4ef3-a53d-d9385ada5879


set_option autoImplicit false
open CookPvsNP

private theorem join {Γ : Type} (M : TM Γ) {a b : ℕ} {c d e : Cfg Γ M.Q}
    (h : M.run a c = d) (g : M.run b d = e) : M.run (a + b) c = e := by
  unfold TM.run at h g ⊢
  rw [Nat.add_comm, Function.iterate_add_apply, h]
  exact g

/-- The original composite machine computes the two finite source runs with linear overhead. -/
theorem solution {I S O A B : Type} [Fintype A] [Fintype B]
    (ι : I ↪ A) (j₁ : S ↪ A) (j₂ : S ↪ B) (κ : O ↪ B)
    (M₁ : TM A) (M₂ : TM B) (x : List I) (y : List S) (z : List O) (n₁ n₂ : ℕ)
    (h₁ : M₁.HaltsWithin n₁ (x.map ι))
    (o₁ : M₁.output (M₁.run n₁ (M₁.init (x.map ι))) = y.map (some ∘ j₁))
    (h₂ : M₂.HaltsWithin n₂ (y.map j₂))
    (o₂ : M₂.output (M₂.run n₂ (M₂.init (y.map j₂))) = z.map (some ∘ κ)) :
    ∃ t ≤ 20 * (x.length + n₁ + n₂ + 1),
      (compTM j₁ j₂ M₁ M₂).HaltsWithin t (x.map (compInputEmbedding ι)) ∧
      (compTM j₁ j₂ M₁ M₂).output
        ((compTM j₁ j₂ M₁ M₂).run t ((compTM j₁ j₂ M₁ M₂).init
          (x.map (compInputEmbedding ι)))) = z.map (some ∘ compOutputEmbedding κ) := by
  let C := compTM j₁ j₂ M₁ M₂
  let c := M₁.run n₁ (M₁.init (x.map ι))
  have hs := comp_setup_frame ι j₁ j₂ M₁ M₂ x
  obtain ⟨m₁, hm₁, hf⟩ := comp_first_halt j₁ j₂ M₁ M₂ (M₁.init (x.map ι)) n₁ h₁
  obtain ⟨d, hd, hds, hdr⟩ := comp_handoff j₁ j₂ M₁ M₂ c y h₁ o₁
  have hn₂ : M₂.IsHalting (M₂.run n₂ d.source) := by rw [hds]; exact h₂
  obtain ⟨m₂, hm₂, e, he, hes, her⟩ := comp_second_halt j₁ j₂ M₁ M₂ d n₂ hn₂
  have hen : M₂.IsHalting e.source := by rw [hes]; exact hn₂
  have heo : M₂.output e.source = z.map (some ∘ κ) := by rw [hes, hds]; exact o₂
  have hc := comp_cleanup j₁ j₂ M₁ M₂ e hen
  have hout := comp_cleanup_output j₁ j₂ κ M₁ M₂ e z heo
  let t := (((2 * max x.length 1 + 2) + 3 * m₁) + (2 * c.right.length + 6) +
    3 * m₂) + (2 * e.right.length + 4)
  have hrun : C.run t (C.init (x.map (compInputEmbedding ι))) = compCleanCfg e :=
    join C (join C (join C (join C hs hf) hd) he) hc
  have hr : c.right.length ≤ n₁ + x.length := by
    have h := tm_run_tape_len M₁ n₁ (M₁.init (x.map ι))
    change (M₁.run n₁ (M₁.init (x.map ι))).left.length + c.right.length ≤
      n₁ + (M₁.init (x.map ι)).left.length + (M₁.init (x.map ι)).right.length at h
    simp only [TM.init, List.length_nil, List.length_tail, List.length_map] at h
    dsimp only [c, TM.init] at h ⊢
    omega
  refine ⟨t, ?_, ?_, ?_⟩
  · have hmax : max x.length 1 ≤ x.length + 1 := by omega
    dsimp [t]
    omega
  · change C.IsHalting (C.run t (C.init (x.map (compInputEmbedding ι))))
    rw [hrun]
    exact Or.inl rfl
  · change C.output (C.run t (C.init (x.map (compInputEmbedding ι)))) = _
    rw [hrun]
    exact hout

end CookSource_comp_run_bound
namespace CookPvsNP
alias comp_run_bound := _root_.CookSource_comp_run_bound.solution
end CookPvsNP

namespace CookSource_comp_budget
-- Prove2me | solution 1 for CookPvsNP.comp_budget
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T09:12:17.276401+00:00
-- url     : https://prove2.me/submissions/60abd08f-9428-4959-ac11-1b01b1bd913d


set_option autoImplicit false

private theorem absorb (A d B : ℕ) : ∃ k, ∀ n : ℕ, A * (n + 1) ^ d + B ≤ n ^ k + k := by
  let k := A + 2 * d + A * 2 ^ d + B + 1
  refine ⟨k, ?_⟩
  intro n
  by_cases hz : n = 0
  · subst n
    simp only [Nat.zero_add, one_pow, Nat.mul_one]
    dsimp [k]
    omega
  by_cases ho : n = 1
  · subst n
    simp only [one_pow]
    dsimp [k]
    omega
  have hn : 2 ≤ n := by omega
  have hc : A ≤ n ^ A :=
    (Nat.le_of_lt (Nat.lt_two_pow_self (n := A))).trans (Nat.pow_le_pow_left hn A)
  have hb : n + 1 ≤ n ^ 2 := by nlinarith
  calc
    A * (n + 1) ^ d + B ≤ n ^ A * (n ^ 2) ^ d + B := by
      gcongr
    _ = n ^ (A + 2 * d) + B := by rw [pow_add, pow_mul]
    _ ≤ n ^ k + k := Nat.add_le_add
      (Nat.pow_le_pow_right (by omega) (by dsimp [k]; omega)) (by dsimp [k]; omega)

/-- All linear simulation overhead and the nested source budgets fit one Cook exponent. -/
theorem solution (k₁ k₂ : ℕ) : ∃ k, ∀ n : ℕ,
    20 * (n + (n ^ k₁ + k₁) + ((n + (n ^ k₁ + k₁) + 1) ^ k₂ + k₂) + 1) ≤
      n ^ k + k := by
  let a := k₁ + 3
  let d := (k₁ + 1) * (k₂ + 1)
  obtain ⟨k, hk⟩ := absorb (20 * (a + a ^ k₂)) d (20 * k₂)
  refine ⟨k, fun n => le_trans ?_ (hk n)⟩
  have hn : 0 < n + 1 := by omega
  have hd : k₁ + 1 ≤ d := by dsimp [d]; nlinarith
  have hd₂ : (k₁ + 1) * k₂ ≤ d := by dsimp [d]; nlinarith
  have hpow : 1 ≤ (n + 1) ^ (k₁ + 1) := by
    have : 0 < (n + 1) ^ (k₁ + 1) := by positivity
    omega
  have hp₁ : n ≤ (n + 1) ^ (k₁ + 1) := by
    calc
      n ≤ n + 1 := by omega
      _ = (n + 1) ^ 1 := by simp
      _ ≤ _ := Nat.pow_le_pow_right hn (by omega)
  have hp₂ : n ^ k₁ ≤ (n + 1) ^ (k₁ + 1) :=
    (Nat.pow_le_pow_left (Nat.le_succ n) k₁).trans (Nat.pow_le_pow_right hn (by omega))
  have hbase : n + (n ^ k₁ + k₁) + 1 ≤ a * (n + 1) ^ (k₁ + 1) := by
    dsimp [a]
    nlinarith
  have h₁ : n + (n ^ k₁ + k₁) + 1 ≤ a * (n + 1) ^ d :=
    hbase.trans (Nat.mul_le_mul_left a (Nat.pow_le_pow_right hn hd))
  have h₂ : (n + (n ^ k₁ + k₁) + 1) ^ k₂ ≤ a ^ k₂ * (n + 1) ^ d := by
    calc
      _ ≤ (a * (n + 1) ^ (k₁ + 1)) ^ k₂ := Nat.pow_le_pow_left hbase k₂
      _ = a ^ k₂ * (n + 1) ^ ((k₁ + 1) * k₂) := by rw [mul_pow, ← pow_mul]
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn hd₂)
  nlinarith

end CookSource_comp_budget
namespace CookPvsNP
alias comp_budget := _root_.CookSource_comp_budget.solution
end CookPvsNP

namespace CookSource_tm_output_length_le
-- Prove2me | solution 1 for CookPvsNP.tm_output_length_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T10:02:24.151447+00:00
-- url     : https://prove2.me/submissions/72044d12-6493-45aa-b870-6adc677a0c62


open CookPvsNP

variable {Γ : Type} {Q : Type} (M : TM Γ)

theorem solution (n : ℕ) (w : List Γ) :
    (M.output (M.run n (M.init w))).length ≤ n + w.length + 1 := by
  have hdrop : ∀ c : Cfg Γ M.Q, ((c.head :: c.right).reverse.dropWhile Option.isNone).length
      ≤ 1 + c.right.length := by
    intro c
    have h := List.length_dropWhile_le Option.isNone (c.head :: c.right).reverse
    have h' : (c.head :: c.right).reverse.length = c.right.length + 1 := by
      simp only [List.length_reverse, List.length_cons]
    omega
  have hout : ∀ c : Cfg Γ M.Q, (M.output c).length ≤ 1 + c.right.length := by
    intro c
    have h2 := hdrop c
    simpa [TM.output, add_comm] using h2
  have hinit : (M.init w).left.length + (M.init w).right.length ≤ w.length := by
    simp [TM.init]
  have hrun := tm_run_tape_len (M := M) n (M.init w)
  have hc := hout (M.run n (M.init w))
  omega

end CookSource_tm_output_length_le
namespace CookPvsNP
alias tm_output_length_le := _root_.CookSource_tm_output_length_le.solution
end CookPvsNP

namespace CookSource_tm_compose_poly_witness
-- Prove2me | solution 1 for CookPvsNP.tm_compose_poly_witness
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T09:30:07.080907+00:00
-- url     : https://prove2.me/submissions/bf78f3c2-f92b-4103-9e03-b431cc9fcb99


set_option autoImplicit false
open CookPvsNP

theorem solution
    {Sym₁ Sym₂ Sym₃ Γ₁ Γ₂ : Type}
    [Fintype Γ₁] [Fintype Γ₂]
    (ι₁ : Sym₁ ↪ Γ₁) (ι₂₁ : Sym₂ ↪ Γ₁) (M₁ : TM Γ₁) (k₁ : ℕ)
    (ι₂₂ : Sym₂ ↪ Γ₂) (ι₃ : Sym₃ ↪ Γ₂) (M₂ : TM Γ₂) (k₂ : ℕ)
    (f : List Sym₁ → List Sym₂) (g : List Sym₂ → List Sym₃)
    (h₁ : ∀ x : List Sym₁,
      M₁.HaltsWithin (x.length ^ k₁ + k₁) (x.map ι₁) ∧
      M₁.output (M₁.run (x.length ^ k₁ + k₁) (M₁.init (x.map ι₁))) =
        (f x).map (some ∘ ι₂₁))
    (h₂ : ∀ y : List Sym₂,
      M₂.HaltsWithin (y.length ^ k₂ + k₂) (y.map ι₂₂) ∧
      M₂.output (M₂.run (y.length ^ k₂ + k₂) (M₂.init (y.map ι₂₂))) =
        (g y).map (some ∘ ι₃)) :
    ∃ (Γ : Type) (_ : Fintype Γ) (j₁ : Sym₁ ↪ Γ) (j₃ : Sym₃ ↪ Γ)
      (M : TM Γ) (k : ℕ),
      ∀ x : List Sym₁,
        M.HaltsWithin (x.length ^ k + k) (x.map j₁) ∧
        M.output (M.run (x.length ^ k + k) (M.init (x.map j₁))) =
          (g (f x)).map (some ∘ j₃) := by
  obtain ⟨k, hk⟩ := CookPvsNP.comp_budget k₁ k₂
  let C := compTM ι₂₁ ι₂₂ M₁ M₂
  refine ⟨CompCell Γ₁ Γ₂, inferInstance, compInputEmbedding ι₁, compOutputEmbedding ι₃, C, k, ?_⟩
  intro x
  obtain ⟨t, ht, hhalt, hout⟩ := comp_run_bound ι₁ ι₂₁ ι₂₂ ι₃ M₁ M₂ x (f x) (g (f x))
    (x.length ^ k₁ + k₁) ((f x).length ^ k₂ + k₂) (h₁ x).1 (h₁ x).2 (h₂ (f x)).1 (h₂ (f x)).2
  have hlen := tm_output_length_le M₁ (x.length ^ k₁ + k₁) (x.map ι₁)
  rw [(h₁ x).2] at hlen
  simp only [List.length_map] at hlen
  have htk : t ≤ x.length ^ k + k := by
    apply le_trans ht
    apply le_trans _ (hk x.length)
    gcongr
    omega
  have hrun : C.run (x.length ^ k + k) (C.init (x.map (compInputEmbedding ι₁))) =
      C.run t (C.init (x.map (compInputEmbedding ι₁))) := by
    conv_lhs => rw [← Nat.sub_add_cancel htk]
    change C.step^[(x.length ^ k + k - t) + t] _ = _
    rw [Function.iterate_add_apply]
    exact tm_run_eq_of_halting C _ hhalt _
  constructor
  · change C.IsHalting (C.run (x.length ^ k + k) (C.init (x.map (compInputEmbedding ι₁))))
    rw [hrun]
    exact hhalt
  · rw [hrun]
    exact hout

end CookSource_tm_compose_poly_witness
namespace CookPvsNP
alias tm_compose_poly_witness := _root_.CookSource_tm_compose_poly_witness.solution
end CookPvsNP

namespace CookSource_polyTimeComputable_comp
-- Prove2me | solution 1 for CookPvsNP.polyTimeComputable_comp
-- status  : ACCEPTED   (prove)
-- author  : @Sneed
-- created : 2026-09-30T17:10:00.965578+00:00
-- url     : https://prove2.me/submissions/de1dedae-ce6d-4be8-bd57-d7739fe76441


set_option autoImplicit false

open CookPvsNP

theorem solution {Sym₁ Sym₂ Sym₃ : Type}
    (f : List Sym₁ → List Sym₂) (g : List Sym₂ → List Sym₃)
    (hf : CookPvsNP.PolyTimeComputable f) (hg : CookPvsNP.PolyTimeComputable g) :
    CookPvsNP.PolyTimeComputable (g ∘ f) := by
  rcases hf with ⟨Γ₁, hfin₁, ι₁, ι₂₁, M₁, k₁, h₁⟩
  rcases hg with ⟨Γ₂, hfin₂, ι₂₂, ι₃, M₂, k₂, h₂⟩
  let : Fintype Γ₁ := hfin₁
  let : Fintype Γ₂ := hfin₂
  exact CookPvsNP.tm_compose_poly_witness ι₁ ι₂₁ M₁ k₁ ι₂₂ ι₃ M₂ k₂ f g h₁ h₂

end CookSource_polyTimeComputable_comp
namespace CookPvsNP
alias polyTimeComputable_comp := _root_.CookSource_polyTimeComputable_comp.solution
end CookPvsNP

namespace CookSource_polyReducible_trans
-- Prove2me | solution 1 for CookPvsNP.polyReducible_trans
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T10:20:29.608883+00:00
-- url     : https://prove2.me/submissions/90543bc3-4721-4e49-9c26-bf5df8ad2503


open CookPvsNP

theorem solution {Sym₁ Sym₂ Sym₃ : Type} {L₁ : Lang Sym₁} {L₂ : Lang Sym₂} {L₃ : Lang Sym₃}
    (h₁₂ : PolyReducible L₁ L₂) (h₂₃ : PolyReducible L₂ L₃) : PolyReducible L₁ L₃ := by
  rcases h₁₂ with ⟨f, hf, hfm⟩
  rcases h₂₃ with ⟨g, hg, hgm⟩
  refine ⟨g ∘ f, polyTimeComputable_comp f g hf hg, ?_⟩
  intro x
  exact Iff.trans (hfm x) (hgm (f x))

end CookSource_polyReducible_trans
namespace CookPvsNP
alias polyReducible_trans := _root_.CookSource_polyReducible_trans.solution
end CookPvsNP

namespace CookSource_polynomial_absorb
-- Prove2me | solution 1 for CookPvsNP.polynomial_absorb
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:28:08.495978+00:00
-- url     : https://prove2.me/submissions/c2e1c7c8-baae-4cff-bab6-7e1f337912b1


set_option autoImplicit false

theorem solution (A d B : ℕ) : ∃ k, ∀ n : ℕ, A * (n + 1) ^ d + B ≤ n ^ k + k := by
  let k := A + 2 * d + A * 2 ^ d + B + 1
  refine ⟨k, ?_⟩
  intro n
  by_cases hz : n = 0
  · subst n
    simp only [Nat.zero_add, one_pow, Nat.mul_one]
    dsimp [k]
    omega
  by_cases ho : n = 1
  · subst n
    simp only [one_pow]
    dsimp [k]
    omega
  have hn : 2 ≤ n := by omega
  have hc : A ≤ n ^ A :=
    (Nat.le_of_lt (Nat.lt_two_pow_self (n := A))).trans (Nat.pow_le_pow_left hn A)
  have hb : n + 1 ≤ n ^ 2 := by nlinarith
  calc
    A * (n + 1) ^ d + B ≤ n ^ A * (n ^ 2) ^ d + B := by gcongr
    _ = n ^ (A + 2 * d) + B := by rw [pow_add, pow_mul]
    _ ≤ n ^ k + k := Nat.add_le_add
      (Nat.pow_le_pow_right (by omega) (by dsimp [k]; omega)) (by dsimp [k]; omega)

end CookSource_polynomial_absorb
namespace CookPvsNP
alias polynomial_absorb := _root_.CookSource_polynomial_absorb.solution
end CookPvsNP

namespace CookSource_stack_transfer
-- Prove2me | solution 1 for CookPvsNP.stack_transfer
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:43:33.682198+00:00
-- url     : https://prove2.me/submissions/d53bebfc-d831-4207-83b8-067d63206803


set_option autoImplicit false
open CookPvsNP

private theorem transfer {K A : Type} [DecidableEq K] (src : K) (targets : K → Bool)
    (w : List A) (s : K → List A) (hs : s src = w) :
    (transferProg src targets).Exec s (transferStore src targets s) (3 * w.length + 1) := by
  induction w generalizing s with
  | nil =>
    have hf : transferStore src targets s = s := by
      funext k
      by_cases hk : k = src <;> simp [transferStore, hk, hs]
    rw [hf]
    exact .loopFalse (by simp [hs])
  | cons a w ih =>
    let s' := StackProg.applyAct (transferAct src targets) s
    have hs' : s' src = w := by simp [s', StackProg.applyAct, transferAct, hs, StackAct.apply]
    have hout : transferStore src targets s' = transferStore src targets s := by
      funext k
      by_cases hk : k = src
      · simp [transferStore, hk]
      · cases ht : targets k <;>
          simp [transferStore, hk, ht, hs', s', StackProg.applyAct, transferAct, hs,
            StackAct.apply, List.reverse_cons, List.append_assoc]
    have h := StackProg.Exec.loopTrue (by simp [hs])
      (StackProg.Exec.act (transferAct src targets) s) (ih s' hs')
    rw [hout] at h
    convert h using 1 <;> simp [transferProg]
    omega

theorem solution {K A : Type} [DecidableEq K] (src : K) (targets : K → Bool)
    (s : K → List A) :
    (transferProg src targets).Exec s (transferStore src targets s) (3 * (s src).length + 1) := by
  exact transfer src targets (s src) s rfl

end CookSource_stack_transfer
namespace CookPvsNP
alias stack_transfer := _root_.CookSource_stack_transfer.solution
end CookPvsNP

namespace CookSource_stack_basic_macros
-- Prove2me | solution 1 for CookPvsNP.stack_basic_macros
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:43:36.650992+00:00
-- url     : https://prove2.me/submissions/5bd9c107-ba8e-4a76-ba3c-3e402e22a41b


set_option autoImplicit false
open CookPvsNP

theorem solution {K A : Type} [DecidableEq K] (k : K) (s : K → List A) :
    (∀ a : A, (pushProg k a).Exec s (Function.update s k (a :: s k)) 1) ∧
    (popProg k).Exec s (Function.update s k (s k).tail) 1 ∧
    (clearProg k).Exec s (Function.update s k []) (3 * (s k).length + 1) := by
  constructor
  · intro a
    have he : StackProg.applyAct (fun _ j => if j = k then .push a else .keep) s =
        Function.update s k (a :: s k) := by
      funext j; by_cases h : j = k <;> simp [StackProg.applyAct, h, StackAct.apply]
    simpa [pushProg, he] using StackProg.Exec.act (fun _ j => if j = k then .push a else .keep) s
  constructor
  · have he : StackProg.applyAct (fun _ j => if j = k then .pop else .keep) s =
        Function.update s k (s k).tail := by
      funext j; by_cases h : j = k <;> simp [StackProg.applyAct, h, StackAct.apply]
    simpa [popProg, he] using StackProg.Exec.act (fun _ j => if j = k then .pop else .keep) s
  · have he : transferStore k (fun _ => false) s = Function.update s k [] := by
      funext j; by_cases h : j = k <;> simp [transferStore, h]
    simpa [clearProg, he] using stack_transfer k (fun _ => false) s

end CookSource_stack_basic_macros
namespace CookPvsNP
alias stack_basic_macros := _root_.CookSource_stack_basic_macros.solution
end CookPvsNP

namespace CookSource_stack_bounded_loop
-- Prove2me | solution 1 for CookPvsNP.stack_bounded_loop
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:24:46.623795+00:00
-- url     : https://prove2.me/submissions/8d92fc92-646e-4a11-b967-1243775a02f3


set_option autoImplicit false
open CookPvsNP

private theorem loop_exec {K A : Type} (test : (K → Option A) → Bool) (p : StackProg K A)
    (n : ℕ) (s : ℕ → K → List A) (cost : ℕ → ℕ)
    (hg : ∀ i < n, test (fun k => (s i k).head?) = true)
    (he : test (fun k => (s n k).head?) = false)
    (hb : ∀ i < n, p.Exec (s i) (s (i + 1)) (cost i)) :
    (StackProg.loop test p).Exec (s 0) (s n)
      ((∑ i ∈ Finset.range n, (cost i + 2)) + 1) := by
  induction n generalizing s cost with
  | zero => simpa using StackProg.Exec.loopFalse he
  | succ n ih =>
    have hh := ih (fun i => s (i + 1)) (fun i => cost (i + 1))
      (fun i hi => hg (i + 1) (by omega)) he (fun i hi => hb (i + 1) (by omega))
    have hx := StackProg.Exec.loopTrue (hg 0 (by omega)) (hb 0 (by omega)) hh
    convert hx using 1
    rw [Finset.sum_range_succ']
    omega

theorem solution {K A : Type} (test : (K → Option A) → Bool) (p : StackProg K A)
    (n : ℕ) (s : ℕ → K → List A) (cost : ℕ → ℕ) (B : ℕ)
    (hg : ∀ i < n, test (fun k => (s i k).head?) = true)
    (he : test (fun k => (s n k).head?) = false)
    (hb : ∀ i < n, p.Exec (s i) (s (i + 1)) (cost i))
    (hc : ∀ i < n, cost i ≤ B) :
    ∃ t ≤ n * (B + 2) + 1, (StackProg.loop test p).Exec (s 0) (s n) t := by
  refine ⟨(∑ i ∈ Finset.range n, (cost i + 2)) + 1, ?_, loop_exec test p n s cost hg he hb⟩
  have h : (∑ i ∈ Finset.range n, (cost i + 2)) ≤ ∑ _i ∈ Finset.range n, (B + 2) :=
    Finset.sum_le_sum (fun i hi => Nat.add_le_add_right (hc i (Finset.mem_range.mp hi)) 2)
  simpa using Nat.add_le_add_right h 1

end CookSource_stack_bounded_loop
namespace CookPvsNP
alias stack_bounded_loop := _root_.CookSource_stack_bounded_loop.solution
end CookPvsNP

namespace CookSource_stack_cleanup
-- Prove2me | solution 1 for CookPvsNP.stack_cleanup
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T12:09:35.876276+00:00
-- url     : https://prove2.me/submissions/cd0cb1e7-1813-4cb1-ad0f-0517614b4754


set_option autoImplicit false
open CookPvsNP

section
variable {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q]
  [DecidableEq K] [DecidableEq A] [DecidableEq Q]
  (P : StackMachine K A Q) (ki ko : K)
local notation "M" => stackTM P ki ko

private theorem scan (r : List (StackCol K A)) (L : List (Option (StackSym K A))) :
    (M).run r.length
      ⟨.clean, L, (r.map (some ∘ StackSym.work)).headD none,
        (r.map (some ∘ StackSym.work)).tail⟩ =
      ⟨.clean, (r.map (fun x => (x ko).map StackSym.output)).reverse ++ L, none, []⟩ := by
  induction r generalizing L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, TM.run, Function.iterate_succ_apply, List.map_cons,
      List.headD_cons, List.tail_cons]
    have hs : (M).step ⟨.clean, L, some (.work x), xs.map (some ∘ StackSym.work)⟩ =
        ⟨.clean, (x ko).map StackSym.output :: L,
          (xs.map (some ∘ StackSym.work)).headD none,
          (xs.map (some ∘ StackSym.work)).tail⟩ := by
      simp [TM.step, TM.IsHalting, stackTM]
    refine (congrArg ((M).step^[xs.length]) hs).trans ?_
    simpa [TM.run, List.reverse_cons, List.append_assoc] using
      ih ((x ko).map StackSym.output :: L)

private theorem back (r : List (Option A)) (R : List (Option (StackSym K A))) :
    (M).run r.length
      ⟨.cleanBack, (r.map (Option.map StackSym.output) ++ [some (StackSym.origin (K := K) (A := A))]).tail,
        (r.map (Option.map StackSym.output) ++ [some (StackSym.origin (K := K) (A := A))]).headD none, R⟩ =
      ⟨.cleanBack, [], some (StackSym.origin (K := K) (A := A)), (r.map (Option.map StackSym.output)).reverse ++ R⟩ := by
  induction r generalizing R with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, TM.run, Function.iterate_succ_apply, List.map_cons,
      List.cons_append, List.headD_cons, List.tail_cons]
    have hs : (M).step
        ⟨.cleanBack, xs.map (Option.map StackSym.output) ++ [some (StackSym.origin (K := K) (A := A))],
          x.map StackSym.output, R⟩ =
        ⟨.cleanBack, (xs.map (Option.map StackSym.output) ++ [some (StackSym.origin (K := K) (A := A))]).tail,
          (xs.map (Option.map StackSym.output) ++ [some (StackSym.origin (K := K) (A := A))]).headD none,
          x.map StackSym.output :: R⟩ := by
      cases x <;> cases xs <;> simp [TM.step, TM.IsHalting, stackTM]
    refine (congrArg ((M).step^[xs.length]) hs).trans ?_
    simpa [TM.run, List.reverse_cons, List.append_assoc] using ih (x.map StackSym.output :: R)

end

theorem solution {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q]
    [DecidableEq K] [DecidableEq A] [DecidableEq Q]
    (P : StackMachine K A Q) (ki ko : K) (q : Q)
    (x : StackCol K A) (xs : List (StackCol K A)) (hq : P.done q = true) :
    let out := (x :: xs).map (fun v => (v ko).map (StackSym.output (K := K))) ++ [none]
    (stackTM P ki ko).run (2 * (x :: xs).length + 2) (stackFrame q (x :: xs)) =
      ⟨.accept, [some (StackSym.origin (K := K) (A := A))], out.headD none, out.tail⟩ := by
  let M := stackTM P ki ko
  let ys := (x :: xs).map (fun v => v ko)
  let out := ys.map (Option.map (StackSym.output (K := K))) ++ [none]
  have hfirst : (M).run 1 (stackFrame q (x :: xs)) =
      ⟨.clean, (x ko).map StackSym.output :: [some (StackSym.origin (K := K) (A := A))],
        (xs.map (some ∘ StackSym.work)).headD none,
        (xs.map (some ∘ StackSym.work)).tail⟩ := by
    simp [M, TM.run, TM.step, TM.IsHalting, stackTM, stackFrame, hq]
  have hr := scan P ki ko xs [(x ko).map StackSym.output, some (StackSym.origin (K := K) (A := A))]
  have hb : (M).run 1
      ⟨.clean, (ys.map (Option.map StackSym.output)).reverse ++ [some (StackSym.origin (K := K) (A := A))], none, []⟩ =
      ⟨.cleanBack,
        (ys.reverse.map (Option.map StackSym.output) ++ [some (StackSym.origin (K := K) (A := A))]).tail,
        (ys.reverse.map (Option.map StackSym.output) ++ [some (StackSym.origin (K := K) (A := A))]).headD none,
        [none]⟩ := by
    cases h : ys.reverse <;> simp [M, TM.run, TM.step, TM.IsHalting, stackTM, ← List.map_reverse, h]
  have hl := back P ki ko ys.reverse [none]
  have hf : (M).run 1 ⟨.cleanBack, [], some (StackSym.origin (K := K) (A := A)), out⟩ =
      ⟨.accept, [some (StackSym.origin (K := K) (A := A))], out.headD none, out.tail⟩ := by
    simp [M, TM.run, TM.step, TM.IsHalting, stackTM]
  have hr' : (M).run xs.length ((M).run 1 (stackFrame q (x :: xs))) =
      ⟨.clean, (ys.map (Option.map StackSym.output)).reverse ++ [some (StackSym.origin (K := K) (A := A))], none, []⟩ := by
    exact (congrArg ((M).run xs.length) hfirst).trans
      (by simpa [M, ys, List.reverse_cons, List.append_assoc, List.map_map, Function.comp_def] using hr)
  simp only [List.length_reverse, List.map_reverse, List.reverse_reverse] at hl
  simp only [List.map_reverse] at hb
  have hn : ys.length = (x :: xs).length := List.length_map _
  rw [hn] at hl
  have h2 := (congrArg ((M).run 1) hr').trans hb
  have h3 := (congrArg ((M).run (x :: xs).length) h2).trans hl
  have h4 := (congrArg ((M).run 1) h3).trans hf
  have ht : 1 + ((x :: xs).length + (1 + (xs.length + 1))) = 2 * (x :: xs).length + 2 := by simp; omega
  have hmain : (M).run (2 * (x :: xs).length + 2) (stackFrame q (x :: xs)) =
      ⟨.accept, [some (StackSym.origin (K := K) (A := A))], out.headD none, out.tail⟩ := by
    unfold TM.run at h4 ⊢
    dsimp only [M, stackTM] at h4 ⊢
    rw [← ht, Function.iterate_add_apply, Function.iterate_add_apply,
      Function.iterate_add_apply, Function.iterate_add_apply]
    exact h4
  simpa only [out, ys, List.map_map, Function.comp_def] using hmain

end CookSource_stack_cleanup
namespace CookPvsNP
alias stack_cleanup := _root_.CookSource_stack_cleanup.solution
end CookPvsNP

namespace CookSource_stack_column_laws
-- Prove2me | solution 1 for CookPvsNP.stack_column_laws
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T11:22:30.882049+00:00
-- url     : https://prove2.me/submissions/154eaf76-a519-42a6-a3d9-807ccfe07a8c


set_option autoImplicit false
open CookPvsNP

private theorem forward_length {K A : Type} (a : K → StackAct A)
    (c : StackCol K A) (r : List (StackCol K A)) :
    (stackForward a c r).length = r.length + 1 := by
  induction r generalizing c with
  | nil => rfl
  | cons x xs ih => simp [stackForward, ih]

private theorem forward_projection {K A : Type} (a : K → StackAct A)
    (c : StackCol K A) (r : List (StackCol K A)) (k : K)
    (hc : a k = .keep ∨ a k = .pop → c k = none) :
    (stackForward a c r).map (fun (v : StackCol K A) => v k) =
      match a k with
      | .push _ => c k :: r.map (fun (v : StackCol K A) => v k)
      | _ => r.map (fun (v : StackCol K A) => v k) ++ [none] := by
  induction r generalizing c with
  | nil => cases h : a k <;> simp [stackForward, hc, h]
  | cons x xs ih =>
    have hn : a k = .keep ∨ a k = .pop → stackPushNext a x k = none := by
      rintro (h | h) <;> simp [stackPushNext, h]
    simp only [stackForward, List.map_cons, ih _ hn]
    cases h : a k <;> simp [stackPushCell, stackPushNext, h]

private theorem backward_length {K A : Type} (a : K → StackAct A)
    (r : List (StackCol K A)) : (stackBackward a r).length = r.length := by
  induction r with
  | nil => rfl
  | cons x xs ih => simp [stackBackward, ih]

private theorem backward_projection {K A : Type} (a : K → StackAct A)
    (r : List (StackCol K A)) (k : K) :
    (stackBackward a r).map (fun (v : StackCol K A) => v k) =
      match a k with
      | .pop => (r.map (fun (v : StackCol K A) => v k)).tail ++ List.replicate (min 1 r.length) none
      | _ => r.map (fun (v : StackCol K A) => v k) := by
  induction r with
  | nil => cases a k <;> rfl
  | cons x xs ih =>
    simp only [stackBackward, List.map_cons, ih]
    cases h : a k with
    | keep => simp [stackPopCell, h]
    | push b => simp [stackPopCell, h]
    | pop => cases xs with
      | nil => simp [stackPopCell, h, stackZero]
      | cons y ys => simp [stackPopCell, h]

theorem solution {K A : Type} (a : K → StackAct A)
    (r : List (StackCol K A)) (k : K) :
    let r' := stackBackward a (stackForward a (stackPushCarry a) r)
    r'.length = r.length + 1 ∧
    r'.map (fun (v : StackCol K A) => v k) =
      match a k with
      | .keep => r.map (fun (v : StackCol K A) => v k) ++ [none]
      | .push b => some b :: r.map (fun (x : StackCol K A) => x k)
      | .pop => (r.map (fun (v : StackCol K A) => v k) ++ [none]).tail ++ [none] := by
  dsimp only
  constructor
  · rw [backward_length, forward_length]
  · have hc : a k = .keep ∨ a k = .pop → stackPushCarry a k = none := by
      rintro (h | h) <;> simp [stackPushCarry, h]
    rw [backward_projection, forward_projection _ _ _ _ hc, forward_length]
    cases h : a k <;> simp [h, stackPushCarry]

end CookSource_stack_column_laws
namespace CookPvsNP
alias stack_column_laws := _root_.CookSource_stack_column_laws.solution
end CookPvsNP

namespace CookSource_stack_consume
-- Prove2me | solution 1 for CookPvsNP.stack_consume
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:43:38.020788+00:00
-- url     : https://prove2.me/submissions/0f0dc773-b60c-4aab-801d-ce2f57198cf8


set_option autoImplicit false
open CookPvsNP

private theorem consume {K A : Type} [DecidableEq K] (src : K) (targets : K → Bool)
    (w : List A) (s : K → List A) (hs : s src = w) :
    (consumeProg src targets).Exec s (consumeStore src targets s) (3 * w.length + 1) := by
  induction w generalizing s with
  | nil =>
    have hf : consumeStore src targets s = s := by
      funext k
      by_cases hk : k = src <;> simp [consumeStore, hk, hs]
    rw [hf]
    exact .loopFalse (by simp [hs])
  | cons a w ih =>
    let s' := StackProg.applyAct (consumeAct src targets) s
    have hs' : s' src = w := by simp [s', StackProg.applyAct, consumeAct, hs, StackAct.apply]
    have hout : consumeStore src targets s' = consumeStore src targets s := by
      funext k
      by_cases hk : k = src
      · simp [consumeStore, hk]
      · cases ht : targets k <;>
          simp [consumeStore, hk, ht, hs', s', StackProg.applyAct, consumeAct, hs,
            StackAct.apply, List.drop_tail]
    have h := StackProg.Exec.loopTrue (by simp [hs])
      (StackProg.Exec.act (consumeAct src targets) s) (ih s' hs')
    rw [hout] at h
    convert h using 1 <;> simp [consumeProg]
    omega

theorem solution {K A : Type} [DecidableEq K] (src : K) (targets : K → Bool)
    (s : K → List A) :
    (consumeProg src targets).Exec s (consumeStore src targets s) (3 * (s src).length + 1) := by
  exact consume src targets (s src) s rfl

end CookSource_stack_consume
namespace CookPvsNP
alias stack_consume := _root_.CookSource_stack_consume.solution
end CookPvsNP

namespace CookSource_stack_copy
-- Prove2me | solution 1 for CookPvsNP.stack_copy
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:43:35.468368+00:00
-- url     : https://prove2.me/submissions/eaa1571c-9766-44c6-ba81-c3608b6a51b8


set_option autoImplicit false
open CookPvsNP

theorem solution {K A : Type} [DecidableEq K] (src dst scratch : K)
    (hsd : src ≠ dst) (hst : src ≠ scratch) (hdt : dst ≠ scratch)
    (s : K → List A) (he : s scratch = []) :
    (copyProg src dst scratch).Exec s
      (Function.update s dst (s src ++ s dst)) (6 * (s src).length + 3) := by
  let targets₁ := fun k => decide (k = scratch)
  let targets₂ := fun k => decide (k = src ∨ k = dst)
  let mid := transferStore src targets₁ s
  have hs : mid scratch = (s src).reverse := by
    simp [mid, transferStore, targets₁, Ne.symm hst, he]
  have hf : transferStore scratch targets₂ mid = Function.update s dst (s src ++ s dst) := by
    funext k
    by_cases hk : k = src
    · subst k
      simp [transferStore, targets₂, hs, mid, targets₁, hst, hsd]
    by_cases hk' : k = dst
    · subst k
      simp [transferStore, targets₂, hs, mid, targets₁, hdt, Ne.symm hsd]
    by_cases hk'' : k = scratch
    · subst k
      simp [transferStore, Function.update_of_ne (Ne.symm hdt), he]
    · simp [transferStore, targets₂, mid, targets₁, hk, hk', hk'']
  have hp := StackProg.Exec.seq (stack_transfer src targets₁ s)
    (stack_transfer scratch targets₂ mid)
  rw [hf] at hp
  convert hp using 1 <;> first | rfl | (simp only [hs, List.length_reverse]; omega)

end CookSource_stack_copy
namespace CookPvsNP
alias stack_copy := _root_.CookSource_stack_copy.solution
end CookPvsNP

namespace CookSource_stack_sweep_right
-- Prove2me | solution 1 for CookPvsNP.stack_sweep_right
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T11:47:04.332509+00:00
-- url     : https://prove2.me/submissions/4e9ffba1-4372-48bd-b1e7-111c9c991dde


set_option autoImplicit false
open CookPvsNP

theorem solution {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q]
    [DecidableEq K] [DecidableEq A] [DecidableEq Q]
    (P : StackMachine K A Q) (ki ko : K) (q : Q) (a : K → StackAct A)
    (c : StackCol K A) (r : List (StackCol K A)) (L : List (Option (StackSym K A))) :
    (stackTM P ki ko).run r.length
      ⟨.scanR q a c, L, (r.map (some ∘ StackSym.work)).headD none,
        (r.map (some ∘ StackSym.work)).tail⟩ =
      ⟨.scanR q a (stackRight a c r).1,
        ((stackRight a c r).2.map (some ∘ StackSym.work)).reverse ++ L, none, []⟩ := by
  induction r generalizing c L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, TM.run, Function.iterate_succ_apply, List.map_cons,
      List.headD_cons, List.tail_cons]
    have hs : (stackTM P ki ko).step
        ⟨.scanR q a c, L, some (.work x), xs.map (some ∘ StackSym.work)⟩ =
        ⟨.scanR q a (stackPushNext a x), some (.work (stackPushCell a c x)) :: L,
          (xs.map (some ∘ StackSym.work)).headD none,
          (xs.map (some ∘ StackSym.work)).tail⟩ := by
      simp [TM.step, TM.IsHalting, stackTM]
    refine (congrArg ((stackTM P ki ko).step^[xs.length]) hs).trans ?_
    simpa [TM.run, stackRight, List.reverse_cons, List.append_assoc] using
      ih (stackPushNext a x) (some (.work (stackPushCell a c x)) :: L)

end CookSource_stack_sweep_right
namespace CookPvsNP
alias stack_sweep_right := _root_.CookSource_stack_sweep_right.solution
end CookPvsNP

namespace CookSource_stack_sweep_left
-- Prove2me | solution 1 for CookPvsNP.stack_sweep_left
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T11:47:05.06827+00:00
-- url     : https://prove2.me/submissions/c012535d-a2a5-4f90-8be7-36cb5b86f0e2


set_option autoImplicit false
open CookPvsNP

theorem solution {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q]
    [DecidableEq K] [DecidableEq A] [DecidableEq Q]
    (P : StackMachine K A Q) (ki ko : K) (q : Q) (a : K → StackAct A)
    (c : StackCol K A) (r : List (StackCol K A)) (R : List (Option (StackSym K A))) :
    (stackTM P ki ko).run r.length
      ⟨.scanL q a c,
        (r.map (some ∘ StackSym.work) ++ [some (StackSym.origin (K := K) (A := A))]).tail,
        (r.map (some ∘ StackSym.work) ++ [some (StackSym.origin (K := K) (A := A))]).headD none, R⟩ =
      ⟨.scanL q a (stackLeft a c r).1, [], some (StackSym.origin (K := K) (A := A)),
        ((stackLeft a c r).2.map (some ∘ StackSym.work)).reverse ++ R⟩ := by
  induction r generalizing c R with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, TM.run, Function.iterate_succ_apply, List.map_cons,
      List.cons_append, List.headD_cons, List.tail_cons]
    have hs : (stackTM P ki ko).step
        ⟨.scanL q a c, xs.map (some ∘ StackSym.work) ++ [some (StackSym.origin (K := K) (A := A))], some (.work x), R⟩ =
        ⟨.scanL q a x, (xs.map (some ∘ StackSym.work) ++ [some (StackSym.origin (K := K) (A := A))]).tail,
          (xs.map (some ∘ StackSym.work) ++ [some (StackSym.origin (K := K) (A := A))]).headD none,
          some (.work (stackPopCell a c x)) :: R⟩ := by
      cases xs <;> simp [TM.step, TM.IsHalting, stackTM]
    refine (congrArg ((stackTM P ki ko).step^[xs.length]) hs).trans ?_
    simpa [TM.run, stackLeft, List.reverse_cons, List.append_assoc] using
      ih x (some (.work (stackPopCell a c x)) :: R)

end CookSource_stack_sweep_left
namespace CookPvsNP
alias stack_sweep_left := _root_.CookSource_stack_sweep_left.solution
end CookPvsNP

namespace CookSource_stack_sweep_algebra
-- Prove2me | solution 1 for CookPvsNP.stack_sweep_algebra
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T11:22:32.738287+00:00
-- url     : https://prove2.me/submissions/89fd4899-1164-4a48-b6cb-fc97d45b2e07


set_option autoImplicit false
open CookPvsNP

private theorem right_form {K A : Type} (a : K → StackAct A)
    (c : StackCol K A) (r : List (StackCol K A)) :
    (stackRight a c r).2 ++ [(stackRight a c r).1] = stackForward a c r := by
  induction r generalizing c with
  | nil => rfl
  | cons x xs ih =>
    simpa [stackRight, stackForward] using
      congrArg (fun z => stackPushCell a c x :: z) (ih (stackPushNext a x))

private theorem right_length {K A : Type} (a : K → StackAct A)
    (c : StackCol K A) (r : List (StackCol K A)) :
    (stackRight a c r).2.length = r.length := by
  induction r generalizing c with
  | nil => rfl
  | cons x xs ih => simp [stackRight, ih]

private theorem right_neutral {K A : Type} (a : K → StackAct A)
    (r : List (StackCol K A)) (c : StackCol K A)
    (hc : ∀ k, a k = .pop → c k = none) :
    stackPopCell a stackZero (stackRight a c r).1 = (stackRight a c r).1 := by
  have hn : ∀ k, a k = .pop → (stackRight a c r).1 k = none := by
    induction r generalizing c with
    | nil => exact hc
    | cons x xs ih =>
      apply ih
      intro k hk
      simp [stackPushNext, hk]
  funext k
  cases h : a k with
  | keep => simp [stackPopCell, h]
  | push b => simp [stackPopCell, h]
  | pop => simp [stackPopCell, stackZero, h, hn k h]

private theorem left_append {K A : Type} (a : K → StackAct A)
    (c : StackCol K A) (r s : List (StackCol K A)) :
    stackLeft a c (r ++ s) =
      let x := stackLeft a c r
      let y := stackLeft a x.1 s
      (y.1, x.2 ++ y.2) := by
  induction r generalizing c with
  | nil => rfl
  | cons x xs ih => simp [stackLeft, ih]

private theorem left_state {K A : Type} (a : K → StackAct A)
    (c : StackCol K A) (r : List (StackCol K A)) :
    (stackLeft a c r.reverse).1 = r.headD c := by
  cases r with
  | nil => rfl
  | cons x xs => simp [List.reverse_cons, left_append, stackLeft]

private theorem left_form {K A : Type} (a : K → StackAct A)
    (r : List (StackCol K A)) (c : StackCol K A)
    (hc : stackPopCell a stackZero c = c) :
    (stackLeft a c r.reverse).2.reverse ++ [c] = stackBackward a (r ++ [c]) := by
  induction r with
  | nil => simp [stackLeft, stackBackward, hc]
  | cons x xs ih =>
    simp only [List.reverse_cons, left_append, stackLeft, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      ih, left_state, stackBackward]
    cases xs <;> rfl

theorem solution {K A : Type} (a : K → StackAct A) (r : List (StackCol K A)) :
    let z := stackRight a (stackPushCarry a) r
    z.2.length = r.length ∧
    (stackLeft a z.1 z.2.reverse).2.reverse ++ [z.1] =
      stackBackward a (stackForward a (stackPushCarry a) r) := by
  dsimp only
  refine ⟨right_length _ _ _, ?_⟩
  rw [left_form, right_form]
  apply right_neutral
  intro k hk
  simp [stackPushCarry, hk]

end CookSource_stack_sweep_algebra
namespace CookPvsNP
alias stack_sweep_algebra := _root_.CookSource_stack_sweep_algebra.solution
end CookPvsNP

namespace CookSource_stack_instruction
-- Prove2me | solution 1 for CookPvsNP.stack_instruction
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T12:09:34.791278+00:00
-- url     : https://prove2.me/submissions/80d2b988-ba16-48b2-befc-7521e5bf05c0


set_option autoImplicit false
open CookPvsNP

theorem solution {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q]
    [DecidableEq K] [DecidableEq A] [DecidableEq Q]
    (P : StackMachine K A Q) (ki ko : K) (q : Q)
    (x : StackCol K A) (xs : List (StackCol K A)) (hq : P.done q = false) :
    let d := P.next q x
    (stackTM P ki ko).run (2 * (x :: xs).length + 2) (stackFrame q (x :: xs)) =
      stackFrame d.1 (stackBackward d.2 (stackForward d.2 (stackPushCarry d.2) (x :: xs))) := by
  let d := P.next q x
  let a := d.2
  let c := stackPushCarry a
  let z := stackRight a c (x :: xs)
  let out := stackBackward a (stackForward a c (x :: xs))
  let M := stackTM P ki ko
  have hfirst : (M).run 1 (stackFrame q (x :: xs)) =
      ⟨.scanR d.1 a (stackPushNext a x), some (.work (stackPushCell a c x)) :: [some (StackSym.origin (K := K) (A := A))],
        (xs.map (some ∘ StackSym.work)).headD none,
        (xs.map (some ∘ StackSym.work)).tail⟩ := by
    simp [M, TM.run, TM.step, TM.IsHalting, stackTM, stackFrame, hq, d, a, c]
  have hright := stack_sweep_right P ki ko d.1 a (stackPushNext a x) xs
    [some (.work (stackPushCell a c x)), some (StackSym.origin (K := K) (A := A))]
  have hb : (M).run 1
      ⟨.scanR d.1 a z.1, (z.2.map (some ∘ StackSym.work)).reverse ++ [some (StackSym.origin (K := K) (A := A))], none, []⟩ =
      ⟨.scanL d.1 a z.1, ((z.2.reverse.map (some ∘ StackSym.work)) ++ [some (StackSym.origin (K := K) (A := A))]).tail,
        ((z.2.reverse.map (some ∘ StackSym.work)) ++ [some (StackSym.origin (K := K) (A := A))]).headD none,
        [some (.work z.1)]⟩ := by
    cases h : z.2.reverse <;>
      simp [M, TM.run, TM.step, TM.IsHalting, stackTM, ← List.map_reverse, h]
  have hleft := stack_sweep_left P ki ko d.1 a z.1 z.2.reverse [some (.work z.1)]
  have hlen : z.2.length = (x :: xs).length := (stack_sweep_algebra a (x :: xs)).1
  have hout : (stackLeft a z.1 z.2.reverse).2.reverse ++ [z.1] = out :=
    (stack_sweep_algebra a (x :: xs)).2
  have hf : (M).run 1
      ⟨.scanL d.1 a (stackLeft a z.1 z.2.reverse).1, [], some (StackSym.origin (K := K) (A := A)),
        ((stackLeft a z.1 z.2.reverse).2.map (some ∘ StackSym.work)).reverse ++
          [some (.work z.1)]⟩ = stackFrame d.1 out := by
    have hm := congrArg (List.map (some ∘ StackSym.work)) hout
    simp only [List.map_append, List.map_reverse, List.map_cons, List.map_nil,
      Function.comp_apply] at hm
    simp only [M, TM.run, Function.iterate_one, TM.step, TM.IsHalting, stackTM]
    simp only [reduceCtorEq, or_self, ↓reduceIte]
    simpa [stackFrame] using congrArg
      (fun r : List (Option (StackSym K A)) =>
        (⟨StackQ.ready d.1, [some (StackSym.origin (K := K) (A := A))], r.headD none, r.tail⟩ :
          Cfg (StackSym K A) (StackQ K A Q))) hm
  change (M).run _ _ = stackFrame d.1 out
  have hr : (M).run xs.length ((M).run 1 (stackFrame q (x :: xs))) =
      ⟨.scanR d.1 a z.1, (z.2.map (some ∘ StackSym.work)).reverse ++ [some (StackSym.origin (K := K) (A := A))], none, []⟩ := by
    rw [hfirst]
    simpa [M, z, stackRight, List.reverse_cons, List.append_assoc] using hright
  rw [List.length_reverse, hlen] at hleft
  rw [show 2 * (x :: xs).length + 2 = 1 + ((x :: xs).length + (1 + (xs.length + 1))) by simp; omega]
  unfold TM.run at hr hb hleft hf ⊢
  dsimp only [M, stackTM] at hr hb hleft hf ⊢
  rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
    Function.iterate_add_apply, hr, hb, hleft]
  exact hf

end CookSource_stack_instruction
namespace CookPvsNP
alias stack_instruction := _root_.CookSource_stack_instruction.solution
end CookPvsNP

namespace CookSource_stack_lookup
-- Prove2me | solution 1 for CookPvsNP.stack_lookup
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:03:56.208997+00:00
-- url     : https://prove2.me/submissions/2503a7e9-2462-410b-8cef-b320623e47a5


set_option autoImplicit false
open CookPvsNP

private theorem drop_head {A : Type} (w : List A) (n : ℕ) (a : A) :
    (w.drop n).headD a = w.getD n a := by
  induction n generalizing w with
  | zero => cases w <;> rfl
  | succ n ih => cases w <;> simp [List.getD]

theorem solution {K A : Type} [DecidableEq K] (r : Fin 6 ↪ K) (fallback : A)
    (s : K → List A) (h2 : s (r 2) = []) (h3 : s (r 3) = [])
    (h4 : s (r 4) = []) (h5 : s (r 5) = []) :
    ∃ n ≤ 9 * (s (r 0)).length + 9 * (s (r 1)).length + 13,
      (lookupProg r fallback).Exec s
        (Function.update s (r 2) [(s (r 0)).getD (s (r 1)).length fallback]) n := by
  have neq (i j : Fin 6) (h : i ≠ j) : r i ≠ r j := r.injective.ne h
  have eqs (i j : Fin 6) : (r i = r j) ↔ i = j := r.injective.eq_iff
  let s1 := Function.update s (r 3) (s (r 0))
  let s2 := Function.update s1 (r 4) (s (r 1))
  let s3 := Function.update (Function.update s (r 3) ((s (r 0)).drop (s (r 1)).length)) (r 4) []
  let value := (s (r 0)).getD (s (r 1)).length fallback
  let s4 := Function.update s3 (r 2) [value]
  have hcopy1 := stack_copy (r 0) (r 3) (r 5)
    (neq _ _ (by decide)) (neq _ _ (by decide)) (neq _ _ (by decide)) s h5
  simp only [h3, List.append_nil] at hcopy1
  have hcopy2 := stack_copy (r 1) (r 4) (r 5)
    (neq _ _ (by decide)) (neq _ _ (by decide)) (neq _ _ (by decide)) s1
    (by simp [s1, eqs, h5])
  simp [s1, eqs, h4] at hcopy2
  have hconsume := stack_consume (r 4) (fun k => decide (k = r 3)) s2
  have hs3 : consumeStore (r 4) (fun k => decide (k = r 3)) s2 = s3 := by
    funext k
    by_cases hk : k = r 4
    · subst k; simp [consumeStore, s3]
    by_cases hk' : k = r 3
    · subst k; simp [consumeStore, s2, s1, s3, Function.update, eqs]
    · simp [consumeStore, s2, s1, s3, Function.update, hk, hk']
  rw [hs3] at hconsume
  have hpeek : (StackProg.act (peekPushAct (r 3) (r 2) fallback)).Exec s3 s4 1 := by
    have he : StackProg.applyAct (peekPushAct (r 3) (r 2) fallback) s3 = s4 := by
      funext k
      by_cases hk : k = r 2
      · subst k
        simp [s4, s3, StackProg.applyAct, peekPushAct, StackAct.apply,
          Function.update, eqs, h2, value]
      · simp [s4, StackProg.applyAct, peekPushAct, StackAct.apply, hk]
    simpa only [he] using StackProg.Exec.act (peekPushAct (r 3) (r 2) fallback) s3
  have hclear := (stack_basic_macros (r 3) s4).2.2
  have hf : Function.update s4 (r 3) [] = Function.update s (r 2) [value] := by
    funext k
    by_cases hk : k = r 3
    · subst k; simp [Function.update, eqs, h3]
    by_cases hk' : k = r 4
    · subst k; simp [s4, s3, Function.update, eqs, h4]
    · simp [s4, s3, Function.update, hk, hk']
  rw [hf] at hclear
  have hprog := StackProg.Exec.seq hcopy1 (StackProg.Exec.seq hcopy2
    (StackProg.Exec.seq hconsume (StackProg.Exec.seq hpeek hclear)))
  refine ⟨_, ?_, hprog⟩
  simp [s4, s3, s2, s1, Function.update, eqs, List.length_drop]
  omega

end CookSource_stack_lookup
namespace CookPvsNP
alias stack_lookup := _root_.CookSource_stack_lookup.solution
end CookPvsNP

namespace CookSource_stack_map_transfer
-- Prove2me | solution 1 for CookPvsNP.stack_map_transfer
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:03:58.280326+00:00
-- url     : https://prove2.me/submissions/31e0a19d-d58b-4652-96d8-4318925c87e5


set_option autoImplicit false
open CookPvsNP

private theorem transfer {K A : Type} [DecidableEq K] (src : K) (targets : K → Bool) (f : A → A)
    (w : List A) (s : K → List A) (hs : s src = w) :
    (mapTransferProg src targets f).Exec s (mapTransferStore src targets f s) (3 * w.length + 1) := by
  induction w generalizing s with
  | nil =>
    have hf : mapTransferStore src targets f s = s := by
      funext k
      by_cases hk : k = src <;> simp [mapTransferStore, hk, hs]
    rw [hf]
    exact .loopFalse (by simp [hs])
  | cons a w ih =>
    let s' := StackProg.applyAct (mapTransferAct src targets f) s
    have hs' : s' src = w := by simp [s', StackProg.applyAct, mapTransferAct, hs, StackAct.apply]
    have hout : mapTransferStore src targets f s' = mapTransferStore src targets f s := by
      funext k
      by_cases hk : k = src
      · simp [mapTransferStore, hk]
      · cases ht : targets k <;>
          simp [mapTransferStore, hk, ht, hs', s', StackProg.applyAct, mapTransferAct, hs,
            StackAct.apply, List.reverse_cons, List.map_append, List.append_assoc]
    have h := StackProg.Exec.loopTrue (by simp [hs])
      (StackProg.Exec.act (mapTransferAct src targets f) s) (ih s' hs')
    rw [hout] at h
    convert h using 1 <;> simp [mapTransferProg]
    omega

theorem solution {K A : Type} [DecidableEq K] (src : K) (targets : K → Bool) (f : A → A)
    (s : K → List A) :
    (mapTransferProg src targets f).Exec s (mapTransferStore src targets f s) (3 * (s src).length + 1) := by
  exact transfer src targets f (s src) s rfl

end CookSource_stack_map_transfer
namespace CookPvsNP
alias stack_map_transfer := _root_.CookSource_stack_map_transfer.solution
end CookPvsNP

namespace CookSource_stack_output
-- Prove2me | solution 1 for CookPvsNP.stack_output
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T12:09:36.9829+00:00
-- url     : https://prove2.me/submissions/1fd65d28-5919-464a-b1cf-b1e96951dd69


set_option autoImplicit false
open CookPvsNP

private theorem trim_blanks {Γ : Type} (xs : List (Option Γ)) (n : ℕ) :
    ((xs ++ List.replicate n none).reverse.dropWhile Option.isNone).reverse =
      (xs.reverse.dropWhile Option.isNone).reverse := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ', ← List.append_assoc]
    simp_all

private theorem trim_word {Γ : Type} (xs : List Γ) :
    ((xs.map some).reverse.dropWhile Option.isNone).reverse = xs.map some := by
  have h (ys : List Γ) : (ys.map some).dropWhile Option.isNone = ys.map some := by
    cases ys <;> simp
  rw [← List.map_reverse, h, ← List.map_reverse, List.reverse_reverse]

theorem solution {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q]
    [DecidableEq K] [DecidableEq A] [DecidableEq Q]
    (P : StackMachine K A Q) (ki ko : K) (r : List (StackCol K A))
    (s : K → List A) (hr : StackRep r s) :
    let out := r.map (fun v => (v ko).map (StackSym.output (K := K))) ++ [none]
    (stackTM P ki ko).output
      ⟨.accept, [some .origin], out.headD none, out.tail⟩ =
      (s ko).map (some ∘ stackOutput) := by
  dsimp only
  have hm := congrArg (List.map (Option.map (StackSym.output (K := K)))) (hr ko).2
  simp only [List.map_map, Function.comp_def, stackPad, List.map_append,
    List.map_replicate, Option.map_none, Option.map_some] at hm
  rw [hm]
  have hne : (List.map (fun a => some (StackSym.output (K := K) a)) (s ko) ++
      List.replicate (r.length - (s ko).length) none ++ [none]) ≠ [] := by simp
  simp only [TM.output]
  have hcons : (List.map (fun a => some (StackSym.output (K := K) a)) (s ko) ++
      List.replicate (r.length - (s ko).length) none ++ [none]).headD none ::
      (List.map (fun a => some (StackSym.output (K := K) a)) (s ko) ++
      List.replicate (r.length - (s ko).length) none ++ [none]).tail =
      List.map (fun a => some (StackSym.output (K := K) a)) (s ko) ++
      List.replicate (r.length - (s ko).length) none ++ [none] := by
    generalize he : (List.map (fun a => some (StackSym.output (K := K) a)) (s ko) ++
      List.replicate (r.length - (s ko).length) none ++ [none]) = l at *
    cases l with
    | nil => contradiction
    | cons _ _ => rfl
  rw [hcons]
  rw [List.append_assoc, show List.replicate (r.length - (s ko).length) (none : Option (StackSym K A)) ++ [none] =
      List.replicate (r.length - (s ko).length + 1) none by rw [List.replicate_succ']]
  rw [trim_blanks]
  have hw := trim_word ((s ko).map (StackSym.output (K := K)))
  simp only [List.map_map] at hw
  convert hw using 1 <;> rfl

end CookSource_stack_output
namespace CookPvsNP
alias stack_output := _root_.CookSource_stack_output.solution
end CookPvsNP

namespace CookSource_stack_setup
-- Prove2me | solution 1 for CookPvsNP.stack_setup
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T11:47:07.631532+00:00
-- url     : https://prove2.me/submissions/195ed9c2-a46d-481e-adb6-db1c3f8c8566


set_option autoImplicit false
open CookPvsNP

section
variable {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q]
  [DecidableEq K] [DecidableEq A] [DecidableEq Q]
  (P : StackMachine K A Q) (ki ko : K)
local notation "M" => stackTM P ki ko

private theorem scan (w : List A) (L : List (Option (StackSym K A))) :
    (M).run w.length
      ⟨.setup, L, (w.map (some ∘ StackSym.input)).headD none,
        (w.map (some ∘ StackSym.input)).tail⟩ =
      ⟨.setup, (w.map (fun b => some (.work (stackInitialCol ki b)))).reverse ++ L, none, []⟩ := by
  induction w generalizing L with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons, TM.run, Function.iterate_succ_apply, List.map_cons,
      List.headD_cons, List.tail_cons]
    have hs : (M).step ⟨.setup, L, some (.input b), bs.map (some ∘ StackSym.input)⟩ =
        ⟨.setup, some (.work (stackInitialCol ki b)) :: L,
          (bs.map (some ∘ StackSym.input)).headD none,
          (bs.map (some ∘ StackSym.input)).tail⟩ := by
      simp [TM.step, TM.IsHalting, stackTM]
    refine (congrArg ((M).step^[bs.length]) hs).trans ?_
    simpa [TM.run, List.reverse_cons, List.append_assoc] using
      ih (some (.work (stackInitialCol ki b)) :: L)

private theorem back (r : List (StackCol K A)) (R : List (Option (StackSym K A))) :
    (M).run r.length
      ⟨.setupBack, (r.map (some ∘ StackSym.work) ++ [some (StackSym.origin (K := K) (A := A))]).tail,
        (r.map (some ∘ StackSym.work) ++ [some (StackSym.origin (K := K) (A := A))]).headD none, R⟩ =
      ⟨.setupBack, [], some (StackSym.origin (K := K) (A := A)), (r.map (some ∘ StackSym.work)).reverse ++ R⟩ := by
  induction r generalizing R with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, TM.run, Function.iterate_succ_apply, List.map_cons,
      List.cons_append, List.headD_cons, List.tail_cons]
    have hs : (M).step
        ⟨.setupBack, xs.map (some ∘ StackSym.work) ++ [some (StackSym.origin (K := K) (A := A))],
          some (.work x), R⟩ =
        ⟨.setupBack, (xs.map (some ∘ StackSym.work) ++ [some (StackSym.origin (K := K) (A := A))]).tail,
          (xs.map (some ∘ StackSym.work) ++ [some (StackSym.origin (K := K) (A := A))]).headD none,
          some (.work x) :: R⟩ := by
      cases xs <;> simp [TM.step, TM.IsHalting, stackTM]
    refine (congrArg ((M).step^[xs.length]) hs).trans ?_
    simpa [TM.run, List.reverse_cons, List.append_assoc] using ih (some (.work x) :: R)

end

theorem solution {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q]
    [DecidableEq K] [DecidableEq A] [DecidableEq Q]
    (P : StackMachine K A Q) (ki ko : K) (w : List A) :
    (stackTM P ki ko).run (2 * w.length + 4)
      ((stackTM P ki ko).init (w.map stackInput)) =
      stackFrame P.initial (w.map (stackInitialCol ki) ++ [stackZero]) := by
  let M := stackTM P ki ko
  let r := w.map (stackInitialCol ki)
  have hs : (M).run 2 ((M).init (w.map stackInput)) =
      ⟨.setup, [some (StackSym.origin (K := K) (A := A))], (w.map (some ∘ StackSym.input)).headD none,
        (w.map (some ∘ StackSym.input)).tail⟩ := by
    cases w <;> simp [M, TM.run, TM.init, Function.iterate_succ_apply,
      TM.step, TM.IsHalting, stackTM, stackInput, List.map_map, Function.comp_def]
    exact ⟨rfl, fun _ _ => rfl⟩
  have hr := scan P ki ko w [some (StackSym.origin (K := K) (A := A))]
  have hb : (M).run 1
      ⟨.setup, (r.map (some ∘ StackSym.work)).reverse ++ [some (StackSym.origin (K := K) (A := A))], none, []⟩ =
      ⟨.setupBack, (r.reverse.map (some ∘ StackSym.work) ++ [some (StackSym.origin (K := K) (A := A))]).tail,
        (r.reverse.map (some ∘ StackSym.work) ++ [some (StackSym.origin (K := K) (A := A))]).headD none,
        [some (.work stackZero)]⟩ := by
    cases h : r.reverse <;>
      simp [M, TM.run, TM.step, TM.IsHalting, stackTM, ← List.map_reverse, h]
  have hl := back P ki ko r.reverse [some (.work stackZero)]
  have hf : (M).run 1
      ⟨.setupBack, [], some (StackSym.origin (K := K) (A := A)), r.map (some ∘ StackSym.work) ++ [some (.work stackZero)]⟩ =
      stackFrame P.initial (r ++ [stackZero]) := by
    simp [M, TM.run, TM.step, TM.IsHalting, stackTM, stackFrame]
  simp only [List.length_reverse, List.map_reverse, List.reverse_reverse] at hl
  simp only [List.map_reverse] at hb
  have hn : r.length = w.length := List.length_map _
  rw [hn] at hl
  have he : w.map (fun b => some (StackSym.work (stackInitialCol ki b))) =
      r.map (some ∘ StackSym.work) := by simp [r, List.map_map, Function.comp_def]
  rw [he] at hr
  have h1 := (congrArg ((M).run w.length) hs).trans hr
  have h2 := (congrArg ((M).run 1) h1).trans hb
  have h3 := (congrArg ((M).run w.length) h2).trans hl
  have h4 := (congrArg ((M).run 1) h3).trans hf
  have ht : 1 + (w.length + (1 + (w.length + 2))) = 2 * w.length + 4 := by omega
  simpa only [TM.run, ← Function.iterate_add_apply, ht] using h4

end CookSource_stack_setup
namespace CookPvsNP
alias stack_setup := _root_.CookSource_stack_setup.solution
end CookPvsNP

namespace CookSource_stack_representation
-- Prove2me | solution 1 for CookPvsNP.stack_representation
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T12:09:33.868769+00:00
-- url     : https://prove2.me/submissions/d9a62091-4730-4323-b733-d134be352aa0


set_option autoImplicit false
open CookPvsNP

private theorem pad_action {A : Type} (a : StackAct A) (s : List A)
    (n : ℕ) (hn : s.length ≤ n) :
    (a.apply s).length ≤ n + 1 ∧
    stackPad (a.apply s) (n + 1) =
      match a with
      | .keep => stackPad s n ++ [none]
      | .push b => some b :: stackPad s n
      | .pop => (stackPad s n ++ [none]).tail ++ [none] := by
  cases a with
  | keep =>
    constructor
    · simpa [StackAct.apply] using hn.trans (Nat.le_succ n)
    · simp only [StackAct.apply, stackPad]
      rw [show n + 1 - s.length = (n - s.length) + 1 by omega]
      simp [List.replicate_add, List.append_assoc]
  | push b => simp [StackAct.apply, stackPad, hn]
  | pop =>
    cases s with
    | nil =>
      simp only [StackAct.apply, List.tail_nil, List.length_nil, Nat.zero_le, true_and,
        stackPad, List.map_nil, Nat.sub_zero, List.nil_append]
      have he : List.replicate n (none : Option A) ++ [none] = List.replicate (n + 1) none := by
        simpa using (List.replicate_add n 1 (none : Option A)).symm
      rw [he, List.replicate_succ, List.tail_cons]
      simpa [List.replicate_succ] using he.symm
    | cons b bs =>
      simp only [List.length_cons] at hn
      constructor
      · simp only [StackAct.apply, List.tail_cons]; omega
      · simp only [StackAct.apply, List.tail_cons, stackPad, List.map_cons, List.length_cons,
          List.cons_append, List.tail_cons]
        rw [show n + 1 - bs.length = (n - (bs.length + 1)) + 2 by omega]
        simp [List.replicate_add, List.append_assoc]

theorem solution {K A : Type} (a : K → StackAct A) (r : List (StackCol K A))
    (s : K → List A) (h : StackRep r s) :
    StackRep (stackBackward a (stackForward a (stackPushCarry a) r))
      (fun k => (a k).apply (s k)) := by
  intro k
  obtain ⟨hlen, hproj⟩ := stack_column_laws a r k
  obtain ⟨hsize, hpad⟩ := pad_action (a k) (s k) r.length (h k).1
  refine ⟨hlen.symm ▸ hsize, ?_⟩
  rw [hlen, hpad, hproj, (h k).2]

end CookSource_stack_representation
namespace CookPvsNP
alias stack_representation := _root_.CookSource_stack_representation.solution
end CookPvsNP

namespace CookSource_stack_run
-- Prove2me | solution 1 for CookPvsNP.stack_run
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T12:09:38.025647+00:00
-- url     : https://prove2.me/submissions/27fda865-88ac-40c6-8e5e-4c849fbe433d


set_option autoImplicit false
open CookPvsNP

private theorem rep_head {K A : Type} (x : StackCol K A) (xs : List (StackCol K A))
    (s : K → List A) (h : StackRep (x :: xs) s) : x = fun k => (s k).head? := by
  funext k
  have hh := congrArg (fun l : List (Option A) => l.headD none) (h k).2
  simp only [List.map_cons, List.headD_cons] at hh
  rw [hh]
  cases he : s k with
  | nil => simp [stackPad, List.replicate_succ]
  | cons b bs => simp [stackPad]

theorem solution {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q]
    [DecidableEq K] [DecidableEq A] [DecidableEq Q]
    (P : StackMachine K A Q) (ki ko : K) (m : ℕ)
    (c : StackCfg K A Q) (r : List (StackCol K A)) (hn : 0 < r.length)
    (hr : StackRep r c.store) :
    ∃ t r', t ≤ stackTime r.length m ∧ r'.length ≤ r.length + m ∧ 0 < r'.length ∧
      StackRep r' ((P.step^[m]) c).store ∧
      (stackTM P ki ko).run t (stackFrame c.state r) =
        stackFrame ((P.step^[m]) c).state r' := by
  induction m generalizing c r with
  | zero => exact ⟨0, r, by simp [stackTime], by simp, hn, hr, rfl⟩
  | succ m ih =>
    by_cases hd : P.done c.state = true
    · have hf : P.step c = c := by simp [StackMachine.step, hd]
      have he : (P.step^[m + 1]) c = c := Function.iterate_fixed hf _
      exact ⟨0, r, Nat.zero_le _, by omega, hn, he.symm ▸ hr, by rw [he]; rfl⟩
    · have hd' : P.done c.state = false := Bool.eq_false_iff.mpr hd
      cases r with
      | nil => simp at hn
      | cons x xs =>
        let a := (P.next c.state x).2
        let z := stackBackward a (stackForward a (stackPushCarry a) (x :: xs))
        have hx := rep_head x xs c.store hr
        have hc : P.step c = ⟨(P.next c.state x).1, fun k => (a k).apply (c.store k)⟩ := by
          simp only [StackMachine.step, hd', Bool.false_eq_true, ↓reduceIte]
          rw [← hx]
        have hl : z.length = (x :: xs).length + 1 := (stack_column_laws a (x :: xs) ki).1
        have hz : StackRep z (P.step c).store := by
          rw [hc]
          exact stack_representation a (x :: xs) c.store hr
        have ht : (stackTM P ki ko).run (2 * (x :: xs).length + 2)
            (stackFrame c.state (x :: xs)) = stackFrame (P.step c).state z := by
          rw [hc]
          exact stack_instruction P ki ko c.state x xs hd'
        obtain ⟨t, r', htbound, hwidth, hpos, hrep, hrun⟩ := ih (P.step c) z (by omega) hz
        refine ⟨t + (2 * (x :: xs).length + 2), r', ?_, ?_, hpos, ?_, ?_⟩
        · rw [hl] at htbound
          unfold stackTime at htbound ⊢
          nlinarith
        · omega
        · simpa only [Function.iterate_succ_apply] using hrep
        · have hh := (congrArg ((stackTM P ki ko).run t) ht).trans hrun
          unfold TM.run at hh ⊢
          dsimp only [stackTM] at hh ⊢
          rw [Function.iterate_add_apply]
          simpa only [Function.iterate_succ_apply] using hh

end CookSource_stack_run
namespace CookPvsNP
alias stack_run := _root_.CookSource_stack_run.solution
end CookPvsNP

namespace CookSource_stack_polytime
-- Prove2me | solution 1 for CookPvsNP.stack_polytime
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T12:09:39.842428+00:00
-- url     : https://prove2.me/submissions/e1726829-56dd-4683-bf81-da2de1d71c21


set_option autoImplicit false
open CookPvsNP

private theorem initial_rep {K A Q : Type} [DecidableEq K]
    (P : StackMachine K A Q) (ki : K) (w : List A) :
    StackRep (w.map (stackInitialCol ki) ++ [stackZero]) (P.init ki w).store := by
  intro k
  by_cases hk : k = ki
  · simp [StackMachine.init, hk, stackPad, stackInitialCol, stackZero,
      List.map_map, Function.comp_def]
  · simp [StackMachine.init, hk, stackPad, stackInitialCol, stackZero,
      List.map_map, Function.comp_def, List.replicate_succ']

theorem solution {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q]
    [DecidableEq K] [DecidableEq A] [DecidableEq Q]
    (P : StackMachine K A Q) (ki ko : K) (f : List A → List A) (k : ℕ)
    (h : ∀ w : List A, ∃ m, m ≤ w.length ^ k + k ∧
      P.done ((P.step^[m]) (P.init ki w)).state = true ∧
      ((P.step^[m]) (P.init ki w)).store ko = f w) : PolyTimeComputable f := by
  classical
  obtain ⟨b, hb⟩ := comp_budget k 2
  refine ⟨StackSym K A, inferInstance, stackInput, stackOutput, stackTM P ki ko, b, ?_⟩
  intro w
  let M := stackTM P ki ko
  let r := w.map (stackInitialCol ki) ++ [stackZero]
  have hlen : r.length = w.length + 1 := by simp [r]
  obtain ⟨m, hm, hd, ho⟩ := h w
  let c := (P.step^[m]) (P.init ki w)
  obtain ⟨t, r', ht, hn, hpos, hrep, hr⟩ :=
    stack_run P ki ko m (P.init ki w) r (by simp [r]) (initial_rep P ki w)
  have hs := stack_setup P ki ko w
  cases r' with
  | nil => simp at hpos
  | cons x xs =>
    have hc := stack_cleanup P ki ko c.state x xs hd
    let out := (x :: xs).map (fun v => (v ko).map (StackSym.output (K := K))) ++ [none]
    let final : Cfg (StackSym K A) (StackQ K A Q) :=
      ⟨.accept, [some .origin], out.headD none, out.tail⟩
    let N := (2 * (x :: xs).length + 2) + (t + (2 * w.length + 4))
    have hall : M.run N (M.init (w.map stackInput)) = final := by
      have h1 := (congrArg (M.run t) hs).trans hr
      have h2 := (congrArg (M.run (2 * (x :: xs).length + 2)) h1).trans hc
      unfold TM.run at h2 ⊢
      dsimp only [M, stackTM] at h2 ⊢
      dsimp only [N]
      rw [Function.iterate_add_apply _ (2 * (x :: xs).length + 2) (t + (2 * w.length + 4)),
        Function.iterate_add_apply _ t (2 * w.length + 4)]
      exact h2
    have hN : N ≤ w.length ^ b + b := by
      apply le_trans _ (hb w.length)
      rw [hlen] at hn ht
      unfold stackTime at ht
      dsimp only [N]
      have hsq : m * m ≤ (w.length ^ k + k) * (w.length ^ k + k) := Nat.mul_self_le_mul_self hm
      have hmul := Nat.mul_le_mul_left (2 * w.length + 3) hm
      nlinarith
    have hf : M.IsHalting final := by simp [TM.IsHalting, M, stackTM, final]
    have hlong : M.run (w.length ^ b + b) (M.init (w.map stackInput)) = final := by
      rw [show w.length ^ b + b = (w.length ^ b + b - N) + N by omega]
      unfold TM.run at hall ⊢
      dsimp only [M, stackTM] at hall ⊢
      rw [Function.iterate_add_apply, hall]
      exact tm_run_eq_of_halting M final hf _
    constructor
    · change M.IsHalting (M.run _ _) 
      rw [hlong]
      exact hf
    · change M.output (M.run _ _) = _
      rw [hlong]
      have hout := stack_output P ki ko (x :: xs) c.store hrep
      change c.store ko = f w at ho
      rw [ho] at hout
      exact hout

end CookSource_stack_polytime
namespace CookPvsNP
alias stack_polytime := _root_.CookSource_stack_polytime.solution
end CookPvsNP

namespace CookSource_stack_trace_laws
-- Prove2me | solution 1 for CookPvsNP.stack_trace_laws
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:24:44.331246+00:00
-- url     : https://prove2.me/submissions/051f2c5c-39b4-4076-9088-5a5f015b2178


set_option autoImplicit false
open CookPvsNP

private theorem trace_run {K A Q : Type} (P : StackMachine K A Q) {n : ℕ}
    {c d : StackCfg K A Q} (h : StackTrace P n c d) : (P.step^[n]) c = d := by
  induction h with
  | refl => rfl
  | cons _ _ ih => simpa only [Function.iterate_succ_apply] using ih

private theorem trace_append {K A Q : Type} (P : StackMachine K A Q) {n m : ℕ}
    {c d e : StackCfg K A Q} (h : StackTrace P n c d) (h' : StackTrace P m d e) :
    StackTrace P (n + m) c e := by
  induction h with
  | refl => simpa using h'
  | cons hd _ ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using StackTrace.cons hd (ih h')

private theorem trace_map {K A Q R : Type} (P : StackMachine K A Q) (S : StackMachine K A R)
    (f : StackCfg K A Q → StackCfg K A R)
    (hf : ∀ c, P.done c.state = false → S.done (f c).state = false ∧ S.step (f c) = f (P.step c))
    {n : ℕ} {c d : StackCfg K A Q} (h : StackTrace P n c d) : StackTrace S n (f c) (f d) := by
  induction h with
  | refl => exact .refl _
  | @cons n c d hd ht ih =>
    exact .cons (hf c hd).1 ((hf c hd).2 ▸ ih)

theorem solution {K A Q : Type} (P : StackMachine K A Q) :
    (∀ {n : ℕ} {c d : StackCfg K A Q}, StackTrace P n c d → (P.step^[n]) c = d) ∧
    (∀ {n m : ℕ} {c d e : StackCfg K A Q}, StackTrace P n c d → StackTrace P m d e →
      StackTrace P (n + m) c e) ∧
    (∀ {R : Type} (S : StackMachine K A R) (f : StackCfg K A Q → StackCfg K A R),
      (∀ c, P.done c.state = false → S.done (f c).state = false ∧ S.step (f c) = f (P.step c)) →
      ∀ {n : ℕ} {c d : StackCfg K A Q}, StackTrace P n c d → StackTrace S n (f c) (f d)) := by
  refine ⟨trace_run P, trace_append P, ?_⟩
  intro R S f hf n c d h
  exact trace_map P S f hf h

end CookSource_stack_trace_laws
namespace CookPvsNP
alias stack_trace_laws := _root_.CookSource_stack_trace_laws.solution
end CookPvsNP

namespace CookSource_stack_program_correct
-- Prove2me | solution 1 for CookPvsNP.stack_program_correct
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:24:45.043981+00:00
-- url     : https://prove2.me/submissions/76732f30-1ba5-4ce1-ad42-8a2d8740a0f6


set_option autoImplicit false
open CookPvsNP
open StackProg

private theorem compile {K A : Type} {p : StackProg K A} {s t : K → List A} {n : ℕ}
    (h : p.Exec s t n) : ∃ l : p.Label, p.done l = true ∧
      StackTrace p.machine n ⟨p.entry, s⟩ ⟨l, t⟩ := by
  induction h with
  | act f s =>
    refine ⟨true, rfl, .cons rfl ?_⟩
    exact .refl _
  | @seq p q s t u n m hp hq ihp ihq =>
    obtain ⟨lp, hdp, htp⟩ := ihp
    obtain ⟨lq, hdq, htq⟩ := ihq
    have hleft := (stack_trace_laws p.machine).2.2 (p.seq q).machine
      (fun c => ⟨Sum.inl c.state, c.store⟩) (by
        intro c hc
        change p.done c.state = false at hc
        simp [StackMachine.step, machine, done, next, hc]) htp
    have hright := (stack_trace_laws q.machine).2.2 (p.seq q).machine
      (fun c => ⟨Sum.inr c.state, c.store⟩) (by
        intro c hc
        change q.done c.state = false at hc
        simp [StackMachine.step, machine, done, next, hc]) htq
    have htransfer : StackTrace (p.seq q).machine 1 ⟨Sum.inl lp, t⟩ ⟨Sum.inr q.entry, t⟩ := by
      apply StackTrace.cons rfl
      simpa [StackMachine.step, machine, done, next, hdp, StackAct.apply] using
        (StackTrace.refl (P := (p.seq q).machine) (⟨Sum.inr q.entry, t⟩))
    refine ⟨Sum.inr lq, hdq, ?_⟩
    exact (stack_trace_laws (p.seq q).machine).2.1
      ((stack_trace_laws (p.seq q).machine).2.1 hleft htransfer) hright
  | @branchTrue test p q s t n ht hp ih =>
    obtain ⟨l, hd, hrun⟩ := ih
    have hbody := (stack_trace_laws p.machine).2.2 (StackProg.branch test p q).machine
      (fun c => ⟨some (Sum.inl c.state), c.store⟩) (by
        intro c hc
        change p.done c.state = false at hc
        simp [StackMachine.step, machine, done, next, hc]) hrun
    refine ⟨some (.inl l), hd, ?_⟩
    rw [Nat.add_comm]
    apply StackTrace.cons rfl
    simpa [StackMachine.step, machine, done, next, ht, StackAct.apply, entry] using hbody
  | @branchFalse test p q s t n ht hq ih =>
    obtain ⟨l, hd, hrun⟩ := ih
    have hbody := (stack_trace_laws q.machine).2.2 (StackProg.branch test p q).machine
      (fun c => ⟨some (Sum.inr c.state), c.store⟩) (by
        intro c hc
        change q.done c.state = false at hc
        simp [StackMachine.step, machine, done, next, hc]) hrun
    refine ⟨some (.inr l), hd, ?_⟩
    rw [Nat.add_comm]
    apply StackTrace.cons rfl
    simpa [StackMachine.step, machine, done, next, ht, StackAct.apply, entry] using hbody
  | @loopFalse test p s ht =>
    refine ⟨some none, rfl, .cons rfl ?_⟩
    simpa [StackMachine.step, machine, done, next, ht, StackAct.apply, entry] using
      (StackTrace.refl (P := (StackProg.loop test p).machine) ⟨some none, s⟩)
  | @loopTrue test p s t u n m ht hp hloop ihp ihloop =>
    obtain ⟨l, hd, hrun⟩ := ihp
    obtain ⟨l', hd', hrest⟩ := ihloop
    have hbody := (stack_trace_laws p.machine).2.2 (StackProg.loop test p).machine
      (fun c => ⟨some (some c.state), c.store⟩) (by
        intro c hc
        change p.done c.state = false at hc
        simp [StackMachine.step, machine, done, next, hc]) hrun
    have henter : StackTrace (StackProg.loop test p).machine (1 + n)
        ⟨none, s⟩ ⟨some (some l), t⟩ := by
      rw [Nat.add_comm]
      apply StackTrace.cons rfl
      simpa [StackMachine.step, machine, done, next, ht, StackAct.apply, entry] using hbody
    have htransfer : StackTrace (StackProg.loop test p).machine 1 ⟨some (some l), t⟩ ⟨none, t⟩ := by
      apply StackTrace.cons rfl
      simpa [StackMachine.step, machine, done, next, hd, StackAct.apply] using
        (StackTrace.refl (P := (StackProg.loop test p).machine) ⟨none, t⟩)
    exact ⟨l', hd', (stack_trace_laws (StackProg.loop test p).machine).2.1
      ((stack_trace_laws (StackProg.loop test p).machine).2.1 henter htransfer) hrest⟩

theorem solution {K A : Type} {p : StackProg K A} {s t : K → List A} {n : ℕ}
    (h : p.Exec s t n) : ∃ l : p.Label, p.done l = true ∧
      (p.machine.step^[n]) ⟨p.entry, s⟩ = ⟨l, t⟩ := by
  obtain ⟨l, hd, ht⟩ := compile h
  exact ⟨l, hd, (stack_trace_laws p.machine).1 ht⟩

end CookSource_stack_program_correct
namespace CookPvsNP
alias stack_program_correct := _root_.CookSource_stack_program_correct.solution
end CookPvsNP

namespace CookSource_stack_program_polytime
-- Prove2me | solution 1 for CookPvsNP.stack_program_polytime
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:24:45.820562+00:00
-- url     : https://prove2.me/submissions/248fb00b-b3aa-46b2-853d-2b599416db5a


set_option autoImplicit false
open CookPvsNP

theorem solution {K A : Type} [Fintype K] [Fintype A] [DecidableEq K] [DecidableEq A]
    (p : StackProg K A) (ki ko : K) (f : List A → List A) (k : ℕ)
    (h : ∀ w : List A, ∃ s n, n ≤ w.length ^ k + k ∧
      p.Exec (fun j => if j = ki then w else []) s n ∧ s ko = f w) :
    PolyTimeComputable f := by
  apply stack_polytime p.machine ki ko f k
  intro w
  obtain ⟨s, n, hn, he, ho⟩ := h w
  obtain ⟨l, hd, hr⟩ := stack_program_correct he
  refine ⟨n, hn, ?_, ?_⟩
  · change p.done ((p.machine.step^[n]) ⟨p.entry, fun j => if j = ki then w else []⟩).state = true
    rw [hr]
    exact hd
  · change ((p.machine.step^[n]) ⟨p.entry, fun j => if j = ki then w else []⟩).store ko = f w
    rw [hr]
    exact ho

end CookSource_stack_program_polytime
namespace CookPvsNP
alias stack_program_polytime := _root_.CookSource_stack_program_polytime.solution
end CookPvsNP

namespace CookSource_stack_repeat_copy
-- Prove2me | solution 1 for CookPvsNP.stack_repeat_copy
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:03:57.203005+00:00
-- url     : https://prove2.me/submissions/96871244-0836-45c0-97fb-91d45f5abcbb


set_option autoImplicit false
open CookPvsNP

private theorem repeat_copy {K A : Type} [DecidableEq K] (r : Fin 4 ↪ K)
    (w : List A) (s : K → List A) (hs : s (r 2) = w) (he : s (r 3) = []) :
    (repeatCopyProg r).Exec s
      (Function.update (Function.update s (r 2) []) (r 1)
        ((List.replicate w.length (s (r 0))).flatten ++ s (r 1)))
      ((6 * (s (r 0)).length + 7) * w.length + 1) := by
  have neq (i j : Fin 4) (h : i ≠ j) : r i ≠ r j := r.injective.ne h
  have eqs (i j : Fin 4) : (r i = r j) ↔ i = j := r.injective.eq_iff
  induction w generalizing s with
  | nil =>
    have hf : Function.update (Function.update s (r 2) []) (r 1) (s (r 1)) = s := by
      funext k
      by_cases hk : k = r 2
      · subst k; simp [Function.update, eqs, hs]
      by_cases hk' : k = r 1
      · subst k; simp [Function.update]
      · simp [Function.update, hk, hk']
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.replicate_zero,
      List.flatten_nil, List.nil_append, hf]
    exact .loopFalse (by simp [hs])
  | cons a w ih =>
    let s1 := Function.update s (r 2) w
    let s2 := Function.update s1 (r 1) (s (r 0) ++ s (r 1))
    have hs0 : s2 (r 0) = s (r 0) := by simp [s2, s1, eqs]
    have hs2 : s2 (r 2) = w := by simp [s2, s1, eqs]
    have hs3 : s2 (r 3) = [] := by simp [s2, s1, eqs, he]
    have hpop := (stack_basic_macros (r 2) s).2.1
    simp only [hs, List.tail_cons] at hpop
    have hcopy := stack_copy (r 0) (r 1) (r 3)
      (neq _ _ (by decide)) (neq _ _ (by decide)) (neq _ _ (by decide)) s1
      (by simp [s1, eqs, he])
    simp only [s1] at hcopy
    simp only [Function.update_of_ne (neq 0 2 (by decide)),
      Function.update_of_ne (neq 1 2 (by decide))] at hcopy
    have hbody := StackProg.Exec.seq hpop hcopy
    have hloop := StackProg.Exec.loopTrue (by simp [hs]) hbody (ih s2 hs2 hs3)
    have hf : Function.update (Function.update s2 (r 2) []) (r 1)
        ((List.replicate w.length (s2 (r 0))).flatten ++ s2 (r 1)) =
        Function.update (Function.update s (r 2) []) (r 1)
        ((List.replicate (a :: w).length (s (r 0))).flatten ++ s (r 1)) := by
      funext k
      by_cases hk : k = r 1
      · subst k
        simp [Function.update, s2, s1, eqs, List.replicate_succ', List.flatten_append, List.append_assoc]
      by_cases hk' : k = r 2
      · subst k; simp [Function.update, eqs]
      · simp [Function.update, s2, s1, hk, hk']
    rw [hf] at hloop
    convert hloop using 1 <;> first | rfl | (simp only [hs0, List.length_cons]; ring)

theorem solution {K A : Type} [DecidableEq K] (r : Fin 4 ↪ K)
    (s : K → List A) (he : s (r 3) = []) :
    (repeatCopyProg r).Exec s
      (Function.update (Function.update s (r 2) []) (r 1)
        ((List.replicate (s (r 2)).length (s (r 0))).flatten ++ s (r 1)))
      ((6 * (s (r 0)).length + 7) * (s (r 2)).length + 1) := by
  exact repeat_copy r (s (r 2)) s rfl he

end CookSource_stack_repeat_copy
namespace CookPvsNP
alias stack_repeat_copy := _root_.CookSource_stack_repeat_copy.solution
end CookPvsNP

namespace CookSource_stack_specification_branch
-- Prove2me | solution 1 for CookPvsNP.stack_specification_branch
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:43:46.497097+00:00
-- url     : https://prove2.me/submissions/ee40f251-19bc-4c10-b196-993987bffae7


set_option autoImplicit false
open CookPvsNP

theorem solution {K A S : Type} (R : S → (K → List A) → Prop)
    (p q : StackProg K A) (test : (K → Option A) → Bool) (b : S → Bool)
    (f g : S → S) (c d : S → ℕ)
    (hp : StackImplements R p f c) (hq : StackImplements R q g d)
    (hb : ∀ s l, R s l → test (fun k => (l k).head?) = b s) :
    StackImplements R (.branch test p q) (fun s => if b s then f s else g s)
      (fun s => 1 + max (c s) (d s)) := by
  intro s l hr
  cases h : b s with
  | false =>
    obtain ⟨n, l', hn, he, hr'⟩ := hq s l hr
    refine ⟨1 + n, l', ?_, .branchFalse ((hb s l hr).trans h) he, ?_⟩
    · dsimp only; have := le_max_right (c s) (d s); omega
    · simpa [h] using hr'
  | true =>
    obtain ⟨n, l', hn, he, hr'⟩ := hp s l hr
    refine ⟨1 + n, l', ?_, .branchTrue ((hb s l hr).trans h) he, ?_⟩
    · dsimp only; have := le_max_left (c s) (d s); omega
    · simpa [h] using hr'

end CookSource_stack_specification_branch
namespace CookPvsNP
alias stack_specification_branch := _root_.CookSource_stack_specification_branch.solution
end CookPvsNP

namespace CookSource_stack_specification_budget
-- Prove2me | solution 1 for CookPvsNP.stack_specification_budget
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:43:47.505866+00:00
-- url     : https://prove2.me/submissions/eb36cc97-1911-4438-a2d8-16365fb0672b


set_option autoImplicit false
open CookPvsNP

theorem solution {K A S : Type} (R : S → (K → List A) → Prop)
    (p : StackProg K A) (f : S → S) (c d : S → ℕ)
    (hp : StackImplements R p f c) (hd : ∀ s, c s ≤ d s) :
    StackImplements R p f d := by
  intro s l hr
  obtain ⟨n, l', hn, he, hr'⟩ := hp s l hr
  exact ⟨n, l', hn.trans (hd s), he, hr'⟩

end CookSource_stack_specification_budget
namespace CookPvsNP
alias stack_specification_budget := _root_.CookSource_stack_specification_budget.solution
end CookPvsNP

namespace CookSource_stack_specification_loop
-- Prove2me | solution 1 for CookPvsNP.stack_specification_loop
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:43:44.168464+00:00
-- url     : https://prove2.me/submissions/a332ed04-e3cb-4bfd-b05f-32f011c93113


set_option autoImplicit false
open CookPvsNP

private theorem loop {K A S : Type} (R : S → (K → List A) → Prop)
    (p : StackProg K A) (test : (K → Option A) → Bool) (f : S → S) (cost rank : S → ℕ)
    (hp : StackImplements R p f cost)
    (ht : ∀ s l, R s l → test (fun k => (l k).head?) = decide (0 < rank s))
    (hd : ∀ s, 0 < rank s → rank (f s) + 1 = rank s)
    (n : ℕ) (s : S) (l : K → List A) (hr : R s l) (hn : rank s = n) :
    ∃ t l', t ≤ stackLoopCost f cost n s ∧
      (StackProg.loop test p).Exec l l' t ∧ R ((f^[n]) s) l' := by
  induction n generalizing s l with
  | zero =>
    refine ⟨1, l, by simp [stackLoopCost], .loopFalse ?_, hr⟩
    simp [ht s l hr, hn]
  | succ n ih =>
    obtain ⟨a, l', ha, he, hrep⟩ := hp s l hr
    have hpos : 0 < rank s := by omega
    have hnext : rank (f s) = n := by have := hd s hpos; omega
    obtain ⟨b, l'', hb, he', hrep'⟩ := ih (f s) l' hrep hnext
    refine ⟨1 + a + 1 + b, l'', ?_, .loopTrue ?_ he he', ?_⟩
    · unfold stackLoopCost at hb ⊢
      rw [Finset.sum_range_succ']
      simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
      omega
    · simp [ht s l hr, hpos]
    · simpa only [Function.iterate_succ_apply] using hrep'

theorem solution {K A S : Type} (R : S → (K → List A) → Prop)
    (p : StackProg K A) (test : (K → Option A) → Bool) (f : S → S) (cost rank : S → ℕ)
    (hp : StackImplements R p f cost)
    (ht : ∀ s l, R s l → test (fun k => (l k).head?) = decide (0 < rank s))
    (hd : ∀ s, 0 < rank s → rank (f s) + 1 = rank s) :
    StackImplements R (StackProg.loop test p) (fun s => (f^[rank s]) s)
      (fun s => stackLoopCost f cost (rank s) s) := by
  intro s l hr
  exact loop R p test f cost rank hp ht hd (rank s) s l hr rfl

end CookSource_stack_specification_loop
namespace CookPvsNP
alias stack_specification_loop := _root_.CookSource_stack_specification_loop.solution
end CookPvsNP

namespace CookSource_stack_specification_seq
-- Prove2me | solution 1 for CookPvsNP.stack_specification_seq
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:43:45.370574+00:00
-- url     : https://prove2.me/submissions/b59935a5-89e7-4680-805d-2c792c87bc36


set_option autoImplicit false
open CookPvsNP

theorem solution {K A S : Type} (R : S → (K → List A) → Prop)
    (p q : StackProg K A) (f g : S → S) (c d : S → ℕ)
    (hp : StackImplements R p f c) (hq : StackImplements R q g d) :
    StackImplements R (p.seq q) (g ∘ f) (fun s => c s + 1 + d (f s)) := by
  intro s l hr
  obtain ⟨n, l', hn, he, hr'⟩ := hp s l hr
  obtain ⟨m, l'', hm, he', hr''⟩ := hq (f s) l' hr'
  exact ⟨n + 1 + m, l'', by dsimp only; omega, he.seq he', hr''⟩

end CookSource_stack_specification_seq
namespace CookPvsNP
alias stack_specification_seq := _root_.CookSource_stack_specification_seq.solution
end CookPvsNP

namespace CookSource_stack_sync_pop
-- Prove2me | solution 1 for CookPvsNP.stack_sync_pop
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:04:00.286214+00:00
-- url     : https://prove2.me/submissions/10b2aa6f-21dc-46d7-a808-dd1b15c829dc


set_option autoImplicit false
open CookPvsNP

private theorem sync_pop {K A : Type} [DecidableEq K] (i j : K) (hne : i ≠ j)
    (w v : List A) (s : K → List A) (hi : s i = w) (hj : s j = v) :
    (syncPopProg i j).Exec s
      (Function.update (Function.update s i (w.drop (min w.length v.length))) j
        (v.drop (min w.length v.length))) (3 * min w.length v.length + 1) := by
  induction w generalizing s v with
  | nil =>
    simp only [List.length_nil, Nat.zero_min, List.drop_zero, Nat.mul_zero, Nat.zero_add]
    have hf : Function.update (Function.update s i []) j v = s := by
      rw [← hi, Function.update_eq_self, ← hj, Function.update_eq_self]
    rw [hf]
    exact .loopFalse (by simp [hi])
  | cons a w ih =>
    cases v with
    | nil =>
      simp only [List.length_nil, Nat.min_zero, List.drop_zero, Nat.mul_zero, Nat.zero_add]
      have hf : Function.update (Function.update s i (a :: w)) j [] = s := by
        rw [← hi, Function.update_eq_self, ← hj, Function.update_eq_self]
      rw [hf]
      exact .loopFalse (by simp [hj])
    | cons b v =>
      let s' := StackProg.applyAct (syncPopAct i j) s
      have hi' : s' i = w := by simp [s', StackProg.applyAct, syncPopAct, StackAct.apply, hi]
      have hj' : s' j = v := by simp [s', StackProg.applyAct, syncPopAct, StackAct.apply, hj]
      have he := StackProg.Exec.loopTrue (by simp [hi, hj])
        (StackProg.Exec.act (syncPopAct i j) s) (ih v s' hi' hj')
      have hf : Function.update (Function.update s' i (w.drop (min w.length v.length))) j
          (v.drop (min w.length v.length)) =
          Function.update (Function.update s i ((a :: w).drop (min (a :: w).length (b :: v).length))) j
          ((b :: v).drop (min (a :: w).length (b :: v).length)) := by
        funext k
        by_cases hk : k = i
        · subst k; simp [Function.update, hne]
        by_cases hk' : k = j
        · subst k; simp [Function.update]
        · simp [Function.update, hk, hk', s', StackProg.applyAct, syncPopAct, StackAct.apply]
      rw [hf] at he
      convert he using 1 <;> first | rfl | (simp; omega)

theorem solution {K A : Type} [DecidableEq K] (i j : K) (hne : i ≠ j) (s : K → List A) :
    let m := min (s i).length (s j).length
    (syncPopProg i j).Exec s (Function.update (Function.update s i ((s i).drop m)) j ((s j).drop m))
      (3 * m + 1) := by
  exact sync_pop i j hne (s i) (s j) s rfl rfl

end CookSource_stack_sync_pop
namespace CookPvsNP
alias stack_sync_pop := _root_.CookSource_stack_sync_pop.solution
end CookPvsNP

end

/- Complete checked body: ReductionCorrectness -/
section

set_option autoImplicit false

namespace ResourceScheduling.ChainProof

open ResourceScheduling.Chain CookPvsNP

theorem chainReduction_correct (w : List USym) :
    w ∈ unaryLang ThreePartition.code ThreePartition.IsYes ↔
      chainReduction w ∈ unaryLang Instance.decisionCode P2Res111Chain := by
  constructor
  · rintro ⟨P, hP, rfl⟩
    refine ⟨(P.chainInstance, 2 * P.t * P.b),
      ⟨chain_instance_class P hP.1, (chain_schedule_iff P hP.1).mp hP.2⟩,
      chainReduction_valid P hP.1⟩
  · intro hw
    rcases chainReduction_spec w with he | ⟨P, hP, hcode, hout⟩
    · rw [he] at hw
      exact (empty_not_target hw).elim
    · obtain ⟨x, hx, he⟩ := hw
      have hex : (P.chainInstance, 2 * P.t * P.b) = x :=
        unary_decisionCode_injective (hout.symm.trans he)
      subst x
      exact ⟨P, ⟨hP, (chain_schedule_iff P hP).mpr hx.2⟩, hcode⟩

theorem chain_hardness_transfer (hpoly : PolyTimeComputable chainReduction)
    (h3P : StronglyNPHard ThreePartition.code ThreePartition.IsYes) :
    StronglyNPHard Instance.decisionCode P2Res111Chain := by
  intro Sym instF instN L hL
  let := instF
  let := instN
  exact polyReducible_trans (h3P Sym L hL)
    ⟨chainReduction, hpoly, chainReduction_correct⟩

end ResourceScheduling.ChainProof

end

/- Complete checked body: ReductionProgram -/
section

open ResourceScheduling.Graph

namespace ResourceScheduling.ChainProof

inductive ReductionReg where
  | t | b | a | parseOk | ok | pos | bit | count | sumA | prod | jobs | horizon
  | arcCount | tmp | diff | blockCounter | jobCounter | scanCounter | flag | offset
  | len | zero | one
  deriving DecidableEq

instance : Fintype ReductionReg where
  elems := {.t, .b, .a, .parseOk, .ok, .pos, .bit, .count, .sumA, .prod, .jobs, .horizon,
    .arcCount, .tmp, .diff, .blockCounter, .jobCounter, .scanCounter, .flag, .offset,
    .len, .zero, .one}
  complete := by intro x; cases x <;> simp

namespace ReductionProgram

open ReductionReg

abbrev Code := RAMCode ReductionReg

def sequence : List Code → Code
  | [] => .skip
  | p :: ps => .seq p (sequence ps)

def const (v : ReductionReg) (n : ℕ) : Code :=
  (RAMCode.zero v).seq (sequence (List.replicate n (.inc v)))

def scale (n : ℕ) (src dst : ReductionReg) (h : src ≠ dst) : Code :=
  (RAMCode.zero dst).seq (sequence (List.replicate n (.add src dst h)))

def assertPos (v : ReductionReg) : Code := .branch v .skip (.zero ok)
def assertZero (v : ReductionReg) : Code := .branch v (.zero ok) .skip

def assertEq (i j : ReductionReg) : Code := sequence
  [.sub i j diff, assertZero diff, .sub j i diff, assertZero diff]

/-- Read every bit of the retained item word; invoke `row` at each separator. -/
def scanRows (row : Code) : Code := sequence
  [.zero a, .zero pos, .length scanCounter,
   .loop scanCounter (sequence
     [.bit pos bit, .branch bit (.inc a) (row.seq (.zero a)), .inc pos])]

def validateRow : Code := sequence
  [.inc count, .add a sumA (by decide),
   scale 4 a tmp (by decide), .sub tmp b diff, assertPos diff,
   scale 2 a tmp (by decide), .sub b tmp diff, assertPos diff]

def validate : Code := sequence
  [const ok 1, const one 1,
   .parse t parseOk (by decide), assertPos parseOk,
   .parse b parseOk (by decide), assertPos parseOk, assertPos b,
   .mul t b prod (by decide), .zero count, .zero sumA,
   scanRows validateRow, assertZero a,
   scale 3 t tmp (by decide), assertEq count tmp, assertEq sumA prod]

def emitRowRequirements : Code := sequence
  [.copy a jobCounter (by decide), .loop jobCounter (.emit zero),
   .copy a jobCounter (by decide), .loop jobCounter (.emit one)]

/-- Emit consecutive arc index pairs of one chain, preserving zero-length chains. -/
def emitChain : Code := .branch len (sequence
  [.copy len jobCounter (by decide), .dec jobCounter,
   .loop jobCounter (sequence [.emit offset, .inc offset, .emit offset]),
   .inc offset]) .skip

def emitRowArcs : Code := (scale 2 a len (by decide)).seq emitChain

def emitInstance : Code := sequence
  [scale 4 prod jobs (by decide), scale 2 prod horizon (by decide),
   .emit jobs, const tmp 2, .emit tmp, .emit one, .emit one,
   scale 2 t blockCounter (by decide), const flag 1,
   .loop blockCounter (sequence
     [.copy b jobCounter (by decide), .loop jobCounter (.emit flag), .sub one flag flag]),
   scanRows emitRowRequirements,
   scale 3 t tmp (by decide), .inc tmp, .sub jobs tmp arcCount, .emit arcCount,
   .zero offset, .copy horizon len (by decide), emitChain,
   scanRows emitRowArcs, .emit horizon]

/-- The total register program validates before emitting any output. -/
def program : Code := validate.seq (.branch ok emitInstance .skip)

end ReductionProgram
end ResourceScheduling.ChainProof
end

/- Complete checked body: ProgramElementary -/
section

open ResourceScheduling.Graph

namespace ResourceScheduling.ChainProof

@[simp] theorem ram_set_self {V : Type} [DecidableEq V] (s : RAMState V) (v : V) :
    s.set v (s.val v) = s := by
  cases s
  simp [RAMState.set]

@[simp] theorem ram_set_set {V : Type} [DecidableEq V] (s : RAMState V)
    (v : V) (a b : ℕ) : (s.set v a).set v b = s.set v b := by
  cases s
  simp [RAMState.set, Function.update_idem]

theorem iterate_inc_eval {V : Type} [DecidableEq V] (v : V) (n : ℕ) (s : RAMState V) :
    ((RAMCode.inc v).eval^[n]) s = s.set v (s.val v + n) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih]
      simp [RAMCode.eval, RAMState.set, Function.update_idem, Nat.add_assoc, Nat.add_comm]

theorem iterate_add_eval {V : Type} [DecidableEq V] (src dst : V) (h : src ≠ dst)
    (n : ℕ) (s : RAMState V) :
    ((RAMCode.add src dst h).eval^[n]) s = s.set dst (n * s.val src + s.val dst) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih]
      simp [RAMCode.eval, RAMState.set, h, Function.update_idem, Nat.add_mul,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

namespace ReductionProgram

theorem sequence_eval_append (ps qs : List Code) (s : RAMState ReductionReg) :
    (sequence (ps ++ qs)).eval s = (sequence qs).eval ((sequence ps).eval s) := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih => simpa only [List.cons_append, sequence, RAMCode.eval] using ih (p.eval s)

theorem sequence_replicate_eval (n : ℕ) (p : Code) (s : RAMState ReductionReg) :
    (sequence (List.replicate n p)).eval s = (p.eval^[n]) s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      simpa only [List.replicate_succ, sequence, RAMCode.eval,
        Function.iterate_succ_apply] using ih (p.eval s)

theorem const_eval (v : ReductionReg) (n : ℕ) (s : RAMState ReductionReg) :
    (const v n).eval s = s.set v n := by
  rw [const, RAMCode.eval, sequence_replicate_eval, iterate_inc_eval]
  simp [RAMCode.eval, RAMState.set, Function.update_idem]

theorem scale_eval (n : ℕ) (src dst : ReductionReg) (h : src ≠ dst)
    (s : RAMState ReductionReg) :
    (scale n src dst h).eval s = s.set dst (n * s.val src) := by
  rw [scale, RAMCode.eval, sequence_replicate_eval, iterate_add_eval]
  simp [RAMCode.eval, RAMState.set, h, Function.update_idem]

theorem program_valid : program.Valid := by
  simp [program, validate, emitInstance, emitRowArcs, emitChain, emitRowRequirements,
    scanRows, validateRow, assertPos, assertZero, assertEq, const, scale, sequence,
    RAMCode.Valid, RAMCode.writes]

end ReductionProgram
end ResourceScheduling.ChainProof

end

/- Complete checked body: RAMStateLemmas -/
section

set_option autoImplicit false

open ResourceScheduling.Graph

namespace ResourceScheduling.ChainProof

theorem ramState_ext {V : Type} {s t : RAMState V} (hv : s.val = t.val)
    (hw : s.word = t.word) (ho : s.out = t.out) : s = t := by
  cases s
  cases t
  cases hv
  cases hw
  cases ho
  rfl

end ResourceScheduling.ChainProof
end

/- Complete checked body: AttributedRAM -/
section

set_option autoImplicit false

namespace RAMSource_ram_frames
-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_frames
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:04:03.252472+00:00
-- url     : https://prove2.me/submissions/13f2993b-9039-4cd4-a5c5-38f4b2881a79


set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph

theorem solution {V : Type} [DecidableEq V] (s : RAMState V)
    (l : RAMWire V → List Letter) (hr : RAMRep s l) :
    (∀ v w, RAMRep (s.set v w.length) (Function.update l (ramReg v) w)) ∧
    (∀ w, RAMRep { s with word := w } (Function.update l ramInput w)) ∧
    (∀ w, RAMRep { s with out := w } (Function.update l ramOutput w)) ∧
    (∀ v, ((l (ramReg v)).head?).isSome = decide (0 < s.val v)) := by
  rcases hr with ⟨hv, hi, ho, ht⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v w
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j
      by_cases h : j = v
      · subst j; simp [RAMState.set]
      · simpa [RAMState.set, ramReg, Function.update, h] using hv j
    · simpa [RAMState.set, ramReg, ramInput] using hi
    · simpa [RAMState.set, ramReg, ramOutput] using ho
    · intro j; simpa [ramReg, ramTmp] using ht j
  · intro w
    refine ⟨?_, by simp, ?_, ?_⟩
    · intro j; simpa [ramReg, ramInput] using hv j
    · simpa [ramInput, ramOutput] using ho
    · intro j; simpa [ramInput, ramTmp] using ht j
  · intro w
    refine ⟨?_, ?_, by simp, ?_⟩
    · intro j; simpa [ramReg, ramOutput] using hv j
    · simpa [ramInput, ramOutput] using hi
    · intro j; simpa [ramOutput, ramTmp] using ht j
  · intro v
    rw [← hv v]
    cases l (ramReg v) <;> simp

end RAMSource_ram_frames
namespace ResourceScheduling.Graph
alias ram_frames := _root_.RAMSource_ram_frames.solution
end ResourceScheduling.Graph

namespace RAMSource_ram_basic
-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_basic
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:38:49.160985+00:00
-- url     : https://prove2.me/submissions/19ded5bf-1a7a-4a90-95ce-b6db8e5b9a3f


set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph

theorem solution {V : Type} [DecidableEq V] (v : V) :
    StackImplements RAMRep (ramSkip (V := V)) id (fun _ => 1) ∧
    StackImplements RAMRep (ramZero v) (fun s => s.set v 0) (fun s => 3 * s.val v + 1) ∧
    StackImplements RAMRep (ramInc v) (fun s => s.set v (s.val v + 1)) (fun _ => 1) ∧
    StackImplements RAMRep (ramDec v) (fun s => s.set v (s.val v - 1)) (fun _ => 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s l hr
    exact ⟨1, l, le_rfl, StackProg.Exec.act (fun _ _ => .keep) l, hr⟩
  · intro s l hr
    refine ⟨3 * (l (ramReg v)).length + 1, Function.update l (ramReg v) [], ?_,
      (stack_basic_macros (ramReg v) l).2.2, ?_⟩
    · simp [hr.1 v]
    · exact (ram_frames s l hr).1 v []
  · intro s l hr
    refine ⟨1, _, le_rfl, (stack_basic_macros (ramReg v) l).1 Letter.one, ?_⟩
    simpa [hr.1 v] using (ram_frames s l hr).1 v (Letter.one :: l (ramReg v))
  · intro s l hr
    refine ⟨1, _, le_rfl, (stack_basic_macros (ramReg v) l).2.1, ?_⟩
    simpa [hr.1 v] using (ram_frames s l hr).1 v (l (ramReg v)).tail

end RAMSource_ram_basic
namespace ResourceScheduling.Graph
alias ram_basic := _root_.RAMSource_ram_basic.solution
end ResourceScheduling.Graph

namespace RAMSource_ram_bound_set
-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_bound_set
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T15:56:18.251991+00:00
-- url     : https://prove2.me/submissions/165eee9f-fe46-45e1-a2d4-44fb5253514c


set_option autoImplicit false
open ResourceScheduling.Graph

theorem solution {V : Type} [DecidableEq V] (B : ℕ) (s : RAMState V) (hs : RAMBound B s)
    (v : V) (a : ℕ) (ha : a ≤ B) : RAMBound B (s.set v a) := by
  refine ⟨?_, hs.2⟩
  intro j
  by_cases h : j = v
  · subst j; simpa [RAMState.set] using ha
  · simpa [RAMState.set, h] using hs.1 j

end RAMSource_ram_bound_set
namespace ResourceScheduling.Graph
alias ram_bound_set := _root_.RAMSource_ram_bound_set.solution
end ResourceScheduling.Graph

namespace RAMSource_ram_budget
-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_budget
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T15:42:33.157977+00:00
-- url     : https://prove2.me/submissions/e4aba728-7e21-4483-97bd-ba2a9eba8a3e


set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph

private theorem join_bound (B a b A C d e : ℕ)
    (ha : a ≤ A * (B + 1)^d) (hb : b ≤ C * (B + 1)^e) :
    a + b + 1 ≤ (A + C + 1) * (B + 1)^(max d e) := by
  have hd := Nat.mul_le_mul_left A (pow_le_pow_right' (by omega : 1 ≤ B + 1) (le_max_left d e))
  have he := Nat.mul_le_mul_left C (pow_le_pow_right' (by omega : 1 ≤ B + 1) (le_max_right d e))
  have hp := one_le_pow₀ (n := max d e) (by omega : 1 ≤ B + 1)
  nlinarith

theorem solution {V : Type} [DecidableEq V] (p : RAMCode V) (B : ℕ) (s : RAMState V)
    (h : p.Bounded B s) : p.cost s ≤ p.weight * (B + 1)^p.degree := by
  induction p generalizing s with
  | seq p q ihp ihq =>
    have hh := join_bound B _ _ _ _ _ _ (ihp s h.1) (ihq (p.eval s) h.2)
    simpa [RAMCode.cost, RAMCode.weight, RAMCode.degree, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hh
  | branch v p q ihp ihq =>
    have hh := join_bound B _ _ _ _ _ _ (ihp s h.1) (ihq s h.2)
    have hm : max (p.cost s) (q.cost s) ≤ p.cost s + q.cost s := max_le (by omega) (by omega)
    dsimp only [RAMCode.cost, RAMCode.weight, RAMCode.degree]; omega
  | loop v p ih =>
    let f := fun s : RAMState V => p.eval (s.set v (s.val v - 1))
    have hc : ∀ i ∈ Finset.range (s.val v),
        1 + 1 + p.cost (((f^[i]) s).set v (((f^[i]) s).val v - 1)) + 2 ≤
          p.weight * (B + 1)^p.degree + 4 := by
      intro i hi
      have hh := ih _ (h.2 i (Finset.mem_range.mp hi))
      dsimp [f] at ⊢; omega
    have hh := Finset.sum_le_sum hc
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hh
    have hn : s.val v ≤ B := h.1.1 v
    have hp := one_le_pow₀ (n := p.degree) (by omega : 1 ≤ B + 1)
    change (∑ i ∈ Finset.range (s.val v),
      (1 + 1 + p.cost (((f^[i]) s).set v (((f^[i]) s).val v - 1)) + 2)) + 1 ≤ _
    dsimp only [RAMCode.weight, RAMCode.degree]
    rw [pow_succ]
    have hm := Nat.mul_le_mul_right (p.weight * (B + 1)^p.degree + 4) hn
    nlinarith
  | mul i j dst hneq =>
    have hi := h.1 i; have hj := h.1 j; have hd := h.1 dst
    dsimp only [RAMCode.cost, RAMCode.weight, RAMCode.degree]
    have hm := Nat.mul_le_mul hi hj
    nlinarith
  | sub i j dst =>
    have hi := h.1 i; have hj := h.1 j; have hd := h.1 dst
    dsimp only [RAMCode.cost, RAMCode.weight, RAMCode.degree]; nlinarith
  | bit i dst =>
    have hi := h.1 i; have hd := h.1 dst; have hw := h.2
    dsimp only [RAMCode.cost, RAMCode.weight, RAMCode.degree]; nlinarith
  | copy i dst hneq =>
    have hi := h.1 i; have hd := h.1 dst
    dsimp only [RAMCode.cost, RAMCode.weight, RAMCode.degree]; nlinarith
  | parse t good hneq =>
    have ht := h.1 t; have hg := h.1 good; have hw := h.2
    dsimp only [RAMCode.cost, RAMCode.weight, RAMCode.degree]; nlinarith
  | length dst =>
    have hd := h.1 dst; have hw := h.2
    dsimp only [RAMCode.cost, RAMCode.weight, RAMCode.degree]; nlinarith
  | zero v | emit v | add v _ _ =>
    have hv := h.1 v
    dsimp only [RAMCode.cost, RAMCode.weight, RAMCode.degree]; nlinarith
  | _ =>
    dsimp only [RAMCode.cost, RAMCode.weight, RAMCode.degree]
    exact Nat.succ_le_of_lt (by positivity)

end RAMSource_ram_budget
namespace ResourceScheduling.Graph
alias ram_budget := _root_.RAMSource_ram_budget.solution
end ResourceScheduling.Graph

namespace RAMSource_ram_copy
-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_copy
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:38:50.471085+00:00
-- url     : https://prove2.me/submissions/da7c0778-61e1-41db-b3e9-09cc59c67328


set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph

theorem solution {V : Type} [DecidableEq V] (src : RAMWire V) (v : V)
    (hd : src ≠ ramReg v) (ht : src ≠ ramTmp 0) (f : RAMState V → ℕ)
    (hf : ∀ s l, RAMRep s l → (l src).length = f s) :
    StackImplements RAMRep (ramAppend src v)
      (fun s => s.set v (f s + s.val v)) (fun s => 6 * f s + 3) ∧
    StackImplements RAMRep (ramAssign src v)
      (fun s => s.set v (f s)) (fun s => 3 * s.val v + 6 * f s + 5) := by
  have hdt : ramReg v ≠ (ramTmp 0 : RAMWire V) := by simp [ramReg, ramTmp]
  constructor
  · intro s l hr
    have he := stack_copy src (ramReg v) (ramTmp 0) hd ht hdt l (hr.2.2.2 0)
    refine ⟨6 * (l src).length + 3, _, ?_, he, ?_⟩
    · simp [hf s l hr]
    · simpa [hf s l hr, hr.1 v] using
        (ram_frames s l hr).1 v (l src ++ l (ramReg v))
  · intro s l hr
    let l' := Function.update l (ramReg v) []
    have hl : l' src = l src := by simp [l', hd]
    have he := stack_copy src (ramReg v) (ramTmp 0) hd ht hdt l'
      (by simpa [l', ramReg, ramTmp] using hr.2.2.2 0)
    have hout : Function.update l' (ramReg v) (l' src ++ l' (ramReg v)) =
        Function.update l (ramReg v) (l src) := by simp [l', hd]
    rw [hout] at he
    refine ⟨3 * (l (ramReg v)).length + 1 + 1 + (6 * (l' src).length + 3), _, ?_,
      ((stack_basic_macros (ramReg v) l).2.2).seq he, ?_⟩
    · simp only [hl, hf s l hr, hr.1 v]; omega
    · simpa [hf s l hr] using (ram_frames s l hr).1 v (l src)

end RAMSource_ram_copy
namespace ResourceScheduling.Graph
alias ram_copy := _root_.RAMSource_ram_copy.solution
end ResourceScheduling.Graph

namespace RAMSource_ram_sub
-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_sub
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:55:55.12915+00:00
-- url     : https://prove2.me/submissions/6ab3321c-bca4-44ab-8096-558306abb8f5


set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph

theorem solution {V : Type} [DecidableEq V] (i j dst : V) :
    StackImplements RAMRep (ramSub i j dst)
      (fun s => s.set dst (s.val i - s.val j))
      (fun s => 9 * s.val i + 9 * s.val j + 3 * s.val dst + 13) := by
  intro s l hr
  let x := l (ramReg i)
  let y := l (ramReg j)
  let l1 := Function.update l (ramTmp 0) x
  let l2 := Function.update l1 (ramTmp 1) y
  let l3 := Function.update l (ramTmp 0) (x.drop y.length)
  let l4 := Function.update l3 (ramReg dst) []
  have he1 := stack_copy (ramReg i) (ramTmp 0) (ramTmp 2)
    (by simp [ramReg, ramTmp]) (by simp [ramReg, ramTmp]) (by simp [ramTmp]) l (hr.2.2.2 2)
  simp only [hr.2.2.2 0, List.append_nil] at he1
  have he2 := stack_copy (ramReg j) (ramTmp 1) (ramTmp 2)
    (by simp [ramReg, ramTmp]) (by simp [ramReg, ramTmp]) (by simp [ramTmp]) l1
    (by simpa [l1, ramTmp] using hr.2.2.2 2)
  have hy : l1 (ramReg j) = y := by simp [l1, y, ramReg, ramTmp]
  have he0 : l1 (ramTmp 1) = [] := by simpa [l1, ramTmp] using hr.2.2.2 1
  simp only [hy, he0, List.append_nil] at he2
  have he3 := stack_consume (ramTmp 1) (fun k => decide (k = ramTmp 0)) l2
  have hf3 : consumeStore (ramTmp 1) (fun k => decide (k = ramTmp 0)) l2 = l3 := by
    funext k
    by_cases h0 : k = ramTmp 0
    · subst k; simp [consumeStore, l2, l1, l3, ramTmp]
    by_cases h1 : k = ramTmp 1
    · subst k; simpa [consumeStore, l3, ramTmp] using hr.2.2.2 1
    · simp [consumeStore, l2, l1, l3, h0, h1]
  rw [hf3] at he3
  have he4 := (stack_basic_macros (ramReg dst) l3).2.2
  have he5 := stack_transfer (ramTmp 0) (fun k => decide (k = ramReg dst)) l4
  have hf5 : transferStore (ramTmp 0) (fun k => decide (k = ramReg dst)) l4 =
      Function.update l (ramReg dst) (x.drop y.length).reverse := by
    funext k
    by_cases hd : k = ramReg dst
    · subst k; simp [transferStore, l4, l3, ramReg, ramTmp]
    by_cases h0 : k = ramTmp 0
    · subst k; simpa [transferStore, ramReg, ramTmp] using hr.2.2.2 0
    · simp [transferStore, l4, l3, hd, h0]
  rw [hf5] at he5
  have he := he1.seq (he2.seq (he3.seq (he4.seq he5)))
  refine ⟨_, _, ?_, he, ?_⟩
  · simp only [l4, l3, l2, l1, ramReg, ramTmp, Function.update_self,
      Function.update_of_ne (by simp : (Sum.inl (Sum.inr (0 : Fin 6)) : RAMWire V) ≠
        Sum.inl (Sum.inl dst)),
      Function.update_of_ne (by simp : (Sum.inl (Sum.inl dst) : RAMWire V) ≠
        Sum.inl (Sum.inr (0 : Fin 6))), List.length_drop]
    change 6 * x.length + 3 + 1 + (6 * y.length + 3 + 1 + (3 * y.length + 1 + 1 +
      (3 * (l (ramReg dst)).length + 1 + 1 + (3 * (x.length - y.length) + 1)))) ≤ _
    have hx := hr.1 i; have hy' := hr.1 j; have hd := hr.1 dst
    dsimp [x, y] at *; omega
  · simpa [x, y, hr.1 i, hr.1 j] using
      (ram_frames s l hr).1 dst (x.drop y.length).reverse

end RAMSource_ram_sub
namespace ResourceScheduling.Graph
alias ram_sub := _root_.RAMSource_ram_sub.solution
end ResourceScheduling.Graph

namespace RAMSource_ram_mul
-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_mul
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:55:55.790242+00:00
-- url     : https://prove2.me/submissions/322be5f2-76ac-4fe1-88d3-eadac7d8b789


set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph

theorem solution {V : Type} [DecidableEq V] (i j dst : V) (h : j ≠ dst) :
    StackImplements RAMRep (ramMul i j dst h)
      (fun s => s.set dst (s.val i * s.val j))
      (fun s => (6 * s.val j + 13) * s.val i + 3 * s.val dst + 7) := by
  intro s l hr
  let x := l (ramReg i)
  let y := l (ramReg j)
  let l1 := Function.update l (ramTmp 0) x
  let l2 := Function.update l1 (ramReg dst) []
  have he1 := stack_copy (ramReg i) (ramTmp 0) (ramTmp 1)
    (by simp [ramReg, ramTmp]) (by simp [ramReg, ramTmp]) (by simp [ramTmp]) l (hr.2.2.2 1)
  simp only [hr.2.2.2 0, List.append_nil] at he1
  have he2 := (stack_basic_macros (ramReg dst) l1).2.2
  have he3 := stack_repeat_copy (ramMulPorts j dst h) l2
    (by simpa [ramMulPorts, l2, l1, ramReg, ramTmp] using hr.2.2.2 1)
  change (repeatCopyProg (ramMulPorts j dst h)).Exec l2
    (Function.update (Function.update l2 (ramTmp 0) []) (ramReg dst)
      ((List.replicate (l2 (ramTmp 0)).length (l2 (ramReg j))).flatten ++ l2 (ramReg dst)))
    ((6 * (l2 (ramReg j)).length + 7) * (l2 (ramTmp 0)).length + 1) at he3
  have hf : Function.update (Function.update l2 (ramTmp 0) []) (ramReg dst)
      ((List.replicate (l2 (ramTmp 0)).length (l2 (ramReg j))).flatten ++ l2 (ramReg dst)) =
      Function.update l (ramReg dst) (List.replicate x.length y).flatten := by
    funext k
    by_cases hd : k = ramReg dst
    · subst k; simp [l2, l1, x, y, ramReg, ramTmp, h]
    by_cases ht : k = ramTmp 0
    · subst k
      simpa [l2, l1, ramReg, ramTmp] using (hr.2.2.2 0).symm
    · simp [l2, l1, hd, ht]
  rw [hf] at he3
  refine ⟨_, _, ?_, he1.seq (he2.seq he3), ?_⟩
  · have hy : (l2 (ramReg j)).length = s.val j := by
      simpa [l2, l1, ramReg, ramTmp, h] using hr.1 j
    have hx : (l2 (ramTmp 0)).length = s.val i := by
      simpa [l2, l1, x, ramReg, ramTmp] using hr.1 i
    have hd : (l1 (ramReg dst)).length = s.val dst := by
      simpa [l1, ramReg, ramTmp] using hr.1 dst
    rw [hy, hx, hd, hr.1 i]; dsimp only; nlinarith
  · simpa [List.length_flatten, x, y, hr.1 i, hr.1 j] using
      (ram_frames s l hr).1 dst (List.replicate x.length y).flatten

end RAMSource_ram_mul
namespace ResourceScheduling.Graph
alias ram_mul := _root_.RAMSource_ram_mul.solution
end ResourceScheduling.Graph

namespace RAMSource_ram_read_bit
-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_read_bit
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:38:52.922593+00:00
-- url     : https://prove2.me/submissions/ae378cde-1300-48a6-b9ce-d18cc35c88a5


set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph

theorem solution {V : Type} [DecidableEq V] (i dst : V) :
    StackImplements RAMRep (ramReadBit i dst)
      (fun s => s.set dst (if s.word.getD (s.val i) Letter.sep = Letter.one then 1 else 0))
      (fun s => 9 * s.word.length + 9 * s.val i + 3 * s.val dst + 17) := by
  intro s l hr
  let a := s.word.getD (s.val i) Letter.sep
  let l1 := Function.update l (ramTmp 0) [a]
  let l2 := Function.update l1 (ramReg dst) []
  let w := if a = Letter.one then [Letter.one] else []
  obtain ⟨n, hn, he⟩ := stack_lookup (ramLookupPorts i) Letter.sep l
    (hr.2.2.2 0) (hr.2.2.2 1) (hr.2.2.2 2) (hr.2.2.2 3)
  change n ≤ 9 * (l ramInput).length + 9 * (l (ramReg i)).length + 13 at hn
  change (lookupProg (ramLookupPorts i) Letter.sep).Exec l
    (Function.update l (ramTmp 0) [(l ramInput).getD (l (ramReg i)).length Letter.sep]) n at he
  rw [hr.2.1, hr.1 i] at he hn
  have hzero := (stack_basic_macros (ramReg dst) l1).2.2
  let act := fun (h : RAMWire V → Option Letter) k =>
    if k = ramTmp 0 then StackAct.pop else
    if k = ramReg dst ∧ h (ramTmp 0) = some Letter.one then .push Letter.one else .keep
  have hout : StackProg.applyAct act l2 = Function.update l (ramReg dst) w := by
    funext k
    by_cases hk : k = ramTmp 0
    · subst k
      simpa [StackProg.applyAct, act, l2, l1, ramTmp, ramReg, StackAct.apply]
        using hr.2.2.2 0
    by_cases hd : k = ramReg dst
    · subst k
      by_cases ha : a = Letter.one <;>
        simp [StackProg.applyAct, act, l2, l1, ramTmp, ramReg, StackAct.apply, w, ha]
    · simp [StackProg.applyAct, act, l2, l1, StackAct.apply, hk, hd]
  have hend := StackProg.Exec.act act l2
  rw [hout] at hend
  refine ⟨n + 1 + (3 * (l1 (ramReg dst)).length + 1 + 1 + 1), _, ?_,
    he.seq (hzero.seq hend), ?_⟩
  · have hd : (l1 (ramReg dst)).length = s.val dst := by
      simpa [l1, ramReg, ramTmp] using hr.1 dst
    rw [hd]; dsimp only; omega
  · have hw : w.length = if a = Letter.one then 1 else 0 := by dsimp [w]; split <;> rfl
    simpa only [hw] using (ram_frames s l hr).1 dst w

end RAMSource_ram_read_bit
namespace ResourceScheduling.Graph
alias ram_read_bit := _root_.RAMSource_ram_read_bit.solution
end ResourceScheduling.Graph

namespace RAMSource_stack_emit
-- Prove2me | solution 1 for ResourceScheduling.Graph.stack_emit
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:18:23.161927+00:00
-- url     : https://prove2.me/submissions/7f8e7ad4-83a5-49b4-9b02-d85c9119b6c2


set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph

theorem solution {K : Type} [DecidableEq K] (r : Fin 4 ↪ K)
    (s : K → List Letter) (h2 : s (r 2) = []) (h3 : s (r 3) = []) :
    (emitUnaryProg r).Exec s
      (Function.update s (r 1) (Letter.sep :: (List.replicate (s (r 0)).length Letter.one ++ s (r 1))))
      (9 * (s (r 0)).length + 7) := by
  have neq (i j : Fin 4) (h : i ≠ j) : r i ≠ r j := r.injective.ne h
  have eqs (i j : Fin 4) : (r i = r j) ↔ i = j := r.injective.eq_iff
  let s1 := Function.update s (r 2) (s (r 0))
  let s2 := Function.update s (r 1) (List.replicate (s (r 0)).length Letter.one ++ s (r 1))
  have hcopy := stack_copy (r 0) (r 2) (r 3)
    (neq _ _ (by decide)) (neq _ _ (by decide)) (neq _ _ (by decide)) s h3
  simp only [h2, List.append_nil] at hcopy
  have hm := stack_map_transfer (r 2) (fun k => decide (k = r 1)) (fun _ => Letter.one) s1
  have hf : mapTransferStore (r 2) (fun k => decide (k = r 1)) (fun _ => Letter.one) s1 = s2 := by
    funext k
    by_cases hk : k = r 1
    · subst k
      simp [s2, s1, mapTransferStore, eqs]
    by_cases hk' : k = r 2
    · subst k; simp [s2, mapTransferStore, eqs, h2]
    · simp [s2, s1, mapTransferStore, hk, hk']
  rw [hf] at hm
  have hp := (stack_basic_macros (r 1) s2).1 Letter.sep
  have hout : Function.update s2 (r 1) (Letter.sep :: s2 (r 1)) =
      Function.update s (r 1) (Letter.sep :: (List.replicate (s (r 0)).length Letter.one ++ s (r 1))) := by
    simp [s2]
  rw [hout] at hp
  have hprog := StackProg.Exec.seq hcopy (StackProg.Exec.seq hm hp)
  convert hprog using 1 <;> first | rfl | (simp only [s1, Function.update_self]; omega)

end RAMSource_stack_emit
namespace ResourceScheduling.Graph
alias stack_emit := _root_.RAMSource_stack_emit.solution
end ResourceScheduling.Graph

namespace RAMSource_ram_emit
-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_emit
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:38:51.845317+00:00
-- url     : https://prove2.me/submissions/07668816-ab32-4efe-8e50-045f77f4f703


set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph

theorem solution {V : Type} [DecidableEq V] (v : V) :
    StackImplements RAMRep (ramEmit v)
      (fun s => { s with out := Letter.sep :: (List.replicate (s.val v) Letter.one ++ s.out) })
      (fun s => 9 * s.val v + 7) := by
  intro s l hr
  have he := stack_emit (ramEmitPorts v) l (hr.2.2.2 0) (hr.2.2.2 1)
  change (ramEmit v).Exec l (Function.update l ramOutput
    (Letter.sep :: (List.replicate (l (ramReg v)).length Letter.one ++ l ramOutput)))
    (9 * (l (ramReg v)).length + 7) at he
  rw [hr.1 v, hr.2.2.1] at he
  refine ⟨9 * s.val v + 7, _, le_rfl, he, ?_⟩
  exact (ram_frames s l hr).2.2.1 _

end RAMSource_ram_emit
namespace ResourceScheduling.Graph
alias ram_emit := _root_.RAMSource_ram_emit.solution
end ResourceScheduling.Graph

namespace RAMSource_split_ones
-- Prove2me | solution 1 for ResourceScheduling.Graph.split_ones
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:51:11.587626+00:00
-- url     : https://prove2.me/submissions/b4d4eae3-1009-4c05-a4a3-8d852645b5b7


set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph

theorem solution (w : List Letter) :
    w = List.replicate (splitOnes w).1 Letter.one ++ (splitOnes w).2 ∧
    (splitOnes w).2.head? ≠ some Letter.one ∧
    (splitOnes w).1 + (splitOnes w).2.length = w.length ∧
    readUnary w = if (splitOnes w).2 = [] then none
      else some ((splitOnes w).1, (splitOnes w).2.tail) := by
  induction w with
  | nil => simp [splitOnes, readUnary]
  | cons a w ih =>
    cases a with
    | sep => simp [splitOnes, readUnary]
    | one =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [splitOnes, List.replicate_succ] using congrArg (List.cons Letter.one) ih.1
      · exact ih.2.1
      · simp only [splitOnes, List.length_cons]; omega
      · simp only [readUnary, ih.2.2.2, splitOnes]
        by_cases h : (splitOnes w).2 = [] <;> simp [h]

end RAMSource_split_ones
namespace ResourceScheduling.Graph
alias split_ones := _root_.RAMSource_split_ones.solution
end ResourceScheduling.Graph

namespace RAMSource_stack_prefix
-- Prove2me | solution 1 for ResourceScheduling.Graph.stack_prefix
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:43:52.467984+00:00
-- url     : https://prove2.me/submissions/885b9c9d-e75f-433a-8bd0-799b9fb56465


set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph

theorem solution {K : Type} [DecidableEq K] (input count : K) (hne : input ≠ count)
    (t : ℕ) (rest : List Letter) (hstop : rest.head? ≠ some .one)
    (s : K → List Letter) (hs : s input = List.replicate t .one ++ rest) :
    (prefixProg input count).Exec s
      (Function.update (Function.update s input rest) count (List.replicate t .one ++ s count))
      (3 * t + 1) := by
  induction t generalizing s with
  | zero =>
    have hf : Function.update (Function.update s input rest) count ([] ++ s count) = s := by
      funext k
      by_cases hk : k = input
      · subst k; simpa [Function.update, hne] using hs.symm
      by_cases hk' : k = count
      · subst k; simp [Function.update]
      · simp [Function.update, hk, hk']
    simp only [List.replicate_zero, Nat.mul_zero, Nat.zero_add, hf]
    exact .loopFalse (by simpa [hs] using hstop)
  | succ t ih =>
    let s' := StackProg.applyAct (prefixAct input count) s
    have hi : s' input = List.replicate t .one ++ rest := by
      simp [s', StackProg.applyAct, prefixAct, StackAct.apply, hs, List.replicate_succ]
    have hc : s' count = .one :: s count := by
      simp [s', StackProg.applyAct, prefixAct, StackAct.apply, Ne.symm hne]
    have he := StackProg.Exec.loopTrue (by simp [hs, List.replicate_succ])
      (StackProg.Exec.act (prefixAct input count) s) (ih s' hi)
    have hf : Function.update (Function.update s' input rest) count (List.replicate t .one ++ s' count) =
        Function.update (Function.update s input rest) count (List.replicate (t + 1) .one ++ s count) := by
      funext k
      by_cases hk : k = input
      · subst k; simp [Function.update, hne]
      by_cases hk' : k = count
      · subst k
        simp [Function.update, hc, List.replicate_succ', List.append_assoc]
      · simp [Function.update, hk, hk', s', StackProg.applyAct, prefixAct, StackAct.apply]
    rw [hf] at he
    convert he using 1 <;> first | rfl | omega

end RAMSource_stack_prefix
namespace ResourceScheduling.Graph
alias stack_prefix := _root_.RAMSource_stack_prefix.solution
end ResourceScheduling.Graph

namespace RAMSource_ram_parse
-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_parse
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:51:12.335579+00:00
-- url     : https://prove2.me/submissions/63bebfe7-c74e-457d-a150-ed9f2d234572


set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph

theorem solution {V : Type} [DecidableEq V] (t good : V) (hne : t ≠ good) :
    StackImplements RAMRep (ramParse t good) (ramParseState t good)
      (fun s => 3 * s.val t + 3 * s.val good + 3 * s.word.length + 7) := by
  intro s l hr
  let n := (splitOnes s.word).1
  let rest := (splitOnes s.word).2
  let l1 := Function.update l (ramReg t) []
  let l2 := Function.update l1 (ramReg good) []
  let l3 := Function.update (Function.update l2 ramInput rest) (ramReg t) (List.replicate n Letter.one)
  let w := if rest = [] then [] else [Letter.one]
  let l4 := Function.update (Function.update l3 ramInput rest.tail) (ramReg good) w
  have hs := split_ones s.word
  have h2i : l2 ramInput = s.word := by simpa [l2, l1, ramReg, ramInput] using hr.2.1
  have h2t : l2 (ramReg t) = [] := by simp [l2, l1, ramReg, hne]
  have hp := stack_prefix ramInput (ramReg t) (by simp [ramInput, ramReg]) n rest hs.2.1 l2
    (h2i.trans hs.1)
  simp only [h2t, List.append_nil] at hp
  let act := fun (h : RAMWire V → Option Letter) k =>
    if k = ramInput then StackAct.pop else
    if k = ramReg good ∧ (h ramInput).isSome then .push Letter.one else .keep
  have ha : StackProg.applyAct act l3 = l4 := by
    funext k
    by_cases hi : k = ramInput
    · subst k; simp [StackProg.applyAct, act, l3, l4, StackAct.apply, ramReg, ramInput]
    by_cases hg : k = ramReg good
    · subst k
      cases hrest : rest <;> simp [StackProg.applyAct, act, l4, l3, l2, l1, StackAct.apply,
        ramReg, ramInput, Ne.symm hne, w, hrest]
    · simp [StackProg.applyAct, act, l4, StackAct.apply, hi, hg]
  have he := ((stack_basic_macros (ramReg t) l).2.2).seq
    (((stack_basic_macros (ramReg good) l1).2.2).seq
      (hp.seq (StackProg.Exec.act act l3)))
  rw [ha] at he
  refine ⟨_, l4, ?_, he, ?_⟩
  · have hg : (l1 (ramReg good)).length = s.val good := by
      simpa [l1, ramReg, Ne.symm hne] using hr.1 good
    rw [hg, hr.1 t]; dsimp only
    have hn : n ≤ s.word.length := by dsimp [n]; omega
    omega
  · have hv (v : V) : (l (Sum.inl (Sum.inl v))).length = s.val v := hr.1 v
    have ht (j : Fin 6) : l (Sum.inl (Sum.inr j)) = [] := hr.2.2.2 j
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro v
      by_cases hg : v = good
      · subst v
        by_cases hempty : (splitOnes s.word).2 = [] <;>
          simp [l4, w, ramParseState, RAMState.set, rest, hempty]
      by_cases hx : v = t
      · subst v
        simp [l4, l3, l2, l1, ramReg, ramInput, hne, ramParseState, RAMState.set, n]
      · simp [l4, l3, l2, l1, ramReg, ramInput, hg, hx, ramParseState, RAMState.set, hv]
    · simp [l4, ramReg, ramInput, ramParseState, rest]
    · simpa [l4, l3, l2, l1, ramReg, ramInput, ramOutput, ramParseState, RAMState.set]
        using hr.2.2.1
    · intro j
      simp [l4, l3, l2, l1, ramReg, ramInput, ramTmp, ht]

end RAMSource_ram_parse
namespace ResourceScheduling.Graph
alias ram_parse := _root_.RAMSource_ram_parse.solution
end ResourceScheduling.Graph

namespace RAMSource_ram_footprint
-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_footprint
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T15:23:34.151189+00:00
-- url     : https://prove2.me/submissions/12694b08-edec-442d-aa0e-7d841faf9039


set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph

private theorem iter {V : Type} (f : RAMState V → RAMState V) (v : V)
    (h : ∀ s, (f s).val v = s.val v) (n : ℕ) (s : RAMState V) :
    ((f^[n]) s).val v = s.val v := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, ih, h]

theorem solution {V : Type} [DecidableEq V] (p : RAMCode V) (v : V)
    (h : p.writes v = false) (s : RAMState V) : (p.eval s).val v = s.val v := by
  induction p generalizing s with
  | seq p q ihp ihq =>
    simp only [RAMCode.writes, Bool.or_eq_false_iff] at h
    exact (ihq h.2 (p.eval s)).trans (ihp h.1 s)
  | branch j p q ihp ihq =>
    simp only [RAMCode.writes, Bool.or_eq_false_iff] at h
    simp only [RAMCode.eval]; split <;> first | exact ihp h.1 s | exact ihq h.2 s
  | loop j p ih =>
    simp only [RAMCode.writes, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    apply iter
    intro s'
    simpa [RAMState.set, h.1] using ih h.2 (s'.set j (s'.val j - 1))
  | parse t good htg =>
    simp only [RAMCode.writes, decide_eq_false_iff_not, not_or] at h
    simp [RAMCode.eval, ramParseState, RAMState.set, h.1, h.2]
  | _ => simp_all [RAMCode.writes, RAMCode.eval, RAMState.set]

end RAMSource_ram_footprint
namespace ResourceScheduling.Graph
alias ram_footprint := _root_.RAMSource_ram_footprint.solution
end ResourceScheduling.Graph

namespace RAMSource_ram_code_correct
-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_code_correct
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T15:23:35.398545+00:00
-- url     : https://prove2.me/submissions/2baab523-63b1-4dfa-be05-64d00878035d


set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph

theorem solution {V : Type} [DecidableEq V] (p : RAMCode V) (hp : p.Valid) :
    StackImplements RAMRep p.code p.eval p.cost := by
  induction p with
  | skip =>
    intro s l hr
    exact ⟨1, l, le_rfl, StackProg.Exec.act (fun _ _ => .keep) l, hr⟩
  | zero v => exact (ram_basic v).2.1
  | inc v => exact (ram_basic v).2.2.1
  | dec v => exact (ram_basic v).2.2.2
  | copy i v h =>
    exact (ram_copy (ramReg i) v (by simpa [ramReg] using h)
      (by simp [ramReg, ramTmp]) (fun s => s.val i) (fun _ _ hr => hr.1 i)).2
  | add i v h =>
    exact (ram_copy (ramReg i) v (by simpa [ramReg] using h)
      (by simp [ramReg, ramTmp]) (fun s => s.val i) (fun _ _ hr => hr.1 i)).1
  | length v =>
    exact (ram_copy ramInput v (by simp [ramInput, ramReg])
      (by simp [ramInput, ramTmp]) (fun s => s.word.length) (fun _ _ hr => congrArg List.length hr.2.1)).2
  | sub i j v => exact ram_sub i j v
  | mul i j v h => exact ram_mul i j v h
  | bit i v => exact ram_read_bit i v
  | emit v => exact ram_emit v
  | parse t good h => exact ram_parse t good h
  | seq p q ihp ihq =>
    exact stack_specification_seq RAMRep p.code q.code p.eval q.eval p.cost q.cost
      (ihp hp.1) (ihq hp.2)
  | branch v p q ihp ihq =>
    simpa [RAMCode.code, RAMCode.eval, RAMCode.cost] using
      stack_specification_branch RAMRep p.code q.code
        (fun h => (h (ramReg v)).isSome) (fun s => decide (0 < s.val v))
        p.eval q.eval p.cost q.cost (ihp hp.1) (ihq hp.2)
        (fun s l hr => (ram_frames s l hr).2.2.2 v)
  | loop v p ih =>
    have hb := stack_specification_seq RAMRep (ramDec v) p.code
      (fun s => s.set v (s.val v - 1)) p.eval (fun _ => 1) p.cost
      (ram_basic v).2.2.2 (ih hp.1)
    exact stack_specification_loop RAMRep ((ramDec v).seq p.code)
      (fun h => (h (ramReg v)).isSome) (fun s => p.eval (s.set v (s.val v - 1)))
      (fun s => 1 + 1 + p.cost (s.set v (s.val v - 1))) (fun s => s.val v) hb
      (fun s l hr => (ram_frames s l hr).2.2.2 v) (by
        intro s hs
        rw [ram_footprint p v hp.2]
        simp only [RAMState.set, Function.update_self]
        omega)

end RAMSource_ram_code_correct
namespace ResourceScheduling.Graph
alias ram_code_correct := _root_.RAMSource_ram_code_correct.solution
end ResourceScheduling.Graph

namespace RAMSource_ram_field_frame
-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_field_frame
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T15:42:38.381161+00:00
-- url     : https://prove2.me/submissions/92442d0e-d493-4848-8910-7466ec5e5e8d


set_option autoImplicit false
open ResourceScheduling.Graph

private theorem iter {V : Type} (f : RAMState V → RAMState V) (b : Bool)
    (h : ∀ s, (f s).field b = s.field b) (k : ℕ) (s : RAMState V) :
    ((f^[k]) s).field b = s.field b := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, ih, h]

theorem solution {V : Type} [DecidableEq V] (p : RAMCode V) (b : Bool)
    (h : p.effect b = false) (s : RAMState V) : (p.eval s).field b = s.field b := by
  induction p generalizing s with
  | seq p q ihp ihq =>
    simp only [RAMCode.effect, Bool.or_eq_false_iff] at h
    exact (ihq h.2 (p.eval s)).trans (ihp h.1 s)
  | branch j p q ihp ihq =>
    simp only [RAMCode.effect, Bool.or_eq_false_iff] at h
    simp only [RAMCode.eval]; split <;> first | exact ihp h.1 s | exact ihq h.2 s
  | loop j p ih =>
    apply iter
    intro s'
    simpa [RAMState.field, RAMState.set] using ih h (s'.set j (s'.val j - 1))
  | _ => cases b <;> simp_all [RAMCode.effect, RAMCode.eval, RAMState.field, RAMState.set, ramParseState]

end RAMSource_ram_field_frame
namespace ResourceScheduling.Graph
alias ram_field_frame := _root_.RAMSource_ram_field_frame.solution
end ResourceScheduling.Graph

namespace RAMSource_ram_loop_invariant
-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_loop_invariant
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T15:42:36.607857+00:00
-- url     : https://prove2.me/submissions/e4b8df76-8853-40fd-87fd-6e6d6d8a6375


set_option autoImplicit false
open ResourceScheduling.Graph

theorem solution {V : Type} [DecidableEq V] (v : V) (p : RAMCode V)
    (B n : ℕ) (I : ℕ → RAMState V → Prop) (s : RAMState V)
    (hs : RAMBound B s) (hn : s.val v = n) (hi : I 0 s)
    (hstep : ∀ k < n, ∀ x, I k x →
      p.Bounded B (x.set v (x.val v - 1)) ∧ I (k + 1) (p.eval (x.set v (x.val v - 1)))) :
    (RAMCode.loop v p).Bounded B s ∧ I n ((RAMCode.loop v p).eval s) := by
  let f := fun x : RAMState V => p.eval (x.set v (x.val v - 1))
  have hall : ∀ k ≤ n, I k ((f^[k]) s) := by
    intro k hk
    induction k with
    | zero => exact hi
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact (hstep k (by omega) _ (ih (by omega))).2
  refine ⟨⟨hs, ?_⟩, ?_⟩
  · intro k hk
    exact (hstep k (by omega) _ (hall k (by omega))).1
  · simpa only [RAMCode.eval, hn] using hall n le_rfl

end RAMSource_ram_loop_invariant
namespace ResourceScheduling.Graph
alias ram_loop_invariant := _root_.RAMSource_ram_loop_invariant.solution
end ResourceScheduling.Graph

namespace RAMSource_ram_safe_laws
-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_safe_laws
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T15:56:18.995654+00:00
-- url     : https://prove2.me/submissions/da9e53fa-d59f-47e4-b345-9afece07ace9


set_option autoImplicit false
open ResourceScheduling.Graph

theorem solution {V : Type} [DecidableEq V] (p q : RAMCode V) (v : V) (B : ℕ) (s : RAMState V) :
    (RAMBound B s → RAMSafe (.skip : RAMCode V) B s) ∧
    (RAMSafe p B s → RAMSafe q B (p.eval s) → RAMSafe (p.seq q) B s) ∧
    (RAMSafe p B s → RAMSafe q B s → RAMSafe (.branch v p q) B s) := by
  refine ⟨fun h => ⟨h, h⟩, ?_, ?_⟩
  · intro hp hq
    exact ⟨⟨hp.1, hq.1⟩, hq.2⟩
  · intro hp hq
    refine ⟨⟨hp.1, hq.1⟩, ?_⟩
    simp only [RAMCode.eval]
    split <;> first | exact hp.2 | exact hq.2

end RAMSource_ram_safe_laws
namespace ResourceScheduling.Graph
alias ram_safe_laws := _root_.RAMSource_ram_safe_laws.solution
end ResourceScheduling.Graph

end

/- Complete checked body: EmissionBasics -/
section

set_option autoImplicit false

open ResourceScheduling.Graph

namespace ResourceScheduling.ChainProof

def appendOutput {V : Type} (s : RAMState V) (ns : List ℕ) : RAMState V :=
  { s with out := (encNatList ns).reverse ++ s.out }

@[simp] theorem appendOutput_nil {V : Type} (s : RAMState V) : appendOutput s [] = s := by
  cases s
  simp [appendOutput, encNatList]

theorem appendOutput_append {V : Type} (s : RAMState V) (ns ms : List ℕ) :
    appendOutput (appendOutput s ns) ms = appendOutput s (ns ++ ms) := by
  simp [appendOutput, encNatList, List.flatMap_append, List.reverse_append, List.append_assoc]

@[simp] theorem appendOutput_val {V : Type} (s : RAMState V) (ns : List ℕ) :
    (appendOutput s ns).val = s.val := rfl

@[simp] theorem appendOutput_word {V : Type} (s : RAMState V) (ns : List ℕ) :
    (appendOutput s ns).word = s.word := rfl

theorem appendOutput_set {V : Type} [DecidableEq V] (s : RAMState V)
    (ns : List ℕ) (v : V) (n : ℕ) :
    (appendOutput s ns).set v n = appendOutput (s.set v n) ns := rfl

theorem emit_eval {V : Type} [DecidableEq V] (v : V) (s : RAMState V) :
    (RAMCode.emit v).eval s = appendOutput s [s.val v] := by
  simp [RAMCode.eval, appendOutput, encNatList, unary, List.reverse_append]

theorem emit_loop_iter {V : Type} [DecidableEq V] (v c : V) (hvc : v ≠ c)
    (n : ℕ) (s : RAMState V) :
    ((fun s => (RAMCode.emit v).eval (s.set c (s.val c - 1)))^[n]) s =
      appendOutput (s.set c (s.val c - n)) (List.replicate n (s.val v)) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih, emit_eval]
      simp only [appendOutput_val, RAMState.set, Function.update_self, Function.update_of_ne hvc]
      change appendOutput ((appendOutput (s.set c (s.val c - 1)) [s.val v]).set c
        (s.val c - 1 - n)) (List.replicate n (s.val v)) = _
      rw [appendOutput_set, ram_set_set, appendOutput_append]
      rw [show s.val c - 1 - n = s.val c - (n + 1) by omega]
      rfl

theorem emit_loop_eval {V : Type} [DecidableEq V] (v c : V) (hvc : v ≠ c)
    (s : RAMState V) :
    (RAMCode.loop c (.emit v)).eval s =
      appendOutput (s.set c 0) (List.replicate (s.val c) (s.val v)) := by
  rw [RAMCode.eval, emit_loop_iter v c hvc]
  simp

def noParse {V : Type} : RAMCode V → Bool
  | .parse _ _ _ => false
  | .seq p q | .branch _ p q => noParse p && noParse q
  | .loop _ p => noParse p
  | _ => true

theorem eval_word_of_noParse {V : Type} [DecidableEq V] (p : RAMCode V)
    (h : noParse p = true) (s : RAMState V) : (p.eval s).word = s.word := by
  induction p generalizing s with
  | seq p q ihp ihq =>
      simp only [noParse, Bool.and_eq_true] at h
      exact (ihq h.2 _).trans (ihp h.1 _)
  | branch v p q ihp ihq =>
      simp only [noParse, Bool.and_eq_true] at h
      simp only [RAMCode.eval]
      split <;> first | exact ihp h.1 _ | exact ihq h.2 _
  | loop v p ih =>
      change (((fun s => p.eval (s.set v (s.val v - 1)))^[s.val v]) s).word = s.word
      have ht : ∀ n (z : RAMState V),
          (((fun s => p.eval (s.set v (s.val v - 1)))^[n]) z).word = z.word := by
        intro n
        induction n with
        | zero => intro z; rfl
        | succ n hn =>
            intro z
            rw [Function.iterate_succ_apply, hn, ih h]
            rfl
      exact ht _ _
  | parse t good htg => cases h
  | _ => rfl

theorem fold_output {V α : Type} (step : RAMState V → α → RAMState V)
    (code : α → List ℕ) (I : RAMState V → Prop)
    (hi : ∀ s a, I s → I (step s a))
    (ho : ∀ s a, I s → (step s a).out = (encNatList (code a)).reverse ++ s.out)
    (xs : List α) (s : RAMState V) (hs : I s) :
    (xs.foldl step s).out = (encNatList (xs.flatMap code)).reverse ++ s.out := by
  induction xs generalizing s with
  | nil => simp [encNatList]
  | cons a xs ih =>
      rw [List.foldl_cons, ih _ (hi s a hs), ho s a hs, List.flatMap_cons]
      simp [encNatList, List.flatMap_append, List.reverse_append, List.append_assoc]

end ResourceScheduling.ChainProof

end

/- Complete checked body: RAMComputability -/
section

open CookPvsNP ResourceScheduling.Graph

namespace ResourceScheduling.ChainProof

theorem stack_exec_length_le {K A : Type} {p : StackProg K A}
    {s t : K → List A} {n : ℕ} (h : p.Exec s t n) (k : K) :
    (t k).length ≤ (s k).length + n := by
  induction h with
  | act f s =>
      simp only [StackProg.applyAct]
      cases f (fun j => (s j).head?) k <;> simp [StackAct.apply]
      omega
  | seq hp hq ihp ihq => omega
  | branchTrue ht hp ih => omega
  | branchFalse ht hp ih => omega
  | loopFalse ht => omega
  | loopTrue ht hp hloop ihp ihloop => omega

def initialRAM {V : Type} (w : List Letter) : RAMState V :=
  ⟨fun _ => 0, w, []⟩

def completedRAM {V : Type} [DecidableEq V] (p : RAMCode V) :
    StackProg (RAMWire V) Letter :=
  p.code.seq ((clearProg ramInput).seq
    (transferProg ramOutput (fun k => decide (k = ramInput))))

theorem completedRAM_exec {V : Type} [DecidableEq V] (p : RAMCode V) (hp : p.Valid)
    (w : List Letter) :
    ∃ s n, n ≤ 7 * p.cost (initialRAM w) + 3 * w.length + 4 ∧
      (completedRAM p).Exec (fun k => if k = ramInput then w else []) s n ∧
      s ramInput = (p.eval (initialRAM w)).out.reverse := by
  let l : RAMWire V → List Letter := fun k => if k = ramInput then w else []
  have hi : RAMRep (initialRAM (V := V) w) l := by
    simp [RAMRep, initialRAM, l, ramReg, ramTmp, ramInput, ramOutput]
  obtain ⟨n, a, hn, he, ha⟩ := ram_code_correct p hp (initialRAM w) l hi
  let a' := Function.update a ramInput []
  have hc : (clearProg ramInput).Exec a a' (3 * (a ramInput).length + 1) :=
    (stack_basic_macros ramInput a).2.2
  have ht := stack_transfer ramOutput (fun k : RAMWire V => decide (k = ramInput)) a'
  have hlenI := stack_exec_length_le he ramInput
  have hlenO := stack_exec_length_le he ramOutput
  have heq : a' ramOutput = a ramOutput := by simp [a', ramInput, ramOutput]
  rw [heq] at ht
  refine ⟨_, _, ?_, he.seq (hc.seq ht), ?_⟩
  · have hi' : (a ramInput).length ≤ w.length + n := by simpa [l] using hlenI
    have ho' : (a ramOutput).length ≤ n := by
      simpa [l, ramInput, ramOutput] using hlenO
    omega
  · simpa [transferStore, a', ramInput, ramOutput] using
      congrArg List.reverse ha.2.2.1

theorem ram_cost_polynomial {V : Type} [DecidableEq V] (p : RAMCode V)
    (C k : ℕ)
    (hb : ∀ w : List Letter, p.Bounded (C * (w.length + 1) ^ k) (initialRAM w)) :
    ∃ e, ∀ w : List Letter,
      7 * p.cost (initialRAM w) + 3 * w.length + 4 ≤ w.length ^ e + e := by
  let A := 7 * p.weight * (C + 1) ^ p.degree + 3
  let d := k * p.degree + 1
  obtain ⟨e, he⟩ := polynomial_absorb A d 4
  refine ⟨e, fun w => le_trans ?_ (he w.length)⟩
  have hp := ram_budget p (C * (w.length + 1) ^ k) (initialRAM w) (hb w)
  have hone : 1 ≤ (w.length + 1) ^ k := Nat.one_le_pow _ _ (by omega)
  have hbase : C * (w.length + 1) ^ k + 1 ≤ (C + 1) * (w.length + 1) ^ k := by
    nlinarith
  have hpow := Nat.pow_le_pow_left hbase p.degree
  rw [Nat.mul_pow, ← Nat.pow_mul] at hpow
  have hd : (w.length + 1) ^ (k * p.degree) ≤ (w.length + 1) ^ d :=
    Nat.pow_le_pow_right (by omega) (by dsimp [d]; omega)
  have hw : w.length ≤ (w.length + 1) ^ d := by
    have hh : (w.length + 1) ^ 1 ≤ (w.length + 1) ^ d :=
      Nat.pow_le_pow_right (by omega) (by dsimp [d]; omega)
    simp only [pow_one] at hh
    omega
  have hc : p.cost (initialRAM w) ≤
      p.weight * (C + 1) ^ p.degree * (w.length + 1) ^ d := by
    calc
      _ ≤ p.weight * (C * (w.length + 1) ^ k + 1) ^ p.degree := hp
      _ ≤ p.weight * ((C + 1) ^ p.degree * (w.length + 1) ^ (k * p.degree)) :=
        Nat.mul_le_mul_left _ hpow
      _ ≤ _ := by rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hd
  dsimp [A]
  nlinarith

theorem polynomial_time_of_ram {V : Type} [Fintype V] [DecidableEq V]
    (p : RAMCode V) (hp : p.Valid) (C k : ℕ)
    (hb : ∀ w : List Letter, p.Bounded (C * (w.length + 1) ^ k) (initialRAM w)) :
    PolyTimeComputable (fun w : List Letter => (p.eval (initialRAM w)).out.reverse) := by
  obtain ⟨e, he⟩ := ram_cost_polynomial p C k hb
  apply stack_program_polytime (completedRAM p) ramInput ramInput _ e
  intro w
  obtain ⟨s, n, hn, hx, ho⟩ := completedRAM_exec p hp w
  exact ⟨s, n, hn.trans (he w), hx, ho⟩

end ResourceScheduling.ChainProof

end

/- Complete checked body: BudgetBasics -/
section

set_option autoImplicit false

open ResourceScheduling.Graph

namespace ResourceScheduling.ChainProof

theorem ramBound_mono {V : Type} {A B : ℕ} {s : RAMState V}
    (h : RAMBound A s) (hab : A ≤ B) : RAMBound B s :=
  ⟨fun v => (h.1 v).trans hab, h.2.trans hab⟩

theorem ramBound_set {V : Type} [DecidableEq V] {B : ℕ} {s : RAMState V}
    (h : RAMBound B s) (v : V) (n : ℕ) (hn : n ≤ B) : RAMBound B (s.set v n) := by
  refine ⟨?_, h.2⟩
  intro w
  by_cases hw : w = v
  · subst w
    simpa [RAMState.set] using hn
  · simpa [RAMState.set, hw] using h.1 w

theorem ramBound_output {V : Type} {B : ℕ} (s : RAMState V) (ns : List ℕ) :
    RAMBound B (appendOutput s ns) ↔ RAMBound B s := Iff.rfl

theorem bounded_mono {V : Type} [DecidableEq V] (p : RAMCode V) {A B : ℕ}
    (hab : A ≤ B) (s : RAMState V) (h : p.Bounded A s) : p.Bounded B s := by
  induction p generalizing s with
  | seq p q ihp ihq => exact ⟨ihp _ h.1, ihq _ h.2⟩
  | branch v p q ihp ihq => exact ⟨ihp _ h.1, ihq _ h.2⟩
  | loop v p ih => exact ⟨ramBound_mono h.1 hab, fun i hi => ih _ (h.2 i hi)⟩
  | _ => exact ramBound_mono h hab

theorem sequence_replicate_bounded {B : ℕ} (p : ReductionProgram.Code) (n : ℕ)
    (s : RAMState ReductionReg)
    (h : ∀ i < n, p.Bounded B ((p.eval^[i]) s))
    (ht : RAMBound B ((p.eval^[n]) s)) :
    (ReductionProgram.sequence (List.replicate n p)).Bounded B s := by
  induction n generalizing s with
  | zero => exact ht
  | succ n ih =>
      refine ⟨h 0 (by omega), ih (p.eval s) ?_ ?_⟩
      · intro i hi
        simpa only [Function.iterate_succ_apply] using h (i + 1) (by omega)
      · simpa only [Function.iterate_succ_apply] using ht

theorem emit_loop_bounded {V : Type} [DecidableEq V] (v c : V) (hvc : v ≠ c)
    (B : ℕ) (s : RAMState V) (hs : RAMBound B s) :
    (RAMCode.loop c (.emit v)).Bounded B s := by
  refine ⟨hs, ?_⟩
  intro i hi
  change RAMBound B (((fun s => (RAMCode.emit v).eval (s.set c (s.val c - 1)))^[i]) s |>.set c _)
  rw [emit_loop_iter v c hvc]
  apply ramBound_set
  · exact ramBound_set hs c _ ((Nat.sub_le _ _).trans (hs.1 c))
  · simp only [appendOutput_val, RAMState.set, Function.update_self]
    exact (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (hs.1 c))

end ResourceScheduling.ChainProof

end

/- Complete checked body: ScanRows -/
section

set_option autoImplicit false

open ResourceScheduling.Graph

namespace ResourceScheduling.ChainProof.ReductionProgram

open ReductionReg

def scanBody (row : Code) : Code := sequence
  [.bit pos bit, .branch bit (.inc a) (row.seq (.zero a)), .inc pos]

def scanStep (row : Code) (s : RAMState ReductionReg) : RAMState ReductionReg :=
  (scanBody row).eval (s.set scanCounter (s.val scanCounter - 1))

def scanTick (row : Code) (s : RAMState ReductionReg) (x : Letter) : RAMState ReductionReg :=
  let z := (s.set scanCounter (s.val scanCounter - 1)).set bit (if x = .one then 1 else 0)
  let z' := if x = .one then z.set a (z.val a + 1) else (row.eval z).set a 0
  z'.set pos (z'.val pos + 1)

theorem scanStep_eq (row : Code) (s : RAMState ReductionReg) (x : Letter)
    (hx : s.word.getD (s.val pos) .sep = x) : scanStep row s = scanTick row s x := by
  change s.word[s.val pos]?.getD .sep = x at hx
  cases x <;> simp [scanStep, scanBody, sequence, RAMCode.eval, RAMState.set, hx, scanTick]

theorem scanTick_word (row : Code) (hw : ∀ s, (row.eval s).word = s.word)
    (s : RAMState ReductionReg) (x : Letter) : (scanTick row s x).word = s.word := by
  cases x <;> simp [scanTick, RAMState.set, hw]

theorem scanTick_pos (row : Code) (hp : ∀ s, (row.eval s).val pos = s.val pos)
    (s : RAMState ReductionReg) (x : Letter) : (scanTick row s x).val pos = s.val pos + 1 := by
  cases x <;> simp [scanTick, RAMState.set, hp]

theorem scan_iterate (row : Code)
    (hw : ∀ s, (row.eval s).word = s.word)
    (hp : ∀ s, (row.eval s).val pos = s.val pos)
    (xs pre : List Letter) (s : RAMState ReductionReg)
    (hsw : s.word = pre ++ xs) (hsp : s.val pos = pre.length) :
    ((scanStep row)^[xs.length]) s = xs.foldl (scanTick row) s := by
  induction xs generalizing pre s with
  | nil => rfl
  | cons x xs ih =>
      have hx : s.word.getD (s.val pos) .sep = x := by
        rw [hsw, hsp]
        simp [List.getD]
      rw [List.length_cons, Function.iterate_succ_apply, scanStep_eq row s x hx, List.foldl_cons]
      apply ih (pre ++ [x])
      · rw [scanTick_word row hw, hsw, List.append_assoc]
        rfl
      · rw [scanTick_pos row hp, hsp, List.length_append, List.length_singleton]

def scanInitial (s : RAMState ReductionReg) : RAMState ReductionReg :=
  ((s.set a 0).set pos 0).set scanCounter s.word.length

theorem scanRows_fold (row : Code)
    (hw : ∀ s, (row.eval s).word = s.word)
    (hp : ∀ s, (row.eval s).val pos = s.val pos)
    (s : RAMState ReductionReg) :
    (scanRows row).eval s = s.word.foldl (scanTick row) (scanInitial s) := by
  change ((scanStep row)^[s.word.length]) (scanInitial s) = _
  exact scan_iterate row hw hp s.word [] (scanInitial s) (by rfl) (by rfl)

def beforeRow (s : RAMState ReductionReg) (n : ℕ) : RAMState ReductionReg :=
  (((s.set scanCounter (s.val scanCounter - (n + 1))).set bit 0).set a (s.val a + n)).set pos
    (s.val pos + n)

def consumeRow (row : Code) (s : RAMState ReductionReg) (n : ℕ) : RAMState ReductionReg :=
  let z := row.eval (beforeRow s n)
  (z.set a 0).set pos (z.val pos + 1)

theorem beforeRow_tick_one (row : Code) (s : RAMState ReductionReg) (n : ℕ) :
    beforeRow (scanTick row s .one) n = beforeRow s (n + 1) := by
  apply ramState_ext
  · funext v
    cases v <;> simp [beforeRow, scanTick, RAMState.set] <;> omega
  · rfl
  · rfl

theorem scanTick_unary (row : Code) (s : RAMState ReductionReg) (n : ℕ) :
    (unary n).foldl (scanTick row) s = consumeRow row s n := by
  induction n generalizing s with
  | zero =>
      have he : beforeRow s 0 = (s.set scanCounter (s.val scanCounter - 1)).set bit 0 := by
        apply ramState_ext
        · funext v
          cases v <;> simp [beforeRow, RAMState.set]
        · rfl
        · rfl
      simp only [unary, List.replicate_zero, List.nil_append, List.foldl_cons, List.foldl_nil]
      simp only [consumeRow, he, scanTick, reduceCtorEq, if_false]
      rfl
  | succ n ih =>
      change (List.replicate (n + 1) Letter.one ++ [Letter.sep]).foldl (scanTick row) s = _
      rw [List.replicate_succ, List.cons_append, List.foldl_cons]
      change (unary n).foldl (scanTick row) (scanTick row s .one) = _
      rw [ih]
      unfold consumeRow
      rw [beforeRow_tick_one]

theorem scanRows_decoded (row : Code)
    (hw : ∀ s, (row.eval s).word = s.word)
    (hp : ∀ s, (row.eval s).val pos = s.val pos)
    (s : RAMState ReductionReg) (ns : List ℕ) (hs : s.word = encNatList ns) :
    (scanRows row).eval s = ns.foldl (consumeRow row) (scanInitial s) := by
  rw [scanRows_fold row hw hp, hs]
  change (ns.flatMap unary).foldl (scanTick row) (scanInitial s) = _
  rw [List.foldl_flatMap]
  have hf : (fun z n => (unary n).foldl (scanTick row) z) = consumeRow row := by
    funext z n
    exact scanTick_unary row z n
  rw [hf]

end ResourceScheduling.ChainProof.ReductionProgram

end

/- Complete checked body: CanonicalCode -/
section

set_option autoImplicit false

namespace ResourceScheduling.ChainProof

open ResourceScheduling.Chain ResourceScheduling.Chain.ThreePartition

def emittedChainCode (t b : ℕ) (as : List ℕ) : List ℕ :=
  [4 * t * b, 2, 1, 1] ++
    (List.range (2 * t)).flatMap (fun k => List.replicate b (if k % 2 = 0 then 1 else 0)) ++
    as.flatMap (fun a => List.replicate a 0 ++ List.replicate a 1) ++
    [4 * t * b - (3 * t + 1)] ++
    (chainArcsFrom ((2 * t * b) :: as.map (fun a => 2 * a)) 0).flatMap
      (fun e => [e.1, e.2]) ++ [2 * t * b]

theorem chain_size (P : ThreePartition) (hP : P.Valid) : P.chainInstance.n = 4 * P.t * P.b := by
  rw [chain_n_eq P hP.1, aux_cs_length, ← Finset.mul_sum, hP.2.1]
  ring

theorem chain_lengths_sum (P : ThreePartition) (hP : P.Valid) :
    P.chainLengths.sum = 4 * P.t * P.b := by
  simp only [chainLengths, List.sum_cons, List.sum_ofFn]
  rw [← Finset.mul_sum, hP.2.1]
  ring

theorem raw_chain_bounds : ∀ (ls : List ℕ) (off : ℕ) (e : ℕ × ℕ),
    e ∈ chainArcsFrom ls off → e.1 < off + ls.sum ∧ e.2 < off + ls.sum
  | [], off, e, h => by simp [chainArcsFrom] at h
  | a :: ls, off, e, h => by
      rcases List.mem_append.mp h with h | h
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
        have hc' : c < a - 1 := List.mem_range.mp hc
        simp only [List.sum_cons]
        constructor <;> omega
      · have hh := raw_chain_bounds ls (off + a) e h
        simpa only [List.sum_cons, Nat.add_assoc] using hh

def forgetArc {n : ℕ} (e : Fin n × Fin n) : ℕ × ℕ := (e.1.val, e.2.val)

theorem filterMap_toFinArc_map (n : ℕ) (es : List (ℕ × ℕ))
    (h : ∀ e ∈ es, e.1 < n ∧ e.2 < n) :
    (es.filterMap (toFinArc n)).map forgetArc = es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      have he := h e (by simp)
      have ht : ∀ a ∈ es, a.1 < n ∧ a.2 < n := fun a ha => h a (by simp [ha])
      simp only [List.filterMap_cons, toFinArc, dif_pos he, List.map_cons]
      rw [ih ht]
      rfl

theorem canonical_arcs_map (P : ThreePartition) (hP : P.Valid) :
    P.chainInstance.arcs.map forgetArc = chainArcsFrom P.chainLengths 0 := by
  apply filterMap_toFinArc_map
  intro e he
  have hh := raw_chain_bounds P.chainLengths 0 e he
  rw [zero_add, chain_lengths_sum P hP, ← chain_size P hP] at hh
  exact hh

theorem raw_arc_count_positive : ∀ (ls : List ℕ) (off : ℕ),
    (∀ a ∈ ls, 0 < a) → (chainArcsFrom ls off).length + ls.length = ls.sum
  | [], off, _ => rfl
  | a :: ls, off, h => by
      have ha := h a (by simp)
      have ht : ∀ b ∈ ls, 0 < b := fun b hb => h b (by simp [hb])
      have ih := raw_arc_count_positive ls (off + a) ht
      simp only [chainArcsFrom, List.length_append, List.length_map, List.length_range,
        List.length_cons, List.sum_cons]
      omega

theorem canonical_arc_count (P : ThreePartition) (hP : P.Valid) :
    P.chainInstance.arcs.length = 4 * P.t * P.b - (3 * P.t + 1) := by
  have hlen : P.chainInstance.arcs.length = (chainArcsFrom P.chainLengths 0).length := by
    simpa only [List.length_map] using congrArg List.length (canonical_arcs_map P hP)
  rw [hlen]
  by_cases ht : P.t = 0
  · simp [chainLengths, ht, chainArcsFrom]
  · have hpos : ∀ a ∈ P.chainLengths, 0 < a := by
      intro a ha
      simp only [chainLengths, List.mem_cons, List.mem_ofFn] at ha
      rcases ha with rfl | ⟨j, rfl⟩
      · exact Nat.mul_pos (Nat.mul_pos (by decide) (Nat.pos_of_ne_zero ht)) hP.1
      · exact Nat.mul_pos (by decide) (item_positive P hP j)
    have hc := raw_arc_count_positive P.chainLengths 0 hpos
    rw [chain_lengths_sum P hP] at hc
    have hs : P.chainLengths.length = 3 * P.t + 1 := by simp [chainLengths]
    rw [hs] at hc
    omega

theorem chain_requirements_code (P : ThreePartition) :
    List.ofFn (fun j : Fin P.chainInstance.n => P.chainInstance.r (⟨0, by decide⟩ : Fin 1) j)
      = P.chainReqs := by
  change List.ofFn (fun j : Fin P.chainReqs.length => P.chainReqs.get j) = P.chainReqs
  exact List.ofFn_get _

theorem emittedChainCode_eq (P : ThreePartition) (hP : P.Valid) :
    emittedChainCode P.t P.b (List.ofFn P.a) =
      Instance.decisionCode (P.chainInstance, 2 * P.t * P.b) := by
  have hreq : (List.ofFn fun h : Fin P.chainInstance.l =>
      List.ofFn (P.chainInstance.r h)).flatten = P.chainReqs := by
    change (List.ofFn fun _ : Fin 1 => List.ofFn P.chainReqs.get).flatten = _
    simp [List.ofFn_get]
  have harcs : P.chainInstance.arcs.flatMap (fun e => [e.1.val, e.2.val]) =
      (chainArcsFrom P.chainLengths 0).flatMap (fun e => [e.1, e.2]) := by
    rw [← canonical_arcs_map P hP, List.flatMap_map]
    rfl
  have hk : (List.ofFn P.a).flatMap (fun a => List.replicate a 0 ++ List.replicate a 1) =
      P.chainKReqs := by
    rw [List.flatMap, List.map_ofFn]
    rfl
  have hl : (2 * P.t * P.b) :: (List.ofFn P.a).map (fun a => 2 * a) = P.chainLengths := by
    rw [List.map_ofFn]
    rfl
  unfold emittedChainCode Instance.decisionCode Instance.code
  rw [hreq, harcs, canonical_arc_count P hP, chain_size P hP, hk, hl]
  change _ = (([4 * P.t * P.b, 2, 1] ++ List.ofFn (fun _ : Fin 1 => (1 : ℕ)) ++
    P.chainReqs ++ [4 * P.t * P.b - (3 * P.t + 1)] ++
    (chainArcsFrom P.chainLengths 0).flatMap (fun e => [e.1, e.2])) ++ [2 * P.t * P.b])
  simp [chainReqs, chainLReqs, List.ofFn_succ, List.ofFn_zero, List.append_assoc]

end ResourceScheduling.ChainProof

end

/- Complete checked body: ProgramEmission -/
section

set_option autoImplicit false

open ResourceScheduling.Graph

namespace ResourceScheduling.ChainProof.ReductionProgram

open ReductionReg

theorem sequence_cons_eval (p : Code) (ps : List Code) (s : RAMState ReductionReg) :
    (sequence (p :: ps)).eval s = (sequence ps).eval (p.eval s) := rfl

theorem sequence_nil_eval (s : RAMState ReductionReg) : (sequence []).eval s = s := rfl

theorem copy_eval (i v : ReductionReg) (h : i ≠ v) (s : RAMState ReductionReg) :
    (RAMCode.copy i v h).eval s = s.set v (s.val i) := rfl

theorem emitRowRequirements_eval (s : RAMState ReductionReg) :
    emitRowRequirements.eval s = appendOutput (s.set jobCounter 0)
      (List.replicate (s.val a) (s.val zero) ++ List.replicate (s.val a) (s.val one)) := by
  rw [emitRowRequirements, sequence_cons_eval, copy_eval, sequence_cons_eval,
    emit_loop_eval zero jobCounter (by decide), sequence_cons_eval, copy_eval,
    sequence_cons_eval, emit_loop_eval one jobCounter (by decide), sequence_nil_eval]
  simp [appendOutput, RAMState.set, Function.update_idem, encNatList,
    List.flatMap_append, List.reverse_append, List.append_assoc]

theorem emitRowRequirements_word (s : RAMState ReductionReg) :
    (emitRowRequirements.eval s).word = s.word :=
  eval_word_of_noParse _ (by decide) _

theorem emitRowRequirements_pos (s : RAMState ReductionReg) :
    (emitRowRequirements.eval s).val pos = s.val pos :=
  ram_footprint _ _ (by decide) _

theorem consume_requirements_out (s : RAMState ReductionReg) (n : ℕ)
    (ha : s.val a = 0) (hz : s.val zero = 0) (ho : s.val one = 1) :
    (consumeRow emitRowRequirements s n).out =
      (encNatList (List.replicate n 0 ++ List.replicate n 1)).reverse ++ s.out := by
  simp [consumeRow, emitRowRequirements_eval, appendOutput, beforeRow, RAMState.set,
    ha, hz, ho]

theorem consume_requirements_invariant (s : RAMState ReductionReg) (n : ℕ)
    (hs : s.val a = 0 ∧ s.val zero = 0 ∧ s.val one = 1) :
    (consumeRow emitRowRequirements s n).val a = 0 ∧
      (consumeRow emitRowRequirements s n).val zero = 0 ∧
      (consumeRow emitRowRequirements s n).val one = 1 := by
  simp [consumeRow, emitRowRequirements_eval, appendOutput, beforeRow, RAMState.set, hs.2]

theorem scan_requirements_out (s : RAMState ReductionReg) (ns : List ℕ)
    (hw : s.word = encNatList ns) (hz : s.val zero = 0) (ho : s.val one = 1) :
    ((scanRows emitRowRequirements).eval s).out =
      (encNatList (ns.flatMap (fun n => List.replicate n 0 ++ List.replicate n 1))).reverse ++ s.out := by
  rw [scanRows_decoded _ emitRowRequirements_word emitRowRequirements_pos _ _ hw]
  exact fold_output (consumeRow emitRowRequirements)
    (fun n => List.replicate n 0 ++ List.replicate n 1)
    (fun s => s.val a = 0 ∧ s.val zero = 0 ∧ s.val one = 1)
    consume_requirements_invariant (fun s n hs => consume_requirements_out s n hs.1 hs.2.1 hs.2.2)
    ns (scanInitial s) (by simp [scanInitial, RAMState.set, hz, ho])

end ResourceScheduling.ChainProof.ReductionProgram

end

/- Complete checked body: ChainEmission -/
section

set_option autoImplicit false

open ResourceScheduling.Graph

namespace ResourceScheduling.ChainProof.ReductionProgram

open ReductionReg

def arcPairs (off n : ℕ) : List ℕ :=
  (List.range n).flatMap (fun c => [off + c, off + c + 1])

theorem arcPairs_succ (off n : ℕ) :
    arcPairs off (n + 1) = [off, off + 1] ++ arcPairs (off + 1) n := by
  simp [arcPairs, List.range_succ_eq_map, List.flatMap_map, Nat.add_assoc,
    Nat.add_left_comm, Nat.add_comm]

def arcStep (s : RAMState ReductionReg) : RAMState ReductionReg :=
  (sequence [.emit offset, .inc offset, .emit offset]).eval
    (s.set jobCounter (s.val jobCounter - 1))

theorem arcStep_eval (s : RAMState ReductionReg) :
    arcStep s = appendOutput ((s.set jobCounter (s.val jobCounter - 1)).set offset
      (s.val offset + 1)) [s.val offset, s.val offset + 1] := by
  simp [arcStep, sequence, RAMCode.eval, RAMState.set, appendOutput, encNatList,
    unary, List.reverse_append, List.append_assoc]

theorem arcStep_iter (n : ℕ) (s : RAMState ReductionReg) :
    (arcStep^[n]) s = appendOutput ((s.set jobCounter (s.val jobCounter - n)).set offset
      (s.val offset + n)) (arcPairs (s.val offset) n) := by
  induction n generalizing s with
  | zero => simp [arcPairs]
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih, arcStep_eval]
      apply ramState_ext
      · funext v
        cases v <;> simp [appendOutput, RAMState.set,
          Nat.sub_sub, Nat.add_assoc, Nat.add_comm]
      · rfl
      · simp [appendOutput, RAMState.set, arcPairs_succ, encNatList,
          List.reverse_append, List.append_assoc]

theorem emitChain_eval (s : RAMState ReductionReg) :
    emitChain.eval s =
      if s.val len = 0 then s else appendOutput ((s.set jobCounter 0).set offset
        (s.val offset + s.val len)) (arcPairs (s.val offset) (s.val len - 1)) := by
  by_cases hz : s.val len = 0
  · simp [emitChain, RAMCode.eval, hz]
  · have hp : 0 < s.val len := Nat.pos_of_ne_zero hz
    rw [emitChain, RAMCode.eval, if_pos hp, if_neg hz]
    change ((sequence [.inc offset]).eval ((arcStep^[s.val len - 1])
      ((s.set jobCounter (s.val len)).set jobCounter (s.val len - 1)))) = _
    rw [ram_set_set, arcStep_iter]
    simp [sequence, RAMCode.eval, appendOutput, RAMState.set, Function.update_idem,
      Nat.sub_add_cancel hp, Nat.add_assoc]

theorem emitChain_word (s : RAMState ReductionReg) : (emitChain.eval s).word = s.word :=
  eval_word_of_noParse _ (by decide) _

theorem emitChain_offset (s : RAMState ReductionReg) :
    (emitChain.eval s).val offset = s.val offset + s.val len := by
  rw [emitChain_eval]
  split <;> simp_all [appendOutput, RAMState.set]

theorem emitChain_out (s : RAMState ReductionReg) :
    (emitChain.eval s).out =
      (encNatList (arcPairs (s.val offset) (s.val len - 1))).reverse ++ s.out := by
  rw [emitChain_eval]
  split <;> simp_all [appendOutput, arcPairs, encNatList, RAMState.set]

theorem emitRowArcs_out (s : RAMState ReductionReg) :
    (emitRowArcs.eval s).out =
      (encNatList (arcPairs (s.val offset) (2 * s.val a - 1))).reverse ++ s.out := by
  rw [emitRowArcs, RAMCode.eval, scale_eval, emitChain_out]
  simp [RAMState.set]

theorem emitRowArcs_offset (s : RAMState ReductionReg) :
    (emitRowArcs.eval s).val offset = s.val offset + 2 * s.val a := by
  rw [emitRowArcs, RAMCode.eval, scale_eval, emitChain_offset]
  simp [RAMState.set]

theorem emitRowArcs_word (s : RAMState ReductionReg) : (emitRowArcs.eval s).word = s.word :=
  eval_word_of_noParse _ (by decide) _

theorem emitRowArcs_pos (s : RAMState ReductionReg) : (emitRowArcs.eval s).val pos = s.val pos :=
  ram_footprint _ _ (by decide) _

theorem consume_arcs_out (s : RAMState ReductionReg) (n : ℕ) (ha : s.val a = 0) :
    (consumeRow emitRowArcs s n).out =
      (encNatList (arcPairs (s.val offset) (2 * n - 1))).reverse ++ s.out := by
  simp [consumeRow, emitRowArcs_out, beforeRow, RAMState.set, ha]

theorem consume_arcs_offset (s : RAMState ReductionReg) (n : ℕ) (ha : s.val a = 0) :
    (consumeRow emitRowArcs s n).val offset = s.val offset + 2 * n := by
  simp [consumeRow, emitRowArcs_offset, beforeRow, RAMState.set, ha]

theorem consume_arcs_a (s : RAMState ReductionReg) (n : ℕ) :
    (consumeRow emitRowArcs s n).val a = 0 := by
  simp [consumeRow, RAMState.set]

theorem chainArcs_word_cons (d : ℕ) (ds : List ℕ) (off : ℕ) :
    (ResourceScheduling.Chain.chainArcsFrom (d :: ds) off).flatMap (fun e => [e.1, e.2]) =
      arcPairs off (d - 1) ++
        (ResourceScheduling.Chain.chainArcsFrom ds (off + d)).flatMap (fun e => [e.1, e.2]) := by
  simp [ResourceScheduling.Chain.chainArcsFrom, arcPairs, List.flatMap_append, List.flatMap_map]

theorem fold_arcs_out (ns : List ℕ) (s : RAMState ReductionReg) (ha : s.val a = 0) :
    (ns.foldl (consumeRow emitRowArcs) s).out =
      (encNatList ((ResourceScheduling.Chain.chainArcsFrom (ns.map (fun n => 2 * n))
        (s.val offset)).flatMap (fun e => [e.1, e.2]))).reverse ++ s.out := by
  induction ns generalizing s with
  | nil => simp [ResourceScheduling.Chain.chainArcsFrom, encNatList]
  | cons n ns ih =>
      rw [List.foldl_cons, ih _ (consume_arcs_a _ _), consume_arcs_offset _ _ ha,
        consume_arcs_out _ _ ha, List.map_cons, chainArcs_word_cons]
      simp [encNatList, List.flatMap_append, List.reverse_append, List.append_assoc]

theorem scan_arcs_out (ns : List ℕ) (s : RAMState ReductionReg)
    (hw : s.word = encNatList ns) :
    ((scanRows emitRowArcs).eval s).out =
      (encNatList ((ResourceScheduling.Chain.chainArcsFrom (ns.map (fun n => 2 * n))
        (s.val offset)).flatMap (fun e => [e.1, e.2]))).reverse ++ s.out := by
  rw [scanRows_decoded _ emitRowArcs_word emitRowArcs_pos _ _ hw]
  simpa [scanInitial, RAMState.set] using
    fold_arcs_out ns (scanInitial s) (by simp [scanInitial, RAMState.set])

end ResourceScheduling.ChainProof.ReductionProgram

end

/- Complete checked body: BlockEmission -/
section

set_option autoImplicit false

open ResourceScheduling.Graph

namespace ResourceScheduling.ChainProof.ReductionProgram

open ReductionReg

def blockBody : Code := sequence
  [.copy b jobCounter (by decide), .loop jobCounter (.emit flag), .sub one flag flag]

def blockStep (s : RAMState ReductionReg) : RAMState ReductionReg :=
  blockBody.eval (s.set blockCounter (s.val blockCounter - 1))

theorem blockStep_eval (s : RAMState ReductionReg) :
    blockStep s = appendOutput
      (((s.set blockCounter (s.val blockCounter - 1)).set jobCounter 0).set flag
        (s.val one - s.val flag)) (List.replicate (s.val b) (s.val flag)) := by
  rw [blockStep, blockBody, sequence_cons_eval, copy_eval, sequence_cons_eval,
    emit_loop_eval flag jobCounter (by decide), sequence_cons_eval, sequence_nil_eval]
  simp [RAMCode.eval, RAMState.set, appendOutput, Function.update_idem]

def blockValues (b f n : ℕ) : List ℕ :=
  (List.range n).flatMap (fun k => List.replicate b (if k % 2 = 0 then f else 1 - f))

theorem blockValues_succ (b f n : ℕ) (hf : f ≤ 1) :
    blockValues b f (n + 1) = List.replicate b f ++ blockValues b (1 - f) n := by
  rw [blockValues, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  simp only [Nat.zero_mod, if_true]
  congr 1
  apply congrArg (List.flatMap · (List.range n))
  funext k
  congr 1
  have hm := Nat.mod_lt k (by decide : 0 < 2)
  split_ifs <;> omega

theorem blockStep_iter_out (n : ℕ) (s : RAMState ReductionReg)
    (ho : s.val one = 1) (hf : s.val flag ≤ 1) :
    ((blockStep^[n]) s).out =
      (encNatList (blockValues (s.val b) (s.val flag) n)).reverse ++ s.out := by
  induction n generalizing s with
  | zero => simp [blockValues, encNatList]
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      have ho' : (blockStep s).val one = 1 := by simp [blockStep_eval, appendOutput, RAMState.set, ho]
      have hf' : (blockStep s).val flag ≤ 1 := by
        simp only [blockStep_eval, appendOutput_val, RAMState.set, Function.update_self]
        omega
      rw [ih _ ho' hf', blockValues_succ _ _ _ hf]
      simp [blockStep_eval, appendOutput, RAMState.set, ho, encNatList,
        List.flatMap_append, List.reverse_append, List.append_assoc]

def emitL : Code := sequence
  [scale 2 t blockCounter (by decide), const flag 1, .loop blockCounter blockBody]

theorem emitL_out (s : RAMState ReductionReg) (ho : s.val one = 1) :
    (emitL.eval s).out =
      (encNatList ((List.range (2 * s.val t)).flatMap
        (fun k => List.replicate (s.val b) (if k % 2 = 0 then 1 else 0)))).reverse ++ s.out := by
  rw [emitL, sequence_cons_eval, scale_eval, sequence_cons_eval, const_eval,
    sequence_cons_eval, sequence_nil_eval]
  change ((blockStep^[2 * s.val t]) ((s.set blockCounter (2 * s.val t)).set flag 1)).out = _
  rw [blockStep_iter_out _ _ (by simpa [RAMState.set] using ho) (by simp [RAMState.set])]
  simp [blockValues, RAMState.set]

theorem emitL_word (s : RAMState ReductionReg) : (emitL.eval s).word = s.word :=
  eval_word_of_noParse _ (by decide) _

end ResourceScheduling.ChainProof.ReductionProgram

end

/- Complete checked body: FinalEmission -/
section

set_option autoImplicit false

open ResourceScheduling.Graph

namespace ResourceScheduling.ChainProof.ReductionProgram

open ReductionReg

def emitHeader : Code := sequence
  [scale 4 prod jobs (by decide), scale 2 prod horizon (by decide),
   .emit jobs, const tmp 2, .emit tmp, .emit one, .emit one]

theorem emitHeader_eval (s : RAMState ReductionReg) :
    emitHeader.eval s = appendOutput (((s.set jobs (4 * s.val prod)).set horizon
      (2 * s.val prod)).set tmp 2) [4 * s.val prod, 2, s.val one, s.val one] := by
  simp only [emitHeader, sequence_cons_eval, sequence_nil_eval, scale_eval, const_eval, emit_eval]
  simp [appendOutput, RAMState.set, encNatList, unary, List.reverse_append, List.append_assoc]

def emitCount : Code := sequence
  [scale 3 t tmp (by decide), .inc tmp, .sub jobs tmp arcCount, .emit arcCount]

theorem emitCount_out (s : RAMState ReductionReg) :
    (emitCount.eval s).out =
      (encNatList [s.val jobs - (3 * s.val t + 1)]).reverse ++ s.out := by
  simp only [emitCount, sequence_cons_eval, sequence_nil_eval, scale_eval]
  simp [RAMCode.eval, RAMState.set, encNatList, unary, List.reverse_append]

def emitAllArcs : Code := sequence
  [.zero offset, .copy horizon len (by decide), emitChain, scanRows emitRowArcs]

theorem emitAllArcs_out (s : RAMState ReductionReg) (ns : List ℕ)
    (hw : s.word = encNatList ns) :
    (emitAllArcs.eval s).out =
      (encNatList ((ResourceScheduling.Chain.chainArcsFrom
        (s.val horizon :: ns.map (fun n => 2 * n)) 0).flatMap (fun e => [e.1, e.2]))).reverse ++ s.out := by
  change ((scanRows emitRowArcs).eval (emitChain.eval
    ((s.set offset 0).set len (s.val horizon)))).out = _
  rw [scan_arcs_out ns _ (by rw [emitChain_word]; exact hw),
    emitChain_offset, emitChain_out, chainArcs_word_cons]
  simp [RAMState.set, encNatList, List.flatMap_append, List.reverse_append, List.append_assoc]

theorem emitInstance_word (s : RAMState ReductionReg) :
    (emitInstance.eval s).word = s.word := eval_word_of_noParse _ (by decide) _

theorem emitInstance_out (s : RAMState ReductionReg) (t b : ℕ) (ns : List ℕ)
    (ht : s.val .t = t) (hb : s.val .b = b) (hp : s.val .prod = t * b)
    (hz : s.val .zero = 0) (ho : s.val .one = 1) (hw : s.word = encNatList ns) :
    (emitInstance.eval s).out = (encNatList (emittedChainCode t b ns)).reverse ++ s.out := by
  have he : emitInstance.eval s = (RAMCode.emit horizon).eval
      (emitAllArcs.eval (emitCount.eval ((scanRows emitRowRequirements).eval
        (emitL.eval (emitHeader.eval s))))) := by rfl
  generalize hs1 : emitHeader.eval s = s1 at he
  generalize hs2 : emitL.eval s1 = s2 at he
  generalize hs3 : (scanRows emitRowRequirements).eval s2 = s3 at he
  generalize hs4 : emitCount.eval s3 = s4 at he
  generalize hs5 : emitAllArcs.eval s4 = s5 at he
  have h1t : s1.val .t = t := by simp [← hs1, emitHeader_eval, appendOutput, RAMState.set, ht]
  have h1b : s1.val .b = b := by simp [← hs1, emitHeader_eval, appendOutput, RAMState.set, hb]
  have h1z : s1.val .zero = 0 := by simp [← hs1, emitHeader_eval, appendOutput, RAMState.set, hz]
  have h1o : s1.val .one = 1 := by simp [← hs1, emitHeader_eval, appendOutput, RAMState.set, ho]
  have h1j : s1.val jobs = 4 * t * b := by simp [← hs1, emitHeader_eval, appendOutput, RAMState.set, hp, Nat.mul_assoc]
  have h1h : s1.val horizon = 2 * t * b := by simp [← hs1, emitHeader_eval, appendOutput, RAMState.set, hp, Nat.mul_assoc]
  have h1w : s1.word = encNatList ns := by simp [← hs1, emitHeader_eval, appendOutput, RAMState.set, hw]
  have h1out : s1.out = (encNatList [4 * t * b, 2, 1, 1]).reverse ++ s.out := by
    simp [← hs1, emitHeader_eval, appendOutput, RAMState.set, ho, hp, Nat.mul_assoc]
  have h2t : s2.val .t = t := by
    simpa only [hs2] using (ram_footprint emitL .t (by decide) s1).trans h1t
  have h2z : s2.val .zero = 0 := by
    simpa only [hs2] using (ram_footprint emitL .zero (by decide) s1).trans h1z
  have h2o : s2.val .one = 1 := by
    simpa only [hs2] using (ram_footprint emitL .one (by decide) s1).trans h1o
  have h2j : s2.val jobs = 4 * t * b := by
    simpa only [hs2] using (ram_footprint emitL jobs (by decide) s1).trans h1j
  have h2h : s2.val horizon = 2 * t * b := by
    simpa only [hs2] using (ram_footprint emitL horizon (by decide) s1).trans h1h
  have h2w : s2.word = encNatList ns := by
    simpa only [hs2] using (emitL_word s1).trans h1w
  have h2out : s2.out = (encNatList ((List.range (2 * t)).flatMap
      (fun k => List.replicate b (if k % 2 = 0 then 1 else 0)))).reverse ++ s1.out := by
    simpa only [hs2, h1t, h1b] using emitL_out s1 h1o
  have h3t : s3.val .t = t := by
    simpa only [hs3] using (ram_footprint (scanRows emitRowRequirements) .t (by decide) s2).trans h2t
  have h3j : s3.val jobs = 4 * t * b := by
    simpa only [hs3] using (ram_footprint (scanRows emitRowRequirements) jobs (by decide) s2).trans h2j
  have h3h : s3.val horizon = 2 * t * b := by
    simpa only [hs3] using (ram_footprint (scanRows emitRowRequirements) horizon (by decide) s2).trans h2h
  have h3w : s3.word = encNatList ns :=
    by simpa only [hs3] using (eval_word_of_noParse (scanRows emitRowRequirements) (by decide) s2).trans h2w
  have h3out : s3.out = (encNatList (ns.flatMap
      (fun n => List.replicate n 0 ++ List.replicate n 1))).reverse ++ s2.out :=
    by simpa only [hs3] using scan_requirements_out s2 ns h2w h2z h2o
  have h4h : s4.val horizon = 2 * t * b := by
    simpa only [hs4] using (ram_footprint emitCount horizon (by decide) s3).trans h3h
  have h4w : s4.word = encNatList ns := by
    simpa only [hs4] using (eval_word_of_noParse emitCount (by decide) s3).trans h3w
  have h4out : s4.out = (encNatList [4 * t * b - (3 * t + 1)]).reverse ++ s3.out := by
    simpa only [hs4, h3t, h3j] using emitCount_out s3
  have h5h : s5.val horizon = 2 * t * b := by
    simpa only [hs5] using (ram_footprint emitAllArcs horizon (by decide) s4).trans h4h
  have h5out : s5.out = (encNatList ((ResourceScheduling.Chain.chainArcsFrom
      ((2 * t * b) :: ns.map (fun n => 2 * n)) 0).flatMap (fun e => [e.1, e.2]))).reverse ++ s4.out := by
    simpa only [hs5, h4h] using emitAllArcs_out s4 ns h4w
  rw [he, emit_eval]
  change (encNatList [s5.val horizon]).reverse ++ s5.out = _
  rw [h5h, h5out, h4out, h3out, h2out, h1out]
  simp only [emittedChainCode, encNatList, List.flatMap_append, List.reverse_append,
    List.append_assoc]

end ResourceScheduling.ChainProof.ReductionProgram

end

/- Complete checked body: BudgetElementary -/
section

set_option autoImplicit false

open ResourceScheduling.Graph

namespace ResourceScheduling.ChainProof.ReductionProgram

open ReductionReg

theorem const_bounded {B : ℕ} (v : ReductionReg) (n : ℕ) (s : RAMState ReductionReg)
    (hs : RAMBound B s) (hn : n ≤ B) : (const v n).Bounded B s := by
  refine ⟨hs, ?_⟩
  apply sequence_replicate_bounded
  · intro i hi
    change RAMBound B (((RAMCode.inc v).eval^[i]) (s.set v 0))
    rw [iterate_inc_eval]
    apply ramBound_set (ramBound_set hs v 0 (Nat.zero_le _))
    simpa [RAMState.set] using (Nat.le_of_lt hi).trans hn
  · rw [iterate_inc_eval]
    apply ramBound_set (ramBound_set hs v 0 (Nat.zero_le _))
    simpa [RAMState.set, RAMCode.eval] using hn

theorem const_bound_after {B : ℕ} (v : ReductionReg) (n : ℕ) (s : RAMState ReductionReg)
    (hs : RAMBound B s) (hn : n ≤ B) : RAMBound B ((const v n).eval s) := by
  rw [const_eval]
  exact ramBound_set hs v n hn

theorem scale_bounded {B : ℕ} (n : ℕ) (src dst : ReductionReg) (h : src ≠ dst)
    (s : RAMState ReductionReg) (hs : RAMBound B s) (hn : n * s.val src ≤ B) :
    (scale n src dst h).Bounded B s := by
  refine ⟨hs, ?_⟩
  apply sequence_replicate_bounded
  · intro i hi
    change RAMBound B (((RAMCode.add src dst h).eval^[i]) (s.set dst 0))
    rw [iterate_add_eval]
    apply ramBound_set (ramBound_set hs dst 0 (Nat.zero_le _))
    simpa [RAMState.set, h] using
      (Nat.mul_le_mul_right (s.val src) (Nat.le_of_lt hi)).trans hn
  · rw [iterate_add_eval]
    apply ramBound_set (ramBound_set hs dst 0 (Nat.zero_le _))
    simpa [RAMState.set, RAMCode.eval, h] using hn

theorem scale_bound_after {B : ℕ} (n : ℕ) (src dst : ReductionReg) (h : src ≠ dst)
    (s : RAMState ReductionReg) (hs : RAMBound B s) (hn : n * s.val src ≤ B) :
    RAMBound B ((scale n src dst h).eval s) := by
  rw [scale_eval]
  exact ramBound_set hs dst _ hn

theorem assertPos_bounded {B : ℕ} (v : ReductionReg) (s : RAMState ReductionReg)
    (hs : RAMBound B s) : (assertPos v).Bounded B s := ⟨hs, hs⟩

theorem assertZero_bounded {B : ℕ} (v : ReductionReg) (s : RAMState ReductionReg)
    (hs : RAMBound B s) : (assertZero v).Bounded B s := ⟨hs, hs⟩

theorem assertPos_bound_after {B : ℕ} (v : ReductionReg) (s : RAMState ReductionReg)
    (hs : RAMBound B s) : RAMBound B ((assertPos v).eval s) := by
  unfold assertPos RAMCode.eval
  split
  · exact hs
  · exact ramBound_set hs ok 0 (Nat.zero_le _)

theorem assertZero_bound_after {B : ℕ} (v : ReductionReg) (s : RAMState ReductionReg)
    (hs : RAMBound B s) : RAMBound B ((assertZero v).eval s) := by
  unfold assertZero RAMCode.eval
  split
  · exact ramBound_set hs ok 0 (Nat.zero_le _)
  · exact hs

theorem sub_bound_after {B : ℕ} (i j dst : ReductionReg) (s : RAMState ReductionReg)
    (hs : RAMBound B s) : RAMBound B ((RAMCode.sub i j dst).eval s) :=
  ramBound_set hs dst _ ((Nat.sub_le _ _).trans (hs.1 i))

end ResourceScheduling.ChainProof.ReductionProgram

end

/- Complete checked body: BudgetSequence -/
section

set_option autoImplicit false

open ResourceScheduling.Graph

namespace ResourceScheduling.ChainProof.ReductionProgram

theorem sequence_safe_invariant (ps : List Code) (B : ℕ) (I : RAMState ReductionReg → Prop)
    (hbound : ∀ s, I s → RAMBound B s)
    (hstep : ∀ p ∈ ps, ∀ s, I s → RAMSafe p B s ∧ I (p.eval s))
    (s : RAMState ReductionReg) (hs : I s) :
    RAMSafe (sequence ps) B s ∧ I ((sequence ps).eval s) := by
  induction ps generalizing s with
  | nil => exact ⟨⟨hbound s hs, hbound s hs⟩, hs⟩
  | cons p ps ih =>
      obtain ⟨hp, hpI⟩ := hstep p (by simp) s hs
      obtain ⟨hq, hqI⟩ := ih (fun q hq => hstep q (by simp [hq])) (p.eval s) hpI
      exact ⟨⟨⟨hp.1, hq.1⟩, hq.2⟩, hqI⟩

theorem safe_scale {B : ℕ} (n : ℕ) (i j : ReductionReg) (hij : i ≠ j)
    (s : RAMState ReductionReg) (hs : RAMBound B s) (hn : n * s.val i ≤ B) :
    RAMSafe (scale n i j hij) B s :=
  ⟨scale_bounded n i j hij s hs hn, scale_bound_after n i j hij s hs hn⟩

theorem safe_sub {B : ℕ} (i j dst : ReductionReg) (s : RAMState ReductionReg)
    (hs : RAMBound B s) : RAMSafe (.sub i j dst : Code) B s :=
  ⟨hs, sub_bound_after i j dst s hs⟩

theorem safe_assertPos {B : ℕ} (v : ReductionReg) (s : RAMState ReductionReg)
    (hs : RAMBound B s) : RAMSafe (assertPos v) B s :=
  ⟨assertPos_bounded v s hs, assertPos_bound_after v s hs⟩

theorem safe_assertZero {B : ℕ} (v : ReductionReg) (s : RAMState ReductionReg)
    (hs : RAMBound B s) : RAMSafe (assertZero v) B s :=
  ⟨assertZero_bounded v s hs, assertZero_bound_after v s hs⟩

theorem safe_loop_closed (p : Code) (v : ReductionReg) (B : ℕ)
    (hp : ∀ z, RAMBound B z → RAMSafe p B z)
    (s : RAMState ReductionReg) (hs : RAMBound B s) : RAMSafe (.loop v p : Code) B s := by
  have h := ram_loop_invariant v p B (s.val v) (fun _ z => RAMBound B z) s hs rfl hs
  exact h (fun _ _ z hz => hp _ (ramBound_set hz v _ ((Nat.sub_le _ _).trans (hz.1 v))))

theorem safe_emit_loop (v c : ReductionReg) (B : ℕ) (s : RAMState ReductionReg)
    (hs : RAMBound B s) : RAMSafe (.loop c (.emit v) : Code) B s :=
  safe_loop_closed (.emit v) c B (fun _ hz => ⟨hz, hz⟩) s hs

theorem safe_copy (i j : ReductionReg) (hij : i ≠ j) (B : ℕ) (s : RAMState ReductionReg)
    (hs : RAMBound B s) : RAMSafe (.copy i j hij : Code) B s :=
  ⟨hs, ramBound_set hs j _ (hs.1 i)⟩

theorem sequence_append_bounded (ps qs : List Code) (B : ℕ) (s : RAMState ReductionReg)
    (hp : (sequence ps).Bounded B s)
    (hq : (sequence qs).Bounded B ((sequence ps).eval s)) :
    (sequence (ps ++ qs)).Bounded B s := by
  induction ps generalizing s with
  | nil => exact hq
  | cons p ps ih => exact ⟨hp.1, ih (p.eval s) hp.2 hq⟩

end ResourceScheduling.ChainProof.ReductionProgram
end

/- Complete checked body: BudgetState -/
section

set_option autoImplicit false

open ResourceScheduling.Graph

namespace ResourceScheduling.ChainProof.ReductionProgram

open ReductionReg

theorem budget_square_expand (N : ℕ) : (N + 1) ^ 2 = N ^ 2 + 2 * N + 1 := by ring

def SmallInput (N : ℕ) (s : RAMState ReductionReg) : Prop :=
  s.word.length ≤ N ∧ s.val t ≤ N ∧ s.val b ≤ N ∧ s.val prod ≤ N ^ 2

theorem SmallInput.preserve {N : ℕ} {s : RAMState ReductionReg} (hs : SmallInput N s)
    (p : Code) (hw : noParse p = true) (ht : p.writes t = false)
    (hb : p.writes b = false) (hp : p.writes prod = false) : SmallInput N (p.eval s) := by
  unfold SmallInput
  rw [eval_word_of_noParse p hw, ram_footprint p t ht, ram_footprint p b hb,
    ram_footprint p prod hp]
  exact hs

theorem assertEq_safe (i j : ReductionReg) (B : ℕ) (s : RAMState ReductionReg)
    (hs : RAMBound B s) : RAMSafe (assertEq i j) B s := by
  apply (sequence_safe_invariant _ B (RAMBound B) (fun _ h => h) ?_ s hs).1
  intro p hp z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  have hsafe : RAMSafe p B z := by
    rcases hp with rfl | rfl | rfl | rfl
    · exact safe_sub i j diff z hz
    · exact safe_assertZero diff z hz
    · exact safe_sub j i diff z hz
    · exact safe_assertZero diff z hz
  exact ⟨hsafe, hsafe.2⟩

end ResourceScheduling.ChainProof.ReductionProgram
end

/- Complete checked body: AlphabetTransport -/
section

open CookPvsNP

namespace ResourceScheduling.ChainProof

def alphabetEquiv : Chain.USym ≃ Graph.Letter where
  toFun := fun a => match a with | .one => .one | .sep => .sep
  invFun := fun a => match a with | .one => .one | .sep => .sep
  left_inv := by intro a; cases a <;> rfl
  right_inv := by intro a; cases a <;> rfl

theorem polynomial_time_alphabet_equiv {A B : Type} (e : A ≃ B)
    (f : List B → List B) (hf : PolyTimeComputable f) :
    PolyTimeComputable (fun w : List A => (f (w.map e)).map e.symm) := by
  obtain ⟨Γ, hΓ, i, o, M, k, h⟩ := hf
  refine ⟨Γ, hΓ, e.toEmbedding.trans i, e.toEmbedding.trans o, M, k, ?_⟩
  intro w
  simpa only [List.length_map, List.map_map, Function.Embedding.coe_trans,
    Equiv.coe_toEmbedding, Function.comp_def, Equiv.apply_symm_apply] using h (w.map e)

end ResourceScheduling.ChainProof

end

/- Complete checked body: WordDecomposition -/
section

open ResourceScheduling.Chain ResourceScheduling.Graph

namespace ResourceScheduling.ChainProof

theorem alphabet_unary (n : ℕ) :
    (unary n).map alphabetEquiv.symm = encNat n := by
  simp [unary, encNat, alphabetEquiv]

theorem alphabet_encNatList (ns : List ℕ) :
    (encNatList ns).map alphabetEquiv.symm = encNats ns := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
      simpa only [encNatList, encNats, List.flatMap_cons, List.map_append,
        alphabet_unary] using congrArg (encNat n ++ ·) ih

theorem exists_word_decomposition (w : List Letter) :
    ∃ ns : List ℕ, ∃ r : ℕ, w = encNatList ns ++ List.replicate r Letter.one := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨[], 0, rfl⟩
  | append_singleton w a ih =>
      obtain ⟨ns, r, rfl⟩ := ih
      cases a with
      | one =>
          refine ⟨ns, r + 1, ?_⟩
          simp [List.replicate_succ', List.append_assoc]
      | sep =>
          refine ⟨ns ++ [r], 0, ?_⟩
          simp [encNatList, unary, List.flatMap_append, List.append_assoc]

theorem decodeNats_encNats_append (ns : List ℕ) (w : List USym) :
    decodeNats (encNats ns ++ w) = (decodeNats w).map (ns ++ ·) := by
  induction ns with
  | nil => simp [encNats]
  | cons n ns ih =>
      rw [encNats, List.flatMap_cons, List.append_assoc, decodeNats_encNat]
      change (decodeNats (encNats ns ++ w)).map (n :: ·) = _
      rw [ih]
      cases decodeNats w <;> rfl

theorem decodeNats_ones_succ (n : ℕ) :
    decodeNats (List.replicate (n + 1) USym.one) = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ]
      change (decodeNats (List.replicate (n + 1) USym.one)).bind _ = none
      rw [ih]
      rfl

theorem decode_word_decomposition (ns : List ℕ) (r : ℕ) :
    decodeNats ((encNatList ns ++ List.replicate r Letter.one).map alphabetEquiv.symm) =
      if r = 0 then some ns else none := by
  rw [List.map_append, alphabet_encNatList]
  simp only [List.map_replicate]
  change decodeNats (encNats ns ++ List.replicate r USym.one) = _
  rw [decodeNats_encNats_append]
  cases r with
  | zero => simp [decodeNats]
  | succ r => simp [decodeNats_ones_succ]

theorem readUnary_unary (n : ℕ) (w : List Letter) :
    readUnary (unary n ++ w) = some (n, w) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [unary, List.replicate_succ, List.cons_append, readUnary] at ih ⊢
      rw [ih]
      rfl

theorem ofFn_getD_eq {n : ℕ} (as : List ℕ) (h : as.length = n) :
    List.ofFn (fun i : Fin n => as.getD i 0) = as := by
  apply List.ext_getElem
  · simpa using h.symm
  · intro i hi hj
    simp only [List.getElem_ofFn]
    exact List.getD_eq_getElem _ _ hj

theorem list_partition_valid (t b : ℕ) (as : List ℕ) (h : as.length = 3 * t) :
    (ThreePartition.mk t b (fun i => as.getD i 0)).Valid ↔
      0 < b ∧ as.sum = t * b ∧ ∀ a ∈ as, b < 4 * a ∧ 2 * a < b := by
  have he := ofFn_getD_eq as h
  constructor
  · rintro ⟨hb, hs, ha⟩
    refine ⟨hb, ?_, ?_⟩
    · rw [← he, List.sum_ofFn]
      exact hs
    · intro a ha'
      rw [← he, List.mem_ofFn] at ha'
      obtain ⟨i, rfl⟩ := ha'
      exact ha i
  · rintro ⟨hb, hs, ha⟩
    refine ⟨hb, ?_, ?_⟩
    · rw [← he, List.sum_ofFn] at hs
      exact hs
    · intro i
      apply ha
      have hm : as.getD i 0 ∈ List.ofFn (fun j : Fin (3 * t) => as.getD j 0) :=
        List.mem_ofFn.mpr ⟨i, rfl⟩
      simpa only [he] using hm

end ResourceScheduling.ChainProof

end

/- Complete checked body: ValidationRows -/
section

open ResourceScheduling.Graph

namespace ResourceScheduling.ChainProof.ReductionProgram

open ReductionReg

def goodItem (b n : ℕ) : Prop := b < 4 * n ∧ 2 * n < b

instance (b n : ℕ) : Decidable (goodItem b n) := by
  unfold goodItem
  infer_instance

theorem validateRow_word (s : RAMState ReductionReg) :
    (validateRow.eval s).word = s.word :=
  ram_field_frame validateRow true (by decide) s

theorem validateRow_out (s : RAMState ReductionReg) :
    (validateRow.eval s).out = s.out :=
  ram_field_frame validateRow false (by decide) s

theorem validateRow_pos (s : RAMState ReductionReg) :
    (validateRow.eval s).val pos = s.val pos :=
  ram_footprint validateRow pos (by decide) s

theorem validateRow_a (s : RAMState ReductionReg) :
    (validateRow.eval s).val a = s.val a :=
  ram_footprint validateRow a (by decide) s

theorem validateRow_b (s : RAMState ReductionReg) :
    (validateRow.eval s).val b = s.val b :=
  ram_footprint validateRow b (by decide) s

theorem validateRow_count (s : RAMState ReductionReg) :
    (validateRow.eval s).val count = s.val count + 1 := by
  let rest : Code := sequence
    [.add a sumA (by decide), scale 4 a tmp (by decide), .sub tmp b diff, assertPos diff,
     scale 2 a tmp (by decide), .sub b tmp diff, assertPos diff]
  change (rest.eval (s.set count (s.val count + 1))).val count = _
  rw [ram_footprint rest count (by decide)]
  simp [RAMState.set]

theorem validateRow_sum (s : RAMState ReductionReg) :
    (validateRow.eval s).val sumA = s.val a + s.val sumA := by
  let rest : Code := sequence
    [scale 4 a tmp (by decide), .sub tmp b diff, assertPos diff,
     scale 2 a tmp (by decide), .sub b tmp diff, assertPos diff]
  change (rest.eval ((s.set count (s.val count + 1)).set sumA
    ((s.set count (s.val count + 1)).val a + (s.set count (s.val count + 1)).val sumA))).val sumA = _
  rw [ram_footprint rest sumA (by decide)]
  simp [RAMState.set]

theorem validateRow_ok (s : RAMState ReductionReg) :
    (validateRow.eval s).val ok = if goodItem (s.val b) (s.val a) then s.val ok else 0 := by
  classical
  by_cases h1 : s.val b < 4 * s.val a
  · by_cases h2 : 2 * s.val a < s.val b
    · simp [validateRow, sequence, RAMCode.eval, scale_eval, assertPos, RAMState.set,
        goodItem, h1, h2]
    · simp [validateRow, sequence, RAMCode.eval, scale_eval, assertPos, RAMState.set,
        goodItem, h1, h2]
  · by_cases h2 : 2 * s.val a < s.val b
    · simp [validateRow, sequence, RAMCode.eval, scale_eval, assertPos, RAMState.set,
        goodItem, h1, h2]
    · simp [validateRow, sequence, RAMCode.eval, scale_eval, assertPos, RAMState.set,
        goodItem, h1, h2]

end ResourceScheduling.ChainProof.ReductionProgram

end

/- Complete checked body: ValidationScan -/
section

open ResourceScheduling.Graph

namespace ResourceScheduling.ChainProof.ReductionProgram

open ReductionReg

theorem consumeValidate_a (s : RAMState ReductionReg) (n : ℕ) :
    (consumeRow validateRow s n).val a = 0 := by
  simp [consumeRow, RAMState.set]

theorem consumeValidate_b (s : RAMState ReductionReg) (n : ℕ) :
    (consumeRow validateRow s n).val b = s.val b := by
  simp [consumeRow, validateRow_b, beforeRow, RAMState.set]

theorem consumeValidate_count (s : RAMState ReductionReg) (n : ℕ) :
    (consumeRow validateRow s n).val count = s.val count + 1 := by
  simp [consumeRow, validateRow_count, beforeRow, RAMState.set]

theorem consumeValidate_sum (s : RAMState ReductionReg) (n : ℕ) :
    (consumeRow validateRow s n).val sumA = s.val a + n + s.val sumA := by
  simp [consumeRow, validateRow_sum, beforeRow, RAMState.set]

theorem consumeValidate_ok (s : RAMState ReductionReg) (n : ℕ) :
    (consumeRow validateRow s n).val ok =
      if goodItem (s.val b) (s.val a + n) then s.val ok else 0 := by
  simp [consumeRow, validateRow_ok, beforeRow, RAMState.set]

theorem validate_fold_summary (ns : List ℕ) (s : RAMState ReductionReg) (ha : s.val a = 0) :
    let z := ns.foldl (consumeRow validateRow) s
    z.val a = 0 ∧ z.val b = s.val b ∧ z.val count = s.val count + ns.length ∧
      z.val sumA = s.val sumA + ns.sum ∧
      z.val ok = if ns.all (fun n => decide (goodItem (s.val b) n)) then s.val ok else 0 := by
  induction ns generalizing s with
  | nil => simp [ha]
  | cons n ns ih =>
      dsimp only [List.foldl_cons]
      obtain ⟨hza, hzb, hzc, hzs, hzo⟩ :=
        ih (consumeRow validateRow s n) (consumeValidate_a s n)
      refine ⟨hza, hzb.trans (consumeValidate_b s n), ?_, ?_, ?_⟩
      · simpa [consumeValidate_count, Nat.add_assoc, Nat.add_comm] using hzc
      · simpa [consumeValidate_sum, ha, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hzs
      · by_cases hn : goodItem (s.val b) n
        · simpa [consumeValidate_ok, consumeValidate_b, ha, List.all_cons, hn] using hzo
        · simpa [consumeValidate_ok, consumeValidate_b, ha, List.all_cons, hn] using hzo

theorem ones_fold_a (row : Code) (r : ℕ) (s : RAMState ReductionReg) :
    ((List.replicate r Letter.one).foldl (scanTick row) s).val a = s.val a + r := by
  induction r generalizing s with
  | zero => simp
  | succ r ih =>
      rw [List.replicate_succ, List.foldl_cons, ih]
      simp [scanTick, RAMState.set, Nat.add_assoc, Nat.add_comm]

theorem ones_fold_fixed (row : Code) (r : ℕ) (s : RAMState ReductionReg) (v : ReductionReg)
    (hv : v ≠ scanCounter ∧ v ≠ bit ∧ v ≠ a ∧ v ≠ pos) :
    ((List.replicate r Letter.one).foldl (scanTick row) s).val v = s.val v := by
  induction r generalizing s with
  | zero => rfl
  | succ r ih =>
      rw [List.replicate_succ, List.foldl_cons, ih]
      simp [scanTick, RAMState.set, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2]

theorem decoded_tick_fold (row : Code) (ns : List ℕ) (s : RAMState ReductionReg) :
    (encNatList ns).foldl (scanTick row) s = ns.foldl (consumeRow row) s := by
  rw [encNatList, List.foldl_flatMap]
  have he : (fun s n => (unary n).foldl (scanTick row) s) = consumeRow row := by
    funext s n
    exact scanTick_unary row s n
  rw [he]

theorem validation_scan_summary (s : RAMState ReductionReg) (ns : List ℕ) (r : ℕ)
    (hw : s.word = encNatList ns ++ List.replicate r Letter.one) :
    let z := (scanRows validateRow).eval s
    z.val a = r ∧ z.val b = s.val b ∧ z.val count = s.val count + ns.length ∧
      z.val sumA = s.val sumA + ns.sum ∧
      z.val ok = if ns.all (fun n => decide (goodItem (s.val b) n)) then s.val ok else 0 := by
  dsimp only
  rw [scanRows_fold validateRow validateRow_word validateRow_pos, hw, List.foldl_append,
    decoded_tick_fold]
  let v := ns.foldl (consumeRow validateRow) (scanInitial s)
  have h := validate_fold_summary ns (scanInitial s) (by simp [scanInitial, RAMState.set])
  change v.val a = 0 ∧ _ at h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [ones_fold_a, h.1, zero_add]
  · rw [ones_fold_fixed _ _ _ b (by decide)]
    simpa [scanInitial, RAMState.set] using h.2.1
  · rw [ones_fold_fixed _ _ _ count (by decide)]
    simpa [scanInitial, RAMState.set] using h.2.2.1
  · rw [ones_fold_fixed _ _ _ sumA (by decide)]
    simpa [scanInitial, RAMState.set] using h.2.2.2.1
  · rw [ones_fold_fixed _ _ _ ok (by decide)]
    simpa [scanInitial, RAMState.set] using h.2.2.2.2

end ResourceScheduling.ChainProof.ReductionProgram

end

/- Complete checked body: ValidationPrefix -/
section

open ResourceScheduling.Graph

namespace ResourceScheduling.ChainProof.ReductionProgram

open ReductionReg

def validationPrefixCommands : List Code :=
  [const ok 1, const one 1,
   .parse t parseOk (by decide), assertPos parseOk,
   .parse b parseOk (by decide), assertPos parseOk, assertPos b,
   .mul t b prod (by decide), .zero count, .zero sumA]

def validationSuffixCommands : List Code :=
  [assertZero a, scale 3 t tmp (by decide), assertEq count tmp, assertEq sumA prod]

def validationPrefix : Code := sequence validationPrefixCommands
def validationSuffix : Code := sequence validationSuffixCommands

theorem validate_factor (s : RAMState ReductionReg) :
    validate.eval s = validationSuffix.eval
      ((scanRows validateRow).eval (validationPrefix.eval s)) := by
  have he : validate = sequence
      ((validationPrefixCommands ++ [scanRows validateRow]) ++ validationSuffixCommands) := rfl
  have hsingle (p : Code) (z : RAMState ReductionReg) :
      (sequence [p]).eval z = p.eval z := rfl
  have h := sequence_eval_append (validationPrefixCommands ++ [scanRows validateRow])
    validationSuffixCommands s
  rw [sequence_eval_append validationPrefixCommands [scanRows validateRow] s, hsingle, ← he] at h
  exact h

def readState (v : ReductionReg) (s : RAMState ReductionReg) : RAMState ReductionReg :=
  let p := splitOnes s.word
  { val := Function.update (Function.update (Function.update s.val v p.1) parseOk
      (if p.2 = [] then 0 else 1)) ok (if p.2 = [] then 0 else s.val ok)
    word := p.2.tail
    out := s.out }

theorem parseAssert_eval (v : ReductionReg) (hv : v ≠ ok) (s : RAMState ReductionReg) :
    (assertPos parseOk).eval (ramParseState v parseOk s) = readState v s := by
  have he : readState v s = (ramParseState v parseOk s).set ok
      (if (splitOnes s.word).2 = [] then 0 else s.val ok) := rfl
  rw [he]
  by_cases h : (splitOnes s.word).2 = []
  · simp [assertPos, RAMCode.eval, ramParseState, RAMState.set, h]
  · have hp : (ramParseState v parseOk s).val parseOk = 1 := by
      simp [ramParseState, RAMState.set, h]
    have hk : (ramParseState v parseOk s).val ok = s.val ok := by
      simp [ramParseState, RAMState.set, Ne.symm hv]
    rw [if_neg h, ← hk, ram_set_self]
    simp [assertPos, RAMCode.eval, hp]

theorem assertPos_eval (v : ReductionReg) (s : RAMState ReductionReg) :
    (assertPos v).eval s = s.set ok (if 0 < s.val v then s.val ok else 0) := by
  by_cases h : 0 < s.val v <;> simp [assertPos, RAMCode.eval, h]

def headerTail (w : List Letter) : List Letter := (splitOnes w).2.tail
def headerRest (w : List Letter) : List Letter := headerTail (headerTail w)
def headerT (w : List Letter) : ℕ := (splitOnes w).1
def headerB (w : List Letter) : ℕ := headerT (headerTail w)

def headerGood (w : List Letter) : Prop :=
  (splitOnes w).2 ≠ [] ∧ (splitOnes (headerTail w)).2 ≠ [] ∧ 0 < headerB w

instance (w : List Letter) : Decidable (headerGood w) := by
  unfold headerGood
  infer_instance

theorem validationPrefix_spec (w : List Letter) :
    let s := validationPrefix.eval (initialRAM w)
    s.word = headerRest w ∧ s.val t = headerT w ∧ s.val b = headerB w ∧
      s.val prod = headerT w * headerB w ∧ s.val count = 0 ∧ s.val sumA = 0 ∧
      s.val zero = 0 ∧ s.val one = 1 ∧ s.val ok = if headerGood w then 1 else 0 := by
  simp only [validationPrefix, validationPrefixCommands, sequence, RAMCode.eval, const_eval]
  rw [parseAssert_eval t (by decide), parseAssert_eval b (by decide), assertPos_eval b]
  by_cases h0 : (splitOnes w).2 = []
  · simp [readState, initialRAM, RAMState.set, headerRest, headerTail, headerT, headerB,
      headerGood, splitOnes, h0]
  · by_cases h1 : (splitOnes (splitOnes w).2.tail).2 = []
    · simp [readState, initialRAM, RAMState.set, headerRest, headerTail, headerT, headerB,
        headerGood, h0, h1]
    · by_cases hb : (splitOnes (splitOnes w).2.tail).1 = 0
      · simp [readState, initialRAM, RAMState.set, headerRest, headerTail, headerT, headerB,
          headerGood, h0, h1, hb]
      · have hbpos := Nat.pos_of_ne_zero hb
        simp [readState, initialRAM, RAMState.set, headerRest, headerTail, headerT, headerB,
          headerGood, h0, h1, hbpos]

theorem splitOnes_word (w : List Letter) (h : (splitOnes w).2 ≠ []) :
    w = unary (headerT w) ++ headerTail w := by
  obtain ⟨he, hn, _, _⟩ := split_ones w
  cases hr : (splitOnes w).2 with
  | nil => exact (h hr).elim
  | cons c cs =>
      cases c with
      | one => simp [hr] at hn
      | sep => simpa [headerT, headerTail, unary, hr, List.append_assoc] using he

theorem good_header_word (w : List Letter) (h : headerGood w) :
    w = unary (headerT w) ++ unary (headerB w) ++ headerRest w := by
  have ht : headerTail w = unary (headerB w) ++ headerRest w :=
    splitOnes_word (headerTail w) h.2.1
  calc
    w = unary (headerT w) ++ headerTail w := splitOnes_word w h.1
    _ = unary (headerT w) ++ (unary (headerB w) ++ headerRest w) :=
      congrArg (fun z => unary (headerT w) ++ z) ht
    _ = _ := (List.append_assoc _ _ _).symm

theorem validate_out (s : RAMState ReductionReg) :
    (validate.eval s).out = s.out :=
  ram_field_frame validate false (by decide) s

end ResourceScheduling.ChainProof.ReductionProgram

end

/- Complete checked body: BudgetPrefix -/
section

set_option autoImplicit false

open ResourceScheduling.Graph

namespace ResourceScheduling.ChainProof.ReductionProgram

open ReductionReg

theorem parse_header_safe (v : ReductionReg) (h : v ≠ parseOk) (hv : v = t ∨ v = b)
    (N B : ℕ) (hNB : N ≤ B) (hB : 1 ≤ B) (s : RAMState ReductionReg)
    (hs : RAMBound B s) (hi : SmallInput N s) :
    RAMSafe (.parse v parseOk h : Code) B s ∧
      SmallInput N ((RAMCode.parse v parseOk h).eval s) := by
  have he := (split_ones s.word).2.2.1
  have hfirst : (splitOnes s.word).1 ≤ N := by have := hi.1; omega
  have htail : (splitOnes s.word).2.tail.length ≤ N := by
    rw [List.length_tail]
    have := hi.1
    omega
  have hu := ramBound_set (ramBound_set hs v _ (hfirst.trans hNB)) parseOk
    (if (splitOnes s.word).2 = [] then 0 else 1) (by split <;> omega)
  have hpost : RAMBound B ((RAMCode.parse v parseOk h).eval s) :=
    ⟨hu.1, htail.trans hNB⟩
  refine ⟨⟨hs, hpost⟩, ?_⟩
  rcases hv with rfl | rfl
  · simpa [SmallInput, RAMCode.eval, ramParseState, RAMState.set] using
      And.intro htail (And.intro hfirst (And.intro hi.2.2.1 hi.2.2.2))
  · simpa [SmallInput, RAMCode.eval, ramParseState, RAMState.set] using
      And.intro htail (And.intro hi.2.1 (And.intro hfirst hi.2.2.2))

theorem validationPrefix_budget (w : List Letter) :
    validationPrefix.Bounded (100 * (w.length + 1) ^ 2) (initialRAM w) ∧
      RAMBound ((w.length + 1) ^ 2) (validationPrefix.eval (initialRAM w)) ∧
      SmallInput w.length (validationPrefix.eval (initialRAM w)) := by
  let N := w.length
  let R := (N + 1) ^ 2
  have hNR : N ≤ R := by dsimp [R]; nlinarith [budget_square_expand N]
  have h1R : 1 ≤ R := by dsimp [R]; rw [budget_square_expand]; omega
  have hstep : ∀ p ∈ validationPrefixCommands, ∀ z : RAMState ReductionReg,
      RAMBound R z ∧ SmallInput N z →
      RAMSafe p R z ∧ (RAMBound R (p.eval z) ∧ SmallInput N (p.eval z)) := by
    intro p hp z hz
    simp only [validationPrefixCommands, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have hsafe : RAMSafe (const ok 1) R z :=
        ⟨const_bounded ok 1 z hz.1 h1R, const_bound_after ok 1 z hz.1 h1R⟩
      exact ⟨hsafe, hsafe.2, hz.2.preserve _ (by decide) (by decide) (by decide) (by decide)⟩
    · have hsafe : RAMSafe (const one 1) R z :=
        ⟨const_bounded one 1 z hz.1 h1R, const_bound_after one 1 z hz.1 h1R⟩
      exact ⟨hsafe, hsafe.2, hz.2.preserve _ (by decide) (by decide) (by decide) (by decide)⟩
    · obtain ⟨hh, hi⟩ := parse_header_safe t (by decide) (Or.inl rfl) N R hNR h1R z hz.1 hz.2
      exact ⟨hh, hh.2, hi⟩
    · have hh := safe_assertPos parseOk z hz.1
      exact ⟨hh, hh.2, hz.2.preserve _ (by decide) (by decide) (by decide) (by decide)⟩
    · obtain ⟨hh, hi⟩ := parse_header_safe b (by decide) (Or.inr rfl) N R hNR h1R z hz.1 hz.2
      exact ⟨hh, hh.2, hi⟩
    · have hh := safe_assertPos parseOk z hz.1
      exact ⟨hh, hh.2, hz.2.preserve _ (by decide) (by decide) (by decide) (by decide)⟩
    · have hh := safe_assertPos b z hz.1
      exact ⟨hh, hh.2, hz.2.preserve _ (by decide) (by decide) (by decide) (by decide)⟩
    · have hmul : z.val t * z.val b ≤ N ^ 2 := by
        simpa only [pow_two] using Nat.mul_le_mul hz.2.2.1 hz.2.2.2.1
      have he : RAMBound R ((RAMCode.mul t b prod (by decide)).eval z) :=
        ramBound_set hz.1 prod _ (hmul.trans (by dsimp [R]; nlinarith [budget_square_expand N]))
      refine ⟨⟨hz.1, he⟩, he, ?_⟩
      simpa [SmallInput, RAMCode.eval, RAMState.set] using
        And.intro hz.2.1 (And.intro hz.2.2.1 (And.intro hz.2.2.2.1 hmul))
    · have he := ramBound_set hz.1 count 0 (Nat.zero_le _)
      exact ⟨⟨hz.1, he⟩, he, hz.2.preserve _ (by decide) (by decide) (by decide) (by decide)⟩
    · have he := ramBound_set hz.1 sumA 0 (Nat.zero_le _)
      exact ⟨⟨hz.1, he⟩, he, hz.2.preserve _ (by decide) (by decide) (by decide) (by decide)⟩
  have hi : RAMBound R (initialRAM (V := ReductionReg) w) ∧
      SmallInput N (initialRAM w) := by
    constructor
    · exact ⟨fun _ => Nat.zero_le _, hNR⟩
    · simp [SmallInput, initialRAM, N]
  have hh := sequence_safe_invariant validationPrefixCommands R
    (fun z => RAMBound R z ∧ SmallInput N z) (fun _ h => h.1) hstep (initialRAM w) hi
  exact ⟨bounded_mono validationPrefix (by dsimp [R, N]; nlinarith [budget_square_expand N]) _ hh.1.1,
    hh.2.1, hh.2.2⟩

end ResourceScheduling.ChainProof.ReductionProgram

end

/- Complete checked body: BudgetSuffix -/
section

set_option autoImplicit false

open ResourceScheduling.Graph

namespace ResourceScheduling.ChainProof.ReductionProgram

open ReductionReg

theorem validationSuffix_safe (B N : ℕ) (hN : 3 * N ≤ B) (s : RAMState ReductionReg)
    (hs : RAMBound B s) (ht : s.val t ≤ N) : RAMSafe validationSuffix B s := by
  apply (sequence_safe_invariant _ B (fun z => RAMBound B z ∧ z.val t ≤ N)
    (fun _ h => h.1) ?_ s ⟨hs, ht⟩).1
  intro p hp z hz
  simp only [validationSuffixCommands, List.mem_cons, List.not_mem_nil, or_false] at hp
  have hpt : p.writes t = false := by
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  have hsafe : RAMSafe p B z := by
    rcases hp with rfl | rfl | rfl | rfl
    · exact safe_assertZero a z hz.1
    · exact safe_scale 3 t tmp (by decide) z hz.1 ((Nat.mul_le_mul_left 3 hz.2).trans hN)
    · exact assertEq_safe count tmp B z hz.1
    · exact assertEq_safe sumA prod B z hz.1
  exact ⟨hsafe, hsafe.2, (ram_footprint p t hpt z) ▸ hz.2⟩

end ResourceScheduling.ChainProof.ReductionProgram

end

/- Complete checked body: BudgetValidationRow -/
section

set_option autoImplicit false

open ResourceScheduling.Graph

namespace ResourceScheduling.ChainProof.ReductionProgram

open ReductionReg

def rowChecks : List Code :=
  [scale 4 a tmp (by decide), .sub tmp b diff, assertPos diff,
    scale 2 a tmp (by decide), .sub b tmp diff, assertPos diff]

theorem rowChecks_safe (B N : ℕ) (hN : 4 * N ≤ B) (s : RAMState ReductionReg)
    (hs : RAMBound B s) (ha : s.val a ≤ N) :
    RAMSafe (sequence rowChecks) B s := by
  have hstep : ∀ p ∈ rowChecks, ∀ z : RAMState ReductionReg,
      RAMBound B z ∧ z.val a ≤ N → RAMSafe p B z ∧
        (RAMBound B (p.eval z) ∧ (p.eval z).val a ≤ N) := by
    intro p hp z hz
    have hpa : p.writes a = false := by
      simp only [rowChecks, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hsafe : RAMSafe p B z := by
      simp only [rowChecks, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact safe_scale 4 a tmp (by decide) z hz.1 ((Nat.mul_le_mul_left 4 hz.2).trans hN)
      · exact safe_sub tmp b diff z hz.1
      · exact safe_assertPos diff z hz.1
      · apply safe_scale 2 a tmp (by decide) z hz.1
        nlinarith [hz.2]
      · exact safe_sub b tmp diff z hz.1
      · exact safe_assertPos diff z hz.1
    exact ⟨hsafe, hsafe.2, (ram_footprint p a hpa z) ▸ hz.2⟩
  exact (sequence_safe_invariant rowChecks B (fun z => RAMBound B z ∧ z.val a ≤ N)
    (fun _ h => h.1) hstep s ⟨hs, ha⟩).1

theorem validateRow_budget (D N B : ℕ) (s : RAMState ReductionReg)
    (hs : RAMBound D s) (ha : s.val a ≤ N) (hB : D + 4 * N + 2 ≤ B) :
    validateRow.Bounded B s ∧ RAMBound (D + 4 * N + 2) (validateRow.eval s) := by
  let R := D + 4 * N + 2
  let u := s.set count (s.val count + 1)
  let v := u.set sumA (s.val a + s.val sumA)
  have hsR : RAMBound R s := ramBound_mono hs (by dsimp [R]; omega)
  have hu : RAMBound R u := by
    apply ramBound_set hsR
    have := hs.1 count
    dsimp [R]
    omega
  have hv : RAMBound R v := by
    apply ramBound_set hu
    have := hs.1 sumA
    dsimp [R]
    omega
  have hva : v.val a ≤ N := by simpa [v, u, RAMState.set] using ha
  have hrest := rowChecks_safe R N (by dsimp [R]; omega) v hv hva
  have hall : RAMSafe validateRow R s := by
    change ((RAMBound R s ∧ RAMBound R u ∧ (sequence rowChecks).Bounded R v) ∧
      RAMBound R ((sequence rowChecks).eval v))
    exact ⟨⟨hsR, hu, hrest.1⟩, hrest.2⟩
  exact ⟨bounded_mono validateRow hB s hall.1, hall.2⟩

end ResourceScheduling.ChainProof.ReductionProgram

end

/- Complete checked body: BudgetScan -/
section

set_option autoImplicit false

open ResourceScheduling.Graph

namespace ResourceScheduling.ChainProof.ReductionProgram

open ReductionReg

theorem scanBody_budget (row : Code) (N B D E : ℕ) (s : RAMState ReductionReg)
    (hs : RAMBound D s) (hD : 1 ≤ D) (ha : s.val a ≤ N) (hB : D + E + 2 ≤ B)
    (hr : ∀ z, RAMBound D z → z.val a ≤ N →
      row.Bounded B z ∧ RAMBound (D + E) (row.eval z)) :
    (scanBody row).Bounded B s ∧ RAMBound (D + E + 2) ((scanBody row).eval s) ∧
      ((scanBody row).eval s).val a ≤ s.val a + 1 := by
  let z := (RAMCode.bit pos bit).eval s
  have hz : RAMBound D z := by
    apply ramBound_set hs bit
    split <;> omega
  have hza : z.val a = s.val a := by simp [z, RAMCode.eval, RAMState.set]
  obtain ⟨hrb, hre⟩ := hr z hz (hza ▸ ha)
  let q : Code := .branch bit (.inc a) (row.seq (.zero a))
  have hq : q.Bounded B z :=
    ⟨ramBound_mono hz (by omega), ⟨hrb, ramBound_mono hre (by omega)⟩⟩
  have he : RAMBound (D + E + 1) (q.eval z) := by
    dsimp only [q, RAMCode.eval]
    split
    · apply ramBound_set (ramBound_mono hz (by omega))
      have := hz.1 a
      omega
    · exact ramBound_set (ramBound_mono hre (by omega)) a 0 (Nat.zero_le _)
  have hqa : (q.eval z).val a ≤ s.val a + 1 := by
    dsimp only [q, RAMCode.eval]
    split <;> simp_all [RAMState.set]
  let w := (RAMCode.inc pos).eval (q.eval z)
  have hw : RAMBound (D + E + 2) w := by
    apply ramBound_set (ramBound_mono he (by omega))
    have := he.1 pos
    omega
  have hwa : w.val a ≤ s.val a + 1 := by
    simpa [w, RAMCode.eval, RAMState.set] using hqa
  refine ⟨?_, hw, hwa⟩
  exact ⟨ramBound_mono hs (by omega), hq, ramBound_mono he (by omega),
    ramBound_mono hw hB⟩

theorem scanRows_budget (row : Code) (N B A E : ℕ) (s : RAMState ReductionReg)
    (hs : RAMBound A s) (hA : 1 ≤ A) (hN : s.word.length ≤ N)
    (hB : A + (N + 1) * (E + 2) ≤ B)
    (hr : ∀ D z, RAMBound D z → 1 ≤ D → z.val a ≤ N → D + E + 2 ≤ B →
      row.Bounded B z ∧ RAMBound (D + E) (row.eval z)) :
    (scanRows row).Bounded B s ∧
      RAMBound (A + N * (E + 2)) ((scanRows row).eval s) ∧
      ((scanRows row).eval s).val a ≤ N := by
  let z := scanInitial s
  have hz : RAMBound A z :=
    ramBound_set (ramBound_set (ramBound_set hs a 0 (Nat.zero_le _)) pos 0 (Nat.zero_le _))
      scanCounter _ hs.2
  have hzB : RAMBound B z := ramBound_mono hz (by omega)
  have hloop := ram_loop_invariant scanCounter (scanBody row) B s.word.length
    (fun i x => RAMBound (A + i * (E + 2)) x ∧ x.val a ≤ i) z hzB (by rfl)
    (by simpa [z, scanInitial, RAMState.set] using And.intro hz (show z.val a ≤ 0 by rfl))
  have hsteps : ∀ i < s.word.length, ∀ x : RAMState ReductionReg,
      RAMBound (A + i * (E + 2)) x ∧ x.val a ≤ i →
      (scanBody row).Bounded B (x.set scanCounter (x.val scanCounter - 1)) ∧
        (RAMBound (A + (i + 1) * (E + 2))
          ((scanBody row).eval (x.set scanCounter (x.val scanCounter - 1))) ∧
        ((scanBody row).eval (x.set scanCounter (x.val scanCounter - 1))).val a ≤ i + 1) := by
    intro i hi x hx
    let D := A + i * (E + 2)
    have hDB : D + E + 2 ≤ B := by
      have hh := Nat.mul_le_mul_right (E + 2) (show i + 1 ≤ N + 1 by omega)
      dsimp [D]
      nlinarith
    have hD : 1 ≤ D := by dsimp [D]; omega
    have hdec : RAMBound D (x.set scanCounter (x.val scanCounter - 1)) :=
      ramBound_set hx.1 scanCounter _ ((Nat.sub_le _ _).trans (hx.1.1 scanCounter))
    have hda : (x.set scanCounter (x.val scanCounter - 1)).val a ≤ N := by
      simpa [RAMState.set] using hx.2.trans (show i ≤ N by omega)
    obtain ⟨hcode, hafter, hac⟩ := scanBody_budget row N B D E _ hdec hD hda hDB
      (fun z hz ha => hr D z hz hD ha hDB)
    refine ⟨hcode, ?_, ?_⟩
    · convert hafter using 1
      dsimp [D]
      ring
    · have hxa : (x.set scanCounter (x.val scanCounter - 1)).val a = x.val a := by simp [RAMState.set]
      rw [hxa] at hac
      omega
  obtain ⟨hlb, hle, hla⟩ := hloop hsteps
  have hleB : RAMBound B ((RAMCode.loop scanCounter (scanBody row)).eval z) :=
    ramBound_mono hle (by
      have hh := Nat.mul_le_mul_right (E + 2) (show s.word.length ≤ N + 1 by omega)
      omega)
  refine ⟨?_, ?_, hla.trans hN⟩
  · exact ⟨ramBound_mono hs (by omega),
      ramBound_mono (ramBound_set hs a 0 (Nat.zero_le _)) (by omega),
      ramBound_mono (ramBound_set (ramBound_set hs a 0 (Nat.zero_le _)) pos 0 (Nat.zero_le _)) (by omega),
      hlb, hleB⟩
  · exact ramBound_mono hle (Nat.add_le_add_left (Nat.mul_le_mul_right _ hN) A)

end ResourceScheduling.ChainProof.ReductionProgram

end

/- Complete checked body: BudgetValidation -/
section

set_option autoImplicit false

open ResourceScheduling.Graph

namespace ResourceScheduling.ChainProof.ReductionProgram

theorem validate_bounded_chunks (B : ℕ) (s p q : RAMState ReductionReg)
    (hsp : validationPrefix.eval s = p) (hsq : (scanRows validateRow).eval p = q)
    (hp : RAMSafe validationPrefix B s)
    (hq : RAMSafe (scanRows validateRow) B p) (hr : RAMSafe validationSuffix B q) :
    validate.Bounded B s := by
  change (sequence (validationPrefixCommands ++ ([scanRows validateRow] ++
    validationSuffixCommands))).Bounded B s
  apply sequence_append_bounded validationPrefixCommands _ B s hp.1
  change (sequence ([scanRows validateRow] ++ validationSuffixCommands)).Bounded B (validationPrefix.eval s)
  rw [hsp]
  apply sequence_append_bounded [scanRows validateRow] _ B p ⟨hq.1, hq.2⟩
  change validationSuffix.Bounded B ((scanRows validateRow).eval p)
  rw [hsq]
  exact hr.1

theorem validate_budget (w : List Letter) :
    validate.Bounded (100 * (w.length + 1) ^ 2) (initialRAM w) ∧
      RAMBound (5 * (w.length + 1) ^ 2) (validate.eval (initialRAM w)) ∧
      SmallInput w.length (validate.eval (initialRAM w)) := by
  let N := w.length
  let A := (N + 1) ^ 2
  let R := 5 * (N + 1) ^ 2
  let B := 100 * (N + 1) ^ 2
  have he := validate_factor (initialRAM w)
  generalize hp : validationPrefix.eval (initialRAM w) = p at he
  generalize hq : (scanRows validateRow).eval p = q at he
  have hP := validationPrefix_budget w
  rw [hp] at hP
  have hscan := scanRows_budget validateRow N B A (4 * N + 2) p hP.2.1
    (by dsimp [A]; rw [budget_square_expand]; omega) hP.2.2.1 (by dsimp [A, B]; nlinarith [budget_square_expand N])
    (fun D z hz _ ha hDB => validateRow_budget D N B z hz ha (by omega))
  have hQ : RAMBound R q := by
    rw [← hq]
    exact ramBound_mono hscan.2.1 (by dsimp [A, R]; nlinarith [budget_square_expand N])
  have hiQ : SmallInput N q := by
    rw [← hq]
    exact hP.2.2.preserve (scanRows validateRow) (by decide) (by decide) (by decide) (by decide)
  have hS := validationSuffix_safe R N (by dsimp [R]; nlinarith [budget_square_expand N]) q hQ hiQ.2.1
  have hRB : R ≤ B := by dsimp [R, B]; nlinarith [budget_square_expand N]
  refine ⟨?_, ?_, ?_⟩
  · apply validate_bounded_chunks B (initialRAM w) p q hp hq
    · exact ⟨hP.1, by rw [hp]; exact ramBound_mono hP.2.1 (by dsimp [A, B]; nlinarith [budget_square_expand N])⟩
    · exact ⟨hscan.1, by rw [hq]; exact ramBound_mono hQ hRB⟩
    · exact ⟨bounded_mono _ hRB _ hS.1, ramBound_mono hS.2 hRB⟩
  · rw [he]
    exact hS.2
  · rw [he]
    exact hiQ.preserve validationSuffix (by decide) (by decide) (by decide) (by decide)

end ResourceScheduling.ChainProof.ReductionProgram

end

/- Complete checked body: BudgetEmission -/
section

set_option autoImplicit false

open ResourceScheduling.Graph

namespace ResourceScheduling.ChainProof.ReductionProgram

open ReductionReg

theorem emitRowRequirements_safe (B : ℕ) (s : RAMState ReductionReg) (hs : RAMBound B s) :
    RAMSafe emitRowRequirements B s := by
  apply (sequence_safe_invariant _ B (RAMBound B) (fun _ h => h) ?_ s hs).1
  intro p hp z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  have hsafe : RAMSafe p B z := by
    rcases hp with rfl | rfl | rfl | rfl
    · exact safe_copy a jobCounter (by decide) B z hz
    · exact safe_emit_loop zero jobCounter B z hz
    · exact safe_copy a jobCounter (by decide) B z hz
    · exact safe_emit_loop one jobCounter B z hz
  exact ⟨hsafe, hsafe.2⟩

theorem blockBody_safe (B : ℕ) (s : RAMState ReductionReg) (hs : RAMBound B s) :
    RAMSafe blockBody B s := by
  apply (sequence_safe_invariant _ B (RAMBound B) (fun _ h => h) ?_ s hs).1
  intro p hp z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  have hsafe : RAMSafe p B z := by
    rcases hp with rfl | rfl | rfl
    · exact safe_copy b jobCounter (by decide) B z hz
    · exact safe_emit_loop flag jobCounter B z hz
    · exact safe_sub one flag flag z hz
  exact ⟨hsafe, hsafe.2⟩

theorem emitL_safe (B : ℕ) (s : RAMState ReductionReg) (hs : RAMBound B s)
    (ht : 2 * s.val t ≤ B) (hB : 1 ≤ B) : RAMSafe emitL B s := by
  have hscale := safe_scale 2 t blockCounter (by decide) s hs ht
  have hc : RAMSafe (const flag 1) B ((scale 2 t blockCounter (by decide)).eval s) :=
    ⟨const_bounded flag 1 _ hscale.2 hB, const_bound_after flag 1 _ hscale.2 hB⟩
  have hl := safe_loop_closed blockBody blockCounter B (blockBody_safe B) _ hc.2
  exact ⟨⟨hscale.1, hc.1, hl.1, hl.2⟩, hl.2⟩

def arcBody : Code := sequence [.emit offset, .inc offset, .emit offset]

theorem arcBody_safe (B : ℕ) (s : RAMState ReductionReg) (hs : RAMBound B s)
    (ho : s.val offset + 1 ≤ B) : RAMSafe arcBody B s := by
  have he : RAMBound B ((RAMCode.emit offset).eval s) := hs
  have hi : RAMBound B ((RAMCode.inc offset).eval ((RAMCode.emit offset).eval s)) :=
    ramBound_set he offset _ ho
  exact ⟨⟨hs, he, hi, hi⟩, hi⟩

theorem emitChain_safe (B : ℕ) (s : RAMState ReductionReg) (hs : RAMBound B s)
    (hoff : s.val offset + s.val len + 1 ≤ B) : RAMSafe emitChain B s := by
  let z := s.set jobCounter (s.val len - 1)
  have hz : RAMBound B z := ramBound_set hs jobCounter _ ((Nat.sub_le _ _).trans (hs.1 len))
  have hiter : ∀ i, i ≤ s.val len - 1 → RAMBound B ((arcStep^[i]) z) := by
    intro i hi
    rw [arcStep_iter]
    apply ramBound_set
    · exact ramBound_set hz jobCounter _ ((Nat.sub_le _ _).trans (hz.1 jobCounter))
    · change s.val offset + i ≤ B
      omega
  have hloop : (RAMCode.loop jobCounter arcBody).Bounded B z := by
    refine ⟨hz, ?_⟩
    intro i hi
    have his : i < s.val len - 1 := by simpa [z, RAMState.set] using hi
    have hb := hiter i (Nat.le_of_lt his)
    apply (arcBody_safe B _
      (ramBound_set hb jobCounter _ ((Nat.sub_le _ _).trans (hb.1 jobCounter))) ?_).1
    rw [arcStep_iter]
    simp only [RAMState.set, Function.update_of_ne (by decide : offset ≠ jobCounter),
      appendOutput_val, Function.update_self]
    change s.val offset + i + 1 ≤ B
    omega
  have hlast := hiter (s.val len - 1) le_rfl
  have hend : RAMBound B ((RAMCode.inc offset).eval ((RAMCode.loop jobCounter arcBody).eval z)) := by
    apply ramBound_set hlast
    change ((arcStep^[s.val len - 1]) z).val offset + 1 ≤ B
    rw [arcStep_iter]
    simp only [appendOutput_val, RAMState.set, Function.update_self]
    change s.val offset + (s.val len - 1) + 1 ≤ B
    omega
  have hez : (RAMCode.dec jobCounter).eval ((RAMCode.copy len jobCounter (by decide)).eval s) = z := by
    simp [RAMCode.eval, RAMState.set, Function.update_idem, z]
  have htrue : (sequence [.copy len jobCounter (by decide), .dec jobCounter,
      .loop jobCounter arcBody, .inc offset]).Bounded B s := by
    refine ⟨hs, ramBound_set hs jobCounter _ (hs.1 len), ?_⟩
    rw [hez]
    exact ⟨hloop, hlast, hend⟩
  refine ⟨⟨htrue, hs⟩, ?_⟩
  rw [emitChain_eval]
  split
  · exact hs
  · apply ramBound_set (ramBound_set hs jobCounter 0 (Nat.zero_le _))
    omega

theorem emitRowArcs_budget (D N B : ℕ) (s : RAMState ReductionReg)
    (hs : RAMBound D s) (ha : s.val a ≤ N) (hB : D + 2 * N + 2 ≤ B) :
    emitRowArcs.Bounded B s ∧ RAMBound (D + 2 * N + 2) (emitRowArcs.eval s) := by
  let R := D + 2 * N + 2
  have hsR : RAMBound R s := ramBound_mono hs (by dsimp [R]; omega)
  have hsc := safe_scale 2 a len (by decide) s hsR (by dsimp [R]; omega)
  have he := emitChain_safe R ((scale 2 a len (by decide)).eval s) hsc.2 (by
    rw [scale_eval]
    simp only [RAMState.set, Function.update_self, Function.update_of_ne (by decide : offset ≠ len)]
    have := hs.1 offset
    dsimp [R]
    omega)
  exact ⟨bounded_mono emitRowArcs hB s ⟨hsc.1, he.1⟩, he.2⟩

end ResourceScheduling.ChainProof.ReductionProgram

end

/- Complete checked body: BudgetOutput -/
section

set_option autoImplicit false

open ResourceScheduling.Graph

namespace ResourceScheduling.ChainProof.ReductionProgram

open ReductionReg

theorem emitHeader_safe (B N : ℕ) (hN : 4 * N ^ 2 ≤ B) (hB : 2 ≤ B)
    (s : RAMState ReductionReg) (hs : RAMBound B s) (hp : s.val prod ≤ N ^ 2) :
    RAMSafe emitHeader B s := by
  apply (sequence_safe_invariant _ B (fun z => RAMBound B z ∧ z.val prod ≤ N ^ 2)
    (fun _ h => h.1) ?_ s ⟨hs, hp⟩).1
  intro p hp' z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
  have hpp : p.writes prod = false := by
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hsafe : RAMSafe p B z := by
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact safe_scale 4 prod jobs (by decide) z hz.1 ((Nat.mul_le_mul_left 4 hz.2).trans hN)
    · apply safe_scale 2 prod horizon (by decide) z hz.1
      nlinarith [hz.2]
    · exact ⟨hz.1, hz.1⟩
    · exact ⟨const_bounded tmp 2 z hz.1 hB, const_bound_after tmp 2 z hz.1 hB⟩
    · exact ⟨hz.1, hz.1⟩
    · exact ⟨hz.1, hz.1⟩
    · exact ⟨hz.1, hz.1⟩
  exact ⟨hsafe, hsafe.2, (ram_footprint p prod hpp z) ▸ hz.2⟩

theorem emitCount_safe (B : ℕ) (s : RAMState ReductionReg)
    (hs : RAMBound B s) (ht : 3 * s.val t + 1 ≤ B) : RAMSafe emitCount B s := by
  have hscale := safe_scale 3 t tmp (by decide) s hs (by omega)
  have hinc : RAMSafe (.inc tmp : Code) B ((scale 3 t tmp (by decide)).eval s) := by
    refine ⟨hscale.2, ramBound_set hscale.2 tmp _ ?_⟩
    simpa [scale_eval, RAMState.set] using ht
  have hsub := safe_sub jobs tmp arcCount _ hinc.2
  exact ⟨⟨hscale.1, hinc.1, hsub.1, hsub.2, hsub.2⟩, hsub.2⟩

theorem emitAllArcs_budget (N B A : ℕ) (s : RAMState ReductionReg)
    (hs : RAMBound A s) (hA : 2 * N ^ 2 + 1 ≤ A)
    (hN : s.word.length ≤ N) (hh : s.val horizon ≤ 2 * N ^ 2)
    (hB : A + (N + 1) * (2 * N + 4) ≤ B) :
    emitAllArcs.Bounded B s ∧
      RAMBound (A + N * (2 * N + 4)) (emitAllArcs.eval s) := by
  let z := (s.set offset 0).set len (s.val horizon)
  have hz : RAMBound A z := ramBound_set (ramBound_set hs offset 0 (Nat.zero_le _)) len _ (by omega)
  have hchain := emitChain_safe A z hz (by simp [z, RAMState.set]; omega)
  have hw : (emitChain.eval z).word.length ≤ N := by rwa [emitChain_word]
  have hscan := scanRows_budget emitRowArcs N B A (2 * N + 2) (emitChain.eval z)
    hchain.2 (by omega) hw (by simpa [Nat.add_assoc] using hB)
    (fun D y hy _ ha hDB => emitRowArcs_budget D N B y hy ha (by omega))
  have hpostB : RAMBound B ((scanRows emitRowArcs).eval (emitChain.eval z)) :=
    ramBound_mono hscan.2.1 (by nlinarith)
  refine ⟨?_, ?_⟩
  · exact ⟨ramBound_mono hs (by nlinarith),
      ramBound_mono (ramBound_set hs offset 0 (Nat.zero_le _)) (by nlinarith),
      bounded_mono emitChain (by nlinarith) z hchain.1, hscan.1, hpostB⟩
  · change RAMBound (A + N * (2 * N + 4)) ((scanRows emitRowArcs).eval (emitChain.eval z))
    convert hscan.2.1 using 1

end ResourceScheduling.ChainProof.ReductionProgram

end

/- Complete checked body: BudgetProgramOutput -/
section

set_option autoImplicit false

open ResourceScheduling.Graph

namespace ResourceScheduling.ChainProof.ReductionProgram

open ReductionReg

theorem emitInstance_bounded_chunks (B : ℕ) (s s1 s2 s3 s4 s5 : RAMState ReductionReg)
    (hs1 : emitHeader.eval s = s1) (hs2 : emitL.eval s1 = s2)
    (hs3 : (scanRows emitRowRequirements).eval s2 = s3)
    (hs4 : emitCount.eval s3 = s4) (hs5 : emitAllArcs.eval s4 = s5)
    (hH : RAMSafe emitHeader B s)
    (hL : RAMSafe emitL B s1) (hR : RAMSafe (scanRows emitRowRequirements) B s2)
    (hC : RAMSafe emitCount B s3) (hA : RAMSafe emitAllArcs B s4) : emitInstance.Bounded B s := by
  let ph := [scale 4 prod jobs (by decide), scale 2 prod horizon (by decide),
    .emit jobs, const tmp 2, .emit tmp, .emit one, .emit one]
  let pl := [scale 2 t blockCounter (by decide), const flag 1, .loop blockCounter blockBody]
  let pc := [scale 3 t tmp (by decide), .inc tmp, .sub jobs tmp arcCount, .emit arcCount]
  let pa := [.zero offset, .copy horizon len (by decide), emitChain, scanRows emitRowArcs]
  change (sequence (ph ++ (pl ++ ([scanRows emitRowRequirements] ++
    (pc ++ (pa ++ [.emit horizon])))))).Bounded B s
  apply sequence_append_bounded ph _ B s hH.1
  change (sequence (pl ++ ([scanRows emitRowRequirements] ++
    (pc ++ (pa ++ [.emit horizon]))))).Bounded B (emitHeader.eval s)
  rw [hs1]
  apply sequence_append_bounded pl _ B s1 hL.1
  change (sequence ([scanRows emitRowRequirements] ++ (pc ++ (pa ++ [.emit horizon])))).Bounded B (emitL.eval s1)
  rw [hs2]
  apply sequence_append_bounded [scanRows emitRowRequirements] _ B s2 ⟨hR.1, hR.2⟩
  change (sequence (pc ++ (pa ++ [.emit horizon]))).Bounded B ((scanRows emitRowRequirements).eval s2)
  rw [hs3]
  apply sequence_append_bounded pc _ B s3 hC.1
  change (sequence (pa ++ [.emit horizon])).Bounded B (emitCount.eval s3)
  rw [hs4]
  apply sequence_append_bounded pa _ B s4 hA.1
  change (sequence [.emit horizon]).Bounded B (emitAllArcs.eval s4)
  rw [hs5]
  have h5 : RAMBound B s5 := by simpa only [hs5] using hA.2
  exact ⟨h5, h5⟩

theorem emitInstance_budget (N : ℕ) (s : RAMState ReductionReg)
    (hs : RAMBound (5 * (N + 1) ^ 2) s) (hi : SmallInput N s) :
    emitInstance.Bounded (100 * (N + 1) ^ 2) s ∧
      RAMBound (11 * (N + 1) ^ 2) (emitInstance.eval s) := by
  let B := 100 * (N + 1) ^ 2
  let A := 5 * (N + 1) ^ 2
  let C := 7 * (N + 1) ^ 2
  have he : emitInstance.eval s = (RAMCode.emit horizon).eval
      (emitAllArcs.eval (emitCount.eval ((scanRows emitRowRequirements).eval
        (emitL.eval (emitHeader.eval s))))) := by rfl
  generalize hs1 : emitHeader.eval s = s1 at he
  generalize hs2 : emitL.eval s1 = s2 at he
  generalize hs3 : (scanRows emitRowRequirements).eval s2 = s3 at he
  generalize hs4 : emitCount.eval s3 = s4 at he
  generalize hs5 : emitAllArcs.eval s4 = s5 at he
  have hAB : A ≤ B := by dsimp [A, B]; nlinarith [budget_square_expand N]
  have hCB : C ≤ B := by dsimp [C, B]; nlinarith [budget_square_expand N]
  have hH := emitHeader_safe A N (by dsimp [A]; nlinarith [budget_square_expand N])
    (by dsimp [A]; nlinarith [budget_square_expand N])
    s hs hi.2.2.2
  have h1 : RAMBound A s1 := by simpa only [hs1] using hH.2
  have hi1 : SmallInput N s1 := by
    simpa only [hs1] using hi.preserve emitHeader (by decide) (by decide) (by decide) (by decide)
  have hh1 : s1.val horizon ≤ 2 * N ^ 2 := by
    rw [← hs1, emitHeader_eval]
    simp only [appendOutput_val, RAMState.set, Function.update_of_ne (by decide : horizon ≠ tmp),
      Function.update_self]
    exact Nat.mul_le_mul_left 2 hi.2.2.2
  have hL := emitL_safe A s1 h1 (by have := hi1.2.1; dsimp [A]; nlinarith [budget_square_expand N])
    (by dsimp [A]; nlinarith [budget_square_expand N])
  have h2 : RAMBound A s2 := by simpa only [hs2] using hL.2
  have hi2 : SmallInput N s2 := by
    simpa only [hs2] using hi1.preserve emitL (by decide) (by decide) (by decide) (by decide)
  have hh2 : s2.val horizon ≤ 2 * N ^ 2 := by
    rw [← hs2, ram_footprint emitL horizon (by decide)]
    exact hh1
  have hR := scanRows_budget emitRowRequirements N B A 0 s2 h2
    (by dsimp [A]; nlinarith [budget_square_expand N])
    hi2.1 (by dsimp [A, B]; nlinarith [budget_square_expand N])
    (fun D z hz _ _ hDB => ⟨bounded_mono _ (by omega) z (emitRowRequirements_safe D z hz).1,
      by simpa using (emitRowRequirements_safe D z hz).2⟩)
  have h3 : RAMBound C s3 := by
    rw [← hs3]
    exact ramBound_mono hR.2.1 (by dsimp [A, C]; nlinarith [budget_square_expand N])
  have hi3 : SmallInput N s3 := by
    simpa only [hs3] using hi2.preserve (scanRows emitRowRequirements)
      (by decide) (by decide) (by decide) (by decide)
  have hh3 : s3.val horizon ≤ 2 * N ^ 2 := by
    rw [← hs3, ram_footprint (scanRows emitRowRequirements) horizon (by decide)]
    exact hh2
  have hC := emitCount_safe C s3 h3 (by have := hi3.2.1; dsimp [C]; nlinarith [budget_square_expand N])
  have h4 : RAMBound C s4 := by simpa only [hs4] using hC.2
  have hi4 : SmallInput N s4 := by
    simpa only [hs4] using hi3.preserve emitCount (by decide) (by decide) (by decide) (by decide)
  have hh4 : s4.val horizon ≤ 2 * N ^ 2 := by
    rw [← hs4, ram_footprint emitCount horizon (by decide)]
    exact hh3
  have hA := emitAllArcs_budget N B C s4 h4 (by dsimp [C]; nlinarith [budget_square_expand N]) hi4.1 hh4
    (by dsimp [C, B]; nlinarith [budget_square_expand N])
  have h5 : RAMBound (11 * (N + 1) ^ 2) s5 := by
    rw [← hs5]
    exact ramBound_mono hA.2 (by dsimp [C]; nlinarith [budget_square_expand N])
  refine ⟨?_, ?_⟩
  · apply emitInstance_bounded_chunks B s s1 s2 s3 s4 s5 hs1 hs2 hs3 hs4 hs5
    · exact ⟨bounded_mono _ hAB _ hH.1, ramBound_mono hH.2 hAB⟩
    · exact ⟨bounded_mono _ hAB _ hL.1, ramBound_mono hL.2 hAB⟩
    · exact ⟨hR.1, by rw [hs3]; exact ramBound_mono h3 hCB⟩
    · exact ⟨bounded_mono _ hCB _ hC.1, ramBound_mono hC.2 hCB⟩
    · exact ⟨hA.1, by rw [hs5]; exact ramBound_mono h5 (by dsimp [B]; nlinarith [budget_square_expand N])⟩
  · rw [he]
    exact h5

end ResourceScheduling.ChainProof.ReductionProgram

end

/- Complete checked body: ProgramBounds -/
section

set_option autoImplicit false

open ResourceScheduling.Graph

namespace ResourceScheduling.ChainProof.ReductionProgram

theorem program_polynomial_bound : ∃ C k : ℕ, ∀ w : List Letter,
    program.Bounded (C * (w.length + 1) ^ k) (initialRAM w) := by
  refine ⟨100, 2, ?_⟩
  intro w
  have hv := validate_budget w
  have he := emitInstance_budget w.length (validate.eval (initialRAM w)) hv.2.1 hv.2.2
  exact ⟨hv.1, he.1, ramBound_mono hv.2.1 (by nlinarith)⟩

end ResourceScheduling.ChainProof.ReductionProgram

end

/- Complete checked body: ValidationSuffix -/
section

open ResourceScheduling.Graph

namespace ResourceScheduling.ChainProof.ReductionProgram

open ReductionReg

theorem assertZero_ok (v : ReductionReg) (s : RAMState ReductionReg) :
    ((assertZero v).eval s).val ok = if s.val v = 0 then s.val ok else 0 := by
  by_cases h : s.val v = 0
  · simp [assertZero, RAMCode.eval, h]
  · have hp : 0 < s.val v := Nat.pos_of_ne_zero h
    simp [assertZero, RAMCode.eval, RAMState.set, hp, h]

theorem assertZero_fixed (v w : ReductionReg) (hw : w ≠ ok) (s : RAMState ReductionReg) :
    ((assertZero v).eval s).val w = s.val w :=
  ram_footprint (assertZero v) w (by simp [assertZero, RAMCode.writes, hw]) s

theorem assertEq_fixed (i j v : ReductionReg) (hv : v ≠ diff ∧ v ≠ ok)
    (s : RAMState ReductionReg) : ((assertEq i j).eval s).val v = s.val v :=
  ram_footprint (assertEq i j) v
    (by simp [assertEq, sequence, assertZero, RAMCode.writes, hv.1, hv.2]) s

theorem assertEq_ok (i j : ReductionReg) (hi : i ≠ diff ∧ i ≠ ok)
    (hj : j ≠ diff ∧ j ≠ ok) (s : RAMState ReductionReg) :
    ((assertEq i j).eval s).val ok = if s.val i = s.val j then s.val ok else 0 := by
  by_cases he : s.val i = s.val j
  · simp [assertEq, sequence, assertZero, RAMCode.eval, RAMState.set, hi.1, hj.1, he]
  · rcases lt_or_gt_of_ne he with hlt | hgt
    · have h0 : s.val i - s.val j = 0 := Nat.sub_eq_zero_of_le hlt.le
      have hp : 0 < s.val j - s.val i := by omega
      simp [assertEq, sequence, assertZero, RAMCode.eval, RAMState.set,
        hi.1, hj.1, he, h0, hp]
    · have h0 : s.val j - s.val i = 0 := Nat.sub_eq_zero_of_le hgt.le
      have hp : 0 < s.val i - s.val j := by omega
      simp [assertEq, sequence, assertZero, RAMCode.eval, RAMState.set,
        hi.1, hi.2, hj.1, hj.2, he, h0, hp]

theorem validationSuffix_ok (s : RAMState ReductionReg) :
    (validationSuffix.eval s).val ok =
      if s.val a = 0 ∧ s.val count = 3 * s.val t ∧ s.val sumA = s.val prod
      then s.val ok else 0 := by
  have hc : (validationSuffix.eval s).val ok =
      if s.val sumA = s.val prod then
        (if s.val count = 3 * s.val t then
          (if s.val a = 0 then s.val ok else 0) else 0) else 0 := by
    simp [validationSuffix, validationSuffixCommands, sequence, RAMCode.eval, assertEq_ok, assertEq_fixed,
      scale_eval, assertZero_ok, assertZero_fixed, RAMState.set]
  rw [hc]
  split_ifs <;> simp_all

theorem validationSuffix_fixed (v : ReductionReg) (hv : v ≠ ok ∧ v ≠ tmp ∧ v ≠ diff)
    (s : RAMState ReductionReg) : (validationSuffix.eval s).val v = s.val v :=
  ram_footprint validationSuffix v
    (by simp [validationSuffix, validationSuffixCommands, sequence, scale, assertEq, assertZero, RAMCode.writes,
      hv.1, hv.2.1, hv.2.2]) s

theorem validationSuffix_word (s : RAMState ReductionReg) :
    (validationSuffix.eval s).word = s.word :=
  ram_field_frame validationSuffix true (by decide) s

end ResourceScheduling.ChainProof.ReductionProgram

end

/- Complete checked body: ValidationCriterion -/
section

open ResourceScheduling.Graph ResourceScheduling.Chain

namespace ResourceScheduling.ChainProof.ReductionProgram

open ReductionReg

def validationCondition (w : List Letter) (ns : List ℕ) (r : ℕ) : Prop :=
  headerGood w ∧ r = 0 ∧ ns.length = 3 * headerT w ∧ ns.sum = headerT w * headerB w ∧
    ns.all (fun n => decide (goodItem (headerB w) n)) = true

instance (w : List Letter) (ns : List ℕ) (r : ℕ) : Decidable (validationCondition w ns r) := by
  unfold validationCondition
  infer_instance

theorem validate_ok_formula (w : List Letter) (ns : List ℕ) (r : ℕ)
    (hw : headerRest w = encNatList ns ++ List.replicate r Letter.one) :
    (validate.eval (initialRAM w)).val ok = if validationCondition w ns r then 1 else 0 := by
  have hp := validationPrefix_spec w
  dsimp only at hp
  rw [validate_factor]
  generalize hpre : validationPrefix.eval (initialRAM w) = sp at hp ⊢
  obtain ⟨hword, ht, hb, hprod, hcount, hsum, _, _, hok⟩ := hp
  have hs := validation_scan_summary sp ns r (hword.trans hw)
  dsimp only at hs
  generalize hscan : (scanRows validateRow).eval sp = ss at hs ⊢
  obtain ⟨hsa, hsb, hscount, hssum, hsok⟩ := hs
  have hst : ss.val t = sp.val t := by
    rw [← hscan]
    exact ram_footprint (scanRows validateRow) t (by decide) sp
  have hsp : ss.val prod = sp.val prod := by
    rw [← hscan]
    exact ram_footprint (scanRows validateRow) prod (by decide) sp
  rw [validationSuffix_ok, hsa, hscount, hssum, hst, hsp, hcount, hsum, ht, hprod,
    hsok, hb, hok]
  simp only [zero_add]
  unfold validationCondition
  split_ifs <;> simp_all

theorem validate_accept_sound (w : List Letter)
    (h : 0 < (validate.eval (initialRAM w)).val ok) :
    ∃ P : ThreePartition, P.Valid ∧ w.map alphabetEquiv.symm = encNats P.code := by
  obtain ⟨ns, r, hw⟩ := exists_word_decomposition (headerRest w)
  have hc : validationCondition w ns r := by
    by_contra hn
    rw [validate_ok_formula w ns r hw, if_neg hn] at h
    omega
  obtain ⟨hh, hr, hn, hs, hall⟩ := hc
  subst r
  simp only [List.replicate_zero, List.append_nil] at hw
  let P : ThreePartition := ⟨headerT w, headerB w, fun i => ns.getD i 0⟩
  have ha : ∀ n ∈ ns, goodItem (headerB w) n := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using hall
  have hP : P.Valid :=
    (list_partition_valid (headerT w) (headerB w) ns hn).2 ⟨hh.2.2, hs, ha⟩
  have hword : w = encNatList (headerT w :: headerB w :: ns) := by
    calc
      w = unary (headerT w) ++ unary (headerB w) ++ headerRest w := good_header_word w hh
      _ = unary (headerT w) ++ unary (headerB w) ++ encNatList ns := by rw [hw]
      _ = _ := by simp [encNatList, List.append_assoc]
  have hcode : P.code = headerT w :: headerB w :: ns := by
    change [headerT w, headerB w] ++ List.ofFn (fun i : Fin (3 * headerT w) => ns.getD i 0) = _
    rw [ofFn_getD_eq ns hn]
    rfl
  refine ⟨P, hP, ?_⟩
  rw [hword, alphabet_encNatList, hcode]

theorem validate_frame (v : ReductionReg)
    (hs : (scanRows validateRow).writes v = false)
    (hf : validationSuffix.writes v = false) (s : RAMState ReductionReg) :
    (validate.eval s).val v = (validationPrefix.eval s).val v := by
  rw [validate_factor, ram_footprint validationSuffix v hf,
    ram_footprint (scanRows validateRow) v hs]

theorem validate_data (w : List Letter) :
    let s := validate.eval (initialRAM w)
    s.word = headerRest w ∧ s.val t = headerT w ∧ s.val b = headerB w ∧
      s.val prod = headerT w * headerB w ∧ s.val zero = 0 ∧ s.val one = 1 := by
  have hp := validationPrefix_spec w
  dsimp only at hp ⊢
  obtain ⟨hw, ht, hb, hprod, _, _, hz, ho, _⟩ := hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [validate_factor]
    exact (ram_field_frame validationSuffix true (by decide) _).trans
      ((ram_field_frame (scanRows validateRow) true (by decide) _).trans hw)
  · exact (validate_frame t (by decide) (by decide) _).trans ht
  · exact (validate_frame b (by decide) (by decide) _).trans hb
  · exact (validate_frame prod (by decide) (by decide) _).trans hprod
  · exact (validate_frame zero (by decide) (by decide) _).trans hz
  · exact (validate_frame one (by decide) (by decide) _).trans ho

end ResourceScheduling.ChainProof.ReductionProgram

end

/- Complete checked body: ValidationEncoded -/
section

open ResourceScheduling.Graph ResourceScheduling.Chain

namespace ResourceScheduling.ChainProof.ReductionProgram

open ReductionReg

theorem splitOnes_unary (n : ℕ) (w : List Letter) :
    splitOnes (unary n ++ w) = (n, Letter.sep :: w) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change ((splitOnes (unary n ++ w)).1 + 1, (splitOnes (unary n ++ w)).2) = _
      rw [ih]

theorem header_encoded (t b : ℕ) (ns : List ℕ) (hb : 0 < b) :
    headerT (encNatList (t :: b :: ns)) = t ∧
    headerB (encNatList (t :: b :: ns)) = b ∧
    headerRest (encNatList (t :: b :: ns)) = encNatList ns ∧
    headerGood (encNatList (t :: b :: ns)) := by
  simp [headerT, headerB, headerTail, headerRest, headerGood, encNatList,
    splitOnes_unary, hb]

theorem validate_encoded_ok (P : ThreePartition) (hP : P.Valid) :
    (validate.eval (initialRAM (encNatList P.code))).val ok = 1 := by
  have hh := header_encoded P.t P.b (List.ofFn P.a) hP.1
  change headerT (encNatList P.code) = P.t ∧ headerB (encNatList P.code) = P.b ∧
    headerRest (encNatList P.code) = encNatList (List.ofFn P.a) ∧ headerGood (encNatList P.code) at hh
  obtain ⟨ht, hb, hw, hg⟩ := hh
  have hc : validationCondition (encNatList P.code) (List.ofFn P.a) 0 := by
    refine ⟨hg, rfl, ?_, ?_, ?_⟩
    · rw [ht]
      exact List.length_ofFn
    · rw [ht, hb, List.sum_ofFn]
      exact hP.2.1
    · simp only [List.all_eq_true, decide_eq_true_eq]
      intro n hn
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hn
      rw [hb]
      exact hP.2.2 i
  rw [validate_ok_formula _ _ 0 (by simpa using hw), if_pos hc]

theorem validate_encoded_data (P : ThreePartition) (hP : P.Valid) :
    let s := validate.eval (initialRAM (encNatList P.code))
    s.word = encNatList (List.ofFn P.a) ∧ s.val t = P.t ∧ s.val b = P.b ∧
      s.val prod = P.t * P.b ∧ s.val zero = 0 ∧ s.val one = 1 := by
  have hh := header_encoded P.t P.b (List.ofFn P.a) hP.1
  change headerT (encNatList P.code) = P.t ∧ headerB (encNatList P.code) = P.b ∧
    headerRest (encNatList P.code) = encNatList (List.ofFn P.a) ∧ headerGood (encNatList P.code) at hh
  simpa only [hh.1, hh.2.1, hh.2.2.1] using validate_data (encNatList P.code)

end ResourceScheduling.ChainProof.ReductionProgram

end

/- Complete checked body: ProgramSemantics -/
section

open ResourceScheduling.Graph ResourceScheduling.Chain

namespace ResourceScheduling.ChainProof

open ReductionProgram ReductionReg

theorem graph_word_eq_of_map (w : List Letter) (ns : List ℕ)
    (h : w.map alphabetEquiv.symm = encNats ns) : w = encNatList ns :=
  (List.map_injective_iff.mpr alphabetEquiv.symm.injective)
    (h.trans (alphabet_encNatList ns).symm)

private theorem opaque_seq_eval (p q : Code) (s : RAMState ReductionReg) :
    (p.seq q).eval s = q.eval (p.eval s) := rfl

theorem program_eval (s : RAMState ReductionReg) :
    program.eval s = if 0 < (validate.eval s).val ok then
      emitInstance.eval (validate.eval s) else validate.eval s := by
  rw [program, opaque_seq_eval]
  generalize validate.eval s = z
  rfl

theorem program_of_valid_code (P : ThreePartition) (hP : P.Valid) :
    (program.eval (initialRAM (encNatList P.code))).out.reverse =
      encNatList (Instance.decisionCode (P.chainInstance, 2 * P.t * P.b)) := by
  have hd := validate_encoded_data P hP
  have hk := validate_encoded_ok P hP
  have ho : (validate.eval (initialRAM (encNatList P.code))).out = [] :=
    validate_out (initialRAM (encNatList P.code))
  dsimp only at hd
  rw [program_eval]
  generalize hs : validate.eval (initialRAM (encNatList P.code)) = s at hd hk ho ⊢
  obtain ⟨hw, ht, hb, hp, hz, hone⟩ := hd
  rw [if_pos (by omega), emitInstance_out s P.t P.b (List.ofFn P.a) ht hb hp hz hone hw,
    ho, List.append_nil, List.reverse_reverse, emittedChainCode_eq P hP]

theorem program_semantics (w : List Letter) :
    ((program.eval (initialRAM w)).out.reverse).map alphabetEquiv.symm =
      chainReduction (w.map alphabetEquiv.symm) := by
  by_cases ha : 0 < (validate.eval (initialRAM w)).val ok
  · obtain ⟨P, hP, hcode⟩ := validate_accept_sound w ha
    have hw := graph_word_eq_of_map w P.code hcode
    rw [hw, program_of_valid_code P hP, alphabet_encNatList, alphabet_encNatList,
      chainReduction_valid P hP]
  · have ho : (program.eval (initialRAM w)).out.reverse = [] := by
      rw [program_eval, if_neg ha, validate_out]
      rfl
    rw [ho, List.map_nil]
    rcases chainReduction_spec (w.map alphabetEquiv.symm) with hf | ⟨P, hP, hcode, _⟩
    · exact hf.symm
    · have hw := graph_word_eq_of_map w P.code hcode
      have hk := validate_encoded_ok P hP
      exact (ha (by rw [hw, hk]; decide)).elim

end ResourceScheduling.ChainProof

end

/- Complete checked body: ChainPolytime -/
section

open CookPvsNP ResourceScheduling.Chain ResourceScheduling.Graph

namespace ResourceScheduling.ChainProof

theorem chainReduction_polytime : PolyTimeComputable chainReduction := by
  obtain ⟨C, k, hB⟩ := ReductionProgram.program_polynomial_bound
  have hG := polynomial_time_of_ram ReductionProgram.program ReductionProgram.program_valid C k hB
  have hU := polynomial_time_alphabet_equiv alphabetEquiv _ hG
  have he : (fun w : List USym =>
      ((ReductionProgram.program.eval (initialRAM (w.map alphabetEquiv))).out.reverse).map
        alphabetEquiv.symm) = chainReduction := by
    funext w
    simpa only [List.map_map, Function.comp_def, Equiv.symm_apply_apply, List.map_id'] using
      program_semantics (w.map alphabetEquiv)
  rwa [he] at hU

end ResourceScheduling.ChainProof

end

/- Complete checked body: SchedulingRoot -/
section

set_option autoImplicit false

namespace ResourceScheduling.Chain

theorem p2_res111_chain_stronglyNPHard
    (h3P : StronglyNPHard ThreePartition.code ThreePartition.IsYes) :
    StronglyNPHard Instance.decisionCode P2Res111Chain := by
  exact ResourceScheduling.ChainProof.chain_hardness_transfer
    ResourceScheduling.ChainProof.chainReduction_polytime h3P

end ResourceScheduling.Chain

end

open ResourceScheduling.Chain


theorem solution
    (h3P : StronglyNPHard ThreePartition.code ThreePartition.IsYes) :
    StronglyNPHard Instance.decisionCode P2Res111Chain := by
  exact ResourceScheduling.Chain.p2_res111_chain_stronglyNPHard h3P

#print axioms ResourceScheduling.Chain.p2_res111_chain_stronglyNPHard
#print axioms solution
