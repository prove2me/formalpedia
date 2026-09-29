-- Prove2me | solution 1 for ResourceScheduling.Chain.chainSchedule_of_threePartition
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:22:06.070258+00:00
-- url     : https://prove2.me/submissions/845ded84-34e8-4cfb-b055-4910b2d88930

import Mathlib
import Definitions.Def_ResourceScheduling_Chain_Constructions

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
      simp only [List.map_map, List.mem_map, List.mem_range, Function.comp] at hx
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
    (hs : P.IsSolution s) (j : Fin (3 * P.t)) (c : ℕ) (hc : c + 1 < 2 * P.a j) :
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

theorem solution (P : ThreePartition) (hP : P.Valid)
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
      simp only [Option.some.injEq, Prod.mk.injEq] at hfin
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
