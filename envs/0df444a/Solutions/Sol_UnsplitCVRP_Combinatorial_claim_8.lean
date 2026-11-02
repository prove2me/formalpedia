-- Prove2me | solution 1 for UnsplitCVRP.Combinatorial.claim_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T06:13:35.874431+00:00
-- url     : https://prove2.me/submissions/be081b0a-706a-4515-9f85-14a1981cf40d

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_UnsplitCVRP_Combinatorial_Setting

namespace CVRPAux

open SupplyChainTheory UnsplitCVRP.Combinatorial

theorem finite_lists {α : Type} [Finite α] (m : ℕ) :
    {R : List (List α) | R.length ≤ m ∧ ∀ L ∈ R, L.length ≤ m}.Finite := by
  have hS' := List.finite_length_le α m
  have : Finite ↥{l : List α | l.length ≤ m} := hS'.to_subtype
  have hF := (List.finite_length_le (↥{l : List α | l.length ≤ m}) m).image
    (fun l => l.map Subtype.val)
  refine hF.subset ?_
  rintro R ⟨hRl, hR⟩
  lift R to List ↥{l : List α | l.length ≤ m} using hR
  exact ⟨R, by simpa using hRl, rfl⟩

theorem finite_sols {n : ℕ} :
    {R : List (List (Fin (n + 1))) | (∀ L ∈ R, L ≠ []) ∧ R.flatten.Nodup}.Finite := by
  refine (finite_lists (α := Fin (n + 1)) (n + 1)).subset ?_
  rintro R ⟨hne, hnd⟩
  have hlen : R.flatten.length ≤ n + 1 := by
    simpa using hnd.length_le_card
  refine ⟨?_, ?_⟩
  · have : R.length ≤ R.flatten.length := by
      rw [List.length_flatten]
      calc R.length = (R.map (fun _ => 1)).sum := by simp
        _ ≤ (R.map List.length).sum := by
          apply List.sum_le_sum
          intro L hL
          exact List.length_pos_iff.mpr (hne L hL)
    omega
  · intro L hL
    have : L.length ≤ R.flatten.length := by
      rw [List.length_flatten]
      exact List.le_sum_of_mem (List.mem_map_of_mem hL)
    omega

theorem sInf_attained {β : Type} (P : β → Prop) (f : β → ℝ)
    (hfin : {x | P x}.Finite) (hne : ∃ x, P x) :
    ∃ x, P x ∧ f x = sInf {t | ∃ x, P x ∧ t = f x} := by
  have hT : {t | ∃ x, P x ∧ t = f x} = f '' {x | P x} := by
    ext t; constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  obtain ⟨x0, hx0⟩ := hne
  have hmem := Set.Nonempty.csInf_mem (s := f '' {x | P x}) ⟨f x0, x0, hx0, rfl⟩
    (hfin.image f)
  rw [hT]
  obtain ⟨x, hx, hfx⟩ := hmem
  exact ⟨x, hx, hfx⟩

theorem sInf_le_of {β : Type} (P : β → Prop) (f : β → ℝ)
    (hfin : {x | P x}.Finite) (x : β) (hx : P x) :
    sInf {t | ∃ x, P x ∧ t = f x} ≤ f x := by
  have hT : {t | ∃ x, P x ∧ t = f x} = f '' {x | P x} := by
    ext t; constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  rw [hT]
  exact csInf_le (hfin.image f).bddBelow ⟨x, hx, rfl⟩

/-- Length of an open walk. -/
def pathLen {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) : List (Fin (n + 1)) → ℝ
  | x :: y :: t => c x y + pathLen c (y :: t)
  | _ => 0

theorem zip_sum_eq {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (b : Fin (n + 1)) :
    ∀ (l : List (Fin (n + 1))) (a : Fin (n + 1)),
      (List.zipWith c (a :: l) (l ++ [b])).sum = pathLen c (a :: l ++ [b])
  | [], a => by simp [pathLen]
  | h :: t, a => by
    have := zip_sum_eq c b t h
    simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons] at this ⊢
    rw [this]; rfl

theorem routeCost_eq {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (L : List (Fin (n + 1))) :
    routeCost c L = pathLen c (0 :: L ++ [0]) := by
  unfold routeCost closedLength
  rw [← zip_sum_eq]
  congr 2
  simp [List.rotate_cons_succ]

theorem pathLen_append {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (m : Fin (n + 1))
    (l' : List (Fin (n + 1))) :
    ∀ l : List (Fin (n + 1)), pathLen c (l ++ m :: l') = pathLen c (l ++ [m]) + pathLen c (m :: l')
  | [] => by simp [pathLen]
  | [x] => by simp [pathLen]
  | x :: y :: t => by
    have := pathLen_append c m l' (y :: t)
    simp only [List.cons_append] at this ⊢
    simp only [pathLen]
    rw [this]; ring

theorem pathLen_nonneg {n : ℕ} {c : Fin (n + 1) → Fin (n + 1) → ℝ} (hc : VRPMetric c) :
    ∀ l : List (Fin (n + 1)), 0 ≤ pathLen c l
  | [] => by simp [pathLen]
  | [x] => by simp [pathLen]
  | x :: y :: t => by
    simp only [pathLen]
    have := pathLen_nonneg hc (y :: t)
    linarith [hc.nonneg x y]

theorem routeCost_nonneg {n : ℕ} {c : Fin (n + 1) → Fin (n + 1) → ℝ} (hc : VRPMetric c)
    (L : List (Fin (n + 1))) : 0 ≤ routeCost c L := by
  rw [routeCost_eq]; exact pathLen_nonneg hc _

theorem solutionCost_nonneg {n : ℕ} {c : Fin (n + 1) → Fin (n + 1) → ℝ} (hc : VRPMetric c)
    (R : List (List (Fin (n + 1)))) : 0 ≤ solutionCost c R := by
  unfold solutionCost
  apply List.sum_nonneg
  intro x hx
  obtain ⟨L, _, rfl⟩ := List.mem_map.mp hx
  exact routeCost_nonneg hc L

theorem pathLen_drop1 {n : ℕ} {c : Fin (n + 1) → Fin (n + 1) → ℝ} (hc : VRPMetric c)
    (a x : Fin (n + 1)) (m : List (Fin (n + 1))) (hm : m ≠ []) :
    pathLen c (a :: m) ≤ pathLen c (a :: x :: m) := by
  obtain ⟨y, m', rfl⟩ := List.exists_cons_of_ne_nil hm
  simp only [pathLen]
  linarith [hc.triangle a y x]

/-- Shortcutting: deleting interior points does not increase walk length. -/
theorem pathLen_sublist {n : ℕ} {c : Fin (n + 1) → Fin (n + 1) → ℝ} (hc : VRPMetric c)
    (b : Fin (n + 1)) {l₁ l₂ : List (Fin (n + 1))} (h : l₁.Sublist l₂) :
    ∀ a : Fin (n + 1), pathLen c (a :: l₁ ++ [b]) ≤ pathLen c (a :: l₂ ++ [b]) := by
  induction h with
  | slnil => intro a; exact le_refl _
  | cons x h ih =>
    intro a
    refine (ih a).trans ?_
    simp only [List.cons_append]
    exact pathLen_drop1 hc a x _ (by simp)
  | cons_cons x h ih =>
    intro a
    simp only [List.cons_append, pathLen]
    have := ih x
    simp only [List.cons_append] at this
    linarith

theorem routeCost_sublist {n : ℕ} {c : Fin (n + 1) → Fin (n + 1) → ℝ} (hc : VRPMetric c)
    {l₁ l₂ : List (Fin (n + 1))} (h : l₁.Sublist l₂) : routeCost c l₁ ≤ routeCost c l₂ := by
  rw [routeCost_eq, routeCost_eq]; exact pathLen_sublist hc 0 h 0

theorem two_c_le_routeCost {n : ℕ} {c : Fin (n + 1) → Fin (n + 1) → ℝ} (hc : VRPMetric c)
    {L : List (Fin (n + 1))} {v : Fin (n + 1)} (hv : v ∈ L) : 2 * c 0 v ≤ routeCost c L := by
  have := routeCost_sublist hc (List.singleton_sublist.mpr hv)
  rw [routeCost_eq] at this
  simp [pathLen] at this
  linarith [hc.symm v 0]

theorem flatten_walk {n : ℕ} {c : Fin (n + 1) → Fin (n + 1) → ℝ} (hc : VRPMetric c) :
    ∀ R : List (List (Fin (n + 1))), routeCost c R.flatten ≤ solutionCost c R
  | [] => by simp [routeCost_eq, pathLen, solutionCost, hc.refl]
  | L :: R => by
    have ih := flatten_walk hc R
    have h1 : routeCost c (L ++ R.flatten) ≤ pathLen c (0 :: L ++ [0] ++ R.flatten ++ [0]) := by
      rw [routeCost_eq]
      have := pathLen_sublist hc 0 (l₁ := L ++ R.flatten) (l₂ := L ++ [0] ++ R.flatten)
        (by simp) 0
      simpa using this
    have h2 : pathLen c (0 :: L ++ [0] ++ R.flatten ++ [0]) =
        routeCost c L + routeCost c R.flatten := by
      rw [routeCost_eq, routeCost_eq]
      have := pathLen_append c 0 (R.flatten ++ [0]) (0 :: L)
      simpa using this
    simp only [List.flatten_cons, solutionCost, List.map_cons, List.sum_cons] at h1 h2 ih ⊢
    linarith

end CVRPAux

namespace CVRPAux
open SupplyChainTheory UnsplitCVRP.Combinatorial

/-- A tile endpoint lies in `(x, y]`. -/
def LatIn (δ θ x y : ℝ) : Prop := ∃ ℓ : ℕ, x < θ + (ℓ : ℝ) * (1 - δ) ∧ θ + (ℓ : ℝ) * (1 - δ) ≤ y

theorem latIn_exists {δ θ x : ℝ} (hL : 0 < 1 - δ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 - δ)
    (hx : 0 ≤ x) : LatIn δ θ x (x + (1 - δ)) := by
  by_cases hxθ : x < θ
  · exact ⟨0, by simpa using hxθ, by simp; linarith⟩
  · push_neg at hxθ
    set k := ⌊(x - θ) / (1 - δ)⌋₊ with hk
    have h1 : (k : ℝ) ≤ (x - θ) / (1 - δ) := Nat.floor_le (div_nonneg (by linarith) hL.le)
    have h2 : (x - θ) / (1 - δ) < k + 1 := Nat.lt_floor_add_one _
    rw [le_div_iff₀ hL] at h1
    rw [div_lt_iff₀ hL] at h2
    refine ⟨k + 1, ?_, ?_⟩ <;> push_cast <;> nlinarith

/-- An interval of length at least `1 - δ` starting at a nonnegative point contains an
endpoint. -/
theorem lt_of_not_latIn {δ θ x y : ℝ} (hL : 0 < 1 - δ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 - δ)
    (hx : 0 ≤ x) (h : ¬ LatIn δ θ x y) : y - x < 1 - δ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨ℓ, h1, h2⟩ := latIn_exists hL hθ0 hθ1 hx
  exact h ⟨ℓ, h1, by linarith⟩

theorem not_latIn_trans {δ θ x y z : ℝ} (h1 : ¬ LatIn δ θ x y) (h2 : ¬ LatIn δ θ y z) :
    ¬ LatIn δ θ x z := by
  rintro ⟨ℓ, ha, hb⟩
  by_cases hy : θ + (ℓ : ℝ) * (1 - δ) ≤ y
  · exact h1 ⟨ℓ, ha, hy⟩
  · exact h2 ⟨ℓ, lt_of_not_ge hy, hb⟩

/-- Added depot-edge cost of serving `a` with tank level `s`. -/
noncomputable def wAt {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (d : Fin (n + 1) → ℝ)
    (δ θ s : ℝ) (a : Fin (n + 1)) : ℝ := by
  classical
  exact (if LatIn δ θ s (s + d a) then 2 * c 0 a else 0) +
    (if δ < d a ∧ LatIn δ θ s (s + d a - δ) then 2 * c 0 a else 0)

noncomputable def addRec {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (d : Fin (n + 1) → ℝ)
    (δ θ : ℝ) : ℝ → List (Fin (n + 1)) → ℝ
  | _, [] => 0
  | s, a :: B => wAt c d δ θ s a + addRec c d δ θ (s + d a) B

theorem routeCost_cut_after {n : ℕ} {c : Fin (n + 1) → Fin (n + 1) → ℝ} (hc : VRPMetric c)
    (X Y : List (Fin (n + 1))) (a : Fin (n + 1)) :
    routeCost c (X ++ [a]) + routeCost c Y ≤ routeCost c (X ++ a :: Y) + 2 * c 0 a := by
  rw [routeCost_eq, routeCost_eq, routeCost_eq]
  have e1 := pathLen_append c a (Y ++ [0]) (0 :: X)
  have e2 := pathLen_append c a [0] (0 :: X)
  have e3 := pathLen_drop1 hc 0 a (Y ++ [0]) (by simp)
  simp only [List.cons_append, List.append_assoc, List.nil_append] at e1 e2 e3 ⊢
  rw [e1, e2]
  simp only [pathLen] at e3 ⊢
  linarith [hc.symm a 0]

theorem routeCost_cut_iso {n : ℕ} {c : Fin (n + 1) → Fin (n + 1) → ℝ} (hc : VRPMetric c)
    (X Y : List (Fin (n + 1))) (a : Fin (n + 1)) :
    routeCost c X + routeCost c [a] + routeCost c Y ≤
      routeCost c (X ++ a :: Y) + 4 * c 0 a := by
  have h1 := routeCost_cut_after hc X Y a
  have h2 : routeCost c X ≤ routeCost c (X ++ [a]) := routeCost_sublist hc (by simp)
  have h3 : routeCost c [a] = 2 * c 0 a := by
    simp [routeCost_eq, pathLen, hc.symm a 0]; ring
  linarith

theorem wAt_nonneg {n : ℕ} {c : Fin (n + 1) → Fin (n + 1) → ℝ} (hc : VRPMetric c)
    (d : Fin (n + 1) → ℝ) (δ θ s : ℝ) (a : Fin (n + 1)) : 0 ≤ wAt c d δ θ s a := by
  unfold wAt
  have := hc.nonneg 0 a
  split_ifs <;> linarith

theorem load_append_single {n : ℕ} (d : Fin (n + 1) → ℝ) (cur : List (Fin (n + 1)))
    (a : Fin (n + 1)) : load d (cur ++ [a]) = load d cur + d a := by
  simp [load, List.map_append, List.sum_append]

theorem routeCost_nil {n : ℕ} {c : Fin (n + 1) → Fin (n + 1) → ℝ} (hc : VRPMetric c) :
    routeCost c [] = 0 := by
  simp [routeCost_eq, pathLen, hc.refl]

/-- The tank construction for a fixed offset `θ` (proof of Lemma 7). -/
theorem tank_split {n : ℕ} {c : Fin (n + 1) → Fin (n + 1) → ℝ} (hc : VRPMetric c)
    {d : Fin (n + 1) → ℝ} {δ θ : ℝ} (hδ0 : 0 ≤ δ) (hL : 0 < 1 - δ) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1 - δ) :
    ∀ (B : List (Fin (n + 1))), (∀ a ∈ B, 0 ≤ d a ∧ d a ≤ 1) →
    ∀ (cur : List (Fin (n + 1))) (s0 s : ℝ), 0 ≤ s0 → s0 ≤ s → load d cur = s - s0 →
      ¬ LatIn δ θ s0 s →
      ∃ R, IsConsecutiveSplit d (cur ++ B) R ∧
        solutionCost c R ≤ routeCost c (cur ++ B) + addRec c d δ θ s B := by
  intro B
  induction B with
  | nil =>
    intro _ cur s0 s hs0 _ hload hlat
    have hlt := lt_of_not_latIn hL hθ0 hθ1 hs0 hlat
    by_cases hcur : cur = []
    · subst hcur
      refine ⟨[], ⟨rfl, by simp⟩, ?_⟩
      simp [solutionCost, addRec, routeCost_nil hc]
    · refine ⟨[cur], ⟨by simp, ?_⟩, ?_⟩
      · intro L hL'
        rw [List.mem_singleton] at hL'
        subst hL'
        exact ⟨hcur, by linarith⟩
      · simp [solutionCost, addRec]
  | cons a B ih =>
    intro hB cur s0 s hs0 hss hload hlat
    have hB' : ∀ b ∈ B, 0 ≤ d b ∧ d b ≤ 1 := fun b hb => hB b (List.mem_cons_of_mem _ hb)
    have ha := hB a List.mem_cons_self
    have hempty : ¬ LatIn δ θ (s + d a) (s + d a) := by
      rintro ⟨ℓ, h1, h2⟩; linarith
    have hcl := lt_of_not_latIn hL hθ0 hθ1 hs0 hlat
    by_cases hbad : LatIn δ θ s (s + d a)
    · obtain ⟨R', hR', hcR'⟩ := ih hB' [] (s + d a) (s + d a) (by linarith) le_rfl
        (by simp [load]) hempty
      simp only [List.nil_append] at hR' hcR'
      by_cases hfour : δ < d a ∧ LatIn δ θ s (s + d a - δ)
      · have hw : wAt c d δ θ s a = 4 * c 0 a := by
          unfold wAt; rw [if_pos hbad, if_pos hfour]; ring
        have hiso := routeCost_cut_iso hc cur B a
        by_cases hcur : cur = []
        · subst hcur
          refine ⟨[a] :: R', ⟨?_, ?_⟩, ?_⟩
          · simp [hR'.1]
          · intro L hL'
            rcases List.mem_cons.mp hL' with rfl | hL'
            · exact ⟨by simp, by simp [load]; exact ha.2⟩
            · exact hR'.2 L hL'
          · simp only [solutionCost, List.map_cons, List.sum_cons, addRec] at hcR' ⊢
            rw [hw]
            rw [routeCost_nil hc] at hiso
            simp only [List.nil_append] at hiso ⊢
            linarith [hc.nonneg 0 a]
        · refine ⟨cur :: [a] :: R', ⟨?_, ?_⟩, ?_⟩
          · simp [hR'.1]
          · intro L hL'
            rcases List.mem_cons.mp hL' with rfl | hL'
            · exact ⟨hcur, by linarith⟩
            rcases List.mem_cons.mp hL' with rfl | hL'
            · exact ⟨by simp, by simp [load]; exact ha.2⟩
            · exact hR'.2 L hL'
          · simp only [solutionCost, List.map_cons, List.sum_cons, addRec] at hcR' ⊢
            rw [hw]
            linarith
      · have hw : wAt c d δ θ s a = 2 * c 0 a := by
          unfold wAt; rw [if_pos hbad, if_neg hfour]; ring
        have hcap : load d (cur ++ [a]) ≤ 1 := by
          rw [load_append_single, hload]
          by_contra hcon
          push_neg at hcon
          obtain ⟨ℓ, h1, h2⟩ := latIn_exists hL hθ0 hθ1 hs0
          by_cases he : θ + (ℓ : ℝ) * (1 - δ) ≤ s
          · exact hlat ⟨ℓ, h1, he⟩
          · push_neg at he
            by_cases hbig : δ < d a
            · exact hfour ⟨hbig, ℓ, he, by linarith⟩
            · push_neg at hbig
              linarith
        refine ⟨(cur ++ [a]) :: R', ⟨?_, ?_⟩, ?_⟩
        · simp [hR'.1]
        · intro L hL'
          rcases List.mem_cons.mp hL' with rfl | hL'
          · exact ⟨by simp, hcap⟩
          · exact hR'.2 L hL'
        · have hcut := routeCost_cut_after hc cur B a
          simp only [solutionCost, List.map_cons, List.sum_cons, addRec] at hcR' ⊢
          rw [hw]
          linarith
    · obtain ⟨R, hR, hcR⟩ := ih hB' (cur ++ [a]) s0 (s + d a) hs0 (by linarith)
        (by rw [load_append_single, hload]; ring) (not_latIn_trans hlat hbad)
      have heq : cur ++ [a] ++ B = cur ++ a :: B := by simp
      rw [heq] at hR hcR
      refine ⟨R, hR, ?_⟩
      have := wAt_nonneg hc d δ θ s a
      simp only [addRec]
      linarith

theorem prefixLoad_cons_succ {n : ℕ} (d : Fin (n + 1) → ℝ) (a : Fin (n + 1))
    (B : List (Fin (n + 1))) (i : ℕ) :
    prefixLoad d (a :: B) (i + 1) = d a + prefixLoad d B i := by
  simp [prefixLoad, load]

open Classical in
theorem addRec_eq_sum {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (d : Fin (n + 1) → ℝ)
    (δ θ : ℝ) : ∀ (B : List (Fin (n + 1))) (s : ℝ),
    addRec c d δ θ s B = ∑ i ∈ Finset.range B.length,
      ((if LatIn δ θ (s + prefixLoad d B i) (s + prefixLoad d B (i + 1))
        then 2 * c 0 (B.getD i 0) else 0) +
       (if δ < d (B.getD i 0) ∧
          LatIn δ θ (s + prefixLoad d B i) (s + prefixLoad d B (i + 1) - δ)
        then 2 * c 0 (B.getD i 0) else 0))
  | [], s => by simp [addRec]
  | a :: B, s => by
    rw [List.length_cons, Finset.sum_range_succ', addRec, addRec_eq_sum c d δ θ B (s + d a)]
    rw [add_comm]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      simp only [prefixLoad_cons_succ, List.getD_cons_succ, ← add_assoc]
    · simp [wAt, prefixLoad, load]

open Classical in
theorem addRec_zero {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (d : Fin (n + 1) → ℝ)
    (δ θ : ℝ) (A : List (Fin (n + 1))) :
    addRec c d δ θ 0 A = addedCost c d δ A θ := by
  rw [addRec_eq_sum]
  unfold addedCost IsBad IsFourCopies LatIn
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  · exact if_congr (by simp only [zero_add]) rfl rfl
  · exact if_congr (by simp only [zero_add]) rfl rfl

end CVRPAux

namespace CVRPAux
open SupplyChainTheory UnsplitCVRP.Combinatorial MeasureTheory

/-- The set of offsets for which a tile endpoint lands in `(x, y]`. -/
def latSet (δ x y : ℝ) : Set ℝ := ⋃ ℓ : ℕ, Set.Ioc (x - (ℓ : ℝ) * (1 - δ)) (y - (ℓ : ℝ) * (1 - δ))

theorem mem_latSet {δ θ x y : ℝ} : θ ∈ latSet δ x y ↔ LatIn δ θ x y := by
  unfold latSet LatIn
  simp only [Set.mem_iUnion, Set.mem_Ioc]
  constructor
  · rintro ⟨ℓ, h1, h2⟩; exact ⟨ℓ, by linarith, by linarith⟩
  · rintro ⟨ℓ, h1, h2⟩; exact ⟨ℓ, by linarith, by linarith⟩

theorem measurableSet_latSet (δ x y : ℝ) : MeasurableSet (latSet δ x y) :=
  MeasurableSet.iUnion (fun _ => measurableSet_Ioc)

/-- The offsets in `[0, L]` whose tiling has an endpoint in `(a, b]` have measure at most
`b - a` (Claims 8 and 9, upper bound). -/
theorem volume_latSet_le {δ a b : ℝ} (hL : 0 < 1 - δ) (ha : 0 ≤ a) :
    volume (latSet δ a b ∩ Set.Icc 0 (1 - δ)) ≤ ENNReal.ofReal (b - a) := by
  set L := 1 - δ with hLdef
  by_cases hbig : L ≤ b - a
  · calc volume (latSet δ a b ∩ Set.Icc 0 L) ≤ volume (Set.Icc (0 : ℝ) L) :=
          measure_mono Set.inter_subset_right
      _ = ENNReal.ofReal (L - 0) := Real.volume_Icc
      _ ≤ ENNReal.ofReal (b - a) := ENNReal.ofReal_le_ofReal (by linarith)
  push_neg at hbig
  set k := ⌊a / L⌋₊ with hk
  have h1 : (k : ℝ) ≤ a / L := Nat.floor_le (div_nonneg ha hL.le)
  have h2 : a / L < k + 1 := Nat.lt_floor_add_one _
  rw [le_div_iff₀ hL] at h1
  rw [div_lt_iff₀ hL] at h2
  have hsub : latSet δ a b ∩ Set.Icc 0 L ⊆
      Set.Ioc (a - k * L) (min (b - k * L) L) ∪ Set.Icc 0 (b - (k + 1) * L) := by
    rintro θ ⟨hθ, hθ0, hθ1⟩
    simp only [latSet, Set.mem_iUnion, Set.mem_Ioc] at hθ
    obtain ⟨ℓ, hl1, hl2⟩ := hθ
    have hkl : k < ℓ + 1 := by
      have : (k : ℝ) * L < ((ℓ : ℝ) + 1) * L := by nlinarith
      have := (mul_lt_mul_iff_left₀ hL).mp this
      exact_mod_cast this
    have hlk : ℓ < k + 2 := by
      have : (ℓ : ℝ) * L < ((k : ℝ) + 2) * L := by nlinarith
      have := (mul_lt_mul_iff_left₀ hL).mp this
      exact_mod_cast this
    have : ℓ = k ∨ ℓ = k + 1 := by omega
    rcases this with rfl | rfl
    · left; exact ⟨hl1, le_min hl2 hθ1⟩
    · right; push_cast at hl2; exact ⟨hθ0, hl2⟩
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [Real.volume_Ioc, Real.volume_Icc]
  by_cases hb : b - k * L ≤ L
  · rw [min_eq_left hb, ENNReal.ofReal_of_nonpos (p := b - (k + 1) * L - 0) (by linarith),
      add_zero]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · push_neg at hb
    rw [min_eq_right hb.le, ← ENNReal.ofReal_add (by linarith) (by linarith)]
    exact ENNReal.ofReal_le_ofReal (by linarith)

theorem prefixLoad_succ {n : ℕ} (d : Fin (n + 1) → ℝ) :
    ∀ (A : List (Fin (n + 1))) (i : ℕ), i < A.length →
      prefixLoad d A (i + 1) = prefixLoad d A i + d (A.getD i 0)
  | [], i, h => absurd h (by simp)
  | a :: B, 0, _ => by simp [prefixLoad, load]
  | a :: B, i + 1, h => by
    rw [prefixLoad_cons_succ, prefixLoad_cons_succ, prefixLoad_succ d B i (by simpa using h)]
    simp only [List.getD_cons_succ]
    ring

theorem prefixLoad_nonneg {n : ℕ} (d : Fin (n + 1) → ℝ) (A : List (Fin (n + 1)))
    (hA : ∀ a ∈ A, 0 ≤ d a) (i : ℕ) : 0 ≤ prefixLoad d A i := by
  unfold prefixLoad load
  apply List.sum_nonneg
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  exact hA a (List.mem_of_mem_take ha)

theorem sum_range_getD {n : ℕ} (h : Fin (n + 1) → ℝ) :
    ∀ A : List (Fin (n + 1)), ∑ i ∈ Finset.range A.length, h (A.getD i 0) = (A.map h).sum
  | [] => by simp
  | a :: B => by
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.sum_cons]
    rw [sum_range_getD h B]
    ring

theorem getD_mem {n : ℕ} (A : List (Fin (n + 1))) (i : ℕ) (hi : i ∈ Finset.range A.length) :
    A.getD i 0 ∈ A := by
  rw [Finset.mem_range] at hi
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

open Classical in
theorem term_eq {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (hc : VRPMetric c)
    (d : Fin (n + 1) → ℝ) (δ : ℝ) (A : List (Fin (n + 1))) (i : ℕ) (θ : ℝ) :
    ENNReal.ofReal ((if IsBad d δ A i θ then 2 * c 0 (A.getD i 0) else 0) +
      (if δ < d (A.getD i 0) ∧ IsFourCopies d δ A i θ then 2 * c 0 (A.getD i 0) else 0)) =
    ENNReal.ofReal (2 * c 0 (A.getD i 0)) *
        (latSet δ (prefixLoad d A i) (prefixLoad d A (i + 1))).indicator 1 θ +
      ENNReal.ofReal (if δ < d (A.getD i 0) then 2 * c 0 (A.getD i 0) else 0) *
        (latSet δ (prefixLoad d A i) (prefixLoad d A (i + 1) - δ)).indicator 1 θ := by
  have h0 : 0 ≤ 2 * c 0 (A.getD i 0) := by linarith [hc.nonneg 0 (A.getD i 0)]
  have e1 : ENNReal.ofReal (if IsBad d δ A i θ then 2 * c 0 (A.getD i 0) else 0) =
      ENNReal.ofReal (2 * c 0 (A.getD i 0)) *
        (latSet δ (prefixLoad d A i) (prefixLoad d A (i + 1))).indicator 1 θ := by
    by_cases hb : IsBad d δ A i θ
    · have hm : θ ∈ latSet δ (prefixLoad d A i) (prefixLoad d A (i + 1)) := mem_latSet.mpr hb
      rw [if_pos hb, Set.indicator_of_mem hm]; simp
    · have hm : θ ∉ latSet δ (prefixLoad d A i) (prefixLoad d A (i + 1)) :=
        fun h => hb (mem_latSet.mp h)
      rw [if_neg hb, Set.indicator_of_notMem hm]; simp
  have e2 : ENNReal.ofReal
        (if δ < d (A.getD i 0) ∧ IsFourCopies d δ A i θ then 2 * c 0 (A.getD i 0) else 0) =
      ENNReal.ofReal (if δ < d (A.getD i 0) then 2 * c 0 (A.getD i 0) else 0) *
        (latSet δ (prefixLoad d A i) (prefixLoad d A (i + 1) - δ)).indicator 1 θ := by
    by_cases hbig : δ < d (A.getD i 0)
    · by_cases hf : IsFourCopies d δ A i θ
      · have hm : θ ∈ latSet δ (prefixLoad d A i) (prefixLoad d A (i + 1) - δ) :=
          mem_latSet.mpr hf
        rw [if_pos ⟨hbig, hf⟩, if_pos hbig, Set.indicator_of_mem hm]; simp
      · have hm : θ ∉ latSet δ (prefixLoad d A i) (prefixLoad d A (i + 1) - δ) :=
          fun h => hf (mem_latSet.mp h)
        rw [if_neg (fun h => hf h.2), Set.indicator_of_notMem hm]; simp
    · rw [if_neg (fun h => hbig h.1), if_neg hbig]; simp
  rw [ENNReal.ofReal_add (by split_ifs <;> linarith) (by split_ifs <;> linarith), e1, e2]

open Classical in
/-- Averaging over the offset (expected-cost argument of Lemma 7). -/
theorem exists_good_theta {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (hc : VRPMetric c)
    (d : Fin (n + 1) → ℝ) (δ : ℝ) (hL : 0 < 1 - δ)
    (A : List (Fin (n + 1))) (hA : ∀ a ∈ A, 0 ≤ d a) :
    ∃ θ ∈ Set.Icc 0 (1 - δ), addedCost c d δ A θ ≤
      (∑ i ∈ Finset.range A.length,
        (2 * c 0 (A.getD i 0) * d (A.getD i 0) +
          (if δ < d (A.getD i 0) then 2 * c 0 (A.getD i 0) * (d (A.getD i 0) - δ) else 0)))
        / (1 - δ) := by
  have hmeas : ∀ i, Measurable (fun θ : ℝ =>
      ENNReal.ofReal (2 * c 0 (A.getD i 0)) *
        (latSet δ (prefixLoad d A i) (prefixLoad d A (i + 1))).indicator 1 θ +
      ENNReal.ofReal (if δ < d (A.getD i 0) then 2 * c 0 (A.getD i 0) else 0) *
        (latSet δ (prefixLoad d A i) (prefixLoad d A (i + 1) - δ)).indicator 1 θ) := by
    intro i
    exact ((measurable_one.indicator (measurableSet_latSet _ _ _)).const_mul _).add
      ((measurable_one.indicator (measurableSet_latSet _ _ _)).const_mul _)
  have hFeq : ∀ θ, ENNReal.ofReal (addedCost c d δ A θ) =
      ∑ i ∈ Finset.range A.length,
        (ENNReal.ofReal (2 * c 0 (A.getD i 0)) *
          (latSet δ (prefixLoad d A i) (prefixLoad d A (i + 1))).indicator 1 θ +
        ENNReal.ofReal (if δ < d (A.getD i 0) then 2 * c 0 (A.getD i 0) else 0) *
          (latSet δ (prefixLoad d A i) (prefixLoad d A (i + 1) - δ)).indicator 1 θ) := by
    intro θ
    unfold addedCost
    rw [ENNReal.ofReal_sum_of_nonneg]
    · exact Finset.sum_congr rfl (fun i _ => term_eq c hc d δ A i θ)
    · intro i _
      have := hc.nonneg 0 (A.getD i 0)
      split_ifs <;> linarith
  have hFm : Measurable (fun θ => ENNReal.ofReal (addedCost c d δ A θ)) := by
    simp_rw [hFeq]
    exact Finset.measurable_sum _ (fun i _ => hmeas i)
  have hvol : volume (Set.Icc (0 : ℝ) (1 - δ)) = ENNReal.ofReal (1 - δ) := by
    rw [Real.volume_Icc, sub_zero]
  obtain ⟨θ, hθ, hle⟩ := exists_le_setLAverage (μ := volume) (s := Set.Icc (0 : ℝ) (1 - δ))
    (f := fun θ => ENNReal.ofReal (addedCost c d δ A θ))
    (by rw [hvol]; exact ENNReal.ofReal_ne_zero_iff.mpr hL) (by rw [hvol]; simp)
    hFm.aemeasurable
  refine ⟨θ, hθ, ?_⟩
  set K := ∑ i ∈ Finset.range A.length,
        (2 * c 0 (A.getD i 0) * d (A.getD i 0) +
          (if δ < d (A.getD i 0) then 2 * c 0 (A.getD i 0) * (d (A.getD i 0) - δ) else 0))
    with hK
  have hK0 : 0 ≤ K := by
    apply Finset.sum_nonneg
    intro i hi
    have := hc.nonneg 0 (A.getD i 0)
    have := hA _ (getD_mem A i hi)
    split_ifs with h
    · nlinarith
    · nlinarith
  have hint : ∫⁻ x in Set.Icc 0 (1 - δ), ENNReal.ofReal (addedCost c d δ A x) ≤
      ENNReal.ofReal K := by
    simp_rw [hFeq]
    rw [lintegral_finset_sum _ (fun i _ => hmeas i)]
    rw [hK, ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_le_sum
      intro i hi
      have hd0 := hA _ (getD_mem A i hi)
      have hc0 := hc.nonneg 0 (A.getD i 0)
      have hPi : prefixLoad d A (i + 1) = prefixLoad d A i + d (A.getD i 0) :=
        prefixLoad_succ d A i (Finset.mem_range.mp hi)
      have hP0 := prefixLoad_nonneg d A hA i
      rw [lintegral_add_left ((measurable_one.indicator (measurableSet_latSet _ _ _)).const_mul _),
        lintegral_const_mul _ (measurable_one.indicator (measurableSet_latSet _ _ _)),
        lintegral_const_mul _ (measurable_one.indicator (measurableSet_latSet _ _ _)),
        lintegral_indicator_one (measurableSet_latSet _ _ _),
        lintegral_indicator_one (measurableSet_latSet _ _ _),
        Measure.restrict_apply (measurableSet_latSet _ _ _),
        Measure.restrict_apply (measurableSet_latSet _ _ _)]
      have v1 := volume_latSet_le (a := prefixLoad d A i) (b := prefixLoad d A (i + 1)) hL hP0
      have v2 := volume_latSet_le (a := prefixLoad d A i) (b := prefixLoad d A (i + 1) - δ)
        hL hP0
      rw [hPi] at v1 v2
      have v1' : prefixLoad d A i + d (A.getD i 0) - prefixLoad d A i = d (A.getD i 0) := by ring
      have v2' : prefixLoad d A i + d (A.getD i 0) - δ - prefixLoad d A i =
        d (A.getD i 0) - δ := by ring
      rw [v1'] at v1
      rw [v2'] at v2
      rw [hPi]
      calc ENNReal.ofReal (2 * c 0 (A.getD i 0)) *
            volume (latSet δ (prefixLoad d A i) (prefixLoad d A i + d (A.getD i 0)) ∩
              Set.Icc 0 (1 - δ)) +
          ENNReal.ofReal (if δ < d (A.getD i 0) then 2 * c 0 (A.getD i 0) else 0) *
            volume (latSet δ (prefixLoad d A i) (prefixLoad d A i + d (A.getD i 0) - δ) ∩
              Set.Icc 0 (1 - δ))
          ≤ ENNReal.ofReal (2 * c 0 (A.getD i 0)) * ENNReal.ofReal (d (A.getD i 0)) +
            ENNReal.ofReal (if δ < d (A.getD i 0) then 2 * c 0 (A.getD i 0) else 0) *
              ENNReal.ofReal (d (A.getD i 0) - δ) := by gcongr
        _ = ENNReal.ofReal (2 * c 0 (A.getD i 0) * d (A.getD i 0) +
          (if δ < d (A.getD i 0) then 2 * c 0 (A.getD i 0) * (d (A.getD i 0) - δ) else 0)) := by
            split_ifs with h
            · rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by linarith),
                ← ENNReal.ofReal_add (by nlinarith) (by nlinarith)]
            · rw [← ENNReal.ofReal_mul (by linarith)]; simp
    · intro i hi
      have := hc.nonneg 0 (A.getD i 0)
      have := hA _ (getD_mem A i hi)
      split_ifs with h
      · nlinarith
      · nlinarith
  rw [setLAverage_eq, hvol] at hle
  have hle2 : ENNReal.ofReal (addedCost c d δ A θ) ≤ ENNReal.ofReal (K / (1 - δ)) := by
    rw [ENNReal.ofReal_div_of_pos hL]
    exact hle.trans (ENNReal.div_le_div_right hint _)
  exact (ENNReal.ofReal_le_ofReal_iff (div_nonneg hK0 hL.le)).mp hle2

end CVRPAux

namespace CVRPAux
open SupplyChainTheory UnsplitCVRP.Combinatorial MeasureTheory

/-- Exact measure of the offsets whose tiling meets `(a, b]`. -/
theorem volume_latSet_eq {δ a b : ℝ} (hL : 0 < 1 - δ) (ha : 0 ≤ a) (hab : a ≤ b) :
    volume (latSet δ a b ∩ Set.Icc 0 (1 - δ)) = ENNReal.ofReal (min (1 - δ) (b - a)) := by
  set L := 1 - δ with hLdef
  by_cases hbig : L ≤ b - a
  · rw [min_eq_left hbig]
    apply le_antisymm
    · calc volume (latSet δ a b ∩ Set.Icc 0 L) ≤ volume (Set.Icc (0 : ℝ) L) :=
            measure_mono Set.inter_subset_right
        _ = ENNReal.ofReal L := by rw [Real.volume_Icc, sub_zero]
    · have hsub : Set.Icc (0 : ℝ) L ⊆ latSet δ a b ∩ Set.Icc 0 L := by
        intro θ hθ
        refine ⟨?_, hθ⟩
        obtain ⟨ℓ, h1, h2⟩ := latIn_exists hL hθ.1 hθ.2 ha
        exact mem_latSet.mpr ⟨ℓ, h1, by linarith⟩
      calc ENNReal.ofReal L = volume (Set.Icc (0 : ℝ) L) := by rw [Real.volume_Icc, sub_zero]
        _ ≤ _ := measure_mono hsub
  push_neg at hbig
  rw [min_eq_right hbig.le]
  apply le_antisymm (volume_latSet_le hL ha)
  set k := ⌊a / L⌋₊ with hk
  have h1 : (k : ℝ) ≤ a / L := Nat.floor_le (div_nonneg ha hL.le)
  have h2 : a / L < k + 1 := Nat.lt_floor_add_one _
  rw [le_div_iff₀ hL] at h1
  rw [div_lt_iff₀ hL] at h2
  have hsub : Set.Ioc (a - k * L) (min (b - k * L) L) ∪ Set.Icc 0 (b - (k + 1) * L) ⊆
      latSet δ a b ∩ Set.Icc 0 L := by
    rintro θ (⟨hθ1, hθ2⟩ | ⟨hθ1, hθ2⟩)
    · have := min_le_left (b - k * L) L
      have := min_le_right (b - k * L) L
      refine ⟨?_, by constructor <;> linarith⟩
      simp only [latSet, Set.mem_iUnion, Set.mem_Ioc]
      exact ⟨k, hθ1, by linarith⟩
    · refine ⟨?_, by constructor <;> nlinarith⟩
      simp only [latSet, Set.mem_iUnion, Set.mem_Ioc]
      exact ⟨k + 1, by push_cast; nlinarith, by push_cast; linarith⟩
  have hdisj : Disjoint (Set.Ioc (a - k * L) (min (b - k * L) L)) (Set.Icc 0 (b - (k + 1) * L)) := by
    rw [Set.disjoint_left]
    rintro θ ⟨hθ1, _⟩ ⟨_, hθ4⟩
    linarith
  refine le_trans ?_ (measure_mono hsub)
  rw [measure_union hdisj measurableSet_Icc, Real.volume_Ioc, Real.volume_Icc]
  by_cases hb : b - k * L ≤ L
  · rw [min_eq_left hb, ENNReal.ofReal_of_nonpos (p := b - (k + 1) * L - 0) (by linarith),
      add_zero]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · push_neg at hb
    rw [min_eq_right hb.le, ← ENNReal.ofReal_add (by linarith) (by linarith)]
    exact ENNReal.ofReal_le_ofReal (by linarith)

theorem claim_set_eq {n : ℕ} (d : Fin (n + 1) → ℝ) (δ : ℝ) (A : List (Fin (n + 1))) (i : ℕ) :
    {θ : ℝ | θ ∈ Set.Icc 0 (1 - δ) ∧ IsBad d δ A i θ} =
      latSet δ (prefixLoad d A i) (prefixLoad d A (i + 1)) ∩ Set.Icc 0 (1 - δ) := by
  ext θ
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [mem_latSet]
  exact and_comm

theorem claim_set_eq' {n : ℕ} (d : Fin (n + 1) → ℝ) (δ : ℝ) (A : List (Fin (n + 1))) (i : ℕ) :
    {θ : ℝ | θ ∈ Set.Icc 0 (1 - δ) ∧ IsFourCopies d δ A i θ} =
      latSet δ (prefixLoad d A i) (prefixLoad d A (i + 1) - δ) ∩ Set.Icc 0 (1 - δ) := by
  ext θ
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [mem_latSet]
  exact and_comm

end CVRPAux

open SupplyChainTheory UnsplitCVRP.Combinatorial CVRPAux in
theorem solution {n : ℕ} (d : Fin (n + 1) → ℝ) (hd : Demands d)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2)
    (A : List (Fin (n + 1))) (hAn : A.Nodup)
    (hA : (0 : Fin (n + 1)) ∉ A)
    (i : ℕ) (hi : i < A.length) :
    (MeasureTheory.volume {θ : ℝ | θ ∈ Set.Icc 0 (1 - δ) ∧ IsBad d δ A i θ}).toReal /
        (1 - δ) =
      min 1 (d (A.getD i 0) / (1 - δ)) := by
  have hL : 0 < 1 - δ := by linarith
  have hA0 : ∀ a ∈ A, 0 ≤ d a := fun a ha => (hd a (by rintro rfl; exact hA ha)).1.le
  have hd0 := hA0 _ (getD_mem A i (Finset.mem_range.mpr hi))
  have hP := prefixLoad_nonneg d A hA0 i
  rw [claim_set_eq, prefixLoad_succ d A i hi, volume_latSet_eq hL hP (by linarith),
    ENNReal.toReal_ofReal (le_min hL.le (by linarith)),
    show prefixLoad d A i + d (A.getD i 0) - prefixLoad d A i = d (A.getD i 0) by ring,
    ← min_div_div_right hL.le, div_self hL.ne']
