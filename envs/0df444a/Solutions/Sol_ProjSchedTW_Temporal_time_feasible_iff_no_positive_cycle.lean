-- Prove2me | solution 1 for ProjSchedTW.Temporal.time_feasible_iff_no_positive_cycle
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T13:36:02.677632+00:00
-- url     : https://prove2.me/submissions/d461cb5c-ce4e-4e44-becd-90881f6da68e

/-
Bellman/Ford: a project network admits a time-feasible schedule iff it has no cycle of positive
length (Theorem 1.3.3 of Neumann, Schwindt and Zimmermann, Project Scheduling with Time Windows and
Scarce Resources).

(⇒) Summing the arc constraints `δ_ij ≤ S_j - S_i` around a cycle telescopes to `length ≤ 0`.
(⇐) Put `S_i` = the length of a longest path from node 0 to `i`. Without positive cycles every
walk is dominated by a path with the same ends (cut out the first closed segment), which gives
`S_j ≥ S_i + δ_ij` for each arc; the standing assumption gives `S_i ≥ 0`, and `S_0 = 0`.
-/
import Mathlib
import Definitions.Def_ProjSchedTW_Temporal_Project

set_option autoImplicit false

namespace TfAux

open ProjSchedTW.Temporal

variable {n : ℕ}

/-- Walks indexed by `ℕ`: nodes `w 0, …, w m`, arcs `(w k, w (k+1))` for `k < m`. -/
def NWalk (N : Network n) (m : ℕ) (w : ℕ → Fin (n + 2)) : Prop :=
  ∀ k, k < m → (w k, w (k + 1)) ∈ N.E

def nlen (N : Network n) (m : ℕ) (w : ℕ → Fin (n + 2)) : ℤ :=
  ∑ k ∈ Finset.range m, N.δ (w k) (w (k + 1))

def NPath (N : Network n) (m : ℕ) (w : ℕ → Fin (n + 2)) : Prop :=
  NWalk N m w ∧ ∀ a b, a ≤ m → b ≤ m → w a = w b → a = b

def NCycle (N : Network n) (m : ℕ) (w : ℕ → Fin (n + 2)) : Prop :=
  NWalk N m w ∧ 0 < m ∧ w 0 = w m ∧ ∀ a b, a < m → b < m → w a = w b → a = b

/-- Extension of a `Fin`-indexed sequence to `ℕ`. -/
def ext {m : ℕ} (w : Fin (m + 1) → Fin (n + 2)) : ℕ → Fin (n + 2) :=
  fun k => if h : k < m + 1 then w ⟨k, h⟩ else w 0

theorem ext_apply {m : ℕ} (w : Fin (m + 1) → Fin (n + 2)) (k : Fin (m + 1)) :
    ext w k.val = w k := by
  simp [ext, k.2]

theorem ext_zero {m : ℕ} (w : Fin (m + 1) → Fin (n + 2)) : ext w 0 = w 0 := by
  simpa using ext_apply w 0

theorem ext_last {m : ℕ} (w : Fin (m + 1) → Fin (n + 2)) : ext w m = w (Fin.last m) := by
  simpa using ext_apply w (Fin.last m)

theorem walk_of_fin {N : Network n} {m : ℕ} {w : Fin (m + 1) → Fin (n + 2)} (h : IsWalk N w) :
    NWalk N m (ext w) := by
  intro k hk
  have := h ⟨k, hk⟩
  have e1 : ext w k = w (Fin.castSucc ⟨k, hk⟩) := ext_apply w (Fin.castSucc ⟨k, hk⟩)
  have e2 : ext w (k + 1) = w (Fin.succ ⟨k, hk⟩) := ext_apply w (Fin.succ ⟨k, hk⟩)
  rw [e1, e2]
  exact this

theorem walkLength_eq {N : Network n} {m : ℕ} (w : Fin (m + 1) → Fin (n + 2)) :
    walkLength N w = nlen N m (ext w) := by
  unfold walkLength nlen
  rw [← Fin.sum_univ_eq_sum_range (fun k => N.δ (ext w k) (ext w (k + 1))) m]
  apply Finset.sum_congr rfl
  intro k _
  have e1 : ext w k.val = w k.castSucc := ext_apply w k.castSucc
  have e2 : ext w (k.val + 1) = w k.succ := ext_apply w k.succ
  rw [e1, e2]

theorem npath_of_fin {N : Network n} {m : ℕ} {w : Fin (m + 1) → Fin (n + 2)} (h : IsPath N w) :
    NPath N m (ext w) := by
  refine ⟨walk_of_fin h.1, ?_⟩
  intro a b ha hb hab
  have hinj : Function.Injective w := h.2
  have h1 : ext w a = w ⟨a, by omega⟩ := ext_apply w ⟨a, by omega⟩
  have h2 : ext w b = w ⟨b, by omega⟩ := ext_apply w ⟨b, by omega⟩
  rw [h1, h2] at hab
  exact congrArg Fin.val (hinj hab)

theorem npath_card {N : Network n} {m : ℕ} {w : ℕ → Fin (n + 2)} (h : NPath N m w) : m < n + 2 := by
  have hinj : Function.Injective (fun k : Fin (m + 1) => w k.val) := by
    intro a b hab
    exact Fin.ext (h.2 a b (by omega) (by omega) hab)
  have := Fintype.card_le_of_injective _ hinj
  simp at this
  omega

theorem mem_pathLengths_of_npath {N : Network n} {m : ℕ} {w : ℕ → Fin (n + 2)}
    (h : NPath N m w) {i j : Fin (n + 2)} (hi : w 0 = i) (hj : w m = j) :
    nlen N m w ∈ pathLengths N i j := by
  classical
  unfold pathLengths
  rw [Finset.mem_image]
  refine ⟨⟨⟨m, npath_card h⟩, fun k => w k.val⟩, ?_, ?_⟩
  · rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ⟨?_, ?_⟩, ?_, ?_⟩
    · intro k
      exact h.1 k.val k.2
    · intro a b hab
      have ha : a.val ≤ m := Nat.lt_succ_iff.mp a.2
      have hb : b.val ≤ m := Nat.lt_succ_iff.mp b.2
      exact Fin.ext (h.2 a.val b.val ha hb hab)
    · simpa using hi
    · simpa using hj
  · unfold walkLength nlen
    rw [← Fin.sum_univ_eq_sum_range (fun k => N.δ (w k) (w (k + 1))) m]
    exact Finset.sum_congr rfl (fun k _ => by simp)

theorem exists_npath_of_mem {N : Network n} {i j : Fin (n + 2)} {l : ℤ}
    (h : l ∈ pathLengths N i j) :
    ∃ m w, NPath N m w ∧ w 0 = i ∧ w m = j ∧ nlen N m w = l := by
  classical
  unfold pathLengths at h
  rw [Finset.mem_image] at h
  obtain ⟨⟨⟨m, hm⟩, w⟩, hf, rfl⟩ := h
  rw [Finset.mem_filter] at hf
  obtain ⟨_, hpath, hi, hj⟩ := hf
  refine ⟨m, ext w, npath_of_fin hpath, ?_, ?_, (walkLength_eq w).symm⟩
  · rw [ext_zero]; exact hi
  · rw [ext_last]; exact hj

/-- Cutting out the closed segment `i … i + d` of a walk. -/
theorem shortcut {N : Network n} {i d r : ℕ} {w : ℕ → Fin (n + 2)}
    (hw : NWalk N (i + d + r) w) (heq : w i = w (i + d)) :
    ∃ w' : ℕ → Fin (n + 2), NWalk N (i + r) w' ∧ w' 0 = w 0 ∧ w' (i + r) = w (i + d + r) ∧
      nlen N (i + d + r) w = nlen N d (fun k => w (i + k)) + nlen N (i + r) w' := by
  let w' : ℕ → Fin (n + 2) := fun k => if k < i then w k else w (k + d)
  have hw1 : ∀ k, k ≤ i → w' k = w k := by
    intro k hk
    by_cases h : k < i
    · simp [w', h]
    · have : k = i := by omega
      subst this
      simp [w', heq]
  have hw2 : ∀ k, i ≤ k → w' k = w (k + d) := by
    intro k hk
    have : ¬ k < i := by omega
    simp [w', this]
  refine ⟨w', ?_, ?_, ?_, ?_⟩
  · intro k hk
    by_cases h : k + 1 ≤ i
    · rw [hw1 k (by omega), hw1 (k + 1) h]
      exact hw k (by omega)
    · rw [hw2 k (by omega), hw2 (k + 1) (by omega)]
      have := hw (k + d) (by omega)
      have e : k + 1 + d = k + d + 1 := by omega
      rw [e]
      exact this
  · rw [hw1 0 (by omega)]
  · rw [hw2 (i + r) (by omega)]
    have e : i + r + d = i + d + r := by omega
    rw [e]
  · have hseg : nlen N d (fun k => w (i + k)) =
        ∑ x ∈ Finset.range d, N.δ (w (i + x)) (w (i + x + 1)) := rfl
    have hsplit : nlen N (i + d + r) w =
        ∑ x ∈ Finset.range d, N.δ (w (i + x)) (w (i + x + 1)) +
        (∑ k ∈ Finset.range i, N.δ (w k) (w (k + 1)) +
          ∑ x ∈ Finset.range r, N.δ (w (i + d + x)) (w (i + d + x + 1))) := by
      unfold nlen
      rw [Finset.sum_range_add, Finset.sum_range_add]
      ring
    have hw'len : nlen N (i + r) w' =
        ∑ k ∈ Finset.range i, N.δ (w k) (w (k + 1)) +
          ∑ x ∈ Finset.range r, N.δ (w (i + d + x)) (w (i + d + x + 1)) := by
      unfold nlen
      rw [Finset.sum_range_add]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        have hk' := Finset.mem_range.mp hk
        rw [hw1 k (by omega), hw1 (k + 1) (by omega)]
      · apply Finset.sum_congr rfl
        intro x _
        rw [hw2 (i + x) (by omega), hw2 (i + x + 1) (by omega)]
        have e1 : i + x + d = i + d + x := by omega
        have e2 : i + x + 1 + d = i + d + x + 1 := by omega
        rw [e1, e2]
    rw [hsplit, hw'len, hseg]

/-- A cycle in the `ℕ`-indexed sense gives a cycle in the sense of the platform. -/
theorem hasPositiveCycle_of_ncycle {N : Network n} {d : ℕ} {seg : ℕ → Fin (n + 2)}
    (h : NCycle N d seg) (hpos : 0 < nlen N d seg) : HasPositiveCycle N := by
  refine ⟨d, fun k : Fin (d + 1) => seg k.val, ⟨?_, h.2.1, ?_, ?_⟩, ?_⟩
  · intro k
    exact h.1 k.val k.2
  · simpa using h.2.2.1
  · intro a b hab
    exact Fin.ext (h.2.2.2 a b a.2 b.2 hab)
  · have : walkLength N (fun k : Fin (d + 1) => seg k.val) = nlen N d seg := by
      unfold walkLength nlen
      rw [← Fin.sum_univ_eq_sum_range (fun k => N.δ (seg k) (seg (k + 1))) d]
      exact Finset.sum_congr rfl (fun k _ => by simp)
    rw [this]
    exact hpos

theorem ncycle_le {N : Network n} (hno : ¬ HasPositiveCycle N) {d : ℕ} {seg : ℕ → Fin (n + 2)}
    (h : NCycle N d seg) : nlen N d seg ≤ 0 := by
  by_contra hpos
  push_neg at hpos
  exact hno (hasPositiveCycle_of_ncycle h hpos)

/-- Without positive cycles every walk is dominated by a path with the same end points. -/
theorem exists_path_ge (N : Network n) (hno : ¬ HasPositiveCycle N) :
    ∀ (m : ℕ) (w : ℕ → Fin (n + 2)), NWalk N m w →
      ∃ m' w', NPath N m' w' ∧ w' 0 = w 0 ∧ w' m' = w m ∧ nlen N m w ≤ nlen N m' w' := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro w hw
    by_cases hpath : ∀ a b, a ≤ m → b ≤ m → w a = w b → a = b
    · exact ⟨m, w, ⟨hw, hpath⟩, rfl, rfl, le_rfl⟩
    · classical
      have hex : ∃ j, j ≤ m ∧ ∃ i, i < j ∧ w i = w j := by
        push_neg at hpath
        obtain ⟨a, b, ha, hb, hab, hne⟩ := hpath
        rcases lt_or_gt_of_ne hne with h | h
        · exact ⟨b, hb, a, h, hab⟩
        · exact ⟨a, ha, b, h, hab.symm⟩
      obtain ⟨j, ⟨hjm, i, hij, hwij⟩, hmin⟩ : ∃ j, (j ≤ m ∧ ∃ i, i < j ∧ w i = w j) ∧
          ∀ j', j' < j → ¬ (j' ≤ m ∧ ∃ i, i < j' ∧ w i = w j') :=
        ⟨Nat.find hex, Nat.find_spec hex, fun j' h => Nat.find_min hex h⟩
      obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
      obtain ⟨r, rfl⟩ : ∃ r, m = i + d + r := ⟨m - (i + d), by omega⟩
      have hdpos : 0 < d := by omega
      have hcyc : NCycle N d (fun k => w (i + k)) := by
        refine ⟨?_, hdpos, ?_, ?_⟩
        · intro k hk
          exact hw (i + k) (by omega)
        · simpa using hwij
        · intro a b ha hb hab
          by_contra hne
          rcases lt_or_gt_of_ne hne with h | h
          · exact hmin (i + b) (by omega) ⟨by omega, i + a, by omega, hab⟩
          · exact hmin (i + a) (by omega) ⟨by omega, i + b, by omega, hab.symm⟩
      have hle := ncycle_le hno hcyc
      obtain ⟨w', hw', h0, hlast, hlen⟩ := shortcut hw hwij
      obtain ⟨m'', w'', hp, hp0, hpm, hge⟩ := ih (i + r) (by omega) w' hw'
      exact ⟨m'', w'', hp, hp0.trans h0, hpm.trans hlast, by rw [hlen]; linarith⟩

theorem feasible_of_no_cycle (P : Project n) (hP : P.StandingAssumption)
    (hno : ¬ HasPositiveCycle P.N) : ∃ S : Fin (n + 2) → ℝ, IsTimeFeasible P.N S := by
  classical
  have hne : ∀ i, (pathLengths P.N 0 i).Nonempty := by
    intro i
    obtain ⟨m, w, hpath, h0, hl, hlen⟩ := (hP i).1
    refine ⟨walkLength P.N w, ?_⟩
    have := mem_pathLengths_of_npath (npath_of_fin hpath) (i := 0) (j := i)
      (by rw [ext_zero]; exact h0) (by rw [ext_last]; exact hl)
    rwa [← walkLength_eq] at this
  let S : Fin (n + 2) → ℤ := fun i => (pathLengths P.N 0 i).max' (hne i)
  have hS_ge : ∀ {i : Fin (n + 2)} {m : ℕ} {w : ℕ → Fin (n + 2)}, NPath P.N m w → w 0 = 0 →
      w m = i → nlen P.N m w ≤ S i := by
    intro i m w hp h0 hm
    exact Finset.le_max' _ _ (mem_pathLengths_of_npath hp h0 hm)
  have hS_mem : ∀ i, ∃ m w, NPath P.N m w ∧ w 0 = 0 ∧ w m = i ∧ nlen P.N m w = S i := by
    intro i
    exact exists_npath_of_mem (Finset.max'_mem (pathLengths P.N 0 i) (hne i))
  have hS_nonneg : ∀ i, 0 ≤ S i := by
    intro i
    obtain ⟨m, w, hpath, h0, hl, hlen⟩ := (hP i).1
    calc (0 : ℤ) ≤ walkLength P.N w := hlen
      _ ≤ S i := by
        rw [walkLength_eq]
        exact hS_ge (npath_of_fin hpath) (by rw [ext_zero]; exact h0) (by rw [ext_last]; exact hl)
  have hS_zero : S 0 = 0 := by
    apply le_antisymm _ (hS_nonneg 0)
    obtain ⟨m, w, hp, h0, hm, hlen⟩ := hS_mem 0
    have : m = 0 := hp.2 m 0 (le_refl m) (Nat.zero_le _) (hm.trans h0.symm)
    subst this
    simp [← hlen, nlen]
  have harc : ∀ i j : Fin (n + 2), (i, j) ∈ P.N.E → (S i : ℤ) + P.N.δ i j ≤ S j := by
    intro i j hij
    obtain ⟨m, w, hp, h0, hm, hlen⟩ := hS_mem i
    let w'' : ℕ → Fin (n + 2) := fun k => if k ≤ m then w k else j
    have hw''1 : ∀ k, k ≤ m → w'' k = w k := fun k hk => by simp [w'', hk]
    have hw''2 : w'' (m + 1) = j := by simp [w'']
    have hwalk : NWalk P.N (m + 1) w'' := by
      intro k hk
      by_cases h : k < m
      · rw [hw''1 k (by omega), hw''1 (k + 1) (by omega)]
        exact hp.1 k h
      · have : k = m := by omega
        subst this
        rw [hw''1 k (le_refl _), hw''2, hm]
        exact hij
    have hlen'' : nlen P.N (m + 1) w'' = nlen P.N m w + P.N.δ i j := by
      unfold nlen
      rw [Finset.sum_range_succ]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        have hk' := Finset.mem_range.mp hk
        rw [hw''1 k (by omega), hw''1 (k + 1) (by omega)]
      · rw [hw''1 m (le_refl _), hw''2, hm]
    obtain ⟨m', w', hp', h0', hm', hge⟩ := exists_path_ge P.N hno (m + 1) w'' hwalk
    have h0'' : w' 0 = 0 := by rw [h0', hw''1 0 (Nat.zero_le _), h0]
    have := hS_ge hp' h0'' (hm'.trans hw''2)
    rw [hlen''] at hge
    omega
  refine ⟨fun i => (S i : ℝ), ⟨⟨by simp [hS_zero], fun i => by show (0 : ℝ) ≤ (S i : ℝ); exact_mod_cast hS_nonneg i⟩, ?_⟩⟩
  intro e he
  have := harc e.1 e.2 he
  have h2 : ((S e.1 : ℤ) : ℝ) + (P.N.δ e.1 e.2 : ℝ) ≤ (S e.2 : ℝ) := by exact_mod_cast this
  linarith

end TfAux

open ProjSchedTW.Temporal in
theorem solution {n : ℕ} (P : Project n)
    (hP : P.StandingAssumption) :
    (∃ S : Fin (n + 2) → ℝ, IsTimeFeasible P.N S) ↔ ¬ HasPositiveCycle P.N := by
  constructor
  · rintro ⟨S, hS⟩ ⟨m, w, hcyc, hpos⟩
    have hsum : (walkLength P.N w : ℝ) ≤ S (w (Fin.last m)) - S (w 0) := by
      unfold walkLength
      push_cast
      calc ∑ k : Fin m, (P.N.δ (w k.castSucc) (w k.succ) : ℝ)
          ≤ ∑ k : Fin m, (S (w k.succ) - S (w k.castSucc)) :=
            Finset.sum_le_sum (fun k _ => hS.2 _ (hcyc.1 k))
        _ = ∑ k : Fin m, ((fun j : ℕ => S (TfAux.ext w j)) (k.val + 1) -
              (fun j : ℕ => S (TfAux.ext w j)) k.val) := by
            apply Finset.sum_congr rfl
            intro k _
            have e1 : TfAux.ext w (k.val + 1) = w k.succ := TfAux.ext_apply w k.succ
            have e2 : TfAux.ext w k.val = w k.castSucc := TfAux.ext_apply w k.castSucc
            show S (w k.succ) - S (w k.castSucc) = S (TfAux.ext w (k.val + 1)) - S (TfAux.ext w k.val)
            rw [e1, e2]
        _ = S (w (Fin.last m)) - S (w 0) := by
            rw [Fin.sum_univ_eq_sum_range (fun k => (fun j : ℕ => S (TfAux.ext w j)) (k + 1) -
              (fun j : ℕ => S (TfAux.ext w j)) k) m, Finset.sum_range_sub
              (fun j : ℕ => S (TfAux.ext w j)) m]
            simp only [TfAux.ext_last, TfAux.ext_zero]
    have h0 : w 0 = w (Fin.last m) := hcyc.2.2.1
    rw [h0] at hsum
    have : (0 : ℝ) < (walkLength P.N w : ℝ) := by exact_mod_cast hpos
    linarith
  · intro hno
    exact TfAux.feasible_of_no_cycle P hP hno
