-- Prove2me | solution 1 for ProjSchedTW.Temporal.baseInterval_nonempty_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:51:21.024377+00:00
-- url     : https://prove2.me/submissions/402e9452-a83e-46fb-9c77-b52ff2fe28d5

import Mathlib
import Definitions.Def_ProjSchedTW_Temporal_TimeQuantities

set_option autoImplicit false

namespace P2MAux73758b71
open ProjSchedTW.Temporal

variable {n : ℕ}

def wsum (N : Network n) (f : ℕ → Fin (n + 2)) (m : ℕ) : ℤ :=
  ∑ k ∈ Finset.range m, N.δ (f k) (f (k + 1))

def WalkN (N : Network n) (f : ℕ → Fin (n + 2)) (m : ℕ) : Prop :=
  ∀ k < m, (f k, f (k + 1)) ∈ N.E

theorem cycle_of_closed (N : Network n) :
    ∀ m (f : ℕ → Fin (n + 2)), WalkN N f m → f 0 = f m → 0 < wsum N f m →
      HasPositiveCycle N := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro f hw hc hpos
  by_cases hinj : ∀ a < m, ∀ b < m, f a = f b → a = b
  · refine ⟨m, fun k => f k.val, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro k
      exact hw k.val k.isLt
    · rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp [wsum] at hpos
      · exact h
    · simpa using hc
    · intro a b hab
      apply Fin.ext
      exact hinj a.val a.isLt b.val b.isLt hab
    · unfold walkLength
      have := Fin.sum_univ_eq_sum_range (fun k => N.δ (f k) (f (k + 1))) m
      simpa [wsum, this] using hpos
  · push_neg at hinj
    obtain ⟨a, b, hab, hb, heq⟩ : ∃ a b, a < b ∧ b < m ∧ f a = f b := by
      obtain ⟨a, ha, b, hb, hab, hne⟩ := hinj
      rcases lt_or_gt_of_ne hne with h | h
      · exact ⟨a, b, h, hb, hab⟩
      · exact ⟨b, a, h, ha, hab.symm⟩
    obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
    obtain ⟨c, rfl⟩ : ∃ c, m = a + d + c := ⟨m - (a + d), by omega⟩
    have hsplit : wsum N f (a + d + c) =
        wsum N f a + wsum N (fun k => f (a + k)) d + wsum N (fun k => f (a + d + k)) c := by
      unfold wsum
      rw [Finset.sum_range_add, Finset.sum_range_add]
      rfl
    set h : ℕ → Fin (n + 2) := fun k => if k < a then f k else f (k + d) with hh
    have hsum2 : wsum N h (a + c) = wsum N f a + wsum N (fun k => f (a + d + k)) c := by
      unfold wsum
      rw [Finset.sum_range_add]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        have h1 : h k = f k := by simp [hh, hk]
        have h2 : h (k + 1) = f (k + 1) := by
          by_cases hk1 : k + 1 < a
          · simp [hh, hk1]
          · have : k + 1 = a := by omega
            simp only [hh, hk1, if_false]
            rw [this, ← heq]
        rw [h1, h2]
      · apply Finset.sum_congr rfl
        intro k _
        have h1 : h (a + k) = f (a + d + k) := by
          simp only [hh, show ¬ (a + k < a) by omega, if_false]
          congr 1; omega
        have h2 : h (a + k + 1) = f (a + d + (k + 1)) := by
          simp only [hh, show ¬ (a + k + 1 < a) by omega, if_false]
          congr 1; omega
        rw [h1, h2]
    by_cases hin : 0 < wsum N (fun k => f (a + k)) d
    · refine ih d (by omega) (fun k => f (a + k)) ?_ ?_ hin
      · intro k hk
        exact hw (a + k) (by omega)
      · simpa using heq
    · refine ih (a + c) (by omega) h ?_ ?_ (by rw [hsum2]; rw [hsplit] at hpos; linarith)
      · intro k hk
        by_cases hk1 : k + 1 < a
        · have e1 : h k = f k := by simp [hh, show k < a by omega]
          have e2 : h (k + 1) = f (k + 1) := by simp [hh, hk1]
          rw [e1, e2]; exact hw k (by omega)
        · by_cases hk2 : k + 1 = a
          · have e1 : h k = f k := by simp [hh, show k < a by omega]
            have e2 : h (k + 1) = f (k + 1) := by
              simp only [hh, hk1, if_false]
              rw [hk2, ← heq]
            rw [e1, e2]; exact hw k (by omega)
          · have e1 : h k = f (k + d) := by simp [hh, show ¬ k < a by omega]
            have e2 : h (k + 1) = f (k + d + 1) := by
              simp only [hh, hk1, if_false]
              congr 1; omega
            rw [e1, e2]; exact hw (k + d) (by omega)
      · have e1 : h (a + c) = f (a + d + c) := by
          simp only [hh, show ¬ (a + c < a) by omega, if_false]
          congr 1; omega
        have e0 : h 0 = f 0 := by
          by_cases ha : 0 < a
          · simp only [hh, ha, if_true]
          · simp only [hh, ha, if_false]
            have : a = 0 := by omega
            subst this
            exact heq.symm
        rw [e0, e1, hc]

def ext (m : ℕ) (w : Fin (m + 1) → Fin (n + 2)) : ℕ → Fin (n + 2) :=
  fun k => w ⟨min k m, by omega⟩

theorem ext_eq (m : ℕ) (w : Fin (m + 1) → Fin (n + 2)) (k : ℕ) (hk : k < m + 1) :
    ext m w k = w ⟨k, hk⟩ := by
  show w _ = w _
  congr 1
  apply Fin.ext
  show min k m = k
  omega

theorem walk_of_isWalk (N : Network n) (m : ℕ) (w : Fin (m + 1) → Fin (n + 2))
    (hw : IsWalk N w) : WalkN N (ext m w) m := by
  intro k hk
  rw [ext_eq m w k (by omega), ext_eq m w (k + 1) (by omega)]
  exact hw ⟨k, hk⟩

theorem inj_of_isPath (N : Network n) (m : ℕ) (w : Fin (m + 1) → Fin (n + 2))
    (hw : IsPath N w) : ∀ a ≤ m, ∀ b ≤ m, ext m w a = ext m w b → a = b := by
  intro a ha b hb hab
  rw [ext_eq m w a (by omega), ext_eq m w b (by omega)] at hab
  have := hw.2 hab
  simpa using this

theorem wsum_ext (N : Network n) (m : ℕ) (w : Fin (m + 1) → Fin (n + 2)) :
    wsum N (ext m w) m = walkLength N w := by
  unfold wsum walkLength
  rw [← Fin.sum_univ_eq_sum_range (fun k => N.δ (ext m w k) (ext m w (k + 1))) m]
  apply Finset.sum_congr rfl
  intro k _
  rw [ext_eq m w k (by omega), ext_eq m w (k + 1) (by omega)]
  rfl

open Classical in
theorem ofPath (N : Network n) (i j : Fin (n + 2)) (a : ℤ) (h : a ∈ pathLengths N i j) :
    ∃ m f, f 0 = i ∧ f m = j ∧ WalkN N f m ∧ wsum N f m = a := by
  simp only [pathLengths, Finset.mem_image] at h
  obtain ⟨⟨⟨m, hm⟩, w⟩, hw, rfl⟩ := h
  simp only [Finset.mem_filter] at hw
  obtain ⟨_, ⟨hwalk, _⟩, h0, hl⟩ := hw
  refine ⟨m, ext m w, ?_, ?_, walk_of_isWalk N m w hwalk, wsum_ext N m w⟩
  · rw [ext_eq m w 0 (by omega)]; exact h0
  · rw [ext_eq m w m (by omega)]; exact hl

open Classical in
theorem toPath (N : Network n) (f : ℕ → Fin (n + 2)) (m : ℕ) (hw : WalkN N f m)
    (hinj : ∀ a ≤ m, ∀ b ≤ m, f a = f b → a = b) :
    wsum N f m ∈ pathLengths N (f 0) (f m) := by
  have hm : m < n + 2 := by
    have := Fintype.card_le_of_injective (fun k : Fin (m + 1) => f k.val) (by
      intro a b hab
      apply Fin.ext
      exact hinj a.val (by omega) b.val (by omega) hab)
    simp at this
    omega
  simp only [pathLengths, Finset.mem_image]
  refine ⟨⟨⟨m, hm⟩, fun k => f k.val⟩, ?_, ?_⟩
  · simp only [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ⟨?_, ?_⟩, ?_, ?_⟩
    · intro k
      exact hw k.val k.isLt
    · intro a b hab
      apply Fin.ext
      exact hinj a.val (Nat.le_of_lt_succ a.isLt) b.val (Nat.le_of_lt_succ b.isLt) hab
    · rfl
    · rfl
  · show walkLength N (fun k : Fin (m + 1) => f k.val) = wsum N f m
    unfold walkLength wsum
    exact Fin.sum_univ_eq_sum_range (fun k => N.δ (f k) (f (k + 1))) m

theorem walk_plus (N : Network n) (L : ℤ) (f : ℕ → Fin (n + 2)) (m : ℕ) (hw : WalkN N f m) :
    WalkN (N.plus L) f m := by
  intro k hk
  show _ ∈ insert _ N.E
  exact Finset.mem_insert_of_mem (hw k hk)

theorem dist_exists (N : Network n) (i j : Fin (n + 2)) (h : (pathLengths N i j).Nonempty) :
    ∃ m f, f 0 = i ∧ f m = j ∧ WalkN N f m ∧ (ProjSchedTW.Temporal.dist N i j).unbotD 0 = wsum N f m := by
  obtain ⟨a, ha⟩ := Finset.max_of_nonempty h
  have hmem := Finset.mem_of_max ha
  obtain ⟨m, f, h0, hm, hw, hs⟩ := ofPath N i j a hmem
  refine ⟨m, f, h0, hm, hw, ?_⟩
  unfold ProjSchedTW.Temporal.dist
  rw [ha, hs]
  rfl

theorem key {n : ℕ} (P : Project n) (hP : P.StandingAssumption) (L : ℤ)
    (hL : ¬ HasPositiveCycle (P.N.plus L)) (i : Fin (n + 2)) : P.ES L i ≤ P.LS L i := by
  obtain ⟨⟨m1, w1, hp1, h01, hl1, _⟩, ⟨m2, w2, hp2, h02, hl2, _⟩⟩ := hP i
  -- path 0 → i in N⁺
  have ne1 : (pathLengths (P.N.plus L) 0 i).Nonempty := by
    have := toPath (P.N.plus L) (ext m1 w1) m1
      (walk_plus P.N L _ _ (walk_of_isWalk P.N m1 w1 hp1.1)) (inj_of_isPath P.N m1 w1 hp1)
    have e0 : ext m1 w1 0 = 0 := by rw [ext_eq m1 w1 0 (by omega)]; exact h01
    have el : ext m1 w1 m1 = i := by rw [ext_eq m1 w1 m1 (by omega)]; exact hl1
    rw [e0, el] at this
    exact ⟨_, this⟩
  -- path i → 0 in N⁺
  have ne2 : (pathLengths (P.N.plus L) i 0).Nonempty := by
    set g := ext m2 w2 with hg
    have gw : WalkN P.N g m2 := walk_of_isWalk P.N m2 w2 hp2.1
    have gi : ∀ a ≤ m2, ∀ b ≤ m2, g a = g b → a = b := inj_of_isPath P.N m2 w2 hp2
    have g0 : g 0 = i := by rw [hg, ext_eq m2 w2 0 (by omega)]; exact h02
    have gl : g m2 = Fin.last (n + 1) := by rw [hg, ext_eq m2 w2 m2 (by omega)]; exact hl2
    by_cases hz : ∃ k ≤ m2, g k = 0
    · obtain ⟨k, hk, hgk⟩ := hz
      have := toPath (P.N.plus L) g k
        (walk_plus P.N L _ _ (fun j hj => gw j (by omega)))
        (fun a ha b hb hab => gi a (by omega) b (by omega) hab)
      rw [g0, hgk] at this
      exact ⟨_, this⟩
    · push_neg at hz
      set g' : ℕ → Fin (n + 2) := fun j => if j ≤ m2 then g j else 0 with hg'
      have w' : WalkN (P.N.plus L) g' (m2 + 1) := by
        intro j hj
        by_cases hj2 : j < m2
        · have e1 : g' j = g j := by simp [hg', show j ≤ m2 by omega]
          have e2 : g' (j + 1) = g (j + 1) := by simp [hg', show j + 1 ≤ m2 by omega]
          rw [e1, e2]
          exact walk_plus P.N L _ _ gw j hj2
        · have hjm : j = m2 := by omega
          subst hjm
          have e1 : g' j = Fin.last (n + 1) := by simp [hg', gl]
          have e2 : g' (j + 1) = 0 := by simp [hg']
          rw [e1, e2]
          show _ ∈ insert _ P.N.E
          exact Finset.mem_insert_self _ _
      have i' : ∀ a ≤ m2 + 1, ∀ b ≤ m2 + 1, g' a = g' b → a = b := by
        intro a ha b hb hab
        by_cases ha2 : a ≤ m2 <;> by_cases hb2 : b ≤ m2
        · simp only [hg', ha2, hb2, if_true] at hab
          exact gi a ha2 b hb2 hab
        · simp only [hg', ha2, hb2, if_true, if_false] at hab
          exact absurd hab (hz a ha2)
        · simp only [hg', ha2, hb2, if_true, if_false] at hab
          exact absurd hab.symm (hz b hb2)
        · omega
      have := toPath (P.N.plus L) g' (m2 + 1) w' i'
      have e0 : g' 0 = i := by simp [hg', g0]
      have el : g' (m2 + 1) = 0 := by simp [hg']
      rw [e0, el] at this
      exact ⟨_, this⟩
  obtain ⟨n1, f1, f10, f1l, f1w, hES⟩ := dist_exists _ _ _ ne1
  obtain ⟨n2, f2, f20, f2l, f2w, hLS⟩ := dist_exists _ _ _ ne2
  have hE : P.ES L i = wsum (P.N.plus L) f1 n1 := hES
  have hLs : P.LS L i = -wsum (P.N.plus L) f2 n2 := by
    unfold Project.LS; rw [hLS]
  rw [hE, hLs]
  by_contra hcon
  push_neg at hcon
  set F : ℕ → Fin (n + 2) := fun k => if k ≤ n1 then f1 k else f2 (k - n1) with hF
  have Fa : ∀ k, F (n1 + k) = f2 k := by
    intro k
    by_cases hk : k = 0
    · subst hk; simp [hF, f1l, f20]
    · simp only [hF, show ¬ (n1 + k ≤ n1) by omega, if_false]
      congr 1; omega
  have Fb : ∀ k ≤ n1, F k = f1 k := by
    intro k hk; simp [hF, hk]
  apply hL
  refine cycle_of_closed _ (n1 + n2) F ?_ ?_ ?_
  · intro k hk
    by_cases hk1 : k < n1
    · rw [Fb k (by omega), Fb (k + 1) (by omega)]
      exact f1w k hk1
    · obtain ⟨j, rfl⟩ : ∃ j, k = n1 + j := ⟨k - n1, by omega⟩
      rw [Fa j, show n1 + j + 1 = n1 + (j + 1) by omega, Fa (j + 1)]
      exact f2w j (by omega)
  · rw [Fb 0 (by omega), Fa n2, f10, f2l]
  · have : wsum (P.N.plus L) F (n1 + n2) =
        wsum (P.N.plus L) f1 n1 + wsum (P.N.plus L) f2 n2 := by
      unfold wsum
      rw [Finset.sum_range_add]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        rw [Fb k (by omega), Fb (k + 1) (by omega)]
      · apply Finset.sum_congr rfl
        intro k _
        rw [Fa k, show n1 + k + 1 = n1 + (k + 1) by omega, Fa (k + 1)]
    rw [this]
    linarith

end P2MAux73758b71

open ProjSchedTW.Temporal in
theorem solution {n : ℕ} (P : Project n) (hP : P.StandingAssumption)
    (L : ℤ) (hL : ¬ HasPositiveCycle (P.N.plus L))
    (i : Fin (n + 2)) (hi0 : i ≠ 0) (hin : i ≠ Fin.last (n + 1)) :
    (P.baseInterval L i).Nonempty ↔ P.IsCritical L i ∨ P.IsNearCritical L i := by
  have hk := P2MAux73758b71.key P hP L hL i
  have hp := P.p_pos i hi0 hin
  rw [Project.baseInterval, Set.nonempty_Ico]
  unfold Project.IsCritical Project.IsNearCritical Project.TF
  rw [Project.EC]
  push_cast
  constructor
  · intro h
    have h' : P.LS L i < P.ES L i + (P.p i : ℤ) := by exact_mod_cast h
    omega
  · intro h
    have h' : P.LS L i < P.ES L i + (P.p i : ℤ) := by omega
    exact_mod_cast h'
