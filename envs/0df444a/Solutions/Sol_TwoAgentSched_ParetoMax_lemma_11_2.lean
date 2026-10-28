-- Prove2me | solution 1 for TwoAgentSched.ParetoMax.lemma_11_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:24:06.835019+00:00
-- url     : https://prove2.me/submissions/5dbae68c-dda8-4296-b3ac-bc5f3027c0bf

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Card
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_TwoAgentSched_ParetoMax_Model

set_option autoImplicit false
open TwoAgentSched.ParetoMax TwoAgentSched.MaxMax MooreLateJobs.Shared

section generic
variable {ι : Type*} [DecidableEq ι] (p : ι → ℝ)

lemma pm112_ca_append_left (l₁ l₂ : List ι) (m : ℕ) (hm : m < l₁.length) :
    completionAt p (l₁ ++ l₂) m = completionAt p l₁ m := by
  unfold completionAt
  rw [List.take_append_of_le_length (by omega)]

lemma pm112_ct_append_left (l₁ l₂ : List ι) (x : ι) (hx : x ∈ l₁) :
    completionTime p (l₁ ++ l₂) x = completionTime p l₁ x := by
  unfold completionTime
  rw [List.idxOf_append_of_mem hx]
  exact pm112_ca_append_left p l₁ l₂ _ (List.idxOf_lt_length_iff.mpr hx)

lemma pm112_ct_last (l : List ι) (z : ι) (hz : z ∉ l) :
    completionTime p (l ++ [z]) z = ((l ++ [z]).map p).sum := by
  unfold completionTime completionAt
  have h1 : (l ++ [z]).idxOf z = l.length := by
    rw [List.idxOf_append_of_notMem hz]; simp
  rw [h1]
  have h2 : (l ++ [z]).take (l.length + 1) = l ++ [z] := List.take_of_length_le (by simp)
  rw [h2]

lemma pm112_ct_erase_le (hp : ∀ j, 0 ≤ p j) (l : List ι) (hnd : l.Nodup) (z x : ι)
    (hz : z ∈ l) (hx : x ∈ l) (hxz : x ≠ z) :
    completionTime p (l.erase z) x ≤ completionTime p l x := by
  obtain ⟨a, b, rfl⟩ := List.append_of_mem hz
  have hza : z ∉ a := fun h => (List.nodup_append.1 hnd).2.2 z h z (by simp) rfl
  have herase : (a ++ z :: b).erase z = a ++ b := by
    rw [List.erase_append_right _ hza]; simp
  rw [herase]
  have hx' : x ∈ a ∨ x ∈ b := by
    rcases List.mem_append.1 hx with h | h
    · exact Or.inl h
    · rcases List.mem_cons.1 h with h | h
      · exact absurd h hxz
      · exact Or.inr h
  rcases hx' with hxa | hxb
  · rw [pm112_ct_append_left p a b x hxa, pm112_ct_append_left p a (z :: b) x hxa]
  · have hxa : x ∉ a := fun h => (List.nodup_append.1 hnd).2.2 x h x (by simp [hxb]) rfl
    unfold completionTime completionAt
    rw [List.idxOf_append_of_notMem hxa, List.idxOf_append_of_notMem hxa,
      List.idxOf_cons_ne _ (Ne.symm hxz)]
    rw [List.take_append, List.take_append]
    have e1 : a.take (a.length + List.idxOf x b + 1) = a := List.take_of_length_le (by omega)
    have e2 : a.take (a.length + (List.idxOf x b).succ + 1) = a :=
      List.take_of_length_le (by omega)
    rw [e1, e2]
    have e3 : a.length + List.idxOf x b + 1 - a.length = List.idxOf x b + 1 := by omega
    have e4 : a.length + (List.idxOf x b).succ + 1 - a.length = List.idxOf x b + 1 + 1 := by omega
    rw [e3, e4]
    simp only [List.take_succ_cons, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    linarith [hp z]

lemma pm112_last_cost (l : List ι) (hnd : l.Nodup) (hne : l ≠ []) :
    ∃ y ∈ l, completionTime p l y = (l.map p).sum := by
  obtain ⟨L, y, hL⟩ := (List.eq_nil_or_concat l).resolve_left hne
  rw [List.concat_eq_append] at hL
  subst hL
  refine ⟨y, by simp, ?_⟩
  have hy : y ∉ L := fun h => (List.nodup_append.1 hnd).2.2 y h y (by simp) rfl
  exact pm112_ct_last p L y hy

lemma pm112_pos (l : List ι) (x : ι) (hx : x ∈ l) :
    ∃ m, ∃ hm : m < l.length, l[m] = x ∧ completionTime p l x = completionAt p l m :=
  ⟨l.idxOf x, List.idxOf_lt_length_iff.2 hx, List.getElem_idxOf _, rfl⟩

lemma pm112_erase_ex (hp : ∀ j, 0 ≤ p j) (l : List ι) (hnd : l.Nodup) (z : ι) (hz : z ∈ l) :
    ∃ l'', l.Perm (l'' ++ [z]) ∧
      ∀ x ∈ l'', x ∈ l ∧ x ≠ z ∧ completionTime p l'' x ≤ completionTime p l x := by
  refine ⟨l.erase z, ?_, fun x hx => ?_⟩
  · exact (List.perm_cons_erase hz).trans (List.perm_append_singleton z _).symm
  · rw [hnd.mem_erase_iff] at hx
    exact ⟨hx.2, hx.1, pm112_ct_erase_le p hp l hnd z x hz hx.2 hx.1⟩

end generic

instance {nA nB : ℕ} : LawfulBEq (Job nA nB) where
  eq_of_beq {a b} h := by
    rcases a with a | a <;> rcases b with b | b
    · exact congrArg Sum.inl (eq_of_beq h)
    · contradiction
    · contradiction
    · exact congrArg Sum.inr (eq_of_beq h)
  rfl {a} := by
    rcases a with a | a <;> exact beq_self_eq_true a

lemma pm112_beq_eq {nA nB : ℕ} (a z : Job nA nB) :
    @BEq.beq (Job nA nB) instBEqOfDecidableEq a z = (a == z) := by
  change decide (a = z) = (a == z)
  by_cases h : a = z
  · subst h; rw [decide_eq_true rfl, beq_self_eq_true]
  · rw [decide_eq_false h, beq_false_of_ne h]

lemma pm112_idxOf_eq {nA nB : ℕ} (l : List (Job nA nB)) (z : Job nA nB) :
    @List.idxOf (Job nA nB) instBEqOfDecidableEq z l = l.idxOf z := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.idxOf_cons, pm112_beq_eq, ih]

lemma pm112_ct_eq_ca_idxOf {nA nB : ℕ} (p : Job nA nB → ℝ) (l : List (Job nA nB)) (x : Job nA nB) :
    completionTime p l x = completionAt p l (l.idxOf x) := by
  unfold completionTime
  rw [pm112_idxOf_eq]

def FeasAB {nA nB : ℕ} (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ)
    (yA yB : ℝ) (l : List (Job nA nB)) : Prop :=
  (∀ h : Fin nA, Sum.inl h ∈ l → fA h (completionTime p l (Sum.inl h)) ≤ yA) ∧
  (∀ k : Fin nB, Sum.inr k ∈ l → fB k (completionTime p l (Sum.inr k)) ≤ yB)

def IsBPrioritySeq {nA nB : ℕ} (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ)
    (yA yB : ℝ) (σ : List (Job nA nB)) : Prop :=
  ∀ (m : ℕ) (hm : m < σ.length),
    (∃ k : Fin nB, σ[m] = Sum.inr k ∧ fB k (completionAt p σ m) ≤ yB) ∨
    (∃ h : Fin nA, σ[m] = Sum.inl h ∧ fA h (completionAt p σ m) ≤ yA ∧
      ∀ k : Fin nB, Sum.inr k ∈ (σ.take (m + 1)).toFinset → yB < fB k (completionAt p σ m))

def IsAPrioritySeq {nA nB : ℕ} (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ)
    (yA yB : ℝ) (σ : List (Job nA nB)) : Prop :=
  ∀ (m : ℕ) (hm : m < σ.length),
    (∃ h : Fin nA, σ[m] = Sum.inl h ∧ fA h (completionAt p σ m) ≤ yA) ∨
    (∃ k : Fin nB, σ[m] = Sum.inr k ∧ fB k (completionAt p σ m) ≤ yB ∧
      ∀ h : Fin nA, Sum.inl h ∈ (σ.take (m + 1)).toFinset → yA < fA h (completionAt p σ m))

lemma bPriority_append_iff {nA nB : ℕ} (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ)
    (fB : Fin nB → ℝ → ℝ) (yA yB : ℝ) (σ : List (Job nA nB)) (z : Job nA nB) :
    IsBPrioritySeq p fA fB yA yB (σ ++ [z]) ↔
      IsBPrioritySeq p fA fB yA yB σ ∧
      ((∃ k : Fin nB, z = Sum.inr k ∧ fB k ((σ ++ [z]).map p).sum ≤ yB) ∨
        (∃ h : Fin nA, z = Sum.inl h ∧ fA h ((σ ++ [z]).map p).sum ≤ yA ∧
          ∀ k : Fin nB, Sum.inr k ∈ (σ ++ [z]).toFinset → yB < fB k ((σ ++ [z]).map p).sum)) := by
  have hT : ∀ m, m < σ.length → (σ ++ [z]).take (m + 1) = σ.take (m + 1) :=
    fun m hm => List.take_append_of_le_length (by omega)
  have hCA : ∀ m, m < σ.length → completionAt p (σ ++ [z]) m = completionAt p σ m :=
    fun m hm => pm112_ca_append_left p σ [z] m hm
  have hTlast : (σ ++ [z]).take (σ.length + 1) = σ ++ [z] := List.take_of_length_le (by simp)
  have hCAlast : completionAt p (σ ++ [z]) σ.length = ((σ ++ [z]).map p).sum := by
    unfold completionAt; rw [hTlast]
  have hlen : (σ ++ [z]).length = σ.length + 1 := by simp
  constructor
  · intro H
    refine ⟨fun m hm => ?_, ?_⟩
    · have := H m (by omega)
      have hg : (σ ++ [z])[m]'(by omega) = σ[m] := List.getElem_append_left hm
      rw [hg, hT m hm, hCA m hm] at this
      exact this
    · have := H σ.length (by omega)
      have hg : (σ ++ [z])[σ.length]'(by omega) = z := by simp
      rw [hg, hTlast, hCAlast] at this
      exact this
  · rintro ⟨H, hlast⟩ m hm
    rcases Nat.lt_succ_iff_lt_or_eq.1 (hlen ▸ hm) with hm' | hm'
    · have := H m hm'
      have hg : (σ ++ [z])[m]'(by omega) = σ[m] := List.getElem_append_left hm'
      rw [hg, hT m hm', hCA m hm']
      exact this
    · subst hm'
      have hg : (σ ++ [z])[σ.length]'(by omega) = z := by simp
      rw [hg, hTlast, hCAlast]
      exact hlast

lemma aPriority_append_iff {nA nB : ℕ} (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ)
    (fB : Fin nB → ℝ → ℝ) (yA yB : ℝ) (σ : List (Job nA nB)) (z : Job nA nB) :
    IsAPrioritySeq p fA fB yA yB (σ ++ [z]) ↔
      IsAPrioritySeq p fA fB yA yB σ ∧
      ((∃ h : Fin nA, z = Sum.inl h ∧ fA h ((σ ++ [z]).map p).sum ≤ yA) ∨
        (∃ k : Fin nB, z = Sum.inr k ∧ fB k ((σ ++ [z]).map p).sum ≤ yB ∧
          ∀ h : Fin nA, Sum.inl h ∈ (σ ++ [z]).toFinset → yA < fA h ((σ ++ [z]).map p).sum)) := by
  have hT : ∀ m, m < σ.length → (σ ++ [z]).take (m + 1) = σ.take (m + 1) :=
    fun m hm => List.take_append_of_le_length (by omega)
  have hCA : ∀ m, m < σ.length → completionAt p (σ ++ [z]) m = completionAt p σ m :=
    fun m hm => pm112_ca_append_left p σ [z] m hm
  have hTlast : (σ ++ [z]).take (σ.length + 1) = σ ++ [z] := List.take_of_length_le (by simp)
  have hCAlast : completionAt p (σ ++ [z]) σ.length = ((σ ++ [z]).map p).sum := by
    unfold completionAt; rw [hTlast]
  have hlen : (σ ++ [z]).length = σ.length + 1 := by simp
  constructor
  · intro H
    refine ⟨fun m hm => ?_, ?_⟩
    · have := H m (by omega)
      have hg : (σ ++ [z])[m]'(by omega) = σ[m] := List.getElem_append_left hm
      rw [hg, hT m hm, hCA m hm] at this
      exact this
    · have := H σ.length (by omega)
      have hg : (σ ++ [z])[σ.length]'(by omega) = z := by simp
      rw [hg, hTlast, hCAlast] at this
      exact this
  · rintro ⟨H, hlast⟩ m hm
    rcases Nat.lt_succ_iff_lt_or_eq.1 (hlen ▸ hm) with hm' | hm'
    · have := H m hm'
      have hg : (σ ++ [z])[m]'(by omega) = σ[m] := List.getElem_append_left hm'
      rw [hg, hT m hm', hCA m hm']
      exact this
    · subst hm'
      have hg : (σ ++ [z])[σ.length]'(by omega) = z := by simp
      rw [hg, hTlast, hCAlast]
      exact hlast

lemma feasAB_of_bPriority {nA nB : ℕ} (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ)
    (fB : Fin nB → ℝ → ℝ) (yA yB : ℝ) (σ : List (Job nA nB))
    (hrule : IsBPrioritySeq p fA fB yA yB σ) : FeasAB p fA fB yA yB σ := by
  refine ⟨fun h hh => ?_, fun k hk => ?_⟩
  · obtain ⟨m, hm, hg, hct⟩ := pm112_pos p σ (Sum.inl h) hh
    rw [hct]
    rcases hrule m hm with ⟨k', hk', _⟩ | ⟨h', hh', hle, _⟩
    · rw [hg] at hk'; exact absurd hk' (by simp)
    · rw [hg] at hh'
      have : h' = h := (Sum.inl_injective hh').symm
      subst this; exact hle
  · obtain ⟨m, hm, hg, hct⟩ := pm112_pos p σ (Sum.inr k) hk
    rw [hct]
    rcases hrule m hm with ⟨k', hk', hle⟩ | ⟨h', hh', _, _⟩
    · rw [hg] at hk'
      have : k' = k := (Sum.inr_injective hk').symm
      subst this; exact hle
    · rw [hg] at hh'; exact absurd hh' (by simp)

lemma feasAB_of_aPriority {nA nB : ℕ} (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ)
    (fB : Fin nB → ℝ → ℝ) (yA yB : ℝ) (σ : List (Job nA nB))
    (hrule : IsAPrioritySeq p fA fB yA yB σ) : FeasAB p fA fB yA yB σ := by
  refine ⟨fun h hh => ?_, fun k hk => ?_⟩
  · obtain ⟨m, hm, hg, hct⟩ := pm112_pos p σ (Sum.inl h) hh
    rw [hct]
    rcases hrule m hm with ⟨h', hh', hle⟩ | ⟨k', hk', _, _⟩
    · rw [hg] at hh'
      have : h' = h := (Sum.inl_injective hh').symm
      subst this; exact hle
    · rw [hg] at hk'; exact absurd hk' (by simp)
  · obtain ⟨m, hm, hg, hct⟩ := pm112_pos p σ (Sum.inr k) hk
    rw [hct]
    rcases hrule m hm with ⟨h', hh', _⟩ | ⟨k', hk', hle, _⟩
    · rw [hg] at hh'; exact absurd hh' (by simp)
    · rw [hg] at hk'
      have : k' = k := (Sum.inr_injective hk').symm
      subst this; exact hle

lemma build_bPriority {nA nB : ℕ} (p : Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ)
    (hfA : ∀ h, Monotone (fA h)) (hfB : ∀ k, Monotone (fB k)) (yA yB : ℝ) :
    ∀ (n : ℕ) (l : List (Job nA nB)), l.length = n → l.Nodup → FeasAB p fA fB yA yB l →
      ∃ σ : List (Job nA nB), σ.Perm l ∧ IsBPrioritySeq p fA fB yA yB σ := by
  intro n
  induction n with
  | zero =>
    intro l hlen _ _
    have : l = [] := List.length_eq_zero_iff.1 hlen
    subst this
    exact ⟨[], List.Perm.refl _, fun m hm => absurd hm (by simp)⟩
  | succ n ih =>
    intro l hlen hnd hfeas
    have hne : l ≠ [] := by intro h; subst h; simp at hlen
    have hz : ∃ z ∈ l,
        (∃ k : Fin nB, z = Sum.inr k ∧ fB k (l.map p).sum ≤ yB) ∨
        (∃ h : Fin nA, z = Sum.inl h ∧ fA h (l.map p).sum ≤ yA ∧
          ∀ k : Fin nB, Sum.inr k ∈ l → yB < fB k (l.map p).sum) := by
      classical
      by_cases hel : ∃ k : Fin nB, Sum.inr k ∈ l ∧ fB k (l.map p).sum ≤ yB
      · obtain ⟨k, hk, hle⟩ := hel
        exact ⟨Sum.inr k, hk, Or.inl ⟨k, rfl, hle⟩⟩
      · obtain ⟨y, hy, hyc⟩ := pm112_last_cost p l hnd hne
        rcases y with h0 | k0
        · have hle : fA h0 (l.map p).sum ≤ yA := by
            rw [← hyc]; exact hfeas.1 h0 hy
          refine ⟨Sum.inl h0, hy, Or.inr ⟨h0, rfl, hle, fun k hk => ?_⟩⟩
          by_contra hcon
          exact hel ⟨k, hk, not_lt.1 hcon⟩
        · exfalso
          have hle : fB k0 (l.map p).sum ≤ yB := by
            rw [← hyc]; exact hfeas.2 k0 hy
          exact hel ⟨k0, hy, hle⟩
    obtain ⟨z, hzl, hcond⟩ := hz
    obtain ⟨l'', hperm0, hl''⟩ := pm112_erase_ex p hp l hnd z hzl
    have hlen'' : l''.length = n := by
      have := hperm0.length_eq; simp at this; omega
    have hnd'' : l''.Nodup := (List.nodup_append.1 (hperm0.nodup_iff.1 hnd)).1
    have hfeas'' : FeasAB p fA fB yA yB l'' :=
      ⟨fun h hh => (hfA h (hl'' _ hh).2.2).trans (hfeas.1 h (hl'' _ hh).1),
       fun k hk => (hfB k (hl'' _ hk).2.2).trans (hfeas.2 k (hl'' _ hk).1)⟩
    obtain ⟨σ'', hσperm, hσrule⟩ := ih l'' hlen'' hnd'' hfeas''
    have hperm : (σ'' ++ [z]).Perm l := (hσperm.append_right [z]).trans hperm0.symm
    have hsum : ((σ'' ++ [z]).map p).sum = (l.map p).sum := (hperm.map p).sum_eq
    refine ⟨σ'' ++ [z], hperm, (bPriority_append_iff p fA fB yA yB σ'' z).2 ⟨hσrule, ?_⟩⟩
    rw [hsum]
    rcases hcond with ⟨k, hk1, hk2⟩ | ⟨h, hh1, hh2, hh3⟩
    · exact Or.inl ⟨k, hk1, hk2⟩
    · refine Or.inr ⟨h, hh1, hh2, fun k hk => hh3 k ?_⟩
      exact hperm.mem_iff.1 (List.mem_toFinset.1 hk)

lemma build_aPriority {nA nB : ℕ} (p : Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ)
    (hfA : ∀ h, Monotone (fA h)) (hfB : ∀ k, Monotone (fB k)) (yA yB : ℝ) :
    ∀ (n : ℕ) (l : List (Job nA nB)), l.length = n → l.Nodup → FeasAB p fA fB yA yB l →
      ∃ σ : List (Job nA nB), σ.Perm l ∧ IsAPrioritySeq p fA fB yA yB σ := by
  intro n
  induction n with
  | zero =>
    intro l hlen _ _
    have : l = [] := List.length_eq_zero_iff.1 hlen
    subst this
    exact ⟨[], List.Perm.refl _, fun m hm => absurd hm (by simp)⟩
  | succ n ih =>
    intro l hlen hnd hfeas
    have hne : l ≠ [] := by intro h; subst h; simp at hlen
    have hz : ∃ z ∈ l,
        (∃ h : Fin nA, z = Sum.inl h ∧ fA h (l.map p).sum ≤ yA) ∨
        (∃ k : Fin nB, z = Sum.inr k ∧ fB k (l.map p).sum ≤ yB ∧
          ∀ h : Fin nA, Sum.inl h ∈ l → yA < fA h (l.map p).sum) := by
      classical
      by_cases hel : ∃ h : Fin nA, Sum.inl h ∈ l ∧ fA h (l.map p).sum ≤ yA
      · obtain ⟨h, hh, hle⟩ := hel
        exact ⟨Sum.inl h, hh, Or.inl ⟨h, rfl, hle⟩⟩
      · obtain ⟨y, hy, hyc⟩ := pm112_last_cost p l hnd hne
        rcases y with h0 | k0
        · exfalso
          have hle : fA h0 (l.map p).sum ≤ yA := by
            rw [← hyc]; exact hfeas.1 h0 hy
          exact hel ⟨h0, hy, hle⟩
        · have hle : fB k0 (l.map p).sum ≤ yB := by
            rw [← hyc]; exact hfeas.2 k0 hy
          refine ⟨Sum.inr k0, hy, Or.inr ⟨k0, rfl, hle, fun h hh => ?_⟩⟩
          by_contra hcon
          exact hel ⟨h, hh, not_lt.1 hcon⟩
    obtain ⟨z, hzl, hcond⟩ := hz
    obtain ⟨l'', hperm0, hl''⟩ := pm112_erase_ex p hp l hnd z hzl
    have hlen'' : l''.length = n := by
      have := hperm0.length_eq; simp at this; omega
    have hnd'' : l''.Nodup := (List.nodup_append.1 (hperm0.nodup_iff.1 hnd)).1
    have hfeas'' : FeasAB p fA fB yA yB l'' :=
      ⟨fun h hh => (hfA h (hl'' _ hh).2.2).trans (hfeas.1 h (hl'' _ hh).1),
       fun k hk => (hfB k (hl'' _ hk).2.2).trans (hfeas.2 k (hl'' _ hk).1)⟩
    obtain ⟨σ'', hσperm, hσrule⟩ := ih l'' hlen'' hnd'' hfeas''
    have hperm : (σ'' ++ [z]).Perm l := (hσperm.append_right [z]).trans hperm0.symm
    have hsum : ((σ'' ++ [z]).map p).sum = (l.map p).sum := (hperm.map p).sum_eq
    refine ⟨σ'' ++ [z], hperm, (aPriority_append_iff p fA fB yA yB σ'' z).2 ⟨hσrule, ?_⟩⟩
    rw [hsum]
    rcases hcond with ⟨h, hh1, hh2⟩ | ⟨k, hk1, hk2, hk3⟩
    · exact Or.inl ⟨h, hh1, hh2⟩
    · refine Or.inr ⟨k, hk1, hk2, fun h hh => hk3 h ?_⟩
      exact hperm.mem_iff.1 (List.mem_toFinset.1 hh)

lemma nondomFor_of_feasAB {nA nB : ℕ} (hA : 0 < nA) (hB : 0 < nB)
    (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ)
    (yA yB : ℝ) (l0 σ : List (Job nA nB))
    (hl0 : IsNondominatedFor hA hB p fA fB (yA, yB) l0)
    (hperm : σ.Perm l0) (hfeas : FeasAB p fA fB yA yB σ) :
    IsNondominatedFor hA hB p fA fB (yA, yB) σ := by
  obtain ⟨⟨hl0_sched, hl0_nd⟩, hl0_A, hl0_B⟩ := hl0
  dsimp at hl0_A hl0_B
  have hσ_sched : IsSchedule Finset.univ σ :=
    ⟨hperm.nodup_iff.2 hl0_sched.1, fun x => by rw [hperm.mem_iff, hl0_sched.2 x]⟩
  have hAle : maxCostA hA p fA σ ≤ yA :=
    Finset.sup'_le _ _ (fun h _ => hfeas.1 h ((hσ_sched.2 _).2 (Finset.mem_univ _)))
  have hBle : maxCostB hB p fB σ ≤ yB :=
    Finset.sup'_le _ _ (fun k _ => hfeas.2 k ((hσ_sched.2 _).2 (Finset.mem_univ _)))
  have hAeq : maxCostA hA p fA σ = yA := by
    by_contra hne
    have hlt : maxCostA hA p fA σ < yA := lt_of_le_of_ne hAle hne
    exact hl0_nd ⟨σ, hσ_sched, by linarith, by linarith, Or.inl (by linarith)⟩
  have hBeq : maxCostB hB p fB σ = yB := by
    by_contra hne
    have hlt : maxCostB hB p fB σ < yB := lt_of_le_of_ne hBle hne
    exact hl0_nd ⟨σ, hσ_sched, by linarith, by linarith, Or.inr (by linarith)⟩
  refine ⟨⟨hσ_sched, ?_⟩, hAeq, hBeq⟩
  rintro ⟨l', hl', h1, h2, h3⟩
  rw [hAeq] at h1 h3
  rw [hBeq] at h2 h3
  rw [← hl0_A] at h1 h3
  rw [← hl0_B] at h2 h3
  exact hl0_nd ⟨l', hl', h1, h2, h3⟩

lemma feasAB_of_nondomFor {nA nB : ℕ} (hA : 0 < nA) (hB : 0 < nB)
    (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ)
    (yA yB : ℝ) (l0 : List (Job nA nB))
    (hl0 : IsNondominatedFor hA hB p fA fB (yA, yB) l0) :
    FeasAB p fA fB yA yB l0 := by
  obtain ⟨_, hl0_A, hl0_B⟩ := hl0
  dsimp at hl0_A hl0_B
  refine ⟨fun h _ => ?_, fun k _ => ?_⟩
  · rw [← hl0_A]
    exact Finset.le_sup' (fun h => fA h (completionTime p l0 (Sum.inl h))) (Finset.mem_univ h)
  · rw [← hl0_B]
    exact Finset.le_sup' (fun k => fB k (completionTime p l0 (Sum.inr k))) (Finset.mem_univ k)

theorem solution {nA nB : ℕ} (hA : 0 < nA) (hB : 0 < nB) (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ)
    (hfA : ∀ h, Monotone (fA h)) (hfB : ∀ k, Monotone (fB k))
    (yA yB yA' yB' : ℝ)
    (hy : IsNondominatedPair hA hB p fA fB (yA, yB))
    (hy' : IsNondominatedPair hA hB p fA fB (yA', yB'))
    (hAlt : yA < yA') (hBgt : yB' < yB) :
    ∃ σ σ' : List (TwoAgentSched.MaxMax.Job nA nB),
      IsNondominatedFor hA hB p fA fB (yA, yB) σ ∧
      IsNondominatedFor hA hB p fA fB (yA', yB') σ' ∧
      ∀ (h : Fin nA) (k : Fin nB),
        Precedes σ (Sum.inr k) (Sum.inl h) → Precedes σ' (Sum.inr k) (Sum.inl h) := by
  obtain ⟨l0, hl0⟩ := hy
  obtain ⟨l0', hl0'⟩ := hy'
  obtain ⟨σ, hσperm, hσrule⟩ := build_bPriority p hp fA fB hfA hfB yA yB l0.length l0 rfl
    hl0.1.1.1 (feasAB_of_nondomFor hA hB p fA fB yA yB l0 hl0)
  obtain ⟨σ', hσ'perm, hσ'rule⟩ := build_aPriority p hp fA fB hfA hfB yA' yB' l0'.length l0' rfl
    hl0'.1.1.1 (feasAB_of_nondomFor hA hB p fA fB yA' yB' l0' hl0')
  have hσfeas := feasAB_of_bPriority p fA fB yA yB σ hσrule
  have hσ'feas := feasAB_of_aPriority p fA fB yA' yB' σ' hσ'rule
  have hσ_nd := nondomFor_of_feasAB hA hB p fA fB yA yB l0 σ hl0 hσperm hσfeas
  have hσ'_nd := nondomFor_of_feasAB hA hB p fA fB yA' yB' l0' σ' hl0' hσ'perm hσ'feas
  refine ⟨σ, σ', hσ_nd, hσ'_nd, fun h k hprec => ?_⟩
  by_contra hnot
  have hhσ : Sum.inl h ∈ σ := (hσ_nd.1.1.2 _).2 (Finset.mem_univ _)
  have hkσ : Sum.inr k ∈ σ := (hσ_nd.1.1.2 _).2 (Finset.mem_univ _)
  have hhσ' : Sum.inl h ∈ σ' := (hσ'_nd.1.1.2 _).2 (Finset.mem_univ _)
  have hkσ' : Sum.inr k ∈ σ' := (hσ'_nd.1.1.2 _).2 (Finset.mem_univ _)
  -- From hprec : Precedes σ (Sum.inr k) (Sum.inl h) and hσrule, get yB < fB k (C_h(σ))
  have hm : σ.idxOf (Sum.inl h) < σ.length := List.idxOf_lt_length_iff.2 hhσ
  have hg : σ[σ.idxOf (Sum.inl h)] = Sum.inl h := List.getElem_idxOf _
  have hk_take : Sum.inr k ∈ (σ.take (σ.idxOf (Sum.inl h) + 1)).toFinset := by
    rw [List.mem_toFinset, List.mem_take_iff_idxOf_lt hkσ]
    unfold Precedes at hprec
    omega
  have hyB_lt : yB < fB k (completionTime p σ (Sum.inl h)) := by
    rw [pm112_ct_eq_ca_idxOf]
    rcases hσrule (σ.idxOf (Sum.inl h)) hm with ⟨k', hk', _⟩ | ⟨h', hh', _, hlt⟩
    · rw [hg] at hk'; exact absurd hk' (by simp)
    · exact hlt k hk_take
  -- From hnot : ¬ Precedes σ' (Sum.inr k) (Sum.inl h) and hσ'rule, get yA' < fA h (C_k(σ'))
  have hm' : σ'.idxOf (Sum.inr k) < σ'.length := List.idxOf_lt_length_iff.2 hkσ'
  have hg' : σ'[σ'.idxOf (Sum.inr k)] = Sum.inr k := List.getElem_idxOf _
  have hh_take' : Sum.inl h ∈ (σ'.take (σ'.idxOf (Sum.inr k) + 1)).toFinset := by
    rw [List.mem_toFinset, List.mem_take_iff_idxOf_lt hhσ']
    unfold Precedes at hnot
    omega
  have hyA'_lt : yA' < fA h (completionTime p σ' (Sum.inr k)) := by
    rw [pm112_ct_eq_ca_idxOf]
    rcases hσ'rule (σ'.idxOf (Sum.inr k)) hm' with ⟨h', hh', _⟩ | ⟨k', hk', _, hlt⟩
    · rw [hg'] at hh'; exact absurd hh' (by simp)
    · exact hlt h hh_take'
  -- Now compare C_h(σ) and C_k(σ') via monotonicity of fA h and fB k
  have hfB_le : fB k (completionTime p σ' (Sum.inr k)) ≤ yB' := hσ'feas.2 k hkσ'
  have hfA_le : fA h (completionTime p σ (Sum.inl h)) ≤ yA := hσfeas.1 h hhσ
  have h1 : fB k (completionTime p σ' (Sum.inr k)) < fB k (completionTime p σ (Sum.inl h)) := by
    linarith
  have h2 : fA h (completionTime p σ (Sum.inl h)) < fA h (completionTime p σ' (Sum.inr k)) := by
    linarith
  have hct1 : completionTime p σ' (Sum.inr k) < completionTime p σ (Sum.inl h) := by
    by_contra hle
    exact not_le_of_gt h1 (hfB k (not_lt.1 hle))
  have hct2 : completionTime p σ (Sum.inl h) < completionTime p σ' (Sum.inr k) := by
    by_contra hle
    exact not_le_of_gt h2 (hfA h (not_lt.1 hle))
  linarith
