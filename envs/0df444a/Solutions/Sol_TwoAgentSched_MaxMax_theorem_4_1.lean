-- Prove2me | solution 1 for TwoAgentSched.MaxMax.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:51:55.15351+00:00
-- url     : https://prove2.me/submissions/b36097d8-f4b0-4f85-89ff-fe4c2895d497

import Mathlib
import Definitions.Def_TwoAgentSched_MaxMax_BackwardRule

set_option autoImplicit false
open TwoAgentSched.MaxMax MooreLateJobs.Shared

section generic
variable {ι : Type*} [DecidableEq ι] (p : ι → ℝ)

lemma tas_ca_append_left (l₁ l₂ : List ι) (m : ℕ) (hm : m < l₁.length) :
    completionAt p (l₁ ++ l₂) m = completionAt p l₁ m := by
  unfold completionAt
  rw [List.take_append_of_le_length (by omega)]

lemma tas_ct_append_left (l₁ l₂ : List ι) (x : ι) (hx : x ∈ l₁) :
    completionTime p (l₁ ++ l₂) x = completionTime p l₁ x := by
  unfold completionTime
  rw [List.idxOf_append_of_mem hx]
  exact tas_ca_append_left p l₁ l₂ _ (List.idxOf_lt_length_iff.mpr hx)

lemma tas_ct_last (l : List ι) (z : ι) (hz : z ∉ l) :
    completionTime p (l ++ [z]) z = ((l ++ [z]).map p).sum := by
  unfold completionTime completionAt
  have h1 : (l ++ [z]).idxOf z = l.length := by
    rw [List.idxOf_append_of_notMem hz]; simp
  rw [h1]
  have h2 : (l ++ [z]).take (l.length + 1) = l ++ [z] := List.take_of_length_le (by simp)
  rw [h2]

lemma tas_ct_erase_le (hp : ∀ j, 0 ≤ p j) (l : List ι) (hnd : l.Nodup) (z x : ι)
    (hz : z ∈ l) (hx : x ∈ l) (hxz : x ≠ z) :
    completionTime p (l.erase z) x ≤ completionTime p l x := by
  obtain ⟨a, b, rfl⟩ := List.append_of_mem hz
  have hnd' := List.nodup_append.1 hnd
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
  · rw [tas_ct_append_left p a b x hxa, tas_ct_append_left p a (z :: b) x hxa]
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

lemma tas_last_cost (hp : ∀ j, 0 ≤ p j) (l : List ι) (hnd : l.Nodup) (hne : l ≠ []) :
    ∃ y ∈ l, completionTime p l y = (l.map p).sum := by
  obtain ⟨L, y, hL⟩ := (List.eq_nil_or_concat l).resolve_left hne
  rw [List.concat_eq_append] at hL
  subst hL
  refine ⟨y, by simp, ?_⟩
  have hy : y ∉ L := fun h => (List.nodup_append.1 hnd).2.2 y h y (by simp) rfl
  exact tas_ct_last p L y hy

lemma tas_pos (l : List ι) (x : ι) (hx : x ∈ l) :
    ∃ m, ∃ hm : m < l.length, l[m] = x ∧ completionTime p l x = completionAt p l m :=
  ⟨l.idxOf x, List.idxOf_lt_length_iff.2 hx, List.getElem_idxOf _, rfl⟩

lemma tas_erase_ex (hp : ∀ j, 0 ≤ p j) (l : List ι) (hnd : l.Nodup) (z : ι) (hz : z ∈ l) :
    ∃ l'', l.Perm (l'' ++ [z]) ∧
      ∀ x ∈ l'', x ∈ l ∧ x ≠ z ∧ completionTime p l'' x ≤ completionTime p l x := by
  refine ⟨l.erase z, ?_, fun x hx => ?_⟩
  · exact (List.perm_cons_erase hz).trans (List.perm_append_singleton z _).symm
  · rw [hnd.mem_erase_iff] at hx
    exact ⟨hx.2, hx.1, tas_ct_erase_le p hp l hnd z x hz hx.2 hx.1⟩

end generic

/-- the last-position condition of the backward rule -/
def tasLastOK {nA nB : ℕ} (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ)
    (Q : ℝ) (σ : List (Job nA nB)) (z : Job nA nB) : Prop :=
  ((∃ k : Fin nB, Sum.inr k ∈ (σ ++ [z]).toFinset ∧ fB k ((σ ++ [z]).map p).sum ≤ Q) →
      ∃ k : Fin nB, z = Sum.inr k ∧ fB k ((σ ++ [z]).map p).sum ≤ Q) ∧
    ((¬ ∃ k : Fin nB, Sum.inr k ∈ (σ ++ [z]).toFinset ∧ fB k ((σ ++ [z]).map p).sum ≤ Q) →
      ∃ h : Fin nA, z = Sum.inl h ∧
        ∀ h' : Fin nA, Sum.inl h' ∈ (σ ++ [z]).toFinset →
          fA h ((σ ++ [z]).map p).sum ≤ fA h' ((σ ++ [z]).map p).sum)

lemma tas_rule_append_iff {nA nB : ℕ} (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ)
    (fB : Fin nB → ℝ → ℝ) (Q : ℝ) (σ : List (Job nA nB)) (z : Job nA nB) :
    IsBackwardRuleSeq p fA fB Q (σ ++ [z]) ↔
      IsBackwardRuleSeq p fA fB Q σ ∧ tasLastOK p fA fB Q σ z := by
  have hT : ∀ m, m < σ.length → (σ ++ [z]).take (m + 1) = σ.take (m + 1) :=
    fun m hm => List.take_append_of_le_length (by omega)
  have hCA : ∀ m, m < σ.length → completionAt p (σ ++ [z]) m = completionAt p σ m :=
    fun m hm => tas_ca_append_left p σ [z] m hm
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

/-- B-feasibility on the members of a list -/
def tasFeasB {nA nB : ℕ} (p : Job nA nB → ℝ) (fB : Fin nB → ℝ → ℝ) (Q : ℝ)
    (l : List (Job nA nB)) : Prop :=
  ∀ k : Fin nB, Sum.inr k ∈ l → fB k (completionTime p l (Sum.inr k)) ≤ Q

lemma tas_core {nA nB : ℕ} (p : Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ) (hfA : ∀ h, Monotone (fA h))
    (hfB : ∀ k, Monotone (fB k)) (Q : ℝ) :
    ∀ σ : List (Job nA nB), IsBackwardRuleSeq p fA fB Q σ → σ.Nodup →
      ∀ l' : List (Job nA nB), l'.Perm σ → tasFeasB p fB Q l' → ∀ v : ℝ,
        (∀ h : Fin nA, Sum.inl h ∈ l' → fA h (completionTime p l' (Sum.inl h)) ≤ v) →
        ∀ h : Fin nA, Sum.inl h ∈ σ → fA h (completionTime p σ (Sum.inl h)) ≤ v := by
  intro σ
  induction σ using List.reverseRecOn with
  | nil => intro _ _ _ _ _ _ _ h hh; simp at hh
  | append_singleton σ z ih =>
    intro hrule hnd l' hperm hfeas v hv h hh
    obtain ⟨hr0, hlast⟩ := (tas_rule_append_iff p fA fB Q σ z).1 hrule
    have hnd2 := List.nodup_append.1 hnd
    have hσnd : σ.Nodup := hnd2.1
    have hzσ : z ∉ σ := fun hz => hnd2.2.2 z hz z (by simp) rfl
    have hzl' : z ∈ l' := hperm.mem_iff.2 (by simp)
    have hl'nd : l'.Nodup := hperm.nodup_iff.2 hnd
    obtain ⟨l'', hperm0, hl''⟩ := tas_erase_ex p hp l' hl'nd z hzl'
    have hperm'' : l''.Perm σ :=
      (List.perm_append_right_iff [z]).1 (hperm0.symm.trans hperm)
    have hfeas'' : tasFeasB p fB Q l'' := fun k hk =>
      (hfB k (hl'' _ hk).2.2).trans (hfeas k (hl'' _ hk).1)
    have hv'' : ∀ h' : Fin nA, Sum.inl h' ∈ l'' →
        fA h' (completionTime p l'' (Sum.inl h')) ≤ v := fun h' hh' =>
      (hfA h' (hl'' _ hh').2.2).trans (hv h' (hl'' _ hh').1)
    have IH := ih hr0 hσnd l'' hperm'' hfeas'' v hv''
    rcases List.mem_append.1 hh with hhσ | hhz
    · rw [tas_ct_append_left p σ [z] _ hhσ]
      exact IH h hhσ
    · have hz : z = Sum.inl h := (List.mem_singleton.1 hhz).symm
      subst hz
      rw [tas_ct_last p σ _ hzσ]
      obtain ⟨y, hy, hyc⟩ := tas_last_cost p hp l' hl'nd (List.ne_nil_of_mem hzl')
      have hsum : (l'.map p).sum = ((σ ++ [Sum.inl h]).map p).sum := (hperm.map p).sum_eq
      rw [hsum] at hyc
      have hel : ¬ ∃ k : Fin nB, Sum.inr k ∈ (σ ++ [Sum.inl h]).toFinset ∧
          fB k ((σ ++ [Sum.inl h]).map p).sum ≤ Q := by
        rintro ⟨k, hk1, hk2⟩
        obtain ⟨k', hk'⟩ := hlast.1 ⟨k, hk1, hk2⟩
        exact absurd hk'.1 (by simp)
      obtain ⟨h0, hh0, hmin⟩ := hlast.2 hel
      have hh0' : h0 = h := (Sum.inl_injective hh0).symm
      subst hh0'
      have hyU : y ∈ σ ++ [Sum.inl h0] := hperm.mem_iff.1 hy
      rcases y with h' | k'
      · have := hv h' hy
        rw [hyc] at this
        exact (hmin h' (List.mem_toFinset.2 hyU)).trans this
      · exfalso
        have := hfeas k' hy
        rw [hyc] at this
        exact hel ⟨k', List.mem_toFinset.2 hyU, this⟩

lemma tas_feasible_of_rule {nA nB : ℕ} (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ)
    (fB : Fin nB → ℝ → ℝ) (Q : ℝ) (l : List (Job nA nB))
    (hrule : IsBackwardRuleSeq p fA fB Q l) : tasFeasB p fB Q l := by
  intro k hk
  obtain ⟨m, hm, hg, hct⟩ := tas_pos p l (Sum.inr k) hk
  obtain ⟨h1, h2⟩ := hrule m hm
  rw [hct]
  by_cases hel : ∃ k' : Fin nB, Sum.inr k' ∈ (l.take (m + 1)).toFinset ∧
      fB k' (completionAt p l m) ≤ Q
  · obtain ⟨k', hk', hle⟩ := h1 hel
    rw [hg] at hk'
    have : k' = k := (Sum.inr_injective hk').symm
    subst this
    exact hle
  · obtain ⟨h, hh, _⟩ := h2 hel
    rw [hg] at hh
    exact absurd hh (by simp)

lemma tas_build {nA nB : ℕ} (p : Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ)
    (hfB : ∀ k, Monotone (fB k)) (Q : ℝ) :
    ∀ n : ℕ, ∀ l' : List (Job nA nB), l'.length = n → l'.Nodup → tasFeasB p fB Q l' →
      ∃ σ : List (Job nA nB), σ.Perm l' ∧ IsBackwardRuleSeq p fA fB Q σ := by
  intro n
  induction n with
  | zero =>
    intro l' hlen _ _
    have : l' = [] := List.length_eq_zero_iff.1 hlen
    subst this
    exact ⟨[], List.Perm.refl _, fun m hm => absurd hm (by simp)⟩
  | succ n ih =>
    intro l' hlen hnd hfeas
    have hne : l' ≠ [] := by intro h; subst h; simp at hlen
    -- choose the job to be placed last
    have hz : ∃ z ∈ l',
        ((∃ k : Fin nB, Sum.inr k ∈ l' ∧ fB k (l'.map p).sum ≤ Q) →
          ∃ k : Fin nB, z = Sum.inr k ∧ fB k (l'.map p).sum ≤ Q) ∧
        ((¬ ∃ k : Fin nB, Sum.inr k ∈ l' ∧ fB k (l'.map p).sum ≤ Q) →
          ∃ h : Fin nA, z = Sum.inl h ∧
            ∀ h' : Fin nA, Sum.inl h' ∈ l' → fA h (l'.map p).sum ≤ fA h' (l'.map p).sum) := by
      classical
      by_cases hel : ∃ k : Fin nB, Sum.inr k ∈ l' ∧ fB k (l'.map p).sum ≤ Q
      · obtain ⟨k, hk, hle⟩ := hel
        exact ⟨Sum.inr k, hk, fun _ => ⟨k, rfl, hle⟩, fun hn => absurd ⟨k, hk, hle⟩ hn⟩
      · obtain ⟨y, hy, hyc⟩ := tas_last_cost p hp l' hnd hne
        rcases y with h' | k'
        · obtain ⟨h0, hh0, hmin⟩ := Finset.exists_min_image
            (Finset.univ.filter (fun h : Fin nA => Sum.inl h ∈ l')) (fun h => fA h (l'.map p).sum)
            ⟨h', by simp [hy]⟩
          rw [Finset.mem_filter] at hh0
          exact ⟨Sum.inl h0, hh0.2, fun hh => absurd hh hel,
            fun _ => ⟨h0, rfl, fun h' hh' => hmin h' (by simp [hh'])⟩⟩
        · exfalso
          have := hfeas k' hy
          rw [hyc] at this
          exact hel ⟨k', hy, this⟩
    obtain ⟨z, hzl, hz1, hz2⟩ := hz
    obtain ⟨l'', hperm0, hl''⟩ := tas_erase_ex p hp l' hnd z hzl
    have hlen'' : l''.length = n := by
      have := hperm0.length_eq
      simp at this
      omega
    have hnd'' : l''.Nodup :=
      (List.nodup_append.1 (hperm0.nodup_iff.1 hnd)).1
    have hfeas'' : tasFeasB p fB Q l'' := fun k hk =>
      (hfB k (hl'' _ hk).2.2).trans (hfeas k (hl'' _ hk).1)
    obtain ⟨σ'', hσperm, hσrule⟩ := ih l'' hlen'' hnd'' hfeas''
    have hperm : (σ'' ++ [z]).Perm l' :=
      ((hσperm.append_right [z]).trans hperm0.symm)
    have hsum : ((σ'' ++ [z]).map p).sum = (l'.map p).sum := (hperm.map p).sum_eq
    have hmem : ∀ x, x ∈ (σ'' ++ [z]).toFinset ↔ x ∈ l' := fun x => by
      rw [List.mem_toFinset]; exact hperm.mem_iff
    refine ⟨σ'' ++ [z], hperm, (tas_rule_append_iff p fA fB Q σ'' z).2 ⟨hσrule, ?_, ?_⟩⟩
    · intro hex
      obtain ⟨k, hk1, hk2⟩ := hex
      rw [hmem] at hk1
      rw [hsum] at hk2 ⊢
      exact hz1 ⟨k, hk1, hk2⟩
    · intro hnot
      rw [hsum]
      have hel : ¬ ∃ k : Fin nB, Sum.inr k ∈ l' ∧ fB k (l'.map p).sum ≤ Q := by
        rintro ⟨k, hk1, hk2⟩
        exact hnot ⟨k, (hmem _).2 hk1, by rw [hsum]; exact hk2⟩
      obtain ⟨h, hh1, hh2⟩ := hz2 hel
      exact ⟨h, hh1, fun h' hh' => hh2 h' ((hmem _).1 hh')⟩

theorem solution {nA nB : ℕ} (hA : 0 < nA) (p : Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ) (hfA : ∀ h, Monotone (fA h))
    (hfB : ∀ k, Monotone (fB k)) (Q : ℝ) :
    (∀ l : List (Job nA nB), MooreLateJobs.Shared.IsSchedule Finset.univ l →
      IsBackwardRuleSeq p fA fB Q l → IsOptimal hA p fA fB Q l) ∧
    ((∃ l : List (Job nA nB), MooreLateJobs.Shared.IsSchedule Finset.univ l ∧
        IsBackwardRuleSeq p fA fB Q l) ↔
      ∃ l : List (Job nA nB), IsFeasible p fB Q l) := by
  have hfeasible : ∀ l : List (Job nA nB), IsSchedule Finset.univ l →
      IsBackwardRuleSeq p fA fB Q l → IsFeasible p fB Q l := fun l hl hr =>
    ⟨hl, fun k => tas_feasible_of_rule p fA fB Q l hr k ((hl.2 _).2 (Finset.mem_univ _))⟩
  refine ⟨fun l hl hr => ⟨hfeasible l hl hr, fun l' hl' => ?_⟩, ⟨?_, ?_⟩⟩
  · have hperm : l'.Perm l := by
      rw [List.perm_ext_iff_of_nodup hl'.1.1 hl.1]
      intro x
      rw [hl'.1.2 x, hl.2 x]
    have hfe' : tasFeasB p fB Q l' := fun k _ => hl'.2 k
    have hcore := tas_core p hp fA fB hfA hfB Q l hr hl.1 l' hperm hfe'
      (maxCostA hA p fA l') (fun h _ => Finset.le_sup'
        (fun h => fA h (completionTime p l' (Sum.inl h))) (Finset.mem_univ h))
    exact Finset.sup'_le _ _ (fun h _ => hcore h ((hl.2 _).2 (Finset.mem_univ _)))
  · rintro ⟨l, hl, hr⟩
    exact ⟨l, hfeasible l hl hr⟩
  · rintro ⟨l', hl'⟩
    obtain ⟨σ, hσperm, hσrule⟩ :=
      tas_build p hp fA fB hfB Q l'.length l' rfl hl'.1.1 (fun k _ => hl'.2 k)
    refine ⟨σ, ⟨hσperm.nodup_iff.2 hl'.1.1, fun x => ?_⟩, hσrule⟩
    rw [hσperm.mem_iff, hl'.1.2 x]
