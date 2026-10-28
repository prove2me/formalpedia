-- Prove2me | solution 1 for TwoAgentSched.ParetoMax.exchange
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:24:06.043711+00:00
-- url     : https://prove2.me/submissions/1a6d9954-e32d-4de9-86be-6a439c255659

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

lemma pme_ca_append_left (l₁ l₂ : List ι) (m : ℕ) (hm : m < l₁.length) :
    completionAt p (l₁ ++ l₂) m = completionAt p l₁ m := by
  unfold completionAt
  rw [List.take_append_of_le_length (by omega)]

lemma pme_ct_append_left (l₁ l₂ : List ι) (x : ι) (hx : x ∈ l₁) :
    completionTime p (l₁ ++ l₂) x = completionTime p l₁ x := by
  unfold completionTime
  rw [List.idxOf_append_of_mem hx]
  exact pme_ca_append_left p l₁ l₂ _ (List.idxOf_lt_length_iff.mpr hx)

lemma pme_ct_last (l : List ι) (z : ι) (hz : z ∉ l) :
    completionTime p (l ++ [z]) z = ((l ++ [z]).map p).sum := by
  unfold completionTime completionAt
  have h1 : (l ++ [z]).idxOf z = l.length := by
    rw [List.idxOf_append_of_notMem hz]; simp
  rw [h1]
  have h2 : (l ++ [z]).take (l.length + 1) = l ++ [z] := List.take_of_length_le (by simp)
  rw [h2]

lemma pme_ct_erase_le (hp : ∀ j, 0 ≤ p j) (l : List ι) (hnd : l.Nodup) (z x : ι)
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
  · rw [pme_ct_append_left p a b x hxa, pme_ct_append_left p a (z :: b) x hxa]
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

lemma pme_beq_eq {nA nB : ℕ} (a z : Job nA nB) :
    @BEq.beq (Job nA nB) instBEqOfDecidableEq a z = (a == z) := by
  change decide (a = z) = (a == z)
  by_cases h : a = z
  · subst h; rw [decide_eq_true rfl, beq_self_eq_true]
  · rw [decide_eq_false h, beq_false_of_ne h]

lemma pme_erase_eq {nA nB : ℕ} (l : List (Job nA nB)) (z : Job nA nB) :
    @List.erase (Job nA nB) instBEqOfDecidableEq l z = l.erase z := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.erase_cons, pme_beq_eq, ih]

lemma pme_ct_erase_le' {nA nB : ℕ} (p : Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (l : List (Job nA nB)) (hnd : l.Nodup) (z x : Job nA nB)
    (hz : z ∈ l) (hx : x ∈ l) (hxz : x ≠ z) :
    completionTime p (l.erase z) x ≤ completionTime p l x := by
  rw [← pme_erase_eq]
  exact pme_ct_erase_le p hp l hnd z x hz hx hxz

lemma precedes_append_left {nA nB : ℕ} (l₁ l₂ : List (Job nA nB)) (x y : Job nA nB)
    (hx : x ∈ l₁) (hy : y ∈ l₁) :
    Precedes (l₁ ++ l₂) x y ↔ Precedes l₁ x y := by
  unfold Precedes
  rw [List.idxOf_append_of_mem hx, List.idxOf_append_of_mem hy]

lemma idxOf_erase_eq {nA nB : ℕ} (a b : List (Job nA nB)) (z u : Job nA nB)
    (hnd : (a ++ z :: b).Nodup) (hu : u ∈ a ++ b) :
    (a ++ z :: b).idxOf u =
      if (a ++ b).idxOf u < a.length then (a ++ b).idxOf u else (a ++ b).idxOf u + 1 := by
  rcases List.mem_append.1 hu with hua | hub
  · have hlt : a.idxOf u < a.length := List.idxOf_lt_length_iff.2 hua
    rw [List.idxOf_append_of_mem hua, List.idxOf_append_of_mem hua, if_pos hlt]
  · have hua : u ∉ a := fun h => (List.nodup_append.1 hnd).2.2 u h u (by simp [hub]) rfl
    have huz : u ≠ z := fun h => by
      subst h
      exact (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1 hub
    rw [List.idxOf_append_of_notMem hua, List.idxOf_append_of_notMem hua,
      List.idxOf_cons_ne _ (Ne.symm huz)]
    have hnotlt : ¬ (a.length + b.idxOf u < a.length) := by omega
    rw [if_neg hnotlt]
    omega

lemma precedes_erase_iff {nA nB : ℕ} (l : List (Job nA nB)) (hnd : l.Nodup)
    (z x y : Job nA nB) (hz : z ∈ l) (hx : x ∈ l.erase z) (hy : y ∈ l.erase z) :
    Precedes (l.erase z) x y ↔ Precedes l x y := by
  obtain ⟨a, b, rfl⟩ := List.append_of_mem hz
  have hza : z ∉ a := fun h => (List.nodup_append.1 hnd).2.2 z h z (by simp) rfl
  have herase : (a ++ z :: b).erase z = a ++ b := by
    rw [List.erase_append_right _ hza]; simp
  rw [herase] at hx hy ⊢
  unfold Precedes
  rw [idxOf_erase_eq a b z x hnd hx, idxOf_erase_eq a b z y hnd hy]
  split_ifs <;> omega

lemma precedes_last {nA nB : ℕ} (l : List (Job nA nB)) (x z : Job nA nB)
    (hx : x ∈ l) (hz : z ∉ l) :
    Precedes (l ++ [z]) x z := by
  unfold Precedes
  rw [List.idxOf_append_of_mem hx, List.idxOf_append_of_notMem hz]
  simp [List.idxOf_lt_length_iff.2 hx]

lemma pme_dominate_of_no_exchange {nA nB : ℕ} (p : Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j) :
    ∀ (n : ℕ) (σ σ' : List (Job nA nB)),
      σ.length = n → σ.Nodup → σ'.Perm σ →
      (∀ (h : Fin nA) (k : Fin nB),
        Sum.inl h ∈ σ → Sum.inr k ∈ σ →
        Precedes σ (Sum.inl h) (Sum.inr k) → ¬ Precedes σ' (Sum.inr k) (Sum.inl h)) →
      ∃ τ : List (Job nA nB),
        τ.Perm σ ∧
        (∀ h : Fin nA, Sum.inl h ∈ τ →
          completionTime p τ (Sum.inl h) ≤ completionTime p σ (Sum.inl h)) ∧
        (∀ k : Fin nB, Sum.inr k ∈ τ →
          completionTime p τ (Sum.inr k) ≤ completionTime p σ' (Sum.inr k)) := by
  intro n
  induction n with
  | zero =>
    intro σ σ' hlen _ _ _
    have : σ = [] := List.length_eq_zero_iff.1 hlen
    subst this
    exact ⟨[], List.Perm.refl _, fun h hh => absurd hh (by simp), fun k hk => absurd hk (by simp)⟩
  | succ n ih =>
    intro σ σ' hlen hnd hperm hnoex
    have hne : σ ≠ [] := by intro h; subst h; simp at hlen
    have hne' : σ' ≠ [] := by
      intro h; subst h
      have := hperm.length_eq; simp at this; omega
    have hnd' : σ'.Nodup := hperm.nodup_iff.2 hnd
    obtain ⟨σ0, zσ, hσ0⟩ := (List.eq_nil_or_concat σ).resolve_left hne
    rw [List.concat_eq_append] at hσ0
    obtain ⟨σ'0, zσ', hσ'0⟩ := (List.eq_nil_or_concat σ').resolve_left hne'
    rw [List.concat_eq_append] at hσ'0
    rcases zσ with h0 | k0
    · -- last job of σ is Sum.inl h0
      subst hσ0
      have hzσ0 : (Sum.inl h0 : Job nA nB) ∉ σ0 := fun h =>
        (List.nodup_append.1 hnd).2.2 _ h _ (by simp) rfl
      have hnd0 : σ0.Nodup := (List.nodup_append.1 hnd).1
      have hlen0 : σ0.length = n := by simp at hlen; omega
      have hzσ' : (Sum.inl h0 : Job nA nB) ∈ σ' := hperm.mem_iff.2 (by simp)
      set σ'' := σ'.erase (Sum.inl h0)
      have hperm0 : σ'.Perm (σ'' ++ [Sum.inl h0]) :=
        (List.perm_cons_erase hzσ').trans (List.perm_append_singleton _ _).symm
      have hperm'' : σ''.Perm σ0 :=
        (List.perm_append_right_iff [Sum.inl h0]).1 (hperm0.symm.trans hperm)
      have hnoex0 : ∀ (h : Fin nA) (k : Fin nB),
          Sum.inl h ∈ σ0 → Sum.inr k ∈ σ0 →
          Precedes σ0 (Sum.inl h) (Sum.inr k) → ¬ Precedes σ'' (Sum.inr k) (Sum.inl h) := by
        intro h k hh hk hprec hprec'
        have hh'' : Sum.inl h ∈ σ'' := hperm''.mem_iff.2 hh
        have hk'' : Sum.inr k ∈ σ'' := hperm''.mem_iff.2 hk
        have hp1 : Precedes (σ0 ++ [Sum.inl h0]) (Sum.inl h) (Sum.inr k) :=
          (precedes_append_left σ0 [Sum.inl h0] _ _ hh hk).2 hprec
        have hp2 : Precedes σ' (Sum.inr k) (Sum.inl h) :=
          (precedes_erase_iff σ' hnd' (Sum.inl h0) _ _ hzσ' hk'' hh'').1 hprec'
        exact hnoex h k (List.mem_append_left _ hh) (List.mem_append_left _ hk) hp1 hp2
      obtain ⟨τ0, hτperm, hτA, hτB⟩ := ih σ0 σ'' hlen0 hnd0 hperm'' hnoex0
      have hpermτ : (τ0 ++ [Sum.inl h0]).Perm (σ0 ++ [Sum.inl h0]) :=
        hτperm.append_right [Sum.inl h0]
      have hzτ0 : (Sum.inl h0 : Job nA nB) ∉ τ0 := fun h => hzσ0 (hτperm.mem_iff.1 h)
      refine ⟨τ0 ++ [Sum.inl h0], hpermτ, ?_, ?_⟩
      · intro h hh
        rcases List.mem_append.1 hh with hh0 | hh0
        · have hhσ0 : Sum.inl h ∈ σ0 := hτperm.mem_iff.1 hh0
          rw [pme_ct_append_left p τ0 [Sum.inl h0] _ hh0,
            pme_ct_append_left p σ0 [Sum.inl h0] _ hhσ0]
          exact hτA h hh0
        · have heq : h = h0 := Sum.inl_injective (List.mem_singleton.1 hh0)
          subst heq
          rw [pme_ct_last p τ0 _ hzτ0, pme_ct_last p σ0 _ hzσ0, (hpermτ.map p).sum_eq]
      · intro k hk
        have hkτ0 : Sum.inr k ∈ τ0 := by
          rcases List.mem_append.1 hk with h1 | h1
          · exact h1
          · simp at h1
        have hkσ'' : Sum.inr k ∈ σ'' := hperm''.mem_iff.2 (hτperm.mem_iff.1 hkτ0)
        have hkσ' : Sum.inr k ∈ σ' := List.mem_of_mem_erase hkσ''
        rw [pme_ct_append_left p τ0 [Sum.inl h0] _ hkτ0]
        exact (hτB k hkτ0).trans (pme_ct_erase_le' p hp σ' hnd' (Sum.inl h0) (Sum.inr k)
          hzσ' hkσ' (by simp))
    · -- last job of σ is Sum.inr k0
      rcases zσ' with h0 | k1
      · -- last job of σ is Sum.inr k0 AND last job of σ' is Sum.inl h0: contradiction!
        exfalso
        subst hσ0 hσ'0
        have hzσ0 : (Sum.inr k0 : Job nA nB) ∉ σ0 := fun h =>
          (List.nodup_append.1 hnd).2.2 _ h _ (by simp) rfl
        have hzσ'0 : (Sum.inl h0 : Job nA nB) ∉ σ'0 := fun h =>
          (List.nodup_append.1 hnd').2.2 _ h _ (by simp) rfl
        have hh0_in : (Sum.inl h0 : Job nA nB) ∈ σ0 := by
          have : (Sum.inl h0 : Job nA nB) ∈ σ0 ++ [Sum.inr k0] := hperm.mem_iff.1 (by simp)
          rcases List.mem_append.1 this with h1 | h1
          · exact h1
          · simp at h1
        have hk0_in : (Sum.inr k0 : Job nA nB) ∈ σ'0 := by
          have : (Sum.inr k0 : Job nA nB) ∈ σ'0 ++ [Sum.inl h0] := hperm.mem_iff.2 (by simp)
          rcases List.mem_append.1 this with h1 | h1
          · exact h1
          · simp at h1
        have hp1 : Precedes (σ0 ++ [Sum.inr k0]) (Sum.inl h0) (Sum.inr k0) :=
          precedes_last σ0 (Sum.inl h0) (Sum.inr k0) hh0_in hzσ0
        have hp2 : Precedes (σ'0 ++ [Sum.inl h0]) (Sum.inr k0) (Sum.inl h0) :=
          precedes_last σ'0 (Sum.inr k0) (Sum.inl h0) hk0_in hzσ'0
        exact hnoex h0 k0 (List.mem_append_left _ hh0_in) (by simp) hp1 hp2
      · -- last job of σ' is Sum.inr k1
        subst hσ'0
        have hzσ'0 : (Sum.inr k1 : Job nA nB) ∉ σ'0 := fun h =>
          (List.nodup_append.1 hnd').2.2 _ h _ (by simp) rfl
        have hnd'0 : σ'0.Nodup := (List.nodup_append.1 hnd').1
        have hzσ : (Sum.inr k1 : Job nA nB) ∈ σ := hperm.mem_iff.1 (by simp)
        set σ'' := σ.erase (Sum.inr k1)
        have hperm0 : σ.Perm (σ'' ++ [Sum.inr k1]) :=
          (List.perm_cons_erase hzσ).trans (List.perm_append_singleton _ _).symm
        have hperm'' : σ'0.Perm σ'' :=
          (List.perm_append_right_iff [Sum.inr k1]).1 (hperm.trans hperm0)
        have hlen'' : σ''.length = n := by
          have := hperm0.length_eq
          simp at this; omega
        have hnd'' : σ''.Nodup := (List.nodup_append.1 (hperm0.nodup_iff.1 hnd)).1
        have hnoex0 : ∀ (h : Fin nA) (k : Fin nB),
            Sum.inl h ∈ σ'' → Sum.inr k ∈ σ'' →
            Precedes σ'' (Sum.inl h) (Sum.inr k) → ¬ Precedes σ'0 (Sum.inr k) (Sum.inl h) := by
          intro h k hh hk hprec hprec'
          have hh'0 : Sum.inl h ∈ σ'0 := hperm''.mem_iff.2 hh
          have hk'0 : Sum.inr k ∈ σ'0 := hperm''.mem_iff.2 hk
          have hp1 : Precedes σ (Sum.inl h) (Sum.inr k) :=
            (precedes_erase_iff σ hnd (Sum.inr k1) _ _ hzσ hh hk).1 hprec
          have hp2 : Precedes (σ'0 ++ [Sum.inr k1]) (Sum.inr k) (Sum.inl h) :=
            (precedes_append_left σ'0 [Sum.inr k1] _ _ hk'0 hh'0).2 hprec'
          exact hnoex h k (List.mem_of_mem_erase hh) (List.mem_of_mem_erase hk) hp1 hp2
        obtain ⟨τ0, hτperm, hτA, hτB⟩ := ih σ'' σ'0 hlen'' hnd'' hperm'' hnoex0
        have hpermτ : (τ0 ++ [Sum.inr k1]).Perm σ :=
          (hτperm.append_right [Sum.inr k1]).trans hperm0.symm
        have hzσ'' : (Sum.inr k1 : Job nA nB) ∉ σ'' := List.Nodup.not_mem_erase hnd
        have hzτ0 : (Sum.inr k1 : Job nA nB) ∉ τ0 := fun h => hzσ'' (hτperm.mem_iff.1 h)
        refine ⟨τ0 ++ [Sum.inr k1], hpermτ, ?_, ?_⟩
        · intro h hh
          have hhτ0 : Sum.inl h ∈ τ0 := by
            rcases List.mem_append.1 hh with h1 | h1
            · exact h1
            · simp at h1
          have hhσ'' : Sum.inl h ∈ σ'' := hτperm.mem_iff.1 hhτ0
          have hhσ : Sum.inl h ∈ σ := List.mem_of_mem_erase hhσ''
          rw [pme_ct_append_left p τ0 [Sum.inr k1] _ hhτ0]
          exact (hτA h hhτ0).trans (pme_ct_erase_le' p hp σ hnd (Sum.inr k1) (Sum.inl h)
            hzσ hhσ (by simp))
        · intro k hk
          rcases List.mem_append.1 hk with hk0' | hk0'
          · have hkσ'0 : Sum.inr k ∈ σ'0 := hperm''.mem_iff.2 (hτperm.mem_iff.1 hk0')
            rw [pme_ct_append_left p τ0 [Sum.inr k1] _ hk0',
              pme_ct_append_left p σ'0 [Sum.inr k1] _ hkσ'0]
            exact hτB k hk0'
          · have heq : k = k1 := Sum.inr_injective (List.mem_singleton.1 hk0')
            subst heq
            have hpermτ' : (τ0 ++ [Sum.inr k]).Perm (σ'0 ++ [Sum.inr k]) :=
              hpermτ.trans hperm.symm
            rw [pme_ct_last p τ0 _ hzτ0, pme_ct_last p σ'0 _ hzσ'0, (hpermτ'.map p).sum_eq]

theorem solution {nA nB : ℕ} (hA : 0 < nA) (hB : 0 < nB) (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ)
    (hfA : ∀ h, Monotone (fA h)) (hfB : ∀ k, Monotone (fB k))
    (σ σ' : List (TwoAgentSched.MaxMax.Job nA nB))
    (hσ : TwoAgentSched.MaxMax.IsNondominated hA hB p fA fB σ) (hσ' : TwoAgentSched.MaxMax.IsNondominated hA hB p fA fB σ')
    (hAlt : TwoAgentSched.MaxMax.maxCostA hA p fA σ < TwoAgentSched.MaxMax.maxCostA hA p fA σ')
    (hBgt : TwoAgentSched.MaxMax.maxCostB hB p fB σ' < TwoAgentSched.MaxMax.maxCostB hB p fB σ) :
    ∃ (h : Fin nA) (k : Fin nB),
      Precedes σ (Sum.inl h) (Sum.inr k) ∧ Precedes σ' (Sum.inr k) (Sum.inl h) := by
  by_contra hcon
  push_neg at hcon
  have hperm : σ'.Perm σ := by
    rw [List.perm_ext_iff_of_nodup hσ'.1.1 hσ.1.1]
    intro x
    rw [hσ'.1.2 x, hσ.1.2 x]
  obtain ⟨τ, hτperm, hτA, hτB⟩ := pme_dominate_of_no_exchange p hp σ.length σ σ' rfl hσ.1.1
    hperm (fun h k _ _ hp1 => hcon h k hp1)
  have hτsched : IsSchedule Finset.univ τ :=
    ⟨hτperm.nodup_iff.2 hσ.1.1, fun x => by rw [hτperm.mem_iff, hσ.1.2 x]⟩
  have hAle : maxCostA hA p fA τ ≤ maxCostA hA p fA σ := by
    unfold maxCostA
    refine Finset.sup'_le _ _ (fun h _ => ?_)
    have hhτ : Sum.inl h ∈ τ := (hτsched.2 _).2 (Finset.mem_univ _)
    exact (hfA h (hτA h hhτ)).trans (Finset.le_sup'
      (fun h => fA h (completionTime p σ (Sum.inl h))) (Finset.mem_univ h))
  have hBle' : maxCostB hB p fB τ ≤ maxCostB hB p fB σ' := by
    unfold maxCostB
    refine Finset.sup'_le _ _ (fun k _ => ?_)
    have hkτ : Sum.inr k ∈ τ := (hτsched.2 _).2 (Finset.mem_univ _)
    exact (hfB k (hτB k hkτ)).trans (Finset.le_sup'
      (fun k => fB k (completionTime p σ' (Sum.inr k))) (Finset.mem_univ k))
  have hBlt : maxCostB hB p fB τ < maxCostB hB p fB σ := lt_of_le_of_lt hBle' hBgt
  exact hσ.2 ⟨τ, hτsched, hAle, hBlt.le, Or.inr hBlt⟩
