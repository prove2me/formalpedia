-- Prove2me | solution 1 for TwoAgentSched.no_idle
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-07T03:35:45.753395+00:00
-- url     : https://prove2.me/submissions/80a3b5af-856c-4a6f-be61-98b86fc31c60

import Mathlib
import Definitions.Def_TwoAgentSched_Feasible
import Definitions.Def_TwoAgentSched_fAmax

open TwoAgentSched

namespace TwoAgentSched.NoIdleProof

variable {ι : Type} [DecidableEq ι]

lemma seqC_cons_self (p : ι → ℝ) (a : ι) (rest : List ι) :
    seqC p (a :: rest) a = p a := by
  simp [seqC]

lemma seqC_cons_ne (p : ι → ℝ) (a j : ι) (rest : List ι) (h : j ≠ a) :
    seqC p (a :: rest) j = p a + seqC p rest j := by
  simp only [seqC]
  rw [List.idxOf_cons_ne rest (Ne.symm h)]
  simp [List.take_succ_cons, List.map_cons, List.sum_cons]

lemma seqC_nonneg (p : ι → ℝ) (hp : ∀ j, 0 ≤ p j) (σ : List ι) (j : ι) :
    0 ≤ seqC p σ j := by
  rw [seqC]
  exact List.sum_nonneg (fun x hx => by
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact hp y)

end TwoAgentSched.NoIdleProof

namespace TwoAgentSched.NoIdleProof

variable {nA nB : ℕ}

def jobIdx : Job nA nB → ℕ
  | Sum.inl h => h.val
  | Sum.inr k => nA + k.val

lemma jobIdx_injective : Function.Injective (jobIdx (nA := nA) (nB := nB)) := by
  intro a b h
  cases a with
  | inl ha =>
      cases b with
      | inl hb =>
          simp [jobIdx] at h
          exact congrArg Sum.inl (Fin.ext h)
      | inr kb =>
          simp [jobIdx] at h
          omega
  | inr ka =>
      cases b with
      | inl hb =>
          simp [jobIdx] at h
          omega
      | inr kb =>
          simp [jobIdx] at h
          exact congrArg Sum.inr (Fin.ext (by omega))

noncomputable def flag (p : Job nA nB → ℝ) (j : Job nA nB) : Bool := decide (p j ≠ 0)

noncomputable def key (p : Job nA nB → ℝ) (S : Job nA nB → ℝ) (j : Job nA nB) :
    ℝ ×ₗ Bool ×ₗ ℕ :=
  toLex (S j, toLex (flag p j, jobIdx j))

lemma key_injective (p S : Job nA nB → ℝ) : Function.Injective (key p S) := by
  intro a b h
  have h1 := congrArg ofLex h
  simp only [key, ofLex_toLex] at h1
  have h2 := congrArg Prod.snd h1
  have h3 := congrArg ofLex h2
  simp only [ofLex_toLex] at h3
  exact jobIdx_injective (congrArg Prod.snd h3)

lemma head_completion_le (p S : Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j) (hS : Feasible p S)
    (a : Job nA nB) (rest : List (Job nA nB))
    (hpair : List.Pairwise (fun x y => key p S x ≤ key p S y) (a :: rest))
    (hnodup : (a :: rest).Nodup) {i : Job nA nB} (hi : i ∈ rest) :
    S a + p a ≤ S i := by
  rw [List.pairwise_cons] at hpair
  obtain ⟨hhead, _⟩ := hpair
  have hkey_le : key p S a ≤ key p S i := hhead i hi
  have hai : a ≠ i := by
    rw [List.nodup_cons] at hnodup
    intro h
    exact hnodup.1 (h ▸ hi)
  have hkey_ne : key p S a ≠ key p S i := fun h => hai (key_injective p S h)
  have hkey_lt : key p S a < key p S i := lt_of_le_of_ne hkey_le hkey_ne
  simp only [key] at hkey_lt
  rw [Prod.Lex.toLex_lt_toLex] at hkey_lt
  rcases hkey_lt with hSlt | ⟨hSeq, hflag_lt⟩
  · have hfeas := hS.2 a i hai
    rcases hfeas with h | h
    · exact h
    · linarith [hp a, hp i]
  · by_cases hpa : p a = 0
    · linarith
    · have hfa : flag p a = true := by simp [flag, hpa]
      rw [Prod.Lex.toLex_lt_toLex] at hflag_lt
      simp only [Prod.fst, Prod.snd] at hflag_lt
      rcases hflag_lt with hlt | ⟨hfeq, _⟩
      · rw [hfa] at hlt
        exact absurd hlt (by cases flag p i <;> decide)
      · have hfeq' : flag p a = flag p i := hfeq
        have hfi : flag p i = true := by rw [← hfeq', hfa]
        have hpi : p i ≠ 0 := by
          by_contra h
          simp [flag, h] at hfi
        have hpa_pos : 0 < p a := lt_of_le_of_ne (hp a) (Ne.symm hpa)
        have hpi_pos : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm hpi)
        have hfeas := hS.2 a i hai
        rcases hfeas with h | h
        · linarith
        · linarith

lemma seqC_le_of_sorted (p S : Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j) (hS : Feasible p S) :
    ∀ (σ : List (Job nA nB)), σ.Nodup →
      List.Pairwise (fun x y => key p S x ≤ key p S y) σ →
      ∀ (t : ℝ), (∀ j ∈ σ, t ≤ S j) →
      ∀ j ∈ σ, t + seqC p σ j ≤ S j + p j := by
  intro σ
  induction σ with
  | nil =>
      intro _ _ t _ j hj
      simp at hj
  | cons a rest ih =>
      intro hnodup hsorted t ht j hj
      rw [List.pairwise_cons] at hsorted
      obtain ⟨hhead, htail⟩ := hsorted
      rw [List.nodup_cons] at hnodup
      obtain ⟨ha_not, hrest_nodup⟩ := hnodup
      by_cases hja : j = a
      · rw [hja]
        rw [seqC_cons_self]
        have : t ≤ S a := ht a (by simp)
        linarith
      · have hj' : j ∈ rest := by
          rw [List.mem_cons] at hj
          exact hj.resolve_left hja
        rw [seqC_cons_ne p a j rest hja]
        have ht' : ∀ i ∈ rest, t + p a ≤ S i := by
          intro i hi
          have hcomp := head_completion_le p S hp hS a rest
            (by rw [List.pairwise_cons]; exact ⟨hhead, htail⟩)
            (by rw [List.nodup_cons]; exact ⟨ha_not, hrest_nodup⟩) hi
          have hta : t ≤ S a := ht a (by simp)
          linarith
        have hih := ih hrest_nodup htail (t + p a) ht' j hj'
        linarith

lemma fAmax_le_of_le {nA nB : ℕ} (fA : Fin nA → ℝ → ℝ) (C C' : Job nA nB → ℝ)
    (hC : ∀ j, C j ≤ C' j) (hC0 : ∀ j, 0 ≤ C j) (hC'0 : ∀ j, 0 ≤ C' j)
    (hmono : ∀ h, MonotoneOn (fA h) (Set.Ici 0)) :
    fAmax fA C ≤ fAmax fA C' := by
  unfold fAmax
  apply Finset.sup_le
  intro h _
  have hle : fA h (C (Sum.inl h)) ≤ fA h (C' (Sum.inl h)) :=
    hmono h (hC0 _) (hC'0 _) (hC _)
  calc
    ((fA h (C (Sum.inl h)) : ℝ) : EReal) ≤ ((fA h (C' (Sum.inl h)) : ℝ) : EReal) :=
      EReal.coe_le_coe hle
    _ ≤ Finset.univ.sup (fun h => ((fA h (C' (Sum.inl h)) : ℝ) : EReal)) :=
      Finset.le_sup (s := Finset.univ) (f := fun h => ((fA h (C' (Sum.inl h)) : ℝ) : EReal))
        (Finset.mem_univ h)

theorem no_idle (p : Job nA nB → ℝ) (S : Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hS : Feasible p S) :
    ∃ σ : List (Job nA nB), IsSeq σ ∧ (∀ j, seqC p σ j ≤ S j + p j) ∧
      ∀ (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ) (Q : ℝ),
        (∀ h, MonotoneOn (fA h) (Set.Ici 0)) → (∀ k, MonotoneOn (fB k) (Set.Ici 0)) →
        fAmax fA (seqC p σ) ≤ fAmax fA (fun j => S j + p j) ∧
        (BOk fB Q (fun j => S j + p j) → BOk fB Q (seqC p σ)) := by
  let key' : Job nA nB → ℝ ×ₗ Bool ×ₗ ℕ := fun j => key p S j
  let le : Job nA nB → Job nA nB → Bool := fun a b => decide (key' a ≤ key' b)
  let σ : List (Job nA nB) := (Finset.univ.toList).mergeSort le
  have hnodup : σ.Nodup := by
    dsimp only [σ]
    rw [List.nodup_mergeSort]
    exact Finset.nodup_toList _
  have hmem : ∀ j, j ∈ σ := by
    intro j
    dsimp only [σ]
    rw [List.mem_mergeSort]
    rw [Finset.mem_toList]
    exact Finset.mem_univ j
  have hsorted : List.Pairwise (fun a b => key' a ≤ key' b) σ := by
    dsimp only [σ]
    have htrans : ∀ a b c, le a b = true → le b c = true → le a c = true := by
      intro a b c h1 h2
      simp only [le, decide_eq_true_eq] at h1 h2 ⊢
      exact le_trans h1 h2
    have htotal : ∀ a b, (le a b || le b a) = true := by
      intro a b
      simp only [le, Bool.or_eq_true, decide_eq_true_eq]
      exact le_total (key' a) (key' b)
    have hs := List.pairwise_mergeSort (le := le) htrans htotal (Finset.univ.toList)
    exact hs.imp (fun {a b} h => by simpa [le] using h)
  have hpoint : ∀ j, seqC p σ j ≤ S j + p j := by
    intro j
    have h := seqC_le_of_sorted p S hp hS σ hnodup hsorted 0
      (fun i _ => hS.1 i) j (hmem j)
    simpa using h
  refine ⟨σ, ⟨hnodup, hmem⟩, hpoint, ?_⟩
  intro fA fB Q hfA hfB
  constructor
  · exact fAmax_le_of_le fA _ _ hpoint (fun j => seqC_nonneg p hp σ j)
      (fun j => add_nonneg (hS.1 j) (hp j)) hfA
  · intro hBOk k
    have hle := hpoint (Sum.inr k)
    have h0 : 0 ≤ seqC p σ (Sum.inr k) := seqC_nonneg p hp σ _
    have h0' : 0 ≤ S (Sum.inr k) + p (Sum.inr k) := add_nonneg (hS.1 _) (hp _)
    exact le_trans (hfB k h0 h0' hle) (hBOk k)

end TwoAgentSched.NoIdleProof

/-- No idle time: a feasible schedule is dominated by the no-idle schedule of a sequence. -/
theorem solution {nA nB : ℕ} (p : Job nA nB → ℝ) (S : Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hS : Feasible p S) :
    ∃ σ : List (Job nA nB), IsSeq σ ∧ (∀ j, seqC p σ j ≤ S j + p j) ∧
      ∀ (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ) (Q : ℝ),
        (∀ h, MonotoneOn (fA h) (Set.Ici 0)) → (∀ k, MonotoneOn (fB k) (Set.Ici 0)) →
        fAmax fA (seqC p σ) ≤ fAmax fA (fun j => S j + p j) ∧
        (BOk fB Q (fun j => S j + p j) → BOk fB Q (seqC p σ)) :=
  TwoAgentSched.NoIdleProof.no_idle p S hp hS
