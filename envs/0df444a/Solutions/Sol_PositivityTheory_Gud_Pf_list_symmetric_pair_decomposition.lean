-- Prove2me | solution 1 for PositivityTheory.Gud.Pf.list_symmetric_pair_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:26:14.726252+00:00
-- url     : https://prove2.me/submissions/b643c77c-7d6a-4cc6-90df-f12503da0e16

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitaryDualGL_GenericUnitaryDual_PComb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.Gud PositivityTheory.Gud.Pf
namespace PositivityTheory.Gud.Pf
theorem _root_.solution {α : Type*} : ∀ (n : ℕ) (l : List (α × ℝ)), l.length = n →
    List.Perm (l.map (fun p => (p.1, -p.2))) l →
    ∃ (a : List α) (b : List (α × ℝ)), (∀ p ∈ b, 0 < p.2 ∧ p ∈ l) ∧
      List.Perm (a.map (fun x => (x, (0 : ℝ))) ++ b.flatMap (fun p => [p, (p.1, -p.2)])) l := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l hlen hl
  rcases l with _ | ⟨p, l'⟩
  · exact ⟨[], [], by simp, by simp⟩
  by_cases h0 : p.2 = 0
  · have hp : ((p.1, -p.2) : α × ℝ) = p := Prod.ext rfl (by simp [h0])
    have hl' : List.Perm (l'.map (fun p => (p.1, -p.2))) l' := by
      rw [List.map_cons, hp] at hl
      exact hl.cons_inv
    obtain ⟨a', b', hb', hperm'⟩ := ih l'.length (by simp at hlen; omega) l' rfl hl'
    have hp0 : ((p.1, (0 : ℝ)) : α × ℝ) = p := Prod.ext rfl h0.symm
    refine ⟨p.1 :: a', b', fun q hq => ⟨(hb' q hq).1, List.mem_cons_of_mem _ (hb' q hq).2⟩, ?_⟩
    simp only [List.map_cons, List.cons_append, hp0]
    exact hperm'.cons p
  · have hnp : ((p.1, -p.2) : α × ℝ) ≠ p := by
      intro h
      have h2 := congrArg Prod.snd h
      simp only at h2
      exact h0 (by linarith)
    have hmem : ((p.1, -p.2) : α × ℝ) ∈ p :: l' := hl.subset (by simp)
    have hmem' : ((p.1, -p.2) : α × ℝ) ∈ l' := (List.mem_cons.mp hmem).resolve_left hnp
    obtain ⟨s, t, rfl⟩ := List.append_of_mem hmem'
    have hmid : List.Perm (p :: (s ++ (p.1, -p.2) :: t)) (p :: (p.1, -p.2) :: (s ++ t)) :=
      List.perm_middle.cons p
    have h1 : List.Perm ((p :: (p.1, -p.2) :: (s ++ t)).map (fun p => (p.1, -p.2)))
        (p :: (p.1, -p.2) :: (s ++ t)) :=
      ((hmid.map _).symm.trans hl).trans hmid
    simp only [List.map_cons, neg_neg, Prod.mk.eta] at h1
    have h2 : List.Perm ((s ++ t).map (fun p => (p.1, -p.2))) (s ++ t) :=
      ((h1.trans (List.Perm.swap ((p.1, -p.2) : α × ℝ) p (s ++ t))).cons_inv).cons_inv
    obtain ⟨a'', b'', hb'', hperm''⟩ :=
      ih (s ++ t).length (by simp only [List.length_cons, List.length_append] at hlen ⊢; omega) (s ++ t) rfl h2
    have hin : ∀ q ∈ b'', q ∈ p :: (s ++ (p.1, -p.2) :: t) := by
      intro q hq
      have hq' := (hb'' q hq).2
      simp only [List.mem_cons, List.mem_append] at hq' ⊢
      tauto
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · refine ⟨a'', (p.1, -p.2) :: b'', ?_, ?_⟩
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨by simp only; linarith, hmem⟩
        · exact ⟨(hb'' q hq).1, hin q hq⟩
      · simp only [List.flatMap_cons, List.cons_append, List.nil_append, neg_neg, Prod.mk.eta]
        exact List.perm_middle.trans ((List.perm_middle.cons _).trans (((hperm''.cons _).cons _).trans
          ((List.Perm.swap p ((p.1, -p.2) : α × ℝ) (s ++ t)).trans hmid.symm)))
    · refine ⟨a'', p :: b'', ?_, ?_⟩
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨hpos, List.mem_cons_self ..⟩
        · exact ⟨(hb'' q hq).1, hin q hq⟩
      · simp only [List.flatMap_cons, List.cons_append, List.nil_append]
        exact List.perm_middle.trans ((List.perm_middle.cons _).trans (((hperm''.cons _).cons _).trans
          hmid.symm))
end PositivityTheory.Gud.Pf
