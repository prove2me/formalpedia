-- Prove2me | solution 1 for StrategyProofArrow.WeakGS.lemma_9_ii
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T04:33:24.788663+00:00
-- url     : https://prove2.me/submissions/b93e3b60-4cf1-4a0e-8b0a-3405d8b4caed

import Mathlib
import Definitions.Def_StrategyProofArrow_WeakGS_Basic



namespace StrategyProofArrow.WeakGS

open Classical

/-- embed a strong order as a weak order -/
def g4toW {A : Type*} (S : StrategyProofArrow.Correspondence.StrongOrder A) : WeakOrder A :=
  ⟨S.1.rel, S.1.total, S.1.trans⟩

noncomputable def g4key {A : Type*} [Fintype A] (x : A) (a : A) : ℕ :=
  if a = x then 0 else ((Fintype.equivFin A) a : ℕ) + 1

theorem g4key_inj {A : Type*} [Fintype A] (x : A) {a b : A} (h : g4key x a = g4key x b) : a = b := by
  unfold g4key at h
  by_cases ha : a = x <;> by_cases hb : b = x
  · rw [ha, hb]
  · simp [ha, hb] at h
  · simp [ha, hb] at h
  · simp only [ha, hb, if_false, add_left_inj] at h
    exact (Fintype.equivFin A).injective (Fin.ext h)

theorem g4key_x {A : Type*} [Fintype A] (x : A) : g4key x x = 0 := by simp [g4key]

/-- refinement of `R` breaking ties by the key (x first). -/
noncomputable def g4refine {A : Type*} [Fintype A] (R : WeakOrder A) (x : A) :
    StrategyProofArrow.Correspondence.StrongOrder A :=
  ⟨{ rel := fun a b => R.rel a b ∧ (R.rel b a → g4key x a ≤ g4key x b)
     total := by
       intro a b
       by_cases h1 : R.rel a b <;> by_cases h2 : R.rel b a
       · rcases le_total (g4key x a) (g4key x b) with h | h
         · exact Or.inl ⟨h1, fun _ => h⟩
         · exact Or.inr ⟨h2, fun _ => h⟩
       · exact Or.inl ⟨h1, fun h => absurd h h2⟩
       · exact Or.inr ⟨h2, fun h => absurd h h1⟩
       · exact absurd ((R.total a b).resolve_left h1) h2
     trans := by
       rintro a b c ⟨hab, hab'⟩ ⟨hbc, hbc'⟩
       refine ⟨R.trans _ _ _ hab hbc, fun hca => ?_⟩
       have hba : R.rel b a := R.trans _ _ _ hbc hca
       have hcb : R.rel c b := R.trans _ _ _ hca hab
       exact le_trans (hab' hba) (hbc' hcb) },
   by
     rintro a b ⟨h1, h1'⟩ ⟨h2, h2'⟩
     exact g4key_inj x (le_antisymm (h1' h2) (h2' h1))⟩

theorem g4refine_strict {A : Type*} [Fintype A] (R : WeakOrder A) (x a b : A)
    (h : R.strict a b) : (g4refine R x).1.strict a b :=
  ⟨⟨h.1, fun h' => absurd h' h.2⟩, fun h' => h.2 h'.1⟩

theorem g4_step {ι A : Type*} [Fintype A] [DecidableEq ι] (v : VotingProcedure ι A)
    (hv : StrategyProof v) (P : WeakProfile ι A) (i : ι) :
    v (Function.update P i (g4toW (g4refine (P i) (v P)))) = v P := by
  set x := v P with hx
  set C := g4refine (P i) x with hC
  set P' := Function.update P i (g4toW C) with hP'
  have h1 := hv P i (g4toW C)
  have h2 := hv P' i (P i)
  have hPP : Function.update P' i (P i) = P := by
    rw [hP']; simp
  rw [hPP] at h2
  rw [← hP'] at h1
  by_contra hne
  have hP'i : P' i = g4toW C := by rw [hP']; simp
  rw [hP'i] at h2
  -- h2 : ¬ (g4toW C).strict x (v P')
  have hCyx : C.1.rel (v P') x := by
    rcases C.1.total (v P') x with h | h
    · exact h
    · exact absurd ⟨h, fun h' => hne (C.2 _ _ h' h)⟩ h2
  obtain ⟨hR, hR'⟩ := hCyx
  apply h1
  refine ⟨hR, fun hxy => ?_⟩
  have := hR' hxy
  rw [g4key_x] at this
  have h0 : g4key x (v P') = g4key x x := by rw [g4key_x]; omega
  exact hne (g4key_inj x h0)

theorem lemma_9_ii_core {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (v : VotingProcedure ι A) (hv : StrategyProof v) :
    ∃ (ν : StrictVotingProcedure ι A) (α : WeakProfile ι A → StrategyProofArrow.Correspondence.StrongProfile ι A),
      StrictStrategyProof ν ∧ IsTieBreaking α ∧ ∀ B : WeakProfile ι A, v B = ν (α B) := by
  refine ⟨fun C => v (fun j => g4toW (C j)), fun B j => g4refine (B j) (v B), ?_, ?_, ?_⟩
  · intro C i c
    have := hv (fun j => g4toW (C j)) i (g4toW c)
    have heq : (fun j => g4toW (Function.update C i c j)) =
        Function.update (fun j => g4toW (C j)) i (g4toW c) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    simp only
    rw [heq]
    exact this
  · intro B i x y h
    exact g4refine_strict _ _ _ _ h
  · intro B
    let D : Finset ι → WeakProfile ι A := fun S j =>
      if j ∈ S then g4toW (g4refine (B j) (v B)) else B j
    have key : ∀ S : Finset ι, v (D S) = v B := by
      intro S
      induction S using Finset.induction_on with
      | empty => congr 1
      | insert i S hi ih =>
        have hDi : D S i = B i := by simp [D, hi]
        have := g4_step v hv (D S) i
        rw [hDi, ih] at this
        rw [← this]
        congr 1
        funext j
        by_cases hj : j = i
        · subst hj; simp [D]
        · simp [D, Function.update_of_ne hj, hj]
    have := key Finset.univ
    rw [← this]
    congr 1
    funext j
    simp [D]

end StrategyProofArrow.WeakGS

open StrategyProofArrow.WeakGS


theorem solution {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 1 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (v : VotingProcedure ι A) (hv : StrategyProof v) :
    ∃ (ν : StrictVotingProcedure ι A) (α : WeakProfile ι A → StrategyProofArrow.Correspondence.StrongProfile ι A),
      StrictStrategyProof ν ∧ IsTieBreaking α ∧ ∀ B : WeakProfile ι A, v B = ν (α B) := by
  exact lemma_9_ii_core v hv
