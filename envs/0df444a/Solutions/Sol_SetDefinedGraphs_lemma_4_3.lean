-- Prove2me | solution 1 for SetDefinedGraphs.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:21:49.958271+00:00
-- url     : https://prove2.me/submissions/708bdedf-b4f5-4193-858a-829eb2863d7d

import Mathlib
import Definitions.Def_FASTournament_Isomorphic
import Definitions.Def_FASTournament_induce
import Definitions.Def_SetDefinedGraphs_Classes
import Definitions.Def_SetDefinedGraphs_Clauses
import Definitions.Def_SetDefinedGraphs_realisation
import Definitions.Def_SetDefinedGraphs_VectorSets

section
set_option autoImplicit false
namespace SetDefinedGraphs.Dev.Core43
open SetDefinedGraphs

theorem iso_symm {A B : Type} {G : Digraph A} {H : Digraph B}
    (h : FASTournament.Isomorphic G H) : FASTournament.Isomorphic H G := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, fun a b => ?_⟩
  have := he (e.symm a) (e.symm b)
  simpa using this.symm

theorem iso_trans {A B C : Type} {G : Digraph A} {H : Digraph B} {K : Digraph C}
    (h1 : FASTournament.Isomorphic G H) (h2 : FASTournament.Isomorphic H K) :
    FASTournament.Isomorphic G K := by
  obtain ⟨e, he⟩ := h1
  obtain ⟨e', he'⟩ := h2
  exact ⟨e.trans e', fun a b => (he a b).trans (he' _ _)⟩

section quot
variable {d : ℕ} (P : Setoid (Fin d))

noncomputable def dd : ℕ := Nat.card (Quotient P)
noncomputable def eqv : Quotient P ≃ Fin (dd P) := Finite.equivFin _
noncomputable def cls (i : Fin d) : Fin (dd P) := eqv P (Quotient.mk P i)
noncomputable def rep (a : Fin (dd P)) : Fin d := ((eqv P).symm a).out

theorem dd_le : dd P ≤ d := by
  have := Nat.card_le_card_of_surjective (Quotient.mk P) (Quotient.mk_surjective)
  simpa [dd] using this

theorem cls_rep (a : Fin (dd P)) : cls P (rep P a) = a := by
  unfold cls rep
  rw [Quotient.out_eq]; simp

theorem cls_eq (i j : Fin d) : cls P i = cls P j ↔ P.r i j := by
  unfold cls
  rw [(eqv P).apply_eq_iff_eq]
  exact Quotient.eq

theorem rep_rel (i : Fin d) : P.r (rep P (cls P i)) i := by
  rw [← cls_eq, cls_rep]

noncomputable def ex (w : Fin (dd P) → ℕ) : Fin d → ℕ := fun i => w (cls P i)
noncomputable def rs (v : Fin d → ℕ) : Fin (dd P) → ℕ := fun a => v (rep P a)

theorem rs_ex (w : Fin (dd P) → ℕ) : rs P (ex P w) = w := by
  funext a; simp [rs, ex, cls_rep]

theorem ex_rs (v : Fin d → ℕ) (hv : IsPHomogeneousVec P v) : ex P (rs P v) = v := by
  funext i; exact (hv _ _).2 (rep_rel P i)

theorem ex_inj : Function.Injective (ex P) := fun a b h => by
  rw [← rs_ex P a, ← rs_ex P b, h]

theorem ex_homog (w : Fin (dd P) → ℕ) (hw : Function.Injective w) :
    IsPHomogeneousVec P (ex P w) := fun i j => by
  show w (cls P i) = w (cls P j) ↔ _
  rw [hw.eq_iff, cls_eq]

theorem rs_inj (v : Fin d → ℕ) (hv : IsPHomogeneousVec P v) : Function.Injective (rs P v) :=
  fun a b h => by
    have := (hv _ _).1 h
    rw [← cls_eq, cls_rep, cls_rep] at this
    exact this

noncomputable def fp (f : (Fin d → Fin d → Bool) → Bool) (Q : FullClause (Fin (dd P))) : Bool :=
  f (fun i j => Q (cls P i) (cls P j))

open Classical in
noncomputable def Hset (f : (Fin d → Fin d → Bool) → Bool) : Finset (FullClause (Fin (dd P))) :=
  Finset.univ.filter (fun Q => IsInjectiveClause Q ∧ fp P f Q = true)

theorem mem_Hset (f : (Fin d → Fin d → Bool) → Bool) (Q : FullClause (Fin (dd P))) :
    Q ∈ Hset P f ↔ IsInjectiveClause Q ∧ fp P f Q = true := by
  simp [Hset]

theorem Hset_inj (f : (Fin d → Fin d → Bool) → Bool) : IsInjectiveDNF (Hset P f) :=
  fun C hC => ((mem_Hset P f C).1 hC).1

theorem dnf_eq (f : (Fin d → Fin d → Bool) → Bool) (Q : FullClause (Fin (dd P)))
    (hQ : IsInjectiveClause Q) : dnfFun (Hset P f) Q = fp P f Q := by
  rw [Bool.eq_iff_iff]
  simp [dnfFun, mem_Hset, hQ]

theorem pattern_inj {n : ℕ} (u w : Fin n → ℕ) (hu : Function.Injective u)
    (hw : Function.Injective w) : IsInjectiveClause (eqPattern u w) := by
  constructor
  · intro i j j' h h'
    simp only [eqPattern, decide_eq_true_eq] at h h'
    exact hw (h.symm.trans h')
  · intro i i' j h h'
    simp only [eqPattern, decide_eq_true_eq] at h h'
    exact hu (h.trans h'.symm)

theorem iso_ex (f : (Fin d → Fin d → Bool) → Bool) (V' : Set (Fin (dd P) → ℕ)) :
    FASTournament.Isomorphic (realisation f (ex P '' V')) (realisation (fp P f) V') := by
  apply iso_symm
  let e := Equiv.Set.image (ex P) V' (ex_inj P)
  refine ⟨e, fun a b => ?_⟩
  have : e a ≠ e b ↔ a ≠ b := e.injective.ne_iff
  show (a ≠ b ∧ _) ↔ (e a ≠ e b ∧ _)
  exact and_congr this.symm Iff.rfl

theorem iso_dnf (f : (Fin d → Fin d → Bool) → Bool) (V' : Set (Fin (dd P) → ℕ))
    (hV : IsInjectiveSet V') :
    FASTournament.Isomorphic (realisation (fp P f) V') (realisation (dnfFun (Hset P f)) V') := by
  refine ⟨Equiv.refl _, fun a b => ?_⟩
  simp only [realisation, Equiv.refl_apply]
  rw [dnf_eq P f _ (pattern_inj _ _ (hV _ a.2) (hV _ b.2))]

theorem fwd (f : (Fin d → Fin d → Bool) → Bool) (V : Set (Fin d → ℕ)) (hV : IsPHomogeneous P V) :
    FASTournament.Isomorphic (realisation f V)
      (realisation (dnfFun (Hset P f)) (rs P '' V)) := by
  have hVe : V = ex P '' (rs P '' V) := by
    ext v; constructor
    · intro hv; exact ⟨rs P v, ⟨v, hv, rfl⟩, ex_rs P v (hV v hv)⟩
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩; rw [ex_rs P u (hV u hu)]; exact hu
  have hinj : IsInjectiveSet (rs P '' V) := by
    rintro _ ⟨v, hv, rfl⟩; exact rs_inj P v (hV v hv)
  have h1 := iso_ex P f (rs P '' V)
  rw [← hVe] at h1
  exact iso_trans h1 (iso_dnf P f _ hinj)

theorem bwd (f : (Fin d → Fin d → Bool) → Bool) (V' : Set (Fin (dd P) → ℕ))
    (hV : IsInjectiveSet V') :
    FASTournament.Isomorphic (realisation f (ex P '' V'))
      (realisation (dnfFun (Hset P f)) V') :=
  iso_trans (iso_ex P f V') (iso_dnf P f V' hV)

theorem ex_homog_set (V' : Set (Fin (dd P) → ℕ)) (hV : IsInjectiveSet V') :
    IsPHomogeneous P (ex P '' V') := by
  rintro _ ⟨w, hw, rfl⟩
  exact ex_homog P w (hV w hw)

end quot

end SetDefinedGraphs.Dev.Core43
end

section
set_option autoImplicit false
namespace SetDefinedGraphs
open SetDefinedGraphs.Dev.Core43 in
theorem chk_lemma_4_3 {d : ℕ} (f : (Fin d → Fin d → Bool) → Bool) (P : Setoid (Fin d)) :
    ∃ d' : ℕ, d' ≤ d ∧ ∃ H : Finset (FullClause (Fin d')), IsInjectiveDNF H ∧
      ∀ {W : Type} (G : Digraph W), InXP f P G ↔ InX' (dnfFun H) G := by
  refine ⟨dd P, dd_le P, Hset P f, Hset_inj P f, fun {W} G => ?_⟩
  constructor
  · rintro ⟨V, hfin, hhom, hiso⟩
    refine ⟨rs P '' V, hfin.image _, ?_, iso_trans hiso (fwd P f V hhom)⟩
    rintro _ ⟨v, hv, rfl⟩; exact rs_inj P v (hhom v hv)
  · rintro ⟨V', hfin, hinj, hiso⟩
    exact ⟨ex P '' V', hfin.image _, ex_homog_set P V' hinj,
      iso_trans hiso (iso_symm (bwd P f V' hinj))⟩
end SetDefinedGraphs
end

theorem solution : type_of% @SetDefinedGraphs.chk_lemma_4_3 := @SetDefinedGraphs.chk_lemma_4_3
