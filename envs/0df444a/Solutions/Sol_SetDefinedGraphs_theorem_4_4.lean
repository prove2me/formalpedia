-- Prove2me | solution 1 for SetDefinedGraphs.theorem_4_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:21:50.877955+00:00
-- url     : https://prove2.me/submissions/16867104-4f69-4f08-bef2-c22b1ac49a6f

import Mathlib
import Definitions.Def_FASTournament_Isomorphic
import Definitions.Def_FASTournament_induce
import Definitions.Def_SetDefinedGraphs_Classes
import Definitions.Def_SetDefinedGraphs_Clauses
import Definitions.Def_SetDefinedGraphs_realisation
import Definitions.Def_SetDefinedGraphs_VectorSets
import Definitions.Def_SetDefinedGraphs_DigraphBasics

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

theorem induce_iso {ι W : Type} (G : Digraph W) (f : (ι → ι → Bool) → Bool) (V : Set (ι → ℕ))
    (e : W ≃ V) (he : ∀ a b, G.Adj a b ↔ (realisation f V).Adj (e a) (e b)) (S : Set W) :
    FASTournament.Isomorphic (FASTournament.induce G S)
      (realisation f ((fun w => (e w).1) '' S)) := by
  have ginj : Function.Injective (fun w => (e w).1) :=
    Subtype.val_injective.comp e.injective
  let ε := Equiv.Set.image (fun w => (e w).1) S ginj
  refine ⟨ε, fun a b => ?_⟩
  show G.Adj a.1 b.1 ↔ _
  rw [he]
  have h1 : e a.1 ≠ e b.1 ↔ a ≠ b := by
    rw [Ne, Ne, e.apply_eq_iff_eq, Subtype.ext_iff]
  have h2 : ε a ≠ ε b ↔ a ≠ b := ε.injective.ne_iff
  show (e a.1 ≠ e b.1 ∧ _) ↔ (ε a ≠ ε b ∧ _)
  exact and_congr (h1.trans h2.symm) Iff.rfl

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

theorem rs_inj (v : Fin d → ℕ) (hv : IsPHomogeneousVec P v) : Function.Injective (rs P v) :=
  fun a b h => by
    have := (hv _ _).1 h
    rw [← cls_eq, cls_rep, cls_rep] at this
    exact this

theorem rs_ou (T : Set (Fin d → ℕ)) (h : IsOrderUniform T) : IsOrderUniform (rs P '' T) := by
  rintro _ ⟨u, hu, rfl⟩ _ ⟨w, hw, rfl⟩ a b
  exact h u hu w hw _ _

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

end quot

/-- the setoid with classes the fibres of `t` -/
def Pt {d : ℕ} (t : Fin d → Fin d) : Setoid (Fin d) :=
  ⟨fun i j => t i = t j, ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩⟩

/-- standardization -/
noncomputable def sig {d : ℕ} (v : Fin d → ℕ) (i : Fin d) : Fin d :=
  ⟨((Finset.univ.image v).filter (· < v i)).card, by
    have h1 : (Finset.univ.image v).filter (· < v i) ⊂ Finset.univ.image v := by
      rw [Finset.filter_ssubset]
      exact ⟨v i, Finset.mem_image_of_mem _ (Finset.mem_univ _), lt_irrefl _⟩
    have h2 := Finset.card_lt_card h1
    have h3 : (Finset.univ.image v).card ≤ d := by
      simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin d))) (f := v)
    omega⟩

theorem sig_lt {d : ℕ} (v : Fin d → ℕ) {i j : Fin d} (h : v i < v j) : sig v i < sig v j := by
  show ((Finset.univ.image v).filter (· < v i)).card < ((Finset.univ.image v).filter (· < v j)).card
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨v i, by simp [h], by simp⟩
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.trans h⟩

theorem sig_lt_iff {d : ℕ} (v : Fin d → ℕ) (i j : Fin d) : sig v i < sig v j ↔ v i < v j := by
  constructor
  · intro h
    rcases lt_trichotomy (v i) (v j) with h1 | h1 | h1
    · exact h1
    · rw [show sig v i = sig v j by simp only [sig, h1]] at h; exact absurd h (lt_irrefl _)
    · exact absurd (sig_lt v h1) (not_lt.2 h.le)
  · exact sig_lt v

theorem sig_eq_iff {d : ℕ} (v : Fin d → ℕ) (i j : Fin d) : sig v i = sig v j ↔ v i = v j := by
  constructor
  · intro h
    rcases lt_trichotomy (v i) (v j) with h1 | h1 | h1
    · exact absurd h (ne_of_lt (sig_lt v h1))
    · exact h1
    · exact absurd h (ne_of_gt (sig_lt v h1))
  · intro h; simp only [sig, h]

theorem homog_of_sig {d : ℕ} (t : Fin d → Fin d) (T : Set (Fin d → ℕ))
    (hT : ∀ v ∈ T, sig v = t) : IsPHomogeneous (Pt t) T ∧ IsOrderUniform T := by
  constructor
  · intro v hv a b
    show v a = v b ↔ t a = t b
    rw [← hT v hv, sig_eq_iff]
  · intro u hu w hw a b
    rw [← sig_lt_iff, ← sig_lt_iff w, hT u hu, hT w hw]

end SetDefinedGraphs.Dev.Core43
end

section
set_option autoImplicit false
namespace SetDefinedGraphs
open SetDefinedGraphs.Dev.Core43 in
theorem chk_theorem_4_4 {d : ℕ} (f : (Fin d → Fin d → Bool) → Bool) :
    ∃ r : ℕ, r ≤ d ^ (2 * d) ∧ ∃ d' : Fin r → ℕ, (∀ i, d' i ≤ d) ∧
      ∃ H : (i : Fin r) → Finset (FullClause (Fin (d' i))), (∀ i, IsInjectiveDNF (H i)) ∧
        (∀ {W : Type} (G : Digraph W), InX f G →
          ∃ part : W → Fin r, ∀ i, InY (dnfFun (H i)) (FASTournament.induce G {v | part v = i})) ∧
        (∀ (i : Fin r) {W : Type} (G : Digraph W), InY (dnfFun (H i)) G → InX f G) := by
  let idx : (Fin d → Fin d) ≃ Fin (Fintype.card (Fin d → Fin d)) := Fintype.equivFin _
  refine ⟨Fintype.card (Fin d → Fin d), ?_, fun i => dd (Pt (idx.symm i)),
    fun i => dd_le _, fun i => Hset (Pt (idx.symm i)) f, fun i => Hset_inj _ f, ?_, ?_⟩
  · rw [Fintype.card_fun]; simp only [Fintype.card_fin]
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; simp
    · exact Nat.pow_le_pow_right h (by omega)
  · rintro W G ⟨V, hfin, e, he⟩
    refine ⟨fun w => idx (sig (e w).1), fun i => ?_⟩
    have hiso := induce_iso G f V e he {v | idx (sig (e v).1) = i}
    set T : Set (Fin d → ℕ) := (fun w => (e w).1) '' {v | idx (sig (e v).1) = i} with hTdef
    have hT : ∀ v ∈ T, sig v = idx.symm i := by
      rintro _ ⟨w, hw, rfl⟩
      exact idx.eq_symm_apply.2 hw
    obtain ⟨hhom, hou⟩ := homog_of_sig _ T hT
    have hTfin : T.Finite := hfin.subset (by rintro _ ⟨w, _, rfl⟩; exact (e w).2)
    refine ⟨rs _ '' T, hTfin.image _, ?_, rs_ou _ T hou, iso_trans hiso (fwd _ f T hhom)⟩
    rintro _ ⟨v, hv, rfl⟩; exact rs_inj _ v (hhom v hv)
  · intro i W G ⟨V', hfin, hinj, _, hiso⟩
    exact ⟨ex _ '' V', hfin.image _, iso_trans hiso (iso_symm (bwd _ f V' hinj))⟩
end SetDefinedGraphs
end

theorem solution : type_of% @SetDefinedGraphs.chk_theorem_4_4 := @SetDefinedGraphs.chk_theorem_4_4
