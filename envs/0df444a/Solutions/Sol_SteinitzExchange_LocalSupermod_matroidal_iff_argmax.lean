-- Prove2me | solution 1 for SteinitzExchange.LocalSupermod.matroidal_iff_argmax
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-30T14:54:20.799379+00:00
-- url     : https://prove2.me/submissions/8fe65e6b-e0b9-45d4-a306-3d5b3c7df635

import Definitions.Def_SteinitzExchange_LocalSupermod_Matroidal
import Definitions.Def_SteinitzExchange_LocalSupermod_Localization
import Definitions.Def_SteinitzExchange_LocalSupermod_Exchange
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic
open Set
open SteinitzExchange.LocalSupermod

private def B : Finset (Fin 2 → ℤ) := {![2,0],![1,1],![0,2]}
private def g (x : Fin 2 → ℤ) : ℝ := if x=![1,1] then -1 else 0
private def F (p : Fin 2 → ℝ) : ℝ := min (2*p 0) (2*p 1)

private theorem base : IsIntegralBaseSet B := by
  constructor
  · exact ⟨![2,0],by simp [B]⟩
  · intro x hx y hy u hu
    have hx : x=![2,0] ∨ x=![1,1] ∨ x=![0,2] := by simpa [B] using hx
    have hy : y=![2,0] ∨ y=![1,1] ∨ y=![0,2] := by simpa [B] using hy
    rcases hx with rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl <;>
      fin_cases u <;> norm_num [B,chi,Pi.single_apply,Matrix.vecHead,Matrix.vecTail,Fin.exists_fin_two,funext_iff,Fin.forall_fin_two] at *

private theorem conj (p : Fin 2 → ℝ) : concaveConj B g p=F p := by
  classical
  haveI : Nonempty (B : Set (Fin 2 → ℤ)) := ⟨⟨![2,0],by simp [B]⟩⟩
  have hb : BddBelow (Set.range (fun x : (B : Set (Fin 2 → ℤ)) => pairing p (toReal (x : Fin 2 → ℤ))-g x)) := (Set.finite_range _).bddBelow
  apply le_antisymm
  · have h1 := ciInf_le hb ⟨![2,0],by simp [B]⟩
    have h2 := ciInf_le hb ⟨![0,2],by simp [B]⟩
    change (⨅ x : (B : Set (Fin 2 → ℤ)),pairing p (toReal (x : Fin 2 → ℤ))-g x) ≤ _
    apply le_min
    · simpa [pairing,toReal,g,Fin.sum_univ_two,funext_iff,Fin.forall_fin_two,mul_comm] using h1
    · simpa [pairing,toReal,g,Fin.sum_univ_two,funext_iff,Fin.forall_fin_two,mul_comm] using h2
  · apply le_ciInf
    intro x
    obtain ⟨x,hx⟩ := x
    have hx : x=![2,0] ∨ x=![1,1] ∨ x=![0,2] := by simpa [B] using hx
    rcases hx with rfl|rfl|rfl
    · simpa [F,pairing,toReal,g,Fin.sum_univ_two,funext_iff,Fin.forall_fin_two,mul_comm] using min_le_left (2*p 0) (2*p 1)
    · simp only [pairing,toReal,g,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Int.cast_one,mul_one,ite_true,sub_neg_eq_add]
      dsimp [F]
      rcases le_total (p 0) (p 1) with h|h
      · rw [min_eq_left (by linarith)]
        linarith
      · rw [min_eq_right (by linarith)]
        linarith
    · simpa [F,pairing,toReal,g,Fin.sum_univ_two,funext_iff,Fin.forall_fin_two,mul_comm] using min_le_right (2*p 0) (2*p 1)

private theorem loc : localization (concaveConj B g) 0=F := by
  classical
  have hc : concaveConj B g=F := funext conj
  rw [hc]
  have h0 : F 0=0 := by norm_num [F]
  have h1 : (![2,0] : Fin 2 → ℝ) ∈ superdiff F 0 := by
    intro p
    simpa [F,pairing,Fin.sum_univ_two,mul_comm] using min_le_left (2*p 0) (2*p 1)
  have h2 : (![0,2] : Fin 2 → ℝ) ∈ superdiff F 0 := by
    intro p
    simpa [F,pairing,Fin.sum_univ_two,mul_comm] using min_le_right (2*p 0) (2*p 1)
  ext p
  have hb : BddBelow ((fun b => pairing p b) '' superdiff F 0) := by
    refine ⟨F p,?_⟩
    rintro _ ⟨b,hb,rfl⟩
    simpa only [h0,sub_zero] using hb p
  apply le_antisymm
  · apply le_min
    · have hh := csInf_le hb (show pairing p ![2,0] ∈ ((fun b => pairing p b) '' superdiff F 0) from ⟨_,h1,rfl⟩)
      simpa [localization,pairing,Fin.sum_univ_two,mul_comm] using hh
    · have hh := csInf_le hb (show pairing p ![0,2] ∈ ((fun b => pairing p b) '' superdiff F 0) from ⟨_,h2,rfl⟩)
      simpa [localization,pairing,Fin.sum_univ_two,mul_comm] using hh
  · change F p ≤ sInf ((fun b => pairing p b) '' superdiff F 0)
    apply le_csInf (show ((fun b => pairing p b) '' superdiff F 0).Nonempty from ⟨_,⟨_,h1,rfl⟩⟩)
    rintro _ ⟨b,hb,rfl⟩
    simpa only [h0,sub_zero] using hb p

private theorem matroidal : IsMatroidal F := by
  refine ⟨?_,?_,?_⟩
  · intro c hc p
    dsimp [F]
    rw [mul_min_of_nonneg _ _ hc.le]
    congr 1 <;> ring
  · intro X Y
    fin_cases X <;> fin_cases Y <;> norm_num [F,charVec]
  · intro p σ hσ
    simp only [Fintype.card_fin] at *
    have hne : σ 0 ≠ σ 1 := fun he => (by decide : (0 : Fin 2) ≠ 1) (σ.injective he)
    have he : σ=Equiv.refl (Fin 2) ∨ σ=Equiv.swap (0 : Fin 2) 1 := by
      generalize h0 : σ 0 = a
      generalize h1 : σ 1 = b
      fin_cases a <;> fin_cases b
      · exact (hne (h0.trans h1.symm)).elim
      · left; apply Equiv.ext; intro i; fin_cases i
        · change σ 0=0; exact h0
        · change σ 1=1; exact h1
      · right; apply Equiv.ext; intro i; fin_cases i
        · change σ 0=1; exact h0
        · change σ 1=0; exact h1
      · exact (hne (h0.trans h1.symm)).elim
    rcases he with rfl|rfl
    · have hh := hσ (show (0 : Fin 2) ≤ 1 by decide)
      change p 1 ≤ p 0 at hh
      change F p = ∑ j : Fin 2,(p j-(if hj : (j : ℕ)+1<2 then p ⟨(j : ℕ)+1,hj⟩ else 0))*F (charVec (Finset.univ.filter (fun v : Fin 2 => v ≤ j)))
      rw [Fin.sum_univ_two]
      norm_num [F,charVec]
      rw [min_eq_right (by linarith)]
      ring
    · have hh := hσ (show (0 : Fin 2) ≤ 1 by decide)
      change p 0 ≤ p 1 at hh
      change F p = ∑ j : Fin 2,(p (Equiv.swap (0 : Fin 2) 1 j)-(if hj : (j : ℕ)+1<2 then p (Equiv.swap (0 : Fin 2) 1 ⟨(j : ℕ)+1,hj⟩) else 0))*F (charVec (Finset.univ.filter (fun v : Fin 2 => Equiv.swap (0 : Fin 2) 1 v ≤ j)))
      have hf0 : Finset.univ.filter (fun v : Fin 2 => Equiv.swap (0 : Fin 2) 1 v ≤ 0)={1} := by ext i; fin_cases i <;> decide
      have hf1 : Finset.univ.filter (fun v : Fin 2 => Equiv.swap (0 : Fin 2) 1 v ≤ 1)=Finset.univ := by ext i; fin_cases i <;> decide
      rw [Fin.sum_univ_two,hf0,hf1]
      norm_num [F,charVec,Equiv.swap_apply_def]
      rw [min_eq_left (by linarith)]
      norm_num [Finset.mem_filter]
      ring

private theorem argmax : argmaxB B (perturb g (0 : Fin 2 → ℝ))={![2,0],![0,2]} := by
  classical
  have hg (x : Fin 2 → ℤ) : perturb g (0 : Fin 2 → ℝ) x=g x := by simp [perturb,pairing]
  ext x
  simp only [argmaxB,Finset.mem_filter,hg]
  constructor
  · rintro ⟨hx,hm⟩
    have hx : x=![2,0] ∨ x=![1,1] ∨ x=![0,2] := by simpa [B] using hx
    rcases hx with rfl|rfl|rfl
    · simp
    · have hh := hm ![2,0] (by simp [B])
      norm_num [g,funext_iff,Fin.forall_fin_two] at hh
    · simp
  · intro hx
    have hx : x=![2,0] ∨ x=![0,2] := by simpa using hx
    rcases hx with rfl|rfl
    all_goals refine ⟨by simp [B],?_⟩
    all_goals intro y hy
    all_goals norm_num [g,funext_iff,Fin.forall_fin_two]
    all_goals split_ifs <;> norm_num

private theorem not_base : ¬IsIntegralBaseSet ({![2,0],![0,2]} : Finset (Fin 2 → ℤ)) := by
  intro h
  obtain ⟨v,hv,hmem⟩ := h.2 ![2,0] (by simp) ![0,2] (by simp) 0 (by norm_num)
  fin_cases v <;> norm_num [chi,Pi.single_apply,Matrix.vecHead,Matrix.vecTail,funext_iff,Fin.forall_fin_two] at *

theorem solution : ¬(∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ) (p₀ : V → ℝ),
    IsMatroidal (localization (concaveConj B ω) p₀) ↔
      IsIntegralBaseSet (argmaxB B (perturb ω (-p₀)))) := by
  intro h
  have hh := (h (Fin 2) B base g 0).mp (loc ▸ matroidal)
  rw [neg_zero,argmax] at hh
  exact not_base hh
