-- Prove2me | solution 1 for ProximityPadePunctureTransfer.mca_card_le_punctured_add
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-04T17:22:03.664109+00:00
-- url     : https://prove2.me/submissions/c4b2af1c-a91b-4694-aaa6-9622ab6d61f5

import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push
import Mathlib.Tactic.Choose
import Lean.Elab.Tactic.Omega


noncomputable section
open Polynomial
namespace ProximityPadePunctureTransfer

attribute [local instance] Classical.propDecidable

variable {F I : Type*} [Field F] [DecidableEq F] [DecidableEq I]

def Fits (x u : I → F) (w : ℕ) (T : Finset I) : Prop :=
  ∃ P : F[X], P.natDegree ≤ w ∧ ∀ i ∈ T, P.eval (x i) = u i

def MCA (nodes : Finset I) (x u0 u1 : I → F) (w A : ℕ) (γ : F) : Prop :=
  ∃ T : Finset I, T ⊆ nodes ∧ A ≤ T.card ∧
    Fits x (fun i => u0 i + γ * u1 i) w T ∧
    ¬(Fits x u0 w T ∧ Fits x u1 w T)

def Joint (nodes : Finset I) (x u0 u1 : I → F) (w A : ℕ)
    (pair : F[X] × F[X]) : Prop :=
  pair.1.natDegree ≤ w ∧ pair.2.natDegree ≤ w ∧
    A ≤ (nodes.filter (fun i => pair.1.eval (x i) = u0 i ∧
      pair.2.eval (x i) = u1 i)).card

def mismatchRatio (x u0 u1 : I → F) (pair : F[X] × F[X]) (z : I) : F :=
  -(u0 z - pair.1.eval (x z)) / (u1 z - pair.2.eval (x z))

theorem lost_parameter_witness (nodes C : Finset I) (x u0 u1 : I → F)
    (w A A' : ℕ) (hinj : Set.InjOn x (nodes : Set I))
    (hA : A' + C.card ≤ A) (hw : w < A') (γ : F)
    (hγ : MCA nodes x u0 u1 w A γ)
    (hlost : ¬MCA (nodes \ C) x u0 u1 w A' γ) :
    ∃ pair : F[X] × F[X], Joint (nodes \ C) x u0 u1 w A' pair ∧
      ∃ z ∈ C, u1 z - pair.2.eval (x z) ≠ 0 ∧
        γ = mismatchRatio x u0 u1 pair z := by
  classical
  obtain ⟨T, hT, hcard, ⟨P, hPdeg, hPfit⟩, hnot⟩ := hγ
  have hsub : T \ C ⊆ nodes \ C := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨hT (Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hi).2⟩
  have hsize : A' ≤ (T \ C).card := by
    have := Finset.card_le_card_sdiff_add_card (s := T) (t := C)
    omega
  have hboth : Fits x u0 w (T \ C) ∧ Fits x u1 w (T \ C) := by
    by_contra hn
    apply hlost
    exact ⟨T \ C, hsub, hsize,
      ⟨P, hPdeg, fun i hi => hPfit i (Finset.mem_sdiff.mp hi).1⟩, hn⟩
  obtain ⟨⟨P0, h0deg, h0fit⟩, ⟨P1, h1deg, h1fit⟩⟩ := hboth
  have hsumdeg : (P0 + γ • P1).natDegree ≤ w :=
    (Polynomial.natDegree_add_le _ _).trans
      (max_le h0deg ((Polynomial.natDegree_smul_le _ _).trans h1deg))
  have heq : P = P0 + γ • P1 := by
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq P (P0 + γ • P1)
      (f := fun i : ↥(T \ C) => x i)
    · intro a b hab
      apply Subtype.ext
      exact hinj (hT (Finset.mem_sdiff.mp a.property).1)
        (hT (Finset.mem_sdiff.mp b.property).1) hab
    · intro i
      simpa [h0fit i i.property, h1fit i i.property] using
        hPfit i (Finset.mem_sdiff.mp i.property).1
    · simpa only [Fintype.card_coe] using
        (max_le hPdeg hsumdeg).trans_lt (hw.trans_le hsize)
  have hbad : ∃ z ∈ T, ¬(P0.eval (x z) = u0 z ∧ P1.eval (x z) = u1 z) := by
    by_contra hn
    push Not at hn
    exact hnot ⟨⟨P0, h0deg, fun i hi => (hn i hi).1⟩,
      ⟨P1, h1deg, fun i hi => (hn i hi).2⟩⟩
  obtain ⟨z, hzT, hzbad⟩ := hbad
  have hzC : z ∈ C := by
    by_contra hz
    exact hzbad ⟨h0fit z (Finset.mem_sdiff.mpr ⟨hzT, hz⟩),
      h1fit z (Finset.mem_sdiff.mpr ⟨hzT, hz⟩)⟩
  have hzero : (u0 z - P0.eval (x z)) + γ * (u1 z - P1.eval (x z)) = 0 := by
    have hh := hPfit z hzT
    rw [heq] at hh
    simp only [Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul] at hh
    linear_combination -hh
  have hslope : u1 z - P1.eval (x z) ≠ 0 := by
    intro hs
    rw [hs, mul_zero, add_zero] at hzero
    exact hzbad ⟨(sub_eq_zero.mp hzero).symm, (sub_eq_zero.mp hs).symm⟩
  refine ⟨(P0,P1), ⟨h0deg, h1deg, ?_⟩, z, hzC, hslope, ?_⟩
  · apply hsize.trans (Finset.card_le_card ?_)
    intro i hi
    exact Finset.mem_filter.mpr ⟨hsub hi, h0fit i hi, h1fit i hi⟩
  · apply (eq_div_iff hslope).mpr
    dsimp [mismatchRatio]
    linear_combination hzero


/-- Removing a fixed set of nodes costs at most one parameter per joint pair and removed node. -/
theorem mca_card_le_punctured_add_internal (nodes C : Finset I) (x u0 u1 : I → F)
    (w A A' L : ℕ) (hinj : Set.InjOn x (nodes : Set I))
    (hA : A' + C.card ≤ A) (hw : w < A')
    (hpair : ∀ D : Finset (F[X] × F[X]),
      (∀ pair ∈ D, Joint (nodes \ C) x u0 u1 w A' pair) → D.card ≤ L)
    (Γ : Finset F) (hΓ : ∀ γ ∈ Γ, MCA nodes x u0 u1 w A γ) :
    Γ.card ≤ (Γ.filter (MCA (nodes \ C) x u0 u1 w A')).card + C.card * L := by
  classical
  let lost := Γ.filter (fun γ => ¬MCA (nodes \ C) x u0 u1 w A' γ)
  have hwit : ∀ γ : ↥lost, ∃ pair : F[X] × F[X],
      Joint (nodes \ C) x u0 u1 w A' pair ∧
        ∃ z ∈ C, u1 z - pair.2.eval (x z) ≠ 0 ∧
          γ.val = mismatchRatio x u0 u1 pair z := by
    intro γ
    have hg := Finset.mem_filter.mp γ.property
    exact lost_parameter_witness nodes C x u0 u1 w A A' hinj hA hw γ
      (hΓ γ hg.1) hg.2
  choose pair hp z hz hden hval using hwit
  let D := Finset.univ.image pair
  have hD : D.card ≤ L := by
    apply hpair
    intro p hpmem
    obtain ⟨γ, _, rfl⟩ := Finset.mem_image.mp hpmem
    exact hp γ
  let cover := (D.product C).image (fun q => mismatchRatio x u0 u1 q.1 q.2)
  have hcover : cover.card ≤ C.card * L := by
    calc
      cover.card ≤ (D.product C).card := Finset.card_image_le
      _ = D.card * C.card := Finset.card_product D C
      _ ≤ L * C.card := Nat.mul_le_mul_right _ hD
      _ = C.card * L := Nat.mul_comm _ _
  have hsub : Γ ⊆ Γ.filter (MCA (nodes \ C) x u0 u1 w A') ∪ cover := by
    intro γ hγ
    by_cases hkeep : MCA (nodes \ C) x u0 u1 w A' γ
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, hkeep⟩)
    · apply Finset.mem_union_right
      let g : ↥lost := ⟨γ, Finset.mem_filter.mpr ⟨hγ, hkeep⟩⟩
      apply Finset.mem_image.mpr
      exact ⟨(pair g, z g), Finset.mem_product.mpr
        ⟨Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩, hz g⟩, (hval g).symm⟩
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_left hcover _))

end ProximityPadePunctureTransfer

open Polynomial

theorem solution {F I : Type*} [Field F] [DecidableEq F] [DecidableEq I]
    (nodes C : Finset I) (x u0 u1 : I → F) (w A A' L : ℕ)
    (hinj : Set.InjOn x (nodes : Set I)) (hA : A' + C.card ≤ A) (hw : w < A') :
    let fits : (I → F) → Finset I → Prop := fun u T =>
      ∃ P : F[X], P.natDegree ≤ w ∧ ∀ i ∈ T, P.eval (x i) = u i
    let mca : Finset I → ℕ → F → Prop := fun domain threshold γ =>
      ∃ T : Finset I, T ⊆ domain ∧ threshold ≤ T.card ∧
        fits (fun i => u0 i + γ * u1 i) T ∧ ¬(fits u0 T ∧ fits u1 T)
    let joint : F[X] × F[X] → Prop := fun pair =>
      pair.1.natDegree ≤ w ∧ pair.2.natDegree ≤ w ∧
        A' ≤ ((nodes \ C).filter (fun i => pair.1.eval (x i) = u0 i ∧
          pair.2.eval (x i) = u1 i)).card
    (∀ D : Finset (F[X] × F[X]), (∀ pair ∈ D, joint pair) → D.card ≤ L) →
    ∀ Γ : Finset F, (∀ γ ∈ Γ, mca nodes A γ) →
      Γ.card ≤ (@Finset.filter F (mca (nodes \ C) A')
        (fun _ => Classical.propDecidable _) Γ).card + C.card * L := by
  dsimp only
  intro hpair Γ hΓ
  exact ProximityPadePunctureTransfer.mca_card_le_punctured_add_internal
    nodes C x u0 u1 w A A' L hinj hA hw hpair Γ hΓ
