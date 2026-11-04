-- Prove2me | solution 1 for ThreeSum.TernaryPairedSupport.physical_support_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:45:30.723273+00:00
-- url     : https://prove2.me/submissions/a15bee48-91ff-441f-8aa9-ffa150de0522

import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPairedSupport
import Theorems.Thm_ThreeSum_TernaryPairedSupport_exists_joint_independent
import Theorems.Thm_ThreeSum_TernaryPairedSupport_taggedEndpoints_independent

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedSupport
open Finset
attribute [local instance] Classical.propDecidable
variable {K E V W : Type*} [Field K] [Fintype K]
  [AddCommGroup V] [Module K V] [Fintype V]
  [AddCommGroup W] [Module K W] [Fintype W]
  [Fintype E]
variable {P D : Type*} [Fintype P] [DecidableEq D]
namespace ThreeSum.TernaryPairedSupport
theorem _root_.solution (L R : P → V) (H : V →ₗ[K] W) (o : W)
    (mode : P → D) (m : ℕ)
    (hroot : ∀ i, H (L i+R i)=o)
    (hmode : ∀ a b, L a+R a=L b+R b → mode a=mode b)
    (hhash : ∀ a b, H (L a)=H (L b) → mode a=mode b)
    (hno : ∀ e : Fin m → P,
      ¬ LinearIndependent K (taggedEndpoints (K := K) (L ∘ e) (R ∘ e))) :
    (physicalSupport mode).card ≤ 2 * Fintype.card K ^ m := by
  classical
  let S := physicalSupport mode
  have hrep : ∀ d : S, ∃ i : P, mode i=d.val := by
    intro d
    obtain ⟨i,hi,he⟩ := mem_image.mp d.property
    exact ⟨i,he⟩
  let rep : S → P := fun d => Classical.choose (hrep d)
  have hr : ∀ d : S, mode (rep d)=d.val := fun d => Classical.choose_spec (hrep d)
  let f : S → V × K := fun d => (L (rep d)+R (rep d),1)
  let g : S → W × K := fun d => (H (L (rep d)),1)
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    have hh := hmode (rep a) (rep b) (congrArg Prod.fst he)
    simpa only [hr] using hh
  have hg : Function.Injective g := by
    intro a b he
    apply Subtype.ext
    have hh := hhash (rep a) (rep b) (congrArg Prod.fst he)
    simpa only [hr] using hh
  by_contra! hlarge
  have hc : 2 * Fintype.card K ^ m < Fintype.card S := by
    simpa only [Fintype.card_coe] using hlarge
  obtain ⟨e,hef,heg⟩ := exists_joint_independent f g hf hg m hc
  have he := taggedEndpoints_independent (fun i => L (rep (e i)))
    (fun i => R (rep (e i))) H o (fun i => hroot (rep (e i))) hef heg
  exact hno (rep ∘ e) he
end ThreeSum.TernaryPairedSupport
