-- Prove2me | solution 1 for PandoraBO.Private20261023.coordinate_nonanticipative_factorization
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T01:19:00.324108+00:00
-- url     : https://prove2.me/submissions/7fdedf9f-804b-4400-bd63-f4ae189afb65

import Definitions.Def_PandoraBO_Model
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Factorization along an unobserved reward coordinate

A function that is unchanged when one reward coordinate changes factors
through the other coordinates and the independent randomization seed.
The proof explicitly splits that coordinate from the finite product measure.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace PandoraBO.Private20261023.CoordinateFactorization

private theorem seed_probability : IsProbabilityMeasure seedLaw := by
  constructor
  simp [seedLaw, Real.volume_Icc]

theorem factorization_core {n : ℕ} (M : Instance n) (i : Box n)
    (a : Outcome n → ℝ) (g : ℝ → ℝ)
    (ha : ∀ (r r' : Box n → ℝ) (u : ℝ),
      (∀ j, j ≠ i → r j = r' j) → a (r, u) = a (r', u)) :
    (∫ ω : Outcome n, a ω * g (ω.1 i) ∂jointLaw M) =
      (∫ ω : Outcome n, a ω ∂jointLaw M) * (∫ y : ℝ, g y ∂M.law i) := by
  letI : ∀ j, IsProbabilityMeasure (M.law j) := M.law_probability
  letI : IsProbabilityMeasure seedLaw := seed_probability
  let ν : Measure ((Fin n → ℝ) × ℝ) :=
    (Measure.pi fun j : Fin n => M.law (i.succAbove j)).prod seedLaw
  let e : Outcome n ≃ᵐ ℝ × ((Fin n → ℝ) × ℝ) :=
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Box n => ℝ) i).prodCongr
      (MeasurableEquiv.refl ℝ)).trans MeasurableEquiv.prodAssoc
  have he : MeasurePreserving e (jointLaw M) ((M.law i).prod ν) := by
    exact (measurePreserving_prodAssoc (M.law i)
      (Measure.pi fun j : Fin n => M.law (i.succAbove j)) seedLaw).comp
      ((measurePreserving_piFinSuccAbove M.law i).prod (MeasurePreserving.id seedLaw))
  have hinv : ∀ p : ℝ × ((Fin n → ℝ) × ℝ),
      e.symm p = (i.insertNth p.1 p.2.1, p.2.2) := by
    intro p
    rfl
  let a0 : ((Fin n → ℝ) × ℝ) → ℝ := fun q => a (i.insertNth 0 q.1, q.2)
  have ha0 : ∀ p : ℝ × ((Fin n → ℝ) × ℝ), a (e.symm p) = a0 p.2 := by
    intro p
    rw [hinv p]
    apply ha
    intro j hji
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
    simp only [Fin.insertNth_apply_succAbove]
  have hcoord : ∀ p : ℝ × ((Fin n → ℝ) × ℝ), (e.symm p).1 i = p.1 := by
    intro p
    rw [hinv p]
    exact Fin.insertNth_apply_same (α := fun _ : Fin (n + 1) => ℝ) i p.1 p.2.1
  have hIa : (∫ ω : Outcome n, a ω ∂jointLaw M) = ∫ q, a0 q ∂ν := by
    calc
      (∫ ω : Outcome n, a ω ∂jointLaw M) =
          ∫ p, a (e.symm p) ∂(M.law i).prod ν := (he.symm.integral_comp' a).symm
      _ = ∫ p : ℝ × ((Fin n → ℝ) × ℝ), a0 p.2 ∂(M.law i).prod ν := by
        apply integral_congr_ae
        exact ae_of_all _ ha0
      _ = ∫ q, a0 q ∂ν := by
        rw [integral_fun_snd]
        simp only [probReal_univ, one_smul]
  calc
    (∫ ω : Outcome n, a ω * g (ω.1 i) ∂jointLaw M) =
        ∫ p, a (e.symm p) * g ((e.symm p).1 i) ∂(M.law i).prod ν :=
      (he.symm.integral_comp' (fun ω : Outcome n => a ω * g (ω.1 i))).symm
    _ = ∫ p : ℝ × ((Fin n → ℝ) × ℝ), g p.1 * a0 p.2 ∂(M.law i).prod ν := by
      apply integral_congr_ae
      apply ae_of_all
      intro p
      dsimp only
      rw [ha0 p, hcoord p, mul_comm]
    _ = (∫ y : ℝ, g y ∂M.law i) * ∫ q, a0 q ∂ν := integral_prod_mul g a0
    _ = (∫ ω : Outcome n, a ω ∂jointLaw M) * (∫ y : ℝ, g y ∂M.law i) := by
      rw [hIa, mul_comm]

end PandoraBO.Private20261023.CoordinateFactorization

theorem solution {n : ℕ} (M : PandoraBO.Instance n) (i : PandoraBO.Box n)
    (a : PandoraBO.Outcome n → ℝ) (g : ℝ → ℝ)
    (ha : ∀ (r r' : PandoraBO.Box n → ℝ) (u : ℝ),
      (∀ j, j ≠ i → r j = r' j) → a (r, u) = a (r', u)) :
    (∫ ω : PandoraBO.Outcome n, a ω * g (ω.1 i) ∂PandoraBO.jointLaw M) =
      (∫ ω : PandoraBO.Outcome n, a ω ∂PandoraBO.jointLaw M) *
        (∫ y : ℝ, g y ∂M.law i) := by
  exact PandoraBO.Private20261023.CoordinateFactorization.factorization_core M i a g ha
