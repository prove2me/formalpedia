-- Prove2me | solution 1 for Soar.pick_law
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T00:38:53.501985+00:00
-- url     : https://prove2.me/submissions/7bd35e50-d6ff-47e4-9073-08c0256c1d26

import Mathlib
import Definitions.Def_SoarPolicy

set_option autoImplicit false

open MeasureTheory

namespace SoarPoolLawAux

lemma card_fiber (n : ℕ) (i : Fin (n + 1)) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) => i = σ.symm 0)).card
      = (Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) => σ.symm 0 = 0)).card := by
  refine Finset.card_nbij' (fun σ => σ * Equiv.swap 0 i) (fun σ => σ * Equiv.swap 0 i)
    ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
    rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply, ← hσ, Equiv.symm_swap,
      Equiv.swap_apply_right]
  · intro σ hσ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
    rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply, hσ, Equiv.symm_swap,
      Equiv.swap_apply_left]
  · intro σ _
    simp [mul_assoc]
  · intro σ _
    simp [mul_assoc]

lemma uniform_slot (k : ℕ) :
    MeasurePreserving (fun σ : Equiv.Perm (Fin (k + 1)) => σ.symm 0)
      (SoarUniform (Equiv.Perm (Fin (k + 1)))) (SoarUniform (Fin (k + 1))) := by
  refine ⟨Measurable.of_discrete, ?_⟩
  unfold SoarUniform
  rw [PMF.toMeasure_map (hf := Measurable.of_discrete)]
  congr 1
  ext i
  rw [PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_fiber k i]
  set c := (Finset.univ.filter (fun σ : Equiv.Perm (Fin (k + 1)) => σ.symm 0 = 0)).card with hc
  have htot : Fintype.card (Equiv.Perm (Fin (k + 1))) = (k + 1) * c := by
    rw [← Finset.card_univ,
      Finset.card_eq_sum_card_fiberwise (f := fun σ : Equiv.Perm (Fin (k + 1)) => σ.symm 0)
        (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    have : ∀ j : Fin (k + 1),
        (Finset.univ.filter (fun σ : Equiv.Perm (Fin (k + 1)) => σ.symm 0 = j)).card = c := by
      intro j
      rw [hc, ← card_fiber k j]
      congr 1
      ext σ
      simp [eq_comm]
    simp [this]
  have hcpos : c ≠ 0 := by
    intro h0
    have := Fintype.card_pos (α := Equiv.Perm (Fin (k + 1)))
    rw [h0, mul_zero] at htot
    omega
  rw [htot, Fintype.card_fin]
  push_cast
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inr (by exact_mod_cast hcpos)),
    mul_comm, mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hcpos)
      (ENNReal.natCast_ne_top _), mul_one]

lemma perm_invariant {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Measure.map (fun y : Fin n → X => y ∘ σ) (Measure.pi fun _ : Fin n => P)
      = Measure.pi fun _ : Fin n => P := by
  have h := measurePreserving_piCongrLeft (fun _ : Fin n => P) σ.symm
  have hfun : (⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin n => X) σ.symm))
      = fun y : Fin n → X => y ∘ σ := by
    funext y i
    have := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n => X) σ.symm y (σ i)
    simpa using this
  rw [← hfun]
  exact h.map_eq


lemma pool_mp {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (k : ℕ) :
    MeasurePreserving (fun r : SoarEpochRand X k => (SoarPool r, r.2.2.symm 0))
        (SoarEpochMeasure P k)
      ((Measure.pi fun _ : Fin (k + 1) => P).prod (SoarUniform (Fin (k + 1)))) := by
  have hcons : MeasurePreserving
      (fun p : X × (Fin k → X) => Fin.cons (α := fun _ => X) p.1 p.2)
      (P.prod (Measure.pi fun _ : Fin k => P)) (Measure.pi fun _ : Fin (k + 1) => P) := by
    have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => P) 0).symm
    convert h using 1
    funext p
    (try simp [MeasurableEquiv.piFinSuccAbove_symm_apply])
    rfl
  have hA : MeasurePreserving
      (MeasurableEquiv.prodAssoc (α := X) (β := Fin k → X)
        (γ := Equiv.Perm (Fin (k + 1)))).symm
      (SoarEpochMeasure P k)
      ((P.prod (Measure.pi fun _ : Fin k => P)).prod (SoarUniform _)) :=
    MeasurePreserving.symm _ ⟨MeasurableEquiv.prodAssoc.measurable, Measure.prodAssoc_prod⟩
  have hH := (Measure.measurePreserving_swap).comp
    ((hcons.prod (MeasurePreserving.id (SoarUniform (Equiv.Perm (Fin (k + 1)))))).comp hA)
  have hmeas : Measurable (Function.uncurry
      fun (σ : Equiv.Perm (Fin (k + 1))) (y : Fin (k + 1) → X) => y ∘ σ) := by
    apply measurable_from_prod_countable_right
    intro σ
    exact measurable_pi_lambda _ fun j => measurable_pi_apply (σ j)
  have hS := (SoarPoolLawAux.uniform_slot k).skew_product hmeas
    (ae_of_all _ fun σ => SoarPoolLawAux.perm_invariant P (k + 1) σ)
  have hG := (Measure.measurePreserving_swap).comp hS
  exact hG.comp hH

lemma equiv_uniform (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) :
    Measure.map (fun s : Fin (n + 1) => π s) (SoarUniform (Fin (n + 1)))
      = SoarUniform (Fin (n + 1)) := by
  refine Measure.ext_of_singleton fun i => ?_
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton i)]
  have : (fun s : Fin (n + 1) => π s) ⁻¹' {i} = {π.symm i} := by
    ext s; simp [Equiv.eq_symm_apply]
  rw [this]
  unfold SoarUniform
  simp [PMF.toMeasure_apply_singleton]

end SoarPoolLawAux

open MeasureTheory in
theorem solution {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m))
    (hopt : SoarSolverMeasurable opt) (k : ℕ) :
    Measure.map (fun ω : (Fin (k + 1) → Y) × SoarEpochRand X k => (ω.1, SoarPick opt ω.1 ω.2))
        ((Measure.pi fun _ : Fin (k + 1) => Q).prod (SoarEpochMeasure P k))
      = (Measure.pi fun _ : Fin (k + 1) => Q).prod (SoarUniform (Fin (k + 1))) := by
  have h1 := (MeasurePreserving.id (Measure.pi fun _ : Fin (k + 1) => Q)).prod
    (SoarPoolLawAux.pool_mp P k)
  have hA : MeasurePreserving
      (MeasurableEquiv.prodAssoc (α := Fin (k + 1) → Y) (β := Fin (k + 1) → X)
        (γ := Fin (k + 1))).symm
      ((Measure.pi fun _ : Fin (k + 1) => Q).prod
        ((Measure.pi fun _ : Fin (k + 1) => P).prod (SoarUniform (Fin (k + 1)))))
      (((Measure.pi fun _ : Fin (k + 1) => Q).prod (Measure.pi fun _ : Fin (k + 1) => P)).prod
        (SoarUniform (Fin (k + 1)))) :=
    MeasurePreserving.symm _ ⟨MeasurableEquiv.prodAssoc.measurable, Measure.prodAssoc_prod⟩
  have hfst : MeasurePreserving (Prod.fst : (Fin (k + 1) → Y) × (Fin (k + 1) → X) → _)
      ((Measure.pi fun _ : Fin (k + 1) => Q).prod (Measure.pi fun _ : Fin (k + 1) => P))
      (Measure.pi fun _ : Fin (k + 1) => Q) :=
    ⟨measurable_fst, by rw [Measure.map_fst_prod]; simp⟩
  have hgm : Measurable (Function.uncurry
      fun (p : (Fin (k + 1) → Y) × (Fin (k + 1) → X)) (s : Fin (k + 1)) => opt (k + 1) p.2 p.1 s) := by
    apply measurable_from_prod_countable_left
    intro s
    have h := (hopt (k + 1)).comp (measurable_snd.prodMk measurable_fst)
    exact (Measurable.of_discrete (f := fun π : Equiv.Perm (Fin (k + 1)) => π s)).comp h
  have hS := hfst.skew_product hgm
    (ae_of_all _ fun p => SoarPoolLawAux.equiv_uniform k (opt (k + 1) p.2 p.1))
  rw [← ((hS.comp hA).comp h1).map_eq]
  rfl
