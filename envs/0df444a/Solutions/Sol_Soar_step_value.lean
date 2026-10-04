-- Prove2me | solution 1 for Soar.step_value
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T01:43:42.178851+00:00
-- url     : https://prove2.me/submissions/3a5dbfd0-abd6-4e42-9551-b22812127ea9

import Mathlib
import Definitions.Def_SoarPolicy

set_option autoImplicit false

open MeasureTheory

namespace SoarStepValueAux

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
  have hS := (SoarStepValueAux.uniform_slot k).skew_product hmeas
    (ae_of_all _ fun σ => SoarStepValueAux.perm_invariant P (k + 1) σ)
  have hG := (Measure.measurePreserving_swap).comp hS
  exact hG.comp hH

lemma hs_eq {X Y : Type*} (φ : X → Y → ℝ)
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m))
    (hsolver : SoarIsSolver φ opt) {n : ℕ} (x : Fin n → X) (y : Fin n → Y) :
    SoarHindsightSum φ x y = ∑ t, φ (x t) (y (opt n x y t)) := by
  unfold SoarHindsightSum
  apply le_antisymm
  · exact ciSup_le fun σ => hsolver n x y σ
  · exact le_ciSup (Set.finite_range fun σ : Equiv.Perm (Fin n) =>
      ∑ t, φ (x t) (y (σ t))).bddAbove (opt n x y)

lemma F_meas {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (φ : X → Y → ℝ)
    (hφ : Measurable (Function.uncurry φ))
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m))
    (hopt : SoarSolverMeasurable opt) (n : ℕ) :
    Measurable (fun p : ((Fin n → Y) × (Fin n → X)) × Fin n =>
      φ (p.1.2 p.2) (p.1.1 (opt n p.1.2 p.1.1 p.2))) := by
  apply measurable_from_prod_countable_left
  intro s
  have h1 : Measurable (fun q : (Fin n → Y) × (Fin n → X) => q.2 s) :=
    (measurable_pi_apply s).comp measurable_snd
  have h2 : Measurable (fun q : (Fin n → Y) × (Fin n → X) => (q.1, opt n q.2 q.1)) :=
    measurable_fst.prodMk ((hopt n).comp measurable_swap)
  have h3 : Measurable (fun r : (Fin n → Y) × Equiv.Perm (Fin n) => r.1 (r.2 s)) := by
    apply measurable_from_prod_countable_left
    intro π
    exact measurable_pi_apply (π s)
  exact hφ.comp (h1.prodMk (h3.comp h2))

end SoarStepValueAux

open MeasureTheory in
theorem solution {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : X → Y → ℝ) (hφ : Measurable (Function.uncurry φ)) (C : ℝ) (hC : SoarBounded φ C)
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m))
    (hsolver : SoarIsSolver φ opt) (hopt : SoarSolverMeasurable opt) (k : ℕ) :
    ∫ ω : (Fin (k + 1) → Y) × SoarEpochRand X k, φ ω.2.1 (ω.1 (SoarPick opt ω.1 ω.2))
        ∂(Measure.pi fun _ : Fin (k + 1) => Q).prod (SoarEpochMeasure P k)
      = SoarHindsight P Q φ (k + 1) := by
  let F : ((Fin (k + 1) → Y) × (Fin (k + 1) → X)) × Fin (k + 1) → ℝ :=
    fun p => φ (p.1.2 p.2) (p.1.1 (opt (k + 1) p.1.2 p.1.1 p.2))
  have hF : Measurable F := SoarStepValueAux.F_meas φ hφ opt hopt (k + 1)
  let g : (Fin (k + 1) → Y) × SoarEpochRand X k →
      ((Fin (k + 1) → Y) × (Fin (k + 1) → X)) × Fin (k + 1) :=
    fun ω => ((ω.1, SoarPool ω.2), ω.2.2.2.symm 0)
  have hg : MeasurePreserving g
      ((Measure.pi fun _ : Fin (k + 1) => Q).prod (SoarEpochMeasure P k))
      (((Measure.pi fun _ : Fin (k + 1) => Q).prod (Measure.pi fun _ : Fin (k + 1) => P)).prod
        (SoarUniform (Fin (k + 1)))) := by
    have h1 := (MeasurePreserving.id (Measure.pi fun _ : Fin (k + 1) => Q)).prod
      (SoarStepValueAux.pool_mp P k)
    have h2 : MeasurePreserving
        (MeasurableEquiv.prodAssoc (α := Fin (k + 1) → Y) (β := Fin (k + 1) → X)
          (γ := Fin (k + 1))).symm
        ((Measure.pi fun _ : Fin (k + 1) => Q).prod
          ((Measure.pi fun _ : Fin (k + 1) => P).prod (SoarUniform (Fin (k + 1)))))
        (((Measure.pi fun _ : Fin (k + 1) => Q).prod (Measure.pi fun _ : Fin (k + 1) => P)).prod
          (SoarUniform (Fin (k + 1)))) :=
      MeasurePreserving.symm _ ⟨MeasurableEquiv.prodAssoc.measurable, Measure.prodAssoc_prod⟩
    exact h2.comp h1
  have hpt : ∀ ω : (Fin (k + 1) → Y) × SoarEpochRand X k,
      φ ω.2.1 (ω.1 (SoarPick opt ω.1 ω.2)) = F (g ω) := by
    intro ω
    simp [F, g, SoarPick, SoarPool]
  have hbd : ∀ p, ‖F p‖ ≤ C := fun p => by
    simpa [Real.norm_eq_abs] using hC _ _
  have hint : Integrable F
      (((Measure.pi fun _ : Fin (k + 1) => Q).prod (Measure.pi fun _ : Fin (k + 1) => P)).prod
        (SoarUniform (Fin (k + 1)))) :=
    Integrable.of_bound hF.aestronglyMeasurable C (ae_of_all _ hbd)
  calc _ = ∫ ω, F (g ω) ∂((Measure.pi fun _ : Fin (k + 1) => Q).prod (SoarEpochMeasure P k)) :=
        integral_congr_ae (ae_of_all _ hpt)
    _ = ∫ p, F p ∂(Measure.map g
          ((Measure.pi fun _ : Fin (k + 1) => Q).prod (SoarEpochMeasure P k))) :=
        (integral_map hg.measurable.aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ p, F p ∂(((Measure.pi fun _ : Fin (k + 1) => Q).prod
          (Measure.pi fun _ : Fin (k + 1) => P)).prod (SoarUniform (Fin (k + 1)))) := by
        rw [hg.map_eq]
    _ = ∫ q, ∫ s, F (q, s) ∂(SoarUniform (Fin (k + 1)))
          ∂((Measure.pi fun _ : Fin (k + 1) => Q).prod (Measure.pi fun _ : Fin (k + 1) => P)) :=
        integral_prod F hint
    _ = ∫ q, SoarHindsightSum φ q.2 q.1 / ((k + 1 : ℕ) : ℝ)
          ∂((Measure.pi fun _ : Fin (k + 1) => Q).prod (Measure.pi fun _ : Fin (k + 1) => P)) := by
        congr 1
        funext q
        rw [SoarStepValueAux.hs_eq φ opt hsolver, SoarUniform, PMF.integral_eq_sum,
          Finset.sum_div]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp [F, PMF.uniformOfFintype_apply, div_eq_inv_mul]
        left
        exact_mod_cast ENNReal.toReal_natCast (k + 1)
    _ = (∫ p, SoarHindsightSum φ p.1 p.2
          ∂((Measure.pi fun _ : Fin (k + 1) => P).prod (Measure.pi fun _ : Fin (k + 1) => Q)))
          / ((k + 1 : ℕ) : ℝ) := by
        rw [integral_div]
        congr 1
        exact integral_prod_swap
          (fun p : (Fin (k + 1) → X) × (Fin (k + 1) → Y) => SoarHindsightSum φ p.1 p.2)
    _ = SoarHindsight P Q φ (k + 1) := rfl
