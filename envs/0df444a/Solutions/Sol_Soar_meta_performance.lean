-- Prove2me | solution 1 for Soar.meta_performance
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T08:26:32.278786+00:00
-- url     : https://prove2.me/submissions/402bfd3d-8173-4837-9731-f74617ce2249

import Mathlib
import Definitions.Def_SoarPolicy

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

namespace SoarAux

universe u

/-! ### Splitting off the last coordinate of a dependent product -/

def snocME {k : ℕ} (α : Fin (k + 1) → Type u) [∀ i, MeasurableSpace (α i)] :
    (∀ i, α i) ≃ᵐ α (Fin.last k) × ∀ j : Fin k, α j.castSucc where
  toEquiv := (Fin.snocEquiv α).symm
  measurable_toFun :=
    (measurable_pi_apply _).prodMk (measurable_pi_lambda _ fun j => measurable_pi_apply _)
  measurable_invFun := by
    refine measurable_pi_iff.2 fun i => ?_
    show Measurable fun p : α (Fin.last k) × (∀ j : Fin k, α j.castSucc) =>
      (Fin.snoc p.2 p.1 : ∀ i, α i) i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]; exact measurable_fst
    · simp only [Fin.snoc_castSucc]; exact (measurable_pi_apply j).comp measurable_snd

theorem snocME_symm_apply {k : ℕ} (α : Fin (k + 1) → Type u) [∀ i, MeasurableSpace (α i)]
    (p : α (Fin.last k) × ∀ j : Fin k, α j.castSucc) :
    (snocME α).symm p = Fin.snoc p.2 p.1 := rfl

theorem mp_snoc {k : ℕ} {α : Fin (k + 1) → Type u} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (snocME α) (Measure.pi μ)
      ((μ (Fin.last k)).prod (Measure.pi fun j : Fin k => μ j.castSucc)) := by
  set e := (snocME α).symm
  refine MeasurePreserving.symm e ?_
  refine ⟨e.measurable, (Measure.pi_eq fun s _ => ?_).symm⟩
  rw [e.map_apply, Fin.prod_univ_castSucc, mul_comm,
    ← Measure.pi_pi (fun j : Fin k => μ j.castSucc) (fun j => s j.castSucc),
    ← Measure.prod_prod]
  congr 1 with ⟨x, f⟩
  simp only [e, snocME_symm_apply, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_prod]
  constructor
  · intro h
    exact ⟨by simpa using h (Fin.last k), fun j => by simpa using h j.castSucc⟩
  · rintro ⟨h1, h2⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using h1
    · simpa using h2 j

theorem integral_snoc {k : ℕ} {α : Fin (k + 1) → Type u} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (g : (∀ i, α i) → ℝ) :
    ∫ ω, g ω ∂Measure.pi μ =
      ∫ p, g (Fin.snoc p.2 p.1) ∂((μ (Fin.last k)).prod (Measure.pi fun j : Fin k => μ j.castSucc)) := by
  have h := (mp_snoc μ).integral_comp' (fun p => g ((snocME α).symm p))
  simp only [MeasurableEquiv.symm_apply_apply] at h
  rw [h]
  simp only [snocME_symm_apply]

/-! ### Elementary measurability facts -/

theorem integrable_of_bdd {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB x)

theorem meas_eval {m : ℕ} {Z : Type*} [MeasurableSpace Z] :
    Measurable (fun q : (Fin m → Z) × Fin m => q.1 q.2) :=
  measurable_from_prod_countable_left fun i => measurable_pi_apply i

theorem meas_rem {k : ℕ} {Y : Type*} [MeasurableSpace Y] :
    Measurable (fun q : (Fin (k + 1) → Y) × Fin (k + 1) => SoarRemaining q.1 q.2) :=
  measurable_from_prod_countable_left fun i =>
    measurable_pi_lambda _ fun j => measurable_pi_apply (i.succAbove j)

theorem meas_cons {k : ℕ} {X : Type*} [MeasurableSpace X] :
    Measurable (fun a : X × (Fin k → X) => (Fin.cons a.1 a.2 : Fin (k + 1) → X)) := by
  refine measurable_pi_lambda _ fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]; exact measurable_fst
  · simp only [Fin.cons_succ]; exact (measurable_pi_apply j).comp measurable_snd

theorem meas_pool {k : ℕ} {X : Type*} [MeasurableSpace X] :
    Measurable (fun r : SoarEpochRand X k => SoarPool r) := by
  have h1 : Measurable (fun q : (Fin (k + 1) → X) × Equiv.Perm (Fin (k + 1)) =>
      fun j => q.1 (q.2 j)) :=
    measurable_from_prod_countable_left fun σ =>
      measurable_pi_lambda _ fun j => measurable_pi_apply (σ j)
  have h2 : Measurable (fun r : SoarEpochRand X k =>
      ((Fin.cons r.1 r.2.1 : Fin (k + 1) → X), r.2.2)) :=
    (meas_cons.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd)
  exact h1.comp h2

theorem meas_pick {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m))
    (hopt : SoarSolverMeasurable opt) (k : ℕ) :
    Measurable (fun p : (Fin (k + 1) → Y) × SoarEpochRand X k => SoarPick opt p.1 p.2) := by
  have h1 : Measurable (fun p : (Fin (k + 1) → Y) × SoarEpochRand X k =>
      (opt (k + 1) (SoarPool p.2) p.1, p.2.2.2)) :=
    ((hopt (k + 1)).comp ((meas_pool.comp measurable_snd).prodMk measurable_fst)).prodMk
      (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have h2 : Measurable (fun q : Equiv.Perm (Fin (k + 1)) × Equiv.Perm (Fin (k + 1)) =>
      q.1 (q.2.symm 0)) :=
    measurable_of_countable _
  exact h2.comp h1

theorem total_succ {X Y : Type*} (φ : X → Y → ℝ)
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m)) (k : ℕ)
    (ys : Fin (k + 1) → Y) (ω : (j : Fin (k + 1)) → SoarEpochRand X j) :
    SoarTotal φ opt (k + 1) ys ω =
      φ (ω (Fin.last k)).1 (ys (SoarPick opt ys (ω (Fin.last k)))) +
        SoarTotal φ opt k (SoarRemaining ys (SoarPick opt ys (ω (Fin.last k))))
          (fun j => ω j.castSucc) := rfl

theorem meas_total {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (φ : X → Y → ℝ) (hφ : Measurable (Function.uncurry φ))
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m))
    (hopt : SoarSolverMeasurable opt) :
    ∀ n : ℕ, Measurable (fun p : (Fin n → Y) × ((j : Fin n) → SoarEpochRand X j) =>
      SoarTotal φ opt n p.1 p.2)
  | 0 => by simp only [SoarTotal]; exact measurable_const
  | k + 1 => by
    have hl : Measurable (fun p : (Fin (k + 1) → Y) × ((j : Fin (k + 1)) → SoarEpochRand X j) =>
        (p.1, p.2 (Fin.last k))) :=
      measurable_fst.prodMk ((measurable_pi_apply (Fin.last k)).comp measurable_snd)
    have hpk := (meas_pick opt hopt k).comp hl
    have hω : Measurable (fun p : (Fin (k + 1) → Y) × ((j : Fin (k + 1)) → SoarEpochRand X j) =>
        (fun j : Fin k => p.2 j.castSucc : (j : Fin k) → SoarEpochRand X j)) :=
      measurable_pi_lambda _ fun j => (measurable_pi_apply j.castSucc).comp measurable_snd
    have hA : Measurable (fun p : (Fin (k + 1) → Y) × ((j : Fin (k + 1)) → SoarEpochRand X j) =>
        φ (p.2 (Fin.last k)).1 (p.1 (SoarPick opt p.1 (p.2 (Fin.last k))))) :=
      hφ.comp ((measurable_fst.comp ((measurable_pi_apply (Fin.last k)).comp measurable_snd)).prodMk
        (meas_eval.comp (measurable_fst.prodMk hpk)))
    have hB : Measurable (fun p : (Fin (k + 1) → Y) × ((j : Fin (k + 1)) → SoarEpochRand X j) =>
        SoarTotal φ opt k (SoarRemaining p.1 (SoarPick opt p.1 (p.2 (Fin.last k))))
          (fun j => p.2 j.castSucc)) :=
      (meas_total φ hφ opt hopt k).comp ((meas_rem.comp (measurable_fst.prodMk hpk)).prodMk hω)
    simp only [total_succ]
    exact hA.add hB

theorem bound_total {X Y : Type*} (φ : X → Y → ℝ) (C : ℝ) (hC : SoarBounded φ C)
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m)) :
    ∀ (n : ℕ) (ys : Fin n → Y) (ω : (j : Fin n) → SoarEpochRand X j),
      |SoarTotal φ opt n ys ω| ≤ n * C
  | 0, ys, ω => by simp [SoarTotal]
  | k + 1, ys, ω => by
    rw [total_succ]
    have h1 := hC (ω (Fin.last k)).1 (ys (SoarPick opt ys (ω (Fin.last k))))
    have h2 := bound_total φ C hC opt k (SoarRemaining ys (SoarPick opt ys (ω (Fin.last k))))
      (fun j => ω j.castSucc)
    refine (abs_add_le _ _).trans ?_
    push_cast
    linarith

/-! ### Counting permutations -/

theorem count_perm (k : ℕ) (f : Fin (k + 1) → ℝ) :
    ∑ σ : Equiv.Perm (Fin (k + 1)), f (σ.symm 0) = (k.factorial : ℝ) * ∑ t, f t := by
  have h1 : ∀ j : Fin (k + 1), ∑ σ : Equiv.Perm (Fin (k + 1)), f (σ.symm j) =
      ∑ σ : Equiv.Perm (Fin (k + 1)), f (σ.symm 0) := by
    intro j
    refine Fintype.sum_equiv (Equiv.mulLeft (Equiv.swap 0 j)) _ _ ?_
    intro σ
    simp [Equiv.Perm.mul_def, Equiv.swap_apply_left]
  have h2 : ((k : ℝ) + 1) * ∑ σ : Equiv.Perm (Fin (k + 1)), f (σ.symm 0) =
      ((k + 1).factorial : ℝ) * ∑ t, f t := by
    calc ((k : ℝ) + 1) * ∑ σ : Equiv.Perm (Fin (k + 1)), f (σ.symm 0)
        = ∑ j : Fin (k + 1), ∑ σ : Equiv.Perm (Fin (k + 1)), f (σ.symm j) := by
          simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
      _ = ∑ σ : Equiv.Perm (Fin (k + 1)), ∑ j, f (σ.symm j) := Finset.sum_comm
      _ = ∑ σ : Equiv.Perm (Fin (k + 1)), ∑ t, f t := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          exact Equiv.sum_comp σ.symm f
      _ = ((k + 1).factorial : ℝ) * ∑ t, f t := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ hk
  rw [h2, Nat.factorial_succ]
  push_cast; ring

theorem uniform_real (k : ℕ) (σ : Equiv.Perm (Fin (k + 1))) :
    (SoarUniform (Equiv.Perm (Fin (k + 1)))).real {σ} = 1 / ((k + 1).factorial : ℝ) := by
  unfold SoarUniform
  rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton σ),
    PMF.uniformOfFintype_apply]
  simp [Fintype.card_perm, Fintype.card_fin]

/-! ### The law of the pool (pool_law, in integral form) -/

theorem perm_integral {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (k : ℕ) (σ : Equiv.Perm (Fin (k + 1))) (g : (Fin (k + 1) → X) → ℝ) :
    ∫ v, g (fun j => v (σ j)) ∂Measure.pi (fun _ : Fin (k + 1) => P) =
      ∫ w, g w ∂Measure.pi (fun _ : Fin (k + 1) => P) := by
  have mp := measurePreserving_piCongrLeft (α := fun _ : Fin (k + 1) => X)
    (fun _ : Fin (k + 1) => P) σ.symm
  have hfun : ∀ v : Fin (k + 1) → X,
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (k + 1) => X) σ.symm) v = fun j => v (σ j) := by
    intro v; funext j
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rw [← mp.integral_comp' g]
  simp only [hfun]

theorem cons_integral {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (k : ℕ) (g : (Fin (k + 1) → X) → ℝ) :
    ∫ a, g (Fin.cons a.1 a.2) ∂(P.prod (Measure.pi fun _ : Fin k => P)) =
      ∫ w, g w ∂Measure.pi (fun _ : Fin (k + 1) => P) := by
  have mp := (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => P) 0).symm
  have hfun : ∀ a : X × (Fin k → X),
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => X) 0).symm a =
        (Fin.cons a.1 a.2 : Fin (k + 1) → X) := by
    intro a
    simp [MeasurableEquiv.piFinSuccAbove] <;> rfl
  rw [← mp.integral_comp' g]
  simp only [hfun]

theorem pool_integral {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (k : ℕ) (h : (Fin (k + 1) → X) → Fin (k + 1) → ℝ) (hm : ∀ t, Measurable fun w => h w t)
    (B : ℝ) (hB : ∀ w t, |h w t| ≤ B) :
    ∫ r, h (SoarPool r) (r.2.2.symm 0) ∂SoarEpochMeasure P k =
      (∑ t, ∫ w, h w t ∂Measure.pi (fun _ : Fin (k + 1) => P)) / (k + 1) := by
  have hH : Measurable (fun q : (Fin (k + 1) → X) × Fin (k + 1) => h q.1 q.2) :=
    measurable_from_prod_countable_left hm
  have hG : Measurable (fun r : SoarEpochRand X k => h (SoarPool r) (r.2.2.symm 0)) :=
    hH.comp (meas_pool.prodMk
      ((measurable_of_countable (fun σ : Equiv.Perm (Fin (k + 1)) => σ.symm 0)).comp
        (measurable_snd.comp measurable_snd)))
  unfold SoarEpochMeasure
  rw [← (measurePreserving_prodAssoc P (Measure.pi fun _ : Fin k => P)
    (SoarUniform (Equiv.Perm (Fin (k + 1))))).integral_comp'
    (fun r : SoarEpochRand X k => h (SoarPool r) (r.2.2.symm 0))]
  rw [integral_prod_symm (fun x => h (SoarPool (MeasurableEquiv.prodAssoc x))
      ((MeasurableEquiv.prodAssoc x).2.2.symm 0)) (integrable_of_bdd (hG.comp MeasurableEquiv.prodAssoc.measurable) B
    (fun q => hB _ _))]
  rw [integral_fintype Integrable.of_finite]
  simp only [uniform_real, smul_eq_mul]
  have hσ : ∀ σ : Equiv.Perm (Fin (k + 1)),
      ∫ a, h (SoarPool (MeasurableEquiv.prodAssoc (a, σ))) ((MeasurableEquiv.prodAssoc (a, σ)).2.2.symm 0)
        ∂(P.prod (Measure.pi fun _ : Fin k => P)) =
      ∫ w, h w (σ.symm 0) ∂Measure.pi (fun _ : Fin (k + 1) => P) := by
    intro σ
    have := cons_integral P k (fun v => h (fun j => v (σ j)) (σ.symm 0))
    rw [perm_integral P k σ (fun w => h w (σ.symm 0))] at this
    rw [← this]
    rfl
  simp only [hσ]
  rw [← Finset.mul_sum, count_perm k (fun t => ∫ w, h w t ∂Measure.pi (fun _ : Fin (k + 1) => P)),
    Nat.factorial_succ]
  push_cast
  field_simp

/-! ### The remaining supply (remaining_law, in integral form) -/

theorem rem_integral {Y : Type*} [MeasurableSpace Y] (Q : Measure Y) [IsProbabilityMeasure Q]
    (k : ℕ) (i : Fin (k + 1)) (g : (Fin k → Y) → ℝ) :
    ∫ ys, g (SoarRemaining ys i) ∂Measure.pi (fun _ : Fin (k + 1) => Q) =
      ∫ z, g z ∂Measure.pi (fun _ : Fin k => Q) := by
  have mp := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => Q) i
  calc ∫ ys, g (SoarRemaining ys i) ∂Measure.pi (fun _ : Fin (k + 1) => Q)
      = ∫ ys, (fun p : Y × (Fin k → Y) => g p.2)
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => Y) i ys)
          ∂Measure.pi (fun _ : Fin (k + 1) => Q) := rfl
    _ = ∫ p, g p.2 ∂(Q.prod (Measure.pi fun _ : Fin k => Q)) :=
        mp.integral_comp' (fun p : Y × (Fin k → Y) => g p.2)
    _ = ∫ z, g z ∂Measure.pi (fun _ : Fin k => Q) := by
      rw [integral_fun_snd]; simp

/-! ### The induction -/

noncomputable def Fk {X Y : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (φ : X → Y → ℝ) (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m))
    (k : ℕ) (ys : Fin k → Y) : ℝ :=
  ∫ ω, SoarTotal φ opt k ys ω ∂Measure.pi (fun j : Fin k => SoarEpochMeasure P j)

theorem meas_Fk {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) [IsProbabilityMeasure P]
    (φ : X → Y → ℝ) (hφ : Measurable (Function.uncurry φ))
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m))
    (hopt : SoarSolverMeasurable opt) (k : ℕ) : Measurable (Fk P φ opt k) :=
  ((meas_total φ hφ opt hopt k).stronglyMeasurable.integral_prod_right'
    (ν := Measure.pi (fun j : Fin k => SoarEpochMeasure P j))).measurable

theorem bound_Fk {X Y : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (φ : X → Y → ℝ) (C : ℝ) (hC : SoarBounded φ C)
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m)) (k : ℕ) (ys : Fin k → Y) :
    |Fk P φ opt k ys| ≤ k * C := by
  have := norm_integral_le_of_norm_le_const
    (μ := Measure.pi (fun j : Fin k => SoarEpochMeasure P j))
    (f := fun ω => SoarTotal φ opt k ys ω)
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact bound_total φ C hC opt k ys ω)
  simpa [Fk, Real.norm_eq_abs] using this

theorem I_as_F {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : X → Y → ℝ) (hφ : Measurable (Function.uncurry φ)) (C : ℝ) (hC : SoarBounded φ C)
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m))
    (hopt : SoarSolverMeasurable opt) (k : ℕ) :
    ∫ p, SoarTotal φ opt k p.1 p.2 ∂SoarMeasure P Q k =
      ∫ ys, Fk P φ opt k ys ∂Measure.pi (fun _ : Fin k => Q) := by
  unfold SoarMeasure
  rw [integral_prod _ (integrable_of_bdd (meas_total φ hφ opt hopt k) (k * C)
    (fun p => bound_total φ C hC opt k p.1 p.2))]
  rfl

/-- The hindsight sum is attained by the solver. -/
noncomputable def HS' {X Y : Type*} (φ : X → Y → ℝ)
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m)) {m : ℕ}
    (w : Fin m → X) (ys : Fin m → Y) : ℝ :=
  ∑ t, φ (w t) (ys (opt m w ys t))

theorem HS_eq {X Y : Type*} (φ : X → Y → ℝ)
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m))
    (hsolver : SoarIsSolver φ opt) {m : ℕ} (w : Fin m → X) (ys : Fin m → Y) :
    SoarHindsightSum φ w ys = HS' φ opt w ys := by
  unfold SoarHindsightSum HS'
  exact le_antisymm (ciSup_le fun η => hsolver m w ys η)
    (le_ciSup (f := fun σ : Equiv.Perm (Fin m) => ∑ t, φ (w t) (ys (σ t)))
      (Set.finite_range _).bddAbove (opt m w ys))

theorem meas_HS' {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (φ : X → Y → ℝ) (hφ : Measurable (Function.uncurry φ))
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m))
    (hopt : SoarSolverMeasurable opt) (m : ℕ) :
    Measurable (fun p : (Fin m → X) × (Fin m → Y) => HS' φ opt p.1 p.2) := by
  unfold HS'
  refine Finset.measurable_sum _ fun t _ => ?_
  exact hφ.comp (((measurable_pi_apply t).comp measurable_fst).prodMk
    (meas_eval.comp (measurable_snd.prodMk
      ((measurable_of_countable (fun σ : Equiv.Perm (Fin m) => σ t)).comp (hopt m)))))

theorem bound_HS' {X Y : Type*} (φ : X → Y → ℝ) (C : ℝ) (hC : SoarBounded φ C)
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m)) {m : ℕ}
    (w : Fin m → X) (ys : Fin m → Y) : |HS' φ opt w ys| ≤ m * C := by
  unfold HS'
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ t, |φ (w t) (ys (opt m w ys t))| ≤ ∑ _t : Fin m, C :=
        Finset.sum_le_sum fun t _ => hC _ _
    _ = m * C := by simp

theorem F_succ {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) [IsProbabilityMeasure P]
    (φ : X → Y → ℝ) (hφ : Measurable (Function.uncurry φ)) (C : ℝ) (hC : SoarBounded φ C)
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m))
    (hsolver : SoarIsSolver φ opt) (hopt : SoarSolverMeasurable opt) (k : ℕ)
    (ys : Fin (k + 1) → Y) :
    Fk P φ opt (k + 1) ys =
      (∫ w, HS' φ opt w ys ∂Measure.pi (fun _ : Fin (k + 1) => P) +
        ∑ i, Fk P φ opt k (SoarRemaining ys i)) / (k + 1) := by
  -- step 1: split off the last epoch
  have hT := meas_total φ hφ opt hopt (k + 1)
  have hsec : Measurable (fun p : SoarEpochRand X k × ((j : Fin k) → SoarEpochRand X j) =>
      SoarTotal φ opt (k + 1) ys (Fin.snoc p.2 p.1)) :=
    hT.comp (measurable_const.prodMk
      (snocME (fun j : Fin (k + 1) => SoarEpochRand X j)).symm.measurable)
  have step1 : Fk P φ opt (k + 1) ys =
      ∫ r, (φ r.1 (ys (SoarPick opt ys r)) + Fk P φ opt k (SoarRemaining ys (SoarPick opt ys r)))
        ∂SoarEpochMeasure P k := by
    unfold Fk
    rw [integral_snoc (fun j : Fin (k + 1) => SoarEpochMeasure P j)]
    refine (integral_prod _ (integrable_of_bdd hsec ((k + 1 : ℕ) * C)
      (fun p => bound_total φ C hC opt (k + 1) ys _))).trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    simp only [total_succ, Fin.snoc_last, Fin.snoc_castSucc]
    have hsec2 : Measurable (fun ω' : (j : Fin k) → SoarEpochRand X j =>
        SoarTotal φ opt k (SoarRemaining ys (SoarPick opt ys r)) ω') :=
      (meas_total φ hφ opt hopt k).comp (measurable_const.prodMk measurable_id)
    rw [integral_add (integrable_const _)
      (integrable_of_bdd hsec2 (k * C) (fun ω' => bound_total φ C hC opt k _ ω'))]
    simp <;> rfl
  -- step 2: rewrite in terms of the pool
  set Ψ : (Fin (k + 1) → X) → Fin (k + 1) → ℝ := fun w t =>
    φ (w t) (ys (opt (k + 1) w ys t)) + Fk P φ opt k (SoarRemaining ys (opt (k + 1) w ys t))
    with hΨ
  have step2 : ∀ r : SoarEpochRand X k,
      φ r.1 (ys (SoarPick opt ys r)) + Fk P φ opt k (SoarRemaining ys (SoarPick opt ys r)) =
        Ψ (SoarPool r) (r.2.2.symm 0) := by
    intro r
    have hp : SoarPool r (r.2.2.symm 0) = r.1 := by simp [SoarPool]
    simp only [hΨ, SoarPick, hp]
  have hΨm : ∀ t, Measurable fun w => Ψ w t := by
    intro t
    have hπ : Measurable fun w : Fin (k + 1) → X => opt (k + 1) w ys t :=
      (measurable_of_countable (fun σ : Equiv.Perm (Fin (k + 1)) => σ t)).comp
        ((hopt (k + 1)).comp (measurable_id.prodMk measurable_const))
    exact (hφ.comp ((measurable_pi_apply t).prodMk
      ((measurable_of_countable ys).comp hπ))).add
      ((measurable_of_countable (fun i => Fk P φ opt k (SoarRemaining ys i))).comp hπ)
  have hΨB : ∀ w t, |Ψ w t| ≤ C + k * C := by
    intro w t
    refine (abs_add_le _ _).trans ?_
    have := hC (w t) (ys (opt (k + 1) w ys t))
    have := bound_Fk P φ C hC opt k (SoarRemaining ys (opt (k + 1) w ys t))
    linarith
  rw [step1]
  simp only [step2]
  rw [pool_integral P k Ψ hΨm (C + k * C) hΨB]
  congr 1
  rw [← integral_finsetSum _ (fun t _ => integrable_of_bdd (hΨm t) _ (fun w => hΨB w t))]
  have hpt : ∀ w, ∑ t, Ψ w t = HS' φ opt w ys + ∑ i, Fk P φ opt k (SoarRemaining ys i) := by
    intro w
    simp only [hΨ, Finset.sum_add_distrib, HS']
    congr 1
    exact Equiv.sum_comp (opt (k + 1) w ys) (fun i => Fk P φ opt k (SoarRemaining ys i))
  simp only [hpt]
  have hHm : Measurable fun w : Fin (k + 1) → X => HS' φ opt w ys :=
    (meas_HS' φ hφ opt hopt (k + 1)).comp (measurable_id.prodMk measurable_const)
  rw [integral_add (integrable_of_bdd hHm _ (fun w => bound_HS' φ C hC opt w ys))
    (integrable_const _)]
  simp

theorem I_succ {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : X → Y → ℝ) (hφ : Measurable (Function.uncurry φ)) (C : ℝ) (hC : SoarBounded φ C)
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m))
    (hsolver : SoarIsSolver φ opt) (hopt : SoarSolverMeasurable opt) (k : ℕ) :
    ∫ p, SoarTotal φ opt (k + 1) p.1 p.2 ∂SoarMeasure P Q (k + 1) =
      SoarHindsight P Q φ (k + 1) + ∫ p, SoarTotal φ opt k p.1 p.2 ∂SoarMeasure P Q k := by
  rw [I_as_F P Q φ hφ C hC opt hopt (k + 1), I_as_F P Q φ hφ C hC opt hopt k]
  simp only [F_succ P φ hφ C hC opt hsolver hopt k]
  have hHm := meas_HS' φ hφ opt hopt (k + 1)
  have hint1 : Integrable (fun ys : Fin (k + 1) → Y =>
      ∫ w, HS' φ opt w ys ∂Measure.pi (fun _ : Fin (k + 1) => P))
      (Measure.pi fun _ : Fin (k + 1) => Q) := by
    refine integrable_of_bdd ?_ ((k + 1 : ℕ) * C) (fun ys => ?_)
    · exact (hHm.stronglyMeasurable.integral_prod_left'
        (μ := Measure.pi (fun _ : Fin (k + 1) => P))).measurable
    · have := norm_integral_le_of_norm_le_const
        (μ := Measure.pi (fun _ : Fin (k + 1) => P))
        (f := fun w => HS' φ opt w ys)
        (Filter.Eventually.of_forall fun w => by
          rw [Real.norm_eq_abs]; exact bound_HS' φ C hC opt w ys)
      simpa [Real.norm_eq_abs] using this
  have hint2 : ∀ i : Fin (k + 1), Integrable (fun ys : Fin (k + 1) → Y =>
      Fk P φ opt k (SoarRemaining ys i)) (Measure.pi fun _ : Fin (k + 1) => Q) := by
    intro i
    refine integrable_of_bdd ((meas_Fk P φ hφ opt hopt k).comp
      (meas_rem.comp (measurable_id.prodMk measurable_const))) (k * C) (fun ys => ?_)
    exact bound_Fk P φ C hC opt k _
  rw [integral_div, integral_add hint1 (integrable_finsetSum _ fun i _ => hint2 i),
    integral_finsetSum _ fun i _ => hint2 i]
  simp only [rem_integral Q k _ (Fk P φ opt k)]
  have hHS : ∫ ys, ∫ w, HS' φ opt w ys ∂Measure.pi (fun _ : Fin (k + 1) => P)
      ∂Measure.pi (fun _ : Fin (k + 1) => Q) = ((k : ℝ) + 1) * SoarHindsight P Q φ (k + 1) := by
    rw [← integral_prod_symm (fun p : (Fin (k + 1) → X) × (Fin (k + 1) → Y) => HS' φ opt p.1 p.2)
      (integrable_of_bdd hHm _ (fun p => bound_HS' φ C hC opt p.1 p.2))]
    unfold SoarHindsight SoarPairMeasure
    simp only [HS_eq φ opt hsolver]
    push_cast
    field_simp
  rw [hHS]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

theorem I_eq {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : X → Y → ℝ) (hφ : Measurable (Function.uncurry φ)) (C : ℝ) (hC : SoarBounded φ C)
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m))
    (hsolver : SoarIsSolver φ opt) (hopt : SoarSolverMeasurable opt) (n : ℕ) :
    ∫ p, SoarTotal φ opt n p.1 p.2 ∂SoarMeasure P Q n =
      ∑ k ∈ Finset.Icc 1 n, SoarHindsight P Q φ k := by
  induction n with
  | zero => simp [SoarTotal]
  | succ k ih =>
    rw [I_succ P Q φ hφ C hC opt hsolver hopt k, ih, Finset.sum_Icc_succ_top (by omega)]
    ring

end SoarAux

open MeasureTheory in
theorem solution {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : X → Y → ℝ) (hφ : Measurable (Function.uncurry φ)) (C : ℝ) (hC : SoarBounded φ C)
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m))
    (hsolver : SoarIsSolver φ opt) (hopt : SoarSolverMeasurable opt) (n : ℕ) :
    SoarValue P Q φ opt n = (∑ k ∈ Finset.Icc 1 n, SoarHindsight P Q φ k) / n := by
  unfold SoarValue
  rw [SoarAux.I_eq P Q φ hφ C hC opt hsolver hopt n]
