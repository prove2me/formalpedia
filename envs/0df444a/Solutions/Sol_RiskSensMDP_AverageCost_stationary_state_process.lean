-- Prove2me | solution 1 for RiskSensMDP.AverageCost.stationary_state_process
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T02:20:51.682003+00:00
-- url     : https://prove2.me/submissions/b08fb57a-4aac-4f50-8b8a-dbb69cb99622

import Mathlib
import Definitions.Def_RiskSensMDP_AverageCost_Model
import Definitions.Def_RiskSensMDP_AverageCost_HarrisRecurrence

open MeasureTheory ProbabilityTheory Filter Finset

namespace Aux_RSMDP5_ssp

open RiskSensMDP.AverageCost

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

lemma stepKernel_compl (M : Model E A) (σ : Policy M) (t : ℕ) (h : Π _ : Iic t, E × A)
    (S : Set (E × A)) (hS : MeasurableSet S) (hσ : ∀ hb : (Fin (t + 1) → E × A) × E,
      (hb.2, σ.g (t + 1) hb) ∈ S) :
    stepKernel M σ t h Sᶜ = 0 := by
  have : IsMarkovKernel (M.Q.comap (lastPair (E := E) (A := A) t) (measurable_pi_apply _)) :=
    Kernel.IsMarkovKernel.comap _ _
  unfold stepKernel
  rw [Kernel.compProd_apply hS.compl]
  refine (lintegral_eq_zero_iff ?_).2 ?_
  · exact Kernel.measurable_kernel_prodMk_left' (hS.compl) h |>.comp measurable_id
  · refine Filter.Eventually.of_forall (fun b => ?_)
    simp only [Pi.zero_apply]
    rw [Kernel.deterministic_apply' _ _ (measurable_prodMk_left hS.compl)]
    rw [Set.indicator_apply_eq_zero]
    intro hc
    exact absurd (hσ (histFin t h, b)) hc

lemma pathMeasure_map_frestrictLe_zero (M : Model E A) (σ : Policy M) (x : E) :
    (pathMeasure M σ x).map (Preorder.frestrictLe (π := fun _ : ℕ => E × A) 0) =
      Measure.dirac ((MeasurableEquiv.piUnique (fun _ : Iic 0 => E × A)).symm
        (x, σ.g 0 (fun j => j.elim0, x))) := by
  have hm : Measurable (Preorder.frestrictLe (π := fun _ : ℕ => E × A) 0) := by fun_prop
  unfold pathMeasure Kernel.trajMeasure
  rw [Measure.map_comp _ _ hm, Kernel.traj_map_frestrictLe, Kernel.partialTraj_self,
    Measure.id_comp, Measure.map_dirac' (by fun_prop)]

lemma ae_mem (M : Model E A) (σ : Policy M) (x : E) (S : Set (E × A)) (hS : MeasurableSet S)
    (h0 : (x, σ.g 0 (fun j => j.elim0, x)) ∈ S)
    (hσ : ∀ t, ∀ hb : (Fin (t + 1) → E × A) × E, (hb.2, σ.g (t + 1) hb) ∈ S) (k : ℕ) :
    ∀ᵐ ω ∂(pathMeasure M σ x), ω k ∈ S := by
  rw [ae_iff]
  cases k with
  | zero =>
    have hm : Measurable (Preorder.frestrictLe (π := fun _ : ℕ => E × A) 0) := by fun_prop
    have hS' : MeasurableSet {y : Π _ : Iic 0, E × A | y ⟨0, by simp⟩ ∉ S} :=
      (hS.preimage (measurable_pi_apply _)).compl
    have : {ω : ℕ → E × A | ¬ ω 0 ∈ S} =
        Preorder.frestrictLe 0 ⁻¹' {y : Π _ : Iic 0, E × A | y ⟨0, by simp⟩ ∉ S} := rfl
    rw [this, ← Measure.map_apply hm hS', pathMeasure_map_frestrictLe_zero,
      Measure.dirac_apply' _ hS']
    simp only [Set.indicator_apply_eq_zero, Pi.one_apply, one_ne_zero, imp_false]
    intro hc
    exact hc h0
  | succ a =>
    have hm : Measurable (fun ω : ℕ → E × A => (Preorder.frestrictLe a ω, ω (a + 1))) := by
      fun_prop
    have hS' : MeasurableSet ((Set.univ : Set (Π _ : Iic a, E × A)) ×ˢ Sᶜ) :=
      MeasurableSet.univ.prod hS.compl
    have : {ω : ℕ → E × A | ¬ ω (a + 1) ∈ S} =
        (fun ω : ℕ → E × A => (Preorder.frestrictLe a ω, ω (a + 1))) ⁻¹'
          ((Set.univ : Set (Π _ : Iic a, E × A)) ×ˢ Sᶜ) := by
      ext ω; simp
    rw [this, ← Measure.map_apply hm hS']
    unfold pathMeasure
    rw [← Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure,
      Measure.compProd_apply_prod MeasurableSet.univ hS.compl]
    simp [stepKernel_compl M σ a _ S hS (hσ a)]

lemma ae_action [StandardBorelSpace A] (M : Model E A) (f : StationaryRule M) (x : E) :
    ∀ᵐ ω ∂(pathMeasure M f.toPolicy x), ∀ n : ℕ, (ω n).2 = f.f (ω n).1 := by
  rw [ae_all_iff]
  intro n
  have hS : MeasurableSet {p : E × A | p.2 = f.f p.1} :=
    measurableSet_eq_fun measurable_snd (f.f_meas.comp measurable_fst)
  exact ae_mem M f.toPolicy x _ hS rfl (fun _ _ => rfl) n


/-- append a new last coordinate to a history indexed by `Iic n`. -/
def app {β : Type*} (n : ℕ) (p : (Iic n → β) × β) : Iic (n + 1) → β :=
  fun i => if hi : i.1 ≤ n then p.1 ⟨i.1, Finset.mem_Iic.2 hi⟩ else p.2

lemma measurable_app {β : Type*} [MeasurableSpace β] (n : ℕ) :
    Measurable (app (β := β) n) := by
  refine measurable_pi_lambda _ (fun i => ?_)
  by_cases hi : i.1 ≤ n
  · simp only [app, hi, dif_pos]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [app, hi, dif_neg, not_false_eq_true]
    exact measurable_snd

lemma frestrictLe_succ {β : Type*} (n : ℕ) (ω : ℕ → β) :
    Preorder.frestrictLe (π := fun _ => β) (n + 1) ω =
      app n (Preorder.frestrictLe (π := fun _ => β) n ω, ω (n + 1)) := by
  funext i
  obtain ⟨i, hi⟩ := i
  have hi' := Finset.mem_Iic.1 hi
  by_cases h : i ≤ n
  · simp [app, h, Preorder.frestrictLe]
  · have : i = n + 1 := by omega
    subst this
    simp [app, Preorder.frestrictLe]

lemma traj_law_succ {β : Type*} [MeasurableSpace β] (μ₀ : Measure β) [IsProbabilityMeasure μ₀]
    (κ : (n : ℕ) → Kernel (Π _ : Iic n, β) β) [∀ n, IsMarkovKernel (κ n)] (n : ℕ) :
    (Kernel.trajMeasure (X := fun _ => β) μ₀ κ).map (Preorder.frestrictLe (n + 1)) =
      ((Kernel.trajMeasure (X := fun _ => β) μ₀ κ).map (Preorder.frestrictLe n) ⊗ₘ κ n).map
        (app n) := by
  rw [Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure,
    Measure.map_map (measurable_app n) (by fun_prop)]
  congr 1
  funext ω
  exact frestrictLe_succ n ω

/-- pushing a composition-product forward along `g × fst`. -/
lemma compProd_map_prodMap {H H' Y Z : Type*} [MeasurableSpace H] [MeasurableSpace H']
    [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure H) [IsFiniteMeasure μ] (κ : Kernel H (Y × Z)) [IsMarkovKernel κ]
    (η : Kernel H' Y) [IsMarkovKernel η] (g : H → H') (hg : Measurable g)
    (hκ : ∀ᵐ h ∂μ, (κ h).map Prod.fst = η (g h)) :
    (μ ⊗ₘ κ).map (fun p => (g p.1, p.2.1)) = (μ.map g) ⊗ₘ η := by
  have hG : Measurable (fun p : H × (Y × Z) => (g p.1, p.2.1)) := by fun_prop
  ext s hs
  rw [Measure.map_apply hG hs, Measure.compProd_apply (hG hs), Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hg]
  refine lintegral_congr_ae ?_
  filter_upwards [hκ] with h hh
  have hm : MeasurableSet (Prod.mk (g h) ⁻¹' s) := measurable_prodMk_left hs
  rw [← hh, Measure.map_apply measurable_fst hm]
  rfl


/-- forget the actions of a history. -/
def proj (n : ℕ) (h : Iic n → E × A) : Iic n → E := fun i => (h i).1

lemma measurable_proj (n : ℕ) : Measurable (proj (E := E) (A := A) n) :=
  measurable_pi_lambda _ (fun i => measurable_fst.comp (measurable_pi_apply i))

lemma proj_app (n : ℕ) (q : (Iic n → E × A) × (E × A)) :
    proj (n + 1) (app n q) = app n (proj n q.1, q.2.1) := by
  funext i
  by_cases hi : i.1 ≤ n
  · simp [proj, app, hi]
  · simp [proj, app, hi]

lemma marginals [StandardBorelSpace A] (M : Model E A) (f : StationaryRule M) (x : E) (n : ℕ) :
    ((pathMeasure M f.toPolicy x).map (Preorder.frestrictLe n)).map (proj n) =
      (chainLaw (stateKernel M f) x).map (Preorder.frestrictLe (π := fun _ => E) n) := by
  induction n with
  | zero =>
    rw [pathMeasure_map_frestrictLe_zero, Measure.map_dirac' (measurable_proj 0)]
    have hm : Measurable (Preorder.frestrictLe (π := fun _ : ℕ => E) 0) := by fun_prop
    unfold chainLaw Kernel.trajMeasure
    rw [Measure.map_comp _ _ hm, Kernel.traj_map_frestrictLe, Kernel.partialTraj_self,
      Measure.id_comp, Measure.map_dirac' (by fun_prop)]
    congr 1
  | succ n ih =>
    have hL := traj_law_succ (β := E × A) (Measure.dirac (x, f.toPolicy.g 0 (fun j => j.elim0, x)))
      (stepKernel M f.toPolicy) n
    have hC := traj_law_succ (β := E) (Measure.dirac x) (chainStep (stateKernel M f)) n
    unfold pathMeasure chainLaw at *
    rw [hL, hC, ← ih, Measure.map_map (measurable_proj _) (measurable_app n)]
    have hcomp : proj (E := E) (A := A) (n + 1) ∘ app n =
        app n ∘ (fun p : (Iic n → E × A) × (E × A) => (proj n p.1, p.2.1)) := by
      funext q; exact proj_app n q
    have hG : Measurable (fun p : (Iic n → E × A) × (E × A) => (proj n p.1, p.2.1)) :=
      ((measurable_proj n).comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)
    rw [hcomp, ← Measure.map_map (measurable_app n) hG]
    congr 1
    refine compProd_map_prodMap _ _ _ _ (measurable_proj n) ?_
    -- the a.e. identification of the one-step kernels
    have hS : MeasurableSet {h : Iic n → E × A |
        (h ⟨n, Finset.mem_Iic.2 le_rfl⟩).2 = f.f (h ⟨n, Finset.mem_Iic.2 le_rfl⟩).1} :=
      measurableSet_eq_fun (measurable_snd.comp (measurable_pi_apply _))
        (f.f_meas.comp (measurable_fst.comp (measurable_pi_apply _)))
    have hae : ∀ᵐ h ∂((Kernel.trajMeasure (X := fun _ => E × A)
        (Measure.dirac (x, f.toPolicy.g 0 (fun j => j.elim0, x))) (stepKernel M f.toPolicy)).map
          (Preorder.frestrictLe n)),
        (h ⟨n, Finset.mem_Iic.2 le_rfl⟩).2 = f.f (h ⟨n, Finset.mem_Iic.2 le_rfl⟩).1 := by
      rw [ae_map_iff (by fun_prop) hS]
      have := ae_action M f x
      unfold pathMeasure at this
      filter_upwards [this] with ω hω
      exact hω n
    filter_upwards [hae] with h hh
    have : IsMarkovKernel (M.Q.comap (lastPair (E := E) (A := A) n) (measurable_pi_apply _)) :=
      Kernel.IsMarkovKernel.comap _ _
    rw [← Kernel.fst_apply]
    unfold stepKernel
    rw [Kernel.fst_compProd]
    simp only [Kernel.comap_apply, chainStep, stateKernel, proj]
    rw [← hh]
    rfl

end Aux_RSMDP5_ssp

open RiskSensMDP.AverageCost in
theorem solution {E A : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    [MeasurableSpace A] [StandardBorelSpace A]
    (M : Model E A) (f : StationaryRule M) (x : E) :
    (∀ᵐ ω ∂(pathMeasure M f.toPolicy x), ∀ n : ℕ, (ω n).2 = f.f (ω n).1) ∧
    (pathMeasure M f.toPolicy x).map (fun ω n => (ω n).1) = chainLaw (stateKernel M f) x := by
  refine ⟨Aux_RSMDP5_ssp.ae_action M f x, ?_⟩
  set ν' := chainLaw (stateKernel M f) x
  have : IsProbabilityMeasure ν' := by unfold ν' chainLaw; infer_instance
  have hπ : Measurable (fun ω : ℕ → E × A => fun n => (ω n).1) :=
    measurable_pi_lambda _ (fun n => measurable_fst.comp (measurable_pi_apply n))
  have hP : IsProjectiveMeasureFamily (fun I : Finset ℕ => ν'.map I.restrict) :=
    isProjectiveMeasureFamily_map_restrict (X := fun t (ω : ℕ → E) => ω t) (P := ν')
      (fun t => (measurable_pi_apply t).aemeasurable)
  have h1 : IsProjectiveLimit ν' (fun I : Finset ℕ => ν'.map I.restrict) := fun I => rfl
  have h2 : IsProjectiveLimit ((pathMeasure M f.toPolicy x).map (fun ω n => (ω n).1))
      (fun I : Finset ℕ => ν'.map I.restrict) := by
    rw [isProjectiveLimit_nat_iff hP]
    intro n
    rw [Measure.map_map (by fun_prop) hπ]
    have := Aux_RSMDP5_ssp.marginals M f x n
    rw [Measure.map_map (Aux_RSMDP5_ssp.measurable_proj n) (by fun_prop)] at this
    exact this
  exact h2.unique h1
