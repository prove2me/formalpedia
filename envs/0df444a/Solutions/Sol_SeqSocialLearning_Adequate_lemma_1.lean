-- Prove2me | solution 1 for SeqSocialLearning.Adequate.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T10:24:18.143707+00:00
-- url     : https://prove2.me/submissions/e66d6514-f2ba-4b8f-91c1-8c887251d45d

import Mathlib
import Definitions.Def_SeqSocialLearning_Adequate_Model
import Definitions.Def_SeqSocialLearning_Adequate_Signals
import Definitions.Def_SeqSocialLearning_Adequate_Beliefs

open MeasureTheory ProbabilityTheory Filter Topology

namespace SSLLem1Aux
set_option linter.unusedSectionVars false
open SeqSocialLearning.Adequate

variable {Ω A S : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace S]

/-- The kernel giving the (signal, action) of agent `t` from (state, history). -/
noncomputable def eta (F : Kernel Ω S) [IsMarkovKernel F] (p : Profile A S) (t : ℕ) :
    Kernel (Ω × (Fin t → A)) (S × A) :=
  (F.comap (Prod.fst : Ω × (Fin t → A) → Ω) measurable_fst) ⊗ₖ
      ((p.σ t).comap (fun q : (Ω × (Fin t → A)) × S => (q.1.2, q.2))
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

instance (F : Kernel Ω S) [IsMarkovKernel F] (p : Profile A S) (t : ℕ) :
    IsMarkovKernel (eta F p t) := by
  unfold eta; infer_instance

lemma law0 (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (p : Profile A S) :
    (playMeasure μ F p).map (fun x => x 0) = initMeasure μ F p := by
  set e := MeasurableEquiv.piUnique (fun i : Finset.Iic 0 => (fun _ : ℕ => Ω × S × A) i)
  have h1 : (fun x : ℕ → Ω × S × A => x 0) = e ∘ Preorder.frestrictLe 0 := by
    funext x
    rfl
  rw [h1, ← Measure.map_map e.measurable (Preorder.measurable_frestrictLe 0)]
  unfold playMeasure Kernel.trajMeasure
  rw [Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp, Measure.map_map e.measurable e.symm.measurable]
  simp

lemma measurable_state : Measurable (state (Ω := Ω) (S := S) (A := A)) := by
  unfold state; fun_prop

lemma measurable_action (t : ℕ) : Measurable (fun x : ℕ → Ω × S × A => action x t) := by
  unfold action; fun_prop

lemma measurable_signal (t : ℕ) : Measurable (fun x : ℕ → Ω × S × A => signal x t) := by
  unfold signal; fun_prop

lemma measurable_history (t : ℕ) : Measurable (fun x : ℕ → Ω × S × A => history x t) := by
  unfold history action; fun_prop

lemma lawSucc (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (p : Profile A S) (n : ℕ) :
    (playMeasure μ F p).map
      (fun x => ((state x, history x (n + 1)), (signal x (n + 1), action x (n + 1)))) =
    ((playMeasure μ F p).map (fun x => (state x, history x (n + 1)))) ⊗ₘ eta F p (n + 1) := by
  have hstep := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ => Ω × S × A) (μ₀ := initMeasure μ F p) (κ := stepKernel F p) (a := n)
  set P := playMeasure μ F p
  set ν := P.map (Preorder.frestrictLe n)
  let Φ : ((i : Finset.Iic n) → Ω × S × A) × (Ω × S × A) →
      (Ω × (Fin (n + 1) → A)) × (S × A) := fun yz => (stateHist n yz.1, yz.2.2)
  have hΦ : Measurable Φ := by
    exact ((measurable_stateHist n).comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)
  have h1 : (fun x : ℕ → Ω × S × A =>
      ((state x, history x (n + 1)), (signal x (n + 1), action x (n + 1)))) =
      Φ ∘ (fun x => (Preorder.frestrictLe n x, x (n + 1))) := by
    funext x; rfl
  have h2 : (fun x : ℕ → Ω × S × A => (state x, history x (n + 1))) =
      stateHist n ∘ Preorder.frestrictLe n := by
    funext x; rfl
  rw [h1, h2, ← Measure.map_map hΦ (by fun_prop),
    ← Measure.map_map (measurable_stateHist n) (Preorder.measurable_frestrictLe n)]
  change Measure.map Φ (Measure.map _ (Kernel.trajMeasure _ _)) = _
  rw [← hstep]
  ext s hs
  rw [Measure.map_apply hΦ hs, Measure.compProd_apply (hΦ hs), Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) (measurable_stateHist n)]
  refine lintegral_congr fun y => ?_
  have : Prod.mk y ⁻¹' (Φ ⁻¹' s) =
      Set.univ ×ˢ (Prod.mk (stateHist n y) ⁻¹' s) := by
    ext z; simp [Φ]
  rw [this]
  unfold stepKernel
  rw [Kernel.comap_apply, Kernel.prod_apply, Measure.prod_prod]
  simp [eta]

lemma history_zero (x : ℕ → Ω × S × A) : history x 0 = (Fin.elim0 : Fin 0 → A) := by
  funext i; exact i.elim0

lemma init_fst (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (p : Profile A S) : (initMeasure μ F p).map Prod.fst = μ := by
  unfold initMeasure
  exact Measure.fst_compProd _ _

lemma eta_zero (F : Kernel Ω S) [IsMarkovKernel F] (p : Profile A S) (ω : Ω) :
    eta F p 0 (ω, (Fin.elim0 : Fin 0 → A)) =
      (F ⊗ₖ ((p.σ 0).comap (fun q : Ω × S => ((Fin.elim0 : Fin 0 → A), q.2))
        (measurable_const.prodMk measurable_snd))) ω := by
  ext t ht
  rw [eta, Kernel.compProd_apply ht, Kernel.compProd_apply ht]
  simp only [Kernel.comap_apply]

lemma lawZero (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (p : Profile A S) :
    (playMeasure μ F p).map
      (fun x => ((state x, history x 0), (signal x 0, action x 0))) =
    ((playMeasure μ F p).map (fun x => (state x, history x 0))) ⊗ₘ eta F p 0 := by
  let Ψ : Ω × S × A → (Ω × (Fin 0 → A)) × (S × A) :=
    fun y => ((y.1, (Fin.elim0 : Fin 0 → A)), y.2)
  have hΨ : Measurable Ψ := by fun_prop
  let g : Ω → Ω × (Fin 0 → A) := fun ω => (ω, (Fin.elim0 : Fin 0 → A))
  have hg : Measurable g := by fun_prop
  have h1 : (fun x : ℕ → Ω × S × A => ((state x, history x 0), (signal x 0, action x 0))) =
      Ψ ∘ (fun x => x 0) := by
    funext x; simp only [history_zero]; rfl
  have h2 : (fun x : ℕ → Ω × S × A => (state x, history x 0)) =
      (g ∘ Prod.fst) ∘ (fun x => x 0) := by
    funext x; simp only [history_zero]; rfl
  rw [h1, h2, ← Measure.map_map hΨ (measurable_pi_apply 0),
    ← Measure.map_map (hg.comp measurable_fst) (measurable_pi_apply 0), law0,
    ← Measure.map_map hg measurable_fst, init_fst]
  ext s hs
  rw [Measure.map_apply hΨ hs, Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hg]
  unfold initMeasure
  rw [Measure.compProd_apply (hΨ hs)]
  refine lintegral_congr fun ω => ?_
  rw [eta_zero]
  rfl

lemma lawT (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (p : Profile A S) (t : ℕ) :
    (playMeasure μ F p).map
      (fun x => ((state x, history x t), (signal x t, action x t))) =
    ((playMeasure μ F p).map (fun x => (state x, history x t))) ⊗ₘ eta F p t := by
  cases t with
  | zero => exact lawZero μ F p
  | succ n => exact lawSucc μ F p n

lemma stateLaw (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (p : Profile A S) : (playMeasure μ F p).map state = μ := by
  have : (state : (ℕ → Ω × S × A) → Ω) = Prod.fst ∘ (fun x => x 0) := rfl
  rw [this, ← Measure.map_map measurable_fst (measurable_pi_apply 0), law0, init_fst]

lemma measurable_lawMap (t : ℕ) : Measurable
    (fun x : ℕ → Ω × S × A => ((state x, history x t), (signal x t, action x t))) :=
  ((measurable_state).prodMk (measurable_history t)).prodMk
    ((measurable_signal t).prodMk (measurable_action t))


lemma history_succ (x : ℕ → Ω × S × A) (k : ℕ) :
    history x (k + 1) = Fin.snoc (history x k) (action x k) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [history]
  · simp [history]

lemma measurable_snocMap (k : ℕ) : Measurable
    (fun w : (Ω × (Fin k → A)) × (S × A) => (w.1.1, (Fin.snoc w.1.2 w.2.2 : Fin (k + 1) → A))) := by
  refine (measurable_fst.comp measurable_fst).prodMk (measurable_pi_lambda _ fun i => ?_)
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    exact measurable_snd.comp measurable_snd
  · simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)

lemma law_step (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (p : Profile A S) (k : ℕ) :
    (playMeasure μ F p).map (fun x => (state x, history x (k + 1))) =
      (((playMeasure μ F p).map (fun x => (state x, history x k))) ⊗ₘ eta F p k).map
        (fun w => (w.1.1, (Fin.snoc w.1.2 w.2.2 : Fin (k + 1) → A))) := by
  rw [← lawT, Measure.map_map (measurable_snocMap k) (measurable_lawMap k)]
  congr 1
  funext x
  simp only [Function.comp_apply, history_succ]

lemma law_hist0 (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (p : Profile A S) :
    (playMeasure μ F p).map (fun x => (state x, history x 0)) =
      μ.map (fun ω => (ω, (Fin.elim0 : Fin 0 → A))) := by
  have : (fun x : ℕ → Ω × S × A => (state x, history x 0)) =
      (fun ω => (ω, (Fin.elim0 : Fin 0 → A))) ∘ state := by
    funext x; simp only [Function.comp_apply, history_zero]
  rw [this, ← Measure.map_map (by fun_prop) measurable_state, stateLaw]

lemma eta_congr (F : Kernel Ω S) [IsMarkovKernel F] {p q : Profile A S} {k : ℕ}
    (h : q.σ k = p.σ k) : eta F q k = eta F p k := by
  unfold eta
  rw [h]

lemma law_indep (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (p q : Profile A S) (t : ℕ) (hqp : ∀ k < t, q.σ k = p.σ k) :
    ∀ k ≤ t, (playMeasure μ F q).map (fun x => (state x, history x k)) =
      (playMeasure μ F p).map (fun x => (state x, history x k)) := by
  intro k
  induction k with
  | zero => intro _; rw [law_hist0, law_hist0]
  | succ k ih =>
    intro hk
    rw [law_step, law_step, ih (by omega), eta_congr F (hqp k (by omega))]

lemma abs_integral_le {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    (f : X → ℝ) (M : ℝ) (h : ∀ x, |f x| ≤ M) : |∫ x, f x ∂ν| ≤ M := by
  have := norm_integral_le_of_norm_le_const (μ := ν) (f := f) (C := M)
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact h x)
  simpa [Real.norm_eq_abs] using this

lemma payoffG (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (p : Profile A S) (t : ℕ) (G : (Ω × (Fin t → A)) × (S × A) → ℝ) (hG : Measurable G)
    (M : ℝ) (hGb : ∀ w, |G w| ≤ M) :
    ∫ x, G ((state x, history x t), (signal x t, action x t)) ∂(playMeasure μ F p) =
      ∫ w, ∫ z, G (w, z) ∂(eta F p t w) ∂((playMeasure μ F p).map
        (fun x => (state x, history x t))) := by
  have h1 := integral_map (μ := playMeasure μ F p) (measurable_lawMap t).aemeasurable
    hG.aestronglyMeasurable
  rw [← h1, lawT, Measure.integral_compProd (Integrable.of_bound hG.aestronglyMeasurable M
    (ae_of_all _ fun w => by rw [Real.norm_eq_abs]; exact hGb w))]

lemma intL [StandardBorelSpace Ω] [Nonempty Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Kernel Ω S) [IsMarkovKernel F]
    (p : Profile A S) (t : ℕ) (H : Ω × (Fin t → A) → ℝ) (hH : Measurable H) (M : ℝ)
    (hHb : ∀ w, |H w| ≤ M) :
    ∫ w, H w ∂((playMeasure μ F p).map (fun x => (state x, history x t))) =
      ∫ h, ∫ ω, H (ω, h) ∂(publicBelief μ F p t h) ∂((playMeasure μ F p).map
        (fun x => history x t)) := by
  set P := playMeasure μ F p
  have h1 : P.map (fun x => (state x, history x t)) =
      (P.map (fun x => (history x t, state x))).map Prod.swap := by
    rw [Measure.map_map measurable_swap ((measurable_history t).prodMk measurable_state)]
    rfl
  rw [h1, integral_map measurable_swap.aemeasurable hH.aestronglyMeasurable,
    ← compProd_map_condDistrib measurable_state.aemeasurable,
    Measure.integral_compProd (f := fun x => H x.swap)
      (Integrable.of_bound (hH.comp measurable_swap).aestronglyMeasurable M
      (ae_of_all _ fun w => by rw [Real.norm_eq_abs]; exact hHb _))]
  rfl

/-- The expected payoff `∫ s, ∫ a, u a ω ∂κ (h, s) ∂F ω` of strategy `κ` at (state, history). -/
noncomputable def Gam (F : Kernel Ω S) {t : ℕ} (κ : Kernel ((Fin t → A) × S) A)
    (u : A → Ω → ℝ) (w : Ω × (Fin t → A)) : ℝ :=
  ∫ s, ∫ a, u a w.1 ∂(κ (w.2, s)) ∂(F w.1)

lemma eta_integral (F : Kernel Ω S) [IsMarkovKernel F] (p : Profile A S) (t : ℕ)
    (u : A → Ω → ℝ) (hu : Measurable (Function.uncurry u)) (M : ℝ) (hM : ∀ a ω, |u a ω| ≤ M)
    (w : Ω × (Fin t → A)) :
    ∫ z, u z.2 w.1 ∂(eta F p t w) = Gam F (p.σ t) u w := by
  have hm : Measurable fun z : S × A => u z.2 w.1 :=
    hu.comp (measurable_snd.prodMk measurable_const)
  rw [eta, ProbabilityTheory.integral_compProd (Integrable.of_bound hm.aestronglyMeasurable M
    (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hM _ _))]
  simp only [Kernel.comap_apply, Gam]

lemma measurable_Gam (F : Kernel Ω S) [IsMarkovKernel F] (p : Profile A S) (t : ℕ)
    (u : A → Ω → ℝ) (hu : Measurable (Function.uncurry u)) (M : ℝ) (hM : ∀ a ω, |u a ω| ≤ M) :
    Measurable (Gam F (p.σ t) u) := by
  have : Gam F (p.σ t) u = fun w => ∫ z, u z.2 w.1 ∂(eta F p t w) := by
    funext w; rw [eta_integral F p t u hu M hM]
  rw [this]
  have hm : Measurable fun q : (Ω × (Fin t → A)) × (S × A) => u q.2.2 q.1.1 :=
    hu.comp ((measurable_snd.comp measurable_snd).prodMk (measurable_fst.comp measurable_fst))
  exact (hm.stronglyMeasurable.integral_kernel_prod_right' (κ := eta F p t)).measurable

lemma abs_Gam_le (F : Kernel Ω S) [IsMarkovKernel F] {t : ℕ} (κ : Kernel ((Fin t → A) × S) A)
    [IsMarkovKernel κ] (u : A → Ω → ℝ) (M : ℝ) (hM : ∀ a ω, |u a ω| ≤ M) (w : Ω × (Fin t → A)) :
    |Gam F κ u w| ≤ M :=
  abs_integral_le _ _ _ fun s => abs_integral_le _ _ _ fun a => hM _ _

/-- `ψ(h) = E[y_t | h_t = h]`. -/
noncomputable def psi [StandardBorelSpace Ω] [Nonempty Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Kernel Ω S) [IsMarkovKernel F] (p : Profile A S) (t : ℕ) (u : A → Ω → ℝ)
    (h : Fin t → A) : ℝ :=
  ∫ ω, Gam F (p.σ t) u (ω, h) ∂(publicBelief μ F p t h)

lemma measurable_psi [StandardBorelSpace Ω] [Nonempty Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Kernel Ω S) [IsMarkovKernel F] (p : Profile A S) (t : ℕ) (u : A → Ω → ℝ)
    (hu : Measurable (Function.uncurry u)) (M : ℝ) (hM : ∀ a ω, |u a ω| ≤ M) :
    Measurable (psi μ F p t u) := by
  have hm : Measurable fun q : (Fin t → A) × Ω => Gam F (p.σ t) u (q.2, q.1) :=
    (measurable_Gam F p t u hu M hM).comp (measurable_snd.prodMk measurable_fst)
  exact (hm.stronglyMeasurable.integral_kernel_prod_right'
    (κ := publicBelief μ F p t)).measurable

lemma condExp_eq_psi [StandardBorelSpace Ω] [Nonempty Ω] [Nonempty A] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Kernel Ω S) [IsMarkovKernel F] (p : Profile A S) (t : ℕ) (u : A → Ω → ℝ)
    (hu : Measurable (Function.uncurry u)) (M : ℝ) (hM : ∀ a ω, |u a ω| ≤ M) :
    (playMeasure μ F p)[fun y => u (action y t) (state y) | histSigma t] =ᵐ[playMeasure μ F p]
      fun x => psi μ F p t u (history x t) := by
  set P := playMeasure μ F p
  have hm : (histSigma t : MeasurableSpace (ℕ → Ω × S × A)) ≤ MeasurableSpace.pi :=
    (measurable_history t).comap_le
  have hψ := measurable_psi μ F p t u hu M hM
  have hψb : ∀ h, |psi μ F p t u h| ≤ M := fun h =>
    abs_integral_le _ _ _ fun ω => abs_Gam_le F _ u M hM _
  have hyt : Measurable fun y : ℕ → Ω × S × A => u (action y t) (state y) :=
    hu.comp ((measurable_action t).prodMk measurable_state)
  have hyint : Integrable (fun y => u (action y t) (state y)) P :=
    Integrable.of_bound hyt.aestronglyMeasurable M
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hM _ _)
  have hψint : Integrable (fun x => psi μ F p t u (history x t)) P :=
    Integrable.of_bound (hψ.comp (measurable_history t)).aestronglyMeasurable M
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hψb _)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hyint (fun s _ _ => hψint.integrableOn)
    ?_ ?_).symm
  · rintro s ⟨D, hD, rfl⟩ -
    have hDm : MeasurableSet ((fun x => history x t) ⁻¹' D : Set (ℕ → Ω × S × A)) :=
      measurable_history t hD
    -- left side
    rw [← setIntegral_map hD hψ.aestronglyMeasurable (measurable_history t).aemeasurable]
    -- right side
    rw [← integral_indicator hDm]
    have hrhs : (((fun x => history x t) ⁻¹' D).indicator fun y => u (action y t) (state y)) =
        fun x => (fun q : (Ω × (Fin t → A)) × (S × A) => D.indicator 1 q.1.2 * u q.2.2 q.1.1)
          ((state x, history x t), (signal x t, action x t)) := by
      funext x
      by_cases hx : history x t ∈ D
      · simp [Set.indicator_of_mem, hx]
      · simp [Set.indicator_of_notMem, hx]
    have hGm : Measurable fun q : (Ω × (Fin t → A)) × (S × A) => D.indicator 1 q.1.2 * u q.2.2 q.1.1 :=
      ((measurable_one.indicator hD).comp (measurable_snd.comp measurable_fst)).mul
        (hu.comp ((measurable_snd.comp measurable_snd).prodMk (measurable_fst.comp measurable_fst)))
    have hGb : ∀ q : (Ω × (Fin t → A)) × (S × A), |D.indicator 1 q.1.2 * u q.2.2 q.1.1| ≤ M := by
      intro q
      by_cases hq : q.1.2 ∈ D
      · simp [Set.indicator_of_mem hq, hM]
      · simp [Set.indicator_of_notMem hq]; exact (abs_nonneg _).trans (hM q.2.2 q.1.1)
    rw [hrhs, payoffG μ F p t _ hGm M hGb]
    have hinner : ∀ w : Ω × (Fin t → A), ∫ z, D.indicator 1 w.2 * u z.2 w.1 ∂(eta F p t w) =
        D.indicator 1 w.2 * Gam F (p.σ t) u w := by
      intro w
      rw [integral_const_mul, eta_integral F p t u hu M hM]
    simp_rw [hinner]
    have hHm : Measurable fun w : Ω × (Fin t → A) => D.indicator 1 w.2 * Gam F (p.σ t) u w :=
      ((measurable_one.indicator hD).comp measurable_snd).mul (measurable_Gam F p t u hu M hM)
    have hHb : ∀ w : Ω × (Fin t → A), |D.indicator 1 w.2 * Gam F (p.σ t) u w| ≤ M := by
      intro w
      by_cases hq : w.2 ∈ D
      · simp [Set.indicator_of_mem hq, abs_Gam_le F _ u M hM]
      · simp [Set.indicator_of_notMem hq]; exact (abs_nonneg _).trans (hM (Classical.arbitrary A) w.1)
    rw [intL μ F p t _ hHm M hHb, ← integral_indicator hD]
    refine integral_congr_ae (ae_of_all _ fun h => ?_)
    simp only
    rw [integral_const_mul]
    by_cases hh : h ∈ D
    · simp [Set.indicator_of_mem hh, psi]
    · simp [Set.indicator_of_notMem hh]
  · exact (hψ.comp (Measurable.of_comap_le le_rfl)).aestronglyMeasurable

section Top
variable [StandardBorelSpace Ω] [Nonempty Ω]

/-- `G(a, h) = E[u(a, ω) | h_t = h]`. -/
noncomputable def Gv (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (p : Profile A S) (t : ℕ) (u : A → Ω → ℝ) (a : A) (h : Fin t → A) : ℝ :=
  ∫ ω, u a ω ∂(publicBelief μ F p t h)

/-- `Ŷ(h) = sup_a G(a, h)`. -/
noncomputable def Yh (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (p : Profile A S) (t : ℕ) (u : A → Ω → ℝ) (h : Fin t → A) : ℝ :=
  ⨆ a, Gv μ F p t u a h

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
  (p : Profile A S) (t : ℕ) (u : A → Ω → ℝ) (hu : Measurable (Function.uncurry u)) (M : ℝ)
  (hM : ∀ a ω, |u a ω| ≤ M)
include hu hM

lemma Gv_bound (a : A) (h : Fin t → A) : |Gv μ F p t u a h| ≤ M :=
  abs_integral_le _ _ _ fun ω => hM a ω

lemma Gv_meas (a : A) : Measurable (Gv μ F p t u a) := by
  have hm : Measurable fun ω => u a ω := hu.comp (measurable_const.prodMk measurable_id)
  exact (hm.stronglyMeasurable.integral_kernel (κ := publicBelief μ F p t)).measurable

lemma Gv_cont [PseudoMetricSpace A] (hc : ∀ ω, Continuous fun a => u a ω) (h : Fin t → A) :
    Continuous fun a => Gv μ F p t u a h := by
  exact continuous_of_dominated (bound := fun _ => M)
    (fun a => (hu.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (fun a => ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hM a ω)
    (integrable_const M) (ae_of_all _ fun ω => hc ω)

lemma Gv_bdd [Nonempty A] (h : Fin t → A) : BddAbove (Set.range fun a => Gv μ F p t u a h) :=
  ⟨M, by rintro _ ⟨a, rfl⟩; exact (le_abs_self _).trans (Gv_bound μ F p t u hu M hM a h)⟩

lemma Yh_eq_dense [PseudoMetricSpace A] [TopologicalSpace.SeparableSpace A] [Nonempty A]
    (hc : ∀ ω, Continuous fun a => u a ω) (h : Fin t → A) :
    Yh μ F p t u h = ⨆ n, Gv μ F p t u (TopologicalSpace.denseSeq A n) h := by
  set d := TopologicalSpace.denseSeq A
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq A
  have hbdd := Gv_bdd μ F p t u hu M hM h
  have hbdd' : BddAbove (Set.range fun n => Gv μ F p t u (d n) h) :=
    ⟨M, by rintro _ ⟨n, rfl⟩; exact (le_abs_self _).trans (Gv_bound μ F p t u hu M hM _ h)⟩
  apply le_antisymm
  · refine ciSup_le fun a => ?_
    have hcl : IsClosed {a : A | Gv μ F p t u a h ≤ ⨆ n, Gv μ F p t u (d n) h} :=
      isClosed_le (Gv_cont μ F p t u hu M hM hc h) continuous_const
    have hsub : Set.range d ⊆ {a : A | Gv μ F p t u a h ≤ ⨆ n, Gv μ F p t u (d n) h} := by
      rintro _ ⟨n, rfl⟩; exact le_ciSup hbdd' n
    have h2 := hcl.closure_subset_iff.2 hsub
    rw [hd.closure_range] at h2
    exact h2 (Set.mem_univ a)
  · exact ciSup_le fun n => le_ciSup hbdd (d n)

lemma Yh_meas [PseudoMetricSpace A] [TopologicalSpace.SeparableSpace A] [Nonempty A]
    (hc : ∀ ω, Continuous fun a => u a ω) : Measurable (Yh μ F p t u) := by
  have : Yh μ F p t u = fun h => ⨆ n, Gv μ F p t u (TopologicalSpace.denseSeq A n) h := by
    funext h; exact Yh_eq_dense μ F p t u hu M hM hc h
  rw [this]
  exact Measurable.iSup fun n => Gv_meas μ F p t u hu M hM _

lemma Yh_bound [Nonempty A] (h : Fin t → A) : |Yh μ F p t u h| ≤ M := by
  rw [abs_le]
  constructor
  · have h1 := Gv_bound μ F p t u hu M hM (Classical.arbitrary A) h
    rw [abs_le] at h1
    exact h1.1.trans (le_ciSup (Gv_bdd μ F p t u hu M hM h) _)
  · exact ciSup_le fun a => (le_abs_self _).trans (Gv_bound μ F p t u hu M hM a h)

lemma selector [PseudoMetricSpace A] [TopologicalSpace.SeparableSpace A] [Nonempty A]
    (hc : ∀ ω, Continuous fun a => u a ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : (Fin t → A) → A, Measurable g ∧ ∀ h, Yh μ F p t u h - ε < Gv μ F p t u (g h) h := by
  classical
  set d := TopologicalSpace.denseSeq A
  have hex : ∀ h, ∃ n, Yh μ F p t u h - ε < Gv μ F p t u (d n) h := by
    intro h
    have h1 : Yh μ F p t u h - ε < ⨆ n, Gv μ F p t u (d n) h := by
      rw [← Yh_eq_dense μ F p t u hu M hM hc h]; linarith
    exact exists_lt_of_lt_ciSup h1
  let N : (Fin t → A) → ℕ := fun h => Nat.find (hex h)
  have hP : ∀ n, MeasurableSet {h | Yh μ F p t u h - ε < Gv μ F p t u (d n) h} := fun n =>
    measurableSet_lt ((Yh_meas μ F p t u hu M hM hc).sub measurable_const)
      (Gv_meas μ F p t u hu M hM _)
  have hN : Measurable N := by
    refine measurable_to_countable' fun n => ?_
    have : N ⁻¹' {n} = {h | Yh μ F p t u h - ε < Gv μ F p t u (d n) h} ∩
        ⋂ m ∈ Finset.range n, {h | Yh μ F p t u h - ε < Gv μ F p t u (d m) h}ᶜ := by
      ext h
      simp only [Set.mem_preimage, Set.mem_singleton_iff, N, Nat.find_eq_iff, Set.mem_inter_iff,
        Set.mem_iInter, Finset.mem_range, Set.mem_compl_iff, Set.mem_ofPred_eq]
    rw [this]
    exact (hP n).inter (MeasurableSet.biInter (Set.to_countable _) fun m _ => (hP m).compl)
  refine ⟨fun h => d (N h), (measurable_from_nat (f := d)).comp hN, fun h => ?_⟩
  exact Nat.find_spec (hex h)

lemma payoff_Gam (q : Profile A S) :
    ∫ x, u (action x t) (state x) ∂(playMeasure μ F q) =
      ∫ w, Gam F (q.σ t) u w ∂((playMeasure μ F q).map (fun x => (state x, history x t))) := by
  have hG : Measurable fun w : (Ω × (Fin t → A)) × (S × A) => u w.2.2 w.1.1 :=
    hu.comp ((measurable_snd.comp measurable_snd).prodMk (measurable_fst.comp measurable_fst))
  have := payoffG μ F q t (fun w => u w.2.2 w.1.1) hG M (fun w => hM _ _)
  rw [this]
  simp_rw [eta_integral F q t u hu M hM]

lemma psi_ge [PseudoMetricSpace A] [TopologicalSpace.SeparableSpace A] [Nonempty A]
    (hc : ∀ ω, Continuous fun a => u a ω) (hp : IsPBE μ F u p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ h ∂((playMeasure μ F p).map (fun x => history x t)),
      Yh μ F p t u h - 2 * ε ≤ psi μ F p t u h := by
  classical
  obtain ⟨g, hg, hgY⟩ := selector μ F p t u hu M hM hc hε
  set D := {h : Fin t → A | psi μ F p t u h < Yh μ F p t u h - 2 * ε} with hD_def
  have hDm : MeasurableSet D :=
    measurableSet_lt (measurable_psi μ F p t u hu M hM)
      ((Yh_meas μ F p t u hu M hM hc).sub measurable_const)
  set lamH := (playMeasure μ F p).map (fun x => history x t)
  rw [ae_iff]
  have hset : {h | ¬ (Yh μ F p t u h - 2 * ε ≤ psi μ F p t u h)} = D := by
    ext h; simp only [hD_def, not_le, Set.mem_ofPred_eq]
  rw [hset]
  by_contra hne
  have hpos : 0 < lamH D := pos_iff_ne_zero.2 hne
  -- the deviation
  have hD' : MeasurableSet {q : (Fin t → A) × S | q.1 ∈ D} := measurable_fst hDm
  let τ : Kernel ((Fin t → A) × S) A :=
    Kernel.piecewise hD' (Kernel.deterministic (fun q => g q.1) (hg.comp measurable_fst)) (p.σ t)
  have hτ : IsMarkovKernel τ := by infer_instance
  set q := p.replace t τ
  have hqt : q.σ t = τ := by
    show Function.update p.σ t τ t = τ
    rw [Function.update_self]
  have hqk : ∀ k < t, q.σ k = p.σ k := fun k hk => by
    show Function.update p.σ t τ k = p.σ k
    rw [Function.update_of_ne hk.ne]
  have hL : (playMeasure μ F q).map (fun x => (state x, history x t)) =
      (playMeasure μ F p).map (fun x => (state x, history x t)) :=
    law_indep μ F p q t hqk t le_rfl
  have hpbe := hp t τ
  rw [payoff_Gam μ F t u hu M hM, payoff_Gam μ F t u hu M hM, hL, hqt] at hpbe
  set L := (playMeasure μ F p).map (fun x => (state x, history x t))
  -- pointwise description of the deviation payoff
  have hGamτ : ∀ w : Ω × (Fin t → A), Gam F τ u w - Gam F (p.σ t) u w =
      D.indicator 1 w.2 * (u (g w.2) w.1 - Gam F (p.σ t) u w) := by
    intro w
    by_cases hw : w.2 ∈ D
    · have : Gam F τ u w = u (g w.2) w.1 := by
        unfold Gam
        have h1 : ∀ s, ∫ a, u a w.1 ∂(τ (w.2, s)) = u (g w.2) w.1 := by
          intro s
          rw [Kernel.piecewise_apply, if_pos (show (w.2, s) ∈ {q : (Fin t → A) × S | q.1 ∈ D}
            from hw), Kernel.deterministic_apply,
            integral_dirac' (fun a => u a w.1) _
              (hu.comp (measurable_id.prodMk measurable_const)).stronglyMeasurable]
        simp_rw [h1]
        simp
      rw [this, Set.indicator_of_mem hw, Pi.one_apply, one_mul]
    · have : Gam F τ u w = Gam F (p.σ t) u w := by
        unfold Gam
        congr 1; funext s
        rw [Kernel.piecewise_apply, if_neg (show (w.2, s) ∉ {q : (Fin t → A) × S | q.1 ∈ D}
          from hw)]
      rw [this, Set.indicator_of_notMem hw, zero_mul, sub_self]
  have hGσm := measurable_Gam F p t u hu M hM
  have hGτm : Measurable (Gam F τ u) := by
    have := measurable_Gam F q t u hu M hM
    rwa [hqt] at this
  have hGτint : Integrable (Gam F τ u) L :=
    Integrable.of_bound hGτm.aestronglyMeasurable M
      (ae_of_all _ fun w => by rw [Real.norm_eq_abs]; exact abs_Gam_le F τ u M hM w)
  have hGσint : Integrable (Gam F (p.σ t) u) L :=
    Integrable.of_bound hGσm.aestronglyMeasurable M
      (ae_of_all _ fun w => by rw [Real.norm_eq_abs]; exact abs_Gam_le F _ u M hM w)
  have hdiff : ∫ w, Gam F τ u w ∂L - ∫ w, Gam F (p.σ t) u w ∂L ≤ 0 := by linarith
  rw [← integral_sub hGτint hGσint] at hdiff
  simp_rw [hGamτ] at hdiff
  have hHm : Measurable fun w : Ω × (Fin t → A) =>
      D.indicator 1 w.2 * (u (g w.2) w.1 - Gam F (p.σ t) u w) :=
    ((measurable_one.indicator hDm).comp measurable_snd).mul
      ((hu.comp ((hg.comp measurable_snd).prodMk measurable_fst)).sub hGσm)
  have hHb : ∀ w : Ω × (Fin t → A),
      |D.indicator 1 w.2 * (u (g w.2) w.1 - Gam F (p.σ t) u w)| ≤ 2 * M := by
    intro w
    have h1 := hM (g w.2) w.1
    have h2 := abs_Gam_le F (p.σ t) u M hM w
    have hM0 : 0 ≤ M := (abs_nonneg _).trans h1
    by_cases hw : w.2 ∈ D
    · rw [Set.indicator_of_mem hw, Pi.one_apply, one_mul]
      exact (abs_sub _ _).trans (by linarith)
    · rw [Set.indicator_of_notMem hw, zero_mul, abs_zero]; linarith
  rw [intL μ F p t _ hHm (2 * M) hHb] at hdiff
  -- evaluate the inner integral
  have hin : ∀ h : Fin t → A, ∫ ω, D.indicator 1 h * (u (g h) ω - Gam F (p.σ t) u (ω, h))
      ∂(publicBelief μ F p t h) = D.indicator 1 h * (Gv μ F p t u (g h) h - psi μ F p t u h) := by
    intro h
    rw [integral_const_mul, integral_sub]
    · rfl
    · exact Integrable.of_bound (hu.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        M (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hM _ _)
    · exact Integrable.of_bound (hGσm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
        M (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact abs_Gam_le F _ u M hM _)
  simp_rw [hin] at hdiff
  -- lower bound on `D`
  have hlow : ∀ h, D.indicator (fun _ => ε) h ≤
      D.indicator 1 h * (Gv μ F p t u (g h) h - psi μ F p t u h) := by
    intro h
    by_cases hh : h ∈ D
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem hh, Pi.one_apply, one_mul]
      have h1 := hgY h
      have h2 : psi μ F p t u h < Yh μ F p t u h - 2 * ε := hh
      linarith
    · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem hh, zero_mul]
  have hGvm : Measurable fun h => Gv μ F p t u (g h) h := by
    have hm : Measurable fun q : (Fin t → A) × Ω => u (g q.1) q.2 :=
      hu.comp ((hg.comp measurable_fst).prodMk measurable_snd)
    exact (hm.stronglyMeasurable.integral_kernel_prod_right'
      (κ := publicBelief μ F p t)).measurable
  have hint2 : Integrable (fun h => D.indicator 1 h * (Gv μ F p t u (g h) h - psi μ F p t u h)) lamH :=
    Integrable.of_bound (((measurable_one.indicator hDm).mul
      (hGvm.sub (measurable_psi μ F p t u hu M hM))).aestronglyMeasurable) (2 * M)
      (ae_of_all _ fun h => by
        rw [Real.norm_eq_abs]
        have h1 := Gv_bound μ F p t u hu M hM (g h) h
        have h2 : |psi μ F p t u h| ≤ M := abs_integral_le _ _ _ fun ω => abs_Gam_le F _ u M hM _
        by_cases hh : h ∈ D
        · rw [Set.indicator_of_mem hh, Pi.one_apply, one_mul]
          exact (abs_sub _ _).trans (by linarith)
        · rw [Set.indicator_of_notMem hh, zero_mul, abs_zero]
          linarith [abs_nonneg (psi μ F p t u h)])
  have hge : ε * lamH.real D ≤
      ∫ h, D.indicator 1 h * (Gv μ F p t u (g h) h - psi μ F p t u h) ∂lamH := by
    calc ε * lamH.real D = ∫ h, D.indicator (fun _ => ε) h ∂lamH := by
          rw [integral_indicator_const _ hDm, smul_eq_mul, mul_comm]
      _ ≤ _ := integral_mono ((integrable_const ε).indicator hDm) hint2 hlow
  have hreal : 0 < lamH.real D := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  nlinarith

end Top

end SSLLem1Aux

open SeqSocialLearning.Adequate SSLLem1Aux

theorem solution {Ω A S : Type*}
    [MetricSpace Ω] [CompleteSpace Ω] [TopologicalSpace.SeparableSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] [Nonempty Ω]
    [MetricSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
    [MeasurableSpace S] [StandardBorelSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (hF : Standing F)
    (u : A → Ω → ℝ) (hu : InU u) (p : Profile A S) (hp : IsPBE μ F u p) :
    ∀ᵐ x ∂(playMeasure μ F p),
      Tendsto (fun t => valuePrivInfo μ F p u t x) atTop (𝓝 0) := by
  obtain ⟨hmeas, ⟨M, hM⟩, hc⟩ := hu
  set P := playMeasure μ F p with hP
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (Classical.arbitrary A) (Classical.arbitrary Ω))
  have hm : ∀ t, (histSigma t : MeasurableSpace (ℕ → Ω × S × A)) ≤ MeasurableSpace.pi :=
    fun t => (measurable_history t).comap_le
  -- `ŷ_t` as a function of the history
  have hyhat : ∀ t x, yhat μ F p u t x = Yh μ F p t u (history x t) := fun t x => rfl
  have hYm : ∀ t, Measurable fun x : ℕ → Ω × S × A => Yh μ F p t u (history x t) := fun t =>
    (Yh_meas μ F p t u hmeas M hM hc).comp (measurable_history t)
  have hYint : ∀ t, Integrable (fun x : ℕ → Ω × S × A => Yh μ F p t u (history x t)) P := fun t =>
    Integrable.of_bound (hYm t).aestronglyMeasurable M
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact Yh_bound μ F p t u hmeas M hM _)
  have hyt : ∀ t, Measurable fun y : ℕ → Ω × S × A => u (action y t) (state y) := fun t =>
    hmeas.comp ((measurable_action t).prodMk measurable_state)
  have hyint : ∀ t, Integrable (fun y : ℕ → Ω × S × A => u (action y t) (state y)) P := fun t =>
    Integrable.of_bound (hyt t).aestronglyMeasurable M
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hM _ _)
  -- (1) the value of private information is nonnegative
  have hnonneg : ∀ t, ∀ᵐ x ∂P, 0 ≤ valuePrivInfo μ F p u t x := by
    intro t
    have hε : ∀ n : ℕ, ∀ᵐ x ∂P, -(2 * (1 / ((n : ℝ) + 1))) ≤ valuePrivInfo μ F p u t x := by
      intro n
      have h1 := psi_ge μ F p t u hmeas M hM hc hp (ε := 1 / ((n : ℝ) + 1)) (by positivity)
      have h2 := ae_of_ae_map (measurable_history t).aemeasurable h1
      filter_upwards [h2, condExp_eq_psi μ F p t u hmeas M hM] with x hx hx'
      unfold valuePrivInfo
      rw [hx', hyhat]
      linarith
    filter_upwards [ae_all_iff.2 hε] with x hx
    by_contra hneg
    push Not at hneg
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < -(valuePrivInfo μ F p u t x) / 2 by linarith)
    have := hx n
    linarith
  -- (2) integrals
  have hdint : ∀ t, Integrable (fun x => valuePrivInfo μ F p u t x) P := fun t =>
    integrable_condExp.sub (hYint t)
  have hEd : ∀ t, ∫ x, valuePrivInfo μ F p u t x ∂P =
      ∫ x, u (action x t) (state x) ∂P - ∫ x, Yh μ F p t u (history x t) ∂P := by
    intro t
    have : (fun x => valuePrivInfo μ F p u t x) = fun x =>
        P[fun y => u (action y t) (state y) | histSigma t] x - Yh μ F p t u (history x t) := rfl
    rw [this, integral_sub integrable_condExp (hYint t), integral_condExp (hm t)]
  -- (3) imitation: agent `t + 1` can copy agent `t`
  have himit : ∀ t, ∫ x, u (action x t) (state x) ∂P ≤
      ∫ x, Yh μ F p (t + 1) u (history x (t + 1)) ∂P := by
    intro t
    set f : (Fin (t + 1) → A) × Ω → ℝ := fun q => u (q.1 (Fin.last t)) q.2
    have hf : Measurable f := by
      show Measurable fun q : (Fin (t + 1) → A) × Ω => Function.uncurry u (q.1 (Fin.last t), q.2)
      exact hmeas.comp (((measurable_pi_apply (Fin.last t)).comp measurable_fst).prodMk
        measurable_snd)
    have hce := condExp_prod_ae_eq_integral_condDistrib (μ := P) (measurable_history (t + 1))
      measurable_state.aemeasurable hf.stronglyMeasurable (hyint t)
    rw [← integral_condExp (μ := P) ((measurable_history (t + 1)).comap_le)
      (f := fun x => u (action x t) (state x))]
    have hce' : P[fun x => u (action x t) (state x) |
        MeasurableSpace.comap (fun x => history x (t + 1)) inferInstance] =ᵐ[P]
        fun x => Gv μ F p (t + 1) u (history x (t + 1) (Fin.last t)) (history x (t + 1)) := hce
    rw [integral_congr_ae hce']
    refine integral_mono ?_ (hYint (t + 1)) fun x => ?_
    · have hGm : Measurable fun x : ℕ → Ω × S × A =>
          Gv μ F p (t + 1) u (history x (t + 1) (Fin.last t)) (history x (t + 1)) := by
        have hm2 : Measurable fun q : (Fin (t + 1) → A) × Ω => u (q.1 (Fin.last t)) q.2 := hf
        exact ((hm2.stronglyMeasurable.integral_kernel_prod_right'
          (κ := publicBelief μ F p (t + 1))).measurable).comp (measurable_history (t + 1))
      exact Integrable.of_bound hGm.aestronglyMeasurable M
        (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact Gv_bound μ F p _ u hmeas M hM _ _)
    · exact le_ciSup (Gv_bdd μ F p (t + 1) u hmeas M hM _) _
  -- (4) telescoping
  have hsum : ∀ T, ∑ t ∈ Finset.range T, ∫ x, valuePrivInfo μ F p u t x ∂P ≤ 2 * M := by
    intro T
    have h1 : ∀ t, ∫ x, valuePrivInfo μ F p u t x ∂P ≤
        ∫ x, Yh μ F p (t + 1) u (history x (t + 1)) ∂P - ∫ x, Yh μ F p t u (history x t) ∂P := by
      intro t; rw [hEd]; linarith [himit t]
    calc ∑ t ∈ Finset.range T, ∫ x, valuePrivInfo μ F p u t x ∂P
        ≤ ∑ t ∈ Finset.range T, (∫ x, Yh μ F p (t + 1) u (history x (t + 1)) ∂P -
            ∫ x, Yh μ F p t u (history x t) ∂P) := Finset.sum_le_sum fun t _ => h1 t
      _ = ∫ x, Yh μ F p T u (history x T) ∂P - ∫ x, Yh μ F p 0 u (history x 0) ∂P :=
          Finset.sum_range_sub (fun t => ∫ x, Yh μ F p t u (history x t) ∂P) T
      _ ≤ M - (-M) := by
          have hT := abs_integral_le P _ M fun x => Yh_bound μ F p T u hmeas M hM (history x T)
          have h0 := abs_integral_le P _ M fun x => Yh_bound μ F p 0 u hmeas M hM (history x 0)
          rw [abs_le] at hT h0
          linarith
      _ = 2 * M := by ring
  -- (5) almost sure convergence
  have hdm : ∀ t, Measurable fun x => valuePrivInfo μ F p u t x := fun t =>
    ((stronglyMeasurable_condExp.mono (hm t)).measurable).sub (hYm t)
  have hEd0 : ∀ t, 0 ≤ ∫ x, valuePrivInfo μ F p u t x ∂P := fun t =>
    integral_nonneg_of_ae (hnonneg t)
  have hlint : ∫⁻ x, ∑' t, ENNReal.ofReal (valuePrivInfo μ F p u t x) ∂P ≠ ⊤ := by
    rw [lintegral_tsum fun t => (hdm t).ennreal_ofReal.aemeasurable]
    have : ∀ t, ∫⁻ x, ENNReal.ofReal (valuePrivInfo μ F p u t x) ∂P =
        ENNReal.ofReal (∫ x, valuePrivInfo μ F p u t x ∂P) := fun t =>
      (ofReal_integral_eq_lintegral_ofReal (hdint t) (hnonneg t)).symm
    simp_rw [this]
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := 2 * M))
      (ENNReal.tsum_le_of_sum_range_le fun T => ?_)
    rw [← ENNReal.ofReal_sum_of_nonneg fun t _ => hEd0 t]
    exact ENNReal.ofReal_le_ofReal (hsum T)
  have hfin : ∀ᵐ x ∂P, ∑' t, ENNReal.ofReal (valuePrivInfo μ F p u t x) < ⊤ :=
    ae_lt_top (Measurable.tsum fun t => (hdm t).ennreal_ofReal) hlint
  filter_upwards [hfin, ae_all_iff.2 hnonneg] with x hx hx0
  have h1 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hx.ne
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
  simp only [ENNReal.toReal_zero] at h2
  refine h2.congr fun t => ?_
  simp [ENNReal.toReal_ofReal (hx0 t)]
