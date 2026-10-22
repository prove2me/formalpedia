-- Prove2me | solution 1 for SeqSocialLearning.Adequate.necessity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T09:34:53.188881+00:00
-- url     : https://prove2.me/submissions/3bfff06c-e0ad-4bb2-8103-ad0648a743ae

import Mathlib
import Definitions.Def_SeqSocialLearning_Adequate_Model
import Definitions.Def_SeqSocialLearning_Adequate_Signals

open MeasureTheory ProbabilityTheory Filter Topology

namespace SSLNecAux
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

lemma actDirac [MeasurableSingletonClass A] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Kernel Ω S) [IsMarkovKernel F]
    (p : Profile A S) (k : ℕ) (a0 : A)
    (h : p.σ k = Kernel.const _ (Measure.dirac a0)) :
    ∀ᵐ x ∂(playMeasure μ F p), action x k = a0 := by
  rw [ae_iff]
  have hT : MeasurableSet {w : (Ω × (Fin k → A)) × (S × A) | w.2.2 ≠ a0} :=
    (measurableSet_singleton a0).compl.preimage (measurable_snd.comp measurable_snd)
  have : {x : ℕ → Ω × S × A | ¬ action x k = a0} =
      (fun x => ((state x, history x k), (signal x k, action x k))) ⁻¹'
        {w : (Ω × (Fin k → A)) × (S × A) | w.2.2 ≠ a0} := rfl
  rw [this, ← Measure.map_apply (measurable_lawMap k) hT, lawT, Measure.compProd_apply hT]
  have h0 : ∀ w, eta F p k w (Prod.mk w ⁻¹' {w : (Ω × (Fin k → A)) × (S × A) | w.2.2 ≠ a0}) = 0 := by
    intro w
    rw [eta, Kernel.compProd_apply (measurable_prodMk_left hT)]
    simp [Kernel.comap_apply, h]
  rw [lintegral_congr h0, lintegral_zero]

/-- The profile in which every agent plays `a0` regardless of history and signal. -/
noncomputable def constProfile (a0 : A) : Profile A S where
  σ := fun _ => Kernel.const _ (Measure.dirac a0)
  markov := fun _ => inferInstance

lemma devPayoff [MeasurableSingletonClass A] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Kernel Ω S) [IsMarkovKernel F]
    (a0 : A) (t : ℕ) (τ : Kernel ((Fin t → A) × S) A) [IsMarkovKernel τ]
    (f : A → Ω → ℝ) (hf : Measurable (Function.uncurry f)) (M : ℝ)
    (hM : ∀ a ω, |f a ω| ≤ M) :
    ∫ x, f (action x t) (state x) ∂(playMeasure μ F ((constProfile (S := S) a0).replace t τ)) =
      ∫ ω, ∫ s, ∫ a, f a ω ∂(τ ((fun _ => a0), s)) ∂(F ω) ∂μ := by
  set q := (constProfile (S := S) a0).replace t τ with hq
  set P := playMeasure μ F q
  have hk : ∀ k < t, ∀ᵐ x ∂P, action x k = a0 := by
    intro k hkt
    apply actDirac μ F q k a0
    show Function.update (constProfile (S := S) a0).σ t τ k = _
    rw [Function.update_of_ne hkt.ne]
    rfl
  have hhist : ∀ᵐ x ∂P, history x t = fun _ => a0 := by
    have : ∀ᵐ x ∂P, ∀ i : Fin t, action x i = a0 := ae_all_iff.2 (fun i => hk i i.2)
    filter_upwards [this] with x hx
    funext i
    exact hx i
  let g : Ω → Ω × (Fin t → A) := fun ω => (ω, fun _ => a0)
  have hg : Measurable g := by fun_prop
  have hL : P.map (fun x => (state x, history x t)) = μ.map g := by
    have hae : (fun x : ℕ → Ω × S × A => (state x, history x t)) =ᵐ[P] g ∘ state :=
      hhist.mono fun x hx => by simp only [Function.comp_apply, g, hx]
    rw [Measure.map_congr hae, ← Measure.map_map hg measurable_state, stateLaw]
  let G : (Ω × (Fin t → A)) × (S × A) → ℝ := fun w => f w.2.2 w.1.1
  have hG : Measurable G :=
    hf.comp ((measurable_snd.comp measurable_snd).prodMk (measurable_fst.comp measurable_fst))
  have hGb : ∀ w, ‖G w‖ ≤ M := fun w => by rw [Real.norm_eq_abs]; exact hM _ _
  have hσt : q.σ t = τ := by
    show Function.update (constProfile (S := S) a0).σ t τ t = τ
    rw [Function.update_self]
  calc ∫ x, f (action x t) (state x) ∂P
      = ∫ w, G w ∂(P.map (fun x => ((state x, history x t), (signal x t, action x t)))) :=
        (integral_map (measurable_lawMap t).aemeasurable hG.aestronglyMeasurable).symm
    _ = ∫ w, G w ∂((μ.map g) ⊗ₘ eta F q t) := by rw [lawT, hL]
    _ = ∫ y, ∫ z, G (y, z) ∂(eta F q t y) ∂(μ.map g) :=
        Measure.integral_compProd
          (Integrable.of_bound hG.aestronglyMeasurable M (ae_of_all _ hGb))
    _ = ∫ ω, ∫ z, G (g ω, z) ∂(eta F q t (g ω)) ∂μ := by
        rw [integral_map hg.aemeasurable]
        exact (hG.stronglyMeasurable.integral_kernel_prod_right'
          (κ := eta F q t)).aestronglyMeasurable
    _ = _ := by
        refine integral_congr_ae (ae_of_all _ fun ω => ?_)
        simp only
        rw [eta, ProbabilityTheory.integral_compProd (f := fun z => G (g ω, z))
          (Integrable.of_bound (hG.comp measurable_prodMk_left).aestronglyMeasurable M
            (ae_of_all _ fun z => hGb _))]
        simp only [Kernel.comap_apply, hσt, G, g]

lemma herding [TopologicalSpace A] [OpensMeasurableSpace A] [MeasurableSingletonClass A]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (φ : A → ℝ) (hφc : Continuous φ) (hφ0 : ∀ a, 0 ≤ φ a) (hφ1 : ∀ a, φ a ≤ 1)
    (a0 a1 : A) (ha0 : φ a0 = 0) (ha1 : φ a1 = 1)
    (g : Ω → ℝ) (hg : Measurable g) (M : ℝ) (hM : ∀ ω, |g ω| ≤ M)
    (hdev : ∀ ψ : S → ℝ, Measurable ψ → (∀ s, 0 ≤ ψ s) → (∀ s, ψ s ≤ 1) →
      ∫ x, ψ x.2 * g x.1 ∂(μ ⊗ₘ F) ≤ 0)
    (hpos : 0 < μ {ω | 0 < g ω}) :
    InU (fun a ω => φ a * g ω) ∧ ¬ AsymptoticLearning μ F (fun a ω => φ a * g ω) := by
  set u : A → Ω → ℝ := fun a ω => φ a * g ω with hu_def
  have hφm : Measurable φ := hφc.measurable
  have hu : Measurable (Function.uncurry u) :=
    (hφm.comp measurable_fst).mul (hg.comp measurable_snd)
  have hub : ∀ a ω, |u a ω| ≤ M := by
    intro a ω
    simp only [u, abs_mul, abs_of_nonneg (hφ0 a)]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hφ1 a)).trans (hM ω)
  refine ⟨⟨hu, ⟨M, hub⟩, fun ω => hφc.mul continuous_const⟩, ?_⟩
  intro hAL
  set p0 := constProfile (S := S) a0
  have hact0 : ∀ᵐ x ∂(playMeasure μ F p0), ∀ t, action x t = a0 :=
    ae_all_iff.2 fun t => actDirac μ F p0 t a0 rfl
  have hpay0 : ∀ t, ∫ x, u (action x t) (state x) ∂(playMeasure μ F p0) = 0 := by
    intro t
    apply integral_eq_zero_of_ae
    filter_upwards [hact0] with x hx
    simp [u, hx t, ha0]
  have hPBE : IsPBE μ F u p0 := by
    intro t τ _
    rw [hpay0 t, devPayoff μ F a0 t τ u hu M hub]
    let κ' : Kernel S A := τ.comap (fun s => ((fun _ => a0 : Fin t → A), s)) (by fun_prop)
    let ψ : S → ℝ := fun s => ∫ a, φ a ∂(κ' s)
    have hψm : Measurable ψ := (hφm.stronglyMeasurable.integral_kernel (κ := κ')).measurable
    have hψ0 : ∀ s, 0 ≤ ψ s := fun s => integral_nonneg hφ0
    have hψ1 : ∀ s, ψ s ≤ 1 := by
      intro s
      calc ψ s ≤ ∫ _a, (1 : ℝ) ∂(κ' s) :=
            integral_mono (Integrable.of_bound hφm.aestronglyMeasurable 1
              (ae_of_all _ fun a => by
                rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 a)]; exact hφ1 a))
              (integrable_const 1) hφ1
        _ = 1 := by simp
    have hin : ∀ ω s, ∫ a, u a ω ∂(τ ((fun _ => a0), s)) = ψ s * g ω := by
      intro ω s
      simp only [u, ψ, κ', Kernel.comap_apply]
      exact integral_mul_const _ _
    simp_rw [hin]
    have hint : Integrable (fun x : Ω × S => ψ x.2 * g x.1) (μ ⊗ₘ F) := by
      refine Integrable.of_bound ((hψm.comp measurable_snd).mul
        (hg.comp measurable_fst)).aestronglyMeasurable M (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψ0 _)]
      exact (mul_le_of_le_one_left (abs_nonneg _) (hψ1 _)).trans (hM _)
    rw [← Measure.integral_compProd hint]
    exact hdev ψ hψm hψ0 hψ1
  have hconv := hAL p0 hPBE
  have hle : ∀ᵐ x ∂(playMeasure μ F p0), g (state x) ≤ 0 := by
    filter_upwards [hconv, hact0] with x hx ha
    have h0 : (fun t => u (action x t) (state x)) = fun _ => (0 : ℝ) := by
      funext t; simp [u, ha t, ha0]
    rw [h0] at hx
    have hO : maxPayoff u (state x) = 0 := tendsto_nhds_unique hx tendsto_const_nhds
    have hbdd : BddAbove (Set.range fun a => u a (state x)) :=
      ⟨M, by rintro _ ⟨a, rfl⟩; exact (le_abs_self _).trans (hub a _)⟩
    have := le_ciSup hbdd a1
    rw [← maxPayoff, hO] at this
    simpa [u, ha1] using this
  have hmeas : MeasurableSet {ω | 0 < g ω} := measurableSet_lt measurable_const hg
  have : μ {ω | 0 < g ω} = 0 := by
    rw [← stateLaw μ F p0, Measure.map_apply measurable_state hmeas]
    rw [ae_iff] at hle
    simpa [not_le] using hle
  exact hpos.ne' this

lemma postIdentity [StandardBorelSpace Ω] [Nonempty Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Kernel Ω S) [IsMarkovKernel F]
    (E : Set Ω) (hE : MeasurableSet E) (ψ : S → ℝ) (hψ : Measurable ψ)
    (hψb : ∀ s, |ψ s| ≤ 1) (α β : ℝ) :
    ∫ x, ψ x.2 * (α * E.indicator 1 x.1 + β) ∂(μ ⊗ₘ F) =
      ∫ s, ψ s * (α * privPost μ F E s + β) ∂(signalLaw μ F) := by
  have hswap : (μ ⊗ₘ F) = ((F ∘ₘ μ) ⊗ₘ F†μ).map Prod.swap := by
    rw [compProd_posterior_eq_map_swap, Measure.map_map measurable_swap measurable_swap]
    simp
  set f : Ω × S → ℝ := fun x => ψ x.2 * (α * E.indicator 1 x.1 + β) with hf_def
  have hind : Measurable (E.indicator (1 : Ω → ℝ)) := measurable_one.indicator hE
  have hfm : Measurable f :=
    (hψ.comp measurable_snd).mul
      ((measurable_const.mul (hind.comp measurable_fst)).add measurable_const)
  have hfb : ∀ x, ‖f x‖ ≤ |α| + |β| := by
    intro x
    rw [Real.norm_eq_abs, hf_def]
    simp only
    rw [abs_mul]
    have h1 : |α * E.indicator 1 x.1 + β| ≤ |α| + |β| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul]
      gcongr
      by_cases hx : x.1 ∈ E <;> simp [hx]
    calc |ψ x.2| * |α * E.indicator 1 x.1 + β| ≤ 1 * (|α| + |β|) :=
          mul_le_mul (hψb _) h1 (abs_nonneg _) zero_le_one
      _ = |α| + |β| := one_mul _
  rw [hswap, integral_map measurable_swap.aemeasurable hfm.aestronglyMeasurable,
    Measure.integral_compProd (f := fun x => f x.swap)
      (Integrable.of_bound (hfm.comp measurable_swap).aestronglyMeasurable
      (|α| + |β|) (ae_of_all _ fun x => hfb _))]
  unfold signalLaw
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  simp only [Prod.swap, hf_def]
  have hI1 : Integrable (fun ω => α * E.indicator 1 ω) ((F†μ) s) :=
    Integrable.of_bound (measurable_const.mul hind).aestronglyMeasurable |α|
      (ae_of_all _ fun ω => by by_cases h : ω ∈ E <;> simp [h])
  rw [integral_const_mul, integral_add hI1 (integrable_const β), integral_const_mul,
    integral_indicator_one hE]
  simp [privPost, measureReal_def]

end SSLNecAux

open SeqSocialLearning.Adequate SSLNecAux

theorem solution {Ω A S : Type*}
    [MetricSpace Ω] [CompleteSpace Ω] [TopologicalSpace.SeparableSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] [Nonempty Ω]
    [MetricSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
    [MeasurableSpace S] [StandardBorelSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (hF : Standing F) :
    ¬ TotallyUnbounded μ F → ∃ u : A → Ω → ℝ, InU u ∧ ¬ AsymptoticLearning μ F u := by
  intro hTU
  unfold TotallyUnbounded at hTU
  push Not at hTU
  obtain ⟨E, hE, hE0, hE1, hnot⟩ := hTU
  unfold UnboundedWrt at hnot
  push Not at hnot
  obtain ⟨ε, hε, hεE⟩ := hnot
  obtain ⟨a0, a1, ha01⟩ := exists_pair_ne A
  have hd : 0 < dist a1 a0 := dist_pos.2 ha01.symm
  set φ : A → ℝ := fun a => min 1 (dist a a0 / dist a1 a0) with hφ_def
  have hφc : Continuous φ :=
    continuous_const.min ((continuous_id.dist continuous_const).div_const _)
  have hφ0 : ∀ a, 0 ≤ φ a := fun a => le_min zero_le_one (div_nonneg dist_nonneg dist_nonneg)
  have hφ1 : ∀ a, φ a ≤ 1 := fun a => min_le_left _ _
  have ha0 : φ a0 = 0 := by simp [φ]
  have ha1 : φ a1 = 1 := by simp [φ, div_self hd.ne']
  have hind : Measurable (E.indicator (1 : Ω → ℝ)) := measurable_one.indicator hE
  -- general recipe with `g = α · 1_E + β`
  have key : ∀ α β : ℝ,
      (∀ᵐ s ∂(signalLaw μ F), α * privPost μ F E s + β ≤ 0) →
      0 < μ {ω | 0 < α * E.indicator 1 ω + β} →
      ∃ u : A → Ω → ℝ, InU u ∧ ¬ AsymptoticLearning μ F u := by
    intro α β hae hpos
    refine ⟨_, herding μ F φ hφc hφ0 hφ1 a0 a1 ha0 ha1
      (fun ω => α * E.indicator 1 ω + β) ((measurable_const.mul hind).add measurable_const)
      (|α| + |β|) ?_ ?_ hpos⟩
    · intro ω
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul]
      gcongr
      by_cases hx : ω ∈ E <;> simp [hx]
    · intro ψ hψ hψ0 hψ1
      have hψb : ∀ s, |ψ s| ≤ 1 := fun s => by rw [abs_of_nonneg (hψ0 s)]; exact hψ1 s
      rw [postIdentity μ F E hE ψ hψ hψb α β]
      apply integral_nonpos_of_ae
      filter_upwards [hae] with s hs
      exact mul_nonpos_of_nonneg_of_nonpos (hψ0 s) hs
  have hmeasPost : Measurable (privPost μ F E) := by
    unfold privPost
    exact (Kernel.measurable_coe _ hE).ennreal_toReal
  by_cases h1 : signalLaw μ F {s | privPost μ F E s < ε} = 0
  · -- the posterior of `E` is a.s. at least `ε`: everybody herds on "not E"
    refine key (-1) (ε / 2) ?_ ?_
    · have : ∀ᵐ s ∂(signalLaw μ F), ¬ privPost μ F E s < ε := by
        rw [ae_iff]; simpa using h1
      filter_upwards [this] with s hs
      push Not at hs
      linarith
    · have hsub : Eᶜ ⊆ {ω | 0 < (-1) * E.indicator 1 ω + ε / 2} := by
        intro ω hω
        simp only [Set.mem_ofPred_eq, Set.indicator_of_notMem hω]
        linarith
      refine lt_of_lt_of_le ?_ (measure_mono hsub)
      rw [prob_compl_eq_one_sub hE]
      exact tsub_pos_of_lt hE1
  · have h2 : signalLaw μ F {s | 1 - ε < privPost μ F E s} = 0 :=
      le_antisymm (hεE (pos_iff_ne_zero.2 h1)) zero_le
    refine key 1 (-(1 - ε / 2)) ?_ ?_
    · have : ∀ᵐ s ∂(signalLaw μ F), ¬ 1 - ε < privPost μ F E s := by
        rw [ae_iff]; simpa using h2
      filter_upwards [this] with s hs
      push Not at hs
      linarith
    · have hsub : E ⊆ {ω | 0 < 1 * E.indicator 1 ω + -(1 - ε / 2)} := by
        intro ω hω
        simp only [Set.mem_ofPred_eq, Set.indicator_of_mem hω, Pi.one_apply]
        linarith
      exact lt_of_lt_of_le hE0 (measure_mono hsub)
