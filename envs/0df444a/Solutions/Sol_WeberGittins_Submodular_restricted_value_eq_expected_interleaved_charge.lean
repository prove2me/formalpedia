-- Prove2me | solution 1 for WeberGittins.Submodular.restricted_value_eq_expected_interleaved_charge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-20T00:24:06.560693+00:00
-- url     : https://prove2.me/submissions/c587d74c-2eb0-46fc-b6ce-17b69526c14e

import Mathlib
import Definitions.Def_GittinsPrevailingChargeValue
import Definitions.Def_WeberGittins_Submodular_Model
import Definitions.Def_WeberGittins_Submodular_PartialInterleavedSum
import Theorems.Thm_BanditAlgorithm_gittins_finite_prevailing_charge_accounting
import Theorems.Thm_BanditAlgorithm_gittins_finite_prevailing_charge_interleaving
import Theorems.Thm_BanditAlgorithm_tendsto_gittins_terminal_retirement_potential_zero
import Theorems.Thm_BanditAlgorithm_summable_discounted_markovBanditRoundReward


set_option autoImplicit false

open MeasureTheory ProbabilityTheory ENNReal Finset Preorder

namespace G6cb

open BanditAlgorithm

variable {S : Type*} [MeasurableSpace S]

lemma chain_eq (P : Kernel S S) [IsMarkovKernel P] (x : S) :
    markovChainMeasure P x = Kernel.traj (markovChainStep P) 0 (fun _ => x) := by
  have h0 : (MeasurableEquiv.piUnique (fun _ : Iic 0 => S)).symm x = fun _ => x := by
    funext i
    have hi : i = default := Subsingleton.elim _ _
    subst hi; rfl
  rw [markovChainMeasure, Kernel.trajMeasure, Measure.map_dirac' (MeasurableEquiv.measurable _), h0,
    Measure.dirac_bind (Kernel.measurable _)]

instance chain_prob (P : Kernel S S) [IsMarkovKernel P] (x : S) :
    IsProbabilityMeasure (markovChainMeasure P x) := by
  rw [chain_eq]; infer_instance

lemma step_apply (P : Kernel S S) (m : ℕ) (z : Π _i : Iic m, S) :
    markovChainStep P m z = P (z ⟨m, mem_Iic.2 le_rfl⟩) := by
  rw [markovChainStep, Kernel.comap_apply]

lemma markov_step0 (P : Kernel S S) [IsMarkovKernel P] (x : S) (m : ℕ)
    (φ : (Π _i : Iic m, S) × S → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ ω, φ (frestrictLe m ω, ω (m+1)) ∂(markovChainMeasure P x) =
      ∫⁻ ω, ∫⁻ y, φ (frestrictLe m ω, y) ∂(P (ω m)) ∂(markovChainMeasure P x) := by
  rw [chain_eq]
  have h1 := Kernel.partialTraj_compProd_eq_map_traj (X := fun _ => S) (κ := markovChainStep P)
    (Nat.zero_le m) (x₀ := fun _ => x)
  have h2 := Kernel.traj_map_frestrictLe (X := fun _ => S) (κ := markovChainStep P) 0 m
  rw [← lintegral_map hφ (by fun_prop), ← h1, Measure.lintegral_compProd hφ]
  simp_rw [step_apply]
  have hF : Measurable (fun z : Π _i : Iic m, S => ∫⁻ y, φ (z, y) ∂(P (z ⟨m, mem_Iic.2 le_rfl⟩))) := by
    have := Measurable.lintegral_kernel_prod_right' (κ := markovChainStep P m) hφ
    simpa only [step_apply] using this
  rw [← h2, Kernel.map_apply _ (measurable_frestrictLe m), lintegral_map hF (measurable_frestrictLe m)]
  rfl

/-- one-step Markov property, general dependence form. -/
lemma markov_step (P : Kernel S S) [IsMarkovKernel P] (x : S) (m : ℕ)
    (Φ : (ℕ → S) → S → ℝ≥0∞) (hΦ : Measurable (Function.uncurry Φ))
    (hdep : ∀ ω ω' y, (∀ v ≤ m, ω v = ω' v) → Φ ω y = Φ ω' y) :
    ∫⁻ ω, Φ ω (ω (m+1)) ∂(markovChainMeasure P x) =
      ∫⁻ ω, ∫⁻ y, Φ ω y ∂(P (ω m)) ∂(markovChainMeasure P x) := by
  let ext : (Π _i : Iic m, S) → ℕ → S := fun z v => z ⟨min v m, mem_Iic.2 (min_le_right _ _)⟩
  have hext : Measurable ext := by
    refine measurable_pi_lambda _ (fun v => measurable_pi_apply _)
  have hre : ∀ ω : ℕ → S, ∀ v ≤ m, ext (frestrictLe m ω) v = ω v := by
    intro ω v hv
    simp [ext, frestrictLe_apply, min_eq_left hv]
  have key := markov_step0 P x m (fun p => Φ (ext p.1) p.2)
    (hΦ.comp ((hext.comp measurable_fst).prodMk measurable_snd))
  have e1 : ∀ ω y, Φ (ext (frestrictLe m ω)) y = Φ ω y := fun ω y => hdep _ _ y (hre ω)
  simp only [e1] at key
  exact key

lemma ae_zero [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P] (x : S) :
    ∀ᵐ ω ∂(markovChainMeasure P x), ω 0 = x := by
  rw [chain_eq]
  have h2 := Kernel.traj_map_frestrictLe (X := fun _ => S) (κ := markovChainStep P) 0 0
  have hm : (Kernel.traj (markovChainStep P) 0 (fun _ => x)).map (frestrictLe (π := fun _ => S) 0) =
      Measure.dirac (fun _ : Iic 0 => x) := by
    rw [← Kernel.map_apply _ (measurable_frestrictLe 0), h2, Kernel.partialTraj_self, Kernel.id_apply]
  have : ∀ᵐ z ∂(Measure.dirac (fun _ : Iic 0 => x)), z ⟨0, mem_Iic.2 le_rfl⟩ = x := by
    rw [ae_dirac_eq]; exact Filter.eventually_pure.2 rfl
  rw [← hm] at this
  exact ae_of_ae_map (measurable_frestrictLe 0).aemeasurable this

/-- one-step transition operator on nonnegative functions -/
noncomputable def Pe (P : Kernel S S) (h : S → ℝ≥0∞) (y : S) : ℝ≥0∞ := ∫⁻ z, h z ∂P y

lemma Pe_meas (P : Kernel S S) [IsMarkovKernel P] {h : S → ℝ≥0∞} (hh : Measurable h) :
    Measurable (Pe P h) := hh.lintegral_kernel

lemma Pe_iter_meas (P : Kernel S S) [IsMarkovKernel P] {h : S → ℝ≥0∞} (hh : Measurable h) (t : ℕ) :
    Measurable ((Pe P)^[t] h) := by
  induction t generalizing h with
  | zero => exact hh
  | succ t ih => rw [Function.iterate_succ_apply]; exact ih (Pe_meas P hh)

lemma shift_iter (P : Kernel S S) [IsMarkovKernel P] (x : S) {h : S → ℝ≥0∞} (hh : Measurable h)
    (m t : ℕ) :
    ∫⁻ ω, h (ω (m + t)) ∂(markovChainMeasure P x) =
      ∫⁻ ω, ((Pe P)^[t] h) (ω m) ∂(markovChainMeasure P x) := by
  induction t generalizing h with
  | zero => rfl
  | succ t ih =>
    have e1 := markov_step P x (m + t) (fun _ y => h y) (hh.comp measurable_snd)
      (fun _ _ _ _ => rfl)
    rw [show m + (t + 1) = m + t + 1 by omega, e1, Function.iterate_succ_apply]
    exact ih (Pe_meas P hh)

lemma eval_iter [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P] (x : S)
    {h : S → ℝ≥0∞} (hh : Measurable h) (t : ℕ) :
    ∫⁻ ω, h (ω t) ∂(markovChainMeasure P x) = ((Pe P)^[t] h) x := by
  have := shift_iter P x hh 0 t
  rw [zero_add] at this
  rw [this, lintegral_congr_ae ((ae_zero P x).mono fun ω hω => by rw [hω]), lintegral_const,
    measure_univ, mul_one]

/-- Markov step for arm `b` of a product of chains. -/
lemma stack_step {k : ℕ} (P : Kernel S S) [IsMarkovKernel P] (x : Fin k → S) (b : Fin k) (m : ℕ)
    (Φ : (Fin k → ℕ → S) → S → ℝ≥0∞) (hΦ : Measurable (Function.uncurry Φ))
    (hdep : ∀ ω ω' y, (∀ v ≤ m, ω b v = ω' b v) → (∀ i, i ≠ b → ω i = ω' i) → Φ ω y = Φ ω' y) :
    ∫⁻ ω, Φ ω (ω b (m+1)) ∂(Measure.pi (fun i => markovChainMeasure P (x i))) =
      ∫⁻ ω, ∫⁻ y, Φ ω y ∂(P (ω b m)) ∂(Measure.pi (fun i => markovChainMeasure P (x i))) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := b.isLt; omega⟩
  set μ : Fin (n+1) → Measure (ℕ → S) := fun i => markovChainMeasure P (x i) with hμ
  have hmp := measurePreserving_piFinSuccAbove μ b
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℕ → S) b with he
  have hmap : Measure.pi μ = ((μ b).prod (Measure.pi fun j => μ (b.succAbove j))).map e.symm := by
    rw [← hmp.map_eq, Measure.map_map e.symm.measurable e.measurable]
    simp
  have F1m : Measurable (fun ω : Fin (n+1) → ℕ → S => Φ ω (ω b (m+1))) :=
    hΦ.comp (measurable_id.prodMk ((measurable_pi_apply _).comp (measurable_pi_apply b)))
  have F2m : Measurable (fun ω : Fin (n+1) → ℕ → S => ∫⁻ y, Φ ω y ∂(P (ω b m))) := by
    have := Measurable.lintegral_kernel_prod_right' (κ := P.comap (fun ω : Fin (n+1) → ℕ → S => ω b m)
      ((measurable_pi_apply _).comp (measurable_pi_apply b))) hΦ
    simpa only [Kernel.comap_apply, Function.uncurry_apply_pair] using this
  rw [hmap, lintegral_map F1m e.symm.measurable, lintegral_map F2m e.symm.measurable,
    lintegral_prod_symm (fun a => Φ (e.symm a) (e.symm a b (m + 1)))
      (F1m.comp e.symm.measurable).aemeasurable,
    lintegral_prod_symm (fun a => ∫⁻ y, Φ (e.symm a) y ∂P (e.symm a b m))
      (F2m.comp e.symm.measurable).aemeasurable]
  refine lintegral_congr fun z => ?_
  have hsymm : ∀ w : ℕ → S, e.symm (w, z) = Fin.insertNth (α := fun _ => ℕ → S) b w z := fun w => rfl
  simp only [hsymm, Fin.insertNth_apply_same]
  refine markov_step P (x b) m (fun w y => Φ (Fin.insertNth (α := fun _ => ℕ → S) b w z) y) ?_ ?_
  · have hins : Measurable (fun w : ℕ → S => Fin.insertNth (α := fun _ => ℕ → S) b w z) :=
      e.symm.measurable.comp (measurable_id.prodMk measurable_const)
    exact hΦ.comp ((hins.comp measurable_fst).prodMk measurable_snd)
  · intro w w' y hw
    apply hdep
    · simpa using hw
    · intro i hi
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
      simp

set_option linter.unusedSectionVars false

section Coupling
variable {k : ℕ}

def cnt {n : ℕ} (a : Fin n → Fin k) (i : Fin k) (t : ℕ) : ℕ :=
  ∑ s : Fin n, if (s : ℕ) < t ∧ a s = i then 1 else 0

def hist {n : ℕ} (a : Fin n → Fin k) (ω : Fin k → ℕ → S) (t : Fin n) :
    MarkovBanditHistory k S t :=
  ((fun u : Fin (t : ℕ) ↦ ((fun i ↦ ω i (cnt a i u)), a ⟨u, lt_trans u.isLt t.isLt⟩)),
    fun i ↦ ω i (cnt a i t))

def histN {n : ℕ} (a : Fin n → Fin k) (ω : Fin k → ℕ → S) : MarkovBanditHistory k S n :=
  ((fun u : Fin n ↦ ((fun i ↦ ω i (cnt a i u)), a u)), fun i ↦ ω i (cnt a i n))

noncomputable def lik {n : ℕ} (π : MarkovBanditPolicy k S) (a : Fin n → Fin k)
    (ω : Fin k → ℕ → S) : ℝ≥0∞ :=
  ∏ t : Fin n, (π.select t) (hist a ω t) {a t}

noncomputable def stack (P : Kernel S S) [IsMarkovKernel P] (x : Fin k → S) :
    Measure (Fin k → ℕ → S) :=
  Measure.pi (fun i => markovChainMeasure P (x i))

instance stack_prob (P : Kernel S S) [IsMarkovKernel P] (x : Fin k → S) :
    IsProbabilityMeasure (stack P x) := by
  unfold stack; infer_instance

lemma cnt_mono {n : ℕ} (a : Fin n → Fin k) (i : Fin k) {t t' : ℕ} (h : t ≤ t') :
    cnt a i t ≤ cnt a i t' := by
  unfold cnt
  apply Finset.sum_le_sum
  intro s _
  by_cases h1 : (s : ℕ) < t ∧ a s = i
  · rw [if_pos h1, if_pos ⟨lt_of_lt_of_le h1.1 h, h1.2⟩]
  · rw [if_neg h1]; exact Nat.zero_le _

lemma snoc_lt {n : ℕ} (a : Fin n → Fin k) (b : Fin k) (j : Fin (n+1)) (h : (j : ℕ) < n) :
    Fin.snoc (α := fun _ => Fin k) a b j = a ⟨j, h⟩ := by
  rw [Fin.snoc, dif_pos h]; rfl

lemma cnt_snoc_le {n : ℕ} (a : Fin n → Fin k) (b : Fin k) (i : Fin k) {t : ℕ} (ht : t ≤ n) :
    cnt (Fin.snoc (α := fun _ => Fin k) a b) i t = cnt a i t := by
  unfold cnt
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.val_castSucc, Fin.val_last]
  rw [if_neg (fun h => absurd h.1 (by omega)), add_zero]

lemma cnt_snoc_last {n : ℕ} (a : Fin n → Fin k) (b : Fin k) (i : Fin k) :
    cnt (Fin.snoc (α := fun _ => Fin k) a b) i (n+1) = cnt a i n + if b = i then 1 else 0 := by
  unfold cnt
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.val_castSucc, Fin.val_last, Fin.snoc_last]
  congr 1
  · refine Finset.sum_congr rfl fun s _ => ?_
    have h1 : (s : ℕ) < n := s.isLt
    have h2 : (s : ℕ) < n + 1 := by omega
    simp [h1, h2]
  · simp

lemma cnt_zero {n : ℕ} (a : Fin n → Fin k) (i : Fin k) : cnt a i 0 = 0 := by
  simp [cnt]

lemma hist_snoc_cast {n : ℕ} (a : Fin n → Fin k) (b : Fin k) (ω : Fin k → ℕ → S) (t : Fin n) :
    hist (Fin.snoc (α := fun _ => Fin k) a b) ω (Fin.castSucc t) = hist a ω t := by
  have ht : (t : ℕ) ≤ n := t.isLt.le
  unfold hist
  refine Prod.ext ?_ ?_
  · funext u
    have hu : (u : ℕ) < n := lt_trans u.isLt t.isLt
    refine Prod.ext ?_ ?_
    · funext i
      exact congrArg (ω i) (cnt_snoc_le a b i hu.le)
    · exact snoc_lt a b _ hu
  · funext i
    exact congrArg (ω i) (cnt_snoc_le a b i ht)

lemma hist_snoc_last {n : ℕ} (a : Fin n → Fin k) (b : Fin k) (ω : Fin k → ℕ → S) :
    hist (Fin.snoc (α := fun _ => Fin k) a b) ω (Fin.last n) = histN a ω := by
  unfold hist histN
  refine Prod.ext ?_ ?_
  · funext u
    have hu : (u : ℕ) < n := u.isLt
    refine Prod.ext ?_ ?_
    · funext i
      exact congrArg (ω i) (cnt_snoc_le a b i hu.le)
    · exact snoc_lt a b _ hu
  · funext i
    exact congrArg (ω i) (cnt_snoc_le a b i le_rfl)

lemma histN_snoc {n : ℕ} (a : Fin n → Fin k) (b : Fin k) (ω : Fin k → ℕ → S) :
    histN (Fin.snoc (α := fun _ => Fin k) a b) ω =
      (Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) (histN a ω).1 ((histN a ω).2, b),
        Function.update (histN a ω).2 b (ω b (cnt a b n + 1))) := by
  refine Prod.ext ?_ ?_
  · funext u
    induction u using Fin.lastCases with
    | last =>
      simp only [histN, Fin.snoc_last, Fin.val_last]
      refine Prod.ext ?_ rfl
      funext i
      exact congrArg (ω i) (cnt_snoc_le a b i le_rfl)
    | cast u' =>
      simp only [histN, Fin.snoc_castSucc, Fin.val_castSucc]
      refine Prod.ext ?_ rfl
      funext i
      exact congrArg (ω i) (cnt_snoc_le a b i u'.isLt.le)
  · funext i
    simp only [histN, cnt_snoc_last]
    by_cases hi : i = b
    · subst hi; simp
    · rw [Function.update_of_ne hi, if_neg (Ne.symm hi), add_zero]

lemma lik_snoc {n : ℕ} (π : MarkovBanditPolicy k S) (a : Fin n → Fin k) (b : Fin k)
    (ω : Fin k → ℕ → S) :
    lik π (Fin.snoc (α := fun _ => Fin k) a b) ω = lik π a ω * π.select n (histN a ω) {b} := by
  unfold lik
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun t _ => ?_
    rw [hist_snoc_cast, Fin.snoc_castSucc]
    rfl
  · rw [hist_snoc_last, Fin.snoc_last]
    rfl

lemma histN_meas {n : ℕ} (a : Fin n → Fin k) :
    Measurable (fun ω : Fin k → ℕ → S => histN a ω) := by
  unfold histN
  refine Measurable.prodMk ?_ ?_
  · refine measurable_pi_lambda _ fun u => Measurable.prodMk ?_ measurable_const
    exact measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp (measurable_pi_apply i)
  · exact measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp (measurable_pi_apply i)

lemma hist_meas {n : ℕ} (a : Fin n → Fin k) (t : Fin n) :
    Measurable (fun ω : Fin k → ℕ → S => hist a ω t) := by
  unfold hist
  refine Measurable.prodMk ?_ ?_
  · refine measurable_pi_lambda _ fun u => Measurable.prodMk ?_ measurable_const
    exact measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp (measurable_pi_apply i)
  · exact measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp (measurable_pi_apply i)

lemma lik_meas {n : ℕ} (π : MarkovBanditPolicy k S) (a : Fin n → Fin k) :
    Measurable (fun ω : Fin k → ℕ → S => lik π a ω) := by
  unfold lik
  exact Finset.measurable_prod _ fun t _ =>
    (Kernel.measurable_coe _ (measurableSet_singleton _)).comp (hist_meas a t)

lemma hist_dep {n : ℕ} (a : Fin n → Fin k) (ω ω' : Fin k → ℕ → S)
    (h : ∀ i v, v ≤ cnt a i n → ω i v = ω' i v) :
    histN a ω = histN a ω' ∧ ∀ t, hist a ω t = hist a ω' t := by
  have hc : ∀ i (u : ℕ), u ≤ n → ω i (cnt a i u) = ω' i (cnt a i u) :=
    fun i u hu => h i _ (cnt_mono a i hu)
  refine ⟨?_, fun t => ?_⟩
  · unfold histN
    congr 1
    · funext u; congr 1; funext i; exact hc i u u.isLt.le
    · funext i; exact hc i n le_rfl
  · unfold hist
    congr 1
    · funext u; congr 1; funext i; exact hc i u (by have := u.isLt; have := t.isLt; omega)
    · funext i; exact hc i t t.isLt.le

lemma lik_dep {n : ℕ} (π : MarkovBanditPolicy k S) (a : Fin n → Fin k) (ω ω' : Fin k → ℕ → S)
    (h : ∀ i v, v ≤ cnt a i n → ω i v = ω' i v) : lik π a ω = lik π a ω' := by
  unfold lik
  exact Finset.prod_congr rfl fun t _ => by rw [(hist_dep a ω ω' h).2 t]

lemma stack_ae_zero [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P]
    (x : Fin k → S) : ∀ᵐ ω ∂(stack P x), ∀ i, ω i 0 = x i := by
  rw [ae_all_iff]; intro i
  unfold stack
  exact (Measure.tendsto_eval_ae_ae (μ := fun i => markovChainMeasure P (x i)) (i := i)).eventually
    (ae_zero P (x i))

theorem coupling [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P]
    (π : MarkovBanditPolicy k S) (x : Fin k → S) (n : ℕ)
    (G : MarkovBanditHistory k S n → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ h, G h ∂(markovBanditMeasure P π x n) =
      ∑ a : Fin n → Fin k, ∫⁻ ω, lik π a ω * G (histN a ω) ∂(stack P x) := by
  induction n with
  | zero =>
    rw [markovBanditMeasure, lintegral_dirac' _ hG, Fintype.sum_unique]
    rw [lintegral_congr_ae ((stack_ae_zero P x).mono fun ω hω => ?_), lintegral_const,
      measure_univ, mul_one]
    have e1 : lik π (default : Fin 0 → Fin k) ω = 1 := by simp [lik]
    have e2 : histN (default : Fin 0 → Fin k) ω = ((fun t => t.elim0), x) := by
      refine Prod.ext ?_ ?_
      · funext u; exact u.elim0
      · funext i; simp [histN, cnt_zero, hω i]
    show lik π (default : Fin 0 → Fin k) ω * G (histN default ω) = G ((fun t => t.elim0), x)
    rw [e1, e2, one_mul]
  | succ n ih =>
    have hsn := measurable_markovBanditSnoc (S := S) (k := k) (n := n)
    rw [markovBanditMeasure, lintegral_map hG hsn]
    refine Eq.trans (Measure.lintegral_compProd (hG.comp hsn)) ?_
    let H : MarkovBanditHistory k S n → Fin k → S → ℝ≥0∞ := fun h b y =>
      G (Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) h.1 (h.2, b), Function.update h.2 b y)
    have hHm : ∀ b, Measurable (fun p : MarkovBanditHistory k S n × S => H p.1 b p.2) := fun b =>
      hG.comp (hsn.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))
    let G' : MarkovBanditHistory k S n → ℝ≥0∞ := fun h =>
      ∑ b : Fin k, π.select n h {b} * ∫⁻ y, H h b y ∂(P (h.2 b))
    have hIm : ∀ b, Measurable (fun h : MarkovBanditHistory k S n => ∫⁻ y, H h b y ∂(P (h.2 b))) := by
      intro b
      have := Measurable.lintegral_kernel_prod_right' (κ := P.comap
        (fun h : MarkovBanditHistory k S n => h.2 b) ((measurable_pi_apply b).comp measurable_snd)) (hHm b)
      simpa only [Kernel.comap_apply] using this
    have hG'm : Measurable G' := Finset.measurable_sum _ fun b _ =>
      (Kernel.measurable_coe _ (measurableSet_singleton b)).mul (hIm b)
    have hinner : ∀ h : MarkovBanditHistory k S n,
        ∫⁻ q, G (Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) h.1 (h.2, q.1),
          Function.update h.2 q.1 q.2) ∂(markovBanditStepKernel P π n h) = G' h := by
      intro h
      rw [markovBanditStepKernel, Kernel.lintegral_compProd _ _ _ ?_, lintegral_fintype]
      · refine Finset.sum_congr rfl fun b _ => ?_
        rw [Kernel.comap_apply, mul_comm]
      · exact hG.comp (hsn.comp (measurable_const.prodMk measurable_id))
    refine Eq.trans (lintegral_congr fun h => hinner h) ?_
    rw [ih G' hG'm]
    rw [← (Fin.snocEquiv (fun _ => Fin k)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [G', Finset.mul_sum]
    rw [lintegral_finsetSum _ fun b _ => ?_]
    · refine Finset.sum_congr rfl fun b _ => ?_
      simp only [Fin.snocEquiv, Equiv.coe_fn_mk, lik_snoc, histN_snoc]
      -- apply the stack Markov step for arm b at level cnt a b n
      have hΦ : Measurable (Function.uncurry fun (ω : Fin k → ℕ → S) (y : S) =>
          lik π a ω * π.select n (histN a ω) {b} * H (histN a ω) b y) := by
        refine ((lik_meas π a).comp measurable_fst |>.mul
          ((Kernel.measurable_coe _ (measurableSet_singleton b)).comp
            ((histN_meas a).comp measurable_fst))).mul ?_
        exact (hHm b).comp (((histN_meas a).comp measurable_fst).prodMk measurable_snd)
      have key := stack_step P x b (cnt a b n)
        (fun ω y => lik π a ω * π.select n (histN a ω) {b} * H (histN a ω) b y) hΦ
        (fun ω ω' y hb ho => by
          have hall : ∀ i v, v ≤ cnt a i n → ω i v = ω' i v := by
            intro i v hv
            by_cases hi : i = b
            · subst hi; exact hb v hv
            · rw [ho i hi]
          simp only [lik_dep π a ω ω' hall, (hist_dep a ω ω' hall).1])
      unfold stack
      refine Eq.trans ?_ key.symm
      refine lintegral_congr fun ω => ?_
      rw [lintegral_const_mul _ ?_, mul_assoc]
      · rfl
      · exact (hHm b).comp (measurable_const.prodMk measurable_id)
    · exact (lik_meas π a).mul (((Kernel.measurable_coe _ (measurableSet_singleton b)).comp
        (histN_meas a)).mul ((hIm b).comp (histN_meas a)))

end Coupling

section Assembly
variable {k : ℕ}

noncomputable def chg (g : S → ℝ) (ω : Fin k → ℕ → S) (i : Fin k) (u : ℕ) : ℝ :=
  (Finset.range (u + 1)).inf' ⟨0, Finset.mem_range.2 (Nat.zero_lt_succ u)⟩ (fun v ↦ g (ω i v))

lemma chg_zero (g : S → ℝ) (ω : Fin k → ℕ → S) (i : Fin k) : chg g ω i 0 = g (ω i 0) := by
  simp [chg]

lemma chg_succ (g : S → ℝ) (ω : Fin k → ℕ → S) (i : Fin k) (u : ℕ) :
    chg g ω i (u + 1) = min (chg g ω i u) (g (ω i (u + 1))) := by
  unfold chg
  apply le_antisymm
  · exact le_min (Finset.le_inf' _ _ fun v hv => Finset.inf'_le _
      (Finset.mem_range.2 (by rw [Finset.mem_range] at hv; omega)))
      (Finset.inf'_le _ (Finset.mem_range.2 (by omega)))
  · apply Finset.le_inf'
    intro v hv
    rw [Finset.mem_range] at hv
    rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | hv
    · exact (min_le_left _ _).trans (Finset.inf'_le _ (Finset.mem_range.2 hv))
    · subst hv; exact min_le_right _ _

lemma chg_le_last (g : S → ℝ) (ω : Fin k → ℕ → S) (i : Fin k) (u : ℕ) :
    chg g ω i u ≤ g (ω i u) :=
  Finset.inf'_le _ (Finset.mem_range.2 (Nat.lt_succ_self u))

lemma chg_meas {g : S → ℝ} (hg : Measurable g) (i : Fin k) (u : ℕ) :
    Measurable (fun ω : Fin k → ℕ → S => chg g ω i u) := by
  induction u with
  | zero =>
    simp only [chg_zero]; exact hg.comp ((measurable_pi_apply 0).comp (measurable_pi_apply i))
  | succ u ih =>
    simp only [chg_succ]
    exact ih.min (hg.comp ((measurable_pi_apply _).comp (measurable_pi_apply i)))

lemma chg_le (g : S → ℝ) (ω : Fin k → ℕ → S) (i : Fin k) (u : ℕ) : chg g ω i u ≤ g (ω i 0) := by
  induction u with
  | zero => rw [chg_zero]
  | succ u ih => rw [chg_succ]; exact (min_le_left _ _).trans ih

lemma chg_ge {g r : S → ℝ} (hrg : ∀ y, r y ≤ g y) (ω : Fin k → ℕ → S) (i : Fin k) (u : ℕ) :
    -∑ v ∈ Finset.range (u + 1), |r (ω i v)| ≤ chg g ω i u := by
  induction u with
  | zero => simp only [chg_zero, zero_add, Finset.sum_range_one]; exact (neg_abs_le _).trans (hrg _)
  | succ u ih =>
    rw [chg_succ, Finset.sum_range_succ]
    refine le_min ?_ ?_
    · have : 0 ≤ |r (ω i (u + 1))| := abs_nonneg _
      linarith
    · have := (neg_abs_le (r (ω i (u+1)))).trans (hrg _)
      have : 0 ≤ ∑ v ∈ Finset.range (u + 1), |r (ω i v)| :=
        Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith

lemma truncate_histN_snoc {n : ℕ} (a : Fin n → Fin k) (b : Fin k) (ω : Fin k → ℕ → S) :
    truncateMarkovBanditHistory (histN (Fin.snoc (α := fun _ => Fin k) a b) ω) = histN a ω := by
  rw [histN_snoc, truncateMarkovBanditHistory]
  simp only [Fin.init_snoc, Fin.snoc_last]

lemma chpc_histN (g : S → ℝ) (ω : Fin k → ℕ → S) (i : Fin k) (n : ℕ) :
    ∀ a : Fin n → Fin k,
      currentHistoryPrevailingCharge g n (histN a ω) i = chg g ω i (cnt a i n) := by
  induction n with
  | zero =>
    intro a
    simp only [currentHistoryPrevailingCharge, histN, cnt_zero, chg_zero]
  | succ n ih =>
    intro a'
    obtain ⟨a, b, rfl⟩ : ∃ (a : Fin n → Fin k) (b : Fin k),
        a' = Fin.snoc (α := fun _ => Fin k) a b :=
      ⟨Fin.init a', a' (Fin.last n), (Fin.snoc_init_self a').symm⟩
    rw [currentHistoryPrevailingCharge, truncate_histN_snoc, ih, cnt_snoc_last]
    have e2 : (histN (Fin.snoc (α := fun _ => Fin k) a b) ω).2 i =
        ω i (cnt a i n + if b = i then 1 else 0) := by
      simp only [histN, cnt_snoc_last]
    rw [e2]
    by_cases hb : b = i
    · rw [if_pos hb, chg_succ]
    · rw [if_neg hb, add_zero]
      exact min_eq_left (chg_le_last g ω i _)

lemma chpc_meas {g : S → ℝ} (hg : Measurable g) (n : ℕ) (i : Fin k) :
    Measurable (fun h : MarkovBanditHistory k S n => currentHistoryPrevailingCharge g n h i) := by
  induction n with
  | zero =>
    simp only [currentHistoryPrevailingCharge]
    exact hg.comp ((measurable_pi_apply i).comp measurable_snd)
  | succ n ih =>
    simp only [currentHistoryPrevailingCharge]
    have ht : Measurable (fun h : MarkovBanditHistory k S (n+1) => truncateMarkovBanditHistory h) := by
      unfold truncateMarkovBanditHistory
      refine Measurable.prodMk ?_ ?_
      · exact measurable_pi_lambda _ fun j => (measurable_pi_apply _).comp measurable_fst
      · exact measurable_fst.comp ((measurable_pi_apply _).comp measurable_fst)
    exact (ih.comp ht).min (hg.comp ((measurable_pi_apply i).comp measurable_snd))

lemma lik_le_one {n : ℕ} (π : MarkovBanditPolicy k S) (a : Fin n → Fin k) (ω : Fin k → ℕ → S) :
    lik π a ω ≤ 1 := by
  unfold lik
  exact Finset.prod_le_one' fun t _ => prob_le_one

lemma sum_sel (π : MarkovBanditPolicy k S) (n : ℕ) (h : MarkovBanditHistory k S n) :
    ∑ b : Fin k, ((π.select n) h {b}).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _), sum_measure_singleton, Finset.coe_univ,
    measure_univ, ENNReal.toReal_one]

lemma Lcomp [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P]
    (π : MarkovBanditPolicy k S) (x : Fin k → S) (n : ℕ)
    (f : MarkovBanditHistory k S n × Fin k → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ p, f (p.1, p.2.1) ∂((markovBanditMeasure P π x n).compProd (markovBanditStepKernel P π n)) =
      ∑ a : Fin n → Fin k, ∑ b : Fin k,
        ∫⁻ ω, (lik π a ω * π.select n (histN a ω) {b}) * f (histN a ω, b) ∂(stack P x) := by
  have hf2 : Measurable (fun p : MarkovBanditHistory k S n × (Fin k × S) => f (p.1, p.2.1)) :=
    hf.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  refine Eq.trans (Measure.lintegral_compProd hf2) ?_
  have hin : ∀ h, ∫⁻ q, f (h, q.1) ∂(markovBanditStepKernel P π n h) =
      ∑ b : Fin k, π.select n h {b} * f (h, b) := by
    intro h
    rw [markovBanditStepKernel, Kernel.lintegral_compProd _ _ _ ?_, lintegral_fintype]
    · refine Finset.sum_congr rfl fun b _ => ?_
      simp only [lintegral_const, measure_univ, mul_one]
      rw [mul_comm]
    · exact hf.comp (measurable_const.prodMk measurable_fst)
  refine Eq.trans (lintegral_congr fun h => hin h) ?_
  rw [coupling P π x n _ ?_]
  swap
  · exact Finset.measurable_sum _ fun b _ =>
      (Kernel.measurable_coe _ (measurableSet_singleton b)).mul
        (hf.comp (measurable_id.prodMk measurable_const))
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Finset.mul_sum]
  rw [lintegral_finsetSum _ fun b _ => ?_]
  · refine Finset.sum_congr rfl fun b _ => ?_
    refine lintegral_congr fun ω => ?_
    ring
  · exact (lik_meas π a).mul (((Kernel.measurable_coe _ (measurableSet_singleton b)).comp
      (histN_meas a)).mul (hf.comp ((histN_meas a).prodMk measurable_const)))

lemma ofReal_toReal_mul (w : ℝ≥0∞) (hw : w ≠ ⊤) (c : ℝ) :
    ENNReal.ofReal (w.toReal * c) = w * ENNReal.ofReal c := by
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hw]

lemma round_eq [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} {α : ℝ}
    (π : MarkovBanditPolicy k S) (x : Fin k → S) (n : ℕ)
    (hgm : Measurable (gittinsIndex P r α))
    (hci : ∀ i u, Integrable (fun ω => chg (gittinsIndex P r α) ω i u) (stack P x)) :
    markovBanditRoundPrevailingCharge P r α π x n =
      ∑ a : Fin n → Fin k, ∑ b : Fin k, ∫ ω, (lik π a ω * π.select n (histN a ω) {b}).toReal *
        chg (gittinsIndex P r α) ω b (cnt a b n) ∂(stack P x) := by
  set g := gittinsIndex P r α with hg
  have hFm : Measurable (fun p : MarkovBanditHistory k S n × Fin k =>
      currentHistoryPrevailingCharge g n p.1 p.2) :=
    measurable_from_prod_countable_left fun b => chpc_meas hgm n b
  have hw1 : ∀ (a : Fin n → Fin k) (b : Fin k) ω,
      lik π a ω * π.select n (histN a ω) {b} ≤ 1 :=
    fun a b ω => mul_le_one' (lik_le_one π a ω) prob_le_one
  have hwt : ∀ (a : Fin n → Fin k) (b : Fin k) ω, lik π a ω * π.select n (histN a ω) {b} ≠ ⊤ :=
    fun a b ω => ((hw1 a b ω).trans_lt one_lt_top).ne
  have hwm : ∀ (a : Fin n → Fin k) (b : Fin k),
      Measurable (fun ω => lik π a ω * π.select n (histN a ω) {b}) := fun a b =>
    (lik_meas π a).mul ((Kernel.measurable_coe _ (measurableSet_singleton b)).comp (histN_meas a))
  have L : ∀ φ : ℝ → ℝ, Measurable φ →
      ∫⁻ p, ENNReal.ofReal (φ (currentHistoryPrevailingCharge g n p.1 p.2.1))
        ∂((markovBanditMeasure P π x n).compProd (markovBanditStepKernel P π n)) =
        ∑ a : Fin n → Fin k, ∑ b : Fin k, ∫⁻ ω, (lik π a ω * π.select n (histN a ω) {b}) *
          ENNReal.ofReal (φ (chg g ω b (cnt a b n))) ∂(stack P x) := by
    intro φ hφ
    rw [Lcomp P π x n (fun p => ENNReal.ofReal (φ (currentHistoryPrevailingCharge g n p.1 p.2)))
      (ENNReal.measurable_ofReal.comp (hφ.comp hFm))]
    simp only [chpc_histN]
  have hfin : ∀ (a : Fin n → Fin k) (b : Fin k) (φ : ℝ → ℝ), (∀ t, φ t ≤ |t|) →
      ∫⁻ ω, (lik π a ω * π.select n (histN a ω) {b}) *
        ENNReal.ofReal (φ (chg g ω b (cnt a b n))) ∂(stack P x) ≠ ⊤ := by
    intro a b φ hφ
    refine ne_top_of_le_ne_top (hci b (cnt a b n)).hasFiniteIntegral.ne ?_
    refine lintegral_mono fun ω => ?_
    calc (lik π a ω * π.select n (histN a ω) {b}) * ENNReal.ofReal (φ (chg g ω b (cnt a b n)))
        ≤ 1 * ENNReal.ofReal |chg g ω b (cnt a b n)| :=
          mul_le_mul' (hw1 a b ω) (ENNReal.ofReal_le_ofReal (hφ _))
      _ = ‖chg g ω b (cnt a b n)‖ₑ := by rw [one_mul, Real.enorm_eq_ofReal_abs]
  have hI : Integrable (fun p : MarkovBanditHistory k S n × (Fin k × S) =>
      currentHistoryPrevailingCharge g n p.1 p.2.1)
      ((markovBanditMeasure P π x n).compProd (markovBanditStepKernel P π n)) := by
    refine ⟨(hFm.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simp only [Real.enorm_eq_ofReal_abs]
    rw [L abs measurable_abs]
    exact ENNReal.sum_lt_top.2 fun a _ => ENNReal.sum_lt_top.2 fun b _ =>
      (hfin a b abs fun t => le_rfl).lt_top
  rw [markovBanditRoundPrevailingCharge, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hI]
  have e1 := L id measurable_id
  have e2 := L (fun t => -t) measurable_neg
  simp only [id] at e1 e2
  have hA : ∀ (a : Fin n → Fin k) (b : Fin k), ∫⁻ ω, (lik π a ω * π.select n (histN a ω) {b}) *
      ENNReal.ofReal (chg g ω b (cnt a b n)) ∂(stack P x) ≠ ⊤ :=
    fun a b => hfin a b id fun t => le_abs_self t
  have hB : ∀ (a : Fin n → Fin k) (b : Fin k), ∫⁻ ω, (lik π a ω * π.select n (histN a ω) {b}) *
      ENNReal.ofReal (-chg g ω b (cnt a b n)) ∂(stack P x) ≠ ⊤ :=
    fun a b => hfin a b (fun t => -t) fun t => neg_le_abs t
  rw [e1, e2, ENNReal.toReal_sum (fun a _ => (ENNReal.sum_lt_top.2 fun b _ => (hA a b).lt_top).ne),
    ENNReal.toReal_sum (fun a _ => (ENNReal.sum_lt_top.2 fun b _ => (hB a b).lt_top).ne),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ENNReal.toReal_sum (fun b _ => hA a b), ENNReal.toReal_sum (fun b _ => hB a b),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hint2 : Integrable (fun ω => (lik π a ω * π.select n (histN a ω) {b}).toReal *
      chg g ω b (cnt a b n)) (stack P x) :=
    (hci b (cnt a b n)).bdd_mul (c := 1) (hwm a b).ennreal_toReal.aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hw1 a b ω))
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint2]
  congr 2
  · refine lintegral_congr fun ω => ?_
    rw [ofReal_toReal_mul _ (hwt a b ω)]
  · refine lintegral_congr fun ω => ?_
    rw [← mul_neg, ofReal_toReal_mul _ (hwt a b ω)]

noncomputable def val (g : S → ℝ) (α : ℝ) {n : ℕ} (a : Fin n → Fin k) (ω : Fin k → ℕ → S) : ℝ :=
  ∑ t : Fin n, α ^ (t : ℕ) * chg g ω (a t) (cnt a (a t) t)

lemma val_snoc (g : S → ℝ) (α : ℝ) {n : ℕ} (a : Fin n → Fin k) (b : Fin k) (ω : Fin k → ℕ → S) :
    val g α (Fin.snoc (α := fun _ => Fin k) a b) ω =
      val g α a ω + α ^ n * chg g ω b (cnt a b n) := by
  unfold val
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  congr 1
  · refine Finset.sum_congr rfl fun t _ => ?_
    rw [cnt_snoc_le a b _ t.isLt.le]
  · rw [cnt_snoc_le a b _ le_rfl]

theorem main_of_meas [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} {α : ℝ} (π : MarkovBanditPolicy k S) (x : Fin k → S)
    (hgm : Measurable (gittinsIndex P r α))
    (hci : ∀ i u, Integrable (fun ω => chg (gittinsIndex P r α) ω i u) (stack P x)) (N : ℕ) :
    markovBanditFinitePrevailingChargeValue P r α π x N =
      ∑ a : Fin N → Fin k,
        ∫ ω, val (gittinsIndex P r α) α a ω ∂((stack P x).withDensity (lik π a)) := by
  set g := gittinsIndex P r α with hg
  have hwd : ∀ {n : ℕ} (a : Fin n → Fin k) (f : (Fin k → ℕ → S) → ℝ),
      ∫ ω, f ω ∂((stack P x).withDensity (lik π a)) =
        ∫ ω, (lik π a ω).toReal * f ω ∂(stack P x) := by
    intro n a f
    rw [integral_withDensity_eq_integral_toReal_smul (lik_meas π a)
      (ae_of_all _ fun ω => (lik_le_one π a ω).trans_lt one_lt_top)]
    rfl
  have hbdd : ∀ (w : (Fin k → ℕ → S) → ℝ≥0∞), Measurable w → (∀ ω, w ω ≤ 1) →
      ∀ f, Integrable f (stack P x) →
      Integrable (fun ω => (w ω).toReal * f ω) (stack P x) := fun w hw h1 f hf =>
    hf.bdd_mul (c := 1) hw.ennreal_toReal.aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h1 ω))
  have hvi : ∀ {n : ℕ} (a : Fin n → Fin k), Integrable (fun ω => val g α a ω) (stack P x) :=
    fun a => integrable_finset_sum _ fun t _ => (hci _ _).const_mul _
  induction N with
  | zero => simp [markovBanditFinitePrevailingChargeValue, val]
  | succ N ih =>
    rw [markovBanditFinitePrevailingChargeValue, Finset.sum_range_succ,
      ← markovBanditFinitePrevailingChargeValue, ih, round_eq P π x N hgm hci]
    have hR : ∀ F : (Fin (N+1) → Fin k) → ℝ,
        ∑ a', F a' = ∑ a : Fin N → Fin k, ∑ b : Fin k, F (Fin.snoc (α := fun _ => Fin k) a b) := by
      intro F
      rw [← (Fin.snocEquiv (fun _ => Fin k)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
      rfl
    rw [hR, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hw1 : ∀ (b : Fin k) ω, lik π a ω * π.select N (histN a ω) {b} ≤ 1 :=
      fun b ω => mul_le_one' (lik_le_one π a ω) prob_le_one
    have hwm : ∀ (b : Fin k), Measurable (fun ω => lik π a ω * π.select N (histN a ω) {b}) :=
      fun b => (lik_meas π a).mul
        ((Kernel.measurable_coe _ (measurableSet_singleton b)).comp (histN_meas a))
    have e1 : ∀ b : Fin k, ∫ ω, (lik π (Fin.snoc (α := fun _ => Fin k) a b) ω).toReal *
          val g α (Fin.snoc (α := fun _ => Fin k) a b) ω ∂(stack P x) =
        ∫ ω, (lik π a ω * π.select N (histN a ω) {b}).toReal * val g α a ω ∂(stack P x) +
        α ^ N * ∫ ω, (lik π a ω * π.select N (histN a ω) {b}).toReal *
          chg g ω b (cnt a b N) ∂(stack P x) := by
      intro b
      simp only [lik_snoc, val_snoc]
      rw [← integral_const_mul]
      refine (integral_congr_ae (ae_of_all _ fun ω => ?_)).trans
        (integral_add (hbdd _ (hwm b) (hw1 b) _ (hvi a))
          ((hbdd _ (hwm b) (hw1 b) _ (hci b (cnt a b N))).const_mul (α ^ N)))
      ring
    have e2 : ∑ b : Fin k, ∫ ω, (lik π a ω * π.select N (histN a ω) {b}).toReal *
          val g α a ω ∂(stack P x) = ∫ ω, (lik π a ω).toReal * val g α a ω ∂(stack P x) := by
      refine ((integral_finset_sum _ fun b _ => hbdd _ (hwm b) (hw1 b) _ (hvi a)).symm).trans ?_
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      dsimp only
      rw [← Finset.sum_mul]
      congr 1
      simp only [ENNReal.toReal_mul, ← Finset.mul_sum, sum_sel, mul_one]
    simp only [hwd, e1]
    rw [Finset.sum_add_distrib, e2, Finset.mul_sum]

end Assembly

section GI
variable [MeasurableSingletonClass S]

lemma stop_meas {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) (n : ℕ) :
    MeasurableSet {ω : ℕ → S | τ ω ≤ n} :=
  Measurable.comap_le (measurable_pi_lambda (fun ω (i : Iic n) => ω i.1)
    fun i => measurable_pi_apply _) _ (hτ n)

lemma stop_lt_meas {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) (t : ℕ) :
    MeasurableSet {ω : ℕ → S | (t : ℕ∞) < τ ω} := by
  have := (stop_meas hτ t).compl
  simpa only [Set.compl_setOf, not_le] using this

lemma stop_dep {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) (n : ℕ) {ω ω' : ℕ → S}
    (h : ∀ v ≤ n, ω v = ω' v) : (τ ω ≤ n ↔ τ ω' ≤ n) := by
  obtain ⟨s, -, hs⟩ := hτ n
  have e : (fun (i : Iic n) => ω i.1) = (fun (i : Iic n) => ω' i.1) :=
    funext fun i => h i.1 (mem_Iic.1 i.2)
  have h1 : ω ∈ (fun ω : ℕ → S => fun (i : Iic n) => ω i.1) ⁻¹' s ↔
      ω' ∈ (fun ω : ℕ → S => fun (i : Iic n) => ω i.1) ⁻¹' s := by
    simp only [Set.mem_preimage, e]
  rw [hs] at h1
  exact h1

lemma disc_trunc (α : ℝ) (f : S → ℝ) (τ : (ℕ → S) → ℕ∞) (n : ℕ) (ω : ℕ → S) :
    discountedStoppedSum α f (fun ω => min (τ ω) n) ω =
      ∑ t ∈ Finset.range n, if (t : ℕ∞) < τ ω then α ^ t * f (ω t) else 0 := by
  unfold discountedStoppedSum
  rw [tsum_eq_sum (s := Finset.range n) (fun t ht => by
    have : ¬ ((t : ℕ∞) < n) := by
      rw [Finset.mem_range] at ht; exact_mod_cast ht
    simp only [lt_min_iff, this, and_false, if_false])]
  refine Finset.sum_congr rfl fun t ht => ?_
  have : (t : ℕ∞) < n := by exact_mod_cast Finset.mem_range.1 ht
  simp only [lt_min_iff, this, and_true]

lemma disc_fin (α : ℝ) (f : S → ℝ) {σ : (ℕ → S) → ℕ∞} {H : ℕ} (hH : ∀ ω, σ ω ≤ H) (ω : ℕ → S) :
    discountedStoppedSum α f σ ω =
      ∑ t ∈ Finset.range H, (if (t : ℕ∞) < σ ω then (1:ℝ) else 0) * α ^ t * f (ω t) := by
  have e : discountedStoppedSum α f σ ω = discountedStoppedSum α f (fun ω => min (σ ω) H) ω := by
    congr 1; exact funext fun ω => (min_eq_left (hH ω)).symm
  rw [e, disc_trunc]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> ring

lemma pw_disc {α : ℝ} (hα0 : 0 < α) (f : S → ℝ) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S)
    (hS : ∑' t, ENNReal.ofReal (α ^ t * |f (ω t)|) ≠ ⊤) :
    (∀ n : ℕ, ‖discountedStoppedSum α f (fun ω => min (τ ω) n) ω‖ ≤
        (∑' t, ENNReal.ofReal (α ^ t * |f (ω t)|)).toReal) ∧
    ‖discountedStoppedSum α f τ ω‖ ≤ (∑' t, ENNReal.ofReal (α ^ t * |f (ω t)|)).toReal ∧
    Filter.Tendsto (fun n : ℕ => discountedStoppedSum α f (fun ω => min (τ ω) n) ω) Filter.atTop
      (nhds (discountedStoppedSum α f τ ω)) := by
  have hnn : ∀ t : ℕ, 0 ≤ α ^ t * |f (ω t)| := fun t => mul_nonneg (pow_pos hα0 t).le (abs_nonneg _)
  have hs : Summable (fun t : ℕ => α ^ t * |f (ω t)|) :=
    (ENNReal.summable_toReal hS).congr fun t => ENNReal.toReal_ofReal (hnn t)
  have hT : (∑' t, ENNReal.ofReal (α ^ t * |f (ω t)|)).toReal = ∑' t, α ^ t * |f (ω t)| := by
    rw [ENNReal.tsum_toReal_eq (fun t => ENNReal.ofReal_ne_top)]
    exact tsum_congr fun t => ENNReal.toReal_ofReal (hnn t)
  let b : ℕ → ℝ := fun t => if (t : ℕ∞) < τ ω then α ^ t * f (ω t) else 0
  have hbn : ∀ t, ‖b t‖ ≤ α ^ t * |f (ω t)| := by
    intro t
    simp only [b]
    split_ifs
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos hα0 t)]
    · simpa using hnn t
  have hbs : Summable b := Summable.of_norm_bounded hs hbn
  have hbsn : Summable (fun t => ‖b t‖) := Summable.of_nonneg_of_le (fun t => norm_nonneg _) hbn hs
  rw [hT]
  refine ⟨fun n => ?_, ?_, ?_⟩
  · rw [disc_trunc]
    calc ‖∑ t ∈ Finset.range n, b t‖ ≤ ∑ t ∈ Finset.range n, α ^ t * |f (ω t)| :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => hbn t)
      _ ≤ ∑' t, α ^ t * |f (ω t)| := hs.sum_le_tsum _ (fun t _ => hnn t)
  · exact (norm_tsum_le_tsum_norm hbsn).trans (Summable.tsum_le_tsum hbn hbsn hs)
  · simp only [disc_trunc]
    exact hbs.hasSum.tendsto_sum_nat

lemma dct_disc (P : Kernel S S) [IsMarkovKernel P] {α : ℝ} (hα0 : 0 < α) {f : S → ℝ}
    (hf : Measurable f) (y : S)
    (hfin : ∫⁻ ω, ∑' t, ENNReal.ofReal (α ^ t * |f (ω t)|) ∂(markovChainMeasure P y) < ⊤)
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) :
    (∀ n : ℕ, Integrable (fun ω => discountedStoppedSum α f (fun ω => min (τ ω) n) ω)
      (markovChainMeasure P y)) ∧
    Filter.Tendsto (fun n : ℕ => ∫ ω, discountedStoppedSum α f (fun ω => min (τ ω) n) ω
      ∂(markovChainMeasure P y)) Filter.atTop
      (nhds (∫ ω, discountedStoppedSum α f τ ω ∂(markovChainMeasure P y))) ∧
    ‖∫ ω, discountedStoppedSum α f τ ω ∂(markovChainMeasure P y)‖ ≤
      ∫ ω, (∑' t, ENNReal.ofReal (α ^ t * |f (ω t)|)).toReal ∂(markovChainMeasure P y) := by
  have hSm : Measurable (fun ω : ℕ → S => ∑' t, ENNReal.ofReal (α ^ t * |f (ω t)|)) :=
    Measurable.ennreal_tsum fun t => ENNReal.measurable_ofReal.comp
      (measurable_const.mul (hf.comp (measurable_pi_apply t)).abs)
  have hB : Integrable (fun ω : ℕ → S => (∑' t, ENNReal.ofReal (α ^ t * |f (ω t)|)).toReal)
      (markovChainMeasure P y) :=
    integrable_toReal_of_lintegral_ne_top hSm.aemeasurable hfin.ne
  have hae : ∀ᵐ ω ∂(markovChainMeasure P y), ∑' t, ENNReal.ofReal (α ^ t * |f (ω t)|) ≠ ⊤ :=
    (ae_lt_top hSm hfin.ne).mono fun ω h => h.ne
  have hFm : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω => discountedStoppedSum α f (fun ω => min (τ ω) n) ω) (markovChainMeasure P y) := by
    intro n
    simp only [disc_trunc]
    refine (Finset.measurable_sum _ fun t _ => ?_).aestronglyMeasurable
    exact Measurable.ite (stop_lt_meas hτ t)
      (measurable_const.mul (hf.comp (measurable_pi_apply t))) measurable_const
  have hbd : ∀ n : ℕ, ∀ᵐ ω ∂(markovChainMeasure P y),
      ‖discountedStoppedSum α f (fun ω => min (τ ω) n) ω‖ ≤
        (∑' t, ENNReal.ofReal (α ^ t * |f (ω t)|)).toReal := fun n =>
    hae.mono fun ω h => (pw_disc hα0 f τ ω h).1 n
  refine ⟨fun n => hB.mono' (hFm n) (hbd n), ?_, ?_⟩
  · exact tendsto_integral_of_dominated_convergence _ hFm hB hbd
      (hae.mono fun ω h => (pw_disc hα0 f τ ω h).2.2)
  · exact norm_integral_le_of_norm_le hB (hae.mono fun ω h => (pw_disc hα0 f τ ω h).2.1)

lemma hfin_one (P : Kernel S S) [IsMarkovKernel P] {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (y : S) :
    ∫⁻ ω, ∑' t, ENNReal.ofReal (α ^ t * |(fun _ : S => (1:ℝ)) (ω t)|)
      ∂(markovChainMeasure P y) < ⊤ := by
  simp only [abs_one, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => (pow_pos hα0 t).le)
    (summable_geometric_of_lt_one hα0.le hα1), lintegral_const, measure_univ, mul_one]
  exact ENNReal.ofReal_lt_top

lemma D_ge_one (P : Kernel S S) [IsMarkovKernel P] {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (y : S)
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) (h1 : ∀ ω, 1 ≤ τ ω) :
    1 ≤ ∫ ω, discountedStoppedSum α (fun _ => 1) τ ω ∂(markovChainMeasure P y) := by
  obtain ⟨hI, hT, -⟩ := dct_disc P hα0 measurable_const y (hfin_one P hα0 hα1 y) hτ
  refine ge_of_tendsto hT (Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have hpt : ∀ ω, (1:ℝ) ≤ discountedStoppedSum α (fun _ => (1:ℝ)) (fun ω => min (τ ω) n) ω := by
    intro ω
    rw [disc_trunc]
    have h0 : (0:ℕ) ∈ Finset.range n := Finset.mem_range.2 (by omega)
    have hτ0 : ((0:ℕ) : ℕ∞) < τ ω := lt_of_lt_of_le (by norm_num) (h1 ω)
    calc (1:ℝ) = if ((0:ℕ):ℕ∞) < τ ω then α ^ 0 * 1 else 0 := by rw [if_pos hτ0]; simp
      _ ≤ ∑ t ∈ Finset.range n, if (t : ℕ∞) < τ ω then α ^ t * 1 else 0 :=
          Finset.single_le_sum (f := fun t : ℕ => if (t:ℕ∞) < τ ω then α ^ t * 1 else 0)
            (fun t _ => by split_ifs <;> positivity) h0
  calc (1:ℝ) = ∫ _ω, (1:ℝ) ∂(markovChainMeasure P y) := by simp
    _ ≤ _ := integral_mono (integrable_const 1) (hI n) hpt

lemma gi_bdd (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hint : DiscountedRewardIntegrable P r α) (y : S) :
    BddAbove {g : ℝ | ∃ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
      g = (∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P y) /
        (∫ ω, discountedStoppedSum α (fun _ ↦ 1) τ ω ∂markovChainMeasure P y)} := by
  refine ⟨∫ ω, (∑' t, ENNReal.ofReal (α ^ t * |r (ω t)|)).toReal ∂(markovChainMeasure P y), ?_⟩
  rintro _ ⟨τ, hτ, h1, rfl⟩
  have hD := D_ge_one P hα0 hα1 y hτ h1
  have hN := (dct_disc P hα0 hr y (hint y) hτ).2.2
  rw [Real.norm_eq_abs] at hN
  calc _ ≤ |∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P y| /
        (∫ ω, discountedStoppedSum α (fun _ ↦ 1) τ ω ∂markovChainMeasure P y) := by
        gcongr; exact le_abs_self _
    _ ≤ |∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P y| := div_le_self (abs_nonneg _) hD
    _ ≤ _ := hN

lemma r_le_gi (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hint : DiscountedRewardIntegrable P r α) (y : S) :
    r y ≤ gittinsIndex P r α y := by
  refine le_csSup (gi_bdd P hr hα0 hα1 hint y) ⟨fun _ => 1, fun n => MeasurableSet.const _,
    fun _ => le_rfl, ?_⟩
  have e : ∀ f : S → ℝ, ∀ ω : ℕ → S, discountedStoppedSum α f (fun _ => 1) ω = f (ω 0) := by
    intro f ω
    have hH1 : ∀ ω : ℕ → S, (fun _ : ℕ → S => (1:ℕ∞)) ω ≤ ((1:ℕ):ℕ∞) := fun _ => by simp
    rw [disc_fin α f hH1]
    simp
  have h1 : ∫ ω, r (ω 0) ∂(markovChainMeasure P y) = r y := by
    rw [integral_congr_ae (g := fun _ => r y) ((ae_zero P y).mono fun ω h => by simp only [h])]
    simp
  simp only [e, h1]
  simp

/-! ### finite-horizon Bellman values -/

lemma U_zero (P : Kernel S S) (r : S → ℝ) (α γ : ℝ) (z : S) :
    gittinsFiniteRetirementValue P r α γ 0 z = 0 := by
  rw [gittinsFiniteRetirementValue]

lemma U_succ (P : Kernel S S) (r : S → ℝ) (α γ : ℝ) (j : ℕ) (z : S) :
    gittinsFiniteRetirementValue P r α γ (j + 1) z =
      max 0 (r z - γ + α * ∫ w, gittinsFiniteRetirementValue P r α γ j w ∂P z) := by
  rw [gittinsFiniteRetirementValue]

lemma U_nonneg (P : Kernel S S) (r : S → ℝ) (α γ : ℝ) (j : ℕ) (z : S) :
    0 ≤ gittinsFiniteRetirementValue P r α γ j z := by
  cases j with
  | zero => rw [U_zero]
  | succ j => rw [U_succ]; exact le_max_left _ _

lemma U_meas (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r) (α γ : ℝ)
    (j : ℕ) : Measurable (gittinsFiniteRetirementValue P r α γ j) := by
  induction j with
  | zero =>
    have : gittinsFiniteRetirementValue P r α γ 0 = fun _ => 0 := funext fun z => U_zero P r α γ z
    rw [this]; exact measurable_const
  | succ j ih =>
    have hI : Measurable (fun z => ∫ w, gittinsFiniteRetirementValue P r α γ j w ∂P z) :=
      (ih.stronglyMeasurable.integral_kernel (κ := P)).measurable
    have : gittinsFiniteRetirementValue P r α γ (j + 1) = fun z =>
        max 0 (r z - γ + α * ∫ w, gittinsFiniteRetirementValue P r α γ j w ∂P z) :=
      funext fun z => U_succ P r α γ j z
    rw [this]
    exact measurable_const.max ((hr.sub measurable_const).add (measurable_const.mul hI))

lemma int_r (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hint : DiscountedRewardIntegrable P r α) (y : S) (s : ℕ) :
    Integrable (fun ω : ℕ → S => r (ω s)) (markovChainMeasure P y) := by
  have hm : Measurable (fun ω : ℕ → S => α ^ s * r (ω s)) :=
    measurable_const.mul (hr.comp (measurable_pi_apply s))
  have h1 : Integrable (fun ω : ℕ → S => α ^ s * r (ω s)) (markovChainMeasure P y) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    refine lt_of_le_of_lt (lintegral_mono fun ω => ?_) (hint y)
    rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_pos (pow_pos hα0 s)]
    exact ENNReal.le_tsum (f := fun t => ENNReal.ofReal (α ^ t * |r (ω t)|)) s
  have h2 := h1.const_mul (α ^ s)⁻¹
  refine h2.congr (ae_of_all _ fun ω => ?_)
  exact inv_mul_cancel_left₀ (pow_ne_zero s hα0.ne') _


lemma Pe_apply (P : Kernel S S) (F : S → ℝ≥0∞) (z : S) : Pe P F z = ∫⁻ w, F w ∂P z := rfl

lemma UB (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r) {α : ℝ} (hα0 : 0 < α)
    (γ : ℝ) (j : ℕ) :
    ∀ z, ENNReal.ofReal (gittinsFiniteRetirementValue P r α γ j z) ≤
      ∑ t ∈ Finset.range j, ENNReal.ofReal (α ^ t) *
        ((Pe P)^[t] (fun w => ENNReal.ofReal |r w - γ|)) z := by
  have hhm : Measurable (fun w => ENNReal.ofReal |r w - γ|) :=
    ENNReal.measurable_ofReal.comp (hr.sub measurable_const).abs
  have hm : ∀ t, Measurable ((Pe P)^[t] (fun w => ENNReal.ofReal |r w - γ|)) := fun t =>
    Pe_iter_meas P hhm t
  induction j with
  | zero => intro z; rw [U_zero]; simp
  | succ j ih =>
    intro z
    rw [U_succ]
    have hI0 : 0 ≤ ∫ w, gittinsFiniteRetirementValue P r α γ j w ∂P z :=
      integral_nonneg fun w => U_nonneg P r α γ j w
    have hle : max 0 (r z - γ + α * ∫ w, gittinsFiniteRetirementValue P r α γ j w ∂P z) ≤
        |r z - γ| + α * ∫ w, gittinsFiniteRetirementValue P r α γ j w ∂P z :=
      max_le (by positivity) (by linarith [le_abs_self (r z - γ)])
    have hOI : ENNReal.ofReal (∫ w, gittinsFiniteRetirementValue P r α γ j w ∂P z) ≤
        ∫⁻ w, ENNReal.ofReal (gittinsFiniteRetirementValue P r α γ j w) ∂P z := by
      have hab : ∀ w, ‖gittinsFiniteRetirementValue P r α γ j w‖ₑ =
          ENNReal.ofReal (gittinsFiniteRetirementValue P r α γ j w) := fun w => by
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (U_nonneg P r α γ j w)]
      calc ENNReal.ofReal (∫ w, gittinsFiniteRetirementValue P r α γ j w ∂P z)
          = ‖∫ w, gittinsFiniteRetirementValue P r α γ j w ∂P z‖ₑ := by
            rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hI0]
        _ ≤ ∫⁻ w, ‖gittinsFiniteRetirementValue P r α γ j w‖ₑ ∂P z :=
            enorm_integral_le_lintegral_enorm _
        _ = _ := by simp only [hab]
    calc ENNReal.ofReal (max 0 (r z - γ + α * ∫ w, gittinsFiniteRetirementValue P r α γ j w ∂P z))
        ≤ ENNReal.ofReal (|r z - γ| + α * ∫ w, gittinsFiniteRetirementValue P r α γ j w ∂P z) :=
          ENNReal.ofReal_le_ofReal hle
      _ = ENNReal.ofReal |r z - γ| + ENNReal.ofReal α *
            ENNReal.ofReal (∫ w, gittinsFiniteRetirementValue P r α γ j w ∂P z) := by
          rw [ENNReal.ofReal_add (abs_nonneg _) (mul_nonneg hα0.le hI0), ENNReal.ofReal_mul hα0.le]
      _ ≤ ENNReal.ofReal |r z - γ| + ENNReal.ofReal α *
            ∫⁻ w, ENNReal.ofReal (gittinsFiniteRetirementValue P r α γ j w) ∂P z := by
          gcongr
      _ ≤ ENNReal.ofReal |r z - γ| + ENNReal.ofReal α *
            ∫⁻ w, ∑ t ∈ Finset.range j, ENNReal.ofReal (α ^ t) *
              ((Pe P)^[t] (fun w => ENNReal.ofReal |r w - γ|)) w ∂P z := by
          gcongr with w; exact ih w
      _ = ∑ t ∈ Finset.range (j + 1), ENNReal.ofReal (α ^ t) *
            ((Pe P)^[t] (fun w => ENNReal.ofReal |r w - γ|)) z := by
          rw [lintegral_finsetSum _ fun t _ => (hm t).const_mul _, Finset.sum_range_succ',
            Finset.mul_sum, add_comm]
          congr 1
          · refine Finset.sum_congr rfl fun t _ => ?_
            rw [lintegral_const_mul _ (hm t), Function.iterate_succ_apply', Pe_apply, pow_succ,
              ENNReal.ofReal_mul (pow_pos hα0 t).le]
            ring
          · simp

lemma U_lint_fin (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hint : DiscountedRewardIntegrable P r α) (γ : ℝ) (y : S) (j m : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (gittinsFiniteRetirementValue P r α γ j (ω m))
      ∂(markovChainMeasure P y) < ⊤ := by
  have hhm : Measurable (fun w => ENNReal.ofReal |r w - γ|) :=
    ENNReal.measurable_ofReal.comp (hr.sub measurable_const).abs
  have hs : ∀ s, ∫⁻ ω, ENNReal.ofReal |r (ω s) - γ| ∂(markovChainMeasure P y) < ⊤ := by
    intro s
    have := ((int_r P hr hα0 hint y s).sub (integrable_const γ)).hasFiniteIntegral
    unfold HasFiniteIntegral at this
    simpa only [Real.enorm_eq_ofReal_abs, Pi.sub_apply] using this
  refine lt_of_le_of_lt (lintegral_mono fun ω => UB P hr hα0 γ j (ω m)) ?_
  rw [lintegral_finsetSum _ fun t _ => ?_]
  · refine ENNReal.sum_lt_top.2 fun t _ => ?_
    rw [lintegral_const_mul _ ?_, ← shift_iter P y hhm m t]
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hs (m + t))
    · exact (Pe_iter_meas P hhm t).comp (measurable_pi_apply m)
  · exact measurable_const.mul ((Pe_iter_meas P hhm t).comp (measurable_pi_apply m))

lemma iU (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hint : DiscountedRewardIntegrable P r α) (γ : ℝ) (y : S) (j m : ℕ) :
    Integrable (fun ω : ℕ → S => gittinsFiniteRetirementValue P r α γ j (ω m))
      (markovChainMeasure P y) := by
  refine ⟨((U_meas P hr α γ j).comp (measurable_pi_apply m)).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hab : ∀ z, |gittinsFiniteRetirementValue P r α γ j z| = gittinsFiniteRetirementValue P r α γ j z :=
    fun z => abs_of_nonneg (U_nonneg P r α γ j z)
  simp only [Real.enorm_eq_ofReal_abs, hab]
  exact U_lint_fin P hr hα0 hint γ y j m

lemma iUP (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hint : DiscountedRewardIntegrable P r α) (γ : ℝ) (j : ℕ) (z : S) :
    Integrable (gittinsFiniteRetirementValue P r α γ j) (P z) := by
  refine ⟨(U_meas P hr α γ j).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hab : ∀ z, |gittinsFiniteRetirementValue P r α γ j z| = gittinsFiniteRetirementValue P r α γ j z :=
    fun z => abs_of_nonneg (U_nonneg P r α γ j z)
  simp only [Real.enorm_eq_ofReal_abs, hab]
  have := U_lint_fin P hr hα0 hint γ z j 1
  rwa [eval_iter P z (h := fun w => ENNReal.ofReal (gittinsFiniteRetirementValue P r α γ j w))
    (ENNReal.measurable_ofReal.comp (U_meas P hr α γ j)) 1, Function.iterate_one,
    Pe_apply] at this

lemma iPU (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hint : DiscountedRewardIntegrable P r α) (γ : ℝ) (y : S) (j m : ℕ) :
    Integrable (fun ω : ℕ → S => ∫ w, gittinsFiniteRetirementValue P r α γ j w ∂P (ω m))
      (markovChainMeasure P y) := by
  have hI : Measurable (fun z => ∫ w, gittinsFiniteRetirementValue P r α γ j w ∂P z) :=
    ((U_meas P hr α γ j).stronglyMeasurable.integral_kernel (κ := P)).measurable
  refine ⟨(hI.comp (measurable_pi_apply m)).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hab : ∀ z, ‖∫ w, gittinsFiniteRetirementValue P r α γ j w ∂P z‖ₑ =
      ∫⁻ w, ENNReal.ofReal (gittinsFiniteRetirementValue P r α γ j w) ∂P z := by
    intro z
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (integral_nonneg fun w => U_nonneg P r α γ j w),
      ofReal_integral_eq_lintegral_ofReal (iUP P hr hα0 hint γ j z)
        (ae_of_all _ fun w => U_nonneg P r α γ j w)]
  simp only [hab]
  have key := markov_step P y m (fun _ w => ENNReal.ofReal (gittinsFiniteRetirementValue P r α γ j w))
    ((ENNReal.measurable_ofReal.comp (U_meas P hr α γ j)).comp measurable_snd) (fun _ _ _ _ => rfl)
  exact key.symm.trans_lt (U_lint_fin P hr hα0 hint γ y j (m+1))

lemma msb (P : Kernel S S) [IsMarkovKernel P] (y : S) (m : ℕ) {c : (ℕ → S) → ℝ}
    (hc : Measurable c) (hc0 : ∀ ω, 0 ≤ c ω) (hcd : ∀ ω ω', (∀ v ≤ m, ω v = ω' v) → c ω = c ω')
    {φ : S → ℝ} (hφ : Measurable φ) (hφ0 : ∀ z, 0 ≤ φ z) (hφP : ∀ z, Integrable φ (P z)) :
    ∫ ω, c ω * φ (ω (m+1)) ∂(markovChainMeasure P y) =
      ∫ ω, c ω * ∫ w, φ w ∂(P (ω m)) ∂(markovChainMeasure P y) := by
  have hI : Measurable (fun z => ∫ w, φ w ∂(P z)) :=
    (hφ.stronglyMeasurable.integral_kernel (κ := P)).measurable
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => mul_nonneg (hc0 ω) (hφ0 _))
      (hc.mul (hφ.comp (measurable_pi_apply _))).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun ω => mul_nonneg (hc0 ω) (integral_nonneg fun w => hφ0 w))
      (hc.mul (hI.comp (measurable_pi_apply _))).aestronglyMeasurable]
  congr 1
  have e : ∀ ω (a : ℝ), ENNReal.ofReal (c ω * a) = ENNReal.ofReal (c ω) * ENNReal.ofReal a :=
    fun ω a => ENNReal.ofReal_mul (hc0 ω)
  simp only [e]
  have key := markov_step P y m (fun ω z => ENNReal.ofReal (c ω) * ENNReal.ofReal (φ z))
    ((ENNReal.measurable_ofReal.comp (hc.comp measurable_fst)).mul
      (ENNReal.measurable_ofReal.comp (hφ.comp measurable_snd)))
    (fun ω ω' z h => by simp only [hcd ω ω' h])
  refine key.trans (lintegral_congr fun ω => ?_)
  rw [lintegral_const_mul _ ?_, ofReal_integral_eq_lintegral_ofReal (hφP _) (ae_of_all _ fun w => hφ0 w)]
  exact ENNReal.measurable_ofReal.comp hφ

lemma bell_step (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hint : DiscountedRewardIntegrable P r α) (γ : ℝ) (y : S) (m j : ℕ)
    {c : (ℕ → S) → ℝ} (hc : Measurable c) (hc0 : ∀ ω, 0 ≤ c ω) (hc1 : ∀ ω, c ω ≤ 1)
    (hcd : ∀ ω ω', (∀ v ≤ m, ω v = ω' v) → c ω = c ω') :
    ∫ ω, c ω * α ^ m * (r (ω m) - γ) ∂(markovChainMeasure P y) +
      ∫ ω, c ω * α ^ (m+1) * gittinsFiniteRetirementValue P r α γ j (ω (m+1))
        ∂(markovChainMeasure P y) =
    ∫ ω, c ω * α ^ m * (r (ω m) - γ + α * ∫ w, gittinsFiniteRetirementValue P r α γ j w ∂(P (ω m)))
      ∂(markovChainMeasure P y) := by
  have hb : ∀ s ω, ‖c ω * α ^ s‖ ≤ α ^ s := fun s ω => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hc0 ω), abs_of_pos (pow_pos hα0 s)]
    exact mul_le_of_le_one_left (pow_pos hα0 s).le (hc1 ω)
  have i1 : Integrable (fun ω => c ω * α ^ m * (r (ω m) - γ)) (markovChainMeasure P y) :=
    ((int_r P hr hα0 hint y m).sub (integrable_const γ)).bdd_mul
      (hc.mul measurable_const).aestronglyMeasurable (ae_of_all _ (hb m))
  have i2 : Integrable (fun ω => c ω * α ^ (m+1) *
      ∫ w, gittinsFiniteRetirementValue P r α γ j w ∂(P (ω m))) (markovChainMeasure P y) :=
    (iPU P hr hα0 hint γ y j m).bdd_mul (hc.mul measurable_const).aestronglyMeasurable
      (ae_of_all _ (hb (m+1)))
  have h1 : ∫ ω, c ω * α ^ (m+1) * gittinsFiniteRetirementValue P r α γ j (ω (m+1))
        ∂(markovChainMeasure P y) =
      ∫ ω, c ω * α ^ (m+1) * ∫ w, gittinsFiniteRetirementValue P r α γ j w ∂(P (ω m))
        ∂(markovChainMeasure P y) :=
    msb P y m (c := fun ω => c ω * α ^ (m+1)) (hc.mul measurable_const)
      (fun ω => mul_nonneg (hc0 ω) (pow_pos hα0 _).le) (fun ω ω' h => by simp only [hcd ω ω' h])
      (U_meas P hr α γ j) (U_nonneg P r α γ j) (iUP P hr hα0 hint γ j)
  rw [h1, ← integral_add i1 i2]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp only [Pi.add_apply]
  ring

lemma bell_le (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hint : DiscountedRewardIntegrable P r α) (γ : ℝ) (y : S) (H : ℕ)
    {σ : (ℕ → S) → ℕ∞} (hσ : IsTrajStoppingTime σ) (h1 : ∀ ω, 1 ≤ σ ω) (hH : ∀ ω, σ ω ≤ H) :
    ∫ ω, ∑ t ∈ Finset.range H, (if (t : ℕ∞) < σ ω then (1:ℝ) else 0) * α ^ t * (r (ω t) - γ)
      ∂(markovChainMeasure P y) ≤ gittinsFiniteRetirementValue P r α γ H y := by

  set μ := markovChainMeasure P y with hμ
  set c : ℕ → (ℕ → S) → ℝ := fun t ω => if (t : ℕ∞) < σ ω then (1:ℝ) else 0 with hcdef
  have cm : ∀ t, Measurable (c t) := fun t =>
    Measurable.ite (stop_lt_meas hσ t) measurable_const measurable_const
  have c0 : ∀ t ω, 0 ≤ c t ω := fun t ω => by simp only [c]; split_ifs <;> norm_num
  have c1 : ∀ t ω, c t ω ≤ 1 := fun t ω => by simp only [c]; split_ifs <;> norm_num
  have cdec : ∀ t ω, c (t+1) ω ≤ c t ω := fun t ω => by
    simp only [c]
    by_cases h : ((t + 1 : ℕ) : ℕ∞) < σ ω
    · have h' : (t : ℕ∞) < σ ω := lt_trans (by exact_mod_cast Nat.lt_succ_self t) h
      rw [if_pos h, if_pos h']
    · rw [if_neg h]; split_ifs <;> norm_num
  have cdep : ∀ t ω ω', (∀ v ≤ t, ω v = ω' v) → c t ω = c t ω' := fun t ω ω' h => by
    have h' : ((t:ℕ∞) < σ ω ↔ (t:ℕ∞) < σ ω') := by
      simpa only [not_le] using not_congr (stop_dep hσ t h)
    simp only [c]
    by_cases ha : (t:ℕ∞) < σ ω
    · rw [if_pos ha, if_pos (h'.1 ha)]
    · rw [if_neg ha, if_neg (fun hb => ha (h'.2 hb))]
  have hb : ∀ t s ω, ‖c t ω * α ^ s‖ ≤ α ^ s := fun t s ω => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (c0 t ω), abs_of_pos (pow_pos hα0 s)]
    exact mul_le_of_le_one_left (pow_pos hα0 s).le (c1 t ω)
  have iF : ∀ t, Integrable (fun ω => c t ω * α ^ t * (r (ω t) - γ)) μ := fun t =>
    ((int_r P hr hα0 hint y t).sub (integrable_const γ)).bdd_mul
      ((cm t).mul measurable_const).aestronglyMeasurable (ae_of_all _ (hb t t))
  have iUc : ∀ t s j, Integrable (fun ω => c t ω * α ^ s *
      gittinsFiniteRetirementValue P r α γ j (ω s)) μ := fun t s j =>
    (iU P hr hα0 hint γ y j s).bdd_mul ((cm t).mul measurable_const).aestronglyMeasurable
      (ae_of_all _ (hb t s))
  have iW : ∀ t j, Integrable (fun ω => c t ω * α ^ t * (r (ω t) - γ +
      α * ∫ w, gittinsFiniteRetirementValue P r α γ j w ∂(P (ω t)))) μ := fun t j =>
    (((int_r P hr hα0 hint y t).sub (integrable_const γ)).add
      ((iPU P hr hα0 hint γ y j t).const_mul α)).bdd_mul
      ((cm t).mul measurable_const).aestronglyMeasurable (ae_of_all _ (hb t t))
  have hsplit : ∀ k, k + 1 ≤ H → ∀ ω, ∑ t ∈ Finset.Ico (H - (k+1)) H, c t ω * α ^ t * (r (ω t) - γ) =
      c (H - (k+1)) ω * α ^ (H - (k+1)) * (r (ω (H - (k+1))) - γ) +
        ∑ t ∈ Finset.Ico (H - (k+1) + 1) H, c t ω * α ^ t * (r (ω t) - γ) := by
    intro k hk ω; rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]

  have claim : ∀ k, k ≤ H → ∫ ω, ∑ t ∈ Finset.Ico (H - k) H, c t ω * α ^ t * (r (ω t) - γ) ∂μ ≤
      ∫ ω, c (H - k) ω * α ^ (H - k) * gittinsFiniteRetirementValue P r α γ k (ω (H - k)) ∂μ := by
    intro k
    induction k with
    | zero => intro _; simp [U_zero]
    | succ k ih =>
      intro hk
      have hm : H - (k+1) + 1 = H - k := by omega
      simp_rw [hsplit k hk]
      rw [integral_add (iF _) (integrable_finset_sum _ fun t _ => iF t)]
      have h2 := ih (by omega)
      rw [← hm] at h2
      have h3 : ∫ ω, c (H - (k+1) + 1) ω * α ^ (H - (k+1) + 1) *
            gittinsFiniteRetirementValue P r α γ k (ω (H - (k+1) + 1)) ∂μ ≤
          ∫ ω, c (H - (k+1)) ω * α ^ (H - (k+1) + 1) *
            gittinsFiniteRetirementValue P r α γ k (ω (H - (k+1) + 1)) ∂μ :=
        integral_mono (iUc _ _ _) (iUc _ _ _) fun ω =>
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (cdec _ ω) (pow_pos hα0 _).le)
            (U_nonneg P r α γ k _)
      have h4 := bell_step P hr hα0 hint γ y (H - (k+1)) k (cm (H - (k+1))) (c0 _) (c1 _) (cdep _)
      calc _ ≤ ∫ ω, c (H - (k+1)) ω * α ^ (H - (k+1)) * (r (ω (H - (k+1))) - γ) ∂μ +
            ∫ ω, c (H - (k+1)) ω * α ^ (H - (k+1) + 1) *
              gittinsFiniteRetirementValue P r α γ k (ω (H - (k+1) + 1)) ∂μ :=
            add_le_add le_rfl (h2.trans h3)
        _ = _ := h4
        _ ≤ _ := integral_mono (iW _ _) (iUc _ _ _) fun ω => by
            dsimp only
            rw [U_succ]
            exact mul_le_mul_of_nonneg_left (le_max_right _ _)
              (mul_nonneg (c0 _ ω) (pow_pos hα0 _).le)
  have hc0' : ∀ ω, c 0 ω = 1 := fun ω => if_pos (lt_of_lt_of_le (by norm_num) (h1 ω))
  have := claim H le_rfl
  rw [Nat.sub_self, ← Finset.range_eq_Ico] at this
  show ∫ ω, ∑ t ∈ Finset.range H, c t ω * α ^ t * (r (ω t) - γ) ∂μ ≤ _
  refine this.trans (le_of_eq ?_)
  rw [integral_congr_ae (g := fun _ => gittinsFiniteRetirementValue P r α γ H y)
    ((ae_zero P y).mono fun ω h => by dsimp only; rw [hc0', h]; ring)]
  simp

lemma bell_eq (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hint : DiscountedRewardIntegrable P r α) (γ : ℝ) (y : S) (H : ℕ) (hH1 : 1 ≤ H)
    {σ : (ℕ → S) → ℕ∞} (hσ : IsTrajStoppingTime σ) (h1 : ∀ ω, 1 ≤ σ ω) (hH : ∀ ω, σ ω ≤ H)
    (copt1 : ∀ m ω, 1 ≤ m → m < H → (m : ℕ∞) < σ ω →
      0 < r (ω m) - γ + α * ∫ w, gittinsFiniteRetirementValue P r α γ (H - m - 1) w ∂P (ω m))
    (copt2 : ∀ m ω, m + 1 < H → σ ω = ((m + 1 : ℕ) : ℕ∞) →
      r (ω (m+1)) - γ + α * ∫ w, gittinsFiniteRetirementValue P r α γ (H - m - 2) w ∂P (ω (m+1))
        ≤ 0) :
    ∫ ω, ∑ t ∈ Finset.range H, (if (t : ℕ∞) < σ ω then (1:ℝ) else 0) * α ^ t * (r (ω t) - γ)
      ∂(markovChainMeasure P y) =
      r y - γ + α * ∫ w, gittinsFiniteRetirementValue P r α γ (H - 1) w ∂P y := by

  set μ := markovChainMeasure P y with hμ
  set c : ℕ → (ℕ → S) → ℝ := fun t ω => if (t : ℕ∞) < σ ω then (1:ℝ) else 0 with hcdef
  have cm : ∀ t, Measurable (c t) := fun t =>
    Measurable.ite (stop_lt_meas hσ t) measurable_const measurable_const
  have c0 : ∀ t ω, 0 ≤ c t ω := fun t ω => by simp only [c]; split_ifs <;> norm_num
  have c1 : ∀ t ω, c t ω ≤ 1 := fun t ω => by simp only [c]; split_ifs <;> norm_num
  have cdec : ∀ t ω, c (t+1) ω ≤ c t ω := fun t ω => by
    simp only [c]
    by_cases h : ((t + 1 : ℕ) : ℕ∞) < σ ω
    · have h' : (t : ℕ∞) < σ ω := lt_trans (by exact_mod_cast Nat.lt_succ_self t) h
      rw [if_pos h, if_pos h']
    · rw [if_neg h]; split_ifs <;> norm_num
  have cdep : ∀ t ω ω', (∀ v ≤ t, ω v = ω' v) → c t ω = c t ω' := fun t ω ω' h => by
    have h' : ((t:ℕ∞) < σ ω ↔ (t:ℕ∞) < σ ω') := by
      simpa only [not_le] using not_congr (stop_dep hσ t h)
    simp only [c]
    by_cases ha : (t:ℕ∞) < σ ω
    · rw [if_pos ha, if_pos (h'.1 ha)]
    · rw [if_neg ha, if_neg (fun hb => ha (h'.2 hb))]
  have hb : ∀ t s ω, ‖c t ω * α ^ s‖ ≤ α ^ s := fun t s ω => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (c0 t ω), abs_of_pos (pow_pos hα0 s)]
    exact mul_le_of_le_one_left (pow_pos hα0 s).le (c1 t ω)
  have iF : ∀ t, Integrable (fun ω => c t ω * α ^ t * (r (ω t) - γ)) μ := fun t =>
    ((int_r P hr hα0 hint y t).sub (integrable_const γ)).bdd_mul
      ((cm t).mul measurable_const).aestronglyMeasurable (ae_of_all _ (hb t t))
  have iUc : ∀ t s j, Integrable (fun ω => c t ω * α ^ s *
      gittinsFiniteRetirementValue P r α γ j (ω s)) μ := fun t s j =>
    (iU P hr hα0 hint γ y j s).bdd_mul ((cm t).mul measurable_const).aestronglyMeasurable
      (ae_of_all _ (hb t s))
  have iW : ∀ t j, Integrable (fun ω => c t ω * α ^ t * (r (ω t) - γ +
      α * ∫ w, gittinsFiniteRetirementValue P r α γ j w ∂(P (ω t)))) μ := fun t j =>
    (((int_r P hr hα0 hint y t).sub (integrable_const γ)).add
      ((iPU P hr hα0 hint γ y j t).const_mul α)).bdd_mul
      ((cm t).mul measurable_const).aestronglyMeasurable (ae_of_all _ (hb t t))
  have hsplit : ∀ k, k + 1 ≤ H → ∀ ω, ∑ t ∈ Finset.Ico (H - (k+1)) H, c t ω * α ^ t * (r (ω t) - γ) =
      c (H - (k+1)) ω * α ^ (H - (k+1)) * (r (ω (H - (k+1))) - γ) +
        ∑ t ∈ Finset.Ico (H - (k+1) + 1) H, c t ω * α ^ t * (r (ω t) - γ) := by
    intro k hk ω; rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]

  have sw : ∀ m k ω, m + 1 + k = H → c (m+1) ω * gittinsFiniteRetirementValue P r α γ k (ω (m+1)) =
      c m ω * gittinsFiniteRetirementValue P r α γ k (ω (m+1)) := by
    intro m k ω hmk
    by_cases ha : ((m+1 : ℕ) : ℕ∞) < σ ω
    · have hb' : (m : ℕ∞) < σ ω := lt_trans (by exact_mod_cast Nat.lt_succ_self m) ha
      simp only [c, if_pos ha, if_pos hb']
    · simp only [c, if_neg ha, zero_mul]
      by_cases hb' : (m : ℕ∞) < σ ω
      · have heq : σ ω = ((m+1 : ℕ) : ℕ∞) := by
          obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.1
            (ne_top_of_le_ne_top (ENat.coe_ne_top H) (hH ω))
          rw [← hs] at ha hb' ⊢
          have e1 : m < s := by exact_mod_cast hb'
          have e2 : ¬ (m + 1 < s) := by exact_mod_cast ha
          exact_mod_cast (show s = m + 1 by omega)
        cases k with
        | zero => rw [U_zero, mul_zero]
        | succ k =>
          have hlt : m + 1 < H := by omega
          have h2 := copt2 m ω hlt heq
          rw [show H - m - 2 = k by omega] at h2
          rw [U_succ, max_eq_left h2, mul_zero]
      · simp only [if_neg hb', zero_mul]
  have claim : ∀ k, k < H → ∫ ω, ∑ t ∈ Finset.Ico (H - k) H, c t ω * α ^ t * (r (ω t) - γ) ∂μ =
      ∫ ω, c (H - k) ω * α ^ (H - k) * gittinsFiniteRetirementValue P r α γ k (ω (H - k)) ∂μ := by
    intro k
    induction k with
    | zero => intro _; simp [U_zero]
    | succ k ih =>
      intro hk
      have hm : H - (k+1) + 1 = H - k := by omega
      simp_rw [hsplit k hk.le]
      rw [integral_add (iF _) (integrable_finset_sum _ fun t _ => iF t), hm, ih (by omega), ← hm]
      have h3 : ∫ ω, c (H - (k+1) + 1) ω * α ^ (H - (k+1) + 1) *
            gittinsFiniteRetirementValue P r α γ k (ω (H - (k+1) + 1)) ∂μ =
          ∫ ω, c (H - (k+1)) ω * α ^ (H - (k+1) + 1) *
            gittinsFiniteRetirementValue P r α γ k (ω (H - (k+1) + 1)) ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun ω => ?_)
        have := sw (H - (k+1)) k ω (by omega)
        dsimp only
        linear_combination α ^ (H - (k + 1) + 1) * this
      rw [h3, bell_step P hr hα0 hint γ y (H - (k+1)) k (cm _) (c0 _) (c1 _) (cdep _)]
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      dsimp only
      by_cases hlt : ((H - (k+1) : ℕ) : ℕ∞) < σ ω
      · have := copt1 (H - (k+1)) ω (by omega) (by omega) hlt
        rw [show H - (H - (k+1)) - 1 = k by omega] at this
        rw [U_succ, max_eq_right this.le]
      · simp only [c, if_neg hlt, zero_mul]
  have hc0' : ∀ ω, c 0 ω = 1 := fun ω => if_pos (lt_of_lt_of_le (by norm_num) (h1 ω))
  have hsplit0 : ∀ ω, ∑ t ∈ Finset.range H, c t ω * α ^ t * (r (ω t) - γ) =
      c 0 ω * α ^ 0 * (r (ω 0) - γ) + ∑ t ∈ Finset.Ico (H - (H - 1)) H, c t ω * α ^ t * (r (ω t) - γ) := by
    intro ω
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), show H - (H - 1) = 0 + 1 by omega]
  show ∫ ω, ∑ t ∈ Finset.range H, c t ω * α ^ t * (r (ω t) - γ) ∂μ = _
  simp_rw [hsplit0]
  rw [integral_add (iF 0) (integrable_finset_sum _ fun t _ => iF t), claim (H - 1) (by omega),
    show H - (H - 1) = 0 + 1 by omega]
  have h3 : ∫ ω, c (0 + 1) ω * α ^ (0 + 1) * gittinsFiniteRetirementValue P r α γ (H - 1) (ω (0 + 1)) ∂μ =
      ∫ ω, c 0 ω * α ^ (0 + 1) * gittinsFiniteRetirementValue P r α γ (H - 1) (ω (0 + 1)) ∂μ :=
    integral_congr_ae (ae_of_all _ fun ω => by
      have := sw 0 (H - 1) ω (by omega); dsimp only; linear_combination α ^ (0 + 1) * this)
  rw [h3, bell_step P hr hα0 hint γ y 0 (H - 1) (cm 0) (c0 0) (c1 0) (cdep 0)]
  rw [integral_congr_ae (g := fun _ => r y - γ + α * ∫ w, gittinsFiniteRetirementValue P r α γ (H - 1) w ∂P y)
    ((ae_zero P y).mono fun ω h => by dsimp only; rw [hc0', h]; ring)]
  simp

lemma val_eq (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hint : DiscountedRewardIntegrable P r α) (γ : ℝ) (y : S) (H : ℕ)
    {σ : (ℕ → S) → ℕ∞} (hσ : IsTrajStoppingTime σ) (hH : ∀ ω, σ ω ≤ H) :
    ∫ ω, discountedStoppedSum α r σ ω ∂(markovChainMeasure P y) -
      γ * ∫ ω, discountedStoppedSum α (fun _ => 1) σ ω ∂(markovChainMeasure P y) =
    ∫ ω, ∑ t ∈ Finset.range H, (if (t : ℕ∞) < σ ω then (1:ℝ) else 0) * α ^ t * (r (ω t) - γ)
      ∂(markovChainMeasure P y) := by
  have cm : ∀ t : ℕ, Measurable (fun ω : ℕ → S => if (t : ℕ∞) < σ ω then (1:ℝ) else 0) := fun t =>
    Measurable.ite (stop_lt_meas hσ t) measurable_const measurable_const
  have hb : ∀ (t : ℕ) (ω : ℕ → S), ‖(if (t : ℕ∞) < σ ω then (1:ℝ) else 0) * α ^ t‖ ≤ α ^ t :=
    fun t ω => by
    split_ifs <;> simp only [one_mul, zero_mul, norm_zero, Real.norm_eq_abs, abs_pow,
      abs_of_pos hα0, le_refl] <;> positivity
  have i1 : Integrable (fun ω => ∑ t ∈ Finset.range H,
      (if (t : ℕ∞) < σ ω then (1:ℝ) else 0) * α ^ t * r (ω t)) (markovChainMeasure P y) :=
    integrable_finset_sum _ fun t _ => (int_r P hr hα0 hint y t).bdd_mul
      ((cm t).mul measurable_const).aestronglyMeasurable (ae_of_all _ (hb t))
  have i2 : Integrable (fun ω => γ * ∑ t ∈ Finset.range H,
      (if (t : ℕ∞) < σ ω then (1:ℝ) else 0) * α ^ t * 1) (markovChainMeasure P y) :=
    (integrable_finset_sum _ fun t _ => (integrable_const (1:ℝ)).bdd_mul
      ((cm t).mul measurable_const).aestronglyMeasurable (ae_of_all _ (hb t))).const_mul γ
  simp only [disc_fin α r hH, disc_fin α (fun _ => (1:ℝ)) hH]
  rw [← integral_const_mul, ← integral_sub i1 i2]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

theorem gi_meas (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hint : DiscountedRewardIntegrable P r α) :
    Measurable (gittinsIndex P r α) := by
  refine measurable_of_Ioi fun γ => ?_
  have hset : gittinsIndex P r α ⁻¹' Set.Ioi γ =
      ⋃ H : ℕ, {y | 0 < gittinsFiniteRetirementValue P r α γ (H + 1) y} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_iUnion, Set.mem_setOf_eq]
    have hbdd := gi_bdd P hr hα0 hα1 hint y
    have hne : ({g : ℝ | ∃ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
      g = (∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P y) /
        (∫ ω, discountedStoppedSum α (fun _ ↦ 1) τ ω ∂markovChainMeasure P y)}).Nonempty :=
      ⟨_, fun _ => 1, fun n => MeasurableSet.const _, fun _ => le_rfl, rfl⟩
    constructor
    · intro hy
      obtain ⟨_, ⟨τ, hτ, h1, rfl⟩, hlt⟩ := (lt_csSup_iff hbdd hne).1 hy
      have hD := D_ge_one P hα0 hα1 y hτ h1
      rw [lt_div_iff₀ (by linarith)] at hlt
      obtain ⟨-, hTN, -⟩ := dct_disc P hα0 hr y (hint y) hτ
      obtain ⟨-, hTD, -⟩ := dct_disc P hα0 measurable_const y (hfin_one P hα0 hα1 y) hτ
      have hT := hTN.sub (hTD.const_mul γ)
      have h0 : (0:ℝ) < (∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P y) -
          γ * (∫ ω, discountedStoppedSum α (fun _ ↦ 1) τ ω ∂markovChainMeasure P y) := by linarith
      obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.1 (hT.eventually (lt_mem_nhds h0))
      have hn := hn0 (max n0 1) (le_max_left _ _)
      set n := max n0 1 with hndef
      have hn1 : 1 ≤ n := le_max_right _ _
      have hσ : IsTrajStoppingTime (fun ω => min (τ ω) (n : ℕ∞)) := by
        intro t
        have e : {ω : ℕ → S | min (τ ω) (n : ℕ∞) ≤ t} =
            {ω | τ ω ≤ t} ∪ {ω | (n : ℕ∞) ≤ t} := by
          ext ω; simp only [Set.mem_setOf_eq, Set.mem_union, min_le_iff]
        rw [e]
        exact (hτ t).union (MeasurableSet.const _)
      have hσ1 : ∀ ω, 1 ≤ min (τ ω) (n : ℕ∞) := fun ω => le_min (h1 ω) (by exact_mod_cast hn1)
      have hσH : ∀ ω, min (τ ω) (n : ℕ∞) ≤ n := fun ω => min_le_right _ _
      have hb := bell_le P hr hα0 hint γ y n hσ hσ1 hσH
      have hv := val_eq P hr hα0 hint γ y n hσ hσH
      refine ⟨n - 1, ?_⟩
      rw [show n - 1 + 1 = n by omega]
      linarith
    · rintro ⟨H, hH⟩
      set W : ℕ → S → ℝ := fun j z =>
        r z - γ + α * ∫ w, gittinsFiniteRetirementValue P r α γ j w ∂P z with hW
      have hWm : ∀ j, Measurable (W j) := fun j => (hr.sub measurable_const).add
        (measurable_const.mul ((U_meas P hr α γ j).stronglyMeasurable.integral_kernel (κ := P)).measurable)
      classical
      let p : (ℕ → S) → ℕ → Prop := fun ω m =>
        (1 ≤ m ∧ m < H + 1 ∧ W (H + 1 - m - 1) (ω m) ≤ 0) ∨ m = H + 1
      have hex : ∀ ω, ∃ m, p ω m := fun ω => ⟨H + 1, Or.inr rfl⟩
      let σ : (ℕ → S) → ℕ∞ := fun ω => (Nat.find (hex ω) : ℕ∞)
      have hσH : ∀ ω, σ ω ≤ ((H + 1 : ℕ) : ℕ∞) := fun ω => by
        show ((Nat.find (hex ω) : ℕ) : ℕ∞) ≤ ((H + 1 : ℕ) : ℕ∞)
        exact_mod_cast Nat.find_min' (hex ω) (Or.inr rfl)
      have hσ1 : ∀ ω, 1 ≤ σ ω := fun ω => by
        have : 0 < Nat.find (hex ω) := (Nat.find_pos _).2 (by simp [p])
        show (1 : ℕ∞) ≤ ((Nat.find (hex ω) : ℕ) : ℕ∞)
        exact_mod_cast Nat.succ_le_of_lt this
      have hσ : IsTrajStoppingTime σ := by
        intro n
        have e : {ω : ℕ → S | σ ω ≤ n} = ⋃ m : Fin (n + 1), {ω | p ω m} := by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_iUnion, σ, Nat.cast_le, Nat.find_le_iff]
          constructor
          · rintro ⟨m, hm, hp⟩; exact ⟨⟨m, by omega⟩, hp⟩
          · rintro ⟨m, hp⟩; exact ⟨m, by omega, hp⟩
        rw [e]
        refine MeasurableSet.iUnion fun m => ?_
        rw [MeasurableSpace.measurableSet_comap]
        refine ⟨{z : Iic n → S | 1 ≤ (m : ℕ) ∧ (m : ℕ) < H + 1} ∩
            {z | W (H + 1 - m - 1) (z ⟨m, mem_Iic.2 (by omega)⟩) ≤ 0} ∪ {z | (m : ℕ) = H + 1},
          ((MeasurableSet.const _).inter (measurableSet_le ((hWm _).comp (measurable_pi_apply _))
            measurable_const)).union (MeasurableSet.const _), ?_⟩
        ext ω
        simp only [Set.mem_preimage, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq, p, and_assoc]
      have copt1 : ∀ m ω, 1 ≤ m → m < H + 1 → (m : ℕ∞) < σ ω →
          0 < r (ω m) - γ + α * ∫ w, gittinsFiniteRetirementValue P r α γ (H + 1 - m - 1) w ∂P (ω m) := by
        intro m ω hm1 hmH hlt
        have hlt' : m < Nat.find (hex ω) := by
          have h' : (m : ℕ∞) < ((Nat.find (hex ω) : ℕ) : ℕ∞) := hlt
          exact_mod_cast h'
        have := Nat.find_min (hex ω) hlt'
        simp only [p, not_or, not_and, not_le] at this
        exact this.1 hm1 hmH
      have copt2 : ∀ m ω, m + 1 < H + 1 → σ ω = ((m + 1 : ℕ) : ℕ∞) →
          r (ω (m+1)) - γ + α * ∫ w, gittinsFiniteRetirementValue P r α γ (H + 1 - m - 2) w ∂P (ω (m+1))
            ≤ 0 := by
        intro m ω hmH heq
        have heq' : Nat.find (hex ω) = m + 1 := by
          have h' : ((Nat.find (hex ω) : ℕ) : ℕ∞) = ((m + 1 : ℕ) : ℕ∞) := heq
          exact_mod_cast h'
        have := Nat.find_spec (hex ω)
        rw [heq'] at this
        rcases this with ⟨-, -, hle⟩ | h
        · rw [show H + 1 - (m + 1) - 1 = H + 1 - m - 2 by omega] at hle; exact hle
        · omega
      have hbe := bell_eq P hr hα0 hint γ y (H + 1) (by omega) hσ hσ1 hσH copt1 copt2
      have hv := val_eq P hr hα0 hint γ y (H + 1) hσ hσH
      have hD := D_ge_one P hα0 hα1 y hσ hσ1
      rw [U_succ] at hH
      have hW0 : 0 < r y - γ + α * ∫ w, gittinsFiniteRetirementValue P r α γ H w ∂P y := by
        rcases lt_max_iff.1 hH with h | h
        · exact absurd h (lt_irrefl 0)
        · exact h
      rw [show H + 1 - 1 = H by omega] at hbe
      refine lt_csSup_of_lt hbdd ⟨σ, hσ, hσ1, rfl⟩ ?_
      rw [lt_div_iff₀ (by linarith)]
      linarith
  rw [hset]
  exact MeasurableSet.iUnion fun H => measurableSet_lt measurable_const (U_meas P hr α γ (H + 1))

end GI

section Final
variable [MeasurableSingletonClass S] {k : ℕ}

lemma chg_int (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hint : DiscountedRewardIntegrable P r α) (x : Fin k → S)
    (i : Fin k) (u : ℕ) :
    Integrable (fun ω => chg (gittinsIndex P r α) ω i u) (stack P x) := by
  have hgm := gi_meas P hr hα0 hα1 hint
  have hrg : ∀ y, r y ≤ gittinsIndex P r α y := fun y => r_le_gi P hr hα0 hα1 hint y
  have hri : ∀ v, Integrable (fun ω : Fin k → ℕ → S => r (ω i v)) (stack P x) := fun v =>
    (measurePreserving_eval (fun j => markovChainMeasure P (x j)) i).integrable_comp_of_integrable
      (int_r P hr hα0 hint (x i) v)
  have hB : Integrable (fun ω : Fin k → ℕ → S => |gittinsIndex P r α (x i)| +
      ∑ v ∈ Finset.range (u + 1), |r (ω i v)|) (stack P x) :=
    (integrable_const _).add (integrable_finset_sum _ fun v _ => (hri v).abs)
  refine hB.mono' (chg_meas hgm i u).aestronglyMeasurable ?_
  filter_upwards [stack_ae_zero P x] with ω hω
  rw [Real.norm_eq_abs, abs_le]
  have h1 := chg_le (gittinsIndex P r α) ω i u
  have h2 := chg_ge hrg ω i u
  rw [hω i] at h1
  have h3 : 0 ≤ |gittinsIndex P r α (x i)| := abs_nonneg _
  have h4 := le_abs_self (gittinsIndex P r α (x i))
  have h5 : 0 ≤ ∑ v ∈ Finset.range (u + 1), |r (ω i v)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  constructor <;> linarith

end Final
end G6cb

namespace WGRed

open BanditAlgorithm WeberGittins.Submodular

lemma pis_zero {n : ℕ} (H : Fin n → ℕ → ℝ) (I : Finset (Fin n)) :
    partialInterleavedSum H I 0 = 0 := by
  unfold partialInterleavedSum
  split_ifs with hI
  · rfl
  · have hz : ∀ m ∈ playAllocations I 0,
        (∑ j ∈ I, ∑ u ∈ Finset.range (m j), H j u) = 0 := by
      intro m hm
      simp only [playAllocations, Finset.mem_filter] at hm
      have h0 : ∀ j, m j = 0 := fun j =>
        (Finset.sum_eq_zero_iff.1 hm.2.2) j (Finset.mem_univ j)
      simp [h0]
    apply le_antisymm
    · exact Finset.sup'_le _ _ fun m hm => (hz m hm).le
    · obtain ⟨m, hm⟩ := playAllocations_nonempty hI 0
      exact Finset.le_sup'_of_le (fun m : Fin n → ℕ => ∑ j ∈ I, ∑ u ∈ Finset.range (m j), H j u)
        hm (hz m hm).symm.le

lemma pis_nonneg {n : ℕ} (H : Fin n → ℕ → ℝ) (hH : ∀ j k, 0 ≤ H j k) (I : Finset (Fin n))
    (t : ℕ) : 0 ≤ partialInterleavedSum H I t := by
  unfold partialInterleavedSum
  split_ifs with hI
  · exact le_rfl
  · obtain ⟨m, hm⟩ := playAllocations_nonempty hI t
    exact Finset.le_sup'_of_le (fun m : Fin n → ℕ => ∑ j ∈ I, ∑ u ∈ Finset.range (m j), H j u)
      hm (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun u _ => hH j u)

lemma pis_le {n : ℕ} (H : Fin n → ℕ → ℝ) (M : ℝ) (hM : ∀ j k, H j k ≤ M) (hM0 : 0 ≤ M)
    (I : Finset (Fin n)) (t : ℕ) : partialInterleavedSum H I t ≤ t * M := by
  unfold partialInterleavedSum
  split_ifs with hI
  · positivity
  · apply Finset.sup'_le
    intro m hm
    simp only [playAllocations, Finset.mem_filter] at hm
    calc ∑ j ∈ I, ∑ u ∈ Finset.range (m j), H j u
        ≤ ∑ j ∈ I, ((m j : ℝ) * M) := Finset.sum_le_sum fun j _ => by
          calc ∑ u ∈ Finset.range (m j), H j u ≤ ∑ u ∈ Finset.range (m j), M :=
                Finset.sum_le_sum fun u _ => hM j u
            _ = (m j : ℝ) * M := by simp
      _ ≤ ∑ j, ((m j : ℝ) * M) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun j _ _ => mul_nonneg (Nat.cast_nonneg _) hM0
      _ = (t : ℝ) * M := by
          rw [← Finset.sum_mul, ← Nat.cast_sum, hm.2.2]

lemma abel (β : ℝ) (U : ℕ → ℝ) (h0 : U 0 = 0) (N : ℕ) :
    ∑ t ∈ Finset.range N, β ^ t * (U (t + 1) - U t) =
      (1 - β) * ∑ t ∈ Finset.range N, β ^ t * U (t + 1) + β ^ N * U N := by
  induction N with
  | zero => simp [h0]
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

lemma partial_ineq {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (U1 U2 U3 U4 : ℕ → ℝ)
    (h1 : U1 0 = 0) (h2 : U2 0 = 0) (h3 : U3 0 = 0) (h4 : U4 0 = 0)
    (h : ∀ t, U1 t + U2 t ≤ U3 t + U4 t) (N : ℕ) :
    ∑ t ∈ Finset.range N, β ^ t * (U1 (t + 1) - U1 t) +
        ∑ t ∈ Finset.range N, β ^ t * (U2 (t + 1) - U2 t) ≤
      ∑ t ∈ Finset.range N, β ^ t * (U3 (t + 1) - U3 t) +
        ∑ t ∈ Finset.range N, β ^ t * (U4 (t + 1) - U4 t) := by
  rw [abel β U1 h1, abel β U2 h2, abel β U3 h3, abel β U4 h4]
  have hA : ∑ t ∈ Finset.range N, β ^ t * U1 (t + 1) + ∑ t ∈ Finset.range N, β ^ t * U2 (t + 1) ≤
      ∑ t ∈ Finset.range N, β ^ t * U3 (t + 1) + ∑ t ∈ Finset.range N, β ^ t * U4 (t + 1) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun t _ => by
      have := h (t + 1)
      have hp := pow_pos hβ0 t
      nlinarith
  have hB : β ^ N * U1 N + β ^ N * U2 N ≤ β ^ N * U3 N + β ^ N * U4 N := by
    have := h N
    have hp := pow_pos hβ0 N
    nlinarith
  have hC := mul_le_mul_of_nonneg_left hA (by linarith : (0:ℝ) ≤ 1 - β)
  nlinarith

lemma summ_bound {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (U : ℕ → ℝ) (M : ℝ)
    (hU0 : ∀ t, 0 ≤ U t) (hUM : ∀ t, U t ≤ t * M) :
    (∀ t, ‖β ^ t * (U (t + 1) - U t)‖ ≤ (2 * M) * ((t : ℝ) ^ 1 * β ^ t) + M * β ^ t) ∧
      Summable (fun t : ℕ => (2 * M) * ((t : ℝ) ^ 1 * β ^ t) + M * β ^ t) := by
  have hnorm : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hβ0]; exact hβ1
  refine ⟨fun t => ?_, ((summable_pow_mul_geometric_of_norm_lt_one 1 hnorm).mul_left (2 * M)).add
    ((summable_geometric_of_lt_one hβ0.le hβ1).mul_left M)⟩
  have hp := pow_pos hβ0 t
  have a1 := hU0 t
  have a2 := hU0 (t + 1)
  have b1 := hUM t
  have b2 := hUM (t + 1)
  push_cast at b2
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hp]
  have hd : |U (t + 1) - U t| ≤ (2 * t + 1) * M := by
    rw [abs_le]; constructor <;> nlinarith
  calc β ^ t * |U (t + 1) - U t| ≤ β ^ t * ((2 * t + 1) * M) :=
        mul_le_mul_of_nonneg_left hd hp.le
    _ = _ := by ring

lemma summ_of {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (U : ℕ → ℝ) (M : ℝ)
    (hU0 : ∀ t, 0 ≤ U t) (hUM : ∀ t, U t ≤ t * M) :
    Summable (fun t : ℕ => β ^ t * (U (t + 1) - U t)) := by
  obtain ⟨hb, hs⟩ := summ_bound hβ0 hβ1 U M hU0 hUM
  exact Summable.of_norm_bounded hs hb

lemma tsum_ineq {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (U1 U2 U3 U4 : ℕ → ℝ)
    (h1 : U1 0 = 0) (h2 : U2 0 = 0) (h3 : U3 0 = 0) (h4 : U4 0 = 0)
    (s1 : Summable (fun t : ℕ => β ^ t * (U1 (t + 1) - U1 t)))
    (s2 : Summable (fun t : ℕ => β ^ t * (U2 (t + 1) - U2 t)))
    (s3 : Summable (fun t : ℕ => β ^ t * (U3 (t + 1) - U3 t)))
    (s4 : Summable (fun t : ℕ => β ^ t * (U4 (t + 1) - U4 t)))
    (h : ∀ t, U1 t + U2 t ≤ U3 t + U4 t) :
    ∑' t, β ^ t * (U1 (t + 1) - U1 t) + ∑' t, β ^ t * (U2 (t + 1) - U2 t) ≤
      ∑' t, β ^ t * (U3 (t + 1) - U3 t) + ∑' t, β ^ t * (U4 (t + 1) - U4 t) :=
  le_of_tendsto_of_tendsto' (s1.hasSum.tendsto_sum_nat.add s2.hasSum.tendsto_sum_nat)
    (s3.hasSum.tendsto_sum_nat.add s4.hasSum.tendsto_sum_nat)
    (partial_ineq hβ0 hβ1 U1 U2 U3 U4 h1 h2 h3 h4 h)

lemma pis_meas {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (H : Ω → Fin n → ℕ → ℝ)
    (hH : ∀ j k, Measurable fun ω => H ω j k) (I : Finset (Fin n)) (t : ℕ) :
    Measurable fun ω => partialInterleavedSum (H ω) I t := by
  unfold partialInterleavedSum
  split_ifs with hI
  · exact measurable_const
  · have := Finset.measurable_sup' (playAllocations_nonempty hI t)
      (f := fun m ω => ∑ j ∈ I, ∑ u ∈ Finset.range (m j), H ω j u)
      (fun m _ => Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun u _ => hH j u)
    convert this using 1
    funext ω
    rw [Finset.sup'_apply]

lemma hint_of {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ}
    (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) : DiscountedRewardIntegrable P r β := by
  obtain ⟨hr0, C, hC⟩ := hrb
  intro x
  have hC0 : 0 ≤ C := (hr0 x).trans (hC x)
  have hb : ∀ ω : ℕ → S, ∑' t, ENNReal.ofReal (β ^ t * |r (ω t)|) ≤
      ∑' t : ℕ, ENNReal.ofReal (β ^ t * C) := fun ω =>
    ENNReal.tsum_le_tsum fun t => ENNReal.ofReal_le_ofReal (by
      rw [abs_of_nonneg (hr0 _)]; exact mul_le_mul_of_nonneg_left (hC _) (pow_pos hβ0 t).le)
  calc _ ≤ ∫⁻ ω, ∑' t : ℕ, ENNReal.ofReal (β ^ t * C) ∂markovChainMeasure P x := lintegral_mono hb
    _ < ⊤ := by
      rw [lintegral_const, measure_univ, mul_one,
        ← ENNReal.ofReal_tsum_of_nonneg (fun t => mul_nonneg (pow_pos hβ0 t).le hC0)
          ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right C)]
      exact ENNReal.ofReal_lt_top

lemma stack_facts {n : ℕ} {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]
    (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r)
    (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (ω : Fin n → ℕ → S) :
    (∀ j, Antitone (prevailingChargeStack P r β ω j)) ∧
      (∀ j k, 0 ≤ prevailingChargeStack P r β ω j k) ∧
      (∀ j k, prevailingChargeStack P r β ω j k ≤ ∑ i, gittinsIndex P r β (ω i 0)) := by
  have hint := hint_of P hrb hβ0 hβ1
  have hg0 : ∀ y, 0 ≤ gittinsIndex P r β y := fun y =>
    (hrb.1 y).trans (G6cb.r_le_gi P hr hβ0 hβ1 hint y)
  have e : ∀ j k, prevailingChargeStack P r β ω j k = G6cb.chg (gittinsIndex P r β) ω j k :=
    fun _ _ => rfl
  refine ⟨fun j => antitone_nat_of_succ_le fun k => ?_, fun j k => ?_, fun j k => ?_⟩
  · rw [e, e, G6cb.chg_succ]; exact min_le_left _ _
  · unfold prevailingChargeStack
    exact Finset.le_inf' _ _ fun v _ => hg0 _
  · rw [e]
    exact (G6cb.chg_le _ ω j k).trans
      (Finset.single_le_sum (f := fun i => gittinsIndex P r β (ω i 0)) (fun i _ => hg0 _)
        (Finset.mem_univ j))

lemma U_facts {n : ℕ} {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]
    (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r)
    (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (ω : Fin n → ℕ → S) (I : Finset (Fin n)) :
    (∀ t, 0 ≤ partialInterleavedSum (prevailingChargeStack P r β ω) I t) ∧
    (∀ t, partialInterleavedSum (prevailingChargeStack P r β ω) I t ≤
      t * ∑ i, gittinsIndex P r β (ω i 0)) := by
  obtain ⟨-, hnn, hle⟩ := stack_facts P hr hrb hβ0 hβ1 ω
  have hM0 : 0 ≤ ∑ i, gittinsIndex P r β (ω i 0) := by
    have hint := hint_of P hrb hβ0 hβ1
    exact Finset.sum_nonneg fun i _ =>
      (hrb.1 _).trans (G6cb.r_le_gi P hr hβ0 hβ1 hint _)
  exact ⟨pis_nonneg _ hnn I, pis_le _ _ hle hM0 I⟩

lemma F_int {n : ℕ} {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]
    (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r)
    (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (x : Fin n → S) (I : Finset (Fin n)) :
    Integrable (fun ω : Fin n → ℕ → S => ∑' t : ℕ, β ^ t *
          (partialInterleavedSum (prevailingChargeStack P r β ω) I (t + 1) -
            partialInterleavedSum (prevailingChargeStack P r β ω) I t))
      (Measure.pi fun j => markovChainMeasure P (x j)) := by
  have hint := hint_of P hrb hβ0 hβ1
  have hg := G6cb.gi_meas P hr hβ0 hβ1 hint
  have hHm : ∀ j k, Measurable fun ω : Fin n → ℕ → S => prevailingChargeStack P r β ω j k :=
    fun j k => G6cb.chg_meas hg j k
  have hUm : ∀ t, Measurable fun ω : Fin n → ℕ → S =>
      partialInterleavedSum (prevailingChargeStack P r β ω) I t :=
    fun t => pis_meas (fun ω => prevailingChargeStack P r β ω) hHm I t
  have hsum : ∀ ω : Fin n → ℕ → S, Summable fun t : ℕ => β ^ t *
      (partialInterleavedSum (prevailingChargeStack P r β ω) I (t + 1) -
        partialInterleavedSum (prevailingChargeStack P r β ω) I t) := fun ω =>
    summ_of hβ0 hβ1 _ _ (U_facts P hr hrb hβ0 hβ1 ω I).1 (U_facts P hr hrb hβ0 hβ1 ω I).2
  have hmeas : Measurable (fun ω : Fin n → ℕ → S => ∑' t : ℕ, β ^ t *
      (partialInterleavedSum (prevailingChargeStack P r β ω) I (t + 1) -
        partialInterleavedSum (prevailingChargeStack P r β ω) I t)) := by
    refine measurable_of_tendsto_metrizable (f := fun N (ω : Fin n → ℕ → S) =>
      ∑ t ∈ Finset.range N, β ^ t *
        (partialInterleavedSum (prevailingChargeStack P r β ω) I (t + 1) -
          partialInterleavedSum (prevailingChargeStack P r β ω) I t)) (fun N => ?_) ?_
    · exact Finset.measurable_sum _ fun t _ =>
        measurable_const.mul ((hUm (t + 1)).sub (hUm t))
    · exact tendsto_pi_nhds.2 fun ω => (hsum ω).hasSum.tendsto_sum_nat
  set K := ∑ i, gittinsIndex P r β (x i)
  refine Integrable.mono' (integrable_const (∑' t : ℕ, ((2 * K) * ((t : ℝ) ^ 1 * β ^ t) + K * β ^ t)))
    hmeas.aestronglyMeasurable ?_
  have hae : ∀ᵐ ω ∂(Measure.pi fun j => markovChainMeasure P (x j)), ∀ i, ω i 0 = x i :=
    G6cb.stack_ae_zero P x
  filter_upwards [hae] with ω hω
  have hM : ∑ i, gittinsIndex P r β (ω i 0) = K := by simp only [K, hω]
  obtain ⟨h0, hle⟩ := U_facts P hr hrb hβ0 hβ1 ω I
  rw [hM] at hle
  obtain ⟨hb, hs⟩ := summ_bound hβ0 hβ1 _ K h0 hle
  exact tsum_of_norm_bounded hs.hasSum hb

end WGRed


open Finset

namespace WG5

open WeberGittins.Submodular

lemma amax_ne {k : ℕ} (hk : 0 < k) (v : Fin k → ℝ) :
    (univ.filter fun i => ∀ j, v j ≤ v i).Nonempty := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (univ : Finset (Fin k)) v ⟨⟨0, hk⟩, mem_univ _⟩
  exact ⟨i, mem_filter.2 ⟨mem_univ _, fun j => hi j (mem_univ _)⟩⟩

/-- argmax over `Fin k` (least index among the maximizers). -/
noncomputable def amax {k : ℕ} (hk : 0 < k) (v : Fin k → ℝ) : Fin k :=
  (univ.filter fun i => ∀ j, v j ≤ v i).min' (amax_ne hk v)

lemma amax_spec {k : ℕ} (hk : 0 < k) (v : Fin k → ℝ) (j : Fin k) : v j ≤ v (amax hk v) := by
  have h := min'_mem (univ.filter fun i => ∀ j, v j ≤ v i) (amax_ne hk v)
  exact (mem_filter.1 h).2 j

lemma amax_eq_iff {k : ℕ} (hk : 0 < k) (v : Fin k → ℝ) (i : Fin k) :
    amax hk v = i ↔ (∀ j, v j ≤ v i) ∧ ∀ j, (∀ l, v l ≤ v j) → i ≤ j := by
  constructor
  · rintro rfl
    exact ⟨amax_spec hk v, fun j hj => min'_le (univ.filter fun i => ∀ j, v j ≤ v i) j
      (mem_filter.2 ⟨mem_univ _, hj⟩)⟩
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · exact min'_le (univ.filter fun i => ∀ j, v j ≤ v i) i (mem_filter.2 ⟨mem_univ _, h1⟩)
    · exact h2 _ (amax_spec hk v)

lemma amax_meas {k : ℕ} (hk : 0 < k) : Measurable (amax hk) := by
  refine measurable_to_countable' fun i => ?_
  have hA : ∀ j : Fin k, MeasurableSet {v : Fin k → ℝ | ∀ l, v l ≤ v j} := fun j => by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun l =>
      measurableSet_le (measurable_pi_apply l) (measurable_pi_apply j)
  have : amax hk ⁻¹' {i} =
      {v | ∀ l, v l ≤ v i} ∩ ⋂ j, {v : Fin k → ℝ | (∀ l, v l ≤ v j) → i ≤ j} := by
    ext v; simp [amax_eq_iff]
  rw [this]
  refine (hA i).inter (MeasurableSet.iInter fun j => ?_)
  by_cases hij : i ≤ j
  · simp [hij]
  · have e : {v : Fin k → ℝ | (∀ l, v l ≤ v j) → i ≤ j} = {v | ∀ l, v l ≤ v j}ᶜ := by
      ext v; simp [hij]
    rw [e]; exact (hA j).compl

section Greedy
variable {k : ℕ} (hk : 0 < k) (H : Fin k → ℕ → ℝ)

/-- play counts of the greedy (largest-top-of-stack) interleaving after `t` plays -/
noncomputable def st : ℕ → Fin k → ℕ
  | 0 => 0
  | t + 1 => st t + Pi.single (amax hk fun i => H i (st t i)) 1

noncomputable def gs (t : ℕ) : Fin k := amax hk fun i => H i (st hk H t i)

noncomputable def gc (t : ℕ) : ℝ := H (gs hk H t) (st hk H t (gs hk H t))

noncomputable def W (t : ℕ) : ℝ := ∑ i, ∑ u ∈ range (st hk H t i), H i u

lemma st_zero (i : Fin k) : st hk H 0 i = 0 := rfl

lemma st_succ (t : ℕ) (i : Fin k) :
    st hk H (t + 1) i = st hk H t i + if i = gs hk H t then 1 else 0 := by
  rw [show st hk H (t + 1) i = st hk H t i + (Pi.single (gs hk H t) (1:ℕ) : Fin k → ℕ) i from rfl]
  by_cases h : i = gs hk H t
  · rw [if_pos h, h, Pi.single_eq_same]
  · rw [if_neg h, Pi.single_eq_of_ne h]

lemma gc_ge (t : ℕ) (i : Fin k) : H i (st hk H t i) ≤ gc hk H t :=
  amax_spec hk (fun i => H i (st hk H t i)) i

lemma st_sum (t : ℕ) : ∑ i, st hk H t i = t := by
  induction t with
  | zero => simp [st_zero]
  | succ t ih =>
    simp only [st_succ, sum_add_distrib, ih, sum_ite_eq', mem_univ, if_true]

lemma st_le (t : ℕ) (i : Fin k) : st hk H t i ≤ t := by
  have h := st_sum hk H t
  calc st hk H t i ≤ ∑ j, st hk H t j := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
    _ = t := h

lemma st_mono (t : ℕ) (i : Fin k) : st hk H t i ≤ st hk H (t + 1) i := by
  rw [st_succ]; omega

lemma W_succ (t : ℕ) : W hk H (t + 1) = W hk H t + gc hk H t := by
  unfold W gc
  have : ∀ i, ∑ u ∈ range (st hk H (t + 1) i), H i u =
      ∑ u ∈ range (st hk H t i), H i u + if i = gs hk H t then H i (st hk H t i) else 0 := by
    intro i
    rw [st_succ]
    split_ifs with h
    · rw [sum_range_succ]
    · simp
  simp only [this, sum_add_distrib, sum_ite_eq', mem_univ, if_true]

lemma W_zero : W hk H 0 = 0 := by simp [W, st_zero]

variable {H}

lemma gc_anti (hH : ∀ i, Antitone (H i)) (t : ℕ) : gc hk H (t + 1) ≤ gc hk H t := by
  calc gc hk H (t + 1) = H (gs hk H (t + 1)) (st hk H (t + 1) (gs hk H (t + 1))) := rfl
    _ ≤ H (gs hk H (t + 1)) (st hk H t (gs hk H (t + 1))) := hH _ (st_mono hk H t _)
    _ ≤ gc hk H t := gc_ge hk H t _

lemma top_le (hH : ∀ i, Antitone (H i)) (t : ℕ) (i : Fin k) (u : ℕ)
    (hu : st hk H (t + 1) i ≤ u) : H i u ≤ gc hk H t := by
  refine (hH i hu).trans ?_
  rw [st_succ]
  split_ifs with h
  · subst h
    exact (hH _ (Nat.le_succ _)).trans le_rfl
  · simpa using gc_ge hk H t i

lemma inv_lo (hH : ∀ i, Antitone (H i)) (t : ℕ) (i : Fin k) (u : ℕ)
    (hu : u < st hk H (t + 1) i) : gc hk H t ≤ H i u := by
  induction t generalizing i u with
  | zero =>
    rw [st_succ, st_zero] at hu
    split_ifs at hu with h
    · have hu0 : u = 0 := by omega
      subst h; subst hu0
      exact le_of_eq (by simp [gc, st_zero])
    · omega
  | succ t ih =>
    rw [st_succ] at hu
    by_cases hlt : u < st hk H (t + 1) i
    · exact (gc_anti hk hH t).trans (ih i u hlt)
    · split_ifs at hu with h
      · have hu' : u = st hk H (t + 1) i := by omega
        subst h; subst hu'
        exact le_rfl
      · omega

lemma gc_nonneg (hH0 : ∀ i u, 0 ≤ H i u) (t : ℕ) : 0 ≤ gc hk H t := hH0 _ _

end Greedy

/-- threshold exchange argument: an allocation that takes every term above `θ` and none
below it maximizes the total among allocations of the same size -/
lemma thresh {ι : Type*} (s : Finset ι) (H : ι → ℕ → ℝ) (g m : ι → ℕ) (θ : ℝ)
    (hsum : ∑ j ∈ s, m j = ∑ j ∈ s, g j)
    (hlo : ∀ j ∈ s, ∀ u < g j, θ ≤ H j u) (hhi : ∀ j ∈ s, ∀ u, g j ≤ u → H j u ≤ θ) :
    ∑ j ∈ s, ∑ u ∈ range (m j), H j u ≤ ∑ j ∈ s, ∑ u ∈ range (g j), H j u := by
  have key : ∀ j ∈ s, ∑ u ∈ range (m j), H j u - ∑ u ∈ range (g j), H j u ≤
      θ * ((m j : ℝ) - g j) := by
    intro j hj
    rcases le_total (m j) (g j) with h | h
    · rw [← sum_range_add_sum_Ico _ h]
      have h1 : ∑ u ∈ Ico (m j) (g j), θ ≤ ∑ u ∈ Ico (m j) (g j), H j u :=
        sum_le_sum fun u hu => hlo j hj u (mem_Ico.1 hu).2
      simp only [sum_const, Nat.card_Ico, nsmul_eq_mul] at h1
      rw [Nat.cast_sub h] at h1
      nlinarith
    · rw [← sum_range_add_sum_Ico _ h]
      have h1 : ∑ u ∈ Ico (g j) (m j), H j u ≤ ∑ u ∈ Ico (g j) (m j), θ :=
        sum_le_sum fun u hu => hhi j hj u (mem_Ico.1 hu).1
      simp only [sum_const, Nat.card_Ico, nsmul_eq_mul] at h1
      rw [Nat.cast_sub h] at h1
      nlinarith
  have h3 := sum_le_sum key
  rw [sum_sub_distrib, ← mul_sum, sum_sub_distrib] at h3
  have h2 : (∑ j ∈ s, (m j : ℝ)) = ∑ j ∈ s, (g j : ℝ) := by exact_mod_cast hsum
  rw [h2, sub_self, mul_zero] at h3
  linarith

lemma pis_of {n : ℕ} (H : Fin n → ℕ → ℝ) (I : Finset (Fin n)) (hI : I ≠ ∅) (t : ℕ)
    (g : Fin n → ℕ) (hg : g ∈ playAllocations I t)
    (hmax : ∀ m ∈ playAllocations I t,
      ∑ j ∈ I, ∑ u ∈ range (m j), H j u ≤ ∑ j ∈ I, ∑ u ∈ range (g j), H j u) :
    partialInterleavedSum H I t = ∑ j ∈ I, ∑ u ∈ range (g j), H j u := by
  unfold partialInterleavedSum
  rw [dif_neg hI]
  exact le_antisymm (sup'_le _ _ hmax)
    (le_sup'_of_le (fun m : Fin n → ℕ => ∑ j ∈ I, ∑ u ∈ range (m j), H j u) hg le_rfl)

/-- `U_t(I)` equals the greedy sum, for stacks indexed through an embedding `e` with image `I`. -/
lemma pis_greedy {k n : ℕ} (hk : 0 < k) (H : Fin k → ℕ → ℝ) (hH : ∀ i, Antitone (H i))
    (e : Fin k ↪ Fin n) (I : Finset (Fin n)) (hIe : I = univ.map e)
    (H' : Fin n → ℕ → ℝ) (hHe : ∀ i u, H' (e i) u = H i u) (t : ℕ) :
    partialInterleavedSum H' I t = W hk H t := by
  have hI : I ≠ ∅ := by
    rw [hIe]; intro h
    have : (⟨0, hk⟩ : Fin k) ∈ (∅ : Finset (Fin k)) := by
      rw [← Finset.map_eq_empty.1 h]; exact mem_univ _
    simp at this
  set g : Fin n → ℕ := fun j => ∑ i, if e i = j then st hk H t i else 0 with hgdef
  have hge : ∀ i, g (e i) = st hk H t i := by
    intro i
    simp only [hgdef, e.injective.eq_iff, sum_ite_eq', mem_univ, if_true]
  have hg0 : ∀ j, j ∉ I → g j = 0 := by
    intro j hj
    refine sum_eq_zero fun i _ => ?_
    rw [if_neg]
    rintro rfl
    exact hj (hIe ▸ mem_map_of_mem e (mem_univ i))
  have hsumI : ∀ F : Fin n → ℝ, ∑ j ∈ I, F j = ∑ i, F (e i) := by
    intro F; rw [hIe, sum_map]
  have hsumIN : ∀ F : Fin n → ℕ, ∑ j ∈ I, F j = ∑ i, F (e i) := by
    intro F; rw [hIe, sum_map]
  have hgsum : ∑ j, g j = t := by
    rw [← sum_subset (subset_univ I) (fun j _ hj => hg0 j hj), hsumIN]
    simp only [hge]
    exact st_sum hk H t
  have hgmem : g ∈ playAllocations I t := by
    simp only [playAllocations, mem_filter, Fintype.mem_piFinset, mem_range]
    refine ⟨fun j => ?_, hg0, hgsum⟩
    have : g j ≤ ∑ j, g j := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ j)
    omega
  have hW : ∑ j ∈ I, ∑ u ∈ range (g j), H' j u = W hk H t := by
    rw [hsumI]
    simp only [hge, hHe]
    rfl
  rw [← hW]
  refine pis_of H' I hI t g hgmem fun m hm => ?_
  simp only [playAllocations, mem_filter] at hm
  have hmsum : ∑ j ∈ I, m j = ∑ j ∈ I, g j := by
    rw [sum_subset (subset_univ I) (fun j _ hj => hm.2.1 j hj),
      sum_subset (subset_univ I) (fun j _ hj => hg0 j hj), hm.2.2, hgsum]
  cases t with
  | zero =>
    have hm0 : ∀ j, m j = 0 := fun j => (sum_eq_zero_iff.1 hm.2.2) j (mem_univ j)
    have hg00 : ∀ j, g j = 0 := fun j => (sum_eq_zero_iff.1 hgsum) j (mem_univ j)
    simp [hm0, hg00]
  | succ t =>
    refine thresh I H' g m (gc hk H t) hmsum ?_ ?_
    · intro j hj u hu
      rw [hIe] at hj
      obtain ⟨i, -, rfl⟩ := mem_map.1 hj
      rw [hge] at hu; rw [hHe]
      exact inv_lo hk hH t i u hu
    · intro j hj u hu
      rw [hIe] at hj
      obtain ⟨i, -, rfl⟩ := mem_map.1 hj
      rw [hge] at hu; rw [hHe]
      exact top_le hk hH t i u hu

end WG5

namespace WG5

open MeasureTheory ProbabilityTheory BanditAlgorithm WeberGittins.Submodular

section Pol
variable {S : Type*} [MeasurableSpace S] {k : ℕ}

/-- deterministic policy playing the argmax of a measurable score of the history -/
noncomputable def detPol (hk : 0 < k) (sc : ∀ n, MarkovBanditHistory k S n → Fin k → ℝ)
    (hsc : ∀ n, Measurable (sc n)) : MarkovBanditPolicy k S where
  select n := Kernel.deterministic (fun h => amax hk (sc n h)) ((amax_meas hk).comp (hsc n))
  markov n := by infer_instance

lemma detPol_apply (hk : 0 < k) (sc : ∀ n, MarkovBanditHistory k S n → Fin k → ℝ)
    (hsc : ∀ n, Measurable (sc n)) (n : ℕ) (h : MarkovBanditHistory k S n) (s : Set (Fin k)) :
    (detPol hk sc hsc).select n h s = Measure.dirac (amax hk (sc n h)) s := by
  simp only [detPol, Kernel.deterministic_apply]

lemma scG_meas {g : S → ℝ} (hg : Measurable g) (n : ℕ) :
    Measurable (fun h : MarkovBanditHistory k S n => fun i => g (h.2 i)) :=
  measurable_pi_lambda _ fun i => hg.comp ((measurable_pi_apply i).comp measurable_snd)

lemma scP_meas {g : S → ℝ} (hg : Measurable g) (n : ℕ) :
    Measurable (fun h : MarkovBanditHistory k S n =>
      fun i => currentHistoryPrevailingCharge g n h i) :=
  measurable_pi_lambda _ fun i => G6cb.chpc_meas hg n i

lemma isGittins (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ) (β : ℝ) (hk : 0 < k)
    (hg : Measurable (gittinsIndex P r β)) :
    IsGittinsIndexPolicy P r β
      (detPol hk (fun n h i => gittinsIndex P r β (h.2 i)) (scG_meas hg)) := by
  intro n h
  rw [detPol_apply]
  exact Measure.dirac_apply_of_mem (amax_spec hk (fun i => gittinsIndex P r β (h.2 i)))

/-- the greedy allocation sequence, truncated to horizon `N` -/
noncomputable def astar (hk : 0 < k) (H : Fin k → ℕ → ℝ) (N : ℕ) : Fin N → Fin k :=
  fun s => gs hk H s

lemma astar_succ (hk : 0 < k) (H : Fin k → ℕ → ℝ) (N : ℕ) :
    astar hk H (N + 1) = Fin.snoc (α := fun _ => Fin k) (astar hk H N) (gs hk H N) := by
  funext s
  refine Fin.lastCases ?_ (fun s' => ?_) s
  · simp [astar, Fin.snoc_last]
  · simp [astar, Fin.snoc_castSucc]

lemma cnt_astar (hk : 0 < k) (H : Fin k → ℕ → ℝ) (N : ℕ) (i : Fin k) :
    G6cb.cnt (astar hk H N) i N = st hk H N i := by
  induction N with
  | zero => rw [G6cb.cnt_zero]; rfl
  | succ N ih =>
    rw [astar_succ, G6cb.cnt_snoc_last, ih, st_succ]
    by_cases h : i = gs hk H N
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]

lemma val_astar (hk : 0 < k) (g : S → ℝ) (β : ℝ) (ω : Fin k → ℕ → S) (N : ℕ) :
    G6cb.val g β (astar hk (G6cb.chg g ω) N) ω =
      ∑ t ∈ Finset.range N, β ^ t * gc hk (G6cb.chg g ω) t := by
  induction N with
  | zero => simp [G6cb.val]
  | succ N ih =>
    rw [astar_succ, G6cb.val_snoc, ih, Finset.sum_range_succ, cnt_astar]
    rfl

lemma lik_astar (hk : 0 < k) {g : S → ℝ} (hg : Measurable g) (ω : Fin k → ℕ → S) (N : ℕ) :
    G6cb.lik (detPol hk (fun n h i => currentHistoryPrevailingCharge g n h i) (scP_meas hg))
      (astar hk (G6cb.chg g ω) N) ω = 1 := by
  induction N with
  | zero => simp [G6cb.lik]
  | succ N ih =>
    rw [astar_succ, G6cb.lik_snoc, ih, one_mul, detPol_apply]
    have e : (fun i => currentHistoryPrevailingCharge g N
        (G6cb.histN (astar hk (G6cb.chg g ω) N) ω) i) =
        fun i => G6cb.chg g ω i (st hk (G6cb.chg g ω) N i) := by
      funext i; rw [G6cb.chpc_histN, cnt_astar]
    rw [e]
    exact Measure.dirac_apply_of_mem (Set.mem_singleton _)

lemma sum_lik (π : MarkovBanditPolicy k S) (ω : Fin k → ℕ → S) :
    ∀ N : ℕ, ∑ a : Fin N → Fin k, G6cb.lik π a ω = 1
  | 0 => by simp [G6cb.lik]
  | N + 1 => by
    rw [← (Fin.snocEquiv (fun _ => Fin k)).sum_comp, Fintype.sum_prod_type]
    have e : ∀ p : Fin k × (Fin N → Fin k),
        (Fin.snocEquiv (fun _ => Fin k)) p = Fin.snoc (α := fun _ => Fin k) p.2 p.1 :=
      fun p => rfl
    simp only [e, G6cb.lik_snoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hs : ∀ h : MarkovBanditHistory k S N, ∑ b : Fin k, (π.select N) h {b} = 1 := by
      intro h
      rw [sum_measure_singleton, Finset.coe_univ, measure_univ]
    simp only [hs, mul_one]
    exact sum_lik π ω N

lemma cnt_sum : ∀ {N : ℕ} (a : Fin N → Fin k) (t : ℕ), t ≤ N → ∑ i, G6cb.cnt a i t = t
  | 0, a, t, ht => by
    have : t = 0 := by omega
    subst this; simp [G6cb.cnt_zero]
  | N + 1, a', t, ht => by
    obtain ⟨a, b, rfl⟩ : ∃ (a : Fin N → Fin k) (b : Fin k),
        a' = Fin.snoc (α := fun _ => Fin k) a b :=
      ⟨Fin.init a', a' (Fin.last N), (Fin.snoc_init_self a').symm⟩
    rcases Nat.lt_or_ge t (N + 1) with h | h
    · simp only [G6cb.cnt_snoc_le a b _ (by omega : t ≤ N)]
      exact cnt_sum a t (by omega)
    · have htN : t = N + 1 := by omega
      subst htN
      simp only [G6cb.cnt_snoc_last, Finset.sum_add_distrib, cnt_sum a N le_rfl,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- cumulative charge paid by the allocation sequence `a` in its first `t` plays -/
noncomputable def X (H : Fin k → ℕ → ℝ) {N : ℕ} (a : Fin N → Fin k) (t : ℕ) : ℝ :=
  ∑ i, ∑ u ∈ Finset.range (G6cb.cnt a i t), H i u

lemma val_X (g : S → ℝ) (β : ℝ) (ω : Fin k → ℕ → S) :
    ∀ {N : ℕ} (a : Fin N → Fin k), G6cb.val g β a ω =
      ∑ t ∈ Finset.range N, β ^ t * (X (G6cb.chg g ω) a (t + 1) - X (G6cb.chg g ω) a t)
  | 0, a => by simp [G6cb.val]
  | N + 1, a' => by
    obtain ⟨a, b, rfl⟩ : ∃ (a : Fin N → Fin k) (b : Fin k),
        a' = Fin.snoc (α := fun _ => Fin k) a b :=
      ⟨Fin.init a', a' (Fin.last N), (Fin.snoc_init_self a').symm⟩
    rw [G6cb.val_snoc, val_X g β ω a, Finset.sum_range_succ]
    congr 1
    · refine Finset.sum_congr rfl fun t ht => ?_
      rw [Finset.mem_range] at ht
      unfold X
      simp only [G6cb.cnt_snoc_le a b _ (by omega : t + 1 ≤ N),
        G6cb.cnt_snoc_le a b _ (by omega : t ≤ N)]
    · unfold X
      simp only [G6cb.cnt_snoc_last, G6cb.cnt_snoc_le a b _ le_rfl]
      congr 1
      have : ∀ i, ∑ u ∈ Finset.range (G6cb.cnt a i N + if b = i then 1 else 0),
          G6cb.chg g ω i u = ∑ u ∈ Finset.range (G6cb.cnt a i N), G6cb.chg g ω i u +
            if b = i then G6cb.chg g ω i (G6cb.cnt a i N) else 0 := by
        intro i
        split_ifs
        · rw [Finset.sum_range_succ]
        · simp
      simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      ring

lemma X_le (hk : 0 < k) (H : Fin k → ℕ → ℝ) {N : ℕ} (a : Fin N → Fin k) (t : ℕ) (ht : t ≤ N) :
    X H a t ≤ partialInterleavedSum H Finset.univ t := by
  have hI : (Finset.univ : Finset (Fin k)) ≠ ∅ :=
    Finset.nonempty_iff_ne_empty.1 ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  unfold partialInterleavedSum
  rw [dif_neg hI]
  have hs := cnt_sum a t ht
  refine Finset.le_sup'_of_le
    (fun m : Fin k → ℕ => ∑ j ∈ Finset.univ, ∑ u ∈ Finset.range (m j), H j u)
    (b := fun i => G6cb.cnt a i t) ?_ le_rfl
  simp only [playAllocations, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  refine ⟨fun j => ?_, fun j hj => absurd (Finset.mem_univ j) hj, hs⟩
  have : G6cb.cnt a j t ≤ ∑ i, G6cb.cnt a i t :=
    Finset.single_le_sum (f := fun i => G6cb.cnt a i t) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
  omega

lemma chg_anti (g : S → ℝ) (ω : Fin k → ℕ → S) (i : Fin k) : Antitone (G6cb.chg g ω i) :=
  antitone_nat_of_succ_le fun u => by rw [G6cb.chg_succ]; exact min_le_left _ _

lemma pis_univ_eq (hk : 0 < k) (g : S → ℝ) (ω : Fin k → ℕ → S) (t : ℕ) :
    partialInterleavedSum (G6cb.chg g ω) Finset.univ t = W hk (G6cb.chg g ω) t :=
  pis_greedy hk (G6cb.chg g ω) (chg_anti g ω) (Function.Embedding.refl _) Finset.univ
    (by rw [Finset.map_refl]) (G6cb.chg g ω) (fun _ _ => rfl) t

/-- `G_N`: the horizon-`N` discounted charge of the nonincreasing interleaving -/
noncomputable def GN (g : S → ℝ) (β : ℝ) (ω : Fin k → ℕ → S) (N : ℕ) : ℝ :=
  ∑ t ∈ Finset.range N, β ^ t * (partialInterleavedSum (G6cb.chg g ω) Finset.univ (t + 1) -
    partialInterleavedSum (G6cb.chg g ω) Finset.univ t)

lemma GN_eq (hk : 0 < k) (g : S → ℝ) (β : ℝ) (ω : Fin k → ℕ → S) (N : ℕ) :
    GN g β ω N = ∑ t ∈ Finset.range N, β ^ t * gc hk (G6cb.chg g ω) t := by
  unfold GN
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [pis_univ_eq hk, pis_univ_eq hk, W_succ]
  ring

lemma val_le_GN (hk : 0 < k) (g : S → ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (ω : Fin k → ℕ → S) {N : ℕ} (a : Fin N → Fin k) : G6cb.val g β a ω ≤ GN g β ω N := by
  rw [val_X, GN, WGRed.abel β _ (by simp [X, G6cb.cnt_zero]) N,
    WGRed.abel β _ (WGRed.pis_zero _ _) N]
  have h1 : ∑ t ∈ Finset.range N, β ^ t * X (G6cb.chg g ω) a (t + 1) ≤
      ∑ t ∈ Finset.range N, β ^ t * partialInterleavedSum (G6cb.chg g ω) Finset.univ (t + 1) :=
    Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_left
      (X_le hk _ a (t + 1) (by rw [Finset.mem_range] at ht; omega)) (pow_nonneg hβ0 t)
  have h2 := mul_le_mul_of_nonneg_left (X_le hk (G6cb.chg g ω) a N le_rfl) (pow_nonneg hβ0 N)
  have h3 := mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ 1 - β)
  linarith

lemma val_astar_eq (hk : 0 < k) (g : S → ℝ) (β : ℝ) (ω : Fin k → ℕ → S) (N : ℕ) :
    G6cb.val g β (astar hk (G6cb.chg g ω) N) ω = GN g β ω N := by
  rw [val_astar, GN_eq hk]

end Pol

end WG5

namespace WG5

open MeasureTheory ProbabilityTheory BanditAlgorithm WeberGittins.Submodular

lemma chg_nonneg {S : Type*} {k : ℕ} {g : S → ℝ} (hg0 : ∀ y, 0 ≤ g y) (ω : Fin k → ℕ → S)
    (i : Fin k) (u : ℕ) : 0 ≤ G6cb.chg g ω i u :=
  Finset.le_inf' _ _ fun v _ => hg0 _

lemma val_nonneg {S : Type*} {k : ℕ} {g : S → ℝ} (hg0 : ∀ y, 0 ≤ g y) {β : ℝ} (hβ0 : 0 ≤ β)
    (ω : Fin k → ℕ → S) {N : ℕ} (a : Fin N → Fin k) : 0 ≤ G6cb.val g β a ω :=
  Finset.sum_nonneg fun t _ => mul_nonneg (pow_nonneg hβ0 _) (chg_nonneg hg0 ω _ _)

/-- the `k`-armed statement (all bandits in play), from the platform's finite-horizon theory -/
theorem main_k {k : ℕ} (hk : 0 < k) {S : Type*} [MeasurableSpace S] [StandardBorelSpace S]
    (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r)
    (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (x : Fin k → S)
    (hacc : ∀ (π πstar : MarkovBanditPolicy k S), IsGittinsIndexPolicy P r β πstar → ∀ N : ℕ,
      (∑ n ∈ Finset.range N, β ^ n * markovBanditRoundReward P r π x n) ≤
          markovBanditFinitePrevailingChargeValue P r β π x N ∧
        markovBanditFinitePrevailingChargeValue P r β πstar x N =
          (∑ n ∈ Finset.range N, β ^ n * markovBanditRoundReward P r πstar x n) +
          β ^ N * markovBanditExpectedRetirementPotential P r β πstar x N)
    (hcmp : ∀ (π πstar : MarkovBanditPolicy k S), IsGittinsIndexPolicy P r β πstar → ∀ N : ℕ,
      markovBanditFinitePrevailingChargeValue P r β π x N ≤
        markovBanditFinitePrevailingChargeValue P r β πstar x N)
    (hpot : ∀ π : MarkovBanditPolicy k S, Filter.Tendsto (fun N ↦ β ^ N *
      markovBanditExpectedRetirementPotential P r β π x N) Filter.atTop (nhds 0))
    (hsumm : ∀ π : MarkovBanditPolicy k S,
      Summable (fun n ↦ β ^ n * markovBanditRoundReward P r π x n)) :
    (⨆ π : MarkovBanditPolicy k S, markovBanditDiscountedValue P r β π x) =
      ∫ ω, ∑' t : ℕ, β ^ t *
          (partialInterleavedSum (prevailingChargeStack P r β ω) Finset.univ (t + 1) -
            partialInterleavedSum (prevailingChargeStack P r β ω) Finset.univ t)
        ∂(Measure.pi fun j => markovChainMeasure P (x j)) := by
  have hint := WGRed.hint_of P hrb hβ0 hβ1
  have hg := G6cb.gi_meas P hr hβ0 hβ1 hint
  have hg0 : ∀ y, 0 ≤ gittinsIndex P r β y := fun y =>
    (hrb.1 y).trans (G6cb.r_le_gi P hr hβ0 hβ1 hint y)
  set γ := gittinsIndex P r β with hγ
  set μ : Measure (Fin k → ℕ → S) := Measure.pi fun j => markovChainMeasure P (x j) with hμ
  have hstack : G6cb.stack P x = μ := rfl
  set D : (Fin k → ℕ → S) → ℝ := fun ω => ∑' t : ℕ, β ^ t *
      (partialInterleavedSum (prevailingChargeStack P r β ω) Finset.univ (t + 1) -
        partialInterleavedSum (prevailingChargeStack P r β ω) Finset.univ t) with hD
  have hDint : Integrable D μ := WGRed.F_int P hr hrb hβ0 hβ1 x Finset.univ
  have hsum : ∀ ω : Fin k → ℕ → S, Summable fun t : ℕ => β ^ t *
      (partialInterleavedSum (prevailingChargeStack P r β ω) Finset.univ (t + 1) -
        partialInterleavedSum (prevailingChargeStack P r β ω) Finset.univ t) := fun ω =>
    WGRed.summ_of hβ0 hβ1 _ _ (WGRed.U_facts P hr hrb hβ0 hβ1 ω Finset.univ).1
      (WGRed.U_facts P hr hrb hβ0 hβ1 ω Finset.univ).2
  have hinc : ∀ (ω : Fin k → ℕ → S) (t : ℕ), 0 ≤ β ^ t *
      (partialInterleavedSum (prevailingChargeStack P r β ω) Finset.univ (t + 1) -
        partialInterleavedSum (prevailingChargeStack P r β ω) Finset.univ t) := by
    intro ω t
    have e1 := pis_univ_eq hk γ ω (t + 1)
    have e2 := pis_univ_eq hk γ ω t
    have e3 := W_succ hk (G6cb.chg γ ω) t
    have e4 := gc_nonneg hk (chg_nonneg hg0 ω) t
    have e5 : (0:ℝ) ≤ β ^ t := pow_nonneg hβ0.le t
    change 0 ≤ β ^ t * (partialInterleavedSum (G6cb.chg γ ω) Finset.univ (t + 1) -
      partialInterleavedSum (G6cb.chg γ ω) Finset.univ t)
    rw [e1, e2, e3]
    nlinarith
  have hGD : ∀ ω N, GN γ β ω N ≤ D ω := fun ω N =>
    Summable.sum_le_tsum (Finset.range N) (fun t _ => hinc ω t) (hsum ω)
  have hG0 : ∀ ω N, 0 ≤ GN γ β ω N := fun ω N =>
    Finset.sum_nonneg fun t _ => hinc ω t
  have hGmeas : ∀ N, Measurable fun ω : Fin k → ℕ → S => GN γ β ω N := by
    intro N
    have hHm : ∀ j u, Measurable fun ω : Fin k → ℕ → S => G6cb.chg γ ω j u :=
      fun j u => G6cb.chg_meas hg j u
    have hUm : ∀ t, Measurable fun ω : Fin k → ℕ → S =>
        partialInterleavedSum (G6cb.chg γ ω) Finset.univ t :=
      fun t => WGRed.pis_meas (fun ω => G6cb.chg γ ω) hHm Finset.univ t
    exact Finset.measurable_sum _ fun t _ => measurable_const.mul ((hUm (t + 1)).sub (hUm t))
  have hGint : ∀ N, Integrable (fun ω : Fin k → ℕ → S => GN γ β ω N) μ := fun N =>
    hDint.mono' (hGmeas N).aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hG0 ω N)]; exact hGD ω N)
  have hvalm : ∀ {N : ℕ} (a : Fin N → Fin k), Measurable fun ω : Fin k → ℕ → S => G6cb.val γ β a ω := by
    intro N a
    exact Finset.measurable_sum _ fun t _ => measurable_const.mul (G6cb.chg_meas hg _ _)
  have hLint : ∀ (π : MarkovBanditPolicy k S) {N : ℕ} (a : Fin N → Fin k),
      Integrable (fun ω : Fin k → ℕ → S => (G6cb.lik π a ω).toReal * G6cb.val γ β a ω) μ := by
    intro π N a
    refine hDint.mono' (((G6cb.lik_meas π a).ennreal_toReal).mul (hvalm a)).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    have h1 : (G6cb.lik π a ω).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using G6cb.lik_le_one π a ω)
    have h2 := val_nonneg hg0 hβ0.le ω a
    have h3 : 0 ≤ (G6cb.lik π a ω).toReal := ENNReal.toReal_nonneg
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h3 h2)]
    calc (G6cb.lik π a ω).toReal * G6cb.val γ β a ω ≤ 1 * G6cb.val γ β a ω :=
          mul_le_mul_of_nonneg_right h1 h2
      _ ≤ GN γ β ω N := by rw [one_mul]; exact val_le_GN hk γ hβ0.le hβ1.le ω a
      _ ≤ D ω := hGD ω N
  have hpc : ∀ (π : MarkovBanditPolicy k S) (N : ℕ),
      markovBanditFinitePrevailingChargeValue P r β π x N =
        ∫ ω, ∑ a : Fin N → Fin k, (G6cb.lik π a ω).toReal * G6cb.val γ β a ω ∂μ := by
    intro π N
    rw [G6cb.main_of_meas P π x hg (fun i u => G6cb.chg_int P hr hβ0 hβ1 hint x i u) N,
      integral_finset_sum _ (fun a _ => hLint π a)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hstack, integral_withDensity_eq_integral_toReal_smul (G6cb.lik_meas π a)
      (ae_of_all _ fun ω => (G6cb.lik_le_one π a ω).trans_lt ENNReal.one_lt_top)]
    rfl
  -- the Gittins index policy and the greedy prevailing-charge policy
  set πs := detPol hk (fun n h i => γ (h.2 i)) (scG_meas hg) with hπs
  have hπsG : IsGittinsIndexPolicy P r β πs := isGittins P r β hk hg
  set πg := detPol hk (fun n h i => currentHistoryPrevailingCharge γ n h i) (scP_meas hg)
    with hπg
  -- (A) every policy is dominated by the expected interleaved charge
  have hA : ∀ π : MarkovBanditPolicy k S, markovBanditDiscountedValue P r β π x ≤ ∫ ω, D ω ∂μ := by
    intro π
    refine le_of_tendsto' (hsumm π).hasSum.tendsto_sum_nat fun N => ?_
    calc (∑ n ∈ Finset.range N, β ^ n * markovBanditRoundReward P r π x n)
        ≤ markovBanditFinitePrevailingChargeValue P r β π x N := (hacc π πs hπsG N).1
      _ = ∫ ω, ∑ a : Fin N → Fin k, (G6cb.lik π a ω).toReal * G6cb.val γ β a ω ∂μ := hpc π N
      _ ≤ ∫ ω, GN γ β ω N ∂μ := by
          refine integral_mono (integrable_finset_sum _ fun a _ => hLint π a) (hGint N) fun ω => ?_
          have hL : ∑ a : Fin N → Fin k, (G6cb.lik π a ω).toReal = 1 := by
            rw [← ENNReal.toReal_sum (fun a _ =>
              ((G6cb.lik_le_one π a ω).trans_lt ENNReal.one_lt_top).ne), sum_lik π ω N]
            rfl
          calc ∑ a : Fin N → Fin k, (G6cb.lik π a ω).toReal * G6cb.val γ β a ω
              ≤ ∑ a : Fin N → Fin k, (G6cb.lik π a ω).toReal * GN γ β ω N :=
                Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
                  (val_le_GN hk γ hβ0.le hβ1.le ω a) ENNReal.toReal_nonneg
            _ = GN γ β ω N := by rw [← Finset.sum_mul, hL, one_mul]
      _ ≤ ∫ ω, D ω ∂μ := integral_mono (hGint N) hDint fun ω => hGD ω N
  -- (B) the Gittins index policy attains it
  have hB : ∫ ω, D ω ∂μ ≤ markovBanditDiscountedValue P r β πs x := by
    have hGt : Filter.Tendsto (fun N => ∫ ω, GN γ β ω N ∂μ) Filter.atTop (nhds (∫ ω, D ω ∂μ)) :=
      tendsto_integral_of_dominated_convergence D (fun N => (hGmeas N).aestronglyMeasurable)
        hDint (fun N => ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hG0 ω N)]; exact hGD ω N)
        (ae_of_all _ fun ω => (hsum ω).hasSum.tendsto_sum_nat)
    have hRt := ((hsumm πs).hasSum.tendsto_sum_nat).add (hpot πs)
    rw [add_zero] at hRt
    refine le_of_tendsto_of_tendsto' hGt hRt fun N => ?_
    calc ∫ ω, GN γ β ω N ∂μ
        ≤ ∫ ω, ∑ a : Fin N → Fin k, (G6cb.lik πg a ω).toReal * G6cb.val γ β a ω ∂μ := by
          refine integral_mono (hGint N) (integrable_finset_sum _ fun a _ => hLint πg a)
            fun ω => ?_
          have h1 : GN γ β ω N = (G6cb.lik πg (astar hk (G6cb.chg γ ω) N) ω).toReal *
              G6cb.val γ β (astar hk (G6cb.chg γ ω) N) ω := by
            rw [lik_astar hk hg ω N, val_astar_eq hk]; simp
          rw [h1]
          exact Finset.single_le_sum
            (f := fun a : Fin N → Fin k => (G6cb.lik πg a ω).toReal * G6cb.val γ β a ω)
            (fun a _ => mul_nonneg ENNReal.toReal_nonneg (val_nonneg hg0 hβ0.le ω a))
            (Finset.mem_univ _)
      _ = markovBanditFinitePrevailingChargeValue P r β πg x N := (hpc πg N).symm
      _ ≤ markovBanditFinitePrevailingChargeValue P r β πs x N := hcmp πg πs hπsG N
      _ = _ := (hacc πg πs hπsG N).2
  haveI : Nonempty (MarkovBanditPolicy k S) := ⟨πs⟩
  have hbdd : BddAbove (Set.range fun π : MarkovBanditPolicy k S =>
      markovBanditDiscountedValue P r β π x) := ⟨∫ ω, D ω ∂μ, by rintro _ ⟨π, rfl⟩; exact hA π⟩
  exact le_antisymm (ciSup_le hA) (hB.trans (le_ciSup hbdd πs))

end WG5

namespace WG5

open MeasureTheory ProbabilityTheory BanditAlgorithm WeberGittins.Submodular

lemma map_restr {n k : ℕ} {S : Type*} [MeasurableSpace S] (μ : Fin n → Measure (ℕ → S))
    [∀ j, IsProbabilityMeasure (μ j)] (e : Fin k ↪ Fin n) :
    Measure.map (fun ω : Fin n → ℕ → S => fun i => ω (e i)) (Measure.pi μ) =
      Measure.pi (fun i => μ (e i)) := by
  have hf : Measurable (fun ω : Fin n → ℕ → S => fun i => ω (e i)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (e i)
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hf (MeasurableSet.univ_pi hs)]
  set s' : Fin n → Set (ℕ → S) := fun j => {y | ∀ i, e i = j → y ∈ s i} with hs'
  have hpre : (fun ω : Fin n → ℕ → S => fun i => ω (e i)) ⁻¹' Set.univ.pi s =
      Set.univ.pi s' := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_univ_pi, hs', Set.mem_setOf_eq]
    constructor
    · rintro h j i rfl; exact h i
    · intro h i; exact h (e i) i rfl
  rw [hpre, Measure.pi_pi]
  have h1 : ∀ i, s' (e i) = s i := by
    intro i; ext y
    simp only [hs', Set.mem_setOf_eq]
    exact ⟨fun h => h i rfl, fun h i' hi' => by rw [e.injective hi']; exact h⟩
  have h2 : ∀ j, j ∉ Finset.univ.map e → s' j = Set.univ := by
    intro j hj; ext y
    simp only [hs', Set.mem_setOf_eq, Set.mem_univ, iff_true]
    intro i hi
    exact absurd (hi ▸ Finset.mem_map_of_mem e (Finset.mem_univ i)) hj
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.map e))
    (fun j _ hj => by rw [h2 j hj, measure_univ]), Finset.prod_map]
  exact Finset.prod_congr rfl fun i _ => by rw [h1]

end WG5

set_option maxHeartbeats 4000000 in
open MeasureTheory ProbabilityTheory BanditAlgorithm WeberGittins.Submodular in
theorem solution {n : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S] (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r)
    (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (x : Fin n → S)
    (I : Finset (Fin n)) :
    restrictedValue P r β x I =
      ∫ ω, ∑' t : ℕ, β ^ t *
          (partialInterleavedSum (prevailingChargeStack P r β ω) I (t + 1) -
            partialInterleavedSum (prevailingChargeStack P r β ω) I t)
        ∂(Measure.pi fun j => markovChainMeasure P (x j)) := by
  by_cases hI : I = ∅
  · subst hI
    simp [restrictedValue, partialInterleavedSum]
  · have hk : 0 < I.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hI)
    have hint := WGRed.hint_of P hrb hβ0 hβ1
    set e : Fin I.card ↪ Fin n := (I.orderEmbOfFin rfl).toEmbedding with he
    have hIe : I = Finset.univ.map e := by
      ext j
      simp only [Finset.mem_map, Finset.mem_univ, true_and, he, RelEmbedding.coe_toEmbedding]
      constructor
      · intro hj
        have : j ∈ Set.range (I.orderEmbOfFin rfl) := by
          rw [Finset.range_orderEmbOfFin]; exact hj
        exact this
      · rintro ⟨i, rfl⟩; exact Finset.orderEmbOfFin_mem I rfl i
    have hpw : ∀ (ω : Fin n → ℕ → S) (t : ℕ),
        partialInterleavedSum (prevailingChargeStack P r β ω) I t =
          partialInterleavedSum (prevailingChargeStack P r β (fun i => ω (e i))) Finset.univ t := by
      intro ω t
      rw [WG5.pis_greedy hk (G6cb.chg (gittinsIndex P r β) (fun i => ω (e i)))
        (WG5.chg_anti _ _) e I hIe (prevailingChargeStack P r β ω) (fun _ _ => rfl) t]
      exact (WG5.pis_univ_eq hk _ _ t).symm
    set x' : Fin I.card → S := fun m => x (I.orderEmbOfFin rfl m) with hx'
    have hmain := WG5.main_k hk P hr hrb hβ0 hβ1 x'
      (fun π πs h N => gittins_finite_prevailing_charge_accounting P hr hβ0 hβ1 hint π πs h x' N)
      (fun π πs h N => gittins_finite_prevailing_charge_interleaving P hr hβ0 hβ1 hint π πs h x' N)
      (fun π => tendsto_gittins_terminal_retirement_potential_zero P hr hβ0 hβ1 hint π x')
      (fun π => summable_discounted_markovBanditRoundReward P hr hβ0 hβ1 hint π x')
    rw [restrictedValue, if_neg hI]
    refine hmain.trans ?_
    have hf : Measurable (fun ω : Fin n → ℕ → S => fun i => ω (e i)) :=
      measurable_pi_lambda _ fun i => measurable_pi_apply (e i)
    have hmap := WG5.map_restr (fun j => markovChainMeasure P (x j)) e
    have hInt : Integrable (fun ω : Fin I.card → ℕ → S => ∑' t : ℕ, β ^ t *
        (partialInterleavedSum (prevailingChargeStack P r β ω) Finset.univ (t + 1) -
          partialInterleavedSum (prevailingChargeStack P r β ω) Finset.univ t))
        (Measure.map (fun ω : Fin n → ℕ → S => fun i => ω (e i))
          (Measure.pi fun j => markovChainMeasure P (x j))) := by
      rw [hmap]; exact WGRed.F_int P hr hrb hβ0 hβ1 x' Finset.univ
    have key := integral_map hf.aemeasurable hInt.aestronglyMeasurable
    rw [hmap] at key
    refine key.trans (integral_congr_ae (ae_of_all _ fun ω => ?_))
    simp only [hpw]
