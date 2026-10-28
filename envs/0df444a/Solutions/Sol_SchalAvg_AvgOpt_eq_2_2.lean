-- Prove2me | solution 1 for SchalAvg.AvgOpt.eq_2_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T09:45:31.896603+00:00
-- url     : https://prove2.me/submissions/c6100006-1cd1-4526-a59d-6cd4f64cd459

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter SchalAvg.AvgOpt

namespace SAeq22

open FeinbergLiang.ACOE

/-! ### Abelian lemma -/

lemma tail_geom (b : ℝ≥0∞) (t : ℕ) :
    ∑' N : ℕ, (if t ≤ N then b ^ N else 0) = b ^ t * (1 - b)⁻¹ := by
  rw [← Summable.sum_add_tsum_nat_add' (k := t) ENNReal.summable]
  have h1 : ∑ i ∈ Finset.range t, (if t ≤ i then b ^ i else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [Finset.mem_range] at hi
    simp [show ¬ t ≤ i by omega]
  rw [h1, zero_add]
  simp only [le_add_iff_nonneg_left, zero_le, if_true, pow_add]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, mul_comm]

lemma abel_ident (a : ℕ → ℝ≥0∞) (b : ℝ≥0∞) (hb : b < 1) :
    ∑' t, b ^ t * a t = (1 - b) * ∑' N : ℕ, b ^ N * ∑ t ∈ Finset.range (N + 1), a t := by
  have e : ∀ N : ℕ, b ^ N * ∑ t ∈ Finset.range (N + 1), a t =
      ∑' t, a t * (if t ≤ N then b ^ N else 0) := by
    intro N
    rw [sum_eq_tsum_indicator, ← ENNReal.tsum_mul_left]
    congr 1; ext t
    by_cases h : t ≤ N
    · simp [Set.indicator, Finset.mem_range, Nat.lt_succ_iff.mpr h, h, mul_comm]
    · simp [Set.indicator, Finset.mem_range, h, show ¬ t < N + 1 by omega]
  simp_rw [e]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left, tail_geom]
  rw [← ENNReal.tsum_mul_left]
  congr 1; ext t
  have h0 : (1 - b) ≠ 0 := (tsub_pos_of_lt hb).ne'
  have ht : (1 - b) ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
  calc b ^ t * a t = b ^ t * a t * ((1 - b) * (1 - b)⁻¹) := by
        rw [ENNReal.mul_inv_cancel h0 ht, mul_one]
    _ = (1 - b) * (a t * (b ^ t * (1 - b)⁻¹)) := by ring

lemma abel_core (a : ℕ → ℝ≥0∞) (C L' : ℝ≥0∞)
    (hS : ∀ N : ℕ, ∑ t ∈ Finset.range N, a t ≤ C + N * L') (b : ℝ≥0∞) (hb : b < 1) :
    (1 - b) * ∑' t, b ^ t * a t ≤ (1 - b) * C + L' := by
  have h0 : (1 - b) ≠ 0 := (tsub_pos_of_lt hb).ne'
  have ht : (1 - b) ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
  have hone := abel_ident (fun _ => (1 : ℝ≥0∞)) b hb
  simp only [mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul, one_mul] at hone
  rw [ENNReal.tsum_geometric] at hone
  push_cast at hone
  rw [abel_ident a b hb]
  set k := (1 - b)⁻¹ with hk
  set s := ∑' N : ℕ, b ^ N * ((N : ℝ≥0∞) + 1) with hs
  have hk1 : (1 - b) * k = 1 := ENNReal.mul_inv_cancel h0 ht
  have hsplit : ∑' N : ℕ, b ^ N * (C + ((N + 1 : ℕ) : ℝ≥0∞) * L') = C * k + L' * s := by
    have e : ∀ N : ℕ, b ^ N * (C + ((N + 1 : ℕ) : ℝ≥0∞) * L') =
        C * b ^ N + L' * (b ^ N * ((N : ℝ≥0∞) + 1)) := fun N => by push_cast; ring
    simp_rw [e]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  calc (1 - b) * ((1 - b) * ∑' N : ℕ, b ^ N * ∑ t ∈ Finset.range (N + 1), a t)
      ≤ (1 - b) * ((1 - b) * ∑' N : ℕ, b ^ N * (C + ((N + 1 : ℕ) : ℝ≥0∞) * L')) := by
        gcongr with N
        exact hS (N + 1)
    _ = (1 - b) * C * ((1 - b) * k) + L' * ((1 - b) * ((1 - b) * s)) := by
        rw [hsplit]; ring
    _ = (1 - b) * C + L' := by
        rw [← hone, hk1, mul_one, mul_one]

lemma abel (a : ℕ → ℝ≥0∞) :
    limsup (fun β : ℝ => ENNReal.ofReal (1 - β) * ∑' t, ENNReal.ofReal (β ^ t) * a t) (𝓝[<] 1)
      ≤ limsup (fun N : ℕ => (N : ℝ≥0∞)⁻¹ * ∑ t ∈ Finset.range N, a t) atTop := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro L' hL'
  rcases eq_or_ne L' ⊤ with rfl | hLt
  · exact le_top
  have hev := Filter.eventually_lt_of_limsup_lt hL'
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 hev
  set N1 := max N0 1
  set S := fun N => ∑ t ∈ Finset.range N, a t
  have hbig : ∀ N ≥ N1, S N ≤ N * L' := by
    intro N hN
    have hN1 : (N : ℝ≥0∞) ≠ 0 := by
      have : 1 ≤ N := le_trans (le_max_right _ _) hN
      exact_mod_cast (show N ≠ 0 by omega)
    have := (hN0 N (le_trans (le_max_left _ _) hN)).le
    calc S N = N * ((N : ℝ≥0∞)⁻¹ * S N) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hN1 (ENNReal.natCast_ne_top N), one_mul]
      _ ≤ N * L' := by gcongr
  have hS : ∀ N : ℕ, S N ≤ S N1 + N * L' := by
    intro N
    rcases le_or_gt N N1 with h | h
    · exact le_add_right (Finset.sum_le_sum_of_subset (Finset.range_mono h))
    · exact le_add_left (hbig N h.le)
  have hCfin : S N1 ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hLt) (hbig N1 le_rfl)
  have hlim : Tendsto (fun β : ℝ => ENNReal.ofReal (1 - β) * S N1 + L') (𝓝[<] 1) (𝓝 L') := by
    have h1 : Tendsto (fun β : ℝ => ENNReal.ofReal (1 - β)) (𝓝[<] 1) (𝓝 0) := by
      have : Tendsto (fun β : ℝ => 1 - β) (𝓝 (1 : ℝ)) (𝓝 0) := by
        have := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_id (x := 𝓝 (1 : ℝ)))
        simpa using this
      have := (ENNReal.tendsto_ofReal this).mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
      simpa using this
    have := (ENNReal.Tendsto.mul_const h1 (Or.inr hCfin)).add_const L'
    simpa using this
  rw [← hlim.limsup_eq]
  apply limsup_le_limsup _ (by isBoundedDefault) (by isBoundedDefault)
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with β hβ
  have hb : ENNReal.ofReal β < 1 := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hβ.2
  have e1 : ENNReal.ofReal (1 - β) = 1 - ENNReal.ofReal β := by
    rw [ENNReal.ofReal_sub _ hβ.1.le, ENNReal.ofReal_one]
  have e2 : ∀ t : ℕ, ENNReal.ofReal (β ^ t) = ENNReal.ofReal β ^ t :=
    fun t => ENNReal.ofReal_pow hβ.1.le t
  simp only [e1, e2]
  exact abel_core a (S N1) L' hS _ hb

/-! ### Path-measure lemmas -/

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

instance initP (π : Policy X A) (x : X) : IsProbabilityMeasure (initMeasure π x) := by
  unfold initMeasure; exact Measure.isProbabilityMeasure_map (by fun_prop)

instance pathP (M : MDP X A) (π : Policy X A) (x : X) :
    IsProbabilityMeasure (pathMeasure M π x) := by
  unfold pathMeasure; infer_instance

lemma path_zero (M : MDP X A) (π : Policy X A) (x : X) {F : X × A → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ ω, F (ω 0) ∂(pathMeasure M π x) = ∫⁻ p, F p ∂(initMeasure π x) := by
  unfold pathMeasure Kernel.trajMeasure
  rw [Measure.lintegral_bind (f := fun ω : ℕ → X × A => F (ω 0)) (Kernel.aemeasurable _) (hF.comp (measurable_pi_apply 0)).aemeasurable]
  have hz : ∀ x₀ : (Π _ : Finset.Iic 0, X × A),
      ∫⁻ ω, F (ω 0) ∂(Kernel.traj (X := fun _ => X × A) (stepKernel M π) 0 x₀) = F (x₀ ⟨0, by simp⟩) := by
    intro x₀
    have hm : Measurable (fun y : (Π _ : Finset.Iic 0, X × A) => F (y ⟨0, by simp⟩)) :=
      hF.comp (measurable_pi_apply _)
    have : ∫⁻ ω, F (ω 0) ∂(Kernel.traj (X := fun _ => X × A) (stepKernel M π) 0 x₀) =
        ∫⁻ y, F (y ⟨0, by simp⟩) ∂((Kernel.traj (X := fun _ => X × A) (stepKernel M π) 0 x₀).map
          (Preorder.frestrictLe 0)) := by
      rw [lintegral_map hm (by fun_prop)]; rfl
    rw [this, ← Kernel.map_apply _ (by fun_prop),
      Kernel.traj_map_frestrictLe_of_le (le_refl 0), Kernel.lintegral_deterministic' _ hm]
    rfl
  simp_rw [hz]
  rw [lintegral_map (f := fun y : (Π _ : Finset.Iic 0, X × A) => F (y ⟨0, by simp⟩))
    (hF.comp (measurable_pi_apply _)) (by fun_prop)]
  rfl

lemma path_succ (M : MDP X A) (π : Policy X A) (x : X) (t : ℕ) {F : X × A → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ ω, F (ω (t + 1)) ∂(pathMeasure M π x) =
      ∫⁻ ω, ∫⁻ p, F p ∂(stepKernel M π t (Preorder.frestrictLe t ω)) ∂(pathMeasure M π x) := by
  have h1 : ∫⁻ ω, F (ω (t + 1)) ∂(pathMeasure M π x) =
      ∫⁻ z, F z.2 ∂((pathMeasure M π x).map (fun ω => (Preorder.frestrictLe t ω, ω (t + 1)))) := by
    rw [lintegral_map (f := fun z : (Π _ : Finset.Iic t, X × A) × (X × A) => F z.2)
      (hF.comp measurable_snd) (by fun_prop)]
  rw [h1]
  unfold pathMeasure
  rw [← Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure,
    Measure.lintegral_compProd (f := fun z : (Π _ : Finset.Iic t, X × A) × (X × A) => F z.2)
      (hF.comp measurable_snd),
    lintegral_map (hF.lintegral_kernel) (by fun_prop)]

lemma step_stat (M : MDP X A) (φ : X → A) (hφ : Measurable φ) (t : ℕ)
    (h : Π _ : Finset.Iic t, X × A) {F : X × A → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F p ∂(stepKernel M (Policy.ofStationary φ hφ) t h) =
      ∫⁻ y, F (y, φ y) ∂(M.q (lastPair t h)) := by
  have : IsMarkovKernel (M.q.comap (lastPair (X := X) (A := A) t) (measurable_pi_apply _)) :=
    Kernel.IsMarkovKernel.comap _ _
  unfold stepKernel
  rw [Kernel.lintegral_compProd _ _ _ hF]
  simp only [Kernel.comap_apply, Policy.ofStationary]
  congr 1; ext y
  rw [Kernel.lintegral_deterministic' (f := fun c => F (y, c)) _ (hF.comp measurable_prodMk_left)]

lemma init_stat (φ : X → A) (hφ : Measurable φ) (x : X) {F : X × A → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ p, F p ∂(initMeasure (Policy.ofStationary φ hφ) x) = F (x, φ x) := by
  unfold initMeasure
  rw [lintegral_map hF (by fun_prop)]
  simp only [Policy.ofStationary]
  rw [Kernel.lintegral_deterministic' (f := fun c => F (x, c)) _ (hF.comp measurable_prodMk_left)]

lemma law_stat (M : MDP X A) (φ : X → A) (hφ : Measurable φ) (x : X) (t : ℕ)
    {F : X × A → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (ω t) ∂(pathMeasure M (Policy.ofStationary φ hφ) x) =
      ∫⁻ ω, F ((ω t).1, φ (ω t).1) ∂(pathMeasure M (Policy.ofStationary φ hφ) x) := by
  have hF' : Measurable (fun p : X × A => F (p.1, φ p.1)) :=
    hF.comp (measurable_fst.prodMk (hφ.comp measurable_fst))
  cases t with
  | zero =>
    rw [path_zero _ _ _ hF, path_zero _ _ _ hF', init_stat _ _ _ hF, init_stat _ _ _ hF']
  | succ t =>
    rw [path_succ _ _ _ _ hF, path_succ _ _ _ _ hF']
    simp_rw [step_stat _ _ _ _ _ hF, step_stat _ _ _ _ _ hF']

/-! ### The iteration bound -/

lemma Jn_eq (M : MDP X A) (hc : Measurable (fun p : X × A => M.cost p.1 p.2))
    (π : Policy X A) (n : ℕ) (x : X) :
    vN M π n 1 x = ∑ t ∈ Finset.range n, ∫⁻ ω, M.cost (ω t).1 (ω t).2 ∂(pathMeasure M π x) := by
  unfold vN
  simp only [one_pow, ENNReal.ofReal_one, one_mul]
  rw [lintegral_finsetSum]
  intro t _
  exact hc.comp (measurable_pi_apply t)

lemma Jb_eq (M : MDP X A) (hc : Measurable (fun p : X × A => M.cost p.1 p.2))
    (π : Policy X A) (β : ℝ) (x : X) :
    vDisc M π β x = ∑' t, ENNReal.ofReal (β ^ t) *
      ∫⁻ ω, M.cost (ω t).1 (ω t).2 ∂(pathMeasure M π x) := by
  unfold vDisc
  rw [lintegral_tsum]
  · congr 1; ext t
    rw [lintegral_const_mul (f := fun ω : ℕ → X × A => M.cost (ω t).1 (ω t).2) _ (hc.comp (measurable_pi_apply t))]
  · intro t
    exact ((hc.comp (measurable_pi_apply t)).const_mul _).aemeasurable


lemma abel_fin (a : ℕ → ℝ≥0∞)
    (hfin : limsup (fun N : ℕ => (N : ℝ≥0∞)⁻¹ * ∑ t ∈ Finset.range N, a t) atTop < ⊤)
    (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) :
    ∑' t, ENNReal.ofReal (β ^ t) * a t < ⊤ := by
  obtain ⟨L', hL', hLt'⟩ := exists_between hfin
  have hLt : L' ≠ ⊤ := hLt'.ne
  have hev := Filter.eventually_lt_of_limsup_lt hL'
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 hev
  set N1 := max N0 1
  set S := fun N => ∑ t ∈ Finset.range N, a t
  have hbig : ∀ N ≥ N1, S N ≤ N * L' := by
    intro N hN
    have hN1 : (N : ℝ≥0∞) ≠ 0 := by
      have : 1 ≤ N := le_trans (le_max_right _ _) hN
      exact_mod_cast (show N ≠ 0 by omega)
    have := (hN0 N (le_trans (le_max_left _ _) hN)).le
    calc S N = N * ((N : ℝ≥0∞)⁻¹ * S N) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hN1 (ENNReal.natCast_ne_top N), one_mul]
      _ ≤ N * L' := by gcongr
  have hS : ∀ N : ℕ, S N ≤ S N1 + N * L' := by
    intro N
    rcases le_or_gt N N1 with h | h
    · exact le_add_right (Finset.sum_le_sum_of_subset (Finset.range_mono h))
    · exact le_add_left (hbig N h.le)
  have hCfin : S N1 ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hLt) (hbig N1 le_rfl)
  have hb : ENNReal.ofReal β < 1 := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hβ.2
  have e2 : ∀ t : ℕ, ENNReal.ofReal (β ^ t) = ENNReal.ofReal β ^ t :=
    fun t => ENNReal.ofReal_pow hβ.1.le t
  simp only [e2]
  have hc := abel_core a (S N1) L' hS _ hb
  have h0 : (1 - ENNReal.ofReal β) ≠ 0 := (tsub_pos_of_lt hb).ne'
  have hr : (1 - ENNReal.ofReal β) * ∑' t, ENNReal.ofReal β ^ t * a t < ⊤ :=
    lt_of_le_of_lt hc (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top
      (ENNReal.sub_ne_top ENNReal.one_ne_top).lt_top hCfin.lt_top, hLt.lt_top⟩)
  by_contra hcon
  rw [not_lt, top_le_iff] at hcon
  rw [hcon, ENNReal.mul_top h0] at hr
  exact lt_irrefl _ hr

/-! ### Bellman equation for a stationary policy -/

noncomputable def Pop (M : MDP X A) (f : X → A) (g : X → ℝ≥0∞) : X → ℝ≥0∞ :=
  fun x => ∫⁻ y, g y ∂(M.q (x, f x))

lemma Pop_meas (M : MDP X A) {f : X → A} (hf : Measurable f) {g : X → ℝ≥0∞}
    (hg : Measurable g) : Measurable (Pop M f g) :=
  hg.lintegral_kernel.comp (measurable_id.prodMk hf)

lemma Pop_iter_meas (M : MDP X A) {f : X → A} (hf : Measurable f) (t : ℕ) {g : X → ℝ≥0∞}
    (hg : Measurable g) : Measurable ((Pop M f)^[t] g) := by
  induction t generalizing g with
  | zero => exact hg
  | succ t ih => rw [Function.iterate_succ_apply]; exact ih (Pop_meas M hf hg)

lemma law_iter (M : MDP X A) (f : X → A) (hf : Measurable f) (t : ℕ) :
    ∀ (x : X) {F : X × A → ℝ≥0∞}, Measurable F →
      ∫⁻ ω, F (ω t) ∂(pathMeasure M (Policy.ofStationary f hf) x) =
        (Pop M f)^[t] (fun y => F (y, f y)) x := by
  induction t with
  | zero =>
    intro x F hF
    rw [path_zero _ _ _ hF, init_stat _ _ _ hF]; rfl
  | succ t ih =>
    intro x F hF
    rw [path_succ _ _ _ _ hF]
    simp_rw [step_stat _ _ _ _ _ hF]
    have e1 : ∀ ω : ℕ → X × A, lastPair t (Preorder.frestrictLe t ω) = ω t := fun ω => rfl
    simp_rw [e1]
    have hG : Measurable (fun p : X × A => ∫⁻ y, F (y, f y) ∂(M.q p)) :=
      (hF.comp (measurable_id.prodMk hf)).lintegral_kernel
    rw [ih x hG, Function.iterate_succ_apply]
    rfl

lemma bellman (M : MDP X A) (hc : Measurable (fun p : X × A => M.cost p.1 p.2))
    (f : X → A) (hf : Measurable f) (β : ℝ) (hβ : 0 ≤ β) (x : X) :
    vDisc M (Policy.ofStationary f hf) β x = M.cost x (f x) +
      ENNReal.ofReal β * ∫⁻ y, vDisc M (Policy.ofStationary f hf) β y ∂(M.q (x, f x)) := by
  have hc' : Measurable (fun y => M.cost y (f y)) := hc.comp (measurable_id.prodMk hf)
  have ha : ∀ t y, ∫⁻ ω, M.cost (ω t).1 (ω t).2 ∂(pathMeasure M (Policy.ofStationary f hf) y) =
      (Pop M f)^[t] (fun y => M.cost y (f y)) y := fun t y =>
    law_iter M f hf t y (F := fun p : X × A => M.cost p.1 p.2) hc
  have hv : ∀ y, vDisc M (Policy.ofStationary f hf) β y =
      ∑' t, ENNReal.ofReal (β ^ t) * (Pop M f)^[t] (fun y => M.cost y (f y)) y := by
    intro y; rw [Jb_eq M hc]; simp_rw [ha]
  rw [hv x, lintegral_congr (fun y => hv y)]
  rw [tsum_eq_zero_add' ENNReal.summable]
  rw [pow_zero, ENNReal.ofReal_one, one_mul, Function.iterate_zero_apply]
  congr 1
  rw [lintegral_tsum (fun t => ((Pop_iter_meas M hf t hc').const_mul _).aemeasurable),
    ← ENNReal.tsum_mul_left]
  congr 1; ext t
  rw [lintegral_const_mul _ (Pop_iter_meas M hf t hc'), ← mul_assoc,
    ← ENNReal.ofReal_mul hβ, ← pow_succ', Function.iterate_succ_apply']
  rfl

theorem main {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (M : Model S A) (hGA : GeneralAssumption M)
    (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (f : S → A) (hf : IsDiscOptimal M β f) (x : S) :
    wβ M β x + ENNReal.ofReal (1 - β) * mβ M β =
      M.toMDP.cost x (f x) + ENNReal.ofReal β * ∫⁻ y, wβ M β y ∂(M.toMDP.q (x, f x)) := by
  obtain ⟨hfs, hopt⟩ := hf
  have hm : mβ M β ≠ ⊤ := by
    unfold GeneralAssumption gStar at hGA
    obtain ⟨x0, h1⟩ := iInf_lt_iff.1 hGA
    obtain ⟨π, h2⟩ := iInf_lt_iff.1 h1
    have hJ : Jbeta M π.1 β x0 < ⊤ := by
      unfold Jbeta; rw [Jb_eq _ M.cost_meas]
      apply abel_fin _ _ β hβ
      unfold Phi avgCost at h2
      simp_rw [Jn_eq _ M.cost_meas] at h2
      exact h2
    exact ne_top_of_le_ne_top hJ.ne ((iInf_le _ x0).trans
      (iInf_le (fun π : {π : Policy S A // Admissible M π} => Jbeta M π.1 β x0) π))
  have hvm : ∀ y, mβ M β ≤ vβ M β y := fun y => iInf_le _ y
  have hB : vβ M β x = M.toMDP.cost x (f x) +
      ENNReal.ofReal β * ∫⁻ y, vβ M β y ∂(M.toMDP.q (x, f x)) := by
    rw [← hopt x]
    simp_rw [← hopt]
    exact bellman M.toMDP M.cost_meas f hfs.1 β hβ.1.le x
  unfold wβ
  set m := mβ M β
  set v := vβ M β
  apply (ENNReal.add_left_inj (a := ENNReal.ofReal β * m)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm)).1
  have hsum : ENNReal.ofReal (1 - β) + ENNReal.ofReal β = 1 := by
    rw [← ENNReal.ofReal_add (by linarith [hβ.2]) hβ.1.le]; norm_num
  calc v x - m + ENNReal.ofReal (1 - β) * m + ENNReal.ofReal β * m
      = v x - m + m := by rw [add_assoc, ← add_mul, hsum, one_mul]
    _ = v x := tsub_add_cancel_of_le (hvm x)
    _ = M.toMDP.cost x (f x) + ENNReal.ofReal β * ∫⁻ y, v y ∂(M.toMDP.q (x, f x)) := hB
    _ = M.toMDP.cost x (f x) + ENNReal.ofReal β * ∫⁻ y, (v y - m + m) ∂(M.toMDP.q (x, f x)) := by
        congr 3; ext y; exact (tsub_add_cancel_of_le (hvm y)).symm
    _ = M.toMDP.cost x (f x) + ENNReal.ofReal β * ∫⁻ y, v y - m ∂(M.toMDP.q (x, f x)) +
          ENNReal.ofReal β * m := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
          mul_add, add_assoc]

end SAeq22

open SchalAvg.AvgOpt in
theorem solution {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [TopologicalSpace S]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (M : Model S A) (hGA : GeneralAssumption M) (hWS : CondW M ∨ CondS M)
    (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (f : S → A) (hf : IsDiscOptimal M β f) (x : S) :
    wβ M β x + ENNReal.ofReal (1 - β) * mβ M β =
      M.toMDP.cost x (f x) + ENNReal.ofReal β * ∫⁻ y, wβ M β y ∂(M.toMDP.q (x, f x)) :=
  SAeq22.main M hGA β hβ f hf x
