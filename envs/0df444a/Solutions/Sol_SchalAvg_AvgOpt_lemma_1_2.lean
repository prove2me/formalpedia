-- Prove2me | solution 1 for SchalAvg.AvgOpt.lemma_1_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T09:31:25.560265+00:00
-- url     : https://prove2.me/submissions/74b910b2-2f3e-4a6e-a40a-ab2fab6717f2

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model
import Definitions.Def_FKZAvg_WStar_Assumptions

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter SchalAvg.AvgOpt

namespace FKZS201

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

/-! ### Main argument -/

open FKZAvg.WStar

lemma step_ineq (M : Model X A) (u : X → ℝ≥0∞) (hu : Measurable u) (φ : X → A)
    (hφ : IsStationary M φ) (g : ℝ≥0∞)
    (h9 : ∀ x, M.toMDP.cost x (φ x) + ∫⁻ y, u y ∂(M.toMDP.q (x, φ x)) ≤ g + u x) (x : X) (t : ℕ) :
    (∫⁻ ω, M.toMDP.cost (ω t).1 (ω t).2 ∂(pathMeasure M.toMDP (statPolicy hφ) x)) +
      ∫⁻ ω, u (ω (t + 1)).1 ∂(pathMeasure M.toMDP (statPolicy hφ) x) ≤
      g + ∫⁻ ω, u (ω t).1 ∂(pathMeasure M.toMDP (statPolicy hφ) x) := by
  have hc := M.cost_meas
  have hG : Measurable (fun p : X × A => ∫⁻ y, u y ∂(M.toMDP.q p)) := hu.lintegral_kernel
  change (∫⁻ ω, M.toMDP.cost (ω t).1 (ω t).2
      ∂(pathMeasure M.toMDP (Policy.ofStationary φ hφ.1) x)) +
      ∫⁻ ω, u (ω (t + 1)).1 ∂(pathMeasure M.toMDP (Policy.ofStationary φ hφ.1) x) ≤
      g + ∫⁻ ω, u (ω t).1 ∂(pathMeasure M.toMDP (Policy.ofStationary φ hφ.1) x)
  rw [path_succ (F := fun p : X × A => u p.1) _ _ _ _ (hu.comp measurable_fst)]
  simp_rw [step_stat (F := fun p : X × A => u p.1) _ _ _ _ _ (hu.comp measurable_fst)]
  have e1 : ∀ ω : ℕ → X × A, lastPair t (Preorder.frestrictLe t ω) = ω t := fun ω => rfl
  simp_rw [e1]
  rw [← lintegral_add_left (f := fun ω : ℕ → X × A => M.toMDP.cost (ω t).1 (ω t).2)
    (hc.comp (measurable_pi_apply t))]
  rw [law_stat (F := fun p : X × A => M.toMDP.cost p.1 p.2 + ∫⁻ y, u y ∂(M.toMDP.q p))
    _ _ hφ.1 _ _ (hc.add hG)]
  calc ∫⁻ ω, M.toMDP.cost (ω t).1 (φ (ω t).1) + ∫⁻ y, u y ∂(M.toMDP.q ((ω t).1, φ (ω t).1))
        ∂(pathMeasure M.toMDP (Policy.ofStationary φ hφ.1) x)
      ≤ ∫⁻ ω, g + u (ω t).1 ∂(pathMeasure M.toMDP (Policy.ofStationary φ hφ.1) x) :=
        lintegral_mono (fun ω => h9 _)
    _ = _ := by
        rw [lintegral_add_left measurable_const]
        simp

lemma iter (M : Model X A) (u : X → ℝ≥0∞) (hu : Measurable u) (φ : X → A)
    (hφ : IsStationary M φ) (g : ℝ≥0∞)
    (h9 : ∀ x, M.toMDP.cost x (φ x) + ∫⁻ y, u y ∂(M.toMDP.q (x, φ x)) ≤ g + u x) (x : X) (n : ℕ) :
    vN M.toMDP (statPolicy hφ) n 1 x +
      ∫⁻ ω, u (ω n).1 ∂(pathMeasure M.toMDP (statPolicy hφ) x) ≤ n * g + u x := by
  induction n with
  | zero =>
    have h0 : ∫⁻ ω, u (ω 0).1 ∂(pathMeasure M.toMDP (statPolicy hφ) x) = u x := by
      change ∫⁻ ω, u (ω 0).1 ∂(pathMeasure M.toMDP (Policy.ofStationary φ hφ.1) x) = u x
      rw [path_zero (F := fun p : X × A => u p.1) _ _ _ (hu.comp measurable_fst),
        init_stat (F := fun p : X × A => u p.1) _ _ _ (hu.comp measurable_fst)]
    simp [vN, h0]
  | succ n ih =>
    rw [Jn_eq _ M.cost_meas] at ih ⊢
    rw [Finset.sum_range_succ, add_assoc]
    calc _ ≤ (∑ t ∈ Finset.range n,
          ∫⁻ ω, M.toMDP.cost (ω t).1 (ω t).2 ∂(pathMeasure M.toMDP (statPolicy hφ) x)) +
          (g + ∫⁻ ω, u (ω n).1 ∂(pathMeasure M.toMDP (statPolicy hφ) x)) := by
          exact add_le_add_right (step_ineq M u hu φ hφ g h9 x n) _
      _ = g + ((∑ t ∈ Finset.range n,
          ∫⁻ ω, M.toMDP.cost (ω t).1 (ω t).2 ∂(pathMeasure M.toMDP (statPolicy hφ) x)) +
          ∫⁻ ω, u (ω n).1 ∂(pathMeasure M.toMDP (statPolicy hφ) x)) := by ring
      _ ≤ g + (n * g + u x) := by gcongr
      _ = ((n + 1 : ℕ) : ℝ≥0∞) * g + u x := by push_cast; ring

lemma phi_le (M : Model X A) (u : X → ℝ≥0∞) (hu : Measurable u) (hu_fin : ∀ x, u x ≠ ⊤)
    (φ : X → A) (hφ : IsStationary M φ) (g : ℝ≥0∞)
    (h9 : ∀ x, M.toMDP.cost x (φ x) + ∫⁻ y, u y ∂(M.toMDP.q (x, φ x)) ≤ g + u x) (x : X) :
    Phi M (statPolicy hφ) x ≤ g := by
  unfold Phi avgCost
  have hlim : Tendsto (fun N : ℕ => g + (N : ℝ≥0∞)⁻¹ * u x) atTop (𝓝 (g)) := by
    have := (ENNReal.Tendsto.mul_const ENNReal.tendsto_inv_nat_nhds_zero
      (Or.inr (hu_fin x))).const_add (g)
    simpa using this
  rw [← hlim.limsup_eq]
  apply limsup_le_limsup _ (by isBoundedDefault) (by isBoundedDefault)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hb : vN M.toMDP (statPolicy hφ) N 1 x ≤ N * g + u x :=
    le_trans le_self_add (iter M u hu φ hφ g h9 x N)
  calc (N : ℝ≥0∞)⁻¹ * vN M.toMDP (statPolicy hφ) N 1 x
      ≤ (N : ℝ≥0∞)⁻¹ * (N * g + u x) := by gcongr
    _ = g + (N : ℝ≥0∞)⁻¹ * u x := by
        rw [mul_add, ← mul_assoc, ENNReal.inv_mul_cancel hN0 (ENNReal.natCast_ne_top N), one_mul]

lemma abel_policy (M : Model X A) (π : Policy X A) (x : X) :
    limsup (fun β : ℝ => ENNReal.ofReal (1 - β) * Jbeta M π β x) (𝓝[<] 1) ≤ Phi M π x := by
  unfold Jbeta Phi avgCost
  simp_rw [Jb_eq _ M.cost_meas, Jn_eq _ M.cost_meas]
  exact abel _

lemma statPolicy_adm (M : Model X A) (φ : X → A) (hφ : IsStationary M φ) :
    Admissible M (statPolicy hφ) := by
  intro t h
  have hm : MeasurableSet (M.Aset h.2) :=
    M.graph_meas.preimage (measurable_prodMk_left (x := h.2))
  have hφm : Measurable φ := hφ.1
  show (Policy.ofStationary φ hφm).rule t h (M.Aset h.2)ᶜ = 0
  simp only [Policy.ofStationary]
  rw [Kernel.deterministic_apply' _ _ hm.compl]
  simp [hφ.2 h.2]

theorem main {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (M : Model X A) (u : X → ℝ≥0∞) (hu : Measurable u) (hu_fin : ∀ x, u x ≠ ⊤)
    (φ : X → A) (hφ : IsStationary M φ) (h9 : Ineq9 M u φ) :
    IsAvgOpt M hφ ∧ Eq10 M hφ := by
  set L := fun x => limsup (fun α : ℝ => ENNReal.ofReal (1 - α) * vβ M α x) (𝓝[<] 1) with hL
  have hLw : ∀ x, L x ≤ wAvg M x := by
    intro x
    apply le_iInf
    intro π
    refine le_trans ?_ (abel_policy M π.1 x)
    apply limsup_le_limsup _ (by isBoundedDefault) (by isBoundedDefault)
    exact Eventually.of_forall (fun β => mul_le_mul_of_nonneg_left
      (iInf_le (fun π : {π : Policy X A // Admissible M π} => Jbeta M π.1 β x) π) zero_le)
  have hgL : ∀ x, gUpper M ≤ L x := by
    intro x
    apply limsup_le_limsup _ (by isBoundedDefault) (by isBoundedDefault)
    exact Eventually.of_forall (fun β => mul_le_mul_of_nonneg_left (iInf_le (fun x => vβ M β x) x) zero_le)
  have hgs : gUpper M ≤ gStar M := le_iInf (fun x => (hgL x).trans (hLw x))
  have hsw : ∀ x, gStar M ≤ wAvg M x := fun x => iInf_le (fun x => wAvg M x) x
  have hwp : ∀ x, wAvg M x ≤ Phi M (statPolicy hφ) x := fun x =>
    iInf_le (fun π : {π : Policy X A // Admissible M π} => Phi M π.1 x)
      ⟨statPolicy hφ, statPolicy_adm M φ hφ⟩
  have hpg : ∀ x, Phi M (statPolicy hφ) x ≤ gUpper M := phi_le M u hu hu_fin φ hφ (gUpper M) h9
  have e1 : ∀ x, wAvg M x = gStar M := fun x =>
    le_antisymm ((hwp x).trans ((hpg x).trans hgs)) (hsw x)
  have e2 : ∀ x, Phi M (statPolicy hφ) x = gStar M := fun x =>
    le_antisymm ((hpg x).trans hgs) ((hsw x).trans (hwp x))
  have e3 : ∀ x : X, gUpper M = gStar M := fun x =>
    le_antisymm hgs ((hsw x).trans ((hwp x).trans (hpg x)))
  refine ⟨fun x => (e2 x).trans (e1 x).symm, fun x => ⟨(e1 x).trans (e2 x).symm, ?_, ?_, e3 x⟩⟩
  · rw [e2 x]
    exact le_antisymm (by rw [← e3 x]; exact hgL x) (by rw [← e1 x]; exact hLw x)
  · exact le_antisymm (by rw [e3 x, ← e1 x]; exact hLw x) (hgL x)


theorem schal_1_2 {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (M : Model S A) :
    (∀ π : Policy S A, Admissible M π → ∀ x : S,
      limsup (fun β : ℝ => ENNReal.ofReal (1 - β) * Jbeta M π β x) (𝓝[<] 1) ≤ Phi M π x) ∧
    (GeneralAssumption M → gLower M ≤ gUpper M ∧ gUpper M ≤ gStar M ∧ gStar M < ⊤) := by
  refine ⟨fun π _ x => abel_policy M π x, fun hG => ⟨?_, ?_, hG⟩⟩
  · exact liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault)
  · apply le_iInf; intro x; apply le_iInf; intro π
    refine le_trans ?_ (abel_policy M π.1 x)
    apply limsup_le_limsup _ (by isBoundedDefault) (by isBoundedDefault)
    exact Eventually.of_forall (fun β => mul_le_mul_of_nonneg_left
      ((iInf_le (fun x => vβ M β x) x).trans
        (iInf_le (fun π : {π : Policy S A // Admissible M π} => Jbeta M π.1 β x) π)) zero_le)

theorem schal_1_3 {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (M : Model S A) (hGA : GeneralAssumption M)
    (w : S → ℝ≥0∞) (hw_meas : Measurable w) (hw_fin : ∀ x, w x ≠ ⊤)
    (f₁ : S → A) (hf₁ : IsStationary M f₁)
    (hACOI : ∀ x, M.toMDP.cost x (f₁ x) + ∫⁻ y, w y ∂(M.toMDP.q (x, f₁ x)) ≤ w x + gLower M) :
    (∀ x, Phi M (statPolicy hf₁) x = gStar M) ∧ gStar M = gLower M ∧ gLower M = gUpper M := by
  have h9 : ∀ x, M.toMDP.cost x (f₁ x) + ∫⁻ y, w y ∂(M.toMDP.q (x, f₁ x)) ≤ gLower M + w x :=
    fun x => (hACOI x).trans (le_of_eq (add_comm _ _))
  have hpg := phi_le M w hw_meas hw_fin f₁ hf₁ (gLower M) h9
  obtain ⟨hLU, hUS, -⟩ := (schal_1_2 M).2 hGA
  have hne : Nonempty S := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : gStar M = ⊤ := by simp [gStar]
    exact (ne_of_lt hGA) this
  obtain ⟨x0⟩ := hne
  have hsp : ∀ x, gStar M ≤ Phi M (statPolicy hf₁) x := fun x =>
    (iInf_le (fun x => ⨅ π : {π : Policy S A // Admissible M π}, Phi M π.1 x) x).trans
      (iInf_le (fun π : {π : Policy S A // Admissible M π} => Phi M π.1 x)
        ⟨statPolicy hf₁, statPolicy_adm M f₁ hf₁⟩)
  have e1 : gStar M = gLower M :=
    le_antisymm ((hsp x0).trans (hpg x0)) (hLU.trans hUS)
  refine ⟨fun x => le_antisymm ((hpg x).trans (e1 ▸ le_rfl)) (hsp x), e1, ?_⟩
  exact le_antisymm hLU (hUS.trans e1.le)

end FKZS201

open SchalAvg.AvgOpt FeinbergLiang.ACOE in
theorem solution {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S]
    [MeasurableSpace A] [StandardBorelSpace A] (M : Model S A) :
    (∀ π : Policy S A, Admissible M π → ∀ x : S,
      limsup (fun β : ℝ => ENNReal.ofReal (1 - β) * Jbeta M π β x) (𝓝[<] 1) ≤ Phi M π x) ∧
    (GeneralAssumption M → gLower M ≤ gUpper M ∧ gUpper M ≤ gStar M ∧ gStar M < ⊤) :=
  FKZS201.schal_1_2 M
