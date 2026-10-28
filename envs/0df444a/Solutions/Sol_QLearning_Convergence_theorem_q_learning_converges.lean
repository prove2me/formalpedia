-- Prove2me | solution 1 for QLearning.Convergence.theorem_q_learning_converges
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-28T02:12:52.942208+00:00
-- url     : https://prove2.me/submissions/c7499824-462e-4694-90b8-02be648ee02f

import Mathlib
import Definitions.Def_QLearning_Convergence_Setting

namespace QLearning.Convergence.QLFresh
end QLearning.Convergence.QLFresh


namespace QLearning.Convergence.QLFresh
open MeasureTheory
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    [MeasurableSpace I] [DiscreteMeasurableSpace I]
lemma measurable_finite_eval {y : Ω → I} (hy : Measurable y) {f : I → Ω → ℝ}
    (hf : ∀i,Measurable (f i)) : Measurable (fun ω => f (y ω) ω) := by
  have he : (fun ω => f (y ω) ω) = fun ω => ∑i : I,if y ω=i then f i ω else 0 := by
    funext ω
    simp
  rw [he]
  exact Finset.measurable_sum _ (fun i _ => Measurable.ite (hy (measurableSet_singleton i)) (hf i) measurable_const)
end QLearning.Convergence.QLFresh


namespace QLearning.Convergence.QLFresh
open MeasureTheory ProbabilityTheory
variable {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [MeasurableSpace A] [DiscreteMeasurableSpace A]
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
omit [Fintype X] [DecidableEq X] [DecidableEq A] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [MeasurableSpace A] [DiscreteMeasurableSpace A] in
lemma measurable_vmax {Q : Ω → X → A → ℝ} (hQ : ∀x a,Measurable (fun ω => Q ω x a)) (x : X) :
    Measurable (fun ω => vmax (Q ω) x) := by
  convert (Finset.measurable_sup' Finset.univ_nonempty (fun a _ => hQ x a)) using 1
  funext ω
  simp [vmax]
lemma qIter_measurable (ℱ : Filtration ℕ mΩ) (γ : ℝ) (Q0 : X → A → ℝ)
    (xs : ℕ → Ω → X) (as : ℕ → Ω → A) (ys : ℕ → Ω → X) (rs αs : ℕ → Ω → ℝ)
    (hxs : ∀n,Measurable[ℱ n] (xs (n+1)))
    (has : ∀n,Measurable[ℱ n] (as (n+1)))
    (hαs : ∀n,Measurable[ℱ n] (αs (n+1)))
    (hys : ∀n,Measurable[ℱ (n+1)] (ys (n+1)))
    (hrs : ∀n,Measurable[ℱ (n+1)] (rs (n+1))) :
    ∀n x a,Measurable[ℱ n] (fun ω => qIter γ Q0 (fun k => xs k ω)
      (fun k => as k ω) (fun k => ys k ω) (fun k => rs k ω) (fun k => αs k ω) n x a) := by
  intro n
  induction n with
  | zero => intro x a; exact measurable_const
  | succ n ih =>
    have hq (x a) := (ih x a).mono (ℱ.mono (Nat.le_succ n)) le_rfl
    have hx := (hxs n).mono (ℱ.mono (Nat.le_succ n)) le_rfl
    have ha := (has n).mono (ℱ.mono (Nat.le_succ n)) le_rfl
    have hα := (hαs n).mono (ℱ.mono (Nat.le_succ n)) le_rfl
    have hv := @measurable_finite_eval Ω X (ℱ (n+1)) _ _ _ _ _ (hys n) _
      (fun x => measurable_vmax (mΩ := ℱ (n+1)) hq x)
    intro x a
    have hp : MeasurableSet[ℱ (n+1)] {ω | x=xs (n+1) ω ∧ a=as (n+1) ω} := by
      simpa only [Set.preimage,Set.mem_singleton_iff,Set.inter_def,Set.mem_ofPred_eq,eq_comm] using (hx (measurableSet_singleton x)).inter (ha (measurableSet_singleton a))
    exact Measurable.ite hp
      (((measurable_const.sub hα).mul (hq x a)).add (hα.mul ((hrs n).add (measurable_const.mul hv)))) (hq x a)
end QLearning.Convergence.QLFresh


namespace QLearning.Convergence.QLFresh
open MeasureTheory ProbabilityTheory
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
lemma integrable_of_abs_bound {f : Ω → ℝ} {K : ℝ} (hf : Measurable f)
    (hb : ∀ω,|f ω| ≤ K) : Integrable f μ := by
  apply (integrable_const K).mono' hf.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hb ω)
lemma integral_cross_zero {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {f g : Ω → ℝ}
    (hf : StronglyMeasurable[m] f) (hfg : Integrable (f*g) μ) (hg : Integrable g μ)
    (hz : μ[g|m] =ᵐ[μ] 0) : (∫ω,f ω*g ω ∂μ)=0 := by
  have he := condExp_mul_of_stronglyMeasurable_left hf hfg hg
  have he0 : μ[f*g|m] =ᵐ[μ] 0 := by
    filter_upwards [he,hz] with ω h1 h2
    simpa only [Pi.mul_apply,h2,Pi.zero_apply,mul_zero] using h1
  have hi := integral_condExp (μ := μ) (f := f*g) hm
  rw [integral_congr_ae he0] at hi
  simpa using hi.symm
lemma elp_one_bound_of_square {f : Ω → ℝ} {C : ℝ} (hf : Integrable f μ)
    (hf2 : Integrable (fun ω => (f ω)^2) μ) (hb : (∫ω,(f ω)^2 ∂μ) ≤ C) :
    eLpNorm f 1 μ ≤ ENNReal.ofReal (C+1) := by
  rw [eLpNorm_one_eq_lintegral_enorm,← ofReal_integral_norm_eq_lintegral_enorm hf]
  apply ENNReal.ofReal_le_ofReal
  have h : (∫ω,‖f ω‖ ∂μ) ≤ ∫ω,(f ω)^2+1 ∂μ := by
    apply integral_mono hf.norm (hf2.add (integrable_const 1))
    intro ω
    change ‖f ω‖ ≤ (f ω)^2+1
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (|f ω|-1),sq_abs (f ω)]
  rw [integral_add hf2 (integrable_const 1)] at h
  have h1 : (∫ω,(1:ℝ) ∂μ)=1 := by simp
  rw [h1] at h
  exact h.trans (add_le_add hb le_rfl)
end QLearning.Convergence.QLFresh


namespace QLearning.Convergence.QLFresh
open MeasureTheory ProbabilityTheory Filter Topology
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
noncomputable def partialSum (z : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : ℝ := ∑k ∈ Finset.range N,z k ω
omit mΩ in
lemma partialSum_succ (z : ℕ → Ω → ℝ) (N : ℕ) : partialSum z (N+1)=partialSum z N+z N := by
  ext ω
  exact Finset.sum_range_succ _ _
lemma partialSum_measurable (ℱ : Filtration ℕ mΩ) {z : ℕ → Ω → ℝ}
    (hz : ∀n,Measurable[ℱ (n+1)] (z n)) (N : ℕ) : Measurable[ℱ N] (partialSum z N) := by
  apply Finset.measurable_sum
  intro k hk
  exact (hz k).mono (ℱ.mono (by simpa using Finset.mem_range.mp hk)) le_rfl
omit mΩ in
lemma partialSum_bound {z : ℕ → Ω → ℝ} {K : ℝ} (hb : ∀n ω,|z n ω| ≤ K) (N : ℕ) (ω : Ω) :
    |partialSum z N ω| ≤ (N:ℝ)*K := by
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum (fun k _ => hb k ω)).trans_eq (by simp))
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
lemma bounded_mul_integrable {f g : Ω → ℝ} {B C : ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfB : ∀ω,|f ω| ≤ B) (hgC : ∀ω,|g ω| ≤ C) : Integrable (f*g) μ := by
  apply integrable_of_abs_bound (hf.mul hg) (K := B*C)
  intro ω
  rw [Pi.mul_apply,abs_mul]
  exact mul_le_mul (hfB ω) (hgC ω) (abs_nonneg _) ((abs_nonneg _).trans (hfB ω))
lemma bounded_sq_integrable {f : Ω → ℝ} {B : ℝ} (hf : Measurable f)
    (hfB : ∀ω,|f ω| ≤ B) : Integrable (fun ω => (f ω)^2) μ := by
  convert bounded_mul_integrable (μ := μ) hf hf hfB hfB using 1
  ext ω
  simp only [pow_two,Pi.mul_apply]
lemma partialSum_integrable (ℱ : Filtration ℕ mΩ) {z : ℕ → Ω → ℝ} {K : ℝ}
    (hz : ∀n,Measurable[ℱ (n+1)] (z n)) (hb : ∀n ω,|z n ω| ≤ K) (N : ℕ) : Integrable (partialSum z N) μ :=
  integrable_of_abs_bound ((partialSum_measurable ℱ hz N).mono (ℱ.le N) le_rfl) (partialSum_bound hb N)
lemma partialSum_martingale (ℱ : Filtration ℕ mΩ) {z : ℕ → Ω → ℝ} {K : ℝ}
    (hz : ∀n,Measurable[ℱ (n+1)] (z n)) (hb : ∀n ω,|z n ω| ≤ K)
    (hc : ∀n,μ[z n|ℱ n] =ᵐ[μ] 0) : Martingale (partialSum z) ℱ μ := by
  have hi := partialSum_integrable (μ := μ) ℱ hz hb
  apply martingale_nat (fun n => (partialSum_measurable ℱ hz n).stronglyMeasurable) hi
  intro n
  rw [partialSum_succ]
  have hzI : Integrable (z n) μ := integrable_of_abs_bound ((hz n).mono (ℱ.le _) le_rfl) (hb n)
  have he := condExp_add (hi n) hzI (m := ℱ n)
  have hp := condExp_of_stronglyMeasurable (ℱ.le n) (partialSum_measurable ℱ hz n).stronglyMeasurable (hi n)
  filter_upwards [he,hc n] with ω h1 h2
  rw [hp] at h1
  simpa only [Pi.add_apply,h2,Pi.zero_apply,add_zero] using h1.symm
end QLearning.Convergence.QLFresh


namespace QLearning.Convergence.QLFresh
open MeasureTheory ProbabilityTheory
variable {Ω I : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [Fintype I] [DecidableEq I] [MeasurableSpace I] [DiscreteMeasurableSpace I]
lemma conditional_finite_eval {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {y : Ω → I} (hy : Measurable[mΩ] y) {f p : I → Ω → ℝ} {K : ℝ}
    (hf : ∀i,Measurable[m] (f i)) (hb : ∀i ω,|f i ω| ≤ K)
    (hp : ∀i,μ[fun ω => if y ω=i then (1:ℝ) else 0|m] =ᵐ[μ] p i) :
    μ[fun ω => f (y ω) ω|m] =ᵐ[μ] fun ω => ∑i,f i ω*p i ω := by
  let : MeasurableSpace Ω := mΩ
  let z (i : I) (ω : Ω) : ℝ := if y ω=i then 1 else 0
  have hzM (i) : Measurable[mΩ] (z i) := Measurable.ite (hy (measurableSet_singleton i)) measurable_const measurable_const
  have hzB (i ω) : |z i ω| ≤ 1 := by dsimp [z]; split_ifs <;> norm_num
  have hzI (i) : Integrable (z i) μ := integrable_of_abs_bound (μ := μ) (hzM i) (hzB i)
  have hprod (i) : Integrable (f i*z i) μ := bounded_mul_integrable (μ := μ) ((hf i).mono hm le_rfl) (hzM i) (hb i) (hzB i)
  have he (i) : μ[f i*z i|m] =ᵐ[μ] fun ω => f i ω*p i ω := by
    filter_upwards [condExp_mul_of_stronglyMeasurable_left (hf i).stronglyMeasurable (hprod i) (hzI i),hp i] with ω h1 h2
    change μ[z i|m] ω = p i ω at h2
    simpa only [Pi.mul_apply,h2] using h1
  have hid : (fun ω => f (y ω) ω) = ∑i,f i*z i := by
    funext ω
    simp [z,Finset.sum_apply,mul_ite]
  rw [hid]
  filter_upwards [condExp_finsetSum (fun i _ => hprod i) m,(ae_all_iff.mpr he)] with ω h1 h2
  simpa only [Finset.sum_apply] using h1.trans (by simp only [Finset.sum_apply]; exact Finset.sum_congr rfl (fun i _ => h2 i))
end QLearning.Convergence.QLFresh


namespace QLearning.Convergence.QLFresh
open Finset
variable {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
noncomputable def bellman (M : FiniteMDP X A) (γ : ℝ) (Q : X → A → ℝ) (x : X) (a : A) : ℝ :=
  M.R x a+γ*∑y,M.P x a y*vmax Q y
omit [Fintype X] [DecidableEq X] [DecidableEq A] in
lemma vmax_upper (Q : X → A → ℝ) (x : X) {C : ℝ} (h : ∀a,Q x a ≤ C) : vmax Q x ≤ C := by
  exact Finset.sup'_le _ _ (fun a _ => h a)
omit [Fintype X] [DecidableEq X] [DecidableEq A] in
lemma le_vmax (Q : X → A → ℝ) (x : X) (a : A) : Q x a ≤ vmax Q x :=
  Finset.le_sup' _ (Finset.mem_univ a)
omit [Fintype X] [DecidableEq X] [DecidableEq A] in
lemma vmax_abs_bound (Q : X → A → ℝ) {C : ℝ} (h : ∀x a,|Q x a| ≤ C) (x : X) : |vmax Q x| ≤ C := by
  rw [abs_le]
  refine ⟨?_,vmax_upper Q x (fun a => (abs_le.mp (h x a)).2)⟩
  let a : A := Classical.choice (inferInstance : Nonempty A)
  exact (abs_le.mp (h x a)).1.trans (le_vmax Q x a)
omit [Fintype X] [DecidableEq X] [DecidableEq A] in
lemma vmax_difference (Q R : X → A → ℝ) {C : ℝ}
    (h : ∀x a,|Q x a-R x a| ≤ C) (x : X) : |vmax Q x-vmax R x| ≤ C := by
  have hup : vmax Q x ≤ vmax R x+C := vmax_upper Q x (fun a => by
    have h1 := (abs_le.mp (h x a)).2
    have h2 := le_vmax R x a
    linarith)
  have hlo : vmax R x ≤ vmax Q x+C := vmax_upper R x (fun a => by
    have h1 := (abs_le.mp (h x a)).1
    have h2 := le_vmax Q x a
    linarith)
  rw [abs_le]
  constructor <;> linarith
omit [DecidableEq X] [DecidableEq A] in
lemma bellman_difference (M : FiniteMDP X A) {γ C : ℝ} (hγ : 0 ≤ γ)
    (Q R : X → A → ℝ) (h : ∀x a,|Q x a-R x a| ≤ C) (x : X) (a : A) :
    |bellman M γ Q x a-bellman M γ R x a| ≤ γ*C := by
  have he : bellman M γ Q x a-bellman M γ R x a = γ*∑y,M.P x a y*(vmax Q y-vmax R y) := by
    simp only [bellman,mul_sub,Finset.sum_sub_distrib]
    ring
  rw [he,abs_mul,abs_of_nonneg hγ]
  apply mul_le_mul_of_nonneg_left _ hγ
  calc
    |∑y,M.P x a y*(vmax Q y-vmax R y)| ≤ ∑y,|M.P x a y*(vmax Q y-vmax R y)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑y,M.P x a y*C := Finset.sum_le_sum (fun y _ => by
      rw [abs_mul,abs_of_nonneg (M.P_nonneg x a y)]
      exact mul_le_mul_of_nonneg_left (vmax_difference Q R h y) (M.P_nonneg x a y))
    _ = C := by rw [← Finset.sum_mul,M.P_sum,one_mul]
end QLearning.Convergence.QLFresh


namespace QLearning.Convergence.QLFresh
open MeasureTheory ProbabilityTheory
variable {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [MeasurableSpace A] [DiscreteMeasurableSpace A]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
lemma noise_core (M : FiniteMDP X A) {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {Q : Ω → X → A → ℝ} {x : Ω → X} {a : Ω → A} {y : Ω → X} {r : Ω → ℝ}
    {γ K R : ℝ} (hγ : 0 ≤ γ) (hQ : ∀x a,Measurable[m] (fun ω => Q ω x a))
    (hx : Measurable[m] x) (ha : Measurable[m] a) (hy : Measurable[mΩ] y) (hr : Measurable[mΩ] r)
    (hB : ∀ω x a,|Q ω x a| ≤ K) (hR : ∀ω,|r ω| ≤ R)
    (ht : ∀j,μ[fun ω => if y ω=j then (1:ℝ) else 0|m] =ᵐ[μ] fun ω => M.P (x ω) (a ω) j)
    (hrew : μ[r|m] =ᵐ[μ] fun ω => M.R (x ω) (a ω)) :
    let ξ := fun ω => r ω+γ*vmax (Q ω) (y ω)-bellman M γ (Q ω) (x ω) (a ω)
    Measurable[mΩ] ξ ∧ (∀ω,|ξ ω| ≤ R+‖M.R‖+2*γ*K) ∧ μ[ξ|m] =ᵐ[μ] 0 := by
  let : MeasurableSpace Ω := mΩ
  let v (j : X) (ω : Ω) := vmax (Q ω) j
  have hvM (j) : Measurable[m] (v j) := measurable_vmax (mΩ := m) hQ j
  have hvB (j ω) : |v j ω| ≤ K := vmax_abs_bound _ (hB ω) j
  let u (ω : Ω) := v (y ω) ω
  have huM : Measurable[mΩ] u := measurable_finite_eval hy (fun j => (hvM j).mono hm le_rfl)
  have huB (ω) : |u ω| ≤ K := hvB _ _
  let b (ω : Ω) := bellman M γ (Q ω) (x ω) (a ω)
  have hbM : Measurable[m] b := by
    exact @measurable_finite_eval Ω X m _ _ _ _ _ hx
      (fun i ω => bellman M γ (Q ω) i (a ω)) (by
        intro i
        exact @measurable_finite_eval Ω A m _ _ _ _ _ ha
          (fun j ω => bellman M γ (Q ω) i j) (by
            intro j
            exact measurable_const.add (measurable_const.mul (Finset.measurable_sum _ (fun k _ => measurable_const.mul (hvM k))))))
  have hbB (ω) : |b ω| ≤ ‖M.R‖+γ*K := by
    have hsum : |∑j,M.P (x ω) (a ω) j*v j ω| ≤ K := by
      calc
        _ ≤ ∑j,|M.P (x ω) (a ω) j*v j ω| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑j,M.P (x ω) (a ω) j*K := Finset.sum_le_sum (fun j _ => by
          rw [abs_mul,abs_of_nonneg (M.P_nonneg _ _ _)]
          exact mul_le_mul_of_nonneg_left (hvB j ω) (M.P_nonneg _ _ _))
        _ = K := by rw [← Finset.sum_mul,M.P_sum,one_mul]
    have hmr : |M.R (x ω) (a ω)| ≤ ‖M.R‖ :=
      (norm_le_pi_norm (M.R (x ω)) (a ω)).trans (norm_le_pi_norm M.R (x ω))
    exact (abs_add_le _ _).trans (add_le_add hmr (by
      rw [abs_mul,abs_of_nonneg hγ]; exact mul_le_mul_of_nonneg_left hsum hγ))
  have huI : Integrable u μ := integrable_of_abs_bound (μ := μ) huM huB
  have hrI : Integrable r μ := integrable_of_abs_bound (μ := μ) hr hR
  have hbI : Integrable b μ := integrable_of_abs_bound (μ := μ) (hbM.mono hm le_rfl) hbB
  have huC := conditional_finite_eval hm hy hvM hvB ht
  have hbC := condExp_of_stronglyMeasurable hm hbM.stronglyMeasurable hbI
  refine ⟨(hr.add (measurable_const.mul huM)).sub (hbM.mono hm le_rfl),?_,?_⟩
  · intro ω
    have hh : |r ω+γ*u ω-b ω| ≤ |r ω+γ*u ω|+|b ω| := by simpa only [Real.norm_eq_abs] using norm_sub_le (r ω+γ*u ω) (b ω)
    have hh2 := abs_add_le (r ω) (γ*u ω)
    have hh3 : |γ*u ω| ≤ γ*K := by rw [abs_mul,abs_of_nonneg hγ]; exact mul_le_mul_of_nonneg_left (huB ω) hγ
    change |r ω+γ*u ω-b ω| ≤ _
    linarith [hR ω,hbB ω]
  · have he1 := condExp_add hrI (huI.smul γ) m
    have he2 := condExp_sub (hrI.add (huI.smul γ)) hbI m
    have he3 := condExp_smul γ u m (μ := μ)
    have hid : (fun ω => r ω+γ*vmax (Q ω) (y ω)-bellman M γ (Q ω) (x ω) (a ω)) = (r+γ•u)-b := rfl
    rw [hid]
    filter_upwards [he1,he2,he3,huC,hrew] with ω h1 h2 h3 h4 h5
    rw [hbC] at h2
    simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at h1 h2 h3
    change μ[(r+γ•u)-b|m] ω = 0
    rw [h2,h1,h3,h4,h5]
    dsimp [b,bellman,v]
    simp only [mul_comm]
    ring
end QLearning.Convergence.QLFresh


namespace QLearning.Convergence.QLFresh
noncomputable def cutoffRate (a : ℕ → ℝ) (m : ℝ) (n : ℕ) : ℝ :=
  if ∑k ∈ Finset.range (n+1),(a k)^2 ≤ m then a n else 0
lemma cutoff_sq_le (a : ℕ → ℝ) (m : ℝ) (n : ℕ) : (cutoffRate a m n)^2 ≤ (a n)^2 := by
  unfold cutoffRate
  split_ifs <;> nlinarith [sq_nonneg (a n)]
lemma cutoff_mass_le (a : ℕ → ℝ) {m : ℝ} (hm : 0 ≤ m) (N : ℕ) :
    ∑k ∈ Finset.range N,(cutoffRate a m k)^2 ≤ m := by
  induction N with
  | zero => simpa using hm
  | succ N ih =>
    by_cases h : ∑k ∈ Finset.range (N+1),(a k)^2 ≤ m
    · exact (Finset.sum_le_sum (fun k _ => cutoff_sq_le a m k)).trans h
    · have hz : cutoffRate a m N = 0 := if_neg h
      rw [Finset.sum_range_succ,hz]
      simpa using ih
lemma cutoff_eq_of_total_le (a : ℕ → ℝ) {m : ℝ}
    (h : ∀N,∑k ∈ Finset.range N,(a k)^2 ≤ m) (n : ℕ) : cutoffRate a m n=a n := by
  exact if_pos (h (n+1))
end QLearning.Convergence.QLFresh


namespace QLearning.Convergence.QLFresh
open MeasureTheory ProbabilityTheory Filter Topology
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
lemma partialSum_square_integral (ℱ : Filtration ℕ mΩ) {z : ℕ → Ω → ℝ} {K : ℝ}
    (hz : ∀n,Measurable[ℱ (n+1)] (z n)) (hb : ∀n ω,|z n ω| ≤ K)
    (hc : ∀n,μ[z n|ℱ n] =ᵐ[μ] 0) (N : ℕ) :
    (∫ω,(partialSum z N ω)^2 ∂μ) = ∑k ∈ Finset.range N,∫ω,(z k ω)^2 ∂μ := by
  have hpM (n) := (partialSum_measurable ℱ hz n).mono (ℱ.le n) le_rfl
  have hzM (n) := (hz n).mono (ℱ.le (n+1)) le_rfl
  have hp2 (n) : Integrable (fun ω => (partialSum z n ω)^2) μ := bounded_sq_integrable (hpM n) (partialSum_bound hb n)
  have hz2 (n) : Integrable (fun ω => (z n ω)^2) μ := bounded_sq_integrable (hzM n) (hb n)
  induction N with
  | zero => simp [partialSum]
  | succ N ih =>
    have hcrossI : Integrable (partialSum z N*z N) μ :=
      bounded_mul_integrable (hpM N) (hzM N) (partialSum_bound hb N) (hb N)
    have hcross : ∫ω,partialSum z N ω*z N ω ∂μ = 0 :=
      integral_cross_zero (ℱ.le N) (partialSum_measurable ℱ hz N).stronglyMeasurable hcrossI
        (integrable_of_abs_bound (hzM N) (hb N)) (hc N)
    rw [Finset.sum_range_succ,← ih]
    calc
      (∫ω,(partialSum z (N+1) ω)^2 ∂μ) =
          ∫ω,((partialSum z N ω)^2+2*(partialSum z N ω*z N ω))+(z N ω)^2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [partialSum_succ,Pi.add_apply]
        ring
      _ = _ := by
        have h1 := integral_add ((hp2 N).add (hcrossI.const_mul 2)) (hz2 N)
        have h2 := integral_add (hp2 N) (hcrossI.const_mul 2)
        simp only [Pi.add_apply,Pi.mul_apply] at h1 h2
        rw [h1,h2,integral_const_mul,hcross]
        ring
lemma bounded_square_sum_converges (ℱ : Filtration ℕ mΩ) {z : ℕ → Ω → ℝ} {K C : ℝ}
    (hC : 0 ≤ C) (hz : ∀n,Measurable[ℱ (n+1)] (z n)) (hb : ∀n ω,|z n ω| ≤ K)
    (hc : ∀n,μ[z n|ℱ n] =ᵐ[μ] 0)
    (hv : ∀N,(∑k ∈ Finset.range N,∫ω,(z k ω)^2 ∂μ) ≤ C) :
    ∀ᵐω ∂μ,∃l : ℝ,Tendsto (fun N => partialSum z N ω) atTop (𝓝 l) := by
  have hm := partialSum_martingale ℱ hz hb hc
  have hi := partialSum_integrable (μ := μ) ℱ hz hb
  apply hm.submartingale.exists_ae_tendsto_of_bdd (R := ⟨C+1,by positivity⟩)
  intro N
  have h2 := bounded_sq_integrable (μ := μ)
    ((partialSum_measurable ℱ hz N).mono (ℱ.le _) le_rfl) (partialSum_bound hb N)
  have hv' : ∫ω,(partialSum z N ω)^2 ∂μ ≤ C := by rw [partialSum_square_integral ℱ hz hb hc]; exact hv N
  exact (elp_one_bound_of_square (hi N) h2 hv').trans_eq
    (ENNReal.ofReal_eq_coe_nnreal (by positivity))
end QLearning.Convergence.QLFresh


namespace QLearning.Convergence.QLFresh
open MeasureTheory ProbabilityTheory Filter Topology
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
lemma cutoff_measurable (ℱ : Filtration ℕ mΩ) {a : ℕ → Ω → ℝ}
    (ha : ∀n,Measurable[ℱ n] (a n)) (m : ℝ) (n : ℕ) :
    Measurable[ℱ n] (fun ω => cutoffRate (fun k => a k ω) m n) := by
  unfold cutoffRate
  have hs : Measurable[ℱ n] (fun ω => ∑k ∈ Finset.range (n+1),(a k ω)^2) := by
    apply Finset.measurable_sum
    intro k hk
    exact ((ha k).mono (ℱ.mono (by simpa using Finset.mem_range.mp hk)) le_rfl).pow_const 2
  exact Measurable.ite (measurableSet_le hs measurable_const) (ha n) measurable_const
lemma cutoff_abs_le_one {a : ℕ → ℝ} (ha : ∀n,0 ≤ a n ∧ a n ≤ 1) (m : ℝ) (n : ℕ) :
    |cutoffRate a m n| ≤ 1 := by
  unfold cutoffRate
  split_ifs
  · rw [abs_of_nonneg (ha n).1]; exact (ha n).2
  · norm_num
lemma cutoff_noise_converges (ℱ : Filtration ℕ mΩ) {a ξ : ℕ → Ω → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (ha : ∀n,Measurable[ℱ n] (a n))
    (har : ∀n ω,0 ≤ a n ω ∧ a n ω ≤ 1)
    (hξ : ∀n,Measurable[ℱ (n+1)] (ξ n)) (hb : ∀n ω,|ξ n ω| ≤ K)
    (hc : ∀n,μ[ξ n|ℱ n] =ᵐ[μ] 0) {m : ℝ} (hm : 0 ≤ m) :
    ∀ᵐω ∂μ,∃l : ℝ,Tendsto
      (fun N => ∑k ∈ Finset.range N,cutoffRate (fun j => a j ω) m k*ξ k ω) atTop (𝓝 l) := by
  let c (n : ℕ) (ω : Ω) := cutoffRate (fun j => a j ω) m n
  let z (n : ℕ) (ω : Ω) := c n ω*ξ n ω
  have hcM (n) : Measurable[ℱ n] (c n) := cutoff_measurable ℱ ha m n
  have hcB (n ω) : |c n ω| ≤ 1 := cutoff_abs_le_one (fun j => har j ω) m n
  have hzM (n) : Measurable[ℱ (n+1)] (z n) :=
    ((hcM n).mono (ℱ.mono (Nat.le_succ n)) le_rfl).mul (hξ n)
  have hzB (n ω) : |z n ω| ≤ K := by
    dsimp [z]
    rw [abs_mul]
    exact (mul_le_mul (hcB n ω) (hb n ω) (abs_nonneg _) (by norm_num)).trans_eq (one_mul K)
  have hzI (n) : Integrable (z n) μ := integrable_of_abs_bound ((hzM n).mono (ℱ.le _) le_rfl) (hzB n)
  have hzC (n) : μ[z n|ℱ n] =ᵐ[μ] 0 := by
    have hi : Integrable (ξ n) μ := integrable_of_abs_bound ((hξ n).mono (ℱ.le _) le_rfl) (hb n)
    have he := condExp_mul_of_stronglyMeasurable_left (hcM n).stronglyMeasurable (hzI n) hi
    filter_upwards [he,hc n] with ω h1 h2
    have hzEq : z n = c n * ξ n := by funext ω; rfl
    rw [hzEq]
    simpa only [Pi.mul_apply,h2,Pi.zero_apply,mul_zero] using h1
  apply bounded_square_sum_converges ℱ (mul_nonneg (sq_nonneg K) hm) hzM hzB hzC
  intro N
  have hI (k) : Integrable (fun ω => (z k ω)^2) μ :=
    bounded_sq_integrable ((hzM k).mono (ℱ.le _) le_rfl) (hzB k)
  rw [← integral_finsetSum _ (fun k _ => hI k)]
  calc
    (∫ω,∑k ∈ Finset.range N,(z k ω)^2 ∂μ) ≤ ∫ω,K^2*m ∂μ := by
      apply integral_mono (integrable_finsetSum _ (fun k _ => hI k)) (integrable_const _)
      intro ω
      calc
        ∑k ∈ Finset.range N,(z k ω)^2 ≤ ∑k ∈ Finset.range N,K^2*(c k ω)^2 := by
          apply Finset.sum_le_sum
          intro k _
          have hh : (ξ k ω)^2 ≤ K^2 := by
            simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).2 (hb k ω)
          dsimp [z]
          rw [mul_pow]
          nlinarith [mul_nonneg (sq_nonneg (c k ω)) (sub_nonneg.mpr hh)]
        _ = K^2*∑k ∈ Finset.range N,(c k ω)^2 := (Finset.mul_sum _ _ _).symm
        _ ≤ K^2*m := mul_le_mul_of_nonneg_left (cutoff_mass_le (fun k => a k ω) hm N) (sq_nonneg K)
    _ = _ := by simp
end QLearning.Convergence.QLFresh


namespace QLearning.Convergence.QLFresh
open MeasureTheory ProbabilityTheory Filter Topology
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
lemma bounded_noise_series (ℱ : Filtration ℕ mΩ) {a ξ : ℕ → Ω → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (ha : ∀n,Measurable[ℱ n] (a n))
    (har : ∀n ω,0 ≤ a n ω ∧ a n ω ≤ 1)
    (hξ : ∀n,Measurable[ℱ (n+1)] (ξ n)) (hb : ∀n ω,|ξ n ω| ≤ K)
    (hc : ∀n,μ[ξ n|ℱ n] =ᵐ[μ] 0)
    (hs : ∀ᵐω ∂μ,Summable (fun n => (a n ω)^2)) :
    ∀ᵐω ∂μ,∃l : ℝ,Tendsto (fun N => ∑k ∈ Finset.range N,a k ω*ξ k ω) atTop (𝓝 l) := by
  have hall : ∀ᵐω ∂μ,∀m : ℕ,∃l : ℝ,Tendsto
      (fun N => ∑k ∈ Finset.range N,cutoffRate (fun j => a j ω) m k*ξ k ω) atTop (𝓝 l) := by
    rw [ae_all_iff]
    intro m
    exact cutoff_noise_converges ℱ hK ha har hξ hb hc (Nat.cast_nonneg m)
  filter_upwards [hs,hall] with ω hsω hallω
  obtain ⟨m,hm⟩ := exists_nat_gt (∑'n,(a n ω)^2)
  have hmass (N) : ∑k ∈ Finset.range N,(a k ω)^2 ≤ (m:ℝ) :=
    (hsω.sum_le_tsum (Finset.range N) (fun k _ => sq_nonneg (a k ω))).trans hm.le
  obtain ⟨l,hl⟩ := hallω m
  refine ⟨l,?_⟩
  simpa only [cutoff_eq_of_total_le _ hmass] using hl
end QLearning.Convergence.QLFresh


namespace QLearning.Convergence.QLFresh
variable {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
omit [Fintype X] in
lemma qIter_bound (γ : ℝ) (Q0 : X → A → ℝ) (xs : ℕ → X) (as : ℕ → A) (ys : ℕ → X)
    (rs αs : ℕ → ℝ) {K R : ℝ} (hγ : 0 ≤ γ) (_hK : 0 ≤ K)
    (h0 : ∀x a,|Q0 x a| ≤ K) (hr : ∀n,|rs n| ≤ R)
    (ha : ∀n,0 ≤ αs n ∧ αs n ≤ 1) (hRK : R+γ*K ≤ K) :
    ∀n x a,|qIter γ Q0 xs as ys rs αs n x a| ≤ K := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    intro x a
    rw [qIter_succ]
    dsimp only
    split_ifs with h
    · have hb : |rs (n+1)+γ*vmax (qIter γ Q0 xs as ys rs αs n) (ys (n+1))| ≤ K := by
        calc
          _ ≤ |rs (n+1)|+|γ*vmax (qIter γ Q0 xs as ys rs αs n) (ys (n+1))| := abs_add_le _ _
          _ ≤ R+γ*K := by
            rw [abs_mul,abs_of_nonneg hγ]
            exact add_le_add (hr _) (mul_le_mul_of_nonneg_left (vmax_abs_bound _ ih _) hγ)
          _ ≤ K := hRK
      calc
        _ ≤ |(1-αs (n+1))*qIter γ Q0 xs as ys rs αs n x a|+
            |αs (n+1)*(rs (n+1)+γ*vmax (qIter γ Q0 xs as ys rs αs n) (ys (n+1)))| := abs_add_le _ _
        _ ≤ (1-αs (n+1))*K+αs (n+1)*K := by
          rw [abs_mul,abs_mul,abs_of_nonneg (by linarith [(ha (n+1)).2]),abs_of_nonneg (ha (n+1)).1]
          exact add_le_add (mul_le_mul_of_nonneg_left (ih x a) (by linarith [(ha (n+1)).2]))
            (mul_le_mul_of_nonneg_left hb (ha (n+1)).1)
        _ = K := by ring
    · exact ih x a
omit [DecidableEq X] [DecidableEq A] [Nonempty A] in
lemma initial_uniform_bound (γ R : ℝ) (hγ : γ < 1) (Q0 : X → A → ℝ) :
    ∃K : ℝ,0 ≤ K ∧ (∀x a,|Q0 x a| ≤ K) ∧ R+γ*K ≤ K := by
  let K : ℝ := ‖Q0‖+|R|/(1-γ)+1
  have hd : 0 < 1-γ := sub_pos.mpr hγ
  have hb : 0 ≤ |R|/(1-γ) := div_nonneg (abs_nonneg _) hd.le
  refine ⟨K,by dsimp [K]; positivity,?_,?_⟩
  · intro x a
    have hh := (norm_le_pi_norm (Q0 x) a).trans (norm_le_pi_norm Q0 x)
    rw [Real.norm_eq_abs] at hh
    dsimp [K]
    linarith
  · have he : (|R|/(1-γ))*(1-γ)=|R| := div_mul_cancel₀ _ hd.ne'
    have hn := mul_nonneg (norm_nonneg Q0) hd.le
    dsimp [K]
    nlinarith [le_abs_self R]
end QLearning.Convergence.QLFresh



namespace QLearning.Convergence.QLFresh
variable {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]

noncomputable def pathNoise (M : FiniteMDP X A) (γ : ℝ) (Q0 : X → A → ℝ)
    (xs : ℕ → X) (as : ℕ → A) (ys : ℕ → X) (rs αs : ℕ → ℝ) (n : ℕ) : ℝ :=
  rs (n+1)+γ*vmax (qIter γ Q0 xs as ys rs αs n) (ys (n+1)) -
    bellman M γ (qIter γ Q0 xs as ys rs αs n) (xs (n+1)) (as (n+1))

lemma qIter_noise_step (M : FiniteMDP X A) (γ : ℝ) (Q0 : X → A → ℝ)
    (xs : ℕ → X) (as : ℕ → A) (ys : ℕ → X) (rs αs : ℕ → ℝ)
    (n : ℕ) (x : X) (a : A) :
    qIter γ Q0 xs as ys rs αs (n+1) x a =
      (1-visitRate xs as αs x a (n+1))*qIter γ Q0 xs as ys rs αs n x a +
      visitRate xs as αs x a (n+1)*bellman M γ (qIter γ Q0 xs as ys rs αs n) x a +
      visitRate xs as αs x a (n+1)*pathNoise M γ Q0 xs as ys rs αs n := by
  by_cases h : xs (n+1)=x ∧ as (n+1)=a
  · obtain ⟨hx,ha⟩ := h
    simp only [qIter_succ,visitRate,pathNoise,hx,ha,ite_true,and_self]
    ring
  · have h' : ¬ (x=xs (n+1) ∧ a=as (n+1)) := by
      rintro ⟨hx,ha⟩
      exact h ⟨hx.symm,ha.symm⟩
    simp only [qIter_succ,visitRate,h,h',ite_false,sub_zero,one_mul,zero_mul,add_zero]

end QLearning.Convergence.QLFresh


namespace QLearning.Convergence.QLFresh
open MeasureTheory ProbabilityTheory Filter Topology
variable {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [MeasurableSpace A] [DiscreteMeasurableSpace A]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
lemma native_noise_series (M : FiniteMDP X A) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (Q0 : X → A → ℝ) (ℱ : Filtration ℕ mΩ)
    (xs : ℕ → Ω → X) (as : ℕ → Ω → A) (ys : ℕ → Ω → X) (rs αs : ℕ → Ω → ℝ)
    (hxs : ∀n,Measurable[ℱ n] (xs (n+1)))
    (has : ∀n,Measurable[ℱ n] (as (n+1)))
    (hαs : ∀n,Measurable[ℱ n] (αs (n+1)))
    (hys : ∀n,Measurable[ℱ (n+1)] (ys (n+1)))
    (hrs : ∀n,Measurable[ℱ (n+1)] (rs (n+1)))
    (htrans : ∀n y,μ[fun ω => if ys (n+1) ω=y then (1:ℝ) else 0|ℱ n] =ᵐ[μ]
      fun ω => M.P (xs (n+1) ω) (as (n+1) ω) y)
    (hrew : ∀n,μ[rs (n+1)|ℱ n] =ᵐ[μ] fun ω => M.R (xs (n+1) ω) (as (n+1) ω))
    (Rbar : ℝ) (hbdd : ∀n ω,|rs n ω| ≤ Rbar)
    (hα : ∀n ω,0 ≤ αs n ω ∧ αs n ω < 1)
    (hs : ∀ᵐω ∂μ,∀x a,Summable (fun n => (visitRate (fun k => xs k ω)
      (fun k => as k ω) (fun k => αs k ω) x a (n+1))^2)) :
    ∀x a,∀ᵐω ∂μ,∃l : ℝ,Tendsto (fun N => ∑n ∈ Finset.range N,
      visitRate (fun k => xs k ω) (fun k => as k ω) (fun k => αs k ω) x a (n+1)*
      pathNoise M γ Q0 (fun k => xs k ω) (fun k => as k ω) (fun k => ys k ω)
        (fun k => rs k ω) (fun k => αs k ω) n) atTop (𝓝 l) := by
  obtain ⟨K,hK,h0,hRK⟩ := initial_uniform_bound γ |Rbar| hγ1 Q0
  let Q (n : ℕ) (ω : Ω) := qIter γ Q0 (fun k => xs k ω) (fun k => as k ω)
    (fun k => ys k ω) (fun k => rs k ω) (fun k => αs k ω) n
  let ξ (n : ℕ) (ω : Ω) := pathNoise M γ Q0 (fun k => xs k ω) (fun k => as k ω)
    (fun k => ys k ω) (fun k => rs k ω) (fun k => αs k ω) n
  have hQB (n ω x a) : |Q n ω x a| ≤ K := qIter_bound γ Q0 _ _ _ _ _ hγ0.le hK h0
    (fun k => (hbdd k ω).trans (le_abs_self _)) (fun k => ⟨(hα k ω).1,(hα k ω).2.le⟩) hRK n x a
  have hQM := qIter_measurable ℱ γ Q0 xs as ys rs αs hxs has hαs hys hrs
  have hcore (n) := noise_core M (ℱ.le n) hγ0.le (hQM n) (hxs n) (has n)
    ((hys n).mono (ℱ.le _) le_rfl) ((hrs n).mono (ℱ.le _) le_rfl)
    (hQB n) (fun ω => (hbdd (n+1) ω).trans (le_abs_self _)) (htrans n) (hrew n)
  have hξM (n) : Measurable[ℱ (n+1)] (ξ n) := by
    have hq (x a) := (hQM n x a).mono (ℱ.mono (Nat.le_succ n)) le_rfl
    have hx := (hxs n).mono (ℱ.mono (Nat.le_succ n)) le_rfl
    have ha := (has n).mono (ℱ.mono (Nat.le_succ n)) le_rfl
    have hv := @measurable_finite_eval Ω X (ℱ (n+1)) _ _ _ _ _ (hys n) _
      (fun x => measurable_vmax (mΩ := ℱ (n+1)) hq x)
    have hb : Measurable[ℱ (n+1)] (fun ω => bellman M γ (Q n ω) (xs (n+1) ω) (as (n+1) ω)) := by
      exact @measurable_finite_eval Ω X (ℱ (n+1)) _ _ _ _ _ hx
        (fun x ω => bellman M γ (Q n ω) x (as (n+1) ω)) (by
          intro x
          exact @measurable_finite_eval Ω A (ℱ (n+1)) _ _ _ _ _ ha
            (fun a ω => bellman M γ (Q n ω) x a) (by
              intro a
              exact measurable_const.add (measurable_const.mul (Finset.measurable_sum _
                (fun y _ => measurable_const.mul (measurable_vmax (mΩ := ℱ (n+1)) hq y))))))
    exact ((hrs n).add (measurable_const.mul hv)).sub hb
  intro x a
  let rate (n : ℕ) (ω : Ω) := visitRate (fun k => xs k ω) (fun k => as k ω) (fun k => αs k ω) x a (n+1)
  have hrate (n) : Measurable[ℱ n] (rate n) :=
    Measurable.ite ((hxs n) (measurableSet_singleton x) |>.inter ((has n) (measurableSet_singleton a))) (hαs n) measurable_const
  have hrange (n ω) : 0 ≤ rate n ω ∧ rate n ω ≤ 1 := by
    dsimp [rate,visitRate]
    split_ifs
    · exact ⟨(hα _ _).1,(hα _ _).2.le⟩
    · norm_num
  exact bounded_noise_series ℱ (by positivity : 0 ≤ |Rbar|+‖M.R‖+2*γ*K) hrate hrange hξM
    (fun n => (hcore n).2.1) (fun n => (hcore n).2.2) (hs.mono (fun ω h => h x a))
end QLearning.Convergence.QLFresh



namespace QLearning.Convergence.QLFresh
open Filter Finset
open scoped Topology

lemma averaging_exp_bound (a u : ℕ → ℝ) (c : ℝ)
    (ha : ∀ n, 0 ≤ a n ∧ a n ≤ 1)
    (hu : ∀ n, u (n+1) ≤ (1-a n)*u n + a n*c) (n : ℕ) :
    u n ≤ c + Real.exp (-(∑ k ∈ range n, a k)) * max (u 0-c) 0 := by
  induction n with
  | zero =>
    simp only [sum_range_zero, neg_zero, Real.exp_zero, one_mul]
    linarith [le_max_left (u 0-c) 0]
  | succ n ih =>
    have he : 1-a n ≤ Real.exp (-a n) := by
      have := Real.add_one_le_exp (-a n)
      linarith
    have hp : 0 ≤ Real.exp (-(∑ k ∈ range n, a k)) * max (u 0-c) 0 :=
      mul_nonneg (Real.exp_pos _).le (le_max_right _ _)
    have hm := mul_le_mul_of_nonneg_right he hp
    have hi := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (ha n).2)
    rw [sum_range_succ]
    rw [neg_add, Real.exp_add]
    nlinarith [hu n]

lemma averaging_eventually_lt (a u : ℕ → ℝ) (c : ℝ)
    (ha : ∀ n, 0 ≤ a n ∧ a n ≤ 1)
    (hs : Tendsto (fun n => ∑ k ∈ range n, a k) atTop atTop)
    (hu : ∀ n, u (n+1) ≤ (1-a n)*u n + a n*c)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ n in atTop, u n < c+ε := by
  have ht : Tendsto (fun n => Real.exp (-(∑ k ∈ range n, a k)) * max (u 0-c) 0)
      atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hs)).mul_const (max (u 0-c) 0)
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn
  exact lt_of_le_of_lt (averaging_exp_bound a u c ha hu n) (by linarith)

lemma sum_shift_tendsto (a : ℕ → ℝ)
    (hs : Tendsto (fun n => ∑ k ∈ range n, a k) atTop atTop) (N : ℕ) :
    Tendsto (fun n => ∑ k ∈ range n, a (N+k)) atTop atTop := by
  have h := tendsto_atTop_add_const_right atTop (-(∑ k ∈ range N, a k))
    (hs.comp (tendsto_add_atTop_nat N))
  convert h using 1
  ext n
  simp only [Function.comp_def]
  rw [Nat.add_comm n N, sum_range_add]
  ring

lemma averaging_eventual_recurrence (a u : ℕ → ℝ) (c : ℝ)
    (ha : ∀ n, 0 ≤ a n ∧ a n ≤ 1)
    (hs : Tendsto (fun n => ∑ k ∈ range n, a k) atTop atTop)
    (hu : ∀ᶠ n in atTop, u (n+1) ≤ (1-a n)*u n + a n*c)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ n in atTop, u n < c+ε := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hu
  have ht := averaging_eventually_lt (fun n => a (N+n)) (fun n => u (N+n)) c
    (fun n => ha _) (sum_shift_tendsto a hs N)
    (fun n => by simpa [Nat.add_assoc] using hN (N+n) (by omega)) hε
  obtain ⟨M, hM⟩ := eventually_atTop.1 ht
  refine eventually_atTop.2 ⟨N+M, fun n hn => ?_⟩
  simpa [Nat.add_sub_of_le (show N ≤ n by omega)] using hM (n-N) (by omega)

end QLearning.Convergence.QLFresh



namespace QLearning.Convergence.QLFresh
open Filter Finset
open scoped Topology

lemma asynchronous_norm_tendsto {I : Type*} [Fintype I]
    (y : ℕ → I → ℝ) (a : ℕ → I → ℝ) (t : ℕ → ℝ) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (ha : ∀ n i, 0 ≤ a n i ∧ a n i ≤ 1)
    (hs : ∀ i, Tendsto (fun n => ∑ k ∈ range n, a k i) atTop atTop)
    (ht : Tendsto t atTop (𝓝 0))
    (hb : ∃ B, ∀ n, ‖y n‖ ≤ B)
    (hr : ∀ n i, |y (n+1) i| ≤ (1-a n i)*|y n i| +
      a n i*(γ*‖y n‖+t n)) : Tendsto (fun n => ‖y n‖) atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := hb
  have hup : IsBoundedUnder (· ≤ ·) atTop (fun n => ‖y n‖) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall hB)
  have hlo : IsBoundedUnder (· ≥ ·) atTop (fun n => ‖y n‖) :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall (fun n => norm_nonneg (y n)))
  let L := limsup (fun n => ‖y n‖) atTop
  have hL0 : 0 ≤ L := by
    apply le_limsup_of_le hup
    intro b hb
    obtain ⟨n, hn⟩ := hb.exists
    exact (norm_nonneg _).trans hn
  have hδ : ∀ δ : ℝ, 0 < δ → L ≤ γ*L+(γ+2)*δ := by
    intro δ hδ
    have hy : ∀ᶠ n in atTop, ‖y n‖ < L+δ :=
      eventually_lt_of_limsup_lt (by dsimp [L]; linarith) hup
    have htδ : ∀ᶠ n in atTop, t n < δ := ht.eventually (gt_mem_nhds hδ)
    have hi : ∀ i, ∀ᶠ n in atTop, |y n i| < γ*(L+δ)+δ+δ := by
      intro i
      apply averaging_eventual_recurrence (fun n => a n i) (fun n => |y n i|)
        (γ*(L+δ)+δ) (fun n => ha n i) (hs i) _ hδ
      filter_upwards [hy, htδ] with n hyn htn
      have hm := mul_le_mul_of_nonneg_left hyn.le hγ0
      have hm' := mul_le_mul_of_nonneg_left (show γ*‖y n‖+t n ≤ γ*(L+δ)+δ by linarith)
        (ha n i).1
      linarith [hr n i]
    have hall := eventually_all.2 hi
    have hn : ∀ᶠ n in atTop, ‖y n‖ ≤ γ*(L+δ)+δ+δ := by
      filter_upwards [hall] with n hn
      apply (pi_norm_le_iff_of_nonneg (by positivity)).2
      intro i
      simpa only [Real.norm_eq_abs] using (hn i).le
    have h := limsup_le_of_le (isCoboundedUnder_le_of_le atTop (fun n => norm_nonneg (y n))) hn
    dsimp [L] at ⊢
    nlinarith
  have hLL : L ≤ γ*L := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hp : 0 < γ+2 := by linarith
    have h := hδ (ε/(γ+2)) (div_pos hε hp)
    have he : (γ+2)*(ε/(γ+2)) = ε := by field_simp
    rw [he] at h
    exact h
  have hL : L ≤ 0 := by nlinarith
  exact tendsto_of_le_liminf_of_limsup_le
    (le_liminf_of_le hup.isCoboundedUnder_ge (Eventually.of_forall (fun n => norm_nonneg (y n))))
    hL hup hlo

end QLearning.Convergence.QLFresh



namespace QLearning.Convergence.QLFresh
open Filter Finset
open scoped Topology

lemma asynchronous_noise_tendsto {I : Type*} [Fintype I]
    (e b S : ℕ → I → ℝ) (a : ℕ → I → ℝ) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (ha : ∀ n i, 0 ≤ a n i ∧ a n i ≤ 1)
    (hs : ∀ i, Tendsto (fun n => ∑ k ∈ range n, a k i) atTop atTop)
    (he : ∃ B, ∀ n, ‖e n‖ ≤ B)
    (hb : ∀ n i, |b n i| ≤ γ*‖e n‖)
    (hr : ∀ n i, e (n+1) i = (1-a n i)*e n i+a n i*b n i+(S (n+1) i-S n i))
    (l : I → ℝ) (hS : Tendsto S atTop (𝓝 l)) :
    Tendsto e atTop (𝓝 0) := by
  let τ : ℕ → I → ℝ := fun n => l-S n
  let y : ℕ → I → ℝ := fun n => e n+τ n
  have hτ : Tendsto τ atTop (𝓝 0) := by
    simpa [τ] using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => l) atTop (𝓝 l)).sub hS)
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto τ hτ).exists_norm_le
  obtain ⟨B, hB⟩ := he
  have hyb : ∃ D, ∀ n, ‖y n‖ ≤ D := by
    refine ⟨B+C, fun n => ?_⟩
    exact (norm_add_le _ _).trans (add_le_add (hB n) (hC _ ⟨n,rfl⟩))
  have hyr : ∀ n i, y (n+1) i = (1-a n i)*y n i+a n i*(b n i+τ n i) := by
    intro n i
    dsimp [y,τ]
    rw [hr n i]
    ring
  have ht : Tendsto (fun n => (γ+1)*‖τ n‖) atTop (𝓝 0) := by
    simpa using hτ.norm.const_mul (γ+1)
  have hrec : ∀ n i, |y (n+1) i| ≤ (1-a n i)*|y n i|+
      a n i*(γ*‖y n‖+(γ+1)*‖τ n‖) := by
    intro n i
    have heq : e n = y n-τ n := by dsimp [y]; abel
    have hen : ‖e n‖ ≤ ‖y n‖+‖τ n‖ := by rw [heq]; exact norm_sub_le _ _
    have hτi : |τ n i| ≤ ‖τ n‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (τ n) i
    have hforce : |b n i+τ n i| ≤ γ*‖y n‖+(γ+1)*‖τ n‖ := by
      have hmul := mul_le_mul_of_nonneg_left hen hγ0
      have hh := abs_add_le (b n i) (τ n i)
      nlinarith [hb n i]
    rw [hyr]
    calc
      _ ≤ |(1-a n i)*y n i|+|a n i*(b n i+τ n i)| := abs_add_le _ _
      _ = (1-a n i)*|y n i|+a n i*|b n i+τ n i| := by
        rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr (ha n i).2),abs_of_nonneg (ha n i).1]
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hforce (ha n i).1)
  have hyn := asynchronous_norm_tendsto y a _ γ hγ0 hγ1 ha hs ht hyb hrec
  have hy : Tendsto y atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hyn
  have hef : e = fun n => y n-τ n := by funext n; dsimp [y]; abel
  rw [hef]
  simpa using hy.sub hτ

end QLearning.Convergence.QLFresh



namespace QLearning.Convergence.QLFresh
open MeasureTheory Filter Finset
open scoped Topology

lemma finite_coordinate_series {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (S : ℕ → Ω → I → ℝ)
    (hS : ∀ i, ∀ᵐ ω ∂μ, ∃ l : ℝ, Tendsto (fun n => S n ω i) atTop (𝓝 l)) :
    ∀ᵐ ω ∂μ, ∃ l : I → ℝ, Tendsto (fun n => S n ω) atTop (𝓝 l) := by
  classical
  have hh : ∀ᵐ ω ∂μ, ∀ i, ∃ l : ℝ, Tendsto (fun n => S n ω i) atTop (𝓝 l) :=
    ae_all_iff.mpr hS
  filter_upwards [hh] with ω hω
  choose l hl using hω
  exact ⟨l, tendsto_pi_nhds.mpr hl⟩

end QLearning.Convergence.QLFresh



namespace QLearning.Convergence.QLFresh
open Filter Finset
open scoped Topology
variable {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]

lemma pathwise_convergence (M : FiniteMDP X A) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (Qstar : X → A → ℝ) (hQ : IsOptimalQ M γ Qstar) (Q0 : X → A → ℝ)
    (xs : ℕ → X) (as : ℕ → A) (ys : ℕ → X) (rs αs : ℕ → ℝ)
    (R : ℝ) (hr : ∀ n, |rs n| ≤ R) (ha : ∀ n, 0 ≤ αs n ∧ αs n ≤ 1)
    (hs : ∀ x a, Tendsto (fun N => ∑ n ∈ range N, visitRate xs as αs x a (n+1)) atTop atTop)
    (hnoise : ∀ x a, ∃ l : ℝ, Tendsto
      (fun N => ∑ n ∈ range N, visitRate xs as αs x a (n+1)*pathNoise M γ Q0 xs as ys rs αs n)
      atTop (𝓝 l)) :
    ∀ x a, Tendsto (fun n => qIter γ Q0 xs as ys rs αs n x a) atTop (𝓝 (Qstar x a)) := by
  classical
  let q := qIter γ Q0 xs as ys rs αs
  let e : ℕ → X × A → ℝ := fun n i => q n i.1 i.2-Qstar i.1 i.2
  let b : ℕ → X × A → ℝ := fun n i => bellman M γ (q n) i.1 i.2-Qstar i.1 i.2
  let a : ℕ → X × A → ℝ := fun n i => visitRate xs as αs i.1 i.2 (n+1)
  let S : ℕ → X × A → ℝ := fun N i => ∑ n ∈ range N, a n i*pathNoise M γ Q0 xs as ys rs αs n
  have hrate : ∀ n i, 0 ≤ a n i ∧ a n i ≤ 1 := by
    intro n i
    dsimp [a,visitRate]
    split_ifs
    · exact ha (n+1)
    · norm_num
  obtain ⟨K,hK,h0,hRK⟩ := initial_uniform_bound γ R hγ1 Q0
  have hqb := qIter_bound γ Q0 xs as ys rs αs hγ0.le hK h0 hr ha hRK
  have heb : ∃ B, ∀ n, ‖e n‖ ≤ B := by
    refine ⟨K+‖Qstar‖,fun n => ?_⟩
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    have hstar := (norm_le_pi_norm (Qstar i.1) i.2).trans (norm_le_pi_norm Qstar i.1)
    rw [Real.norm_eq_abs] at hstar
    change |q n i.1 i.2-Qstar i.1 i.2| ≤ _
    have ht : |q n i.1 i.2-Qstar i.1 i.2| ≤ |q n i.1 i.2|+|Qstar i.1 i.2| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (q n i.1 i.2) (Qstar i.1 i.2)
    exact ht.trans (add_le_add (hqb n i.1 i.2) hstar)
  have hb : ∀ n i, |b n i| ≤ γ*‖e n‖ := by
    intro n i
    have hd := bellman_difference M hγ0.le (q n) Qstar
      (fun x a => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (e n) (x,a)) i.1 i.2
    change |bellman M γ (q n) i.1 i.2-Qstar i.1 i.2| ≤ _
    have heq : bellman M γ Qstar i.1 i.2 = Qstar i.1 i.2 := (hQ i.1 i.2).symm
    rwa [heq] at hd
  have hrec : ∀ n i, e (n+1) i = (1-a n i)*e n i+a n i*b n i+(S (n+1) i-S n i) := by
    intro n i
    have hstep := qIter_noise_step M γ Q0 xs as ys rs αs n i.1 i.2
    dsimp [e,b,S,a,q]
    rw [sum_range_succ]
    rw [hstep]
    ring
  have hlim : ∃ l : X × A → ℝ, Tendsto S atTop (𝓝 l) := by
    choose l hl using (fun i : X × A => hnoise i.1 i.2)
    exact ⟨l,tendsto_pi_nhds.mpr hl⟩
  obtain ⟨l,hl⟩ := hlim
  have heconv := asynchronous_noise_tendsto e b S a γ hγ0.le hγ1 hrate
    (fun i => hs i.1 i.2) heb hb hrec l hl
  intro x a
  have hc := (tendsto_pi_nhds.mp heconv (x,a)).add_const (Qstar x a)
  simpa [e,q] using hc

end QLearning.Convergence.QLFresh



namespace QLearning.Convergence.QLFresh
open MeasureTheory ProbabilityTheory Filter Topology

theorem native_theorem_q_learning_converges {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    [MeasurableSpace X] [DiscreteMeasurableSpace X] [MeasurableSpace A] [DiscreteMeasurableSpace A]
    (M : FiniteMDP X A) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (Qstar : X → A → ℝ) (hQ : IsOptimalQ M γ Qstar) (Q0 : X → A → ℝ)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ)
    (xs : ℕ → Ω → X) (as : ℕ → Ω → A) (ys : ℕ → Ω → X) (rs αs : ℕ → Ω → ℝ)
    (hxs : ∀ n, Measurable[ℱ n] (xs (n + 1)))
    (has : ∀ n, Measurable[ℱ n] (as (n + 1)))
    (hαs : ∀ n, Measurable[ℱ n] (αs (n + 1)))
    (hys : ∀ n, Measurable[ℱ (n + 1)] (ys (n + 1)))
    (hrs : ∀ n, Measurable[ℱ (n + 1)] (rs (n + 1)))
    (htrans : ∀ n y, μ[fun ω => if ys (n + 1) ω = y then (1 : ℝ) else 0 | ℱ n]
      =ᵐ[μ] fun ω => M.P (xs (n + 1) ω) (as (n + 1) ω) y)
    (hrew : ∀ n, μ[rs (n + 1) | ℱ n] =ᵐ[μ] fun ω => M.R (xs (n + 1) ω) (as (n + 1) ω))
    (Rbar : ℝ) (hbdd : ∀ n ω, |rs n ω| ≤ Rbar)
    (hα : ∀ n ω, 0 ≤ αs n ω ∧ αs n ω < 1)
    (h3 : ∀ᵐ ω ∂μ, ∀ x a,
      Tendsto (fun N => ∑ n ∈ Finset.range N,
        visitRate (fun k => xs k ω) (fun k => as k ω) (fun k => αs k ω) x a (n + 1)) atTop atTop ∧
      Summable (fun n =>
        visitRate (fun k => xs k ω) (fun k => as k ω) (fun k => αs k ω) x a (n + 1) ^ 2)) :
    ∀ᵐ ω ∂μ, ∀ x a,
      Tendsto (fun n => qIter γ Q0 (fun k => xs k ω) (fun k => as k ω) (fun k => ys k ω)
          (fun k => rs k ω) (fun k => αs k ω) n x a) atTop (𝓝 (Qstar x a)) := by
  have hsq : ∀ᵐ ω ∂μ, ∀ x a, Summable (fun n =>
      visitRate (fun k => xs k ω) (fun k => as k ω) (fun k => αs k ω) x a (n+1)^2) :=
    h3.mono (fun ω h x a => (h x a).2)
  have hnoise := native_noise_series (μ := μ) M γ hγ0 hγ1 Q0 ℱ xs as ys rs αs
    hxs has hαs hys hrs htrans hrew Rbar hbdd hα hsq
  have hall : ∀ᵐ ω ∂μ, ∀ x a, ∃ l : ℝ, Tendsto (fun N => ∑ n ∈ Finset.range N,
      visitRate (fun k => xs k ω) (fun k => as k ω) (fun k => αs k ω) x a (n+1)*
      pathNoise M γ Q0 (fun k => xs k ω) (fun k => as k ω) (fun k => ys k ω)
        (fun k => rs k ω) (fun k => αs k ω) n) atTop (𝓝 l) := by
    rw [ae_all_iff]
    intro x
    exact ae_all_iff.mpr (hnoise x)
  filter_upwards [h3,hall] with ω hω hnω
  exact pathwise_convergence M γ hγ0 hγ1 Qstar hQ Q0 _ _ _ _ _ Rbar
    (fun n => hbdd n ω) (fun n => ⟨(hα n ω).1,(hα n ω).2.le⟩)
    (fun x a => (hω x a).1) hnω

end QLearning.Convergence.QLFresh


open MeasureTheory ProbabilityTheory Filter Topology
namespace QLearning.Convergence

theorem theorem_q_learning_converges {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    [MeasurableSpace X] [DiscreteMeasurableSpace X] [MeasurableSpace A] [DiscreteMeasurableSpace A]
    (M : FiniteMDP X A) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (Qstar : X → A → ℝ) (hQ : IsOptimalQ M γ Qstar) (Q0 : X → A → ℝ)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ)
    (xs : ℕ → Ω → X) (as : ℕ → Ω → A) (ys : ℕ → Ω → X) (rs αs : ℕ → Ω → ℝ)
    (hxs : ∀ n, Measurable[ℱ n] (xs (n + 1)))
    (has : ∀ n, Measurable[ℱ n] (as (n + 1)))
    (hαs : ∀ n, Measurable[ℱ n] (αs (n + 1)))
    (hys : ∀ n, Measurable[ℱ (n + 1)] (ys (n + 1)))
    (hrs : ∀ n, Measurable[ℱ (n + 1)] (rs (n + 1)))
    (htrans : ∀ n y, μ[fun ω => if ys (n + 1) ω = y then (1 : ℝ) else 0 | ℱ n]
      =ᵐ[μ] fun ω => M.P (xs (n + 1) ω) (as (n + 1) ω) y)
    (hrew : ∀ n, μ[rs (n + 1) | ℱ n] =ᵐ[μ] fun ω => M.R (xs (n + 1) ω) (as (n + 1) ω))
    (Rbar : ℝ) (hbdd : ∀ n ω, |rs n ω| ≤ Rbar)
    (hα : ∀ n ω, 0 ≤ αs n ω ∧ αs n ω < 1)
    (h3 : ∀ᵐ ω ∂μ, ∀ x a,
      Tendsto (fun N => ∑ n ∈ Finset.range N,
        visitRate (fun k => xs k ω) (fun k => as k ω) (fun k => αs k ω) x a (n + 1)) atTop atTop ∧
      Summable (fun n =>
        visitRate (fun k => xs k ω) (fun k => as k ω) (fun k => αs k ω) x a (n + 1) ^ 2)) :
    ∀ᵐ ω ∂μ, ∀ x a,
      Tendsto (fun n => qIter γ Q0 (fun k => xs k ω) (fun k => as k ω) (fun k => ys k ω)
          (fun k => rs k ω) (fun k => αs k ω) n x a) atTop (𝓝 (Qstar x a)) := by
  exact QLFresh.native_theorem_q_learning_converges M γ hγ0 hγ1 Qstar hQ Q0 μ ℱ xs as ys rs αs hxs has hαs hys hrs htrans hrew Rbar hbdd hα h3

end QLearning.Convergence


open QLearning.Convergence
open MeasureTheory ProbabilityTheory Filter Topology
theorem solution {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    [MeasurableSpace X] [DiscreteMeasurableSpace X] [MeasurableSpace A] [DiscreteMeasurableSpace A]
    (M : FiniteMDP X A) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (Qstar : X → A → ℝ) (hQ : IsOptimalQ M γ Qstar) (Q0 : X → A → ℝ)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ)
    (xs : ℕ → Ω → X) (as : ℕ → Ω → A) (ys : ℕ → Ω → X) (rs αs : ℕ → Ω → ℝ)
    (hxs : ∀ n, Measurable[ℱ n] (xs (n + 1)))
    (has : ∀ n, Measurable[ℱ n] (as (n + 1)))
    (hαs : ∀ n, Measurable[ℱ n] (αs (n + 1)))
    (hys : ∀ n, Measurable[ℱ (n + 1)] (ys (n + 1)))
    (hrs : ∀ n, Measurable[ℱ (n + 1)] (rs (n + 1)))
    (htrans : ∀ n y, μ[fun ω => if ys (n + 1) ω = y then (1 : ℝ) else 0 | ℱ n]
      =ᵐ[μ] fun ω => M.P (xs (n + 1) ω) (as (n + 1) ω) y)
    (hrew : ∀ n, μ[rs (n + 1) | ℱ n] =ᵐ[μ] fun ω => M.R (xs (n + 1) ω) (as (n + 1) ω))
    (Rbar : ℝ) (hbdd : ∀ n ω, |rs n ω| ≤ Rbar)
    (hα : ∀ n ω, 0 ≤ αs n ω ∧ αs n ω < 1)
    (h3 : ∀ᵐ ω ∂μ, ∀ x a,
      Tendsto (fun N => ∑ n ∈ Finset.range N,
        visitRate (fun k => xs k ω) (fun k => as k ω) (fun k => αs k ω) x a (n + 1)) atTop atTop ∧
      Summable (fun n =>
        visitRate (fun k => xs k ω) (fun k => as k ω) (fun k => αs k ω) x a (n + 1) ^ 2)) :
    ∀ᵐ ω ∂μ, ∀ x a,
      Tendsto (fun n => qIter γ Q0 (fun k => xs k ω) (fun k => as k ω) (fun k => ys k ω)
          (fun k => rs k ω) (fun k => αs k ω) n x a) atTop (𝓝 (Qstar x a)) := by
  exact QLearning.Convergence.theorem_q_learning_converges M γ hγ0 hγ1 Qstar hQ Q0 μ ℱ xs as ys rs αs hxs has hαs hys hrs htrans hrew Rbar hbdd hα h3
