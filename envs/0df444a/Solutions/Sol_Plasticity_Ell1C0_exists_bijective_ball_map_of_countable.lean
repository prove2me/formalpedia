-- Prove2me | solution 1 for Plasticity.Ell1C0.exists_bijective_ball_map_of_countable
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-11-18T20:10:14.472259+00:00
-- url     : https://prove2.me/submissions/c7197fa6-08f8-48aa-9bf7-9376c410460d

import Definitions.Def_Plasticity_SeqSpace
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Logic.Encodable.Basic
import Theorems.Thm_Plasticity_Polish_exists_isClosed_continuousOn_bijOn
import Theorems.Thm_Plasticity_Ell1_exists_closed_code_set
import Theorems.Thm_Plasticity_Ell1C0_exists_tree_clamp_family

namespace Sol_Plasticity_Ell1C0_exists_bijective_ball_map_of_countable
open Plasticity Filter Topology MeasureTheory
noncomputable section

def relabelFun {α β : Type*} (e : α ≃ β) (p : ENNReal) [Fact (1 ≤ p)]
    (x : lp (fun _ : α => ℝ) p) : lp (fun _ : β => ℝ) p :=
  ⟨fun b => x (e.symm b), by
    have hx : Memℓp (x : ∀ _ : α, ℝ) p := x.2
    show Memℓp _ p
    rcases eq_or_ne p ⊤ with rfl | hp
    · rw [memℓp_infty_iff] at hx ⊢
      obtain ⟨C, hC⟩ := hx
      exact ⟨C, by rintro _ ⟨b, rfl⟩; exact hC ⟨e.symm b, rfl⟩⟩
    · have h0 : p ≠ 0 := by
        have := Fact.out (p := 1 ≤ p)
        intro h; rw [h] at this; simp at this
      rw [memℓp_gen_iff (ENNReal.toReal_pos h0 hp)] at hx ⊢
      exact (e.symm.summable_iff).2 hx⟩

theorem relabelFun_apply {α β : Type*} (e : α ≃ β) (p : ENNReal) [Fact (1 ≤ p)]
    (x : lp (fun _ : α => ℝ) p) (b : β) : relabelFun e p x b = x (e.symm b) := rfl

theorem relabelFun_norm {α β : Type*} (e : α ≃ β) (p : ENNReal) [Fact (1 ≤ p)]
    (x : lp (fun _ : α => ℝ) p) : ‖relabelFun e p x‖ = ‖x‖ := by
  have h0 : 0 < p := lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)
  rcases eq_or_ne p ⊤ with rfl | hp
  · rw [lp.norm_eq_ciSup, lp.norm_eq_ciSup]
    exact e.symm.iSup_comp (g := fun a => ‖x a‖)
  · rw [lp.norm_eq_tsum_rpow (ENNReal.toReal_pos h0.ne' hp), lp.norm_eq_tsum_rpow (ENNReal.toReal_pos h0.ne' hp)]
    congr 1
    exact e.symm.tsum_eq (fun a => ‖x a‖ ^ p.toReal)

def relabel {α β : Type*} (e : α ≃ β) (p : ENNReal) [Fact (1 ≤ p)] :
    lp (fun _ : α => ℝ) p ≃ₗᵢ[ℝ] lp (fun _ : β => ℝ) p where
  toFun := relabelFun e p
  invFun := relabelFun e.symm p
  map_add' x y := by ext b; rfl
  map_smul' c x := by ext b; rfl
  left_inv x := by ext a; simp [relabelFun_apply]
  right_inv x := by ext a; simp [relabelFun_apply]
  norm_map' := relabelFun_norm e p

theorem relabel_apply {α β : Type*} (e : α ≃ β) (p : ENNReal) [Fact (1 ≤ p)]
    (x : lp (fun _ : α => ℝ) p) (b : β) : relabel e p x b = x (e.symm b) := rfl

theorem relabel_mem_c0 {α β : Type*} (e : α ≃ β) (x : Linf α) (hx : x ∈ c0 α) :
    relabel e ⊤ x ∈ c0 β := by
  have h : Tendsto (fun b => x (e.symm b)) cofinite (𝓝 0) :=
    hx.comp e.symm.injective.tendsto_cofinite
  exact h

def relabelC0 {α β : Type*} (e : α ≃ β) : c0 α ≃ₗᵢ[ℝ] c0 β :=
  ((relabel e ⊤).submoduleMap (c0 α)).trans (LinearIsometryEquiv.ofEq _ _ (by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩; exact relabel_mem_c0 e x hx
    · intro y hy
      refine ⟨(relabel e ⊤).symm y, ?_, by simp⟩
      have := relabel_mem_c0 e.symm y hy
      exact this))


abbrev J := ℕ × ℕ
abbrev I := J × ℕ
abbrev L1 := lp (fun _ : J => ℝ) 1
abbrev B := Metric.closedBall (0 : L1) 1
abbrev T := Metric.closedBall (0 : c0 I) 1

def Hfun (x : L1) (i : I) : ℝ := (2 : ℝ) ^ (-((i.2 : ℤ) + 2)) * x i.1
def Sim (f g : I → ℝ) : Prop := {i | f i ≠ g i}.Finite
theorem Sim.trans {f g h : I → ℝ} (a : Sim f g) (b : Sim g h) : Sim f h :=
  (a.union b).subset (by intro i hi; by_contra hc; simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc; exact hi (hc.1.trans hc.2))

theorem Sim.symm {f g : I → ℝ} (a : Sim f g) : Sim g f :=
  a.subset (by intro i hi; exact fun h => hi h.symm)

theorem Sim.refl (f : I → ℝ) : Sim f f := by simp [Sim]

theorem Hinj (x x' : L1) (h : Sim (Hfun x) (Hfun x')) : x = x' := by
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ x' j := by
    by_contra hc; push_neg at hc; exact hne (lp.ext (funext hc))
  have hinf : Set.Infinite {i : I | Hfun x i ≠ Hfun x' i} := by
    have : Function.Injective (fun k : ℕ => ((j, k) : I)) := fun a b hab => by simpa using hab
    refine Set.infinite_of_injective_forall_mem this (fun k => ?_)
    simp only [Set.mem_setOf_eq, Hfun]
    intro hh
    have hp : (2 : ℝ) ^ (-((k : ℤ) + 2)) ≠ 0 := by positivity
    exact hj (mul_left_cancel₀ hp hh)
  exact hinf h


theorem norm_L1 (x : L1) : ‖x‖ = ∑' j, |x j| := by
  have h0 : (0:ℝ) < (1 : ENNReal).toReal := by simp
  rw [lp.norm_eq_tsum_rpow h0]
  simp

theorem summable_L1 (x : L1) : Summable (fun j => |x j|) := by
  have := (lp.memℓp x : Memℓp (x : ∀ _ : J, ℝ) 1)
  rw [memℓp_gen_iff (by norm_num)] at this
  simpa using this

def mass (n : ℕ) (x : L1) : ℝ := ∑' k, |x (n, k)|

theorem summable_mass (x : L1) : Summable (fun n => mass n x) :=
  (summable_L1 x).prod

theorem sum_mass (x : L1) : ∑' n, mass n x = ‖x‖ := by
  rw [norm_L1, (summable_L1 x).tsum_prod]; rfl

theorem mass_nonneg (n : ℕ) (x : L1) : 0 ≤ mass n x := tsum_nonneg (fun _ => abs_nonneg _)

def Dset (x : L1) : Set ℕ := {n | ‖x‖ / 4 < mass n x}

theorem Dset_finite (x : L1) : (Dset x).Finite := by
  rcases eq_or_lt_of_le (norm_nonneg x) with h | h
  · have : x = 0 := norm_eq_zero.1 h.symm
    subst this
    have : Dset (0 : L1) = ∅ := by
      ext n; simp [Dset, mass]
    rw [this]; exact Set.finite_empty
  · have ht := (summable_mass x).tendsto_cofinite_zero
    have hev : ∀ᶠ n in cofinite, mass n x < ‖x‖ / 4 :=
      (tendsto_order.1 ht).2 (‖x‖ / 4) (by linarith)
    rw [eventually_cofinite] at hev
    refine hev.subset ?_
    intro n hn
    simp only [Set.mem_setOf_eq, Dset] at hn ⊢
    linarith

def rk (x : L1) : ℕ := sInf {n | ∀ m ∈ Dset x, m < n}

theorem rk_set_nonempty (x : L1) : {n | ∀ m ∈ Dset x, m < n}.Nonempty := by
  obtain ⟨N, hN⟩ := (Dset_finite x).bddAbove
  exact ⟨N + 1, fun m hm => Nat.lt_succ_of_le (hN hm)⟩

theorem lt_rk {x : L1} {m : ℕ} (hm : m ∈ Dset x) : m < rk x :=
  Nat.sInf_mem (rk_set_nonempty x) m hm

theorem rk_le {x : L1} {n : ℕ} (h : ∀ m ∈ Dset x, m < n) : rk x ≤ n := Nat.sInf_le h

theorem rk_eq_iff (x : L1) (n : ℕ) :
    rk x = n ↔ (∀ m ∈ Dset x, m < n) ∧ (n = 0 ∨ n - 1 ∈ Dset x) := by
  constructor
  · rintro rfl
    refine ⟨fun m hm => lt_rk hm, ?_⟩
    by_cases h0 : rk x = 0
    · exact Or.inl h0
    · right
      have hnot : rk x - 1 ∉ {n | ∀ m ∈ Dset x, m < n} := Nat.notMem_of_lt_sInf (show rk x - 1 < rk x by omega)
      simp only [Set.mem_setOf_eq, not_forall] at hnot
      obtain ⟨m, hm, hle⟩ := hnot
      have := lt_rk hm
      have : m = rk x - 1 := by omega
      rwa [this] at hm
  · rintro ⟨h1, h2⟩
    apply le_antisymm (rk_le h1)
    rcases h2 with rfl | h2
    · exact Nat.zero_le _
    · have := lt_rk h2; omega

theorem rk_zero : rk 0 = 0 := by
  rw [rk_eq_iff]
  refine ⟨fun m hm => ?_, Or.inl rfl⟩
  simp [Dset, mass] at hm

/-! ### Polish structure -/

theorem single_mem_c0 {α : Type*} [DecidableEq α] (i : α) (a : ℝ) :
    (lp.single ⊤ i a : Linf α) ∈ c0 α := by
  show Tendsto (⇑(lp.single ⊤ i a : Linf α)) cofinite (𝓝 0)
  apply tendsto_const_nhds.congr'
  have : ∀ᶠ j in cofinite, j ≠ i := by
    rw [eventually_cofinite]; simp
  filter_upwards [this] with j hj
  simp [lp.single_apply, hj]

theorem c0_closed (α : Type*) : IsClosed ((c0 α : Submodule ℝ (Linf α)) : Set (Linf α)) := by
  refine isClosed_of_closure_subset (fun x hx => ?_)
  show Tendsto (⇑x) cofinite (𝓝 0)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx (ε/2) (by linarith)
  have hy' : Tendsto (⇑y) cofinite (𝓝 0) := hy
  have := (Metric.tendsto_nhds.1 hy') (ε/2) (by linarith)
  filter_upwards [this] with i hi
  have h1 : ‖(x - y) i‖ ≤ ‖x - y‖ := lp.norm_apply_le_norm ENNReal.top_ne_zero (x - y) i
  rw [dist_eq_norm] at hxy
  simp only [Real.dist_eq, sub_zero] at hi ⊢
  have h2 : |x i| ≤ |y i| + ‖(x-y) i‖ := by
    simp only [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs]
    calc |x i| = |y i + (x i - y i)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  linarith

instance c0_complete (α : Type*) : CompleteSpace (c0 α) := (c0_closed α).completeSpace_coe

def eL1 : J → L1 := fun j => lp.single (E := fun _ : J => ℝ) 1 j (1:ℝ)

instance sep_L1 : TopologicalSpace.SeparableSpace L1 := by
  have h : (Set.univ : Set L1) ⊆ closure (Submodule.span ℝ (Set.range eL1) : Set L1) := by
    intro f _
    have hf := lp.hasSum_single (E := fun _ : J => ℝ) (p := 1) ENNReal.one_ne_top f
    refine mem_closure_of_tendsto hf (Eventually.of_forall fun s => ?_)
    refine Submodule.sum_mem _ (fun j _ => ?_)
    have : lp.single (E := fun _ : J => ℝ) 1 j (f j) = (f j) • eL1 j := by
      ext k; simp [eL1, lp.single_apply, Pi.single_apply]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hs : TopologicalSpace.IsSeparable (Submodule.span ℝ (Set.range eL1) : Set L1) :=
    TopologicalSpace.IsSeparable.span (Set.countable_range _).isSeparable
  exact (TopologicalSpace.isSeparable_univ_iff.1 (hs.closure.mono h))

instance sep_c0 : TopologicalSpace.SeparableSpace (c0 I) := by
  classical
  let e : I → c0 I := fun i => ⟨lp.single ⊤ i (1:ℝ), single_mem_c0 i 1⟩
  have h : (Set.univ : Set (c0 I)) ⊆ closure (Submodule.span ℝ (Set.range e) : Set (c0 I)) := by
    intro t _
    rw [Metric.mem_closure_iff]
    intro ε hε
    have ht : Tendsto (⇑(t : Linf I)) cofinite (𝓝 0) := t.2
    have hfin : {i | ε / 2 ≤ |(t : Linf I) i|}.Finite := by
      have := (Metric.tendsto_nhds.1 ht) (ε/2) (by linarith)
      rw [eventually_cofinite] at this
      refine this.subset ?_
      intro i hi
      simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at hi ⊢
      linarith
    refine ⟨∑ i ∈ hfin.toFinset, ((t : Linf I) i) • e i, ?_, ?_⟩
    · exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    · have key : ‖(t : Linf I) - ((∑ i ∈ hfin.toFinset, ((t : Linf I) i) • e i : c0 I) : Linf I)‖ ≤ ε / 2 := by
        refine lp.norm_le_of_forall_le (by linarith) (fun j => ?_)
        have hc : ((∑ i ∈ hfin.toFinset, ((t : Linf I) i) • e i : c0 I) : Linf I) j
            = if j ∈ hfin.toFinset then (t : Linf I) j else 0 := by
          simp only [Submodule.coe_sum, Submodule.coe_smul, lp.coeFn_sum, Finset.sum_apply,
            lp.coeFn_smul, Pi.smul_apply, e, lp.single_apply, smul_eq_mul]
          simp [Pi.single_apply, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
        simp only [lp.coeFn_sub, Pi.sub_apply, hc]
        split_ifs with hj
        · simp; linarith
        · simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_le] at hj
          simp only [sub_zero, Real.norm_eq_abs]; linarith
      rw [dist_eq_norm]
      have : ‖t - ∑ i ∈ hfin.toFinset, ((t : Linf I) i) • e i‖ = ‖(t : Linf I) - ((∑ i ∈ hfin.toFinset, ((t : Linf I) i) • e i : c0 I) : Linf I)‖ := rfl
      rw [this]; linarith
  have hs : TopologicalSpace.IsSeparable (Submodule.span ℝ (Set.range e) : Set (c0 I)) :=
    TopologicalSpace.IsSeparable.span (Set.countable_range _).isSeparable
  exact (TopologicalSpace.isSeparable_univ_iff.1 (hs.closure.mono h))

instance : PolishSpace L1 := inferInstance
instance : PolishSpace (c0 I) := inferInstance
instance : MeasurableSpace L1 := borel L1
instance : BorelSpace L1 := ⟨rfl⟩
instance : MeasurableSpace (c0 I) := borel (c0 I)
instance : BorelSpace (c0 I) := ⟨rfl⟩

/-! ### Hc, SI, Qset -/

def ev (t : c0 I) (i : I) : ℝ := ((t : Linf I)) i

theorem ev_lip (i : I) : LipschitzWith 1 (fun v : c0 I => ev v i) := by
  refine LipschitzWith.of_dist_le_mul (fun v w => ?_)
  have h : ‖((v - w : c0 I) : Linf I) i‖ ≤ ‖((v - w : c0 I) : Linf I)‖ :=
    lp.norm_apply_le_norm ENNReal.top_ne_zero _ i
  simp only [ev, NNReal.coe_one, one_mul, dist_eq_norm, Real.norm_eq_abs]
  have h2 : ((v - w : c0 I) : Linf I) i = (v : Linf I) i - (w : Linf I) i := rfl
  rw [h2] at h
  simpa [Real.norm_eq_abs] using h

theorem abs_le_norm (x : L1) (j : J) : |x j| ≤ ‖x‖ := by
  have := lp.norm_apply_le_norm (E := fun _ : J => ℝ) (p := 1) (by norm_num) x j
  simpa using this

theorem Hfun_bdd (x : L1) (i : I) : |Hfun x i| ≤ ‖x‖ := by
  unfold Hfun
  rw [abs_mul]
  have h1 : |(2 : ℝ) ^ (-((i.2 : ℤ) + 2))| ≤ 1 := by
    rw [abs_of_pos (by positivity)]
    apply zpow_le_one_of_nonpos₀ (by norm_num); omega
  calc _ ≤ 1 * |x i.1| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ ≤ ‖x‖ := by rw [one_mul]; exact abs_le_norm x i.1

theorem Hfun_sub (x y : L1) (i : I) : Hfun x i - Hfun y i = Hfun (x - y) i := by
  simp [Hfun, mul_sub]

theorem Hfun_mem_c0 (x : L1) : Tendsto (Hfun x) cofinite (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hx := (summable_L1 x).tendsto_cofinite_zero
  have hS : {j : J | ε ≤ |x j|}.Finite := by
    have := (Metric.tendsto_nhds.1 hx) ε hε
    rw [eventually_cofinite] at this
    refine this.subset ?_
    intro j hj
    simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, abs_abs] at hj ⊢
    linarith
  have hK : {k : ℕ | ε ≤ (2 : ℝ) ^ (-((k : ℤ) + 2)) * ‖x‖}.Finite := by
    have h2 : Tendsto (fun k : ℕ => (2 : ℝ) ^ (-((k : ℤ) + 2)) * ‖x‖) atTop (𝓝 0) := by
      have : Tendsto (fun k : ℕ => (2 : ℝ) ^ (-((k : ℤ) + 2))) atTop (𝓝 0) := by
        have h3 : Tendsto (fun k : ℕ => ((1:ℝ)/2) ^ (k + 2)) atTop (𝓝 0) :=
          (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp (tendsto_add_atTop_nat 2)
        refine h3.congr (fun k => ?_)
        rw [show -((k : ℤ) + 2) = -(((k + 2 : ℕ) : ℤ)) by push_cast; ring, zpow_neg, zpow_natCast]
        simp
      simpa using this.mul_const ‖x‖
    have := (Metric.tendsto_nhds.1 h2) ε hε
    rw [eventually_atTop] at this
    obtain ⟨N, hN⟩ := this
    refine (Set.finite_Iio N).subset (fun k hk => ?_)
    simp only [Set.mem_ofPred_eq] at hk
    by_contra hc
    have := hN k (not_lt.1 hc)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this
    linarith
  refine (hS.prod hK).subset (fun i hi => ?_)
  have hi' : ε ≤ |Hfun x i| := by
    by_contra h; exact hi (by simpa [Real.dist_eq] using not_le.1 h)
  refine ⟨?_, ?_⟩
  · simp only [Set.mem_ofPred_eq]
    refine le_trans hi' ?_
    unfold Hfun; rw [abs_mul, abs_of_pos (by positivity)]
    have : (2 : ℝ) ^ (-((i.2 : ℤ) + 2)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
    nlinarith [abs_nonneg (x i.1), abs_nonneg (Hfun x i)]
  · simp only [Set.mem_ofPred_eq]
    refine le_trans hi' ?_
    unfold Hfun; rw [abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left (abs_le_norm x i.1) (by positivity)

def HL (x : L1) : Linf I := ⟨Hfun x, by
  show Memℓp (Hfun x) ⊤
  rw [memℓp_infty_iff]
  exact ⟨‖x‖, by rintro _ ⟨i, rfl⟩; simpa using Hfun_bdd x i⟩⟩

def Hc (x : L1) : c0 I := ⟨HL x, Hfun_mem_c0 x⟩

theorem ev_Hc (x : L1) (i : I) : ev (Hc x) i = Hfun x i := rfl

theorem Hc_lip : LipschitzWith 1 Hc := by
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  show ‖((Hc x - Hc y : c0 I) : Linf I)‖ ≤ _
  refine lp.norm_le_of_forall_le (norm_nonneg _) (fun i => ?_)
  have : ((Hc x - Hc y : c0 I) : Linf I) i = Hfun (x - y) i := by
    rw [← Hfun_sub]; rfl
  rw [this, Real.norm_eq_abs]
  exact Hfun_bdd _ i

def SI : Set (c0 I) := {v | {i | ev v i ≠ 0}.Finite}

theorem measurableSet_SI : MeasurableSet (SI : Set (c0 I)) := by
  have : (SI : Set (c0 I)) = ⋃ N : ℕ, ⋂ i : I, {v : c0 I | Encodable.encode i < N ∨ ev v i = 0} := by
    ext v
    simp only [SI, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter]
    constructor
    · intro h
      obtain ⟨N, hN⟩ := (h.image Encodable.encode).bddAbove
      refine ⟨N + 1, fun i => ?_⟩
      by_cases hi : ev v i = 0
      · exact Or.inr hi
      · left; have := hN ⟨i, hi, rfl⟩; omega
    · rintro ⟨N, hN⟩
      refine (Set.finite_lt_nat N).preimage (Encodable.encode_injective.injOn) |>.subset ?_
      intro i hi
      simp only [Set.mem_ofPred_eq, Set.mem_preimage] at hi ⊢
      rcases hN i with h | h
      · exact h
      · exact absurd h hi
  rw [this]
  refine MeasurableSet.iUnion (fun N => MeasurableSet.iInter (fun i => ?_))
  by_cases h : Encodable.encode i < N
  · simp [h]
  · simp only [h, false_or]
    exact (isClosed_eq (ev_lip i).continuous continuous_const).measurableSet

theorem mass_le_add (n : ℕ) (x y : L1) : mass n x ≤ mass n y + ‖x - y‖ := by
  have inj : Function.Injective (fun k : ℕ => ((n, k) : J)) := fun a b h => by simpa using h
  have sx : Summable (fun k : ℕ => |x (n, k)|) := (summable_L1 x).comp_injective inj
  have sy : Summable (fun k : ℕ => |y (n, k)|) := (summable_L1 y).comp_injective inj
  have sd : Summable (fun k : ℕ => |(x - y) (n, k)|) := (summable_L1 (x - y)).comp_injective inj
  have h1 : mass n x ≤ ∑' k, (|y (n, k)| + |(x - y) (n, k)|) := by
    refine Summable.tsum_le_tsum (fun k => ?_) sx (sy.add sd)
    have : x (n, k) = y (n, k) + (x - y) (n, k) := by simp
    rw [this]
    have := abs_add_le (y (n, k)) ((x - y) (n, k))
    simpa [this] using this
  rw [Summable.tsum_add sy sd] at h1
  have h2 : ∑' k, |(x - y) (n, k)| ≤ ‖x - y‖ := by
    rw [norm_L1]
    exact tsum_comp_le_tsum_of_inj (summable_L1 (x - y)) (fun _ => abs_nonneg _) inj
  unfold mass at h1 ⊢; linarith

theorem continuous_mass (n : ℕ) : Continuous (mass n : L1 → ℝ) := by
  have : LipschitzWith 1 (mass n : L1 → ℝ) := by
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    simp only [NNReal.coe_one, one_mul]
    rw [Real.dist_eq, dist_eq_norm, abs_le]
    have h1 := mass_le_add n x y
    have h2 := mass_le_add n y x
    rw [norm_sub_rev] at h2
    constructor <;> linarith
  exact this.continuous

theorem measurableSet_D (m : ℕ) : MeasurableSet {x : L1 | m ∈ Dset x} :=
  measurableSet_lt (continuous_norm.div_const 4).measurable (continuous_mass m).measurable

theorem measurableSet_rk (n : ℕ) : MeasurableSet {x : L1 | rk x = n} := by
  have : {x : L1 | rk x = n} = (⋂ m, {x : L1 | m ∈ Dset x → m < n}) ∩ {x | n = 0 ∨ n - 1 ∈ Dset x} := by
    ext x; simp [rk_eq_iff]
  rw [this]
  refine MeasurableSet.inter (MeasurableSet.iInter fun m => ?_) ?_
  · by_cases h : m < n
    · simp [h]
    · have : {x : L1 | m ∈ Dset x → m < n} = {x | m ∈ Dset x}ᶜ := by ext x; simp [h]
      rw [this]; exact (measurableSet_D m).compl
  · by_cases h : n = 0
    · simp [h]
    · simp only [h, false_or]; exact measurableSet_D _

def Own (t : c0 I) (x : L1) : Prop := ‖x‖ ≤ 1 ∧ Sim (ev t) (Hfun x)

theorem Own_unique {t : c0 I} {x x' : L1} (h : Own t x) (h' : Own t x') : x = x' :=
  Hinj x x' (h.2.symm.trans h'.2)

def rho (t : c0 I) : ℕ := by
  classical exact if h : ∃ x, Own t x then rk h.choose else 0

theorem rho_eq {t : c0 I} {x : L1} (h : Own t x) : rho t = rk x := by
  have hex : ∃ x, Own t x := ⟨x, h⟩
  unfold rho
  rw [dif_pos hex, Own_unique hex.choose_spec h]

theorem rho_none {t : c0 I} (h : ¬ ∃ x, Own t x) : rho t = 0 := by
  unfold rho; rw [dif_neg h]

def Qset (n : ℕ) : Set (c0 I) := {t | ∃ x, Own t x ∧ rk x = n}

def Phi (p : L1 × c0 I) : c0 I := Hc p.1 + p.2

theorem measurableSet_Qset (n : ℕ) : MeasurableSet (Qset n) := by
  let s : Set (L1 × c0 I) := {p | ‖p.1‖ ≤ 1 ∧ rk p.1 = n} ∩ {p | p.2 ∈ SI}
  have hs : MeasurableSet s := by
    refine MeasurableSet.inter ?_ ?_
    · exact ((measurableSet_le continuous_norm.measurable measurable_const).inter
        (measurableSet_rk n)).preimage measurable_fst
    · exact measurableSet_SI.preimage measurable_snd
  have hc : ContinuousOn Phi s := by
    apply Continuous.continuousOn
    exact (Hc_lip.continuous.comp continuous_fst).add continuous_snd
  have hi : Set.InjOn Phi s := by
    rintro ⟨x, v⟩ ⟨⟨hx1, hx2⟩, hv⟩ ⟨x', v'⟩ ⟨⟨hx1', hx2'⟩, hv'⟩ h
    simp only [Phi] at h
    have hS : Sim (Hfun x) (Hfun x') := by
      refine (hv.union hv').subset (fun i hi => ?_)
      simp only [Set.mem_ofPred_eq, Set.mem_union] at hi ⊢
      by_contra hc
      push_neg at hc
      apply hi
      have := congrArg (fun w : c0 I => ev w i) h
      simp only [ev] at this hc
      have e1 : ((Hc x + v : c0 I) : Linf I) i = Hfun x i + ev v i := rfl
      have e2 : ((Hc x' + v' : c0 I) : Linf I) i = Hfun x' i + ev v' i := rfl
      rw [e1, e2] at this
      have := hc.1; have := hc.2
      simp only [ev] at *
      linarith
    have := Hinj x x' hS
    subst this
    have : v = v' := add_left_cancel h
    subst this; rfl
  have himg : Qset n = Phi '' s := by
    ext t
    constructor
    · rintro ⟨x, ⟨hx1, hx2⟩, hn⟩
      refine ⟨(x, t - Hc x), ⟨⟨hx1, hn⟩, ?_⟩, by simp [Phi]⟩
      refine hx2.subset (fun i hi => ?_)
      simp only [Set.mem_ofPred_eq] at hi ⊢
      intro h; apply hi
      have : ev (t - Hc x) i = ev t i - Hfun x i := rfl
      rw [this, h]; ring
    · rintro ⟨⟨x, v⟩, ⟨⟨hx1, hn⟩, hv⟩, rfl⟩
      refine ⟨x, ⟨hx1, hv.subset (fun i hi => ?_)⟩, hn⟩
      simp only [Set.mem_ofPred_eq] at hi ⊢
      intro h; apply hi
      have : ev (Phi (x, v)) i = Hfun x i + ev v i := rfl
      rw [this, h]; ring
  rw [himg]
  exact hs.image_of_continuousOn_injOn hc hi

/-! ### Stage data -/

def Adm (E : ℕ → Set L1) (lab : L1 → T) : Prop :=
  (∀ n, IsClosed (E n)) ∧
  (∀ n, ∀ e ∈ E n, ‖e‖ = 1 ∧ ∀ j, 0 ≤ e j ∧ (j.1 ≠ n → e j = 0)) ∧
  (∀ n, ∀ e ∈ E n, ∀ e' ∈ E n, ‖e - e'‖ < 2 → dist (lab e) (lab e') ≤ ‖e - e'‖ / 4)

def GSpec (G : (ℕ → Set L1) → (L1 → T) → B → T) : Prop :=
  ∀ (E : ℕ → Set L1) (lab : L1 → T), Adm E lab →
    LipschitzWith 1 (G E lab) ∧
    (∀ n (x : B), (x : L1) ∈ E n → G E lab x = lab x) ∧
    (∀ (E' : ℕ → Set L1) (lab' : L1 → T) (x : B),
       (∀ n, ‖(x : L1)‖ / 4 < mass n (x : L1) → E' n = E n ∧ ∀ e ∈ E n, lab' e = lab e) →
       G E' lab' x = G E lab x) ∧
    (∀ x : B, (∀ n, mass n (x : L1) ≤ ‖(x : L1)‖ / 4) → ∀ i, ev ((G E lab x : T) : c0 I) i = Hfun x i) ∧
    (∀ x : B, (∀ n, (x : L1) ∉ E n) → Sim (ev ((G E lab x : T) : c0 I)) (Hfun x))

theorem exists_GSpec : ∃ G, GSpec G := by
  obtain ⟨G, hG⟩ := Ell1C0.exists_tree_clamp_family
  refine ⟨G, fun E lab h => ?_⟩
  obtain ⟨a, b, c, d, e⟩ := hG E lab h.1 h.2.1 h.2.2
  exact ⟨a, b, c, d, e⟩

def Aset (E : ℕ → Set L1) (n : ℕ) : Set L1 := {x | ‖x‖ ≤ 1 ∧ rk x = n ∧ ∀ m, x ∉ E m}

def gfun (G : (ℕ → Set L1) → (L1 → T) → B → T) (E : ℕ → Set L1) (lab : L1 → T) (x : L1) : c0 I :=
  if h : ‖x‖ ≤ 1 then ((G E lab ⟨x, mem_closedBall_zero_iff.2 h⟩ : T) : c0 I) else 0

def Mset (G : (ℕ → Set L1) → (L1 → T) → B → T) (E : ℕ → Set L1) (lab : L1 → T) (n : ℕ) : Set (c0 I) :=
  {t | ‖t‖ ≤ 1 ∧ rho t = n} \ (gfun G E lab '' Aset E n)

theorem rho_set_eq (n : ℕ) : {t : c0 I | rho t = n} = Qset n ∪ {t | n = 0 ∧ t ∉ ⋃ k, Qset k} := by
  ext t
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion, not_exists]
  by_cases h : ∃ x, Own t x
  · obtain ⟨x, hx⟩ := h
    rw [rho_eq hx]
    constructor
    · intro hn; exact Or.inl ⟨x, hx, hn⟩
    · rintro (⟨x', hx', hn⟩ | ⟨_, hk⟩)
      · rw [Own_unique hx hx']; exact hn
      · exact absurd (show t ∈ Qset (rk x) from ⟨x, hx, rfl⟩) (hk (rk x))
  · rw [rho_none h]
    constructor
    · intro hn; right; exact ⟨hn.symm, fun k ⟨x, hx, _⟩ => h ⟨x, hx⟩⟩
    · rintro (⟨x, hx, _⟩ | ⟨h0, _⟩)
      · exact absurd ⟨x, hx⟩ h
      · exact h0.symm

theorem measurableSet_rho (n : ℕ) : MeasurableSet {t : c0 I | rho t = n} := by
  rw [rho_set_eq]
  refine (measurableSet_Qset n).union ?_
  by_cases h : n = 0
  · have : {t : c0 I | n = 0 ∧ t ∉ ⋃ k, Qset k} = (⋃ k, Qset k)ᶜ := by ext t; simp [h]
    rw [this]; exact (MeasurableSet.iUnion measurableSet_Qset).compl
  · have : {t : c0 I | n = 0 ∧ t ∉ ⋃ k, Qset k} = ∅ := by ext t; simp [h]
    rw [this]; exact MeasurableSet.empty

theorem measurableSet_Aset {E : ℕ → Set L1} (hE : ∀ n, IsClosed (E n)) (n : ℕ) :
    MeasurableSet (Aset E n) := by
  have : Aset E n = {x : L1 | ‖x‖ ≤ 1} ∩ {x | rk x = n} ∩ ⋂ m, (E m)ᶜ := by
    ext x; simp [Aset, and_assoc]
  rw [this]
  exact ((measurableSet_le continuous_norm.measurable measurable_const).inter (measurableSet_rk n)).inter
    (MeasurableSet.iInter fun m => (hE m).measurableSet.compl)

theorem measurableSet_Rset {G : (ℕ → Set L1) → (L1 → T) → B → T} (hG : GSpec G)
    {E : ℕ → Set L1} {lab : L1 → T} (hA : Adm E lab) (n : ℕ) :
    MeasurableSet (gfun G E lab '' Aset E n) := by
  obtain ⟨hL, -, -, -, hF⟩ := hG E lab hA
  refine (measurableSet_Aset hA.1 n).image_of_continuousOn_injOn ?_ ?_
  · rw [continuousOn_iff_continuous_restrict]
    let g : Aset E n → B := fun x => ⟨x.1, mem_closedBall_zero_iff.2 x.2.1⟩
    have hg : Continuous g := Continuous.subtype_mk continuous_subtype_val _
    have : (Aset E n).domRestrict (gfun G E lab) = fun x => ((G E lab (g x) : T) : c0 I) := by
      funext x
      simp [gfun, g, Set.domRestrict, x.2.1]
    rw [this]
    exact continuous_subtype_val.comp (hL.continuous.comp hg)
  · intro x hx x' hx' h
    have e1 : Sim (ev (gfun G E lab x)) (Hfun x) := by
      have := hF ⟨x, mem_closedBall_zero_iff.2 hx.1⟩ hx.2.2
      simpa [gfun, hx.1] using this
    have e2 : Sim (ev (gfun G E lab x')) (Hfun x') := by
      have := hF ⟨x', mem_closedBall_zero_iff.2 hx'.1⟩ hx'.2.2
      simpa [gfun, hx'.1] using this
    rw [h] at e1
    exact Hinj x x' (e1.symm.trans e2)

theorem measurableSet_Mset {G : (ℕ → Set L1) → (L1 → T) → B → T} (hG : GSpec G)
    {E : ℕ → Set L1} {lab : L1 → T} (hA : Adm E lab) (n : ℕ) :
    MeasurableSet (Mset G E lab n) := by
  refine MeasurableSet.diff ?_ (measurableSet_Rset hG hA n)
  have : {t : c0 I | ‖t‖ ≤ 1 ∧ rho t = n} = Metric.closedBall 0 1 ∩ {t | rho t = n} := by
    ext t; simp
  rw [this]
  exact Metric.isClosed_closedBall.measurableSet.inter (measurableSet_rho n)

/-! ### Transport into block n and the step lemma -/

abbrev L1N := lp (fun _ : ℕ => ℝ) 1

theorem norm_L1N (x : L1N) : ‖x‖ = ∑' j, |x j| := by
  have h0 : (0:ℝ) < (1 : ENNReal).toReal := by simp
  rw [lp.norm_eq_tsum_rpow h0]
  simp

theorem summable_L1N (x : L1N) : Summable (fun j => |x j|) := by
  have := (lp.memℓp x : Memℓp (x : ∀ _ : ℕ, ℝ) 1)
  rw [memℓp_gen_iff (by norm_num)] at this
  simpa using this

def blockFun (n : ℕ) (y : L1N) (j : J) : ℝ := if j.1 = n then y j.2 else 0

theorem blockFun_inj (n : ℕ) : Function.Injective (fun k : ℕ => ((n, k) : J)) :=
  fun a b h => by simpa using h

theorem blockFun_zero (n : ℕ) (y : L1N) : ∀ j ∉ Set.range (fun k : ℕ => ((n, k) : J)), blockFun n y j = 0 := by
  rintro ⟨a, b⟩ h
  simp only [blockFun]
  rw [if_neg]
  rintro rfl
  exact h ⟨b, rfl⟩

theorem summable_block (n : ℕ) (y : L1N) : Summable (fun j => |blockFun n y j|) := by
  rw [← (blockFun_inj n).summable_iff (f := fun j => |blockFun n y j|)
    (fun j hj => by simp [blockFun_zero n y j hj])]
  refine (summable_L1N y).congr (fun k => ?_)
  simp [blockFun]

def iota (n : ℕ) (y : L1N) : L1 :=
  ⟨blockFun n y, by
    show Memℓp (blockFun n y) 1
    rw [memℓp_gen_iff (by norm_num)]
    simpa using summable_block n y⟩

theorem iota_apply (n : ℕ) (y : L1N) (j : J) : iota n y j = if j.1 = n then y j.2 else 0 := rfl

theorem iota_norm (n : ℕ) (y : L1N) : ‖iota n y‖ = ‖y‖ := by
  rw [norm_L1, norm_L1N]
  rw [← (blockFun_inj n).tsum_eq (f := fun j => |iota n y j|)]
  · congr 1; ext k; simp [iota_apply]
  · intro j hj
    by_contra hc
    apply hj
    show |blockFun n y j| = 0
    rw [blockFun_zero n y j hc]; simp

theorem iota_sub (n : ℕ) (y y' : L1N) : iota n (y - y') = iota n y - iota n y' := by
  ext j; simp only [iota_apply, lp.coeFn_sub, Pi.sub_apply]; split_ifs <;> simp

theorem iota_isometry (n : ℕ) : Isometry (iota n) := by
  refine Isometry.of_dist_eq (fun y y' => ?_)
  rw [dist_eq_norm, dist_eq_norm, ← iota_sub, iota_norm]

def toT (s : c0 I) : T := if h : ‖s‖ ≤ 1 then ⟨s, mem_closedBall_zero_iff.2 h⟩ else ⟨0, by simp⟩

theorem toT_val {s : c0 I} (h : ‖s‖ ≤ 1) : (toT s : c0 I) = s := by
  unfold toT; rw [dif_pos h]

theorem transport (n : ℕ) (M : Set (c0 I)) (hM : M ⊆ Metric.closedBall 0 1)
    (E0 : Set L1N) (hE0 : IsClosed E0) (hE0' : ∀ e ∈ E0, ‖e‖ = 1 ∧ ∀ j, 0 ≤ e j)
    (lab0 : L1N → c0 I) (hb : Set.BijOn lab0 E0 M)
    (hq : ∀ e ∈ E0, ∀ e' ∈ E0, ‖e - e'‖ < 2 → dist (lab0 e) (lab0 e') ≤ ‖e - e'‖ / 4) :
    ∃ En : Set L1, ∃ labn : L1 → T, IsClosed En ∧
      (∀ e ∈ En, ‖e‖ = 1 ∧ ∀ j, 0 ≤ e j ∧ (j.1 ≠ n → e j = 0)) ∧
      (∀ e ∈ En, ∀ e' ∈ En, ‖e - e'‖ < 2 → dist (labn e) (labn e') ≤ ‖e - e'‖ / 4) ∧
      Set.BijOn (fun e => (labn e : c0 I)) En M := by
  have hiso := iota_isometry n
  have hinj := hiso.injective
  let labn : L1 → T := fun x => toT (lab0 (Function.invFun (iota n) x))
  have hlab : ∀ y ∈ E0, (labn (iota n y) : c0 I) = lab0 y := by
    intro y hy
    simp only [labn, Function.leftInverse_invFun hinj y]
    exact toT_val (mem_closedBall_zero_iff.1 (hM (hb.mapsTo hy)))
  refine ⟨iota n '' E0, labn, hiso.isClosedEmbedding.isClosedMap E0 hE0, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨by rw [iota_norm]; exact (hE0' y hy).1, fun j => ⟨?_, fun hj => ?_⟩⟩
    · rw [iota_apply]; split_ifs
      · exact (hE0' y hy).2 _
      · exact le_rfl
    · rw [iota_apply, if_neg hj]
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ h
    rw [← iota_sub, iota_norm] at h ⊢
    rw [Subtype.dist_eq, hlab y hy, hlab y' hy']
    exact hq y hy y' hy' h
  · refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      show (labn (iota n y) : c0 I) ∈ M
      rw [hlab y hy]; exact hb.mapsTo hy
    · rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ h
      simp only [hlab y hy, hlab y' hy'] at h
      rw [hb.injOn hy hy' h]
    · intro t ht
      obtain ⟨y, hy, rfl⟩ := hb.surjOn ht
      exact ⟨iota n y, ⟨y, hy, rfl⟩, hlab y hy⟩

theorem step {G : (ℕ → Set L1) → (L1 → T) → B → T} (hG : GSpec G)
    {E : ℕ → Set L1} {lab : L1 → T} (hA : Adm E lab) (n : ℕ) :
    ∃ En : Set L1, ∃ labn : L1 → T, IsClosed En ∧
      (∀ e ∈ En, ‖e‖ = 1 ∧ ∀ j, 0 ≤ e j ∧ (j.1 ≠ n → e j = 0)) ∧
      (∀ e ∈ En, ∀ e' ∈ En, ‖e - e'‖ < 2 → dist (labn e) (labn e') ≤ ‖e - e'‖ / 4) ∧
      Set.BijOn (fun e => (labn e : c0 I)) En (Mset G E lab n) := by
  have hM := measurableSet_Mset hG hA n
  have hsub : Mset G E lab n ⊆ Metric.closedBall 0 1 := fun t ht =>
    mem_closedBall_zero_iff.2 ht.1.1
  haveI : Nonempty (c0 I) := ⟨0⟩
  obtain ⟨C, hC, φ, hφ, hbij⟩ := Polish.exists_isClosed_continuousOn_bijOn (Mset G E lab n) hM
  obtain ⟨E0, hE0, hE0', lab0, hb, hq⟩ := Ell1.exists_closed_code_set (Mset G E lab n) C hC φ hφ hbij
  exact transport n _ hsub E0 hE0 (fun e he => ⟨(hE0' e he).1, (hE0' e he).2⟩) lab0 hb hq

/-! ### The recursion -/

def zeroT : T := ⟨0, by simp⟩

def comb (E : ℕ → Set L1) (Lb : ℕ → L1 → T) (x : L1) : T :=
  open Classical in
  if h : ∃ m, x ∈ E m then Lb h.choose x else zeroT

def Blk (E : ℕ → Set L1) : Prop :=
  ∀ m, ∀ e ∈ E m, ‖e‖ = 1 ∧ ∀ j, 0 ≤ e j ∧ (j.1 ≠ m → e j = 0)

theorem Blk.disj {E : ℕ → Set L1} (h : Blk E) {m m' : ℕ} {x : L1} (hm : x ∈ E m) (hm' : x ∈ E m') :
    m = m' := by
  by_contra hne
  have h1 := h m x hm
  have h2 := h m' x hm'
  have : x = 0 := by
    ext j
    simp only [lp.coeFn_zero, Pi.zero_apply]
    by_cases hj : j.1 = m
    · exact (h2.2 j).2 (by rw [hj]; exact hne)
    · exact (h1.2 j).2 hj
  rw [this] at h1; simp at h1

theorem comb_eq {E : ℕ → Set L1} {Lb : ℕ → L1 → T} (h : Blk E) {m : ℕ} {x : L1} (hx : x ∈ E m) :
    comb E Lb x = Lb m x := by
  have hex : ∃ m, x ∈ E m := ⟨m, hx⟩
  unfold comb
  rw [dif_pos hex, h.disj hex.choose_spec hx]

def Goodp (G : (ℕ → Set L1) → (L1 → T) → B → T) (n : ℕ) (E : ℕ → Set L1) (lab : L1 → T)
    (p : Set L1 × (L1 → T)) : Prop :=
  IsClosed p.1 ∧ (∀ e ∈ p.1, ‖e‖ = 1 ∧ ∀ j, 0 ≤ e j ∧ (j.1 ≠ n → e j = 0)) ∧
  (∀ e ∈ p.1, ∀ e' ∈ p.1, ‖e - e'‖ < 2 → dist (p.2 e) (p.2 e') ≤ ‖e - e'‖ / 4) ∧
  Set.BijOn (fun e => (p.2 e : c0 I)) p.1 (Mset G E lab n)

def dflt : Set L1 × (L1 → T) := (∅, fun _ => zeroT)

def stepf (G : (ℕ → Set L1) → (L1 → T) → B → T) (n : ℕ) (h : ℕ → Set L1 × (L1 → T)) :
    Set L1 × (L1 → T) :=
  open Classical in
  if hex : ∃ p, Goodp G n (fun m => (h m).1) (comb (fun m => (h m).1) (fun m => (h m).2)) p
  then hex.choose else dflt

def P (G : (ℕ → Set L1) → (L1 → T) → B → T) (n : ℕ) : Set L1 × (L1 → T) :=
  stepf G n (fun m => if hm : m < n then P G m else dflt)
termination_by n
decreasing_by exact hm

def hist (G : (ℕ → Set L1) → (L1 → T) → B → T) (n : ℕ) : ℕ → Set L1 × (L1 → T) :=
  fun m => if hm : m < n then P G m else dflt

def E' (G : (ℕ → Set L1) → (L1 → T) → B → T) (n : ℕ) : ℕ → Set L1 := fun m => (hist G n m).1

def lab' (G : (ℕ → Set L1) → (L1 → T) → B → T) (n : ℕ) : L1 → T :=
  comb (E' G n) (fun m => (hist G n m).2)

theorem P_eq (G : (ℕ → Set L1) → (L1 → T) → B → T) (n : ℕ) : P G n = stepf G n (hist G n) := by
  rw [P]; rfl

theorem hist_lt {G : (ℕ → Set L1) → (L1 → T) → B → T} {n m : ℕ} (hm : m < n) : hist G n m = P G m := by
  simp [hist, hm]

theorem hist_ge {G : (ℕ → Set L1) → (L1 → T) → B → T} {n m : ℕ} (hm : ¬ m < n) : hist G n m = dflt := by
  simp [hist, hm]

theorem good {G : (ℕ → Set L1) → (L1 → T) → B → T} (hG : GSpec G) :
    ∀ n, Goodp G n (E' G n) (lab' G n) (P G n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hblk : Blk (E' G n) := by
      intro m e he
      by_cases hm : m < n
      · have he' : e ∈ (P G m).1 := by
          have : E' G n m = (P G m).1 := by simp [E', hist_lt hm]
          rwa [this] at he
        exact (ih m hm).2.1 e he'
      · have : E' G n m = ∅ := by simp [E', hist_ge hm, dflt]
        rw [this] at he; exact absurd he (Set.notMem_empty _)
    have hadm : Adm (E' G n) (lab' G n) := by
      refine ⟨fun m => ?_, hblk, fun m e he e' he' hlt => ?_⟩
      · by_cases hm : m < n
        · have : E' G n m = (P G m).1 := by simp [E', hist_lt hm]
          rw [this]; exact (ih m hm).1
        · have : E' G n m = ∅ := by simp [E', hist_ge hm, dflt]
          rw [this]; exact isClosed_empty
      · have hm : m < n := by
          by_contra hm
          have : E' G n m = ∅ := by simp [E', hist_ge hm, dflt]
          rw [this] at he; exact Set.notMem_empty _ he
        have hP : ∀ e ∈ E' G n m, e ∈ (P G m).1 ∧ lab' G n e = (P G m).2 e := by
          intro e he
          have h1 : E' G n m = (P G m).1 := by simp [E', hist_lt hm]
          refine ⟨by rwa [h1] at he, ?_⟩
          unfold lab'
          rw [comb_eq hblk he]
          simp [hist_lt hm]
        rw [(hP e he).2, (hP e' he').2]
        exact (ih m hm).2.2.1 e (hP e he).1 e' (hP e' he').1 hlt
    obtain ⟨En, labn, h1, h2, h3, h4⟩ := step hG hadm n
    have hex : ∃ p, Goodp G n (E' G n) (lab' G n) p := ⟨(En, labn), h1, h2, h3, h4⟩
    rw [P_eq]
    unfold stepf
    split
    · next hx => exact hx.choose_spec
    · next hx => exact absurd hex hx

/-! ### The global map -/

abbrev Ed (G : (ℕ → Set L1) → (L1 → T) → B → T) (n : ℕ) : Set L1 := (P G n).1
abbrev Lb (G : (ℕ → Set L1) → (L1 → T) → B → T) (n : ℕ) : L1 → T := (P G n).2

theorem E'_mem {G : (ℕ → Set L1) → (L1 → T) → B → T} {n m : ℕ} (hm : m < n) : E' G n m = Ed G m := by
  simp [E', hist_lt hm]

theorem E'_nmem {G : (ℕ → Set L1) → (L1 → T) → B → T} {n m : ℕ} (hm : ¬ m < n) : E' G n m = ∅ := by
  simp [E', hist_ge hm, dflt]

theorem E'_sub {G : (ℕ → Set L1) → (L1 → T) → B → T} {n m : ℕ} {e : L1} (h : e ∈ E' G n m) :
    m < n ∧ e ∈ Ed G m := by
  by_cases hm : m < n
  · exact ⟨hm, by rwa [E'_mem hm] at h⟩
  · rw [E'_nmem hm] at h; exact absurd h (Set.notMem_empty _)

theorem blk_Ed {G : (ℕ → Set L1) → (L1 → T) → B → T} (hG : GSpec G) : Blk (Ed G) :=
  fun m => (good hG m).2.1

theorem blk_E' {G : (ℕ → Set L1) → (L1 → T) → B → T} (hG : GSpec G) (n : ℕ) : Blk (E' G n) := by
  intro m e he
  obtain ⟨hm, he'⟩ := E'_sub he
  exact blk_Ed hG m e he'

theorem lab'_eq {G : (ℕ → Set L1) → (L1 → T) → B → T} (hG : GSpec G) {m n : ℕ} (hm : m < n)
    {e : L1} (he : e ∈ Ed G m) : lab' G n e = Lb G m e := by
  unfold lab'
  rw [comb_eq (blk_E' hG n) (show e ∈ E' G n m by rw [E'_mem hm]; exact he)]
  simp [hist_lt hm]

theorem adm_E' {G : (ℕ → Set L1) → (L1 → T) → B → T} (hG : GSpec G) (n : ℕ) :
    Adm (E' G n) (lab' G n) := by
  refine ⟨fun m => ?_, blk_E' hG n, fun m e he e' he' hlt => ?_⟩
  · by_cases hm : m < n
    · rw [E'_mem hm]; exact (good hG m).1
    · rw [E'_nmem hm]; exact isClosed_empty
  · obtain ⟨hm, he1⟩ := E'_sub he
    obtain ⟨-, he2⟩ := E'_sub he'
    rw [lab'_eq hG hm he1, lab'_eq hG hm he2]
    exact (good hG m).2.2.1 e he1 e' he2 hlt

def labI (G : (ℕ → Set L1) → (L1 → T) → B → T) : L1 → T := comb (Ed G) (Lb G)

theorem labI_eq {G : (ℕ → Set L1) → (L1 → T) → B → T} (hG : GSpec G) {m : ℕ} {e : L1}
    (he : e ∈ Ed G m) : labI G e = Lb G m e := comb_eq (blk_Ed hG) he

theorem adm_Ed {G : (ℕ → Set L1) → (L1 → T) → B → T} (hG : GSpec G) : Adm (Ed G) (labI G) := by
  refine ⟨fun m => (good hG m).1, blk_Ed hG, fun m e he e' he' hlt => ?_⟩
  rw [labI_eq hG he, labI_eq hG he']
  exact (good hG m).2.2.1 e he e' he' hlt

theorem gfun_injOn {G : (ℕ → Set L1) → (L1 → T) → B → T} (hG : GSpec G)
    {E : ℕ → Set L1} {lab : L1 → T} (hA : Adm E lab) (n : ℕ) :
    Set.InjOn (gfun G E lab) (Aset E n) := by
  obtain ⟨-, -, -, -, hF⟩ := hG E lab hA
  intro x hx x' hx' h
  have e1 : Sim (ev (gfun G E lab x)) (Hfun x) := by
    have := hF ⟨x, mem_closedBall_zero_iff.2 hx.1⟩ hx.2.2
    simpa [gfun, hx.1] using this
  have e2 : Sim (ev (gfun G E lab x')) (Hfun x') := by
    have := hF ⟨x', mem_closedBall_zero_iff.2 hx'.1⟩ hx'.2.2
    simpa [gfun, hx'.1] using this
  rw [h] at e1
  exact Hinj x x' (e1.symm.trans e2)

theorem core {G : (ℕ → Set L1) → (L1 → T) → B → T} (hG : GSpec G) :
    ∃ F : B → T, LipschitzWith 1 F ∧ Function.Bijective F ∧
      F ⟨0, Metric.mem_closedBall_self zero_le_one⟩ = ⟨0, Metric.mem_closedBall_self zero_le_one⟩ ∧
      ∃ u : ℕ → B, ∀ m, ‖(u m : L1)‖ = 1 ∧ ‖((F (u m) : T) : c0 I)‖ = 1 / ((m : ℝ) + 2) := by
  have hgood := good hG
  have hAdm := adm_Ed hG
  obtain ⟨hL, hc2, -, hc4, -⟩ := hG _ _ hAdm
  have hc3 := (hG _ _ hAdm).2.2.1
  let F := G (Ed G) (labI G)
  have h1 : ∀ m (x : B), (x : L1) ∈ Ed G m → (F x : c0 I) = (Lb G m x : c0 I) ∧
      (F x : c0 I) ∈ Mset G (E' G m) (lab' G m) m := by
    intro m x hx
    have e : F x = Lb G m x := by
      show G (Ed G) (labI G) x = _
      rw [hc2 m x hx, labI_eq hG hx]
    rw [e]
    exact ⟨rfl, (good hG m).2.2.2.mapsTo hx⟩
  have h2 : ∀ n (x : B), (x : L1) ∈ Aset (E' G n) n →
      (F x : c0 I) = gfun G (E' G n) (lab' G n) x ∧ rho (F x : c0 I) = n := by
    intro n x hx
    have e : G (E' G n) (lab' G n) x = F x := by
      refine hc3 (E' G n) (lab' G n) x (fun m hm => ?_)
      have hmn : m < n := by
        have := lt_rk (show m ∈ Dset (x : L1) from hm)
        rw [hx.2.1] at this; exact this
      refine ⟨E'_mem hmn, fun e he => ?_⟩
      rw [lab'_eq hG hmn he, labI_eq hG he]
    have e2 : (F x : c0 I) = gfun G (E' G n) (lab' G n) x := by
      rw [← e]; simp [gfun, x.2, mem_closedBall_zero_iff.1 x.2]
    refine ⟨e2, ?_⟩
    have hF5 := ((hG _ _ (adm_E' hG n)).2.2.2.2) x hx.2.2
    have hown : Own (F x : c0 I) x := by
      refine ⟨hx.1, ?_⟩
      rw [← e]; exact hF5
    rw [rho_eq hown, hx.2.1]
  have hmem : ∀ x : B, (∀ m, (x : L1) ∉ Ed G m) → (x : L1) ∈ Aset (E' G (rk (x : L1))) (rk (x : L1)) :=
    fun x hx => ⟨mem_closedBall_zero_iff.1 x.2, rfl, fun m hm => hx m (E'_sub hm).2⟩
  have hinj : Function.Injective F := by
    intro x x' hxx
    have hv : (F x : c0 I) = (F x' : c0 I) := congrArg Subtype.val hxx
    by_cases hx : ∃ m, (x : L1) ∈ Ed G m <;> by_cases hx' : ∃ m, (x' : L1) ∈ Ed G m
    · obtain ⟨m, hm⟩ := hx
      obtain ⟨m', hm'⟩ := hx'
      obtain ⟨e1, c1⟩ := h1 m x hm
      obtain ⟨e2, c2⟩ := h1 m' x' hm'
      have hr : m = m' := by rw [← c1.1.2, hv, c2.1.2]
      subst hr
      apply Subtype.ext
      exact (good hG m).2.2.2.injOn hm hm' (by rw [← e1, ← e2, hv])
    · push Not at hx'
      obtain ⟨m, hm⟩ := hx
      obtain ⟨e1, c1⟩ := h1 m x hm
      have hA' := hmem x' hx'
      obtain ⟨e2, r2⟩ := h2 _ x' hA'
      have : rk (x' : L1) = m := by rw [← r2, ← hv, ← c1.1.2]
      rw [this] at hA' e2
      exact absurd ⟨x', hA', e2.symm.trans (hv.symm.trans rfl)⟩ c1.2
    · push Not at hx
      obtain ⟨m, hm⟩ := hx'
      obtain ⟨e1, c1⟩ := h1 m x' hm
      have hA' := hmem x hx
      obtain ⟨e2, r2⟩ := h2 _ x hA'
      have : rk (x : L1) = m := by rw [← r2, hv, ← c1.1.2]
      rw [this] at hA' e2
      exact absurd ⟨x, hA', e2.symm.trans hv⟩ c1.2
    · push Not at hx hx'
      have hA1 := hmem x hx
      have hA2 := hmem x' hx'
      obtain ⟨e1, r1⟩ := h2 _ x hA1
      obtain ⟨e2, r2⟩ := h2 _ x' hA2
      have hr : rk (x : L1) = rk (x' : L1) := by rw [← r1, hv, r2]
      rw [hr] at hA1 e1
      apply Subtype.ext
      exact gfun_injOn hG (adm_E' hG _) _ hA1 hA2 (by rw [← e1, ← e2, hv])
  have hsurj : Function.Surjective F := by
    intro t
    obtain ⟨n, hn⟩ : ∃ n, n = rho (t : c0 I) := ⟨_, rfl⟩
    by_cases hR : (t : c0 I) ∈ gfun G (E' G n) (lab' G n) '' Aset (E' G n) n
    · obtain ⟨x, hx, hxt⟩ := hR
      refine ⟨⟨x, mem_closedBall_zero_iff.2 hx.1⟩, Subtype.ext ?_⟩
      rw [(h2 n ⟨x, mem_closedBall_zero_iff.2 hx.1⟩ hx).1]; exact hxt
    · have hM : (t : c0 I) ∈ Mset G (E' G n) (lab' G n) n :=
        ⟨⟨mem_closedBall_zero_iff.1 t.2, hn.symm⟩, hR⟩
      obtain ⟨e, he, het⟩ := (good hG n).2.2.2.surjOn hM
      refine ⟨⟨e, mem_closedBall_zero_iff.2 (le_of_eq ((good hG n).2.1 e he).1)⟩, Subtype.ext ?_⟩
      rw [(h1 n _ he).1]; exact het
  have hF0 : F ⟨0, Metric.mem_closedBall_self zero_le_one⟩ = ⟨0, Metric.mem_closedBall_self zero_le_one⟩ := by
    apply Subtype.ext; apply Subtype.ext; apply lp.ext; funext i
    have := hc4 ⟨0, Metric.mem_closedBall_self zero_le_one⟩ (fun n => by simp [mass]) i
    simpa [ev, Hfun] using this
  refine ⟨F, hL, ⟨hinj, hsurj⟩, hF0, ?_⟩
  -- the points u m
  let i0 : I := ((0, 0), 0)
  let i1 : I := ((0, 0), 1)
  have hpos : ∀ m : ℕ, (0 : ℝ) < 1 / ((m : ℝ) + 2) := fun m => by positivity
  let tm : ℕ → c0 I := fun m => ⟨lp.single ⊤ i0 (1 / ((m : ℝ) + 2)), single_mem_c0 _ _⟩
  have tm_norm : ∀ m, ‖tm m‖ = 1 / ((m : ℝ) + 2) := by
    intro m
    show ‖(lp.single ⊤ i0 (1 / ((m : ℝ) + 2)) : Linf I)‖ = _
    rw [lp.norm_single (by simp), Real.norm_eq_abs, abs_of_pos (hpos m)]
  have tm_i0 : ∀ m, ev (tm m) i0 = 1 / ((m : ℝ) + 2) := fun m => by simp [ev, tm, lp.single_apply]
  have tm_ne : ∀ m i, i ≠ i0 → ev (tm m) i = 0 := fun m i hi => by
    simp [ev, tm, lp.single_apply, hi]
  have hmemM : ∀ m, tm m ∈ Mset G (E' G 0) (lab' G 0) 0 := by
    intro m
    have hle : ‖tm m‖ ≤ 1 := by
      rw [tm_norm]
      have : (2 : ℝ) ≤ (m : ℝ) + 2 := by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
      rw [div_le_one (by linarith)]; linarith
    refine ⟨⟨hle, ?_⟩, ?_⟩
    · have hown : Own (tm m) 0 := by
        refine ⟨by simp, (Set.finite_singleton i0).subset ?_⟩
        intro i hi
        by_contra hne
        apply hi
        simp only [Set.mem_singleton_iff] at hne
        have := tm_ne m i hne
        simp [Hfun, this]
      rw [rho_eq hown, rk_zero]
    · rintro ⟨x, hx, hxt⟩
      have hmass : ∀ n, mass n x ≤ ‖x‖ / 4 := by
        intro n
        by_contra hlt
        have := ((rk_eq_iff x 0).1 hx.2.1).1 n (not_le.1 hlt)
        omega
      have hxB : ‖x‖ ≤ 1 := hx.1
      have key := ((hG _ _ (adm_E' hG 0)).2.2.2.1) ⟨x, mem_closedBall_zero_iff.2 hxB⟩ hmass
      have hcoord : ∀ i, ev (tm m) i = Hfun x i := by
        intro i
        rw [← hxt]
        simpa [gfun, hxB] using key i
      have a0 := hcoord i0
      have a1 := hcoord i1
      rw [tm_i0] at a0
      rw [tm_ne m i1 (by simp [i0, i1])] at a1
      have e0 : (2:ℝ) ^ (-(((0:ℕ):ℤ) + 2)) = 1 / 4 := by norm_num
      have e1 : (2:ℝ) ^ (-(((1:ℕ):ℤ) + 2)) = 1 / 8 := by norm_num
      simp only [Hfun, i0, i1, e0, e1] at a0 a1
      have := hpos m
      linarith
  have hsur := fun m => (good hG 0).2.2.2.surjOn (hmemM m)
  choose e he het using hsur
  refine ⟨fun m => ⟨e m, mem_closedBall_zero_iff.2 (le_of_eq ((good hG 0).2.1 _ (he m)).1)⟩,
    fun m => ⟨((good hG 0).2.1 _ (he m)).1, ?_⟩⟩
  rw [(h1 0 _ (he m)).1]
  show ‖((Lb G 0 (e m) : T) : c0 I)‖ = _
  rw [show ((Lb G 0 (e m) : T) : c0 I) = tm m from het m]
  exact tm_norm m

def ballFun {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] (f : E ≃ₗᵢ[ℝ] E') (x : Metric.closedBall (0 : E) 1) :
    Metric.closedBall (0 : E') 1 :=
  ⟨f x, by rw [mem_closedBall_zero_iff, f.norm_map]; exact mem_closedBall_zero_iff.1 x.2⟩

theorem ballFun_dist {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (f : E ≃ₗᵢ[ℝ] E') (x x' : Metric.closedBall (0 : E) 1) :
    dist (ballFun f x) (ballFun f x') = dist x x' := by
  simp only [Subtype.dist_eq, ballFun, f.dist_map]

theorem ballFun_bij {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (f : E ≃ₗᵢ[ℝ] E') :
    Function.Bijective (ballFun f) := by
  constructor
  · intro x x' h
    apply Subtype.ext
    exact f.injective (congrArg Subtype.val h)
  · intro y
    refine ⟨ballFun f.symm y, ?_⟩
    apply Subtype.ext
    simp [ballFun]

theorem ballFun_zero {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (f : E ≃ₗᵢ[ℝ] E') :
    ballFun f ⟨0, Metric.mem_closedBall_self zero_le_one⟩ = ⟨0, Metric.mem_closedBall_self zero_le_one⟩ := by
  apply Subtype.ext; simp [ballFun]

theorem ballFun_norm {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (f : E ≃ₗᵢ[ℝ] E') (x : Metric.closedBall (0 : E) 1) :
    ‖(ballFun f x : E')‖ = ‖(x : E)‖ := by
  simp [ballFun]

theorem ballFun_symm_apply {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (f : E ≃ₗᵢ[ℝ] E') (x : Metric.closedBall (0 : E) 1) :
    ballFun f (ballFun f.symm (ballFun f x)) = ballFun f x := by
  apply Subtype.ext; simp [ballFun]

end
end Sol_Plasticity_Ell1C0_exists_bijective_ball_map_of_countable

open Sol_Plasticity_Ell1C0_exists_bijective_ball_map_of_countable in
theorem solution (Γ : Type*) [Countable Γ] [Infinite Γ] :
    ∃ F : Metric.closedBall (0 : lp (fun _ : Γ => ℝ) 1) 1 → Metric.closedBall (0 : Plasticity.c0 Γ) 1,
      LipschitzWith 1 F ∧ Function.Bijective F ∧
      F ⟨0, Metric.mem_closedBall_self zero_le_one⟩ = ⟨0, Metric.mem_closedBall_self zero_le_one⟩ ∧
      ∃ u : ℕ → Metric.closedBall (0 : lp (fun _ : Γ => ℝ) 1) 1,
        ∀ m, ‖(u m : lp (fun _ : Γ => ℝ) 1)‖ = 1 ∧ ‖(F (u m) : Plasticity.c0 Γ)‖ = 1 / ((m : ℝ) + 2) := by
  obtain ⟨F, hL, hB, h0, u, hu⟩ := core (exists_GSpec).choose_spec
  have hΓJ : Nonempty (Γ ≃ J) := nonempty_equiv_of_countable
  have hΓI : Nonempty (Γ ≃ I) := nonempty_equiv_of_countable
  obtain ⟨eJ⟩ := hΓJ
  obtain ⟨eI⟩ := hΓI
  let Λ := relabel eJ 1
  let Ψ := relabelC0 eI
  refine ⟨ballFun Ψ.symm ∘ F ∘ ballFun Λ, ?_, ?_, ?_, fun m => ballFun Λ.symm (u m), fun m => ?_⟩
  · have h1 : LipschitzWith 1 (ballFun Λ) := (LipschitzWith.of_dist_le_mul (fun x y => by
      rw [ballFun_dist]; simp))
    have h2 : LipschitzWith 1 (ballFun Ψ.symm) := (LipschitzWith.of_dist_le_mul (fun x y => by
      rw [ballFun_dist]; simp))
    simpa using h2.comp (hL.comp h1)
  · exact (ballFun_bij Ψ.symm).comp (hB.comp (ballFun_bij Λ))
  · simp only [Function.comp]
    rw [ballFun_zero, h0, ballFun_zero]
  · have e1 : ballFun Λ (ballFun Λ.symm (u m)) = u m := by
      apply Subtype.ext; simp [ballFun]
    simp only [Function.comp]
    rw [e1, ballFun_norm, ballFun_norm]
    exact hu m
