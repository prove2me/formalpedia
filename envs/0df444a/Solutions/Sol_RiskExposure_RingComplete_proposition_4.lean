-- Prove2me | solution 1 for RiskExposure.RingComplete.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-19T19:11:36.862677+00:00
-- url     : https://prove2.me/submissions/9a5ce232-3add-4d69-be13-e6a493d2d8e2

import Mathlib
import Definitions.Def_RiskExposure_RingComplete_Model

set_option autoImplicit false

namespace RiskExposure.RingComplete.P4X

open Finset RiskExposure.RingComplete

variable {N : ℕ}

structure Reg (θ : Fin N → Fin N → ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ θ i j
  rowsum : ∀ i, ∑ j, θ i j = 1

def InBox (dbar : ℝ) (d : Fin N → ℝ) : Prop := ∀ i, 0 ≤ d i ∧ d i ≤ dbar

noncomputable def clr (θ : Fin N → Fin N → ℝ) (dbar v : ℝ) (ω : Fin N → Bool)
    (d : Fin N → ℝ) : Fin N → ℝ :=
  fun i => if ω i then dbar else max (∑ j, θ i j * d j - v) 0

lemma sum_le_dbar {θ : Fin N → Fin N → ℝ} (hθ : Reg θ) {dbar : ℝ} {d : Fin N → ℝ}
    (hd : InBox dbar d) (i : Fin N) : ∑ j, θ i j * d j ≤ dbar := by
  calc ∑ j, θ i j * d j ≤ ∑ j, θ i j * dbar :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hd j).2 (hθ.nonneg i j)
    _ = dbar := by rw [← Finset.sum_mul, hθ.rowsum i, one_mul]

lemma sum_nn {θ : Fin N → Fin N → ℝ} (hθ : Reg θ) {dbar : ℝ} {d : Fin N → ℝ}
    (hd : InBox dbar d) (i : Fin N) : 0 ≤ ∑ j, θ i j * d j :=
  Finset.sum_nonneg fun j _ => mul_nonneg (hθ.nonneg i j) (hd j).1

lemma clear_eq_clr {θ : Fin N → Fin N → ℝ} (hθ : Reg θ) {dbar v : ℝ} (hv : 0 < v)
    (ω : Fin N → Bool) {Z : Fin N → ℝ} (hZ : ∀ j, v + dbar ≤ Z j) {d : Fin N → ℝ}
    (hd : InBox dbar d) (i : Fin N) :
    clear θ dbar v ω Z d i = clr θ dbar v ω d i := by
  have h1 := sum_le_dbar hθ hd i
  have h0 := sum_nn hθ hd i
  have hdb : 0 ≤ dbar := le_trans (hd i).1 (hd i).2
  unfold clear clr cash
  by_cases hω : ω i = true
  · simp only [hω, if_true]
    have := hZ i
    rw [min_eq_right (by linarith), max_eq_left hdb]
  · have hf : ω i = false := by simpa using hω
    simp only [hf, Bool.false_eq_true, if_false, add_zero]
    rw [min_eq_left (by linarith)]

lemma clr_box {θ : Fin N → Fin N → ℝ} (hθ : Reg θ) {dbar v : ℝ} (hv : 0 < v) (hdb : 0 ≤ dbar)
    (ω : Fin N → Bool) {d : Fin N → ℝ} (hd : InBox dbar d) : InBox dbar (clr θ dbar v ω d) := by
  intro i
  have h1 := sum_le_dbar hθ hd i
  unfold clr
  split_ifs
  · exact ⟨hdb, le_rfl⟩
  · exact ⟨le_max_right _ _, max_le (by linarith) hdb⟩

lemma clr_mono_d {θ : Fin N → Fin N → ℝ} (hθ : Reg θ) {dbar v : ℝ} (ω : Fin N → Bool)
    {d d' : Fin N → ℝ} (h : d ≤ d') : clr θ dbar v ω d ≤ clr θ dbar v ω d' := by
  intro i
  unfold clr
  split_ifs
  · exact le_rfl
  · apply max_le_max_right
    have : ∑ j, θ i j * d j ≤ ∑ j, θ i j * d' j :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (hθ.nonneg i j)
    linarith

lemma clr_mono_ω {θ : Fin N → Fin N → ℝ} (hθ : Reg θ) {dbar v : ℝ} (hv : 0 < v)
    {ω ω' : Fin N → Bool} (hω : ω ≤ ω') {d : Fin N → ℝ} (hd : InBox dbar d) :
    clr θ dbar v ω d ≤ clr θ dbar v ω' d := by
  intro i
  have h1 := sum_le_dbar hθ hd i
  have hdb : 0 ≤ dbar := le_trans (hd i).1 (hd i).2
  have hi := hω i
  unfold clr
  by_cases a : ω i = true
  · have b : ω' i = true := by
      rw [a] at hi; revert hi; cases ω' i <;> simp
    simp [a, b]
  · by_cases b : ω' i = true
    · simp only [a, b, if_true, if_false]
      exact max_le (by linarith) hdb
    · simp [a, b]

def PostSet (θ : Fin N → Fin N → ℝ) (dbar v : ℝ) (ω : Fin N → Bool) : Set (Fin N → ℝ) :=
  {d | InBox dbar d ∧ d ≤ clr θ dbar v ω d}

noncomputable def gs (θ : Fin N → Fin N → ℝ) (dbar v : ℝ) (ω : Fin N → Bool) : Fin N → ℝ :=
  sSup (PostSet θ dbar v ω)

lemma post_bdd (θ : Fin N → Fin N → ℝ) (dbar v : ℝ) (ω : Fin N → Bool) :
    BddAbove (PostSet θ dbar v ω) :=
  ⟨fun _ => dbar, fun d hd i => (hd.1 i).2⟩

lemma zero_mem_post {θ : Fin N → Fin N → ℝ} (dbar v : ℝ) (hdb : 0 ≤ dbar) (ω : Fin N → Bool) :
    (0 : Fin N → ℝ) ∈ PostSet θ dbar v ω := by
  refine ⟨fun i => ⟨le_rfl, hdb⟩, fun i => ?_⟩
  unfold clr
  split_ifs
  · exact hdb
  · exact le_max_right _ _

lemma le_gs {θ : Fin N → Fin N → ℝ} {dbar v : ℝ} {ω : Fin N → Bool} {d : Fin N → ℝ}
    (hd : d ∈ PostSet θ dbar v ω) : d ≤ gs θ dbar v ω :=
  le_csSup (post_bdd θ dbar v ω) hd

lemma gs_box {θ : Fin N → Fin N → ℝ} {dbar v : ℝ} (hdb : 0 ≤ dbar) (ω : Fin N → Bool) :
    InBox dbar (gs θ dbar v ω) := by
  have h0 := le_gs (zero_mem_post (θ := θ) dbar v hdb ω)
  have h1 : gs θ dbar v ω ≤ fun _ => dbar :=
    csSup_le ⟨0, zero_mem_post dbar v hdb ω⟩ fun d hd i => (hd.1 i).2
  exact fun i => ⟨h0 i, h1 i⟩

lemma gs_fixed {θ : Fin N → Fin N → ℝ} (hθ : Reg θ) {dbar v : ℝ} (hv : 0 < v) (hdb : 0 ≤ dbar)
    (ω : Fin N → Bool) : clr θ dbar v ω (gs θ dbar v ω) = gs θ dbar v ω := by
  have hle : gs θ dbar v ω ≤ clr θ dbar v ω (gs θ dbar v ω) :=
    csSup_le ⟨0, zero_mem_post dbar v hdb ω⟩ fun d hd =>
      le_trans hd.2 (clr_mono_d hθ ω (le_gs hd))
  have hmem : clr θ dbar v ω (gs θ dbar v ω) ∈ PostSet θ dbar v ω :=
    ⟨clr_box hθ hv hdb ω (gs_box hdb ω), clr_mono_d hθ ω hle⟩
  exact le_antisymm (le_gs hmem) hle

lemma gs_apply {θ : Fin N → Fin N → ℝ} (hθ : Reg θ) {dbar v : ℝ} (hv : 0 < v) (hdb : 0 ≤ dbar)
    (ω : Fin N → Bool) (i : Fin N) : gs θ dbar v ω i = clr θ dbar v ω (gs θ dbar v ω) i :=
  (congrFun (gs_fixed hθ hv hdb ω) i).symm

lemma paymentEq_eq {θ : Fin N → Fin N → ℝ} (hθ : Reg θ) {dbar v : ℝ} (hv : 0 < v)
    (hdb : 0 ≤ dbar) (ω : Fin N → Bool) {Z : Fin N → ℝ} (hZ : ∀ j, v + dbar ≤ Z j) :
    paymentEq θ dbar v ω Z = gs θ dbar v ω := by
  unfold paymentEq
  apply IsGreatest.csSup_eq
  refine ⟨⟨gs_box hdb ω, fun i => ?_⟩, fun d hd => ?_⟩
  · rw [clear_eq_clr hθ hv ω hZ (gs_box hdb ω) i]
    exact gs_apply hθ hv hdb ω i
  · apply le_gs
    refine ⟨hd.1, fun i => ?_⟩
    rw [← clear_eq_clr hθ hv ω hZ hd.1 i, ← hd.2 i]

lemma gs_mono {θ : Fin N → Fin N → ℝ} (hθ : Reg θ) {dbar v : ℝ} (hv : 0 < v) (hdb : 0 ≤ dbar)
    {ω ω' : Fin N → Bool} (hω : ω ≤ ω') : gs θ dbar v ω ≤ gs θ dbar v ω' := by
  apply le_gs
  refine ⟨gs_box hdb ω, ?_⟩
  calc gs θ dbar v ω = clr θ dbar v ω (gs θ dbar v ω) := (gs_fixed hθ hv hdb ω).symm
    _ ≤ clr θ dbar v ω' (gs θ dbar v ω) := clr_mono_ω hθ hv hω (gs_box hdb ω)

/-! ## Probability weights -/

def W (p : Fin N → ℝ) (ω : Fin N → Bool) : ℝ := ∏ j, if ω j then p j else 1 - p j

def R (p : Fin N → ℝ) (k : Fin N) (ω : Fin N → Bool) : ℝ :=
  ∏ j ∈ univ.erase k, if ω j then p j else 1 - p j

lemma sum_W (p : Fin N → ℝ) : ∑ ω, W p ω = 1 := by
  unfold W
  rw [← Fintype.prod_sum (fun (j : Fin N) (b : Bool) => if b then p j else 1 - p j)]
  simp

lemma W_split (p : Fin N → ℝ) (k : Fin N) (ω : Fin N → Bool) :
    W p ω = (if ω k then p k else 1 - p k) * R p k ω := by
  unfold W R
  exact (Finset.mul_prod_erase univ (fun j => if ω j then p j else 1 - p j) (mem_univ k)).symm

lemma R_update_ω (p : Fin N → ℝ) (k : Fin N) (ω : Fin N → Bool) (b : Bool) :
    R p k (Function.update ω k b) = R p k ω := by
  unfold R
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma R_update_p (p : Fin N → ℝ) (k : Fin N) (a : ℝ) (ω : Fin N → Bool) :
    R (Function.update p k a) k ω = R p k ω := by
  unfold R
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma R_nonneg {p : Fin N → ℝ} (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1) (k : Fin N) (ω : Fin N → Bool) :
    0 ≤ R p k ω := by
  unfold R
  refine Finset.prod_nonneg fun j _ => ?_
  split_ifs
  · exact (hp j).1
  · linarith [(hp j).2]

lemma W_update_one (p : Fin N → ℝ) (i : Fin N) (ω : Fin N → Bool) :
    W (Function.update p i 1) ω =
      if ω i then ∏ j ∈ univ.erase i, (if ω j then p j else 1 - p j) else 0 := by
  rw [W_split _ i, R_update_p]
  unfold R
  simp only [Function.update_self]
  split_ifs <;> simp

lemma filter_sum_eq (p : Fin N → ℝ) (i : Fin N) (X : (Fin N → Bool) → ℝ) :
    ∑ ω ∈ univ.filter (fun ω : Fin N → Bool => ω i = true),
        X ω * ∏ j ∈ univ.erase i, (if ω j then p j else 1 - p j) =
      ∑ ω, X ω * W (Function.update p i 1) ω := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [W_update_one]
  split_ifs <;> simp

lemma sum_pair (k : Fin N) (f : (Fin N → Bool) → ℝ) :
    ∑ ω, f ω = ∑ ω ∈ univ.filter (fun ω : Fin N → Bool => ω k = true),
      (f ω + f (Function.update ω k false)) := by
  rw [Finset.sum_add_distrib,
    ← Finset.sum_filter_add_sum_filter_not univ (fun ω : Fin N → Bool => ω k = true)]
  congr 1
  apply Finset.sum_nbij' (fun ω => Function.update ω k true) (fun ω => Function.update ω k false)
  · intro a _; simp
  · intro a _; simp
  · intro a ha
    simp only [mem_filter, mem_univ, true_and, Bool.not_eq_true] at ha
    funext j
    by_cases hj : j = k
    · subst hj; simp [ha]
    · simp [Function.update_of_ne hj]
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    funext j
    by_cases hj : j = k
    · subst hj; simp [ha]
    · simp [Function.update_of_ne hj]
  · intro a ha
    simp only [mem_filter, mem_univ, true_and, Bool.not_eq_true] at ha
    congr 1
    funext j
    by_cases hj : j = k
    · subst hj; simp [ha]
    · simp [Function.update_of_ne hj]

lemma F_step {g : (Fin N → Bool) → ℝ} (hg : ∀ ω ω', ω ≤ ω' → g ω' ≤ g ω)
    {p : Fin N → ℝ} (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1) (k : Fin N) {a : ℝ} (ha : p k ≤ a) :
    ∑ ω, g ω * W (Function.update p k a) ω ≤ ∑ ω, g ω * W p ω := by
  rw [sum_pair k (fun ω => g ω * W (Function.update p k a) ω),
    sum_pair k (fun ω => g ω * W p ω)]
  refine Finset.sum_le_sum fun ω hω => ?_
  simp only [mem_filter, mem_univ, true_and] at hω
  set ω0 := Function.update ω k false
  have hle : ω0 ≤ ω := by
    intro j
    by_cases hj : j = k
    · subst hj; simp [ω0]
    · simp [ω0, Function.update_of_ne hj]
  have hgg := hg ω0 ω hle
  have hR := R_nonneg hp k ω
  have e1 : W (Function.update p k a) ω = a * R p k ω := by
    rw [W_split _ k, R_update_p]; simp [hω]
  have e2 : W (Function.update p k a) ω0 = (1 - a) * R p k ω := by
    rw [W_split _ k, R_update_p, R_update_ω]; simp [ω0]
  have e3 : W p ω = p k * R p k ω := by
    rw [W_split _ k]; simp [hω]
  have e4 : W p ω0 = (1 - p k) * R p k ω := by
    rw [W_split _ k, R_update_ω]; simp [ω0]
  rw [e1, e2, e3, e4]
  have key : (a - p k) * R p k ω * (g ω - g ω0) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith) hR) (by linarith)
  have : g ω * (a * R p k ω) + g ω0 * ((1 - a) * R p k ω) -
      (g ω * (p k * R p k ω) + g ω0 * ((1 - p k) * R p k ω)) =
      (a - p k) * R p k ω * (g ω - g ω0) := by ring
  linarith

lemma F_mono {g : (Fin N → Bool) → ℝ} (hg : ∀ ω ω', ω ≤ ω' → g ω' ≤ g ω)
    {p p' : Fin N → ℝ} (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1) (hp' : ∀ j, 0 ≤ p' j ∧ p' j ≤ 1)
    (hpp : p ≤ p') : ∑ ω, g ω * W p' ω ≤ ∑ ω, g ω * W p ω := by
  classical
  let q : Finset (Fin N) → Fin N → ℝ := fun s j => if j ∈ s then p' j else p j
  have hq : ∀ s j, 0 ≤ q s j ∧ q s j ≤ 1 := by
    intro s j; simp only [q]; split_ifs
    · exact hp' j
    · exact hp j
  have main : ∀ s : Finset (Fin N), ∑ ω, g ω * W (q s) ω ≤ ∑ ω, g ω * W p ω := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [q]
    | insert a s has ih =>
      have e : q (insert a s) = Function.update (q s) a (p' a) := by
        funext j
        by_cases hj : j = a
        · subst hj; simp [q]
        · simp [q, hj]
      rw [e]
      refine le_trans (F_step hg (hq s) a ?_) ih
      simp only [q, has, if_false]
      exact hpp a
  have e : q univ = p' := by funext j; simp [q]
  simpa [e] using main univ

/-! ## Expected profit and distortion in terms of `gs` -/

lemma distortion_eq {θ : Fin N → Fin N → ℝ} (hθ : Reg θ) {dbar v : ℝ} (hv : 0 < v)
    (hdb : 0 ≤ dbar) (P : ℝ → ℝ) {Z : Fin N → ℝ} (hZ : ∀ j, v + dbar ≤ Z j) (i : Fin N) :
    distortion θ dbar v P Z i =
      ∑ ω, (dbar - ∑ j, θ i j * gs θ dbar v ω j) *
        W (Function.update (fun j => P (Z j)) i 1) ω := by
  unfold distortion
  have key : ∀ ω, paymentEq θ dbar v ω Z = gs θ dbar v ω :=
    fun ω => paymentEq_eq hθ hv hdb ω hZ
  simp only [key]
  exact filter_sum_eq (fun j => P (Z j)) i _

lemma profit_eq {θ : Fin N → Fin N → ℝ} (hθ : Reg θ) {dbar v : ℝ} (hv : 0 < v)
    (hdb : 0 ≤ dbar) (ω : Fin N → Bool) {Z : Fin N → ℝ} (hZ : ∀ j, v + dbar ≤ Z j) (i : Fin N) :
    profit θ dbar v ω Z i =
      if ω i then (∑ j, θ i j * gs θ dbar v ω j + Z i - v - dbar) else 0 := by
  unfold profit
  rw [paymentEq_eq hθ hv hdb ω hZ]
  have hfix := gs_apply hθ hv hdb ω i
  have hb := gs_box (θ := θ) (v := v) hdb ω
  have h0 := sum_nn hθ hb i
  unfold clr at hfix
  unfold cash
  by_cases hω : ω i = true
  · simp only [hω, if_true] at hfix ⊢
    rw [hfix]
    have := hZ i
    exact max_eq_left (by linarith)
  · have hf : ω i = false := by simpa using hω
    simp only [hf, Bool.false_eq_true, if_false, add_zero] at hfix ⊢
    rw [hfix]
    apply max_eq_right
    have := le_max_left (∑ j, θ i j * gs θ dbar v ω j - v) 0
    linarith

lemma expProfit_eq {θ : Fin N → Fin N → ℝ} (hθ : Reg θ) {dbar v : ℝ} (hv : 0 < v)
    (hdb : 0 ≤ dbar) (P : ℝ → ℝ) {Z : Fin N → ℝ} (hZ : ∀ j, v + dbar ≤ Z j) (i : Fin N)
    {y : ℝ} (hy : v + dbar ≤ y) :
    expProfit θ dbar v P (Function.update Z i y) i =
      P y * (y - v - distortion θ dbar v P Z i) := by
  have hZ' : ∀ j, v + dbar ≤ Function.update Z i y j := by
    intro j
    by_cases hj : j = i
    · subst hj; simp [hy]
    · rw [Function.update_of_ne hj]; exact hZ j
  rw [distortion_eq hθ hv hdb P hZ i]
  unfold expProfit
  have hsum := sum_W (Function.update (fun j => P (Z j)) i 1)
  have term : ∀ ω, profit θ dbar v ω (Function.update Z i y) i *
      stateProb P (Function.update Z i y) ω =
      P y * ((y - v) * W (Function.update (fun j => P (Z j)) i 1) ω -
        (dbar - ∑ j, θ i j * gs θ dbar v ω j) *
          W (Function.update (fun j => P (Z j)) i 1) ω) := by
    intro ω
    rw [profit_eq hθ hv hdb ω hZ' i, W_update_one]
    have hsp : stateProb P (Function.update Z i y) ω =
        (if ω i then P y else 1 - P y) *
          ∏ j ∈ univ.erase i, (if ω j then P (Z j) else 1 - P (Z j)) := by
      unfold stateProb
      rw [← Finset.mul_prod_erase univ
        (fun j => if ω j then P (Function.update Z i y j) else 1 - P (Function.update Z i y j))
        (mem_univ i)]
      simp only [Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [hsp]
    simp only [Function.update_self]
    by_cases hω : ω i = true
    · simp only [hω, if_true]; ring
    · have hf : ω i = false := by simpa using hω
      simp [hf]
  rw [Finset.sum_congr rfl fun ω _ => term ω, ← Finset.mul_sum, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hsum]
  ring

lemma distortion_mono {θ : Fin N → Fin N → ℝ} (hθ : Reg θ) {dbar v : ℝ} (hv : 0 < v)
    (hdb : 0 ≤ dbar) {P : ℝ → ℝ} {Zlo Zhi : ℝ} (hnd : v + dbar ≤ Zlo)
    (hP01 : ∀ z ∈ Set.Icc Zlo Zhi, 0 < P z ∧ P z < 1)
    (hPanti : AntitoneOn P (Set.Icc Zlo Zhi)) {Z Z' : Fin N → ℝ}
    (hZ : ∀ j, Z j ∈ Set.Icc Zlo Zhi) (hZ' : ∀ j, Z' j ∈ Set.Icc Zlo Zhi) (hle : Z ≤ Z')
    (i : Fin N) : distortion θ dbar v P Z i ≤ distortion θ dbar v P Z' i := by
  have hZv : ∀ j, v + dbar ≤ Z j := fun j => le_trans hnd (hZ j).1
  have hZv' : ∀ j, v + dbar ≤ Z' j := fun j => le_trans hnd (hZ' j).1
  rw [distortion_eq hθ hv hdb P hZv i, distortion_eq hθ hv hdb P hZv' i]
  have hb : ∀ (X : Fin N → ℝ), (∀ j, X j ∈ Set.Icc Zlo Zhi) →
      ∀ j, 0 ≤ Function.update (fun j => P (X j)) i 1 j ∧
        Function.update (fun j => P (X j)) i 1 j ≤ 1 := by
    intro X hX j
    by_cases hj : j = i
    · subst hj; simp
    · rw [Function.update_of_ne hj]
      exact ⟨(hP01 _ (hX j)).1.le, (hP01 _ (hX j)).2.le⟩
  apply F_mono _ (hb Z' hZ') (hb Z hZ)
  · intro j
    by_cases hj : j = i
    · subst hj; simp
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
      exact hPanti (hZ j) (hZ' j) (hle j)
  · intro ω ω' h
    have h1 := gs_mono hθ hv hdb (dbar := dbar) h
    have : ∑ j, θ i j * gs θ dbar v ω j ≤ ∑ j, θ i j * gs θ dbar v ω' j :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h1 j) (hθ.nonneg i j)
    linarith

/-! ## The two networks are regular -/

lemma reg_ring (hN : 2 ≤ N) : Reg (thetaRing N) where
  nonneg i j := by unfold thetaRing; split_ifs <;> norm_num
  rowsum i := by
    have hpos : 0 < N := by omega
    have hc : ((i : ℕ) + N - 1) % N < N := Nat.mod_lt _ hpos
    have h : ∀ j : Fin N, ((j : ℕ) = ((i : ℕ) + N - 1) % N) ↔ j = ⟨_, hc⟩ :=
      fun j => ⟨fun h => Fin.ext h, fun h => by subst h; rfl⟩
    unfold thetaRing
    simp only [h]
    simp

lemma reg_complete (hN : 2 ≤ N) : Reg (thetaComplete N) where
  nonneg i j := by
    have : (1 : ℝ) ≤ (N : ℝ) - 1 := by
      have : (2 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    unfold thetaComplete; split_ifs
    · exact le_rfl
    · exact div_nonneg zero_le_one (by linarith)
  rowsum i := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) - 1 := by
      have : (2 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have e : ∀ j : Fin N, (if i = j then (0 : ℝ) else 1 / ((N : ℝ) - 1)) =
        1 / ((N : ℝ) - 1) - (if i = j then 1 / ((N : ℝ) - 1) else 0) := by
      intro j; split_ifs <;> ring
    unfold thetaComplete
    rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    field_simp

lemma complete_perm (σ : Equiv.Perm (Fin N)) (i j : Fin N) :
    thetaComplete N (σ i) (σ j) = thetaComplete N i j := by
  unfold thetaComplete
  simp [σ.injective.eq_iff]

/-! ## Permutation equivariance -/

def precomp (σ : Equiv.Perm (Fin N)) : (Fin N → Bool) ≃ (Fin N → Bool) where
  toFun ω := ω ∘ σ
  invFun ω := ω ∘ σ.symm
  left_inv ω := by funext j; simp
  right_inv ω := by funext j; simp

lemma post_perm {θ : Fin N → Fin N → ℝ} {σ : Equiv.Perm (Fin N)}
    (hσθ : ∀ i j, θ (σ i) (σ j) = θ i j) {dbar v : ℝ} {ω : Fin N → Bool} {d : Fin N → ℝ}
    (hd : d ∈ PostSet θ dbar v ω) : d ∘ σ ∈ PostSet θ dbar v (ω ∘ σ) := by
  refine ⟨fun i => hd.1 (σ i), fun i => ?_⟩
  have h := hd.2 (σ i)
  have hs : ∑ j, θ i j * d (σ j) = ∑ j, θ (σ i) j * d j := by
    rw [← Equiv.sum_comp σ (fun j => θ (σ i) j * d j)]
    simp only [hσθ]
  have e : clr θ dbar v (ω ∘ σ) (d ∘ σ) i = clr θ dbar v ω d (σ i) := by
    unfold clr
    simp only [Function.comp, hs]
  rw [e]
  exact h

lemma gs_perm {θ : Fin N → Fin N → ℝ} (hθ : Reg θ) {σ : Equiv.Perm (Fin N)}
    (hσθ : ∀ i j, θ (σ i) (σ j) = θ i j) {dbar v : ℝ} (hv : 0 < v) (hdb : 0 ≤ dbar)
    (ω : Fin N → Bool) : gs θ dbar v (ω ∘ σ) = gs θ dbar v ω ∘ σ := by
  have hmem : ∀ ω', gs θ dbar v ω' ∈ PostSet θ dbar v ω' :=
    fun ω' => ⟨gs_box hdb ω', (gs_fixed hθ hv hdb ω').symm.le⟩
  have hσθ' : ∀ i j, θ (σ.symm i) (σ.symm j) = θ i j := by
    intro i j
    have := hσθ (σ.symm i) (σ.symm j)
    simp only [Equiv.apply_symm_apply] at this
    exact this.symm
  apply le_antisymm
  · intro i
    have h := le_gs (post_perm hσθ' (hmem (ω ∘ σ)))
    have e : (ω ∘ σ) ∘ σ.symm = ω := by funext j; simp
    rw [e] at h
    have := h (σ i)
    simpa using this
  · exact le_gs (post_perm hσθ (hmem ω))

lemma distortion_perm {θ : Fin N → Fin N → ℝ} (hθ : Reg θ) {σ : Equiv.Perm (Fin N)}
    (hσθ : ∀ i j, θ (σ i) (σ j) = θ i j) {dbar v : ℝ} (hv : 0 < v) (hdb : 0 ≤ dbar)
    (P : ℝ → ℝ) {Z : Fin N → ℝ} (hZ : ∀ j, v + dbar ≤ Z j) (i : Fin N) :
    distortion θ dbar v P (Z ∘ σ) i = distortion θ dbar v P Z (σ i) := by
  rw [distortion_eq hθ hv hdb P (Z := Z ∘ σ) (fun j => hZ (σ j)) i,
    distortion_eq hθ hv hdb P hZ (σ i)]
  rw [← Equiv.sum_comp (precomp σ)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have h1 : (precomp σ) ω = ω ∘ σ := rfl
  rw [h1, gs_perm hθ hσθ hv hdb ω]
  have hs : ∑ j, θ i j * (gs θ dbar v ω ∘ σ) j = ∑ j, θ (σ i) j * gs θ dbar v ω j := by
    rw [← Equiv.sum_comp σ (fun j => θ (σ i) j * gs θ dbar v ω j)]
    simp only [hσθ, Function.comp]
  have hu : Function.update (fun j => P ((Z ∘ σ) j)) i 1 =
      Function.update (fun j => P (Z j)) (σ i) 1 ∘ σ := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · have : σ j ≠ σ i := fun h => hj (σ.injective h)
      simp [Function.update_of_ne hj, Function.update_of_ne this]
  have hw : W (Function.update (fun j => P ((Z ∘ σ) j)) i 1) (ω ∘ σ) =
      W (Function.update (fun j => P (Z j)) (σ i) 1) ω := by
    rw [hu]
    unfold W
    exact Equiv.prod_comp σ (fun j => if ω j then Function.update (fun j => P (Z j)) (σ i) 1 j
      else 1 - Function.update (fun j => P (Z j)) (σ i) 1 j)
  rw [hs, hw]

/-! ## Least maximizer of the reduced objective -/

def phi (P : ℝ → ℝ) (t y : ℝ) : ℝ := P y * (y - t)

def maxSet (P : ℝ → ℝ) (Zlo Zhi t : ℝ) : Set ℝ :=
  {z | z ∈ Set.Icc Zlo Zhi ∧ ∀ y ∈ Set.Icc Zlo Zhi, phi P t y ≤ phi P t z}

noncomputable def mt (P : ℝ → ℝ) (Zlo Zhi t : ℝ) : ℝ := sInf (maxSet P Zlo Zhi t)

lemma maxSet_cn {P : ℝ → ℝ} {Zlo Zhi : ℝ} (hZ : Zlo ≤ Zhi)
    (hPcont : ContinuousOn P (Set.Icc Zlo Zhi)) (t : ℝ) :
    IsCompact (maxSet P Zlo Zhi t) ∧ (maxSet P Zlo Zhi t).Nonempty := by
  have hc : ContinuousOn (phi P t) (Set.Icc Zlo Zhi) := by
    unfold phi
    exact hPcont.mul ((continuous_id.sub continuous_const).continuousOn)
  obtain ⟨z0, hz0, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hZ) hc
  have heq : maxSet P Zlo Zhi t = Set.Icc Zlo Zhi ∩ phi P t ⁻¹' Set.Ici (phi P t z0) := by
    ext z
    constructor
    · rintro ⟨hz, h⟩; exact ⟨hz, h z0 hz0⟩
    · rintro ⟨hz, h⟩; exact ⟨hz, fun y hy => le_trans (hmax hy) h⟩
  refine ⟨?_, ⟨z0, hz0, fun y hy => hmax hy⟩⟩
  rw [heq]
  exact isCompact_Icc.of_isClosed_subset
    (hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici) Set.inter_subset_left

lemma mt_mem {P : ℝ → ℝ} {Zlo Zhi : ℝ} (hZ : Zlo ≤ Zhi)
    (hPcont : ContinuousOn P (Set.Icc Zlo Zhi)) (t : ℝ) : mt P Zlo Zhi t ∈ maxSet P Zlo Zhi t :=
  (maxSet_cn hZ hPcont t).1.sInf_mem (maxSet_cn hZ hPcont t).2

lemma mt_le {P : ℝ → ℝ} {Zlo Zhi t z : ℝ} (hz : z ∈ maxSet P Zlo Zhi t) : mt P Zlo Zhi t ≤ z :=
  csInf_le ⟨Zlo, fun _ hx => hx.1.1⟩ hz

lemma mt_mono {P : ℝ → ℝ} {Zlo Zhi : ℝ} (hZ : Zlo ≤ Zhi)
    (hPcont : ContinuousOn P (Set.Icc Zlo Zhi)) (hPanti : AntitoneOn P (Set.Icc Zlo Zhi))
    {t t' : ℝ} (htt : t ≤ t') : mt P Zlo Zhi t ≤ mt P Zlo Zhi t' := by
  by_contra hlt
  push Not at hlt
  set a := mt P Zlo Zhi t'
  set b := mt P Zlo Zhi t
  have ha := mt_mem hZ hPcont t'
  have hb := mt_mem hZ hPcont t
  have hna : a ∉ maxSet P Zlo Zhi t := fun h => absurd (mt_le h) (not_le.mpr hlt)
  have hlt2 : phi P t a < phi P t b := by
    have : ¬ ∀ y ∈ Set.Icc Zlo Zhi, phi P t y ≤ phi P t a := fun h => hna ⟨ha.1, h⟩
    push Not at this
    obtain ⟨y, hy, hy2⟩ := this
    exact lt_of_lt_of_le hy2 (hb.2 y hy)
  have h3 := ha.2 b hb.1
  have hP : P b ≤ P a := hPanti ha.1 hb.1 hlt.le
  unfold phi at hlt2 h3
  nlinarith [mul_nonneg (sub_nonneg.mpr htt) (sub_nonneg.mpr hP)]

lemma br_iff {θ : Fin N → Fin N → ℝ} (hθ : Reg θ) {dbar v : ℝ} (hv : 0 < v) (hdb : 0 ≤ dbar)
    {P : ℝ → ℝ} {Zlo Zhi : ℝ} (hnd : v + dbar ≤ Zlo) {Z : Fin N → ℝ}
    (hZ : ∀ j, Z j ∈ Set.Icc Zlo Zhi) (i : Fin N) (z : ℝ) :
    z ∈ bestResponse θ dbar v P Zlo Zhi Z i ↔
      z ∈ maxSet P Zlo Zhi (v + distortion θ dbar v P Z i) := by
  have hZv : ∀ j, v + dbar ≤ Z j := fun j => le_trans hnd (hZ j).1
  unfold bestResponse maxSet phi
  constructor
  · rintro ⟨hz, h⟩
    refine ⟨hz, fun y hy => ?_⟩
    have := h y hy
    rw [expProfit_eq hθ hv hdb P hZv i (le_trans hnd hy.1),
      expProfit_eq hθ hv hdb P hZv i (le_trans hnd hz.1)] at this
    simpa only [sub_sub] using this
  · rintro ⟨hz, h⟩
    refine ⟨hz, fun y hy => ?_⟩
    have := h y hy
    rw [expProfit_eq hθ hv hdb P hZv i (le_trans hnd hy.1),
      expProfit_eq hθ hv hdb P hZv i (le_trans hnd hz.1)]
    simpa only [sub_sub] using this

lemma complete_const (hN : 2 ≤ N) {dbar v : ℝ} (hv : 0 < v) (hdb : 0 ≤ dbar)
    {P : ℝ → ℝ} {Zlo Zhi : ℝ} (hnd : v + dbar ≤ Zlo) {ZC : Fin N → ℝ}
    (hC : IsLeast {Z | IsEquilibrium (thetaComplete N) dbar v P Zlo Zhi Z} ZC) (a b : Fin N) :
    ZC a ≤ ZC b := by
  have hθ := reg_complete hN
  have hbox : ∀ j, ZC j ∈ Set.Icc Zlo Zhi := fun j => (hC.1 j).1
  have hZv : ∀ j, v + dbar ≤ ZC j := fun j => le_trans hnd (hbox j).1
  set σ : Equiv.Perm (Fin N) := Equiv.swap a b
  have heq : IsEquilibrium (thetaComplete N) dbar v P Zlo Zhi (ZC ∘ σ) := by
    intro i
    have hbox' : ∀ j, (ZC ∘ σ) j ∈ Set.Icc Zlo Zhi := fun j => hbox (σ j)
    rw [br_iff hθ hv hdb hnd hbox' i,
      distortion_perm hθ (complete_perm σ) hv hdb P hZv i]
    have := (br_iff hθ hv hdb hnd hbox (σ i) (ZC (σ i))).1 (hC.1 (σ i))
    exact this
  have := hC.2 heq a
  simpa [σ] using this

/-! ## Ring versus complete at a constant profile -/

lemma gs_succ {θ : Fin N → Fin N → ℝ} (hθ : Reg θ) {dbar v : ℝ} (hv : 0 < v) (hdb : 0 ≤ dbar)
    (ω : Fin N → Bool) (j : Fin N) (hj : ω j = true) : gs θ dbar v ω j = dbar := by
  rw [gs_apply hθ hv hdb ω j]
  unfold clr
  simp [hj]

def cnt (i : Fin N) (ω : Fin N → Bool) : ℕ := ((univ.erase i).filter (fun j => ω j = true)).card

def Om (i : Fin N) (t : ℕ) : Finset (Fin N → Bool) :=
  univ.filter (fun ω : Fin N → Bool => ω i = true ∧ cnt i ω = t)

lemma mem_Om {i : Fin N} {t : ℕ} {ω : Fin N → Bool} : ω ∈ Om i t ↔ ω i = true ∧ cnt i ω = t := by
  simp [Om]

lemma card_Om_filter (i : Fin N) (t : ℕ) (B : Finset (Fin N)) (hiB : i ∉ B) :
    ((Om i t).filter (fun ω => ∀ j ∈ B, ω j = false)).card = (N - 1 - B.card).choose t := by
  have hsub : B ⊆ univ.erase i := fun j hj =>
    mem_erase.mpr ⟨fun h => hiB (h ▸ hj), mem_univ j⟩
  have hcard : ((univ.erase i) \ B).card = N - 1 - B.card := by
    rw [card_sdiff_of_subset hsub, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
  rw [← hcard, ← card_powersetCard]
  refine Finset.card_nbij' (fun ω => (univ.erase i).filter (fun j => ω j = true))
    (fun T k => decide (k = i ∨ k ∈ T)) ?_ ?_ ?_ ?_
  · intro ω hω
    rw [Finset.mem_coe, mem_filter, mem_Om] at hω
    rw [Finset.mem_coe, mem_powersetCard]
    refine ⟨fun j hj => ?_, hω.1.2⟩
    simp only [mem_filter, mem_erase, mem_univ, and_true] at hj
    refine mem_sdiff.mpr ⟨mem_erase.mpr ⟨hj.1, mem_univ j⟩, fun hjB => ?_⟩
    have := hω.2 j hjB
    rw [hj.2] at this
    exact Bool.noConfusion this
  · intro T hT
    rw [Finset.mem_coe, mem_powersetCard] at hT
    rw [Finset.mem_coe, mem_filter, mem_Om]
    have hTi : i ∉ T := fun h => by
      have := hT.1 h
      simp at this
    refine ⟨⟨by simp, ?_⟩, fun j hjB => ?_⟩
    · rw [← hT.2]
      unfold cnt
      congr 1
      ext k
      simp only [mem_filter, mem_erase, mem_univ, and_true, decide_eq_true_eq]
      constructor
      · rintro ⟨hk, h | h⟩
        · exact absurd h hk
        · exact h
      · intro h
        refine ⟨fun hk => hTi (hk ▸ h), Or.inr h⟩
    · have hji : j ≠ i := fun h => hiB (h ▸ hjB)
      have hjT : j ∉ T := fun h => by
        have := hT.1 h
        simp only [mem_sdiff] at this
        exact this.2 hjB
      simp [hji, hjT]
  · intro ω hω
    rw [Finset.mem_coe, mem_filter, mem_Om] at hω
    funext k
    by_cases hk : k = i
    · subst hk; simp [hω.1.1]
    · simp [hk]
  · intro T hT
    rw [Finset.mem_coe, mem_powersetCard] at hT
    ext k
    simp only [mem_filter, mem_erase, mem_univ, and_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hk, h | h⟩
      · exact absurd h hk
      · exact h
    · intro h
      have := hT.1 h
      simp only [mem_sdiff, mem_erase] at this
      exact ⟨this.1.1, Or.inr h⟩

lemma card_Om (i : Fin N) (t : ℕ) : (Om i t).card = (N - 1).choose t := by
  have := card_Om_filter i t ∅ (by simp)
  simpa using this

lemma prod_W_const (i : Fin N) {p : Fin N → ℝ} {q : ℝ} (hp : ∀ j, p j = q) (t : ℕ)
    (ω : Fin N → Bool) (hω : ω ∈ Om i t) :
    W (Function.update p i 1) ω = q ^ t * (1 - q) ^ (N - 1 - t) := by
  simp only [Om, mem_filter, mem_univ, true_and] at hω
  rw [W_update_one, if_pos hω.1]
  simp only [hp]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  have h1 : ((univ.erase i).filter (fun j => ω j = true)).card = t := hω.2
  have h2 := Finset.card_filter_add_card_filter_not (s := univ.erase i) (fun j => ω j = true)
  rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin] at h2
  have h3 : ((univ.erase i).filter (fun j => ¬ ω j = true)).card = N - 1 - t := by omega
  rw [h1, h3]

lemma decomp (hN1 : 1 ≤ N) (i : Fin N) {p : Fin N → ℝ} {q : ℝ} (hp : ∀ j, p j = q)
    (g : (Fin N → Bool) → ℝ) :
    ∑ ω, g ω * W (Function.update p i 1) ω =
      ∑ t ∈ range N, q ^ t * (1 - q) ^ (N - 1 - t) * ∑ ω ∈ Om i t, g ω := by
  have hsplit := Finset.sum_filter_add_sum_filter_not univ (fun ω : Fin N → Bool => ω i = true)
    (fun ω => g ω * W (Function.update p i 1) ω)
  have hzero : ∑ ω ∈ univ.filter (fun ω : Fin N → Bool => ¬ ω i = true),
      g ω * W (Function.update p i 1) ω = 0 := by
    refine Finset.sum_eq_zero fun ω hω => ?_
    simp only [mem_filter, mem_univ, true_and] at hω
    rw [W_update_one, if_neg hω, mul_zero]
  rw [← hsplit, hzero, add_zero]
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter (fun ω : Fin N → Bool => ω i = true))
    (t := range N) (g := cnt i) ?_]
  · refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.filter_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω hω => ?_
    rw [prod_W_const i hp t ω hω]
    ring
  · intro ω _
    simp only [mem_range]
    have := Finset.card_le_card (Finset.filter_subset (fun j => ω j = true) (univ.erase i))
    rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin] at this
    unfold cnt
    omega

lemma mod2 {M x : ℕ} (h : x < 2 * M) : x % M = if x < M then x else x - M := by
  split_ifs with h1
  · exact Nat.mod_eq_of_lt h1
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

def bpos (i : Fin N) (r : ℕ) : Fin N :=
  ⟨((i : ℕ) + N - (r + 1)) % N, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

lemma bpos_val (i : Fin N) (r : ℕ) : ((bpos i r : Fin N) : ℕ) =
    if (i : ℕ) + N - (r + 1) < N then (i : ℕ) + N - (r + 1)
    else (i : ℕ) + N - (r + 1) - N := by
  have := i.isLt
  exact mod2 (by omega)

lemma bpos_succ (i : Fin N) (r : ℕ) (hr : r + 2 ≤ N) :
    bpos (bpos i r) 0 = bpos i (r + 1) := by
  apply Fin.ext
  have := i.isLt
  rw [bpos_val (bpos i r) 0, bpos_val i r, bpos_val i (r + 1)]
  split_ifs <;> omega

lemma bpos_inj (i : Fin N) {r r' : ℕ} (hr : r + 1 ≤ N) (hr' : r' + 1 ≤ N)
    (h : bpos i r = bpos i r') : r = r' := by
  have h2 := congrArg Fin.val h
  have := i.isLt
  rw [bpos_val, bpos_val] at h2
  split_ifs at h2 <;> omega

lemma bpos_ne (i : Fin N) {r : ℕ} (hr : r + 2 ≤ N) : bpos i r ≠ i := by
  intro h
  have h2 := congrArg Fin.val h
  have := i.isLt
  rw [bpos_val] at h2
  split_ifs at h2 <;> omega

lemma bpos_last (i : Fin N) : bpos i (N - 1) = i := by
  apply Fin.ext
  have := i.isLt
  rw [bpos_val]
  split_ifs <;> omega

lemma ring_sum (k : Fin N) (d : Fin N → ℝ) : ∑ j, thetaRing N k j * d j = d (bpos k 0) := by
  have h : ∀ j : Fin N, ((j : ℕ) = ((k : ℕ) + N - 1) % N) ↔ j = bpos k 0 := by
    intro j
    rw [Fin.ext_iff]
    simp [bpos]
  unfold thetaRing
  simp only [h, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', mem_univ, if_true]

lemma ring_step (hN : 2 ≤ N) {dbar v : ℝ} (hv : 0 < v) (hdb : 0 ≤ dbar) (ω : Fin N → Bool)
    (k : Fin N) :
    gs (thetaRing N) dbar v ω (bpos k 0) - v ≤ gs (thetaRing N) dbar v ω k := by
  have h := gs_apply (reg_ring hN) hv hdb ω k
  have hb := gs_box (θ := thetaRing N) (v := v) hdb ω
  unfold clr at h
  rw [ring_sum] at h
  rw [h]
  split_ifs
  · linarith [(hb (bpos k 0)).2]
  · exact le_max_left _ _

lemma ring_chain (hN : 2 ≤ N) {dbar v : ℝ} (hv : 0 < v) (hdb : 0 ≤ dbar) (ω : Fin N → Bool)
    (i : Fin N) : ∀ o : ℕ, o + 1 ≤ N →
      gs (thetaRing N) dbar v ω (bpos i o) - (o : ℝ) * v ≤ gs (thetaRing N) dbar v ω (bpos i 0) := by
  intro o
  induction o with
  | zero => intro _; simp
  | succ o ih =>
    intro ho
    have h1 := ih (by omega)
    have h2 := ring_step hN hv hdb ω (bpos i o)
    rw [bpos_succ i o (by omega)] at h2
    push_cast
    linarith

lemma gR_le_K (hN : 2 ≤ N) {dbar v : ℝ} (hv : 0 < v) (hdb : 0 ≤ dbar) (ω : Fin N → Bool)
    (i : Fin N) (hω : ω i = true) :
    dbar - gs (thetaRing N) dbar v ω (bpos i 0) ≤
      v * (((range (N - 1)).filter
        (fun o => ∀ r, r < o + 1 → ω (bpos i r) = false)).card : ℝ) := by
  classical
  have hex : ∃ o, ω (bpos i o) = true := ⟨N - 1, by rw [bpos_last]; exact hω⟩
  have hK : ω (bpos i (Nat.find hex)) = true := Nat.find_spec hex
  have hKle : Nat.find hex ≤ N - 1 := Nat.find_min' hex (by rw [bpos_last]; exact hω)
  have hmin : ∀ r < Nat.find hex, ω (bpos i r) = false := by
    intro r hr
    have := Nat.find_min hex hr
    simpa using this
  have hdK := gs_succ (reg_ring hN) hv hdb ω _ hK
  have hch := ring_chain hN hv hdb ω i (Nat.find hex) (by omega)
  rw [hdK] at hch
  have hcard : Nat.find hex ≤ ((range (N - 1)).filter
      (fun o => ∀ r, r < o + 1 → ω (bpos i r) = false)).card := by
    have hsub : range (Nat.find hex) ⊆ (range (N - 1)).filter
        (fun o => ∀ r, r < o + 1 → ω (bpos i r) = false) := by
      intro o ho
      simp only [mem_range] at ho
      simp only [mem_filter, mem_range]
      exact ⟨by omega, fun r hr => hmin r (by omega)⟩
    simpa using Finset.card_le_card hsub
  have hcardR : ((Nat.find hex : ℕ) : ℝ) ≤ (((range (N - 1)).filter
      (fun o => ∀ r, r < o + 1 → ω (bpos i r) = false)).card : ℝ) := by exact_mod_cast hcard
  have := mul_le_mul_of_nonneg_left hcardR hv.le
  linarith

lemma hockey (t : ℕ) : ∀ n, ∑ o ∈ range n, o.choose t = n.choose (t + 1) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, Nat.choose_succ_succ']; ring

lemma ring_count (hN : 2 ≤ N) (i : Fin N) (t : ℕ) :
    ∑ ω ∈ Om i t, ((range (N - 1)).filter
      (fun o => ∀ r, r < o + 1 → ω (bpos i r) = false)).card = (N - 1).choose (t + 1) := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  have key : ∀ o ∈ range (N - 1), (∑ ω ∈ Om i t,
      if (∀ r, r < o + 1 → ω (bpos i r) = false) then 1 else 0) =
      (N - 1 - 1 - o).choose t := by
    intro o ho
    simp only [mem_range] at ho
    rw [← Finset.card_filter]
    have hB : ((range (o + 1)).image (bpos i)).card = o + 1 := by
      rw [card_image_of_injOn, card_range]
      intro a ha b hb hab
      simp only [coe_range, Set.mem_Iio] at ha hb
      exact bpos_inj i (by omega) (by omega) hab
    have hiB : i ∉ (range (o + 1)).image (bpos i) := by
      simp only [mem_image, mem_range, not_exists, not_and]
      intro r hr
      exact bpos_ne i (by omega)
    have h := card_Om_filter i t ((range (o + 1)).image (bpos i)) hiB
    rw [hB] at h
    have e : N - 1 - (o + 1) = N - 1 - 1 - o := by omega
    rw [e] at h
    rw [← h]
    congr 1
    apply Finset.filter_congr
    intro ω _
    simp
  rw [Finset.sum_congr rfl key]
  have h2 := Finset.sum_range_reflect (fun o => o.choose t) (N - 1)
  rw [h2, hockey]

lemma ring_Om_bound (hN : 2 ≤ N) {dbar v : ℝ} (hv : 0 < v) (hdb : 0 ≤ dbar) (i : Fin N)
    (t : ℕ) :
    ∑ ω ∈ Om i t, (dbar - gs (thetaRing N) dbar v ω (bpos i 0)) ≤
      min (v * ((N - 1).choose (t + 1) : ℝ)) (dbar * ((N - 2).choose t : ℝ)) := by
  apply le_min
  · calc ∑ ω ∈ Om i t, (dbar - gs (thetaRing N) dbar v ω (bpos i 0))
        ≤ ∑ ω ∈ Om i t, v * (((range (N - 1)).filter
            (fun o => ∀ r, r < o + 1 → ω (bpos i r) = false)).card : ℝ) := by
          refine Finset.sum_le_sum fun ω hω => gR_le_K hN hv hdb ω i ?_
          simp only [Om, mem_filter, mem_univ, true_and] at hω
          exact hω.1
      _ = v * ((N - 1).choose (t + 1) : ℝ) := by
          rw [← Finset.mul_sum, ← ring_count hN i t]
          push_cast
          rfl
  · calc ∑ ω ∈ Om i t, (dbar - gs (thetaRing N) dbar v ω (bpos i 0))
        ≤ ∑ ω ∈ Om i t, dbar * (if ω (bpos i 0) = false then 1 else 0) := by
          refine Finset.sum_le_sum fun ω hω => ?_
          by_cases h : ω (bpos i 0) = true
          · rw [gs_succ (reg_ring hN) hv hdb ω _ h]
            simp [h]
          · have hf : ω (bpos i 0) = false := by simpa using h
            have := (gs_box (θ := thetaRing N) (v := v) hdb ω (bpos i 0)).1
            simp only [hf, if_true, mul_one]
            linarith
      _ = dbar * ((N - 2).choose t : ℝ) := by
          rw [← Finset.mul_sum, Finset.sum_boole]
          congr 1
          have hiB : i ∉ ({bpos i 0} : Finset (Fin N)) := by
            simp only [mem_singleton]
            exact fun h => bpos_ne i (r := 0) (by omega) h.symm
          have h := card_Om_filter i t {bpos i 0} hiB
          rw [card_singleton] at h
          have e : N - 1 - 1 = N - 2 := by omega
          rw [e] at h
          rw [← h]
          congr 2
          apply Finset.filter_congr
          intro ω _
          simp

lemma complete_sum (hN : 2 ≤ N) (k : Fin N) (d : Fin N → ℝ) :
    ∑ j, thetaComplete N k j * d j = (∑ j, d j - d k) / ((N : ℝ) - 1) := by
  have e : ∀ j, thetaComplete N k j * d j =
      d j / ((N : ℝ) - 1) - (if k = j then d j / ((N : ℝ) - 1) else 0) := by
    intro j; unfold thetaComplete; split_ifs <;> ring
  rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_sub_distrib, Finset.sum_ite_eq]
  simp only [mem_univ, if_true]
  rw [← Finset.sum_div, sub_div]

lemma complete_fail_le (hN : 2 ≤ N) {dbar v : ℝ} (hv : 0 < v) (hdb : 0 ≤ dbar)
    (ω : Fin N → Bool) (i : Fin N) (hω : ω i = true) (k : Fin N) (hk : ¬ ω k = true) :
    gs (thetaComplete N) dbar v ω k ≤
      max (dbar - ((N : ℝ) - 1) * v / ((univ.filter (fun j => ω j = true)).card : ℝ)) 0 := by
  classical
  have hθ := reg_complete hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hspos : (0 : ℝ) < ((univ.filter (fun j => ω j = true)).card : ℝ) := by
    have : 0 < (univ.filter (fun j => ω j = true)).card := Finset.card_pos.mpr ⟨i, by simp [hω]⟩
    exact_mod_cast this
  have hsf : (univ.filter (fun j => ω j = true)).card +
      (univ.filter (fun j => ¬ ω j = true)).card = N := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin N)))
      (fun j => ω j = true)
    simpa [card_univ, Fintype.card_fin] using this
  have hsfR : ((univ.filter (fun j => ω j = true)).card : ℝ) +
      ((univ.filter (fun j => ¬ ω j = true)).card : ℝ) = N := by exact_mod_cast hsf
  have hkF : k ∈ univ.filter (fun j => ¬ ω j = true) := by simp [hk]
  obtain ⟨k1, hk1F, hk1max⟩ := (univ.filter (fun j => ¬ ω j = true)).exists_max_image
    (gs (thetaComplete N) dbar v ω) ⟨k, hkF⟩
  have hkM := hk1max k hkF
  by_contra hcon
  push Not at hcon
  have hM0 : 0 < gs (thetaComplete N) dbar v ω k1 :=
    lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hcon hkM)
  have hfix := gs_apply hθ hv hdb ω k1
  have hk1f : ¬ ω k1 = true := by simpa using hk1F
  unfold clr at hfix
  rw [if_neg hk1f, complete_sum hN] at hfix
  have hMeq : gs (thetaComplete N) dbar v ω k1 =
      (∑ j, gs (thetaComplete N) dbar v ω j - gs (thetaComplete N) dbar v ω k1) /
        ((N : ℝ) - 1) - v := by
    rcases le_total ((∑ j, gs (thetaComplete N) dbar v ω j - gs (thetaComplete N) dbar v ω k1) /
        ((N : ℝ) - 1) - v) 0 with h | h
    · rw [max_eq_right h] at hfix; linarith
    · rw [max_eq_left h] at hfix; exact hfix
  have hS : ∑ j, gs (thetaComplete N) dbar v ω j ≤
      ((univ.filter (fun j => ω j = true)).card : ℝ) * dbar +
        ((univ.filter (fun j => ¬ ω j = true)).card : ℝ) * gs (thetaComplete N) dbar v ω k1 := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun j => ω j = true)]
    have h1 : ∑ j ∈ univ.filter (fun j => ω j = true), gs (thetaComplete N) dbar v ω j =
        ((univ.filter (fun j => ω j = true)).card : ℝ) * dbar := by
      rw [Finset.sum_congr rfl fun j hj => gs_succ hθ hv hdb ω j (by simpa using hj),
        Finset.sum_const, nsmul_eq_mul]
    have h2 : ∑ j ∈ univ.filter (fun j => ¬ ω j = true), gs (thetaComplete N) dbar v ω j ≤
        ((univ.filter (fun j => ¬ ω j = true)).card : ℝ) * gs (thetaComplete N) dbar v ω k1 := by
      have := Finset.sum_le_sum fun j (hj : j ∈ univ.filter (fun j => ¬ ω j = true)) =>
        hk1max j hj
      simpa [Finset.sum_const, nsmul_eq_mul] using this
    linarith
  have h3 := hMeq
  rw [eq_sub_iff_add_eq, eq_div_iff (by linarith)] at h3
  have h5 : gs (thetaComplete N) dbar v ω k1 * (N : ℝ) =
      gs (thetaComplete N) dbar v ω k1 * ((univ.filter (fun j => ω j = true)).card : ℝ) +
      gs (thetaComplete N) dbar v ω k1 *
        ((univ.filter (fun j => ¬ ω j = true)).card : ℝ) := by
    rw [← hsfR]; ring
  have h6 : v * (N : ℝ) = v * ((univ.filter (fun j => ω j = true)).card : ℝ) +
      v * ((univ.filter (fun j => ¬ ω j = true)).card : ℝ) := by
    rw [← hsfR]; ring
  have h4 : ((univ.filter (fun j => ω j = true)).card : ℝ) * gs (thetaComplete N) dbar v ω k1 ≤
      ((univ.filter (fun j => ω j = true)).card : ℝ) * dbar - ((N : ℝ) - 1) * v := by
    nlinarith [h3, hS, h5, h6]
  have h7 : ((N : ℝ) - 1) * v / ((univ.filter (fun j => ω j = true)).card : ℝ) ≤
      dbar - gs (thetaComplete N) dbar v ω k1 := by
    rw [div_le_iff₀ hspos]
    nlinarith [h4]
  have h8 := le_max_left (dbar - ((N : ℝ) - 1) * v /
    ((univ.filter (fun j => ω j = true)).card : ℝ)) 0
  linarith

lemma gC_ge (hN : 2 ≤ N) {dbar v : ℝ} (hv : 0 < v) (hdb : 0 ≤ dbar) (i : Fin N) (t : ℕ)
    (ω : Fin N → Bool) (hω : ω ∈ Om i t) :
    ((N - 1 - t : ℕ) : ℝ) * min (((N : ℝ) - 1) * v / ((t : ℝ) + 1)) dbar ≤
      ((N : ℝ) - 1) * (dbar - ∑ j, thetaComplete N i j * gs (thetaComplete N) dbar v ω j) := by
  simp only [Om, mem_filter, mem_univ, true_and] at hω
  obtain ⟨hωi, hcnt⟩ := hω
  have hθ := reg_complete hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hs : (univ.filter (fun j => ω j = true)).card = t + 1 := by
    have h1 : (univ.erase i).filter (fun j => ω j = true) =
        (univ.filter (fun j => ω j = true)).erase i := Finset.filter_erase _ _ _
    have h2 := Finset.card_erase_of_mem (s := univ.filter (fun j => ω j = true)) (a := i)
      (by simp [hωi])
    unfold cnt at hcnt
    rw [h1, h2] at hcnt
    have : 0 < (univ.filter (fun j => ω j = true)).card := Finset.card_pos.mpr ⟨i, by simp [hωi]⟩
    omega
  have hsf : (univ.filter (fun j => ω j = true)).card +
      (univ.filter (fun j => ¬ ω j = true)).card = N := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin N)))
      (fun j => ω j = true)
    simpa [card_univ, Fintype.card_fin] using this
  set x := max (dbar - ((N : ℝ) - 1) * v / ((univ.filter (fun j => ω j = true)).card : ℝ)) 0
    with hx
  have hS : ∑ j, gs (thetaComplete N) dbar v ω j ≤
      ((univ.filter (fun j => ω j = true)).card : ℝ) * dbar +
        ((univ.filter (fun j => ¬ ω j = true)).card : ℝ) * x := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun j => ω j = true)]
    have h1 : ∑ j ∈ univ.filter (fun j => ω j = true), gs (thetaComplete N) dbar v ω j =
        ((univ.filter (fun j => ω j = true)).card : ℝ) * dbar := by
      rw [Finset.sum_congr rfl fun j hj => gs_succ hθ hv hdb ω j (by simpa using hj),
        Finset.sum_const, nsmul_eq_mul]
    have h2 : ∑ j ∈ univ.filter (fun j => ¬ ω j = true), gs (thetaComplete N) dbar v ω j ≤
        ((univ.filter (fun j => ¬ ω j = true)).card : ℝ) * x := by
      have := Finset.sum_le_sum fun j (hj : j ∈ univ.filter (fun j => ¬ ω j = true)) =>
        complete_fail_le hN hv hdb ω i hωi j (by simpa using hj)
      simpa [Finset.sum_const, nsmul_eq_mul] using this
    linarith
  rw [complete_sum hN, gs_succ hθ hv hdb ω i hωi]
  have hNt : ((N - 1 - t : ℕ) : ℝ) = ((univ.filter (fun j => ¬ ω j = true)).card : ℝ) := by
    have : N - 1 - t = (univ.filter (fun j => ¬ ω j = true)).card := by omega
    rw [this]
  have hmin : min (((N : ℝ) - 1) * v / ((t : ℝ) + 1)) dbar = dbar - x := by
    have : ((t : ℝ) + 1) = ((univ.filter (fun j => ω j = true)).card : ℝ) := by
      rw [hs]; push_cast; ring
    rw [this, hx]
    rcases le_total (dbar - ((N : ℝ) - 1) * v /
        ((univ.filter (fun j => ω j = true)).card : ℝ)) 0 with h | h
    · rw [max_eq_right h, min_eq_right (by linarith)]; ring
    · rw [max_eq_left h, min_eq_left (by linarith)]; ring
  rw [hNt, hmin]
  have hsfR : ((univ.filter (fun j => ω j = true)).card : ℝ) +
      ((univ.filter (fun j => ¬ ω j = true)).card : ℝ) = N := by exact_mod_cast hsf
  have e : ((N : ℝ) - 1) * ((∑ j, gs (thetaComplete N) dbar v ω j - dbar) / ((N : ℝ) - 1)) =
      ∑ j, gs (thetaComplete N) dbar v ω j - dbar := by
    field_simp
  rw [mul_sub ((N : ℝ) - 1), e]
  have h6 : dbar * (N : ℝ) = dbar * ((univ.filter (fun j => ω j = true)).card : ℝ) +
      dbar * ((univ.filter (fun j => ¬ ω j = true)).card : ℝ) := by
    rw [← hsfR]; ring
  nlinarith [hS, h6]

theorem ring_le_complete (hN : 2 ≤ N) {dbar v : ℝ} (hv : 0 < v) (hdb : 0 ≤ dbar)
    {P : ℝ → ℝ} {Zlo Zhi : ℝ} (hnd : v + dbar ≤ Zlo)
    (hP01 : ∀ z ∈ Set.Icc Zlo Zhi, 0 < P z ∧ P z < 1)
    (z : ℝ) (hz : z ∈ Set.Icc Zlo Zhi) (i : Fin N) :
    distortion (thetaRing N) dbar v P (fun _ => z) i ≤
      distortion (thetaComplete N) dbar v P (fun _ => z) i := by
  have hZ : ∀ j : Fin N, v + dbar ≤ (fun _ => z) j := fun _ => le_trans hnd hz.1
  rw [distortion_eq (reg_ring hN) hv hdb P hZ i, distortion_eq (reg_complete hN) hv hdb P hZ i]
  have hp : ∀ j : Fin N, (fun j => P ((fun _ => z) j)) j = P z := fun _ => rfl
  rw [decomp (by omega) i hp, decomp (by omega) i hp]
  refine Finset.sum_le_sum fun t _ => ?_
  have hq := hP01 z hz
  have ha : 0 ≤ P z ^ t * (1 - P z) ^ (N - 1 - t) :=
    mul_nonneg (pow_nonneg hq.1.le _) (pow_nonneg (by linarith [hq.2]) _)
  apply mul_le_mul_of_nonneg_left _ ha
  simp only [ring_sum]
  have hN1 : (1 : ℝ) ≤ (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hR := ring_Om_bound hN hv hdb i t
  -- complete side
  have hC : ((N - 1).choose t : ℝ) * (((N - 1 - t : ℕ) : ℝ) *
      min (((N : ℝ) - 1) * v / ((t : ℝ) + 1)) dbar) ≤
      ((N : ℝ) - 1) * ∑ ω ∈ Om i t,
        (dbar - ∑ j, thetaComplete N i j * gs (thetaComplete N) dbar v ω j) := by
    rw [Finset.mul_sum]
    have := Finset.sum_le_sum fun ω (hω : ω ∈ Om i t) => gC_ge hN hv hdb i t ω hω
    rw [Finset.sum_const, card_Om, nsmul_eq_mul] at this
    exact this
  -- binomial identities
  have hA : (((N - 1).choose (t + 1) : ℕ) : ℝ) * ((t : ℝ) + 1) =
      ((N - 1).choose t : ℝ) * ((N - 1 - t : ℕ) : ℝ) := by
    have := Nat.choose_succ_right_eq (N - 1) t
    exact_mod_cast this
  have hB : (((N - 2).choose t : ℕ) : ℝ) * ((N : ℝ) - 1) =
      ((N - 1).choose t : ℝ) * ((N - 1 - t : ℕ) : ℝ) := by
    have h := Nat.choose_mul_succ_eq (N - 2) t
    have e : N - 2 + 1 = N - 1 := by omega
    rw [e] at h
    have e2 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [← e2]
    exact_mod_cast h
  have hkey : ((N : ℝ) - 1) * ∑ ω ∈ Om i t, (dbar - gs (thetaRing N) dbar v ω (bpos i 0)) ≤
      ((N - 1).choose t : ℝ) * (((N - 1 - t : ℕ) : ℝ) *
        min (((N : ℝ) - 1) * v / ((t : ℝ) + 1)) dbar) := by
    have ht1 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
    rcases min_cases (((N : ℝ) - 1) * v / ((t : ℝ) + 1)) dbar with ⟨hm, _⟩ | ⟨hm, _⟩
    · rw [hm]
      have e3 : ((N - 1).choose t : ℝ) * (((N - 1 - t : ℕ) : ℝ) *
          (((N : ℝ) - 1) * v / ((t : ℝ) + 1))) =
          ((N : ℝ) - 1) * (v * (((N - 1).choose (t + 1) : ℕ) : ℝ)) := by
        rw [← mul_assoc, ← hA]
        field_simp
      rw [e3]
      exact mul_le_mul_of_nonneg_left (le_trans hR (min_le_left _ _)) (by linarith)
    · rw [hm]
      have e3 : ((N - 1).choose t : ℝ) * (((N - 1 - t : ℕ) : ℝ) * dbar) =
          ((N : ℝ) - 1) * (dbar * (((N - 2).choose t : ℕ) : ℝ)) := by
        rw [← mul_assoc, ← hB]; ring
      rw [e3]
      exact mul_le_mul_of_nonneg_left (le_trans hR (min_le_right _ _)) (by linarith)
  have hfin := le_trans hkey hC
  exact le_of_mul_le_mul_left hfin (by linarith)

/-! ## Assembly -/

theorem main_of_RC (N : ℕ) (hN : 2 ≤ N) (dbar v : ℝ) (hdbar : 0 < dbar) (hv : 0 < v)
    (Zlo Zhi : ℝ) (hZ : Zlo ≤ Zhi) (hnd : v + dbar ≤ Zlo)
    (P : ℝ → ℝ) (hP01 : ∀ z ∈ Set.Icc Zlo Zhi, 0 < P z ∧ P z < 1)
    (hPanti : AntitoneOn P (Set.Icc Zlo Zhi))
    (hPcont : ContinuousOn P (Set.Icc Zlo Zhi))
    (ZC ZR : Fin N → ℝ)
    (hC : IsLeast {Z | IsEquilibrium (thetaComplete N) dbar v P Zlo Zhi Z} ZC)
    (hR : IsLeast {Z | IsEquilibrium (thetaRing N) dbar v P Zlo Zhi Z} ZR) :
    ∀ i, ZR i ≤ ZC i := by
  have hdb : 0 ≤ dbar := hdbar.le
  have hθR := reg_ring hN
  have hθC := reg_complete hN
  have hCbox : ∀ j, ZC j ∈ Set.Icc Zlo Zhi := fun j => (hC.1 j).1
  have hconst : ∀ i, ZC = fun _ => ZC i := fun i => funext fun j =>
    le_antisymm (complete_const hN hv hdb hnd hC j i) (complete_const hN hv hdb hnd hC i j)
  let L : Set (Fin N → ℝ) := {Z | ∀ j, Zlo ≤ Z j ∧ Z j ≤ ZC j}
  let F : (Fin N → ℝ) → (Fin N → ℝ) :=
    fun Z i => mt P Zlo Zhi (v + distortion (thetaRing N) dbar v P Z i)
  have hLbox : ∀ Z ∈ L, ∀ j, Z j ∈ Set.Icc Zlo Zhi :=
    fun Z hZL j => ⟨(hZL j).1, le_trans (hZL j).2 (hCbox j).2⟩
  have hFmono : ∀ Z ∈ L, ∀ Z' ∈ L, Z ≤ Z' → F Z ≤ F Z' := by
    intro Z hZL Z' hZL' hle i
    have := distortion_mono hθR hv hdb hnd hP01 hPanti (hLbox Z hZL) (hLbox Z' hZL') hle i
    exact mt_mono hZ hPcont hPanti (by linarith)
  have hZCL : ZC ∈ L := fun j => ⟨(hCbox j).1, le_rfl⟩
  have hFZC : F ZC ≤ ZC := by
    intro i
    have h1 : ZC i ∈ maxSet P Zlo Zhi (v + distortion (thetaComplete N) dbar v P ZC i) :=
      (br_iff hθC hv hdb hnd hCbox i (ZC i)).1 (hC.1 i)
    have h2 : distortion (thetaRing N) dbar v P ZC i ≤
        distortion (thetaComplete N) dbar v P ZC i := by
      rw [hconst i]
      exact ring_le_complete hN hv hdb hnd hP01 (ZC i) (hCbox i) i
    exact le_trans (mt_mono hZ hPcont hPanti (by linarith)) (mt_le h1)
  have hFL : ∀ Z ∈ L, F Z ∈ L := by
    intro Z hZL j
    exact ⟨(mt_mem hZ hPcont _).1.1,
      le_trans (hFmono Z hZL ZC hZCL (fun k => (hZL k).2) j) (hFZC j)⟩
  let S : Set (Fin N → ℝ) := {Z | Z ∈ L ∧ F Z ≤ Z}
  have hSne : S.Nonempty := ⟨ZC, hZCL, hFZC⟩
  have hSbdd : BddBelow S := ⟨fun _ => Zlo, fun Z hZ j => (hZ.1 j).1⟩
  have hZsle : ∀ Z ∈ S, sInf S ≤ Z := fun Z hZ => csInf_le hSbdd hZ
  have hZsL : sInf S ∈ L := by
    have h1 : (fun _ => Zlo) ≤ sInf S := le_csInf hSne fun Z hZ j => (hZ.1 j).1
    exact fun j => ⟨h1 j, hZsle ZC ⟨hZCL, hFZC⟩ j⟩
  have hFZs : F (sInf S) ≤ sInf S :=
    le_csInf hSne fun Z hZ => le_trans (hFmono _ hZsL Z hZ.1 (hZsle Z hZ)) hZ.2
  have hfix : F (sInf S) = sInf S :=
    le_antisymm hFZs (hZsle _ ⟨hFL _ hZsL, hFmono _ (hFL _ hZsL) _ hZsL hFZs⟩)
  have heq : IsEquilibrium (thetaRing N) dbar v P Zlo Zhi (sInf S) := by
    intro i
    rw [br_iff hθR hv hdb hnd (hLbox _ hZsL) i]
    have hm := mt_mem (P := P) hZ hPcont (v + distortion (thetaRing N) dbar v P (sInf S) i)
    have e : F (sInf S) i = sInf S i := congrFun hfix i
    rw [← e]
    exact hm
  intro i
  exact le_trans (hR.2 heq i) (hZsL i).2

end RiskExposure.RingComplete.P4X

open RiskExposure.RingComplete in
theorem solution (N : ℕ) (hN : 2 ≤ N) (dbar v : ℝ) (hdbar : 0 < dbar) (hv : 0 < v)
    (Zlo Zhi : ℝ) (hZ : Zlo ≤ Zhi) (hnd : v + dbar ≤ Zlo)
    (P : ℝ → ℝ) (hP01 : ∀ z ∈ Set.Icc Zlo Zhi, 0 < P z ∧ P z < 1)
    (hPanti : AntitoneOn P (Set.Icc Zlo Zhi))
    (hPconc : ConcaveOn ℝ (Set.Icc Zlo Zhi) (fun z => P z * z))
    (hPcont : ContinuousOn P (Set.Icc Zlo Zhi))
    (ZC ZR : Fin N → ℝ)
    (hC : IsLeast {Z | IsEquilibrium (thetaComplete N) dbar v P Zlo Zhi Z} ZC)
    (hR : IsLeast {Z | IsEquilibrium (thetaRing N) dbar v P Zlo Zhi Z} ZR) :
    ∀ i, ZR i ≤ ZC i := by
  exact RiskExposure.RingComplete.P4X.main_of_RC N hN dbar v hdbar hv Zlo Zhi hZ hnd P hP01
    hPanti hPcont ZC ZR hC hR
