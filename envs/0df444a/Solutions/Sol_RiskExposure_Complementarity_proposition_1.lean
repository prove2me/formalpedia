-- Prove2me | solution 1 for RiskExposure.Complementarity.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-14T19:53:14.159907+00:00
-- url     : https://prove2.me/submissions/c1d3db44-e029-4142-b3d1-bbe4cbb458b8

import Definitions.Def_RiskExposure_Complementarity_Model

set_option linter.unusedSectionVars false

namespace RiskExposure.Complementarity

open Finset

section aux
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma theta_nonneg' (dbar : ι → ι → ℝ) (hdbar : ∀ i j, 0 ≤ dbar i j)
    (hdbarTot : ∀ j, 0 < dbarTot dbar j) (i j : ι) : 0 ≤ theta dbar i j :=
  div_nonneg (hdbar i j) (hdbarTot j).le

lemma clear_box (dbar : ι → ι → ℝ) (hdbarTot : ∀ j, 0 < dbarTot dbar j) (v : ι → ℝ)
    (ω : ι → Bool) (Z d : ι → ℝ) (j : ι) :
    0 ≤ clearingMap dbar v ω Z d j ∧ clearingMap dbar v ω Z d j ≤ dbarTot dbar j :=
  ⟨le_max_right _ _, max_le (min_le_right _ _) (hdbarTot j).le⟩

lemma clear_mono (dbar : ι → ι → ℝ) (hdbar : ∀ i j, 0 ≤ dbar i j)
    (hdbarTot : ∀ j, 0 < dbarTot dbar j) (v : ι → ℝ)
    (ω : ι → Bool) (Z d d' : ι → ℝ) (h : d ≤ d') (j : ι) :
    clearingMap dbar v ω Z d j ≤ clearingMap dbar v ω Z d' j := by
  unfold clearingMap
  have : ∑ k, theta dbar j k * d k ≤ ∑ k, theta dbar j k * d' k :=
    Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_left (h k) (theta_nonneg' dbar hdbar hdbarTot j k)
  exact max_le_max (min_le_min (by linarith) le_rfl) le_rfl

lemma pe_spec (dbar : ι → ι → ℝ) (hdbar : ∀ i j, 0 ≤ dbar i j)
    (hdbarTot : ∀ j, 0 < dbarTot dbar j) (v : ι → ℝ) (ω : ι → Bool) (Z : ι → ℝ) :
    (∀ j, 0 ≤ paymentEq dbar v ω Z j ∧ paymentEq dbar v ω Z j ≤ dbarTot dbar j) ∧
    IsPaymentEq dbar v ω Z (paymentEq dbar v ω Z) ∧
    ∀ d : ι → ℝ, (∀ j, 0 ≤ d j ∧ d j ≤ dbarTot dbar j) →
      (∀ j, d j ≤ clearingMap dbar v ω Z d j) → d ≤ paymentEq dbar v ω Z := by
  let T : (ι → ℝ) → (ι → ℝ) := fun d j => clearingMap dbar v ω Z d j
  have Tmono : ∀ d d' : ι → ℝ, d ≤ d' → T d ≤ T d' := fun d d' h j =>
    clear_mono dbar hdbar hdbarTot v ω Z d d' h j
  let Post : Set (ι → ℝ) := {d | (∀ j, 0 ≤ d j ∧ d j ≤ dbarTot dbar j) ∧ d ≤ T d}
  have hB : BddAbove Post := ⟨fun j => dbarTot dbar j, fun d hd j => (hd.1 j).2⟩
  have h0 : (0 : ι → ℝ) ∈ Post :=
    ⟨fun j => ⟨le_rfl, (hdbarTot j).le⟩, fun j => (clear_box dbar hdbarTot v ω Z 0 j).1⟩
  let g := sSup Post
  have g_ge : ∀ d ∈ Post, d ≤ g := fun d hd => le_csSup hB hd
  have g_le_T : g ≤ T g :=
    csSup_le ⟨0, h0⟩ fun d hd => le_trans hd.2 (Tmono _ _ (g_ge d hd))
  have Tg_mem : T g ∈ Post :=
    ⟨fun j => clear_box dbar hdbarTot v ω Z g j, Tmono _ _ g_le_T⟩
  have hfix : T g = g := le_antisymm (g_ge _ Tg_mem) g_le_T
  have gbox : ∀ j, 0 ≤ g j ∧ g j ≤ dbarTot dbar j := by
    intro j
    rw [← hfix]
    exact clear_box dbar hdbarTot v ω Z g j
  have hSol_sub : {d : ι → ℝ | (∀ i, 0 ≤ d i ∧ d i ≤ dbarTot dbar i) ∧
      IsPaymentEq dbar v ω Z d} ⊆ Post := by
    intro d hd
    exact ⟨hd.1, fun j => le_of_eq (hd.2 j)⟩
  have gSol : g ∈ {d : ι → ℝ | (∀ i, 0 ≤ d i ∧ d i ≤ dbarTot dbar i) ∧
      IsPaymentEq dbar v ω Z d} :=
    ⟨gbox, fun j => (congrFun hfix j).symm⟩
  have hpe : paymentEq dbar v ω Z = g := by
    unfold paymentEq
    apply le_antisymm
    · exact csSup_le ⟨g, gSol⟩ fun d hd => g_ge d (hSol_sub hd)
    · exact le_csSup (hB.mono hSol_sub) gSol
  rw [hpe]
  exact ⟨gbox, gSol.2, fun d hd hdT => g_ge d ⟨hd, hdT⟩⟩

lemma clear_eq (dbar : ι → ι → ℝ) (hdbar : ∀ i j, 0 ≤ dbar i j)
    (hdbarTot : ∀ j, 0 < dbarTot dbar j) (v : ι → ℝ) (ω : ι → Bool) (Z : ι → ℝ)
    (hZ : ∀ j, v j + dbarTot dbar j ≤ Z j) (d : ι → ℝ) (hd : ∀ j, 0 ≤ d j) (j : ι) :
    clearingMap dbar v ω Z d j = if ω j = true then dbarTot dbar j
      else max (min (∑ k, theta dbar j k * d k - v j) (dbarTot dbar j)) 0 := by
  have hs : 0 ≤ ∑ k, theta dbar j k * d k :=
    Finset.sum_nonneg fun k _ => mul_nonneg (theta_nonneg' dbar hdbar hdbarTot j k) (hd k)
  unfold clearingMap cash
  by_cases h : ω j = true
  · rw [if_pos h, if_pos h, min_eq_right (by linarith [hZ j]), max_eq_left (hdbarTot j).le]
  · rw [if_neg h, if_neg h, add_zero]

lemma pe_indep (dbar : ι → ι → ℝ) (hdbar : ∀ i j, 0 ≤ dbar i j)
    (hdbarTot : ∀ j, 0 < dbarTot dbar j) (v : ι → ℝ) (ω : ι → Bool) (Z Z' : ι → ℝ)
    (hZ : ∀ j, v j + dbarTot dbar j ≤ Z j) (hZ' : ∀ j, v j + dbarTot dbar j ≤ Z' j) :
    paymentEq dbar v ω Z = paymentEq dbar v ω Z' := by
  unfold paymentEq
  congr 1
  ext d
  simp only [Set.mem_setOf_eq, IsPaymentEq]
  constructor
  · rintro ⟨hb, hp⟩
    refine ⟨hb, fun j => (hp j).trans ?_⟩
    rw [clear_eq dbar hdbar hdbarTot v ω Z hZ d (fun k => (hb k).1),
      clear_eq dbar hdbar hdbarTot v ω Z' hZ' d (fun k => (hb k).1)]
  · rintro ⟨hb, hp⟩
    refine ⟨hb, fun j => (hp j).trans ?_⟩
    rw [clear_eq dbar hdbar hdbarTot v ω Z hZ d (fun k => (hb k).1),
      clear_eq dbar hdbar hdbarTot v ω Z' hZ' d (fun k => (hb k).1)]

lemma pe_mono (dbar : ι → ι → ℝ) (hdbar : ∀ i j, 0 ≤ dbar i j)
    (hdbarTot : ∀ j, 0 < dbarTot dbar j) (v : ι → ℝ) (ω ω' : ι → Bool) (Z : ι → ℝ)
    (hZ : ∀ j, v j + dbarTot dbar j ≤ Z j) (h : ∀ j, ω j = true → ω' j = true) :
    paymentEq dbar v ω Z ≤ paymentEq dbar v ω' Z := by
  obtain ⟨hb, hfix, _⟩ := pe_spec dbar hdbar hdbarTot v ω Z
  obtain ⟨_, _, hmax⟩ := pe_spec dbar hdbar hdbarTot v ω' Z
  have hd : ∀ k, 0 ≤ paymentEq dbar v ω Z k := fun k => (hb k).1
  apply hmax _ hb
  intro j
  rw [hfix j, clear_eq dbar hdbar hdbarTot v ω Z hZ _ hd,
    clear_eq dbar hdbar hdbarTot v ω' Z hZ _ hd]
  by_cases h1 : ω j = true
  · rw [if_pos h1, if_pos (h j h1)]
  · rw [if_neg h1]
    by_cases h2 : ω' j = true
    · rw [if_pos h2]
      exact max_le (min_le_right _ _) (hdbarTot j).le
    · rw [if_neg h2]

noncomputable def Rv (dbar : ι → ι → ℝ) (v : ι → ℝ) (Z : ι → ℝ) (i : ι) (ω : ι → Bool) : ℝ :=
  ∑ j, theta dbar i j * paymentEq dbar v ω Z j

noncomputable def Gv (dbar : ι → ι → ℝ) (v : ι → ℝ) (Z : ι → ℝ) (i : ι) (ω : ι → Bool) : ℝ :=
  max (Rv dbar v Z i ω - v i - paymentEq dbar v ω Z i) 0

def tau (P : ℝ → ℝ) (Z : ι → ℝ) (i m : ι) (ω : ι → Bool) : ℝ :=
  ∏ j ∈ (univ.erase i).erase m, (if ω j = true then P (Z j) else 1 - P (Z j))

noncomputable def uv (dbar : ι → ι → ℝ) (v : ι → ℝ) (P : ℝ → ℝ) (Z : ι → ℝ) (i : ι) (y : ℝ)
    (ω : ι → Bool) : ℝ :=
  (if ω i = true then Rv dbar v Z i ω - (v i + dbarTot dbar i) + y else Gv dbar v Z i ω) *
    (if ω i = true then P y else 1 - P y)

lemma Rv_mono (dbar : ι → ι → ℝ) (hdbar : ∀ i j, 0 ≤ dbar i j)
    (hdbarTot : ∀ j, 0 < dbarTot dbar j) (v : ι → ℝ) (ω ω' : ι → Bool) (Z : ι → ℝ)
    (hZ : ∀ j, v j + dbarTot dbar j ≤ Z j) (h : ∀ j, ω j = true → ω' j = true) (i : ι) :
    Rv dbar v Z i ω ≤ Rv dbar v Z i ω' := by
  unfold Rv
  have := pe_mono dbar hdbar hdbarTot v ω ω' Z hZ h
  exact Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_left (this k) (theta_nonneg' dbar hdbar hdbarTot i k)

lemma Rv_fail_ge (dbar : ι → ι → ℝ) (hdbar : ∀ i j, 0 ≤ dbar i j)
    (hdbarTot : ∀ j, 0 < dbarTot dbar j) (v : ι → ℝ) (ω : ι → Bool) (Z : ι → ℝ)
    (hZ : ∀ j, v j + dbarTot dbar j ≤ Z j) (i : ι) (hω : ω i = true)
    (hR : v i + dbarTot dbar i ≤ Rv dbar v Z i ω) :
    Rv dbar v Z i ω ≤ Rv dbar v Z i (Function.update ω i false) := by
  obtain ⟨hb, hfix, _⟩ := pe_spec dbar hdbar hdbarTot v ω Z
  obtain ⟨_, _, hmax⟩ := pe_spec dbar hdbar hdbarTot v (Function.update ω i false) Z
  have hd : ∀ k, 0 ≤ paymentEq dbar v ω Z k := fun k => (hb k).1
  have hle : paymentEq dbar v ω Z ≤ paymentEq dbar v (Function.update ω i false) Z := by
    apply hmax _ hb
    intro j
    rw [clear_eq dbar hdbar hdbarTot v (Function.update ω i false) Z hZ _ hd]
    by_cases hj : j = i
    · rw [hj, Function.update_self, if_neg (by simp)]
      have : paymentEq dbar v ω Z i = dbarTot dbar i := by
        rw [hfix i, clear_eq dbar hdbar hdbarTot v ω Z hZ _ hd, if_pos hω]
      unfold Rv at hR
      rw [this, min_eq_right (by linarith), max_eq_left (hdbarTot i).le]
    · rw [Function.update_of_ne hj]
      exact le_of_eq ((hfix j).trans (clear_eq dbar hdbar hdbarTot v ω Z hZ _ hd j))
  unfold Rv
  exact Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_left (hle k) (theta_nonneg' dbar hdbar hdbarTot i k)

lemma Gv_formula (dbar : ι → ι → ℝ) (hdbar : ∀ i j, 0 ≤ dbar i j)
    (hdbarTot : ∀ j, 0 < dbarTot dbar j) (v : ι → ℝ) (ω : ι → Bool) (Z : ι → ℝ)
    (hZ : ∀ j, v j + dbarTot dbar j ≤ Z j) (i : ι) (hω : ω i = false) :
    Gv dbar v Z i ω = max (Rv dbar v Z i ω - (v i + dbarTot dbar i)) 0 := by
  obtain ⟨hb, hfix, _⟩ := pe_spec dbar hdbar hdbarTot v ω Z
  have hQ := (hfix i).trans
    (clear_eq dbar hdbar hdbarTot v ω Z hZ _ (fun k => (hb k).1) i)
  rw [if_neg (by simp [hω])] at hQ
  unfold Gv
  rw [hQ]
  unfold Rv
  generalize (∑ k, theta dbar i k * paymentEq dbar v ω Z k) = R
  have := (hdbarTot i).le
  simp only [max_def, min_def]
  split_ifs <;> linarith

lemma profit_eq (dbar : ι → ι → ℝ) (hdbar : ∀ i j, 0 ≤ dbar i j)
    (hdbarTot : ∀ j, 0 < dbarTot dbar j) (v : ι → ℝ) (Zlo : ℝ)
    (hnd : ∀ j, v j + dbarTot dbar j ≤ Zlo) (W Z0 : ι → ℝ) (hW : ∀ j, Zlo ≤ W j)
    (hZ0 : ∀ j, Zlo ≤ Z0 j) (y : ℝ) (hy : Zlo ≤ y) (ω : ι → Bool) (i : ι) :
    profit dbar v ω (Function.update W i y) i =
      if ω i = true then Rv dbar v Z0 i ω - (v i + dbarTot dbar i) + y
      else Gv dbar v Z0 i ω := by
  have hWy : ∀ j, v j + dbarTot dbar j ≤ Function.update W i y j := by
    intro j
    by_cases hj : j = i
    · rw [hj, Function.update_self]; linarith [hnd i]
    · rw [Function.update_of_ne hj]; linarith [hnd j, hW j]
  have hZ0' : ∀ j, v j + dbarTot dbar j ≤ Z0 j := fun j => by linarith [hnd j, hZ0 j]
  have hpe := pe_indep dbar hdbar hdbarTot v ω (Function.update W i y) Z0 hWy hZ0'
  unfold profit cash
  rw [hpe, Function.update_self]
  unfold Gv Rv
  by_cases hω : ω i = true
  · rw [if_pos hω, if_pos hω]
    obtain ⟨hb, hfix, _⟩ := pe_spec dbar hdbar hdbarTot v ω Z0
    have hQ : paymentEq dbar v ω Z0 i = dbarTot dbar i := by
      rw [hfix i, clear_eq dbar hdbar hdbarTot v ω Z0 hZ0' _ (fun k => (hb k).1), if_pos hω]
    have hs : 0 ≤ ∑ k, theta dbar i k * paymentEq dbar v ω Z0 k :=
      Finset.sum_nonneg fun k _ =>
        mul_nonneg (theta_nonneg' dbar hdbar hdbarTot i k) (hb k).1
    rw [hQ, max_eq_left (by linarith [hnd i])]
    ring
  · rw [if_neg hω, if_neg hω, add_zero]

lemma sp_eq (P : ℝ → ℝ) (Z W : ι → ℝ) (i m : ι) (hmi : m ≠ i)
    (hW : ∀ j, j ≠ m → W j = Z j) (y : ℝ) (ω : ι → Bool) :
    stateProb P (Function.update W i y) ω = (if ω i = true then P y else 1 - P y) *
      ((if ω m = true then P (W m) else 1 - P (W m)) * tau P Z i m ω) := by
  unfold stateProb tau
  rw [← Finset.mul_prod_erase univ _ (mem_univ i), Function.update_self,
    ← Finset.mul_prod_erase (univ.erase i) _ (mem_erase.2 ⟨hmi, mem_univ m⟩),
    Function.update_of_ne hmi]
  congr 2
  apply Finset.prod_congr rfl
  intro j hj
  have hjm : j ≠ m := (mem_erase.1 hj).1
  have hji : j ≠ i := (mem_erase.1 (mem_erase.1 hj).2).1
  rw [Function.update_of_ne hji, hW j hjm]

lemma tau_upd (P : ℝ → ℝ) (Z : ι → ℝ) (i m k : ι) (hk : k = i ∨ k = m) (b : Bool)
    (ω : ι → Bool) : tau P Z i m (Function.update ω k b) = tau P Z i m ω := by
  unfold tau
  apply Finset.prod_congr rfl
  intro j hj
  have hjm : j ≠ m := (mem_erase.1 hj).1
  have hji : j ≠ i := (mem_erase.1 (mem_erase.1 hj).2).1
  have hjk : j ≠ k := by rcases hk with rfl | rfl <;> assumption
  rw [Function.update_of_ne hjk]

lemma tau_nonneg (P : ℝ → ℝ) (Z : ι → ℝ) (hP : ∀ j, 0 ≤ P (Z j) ∧ P (Z j) ≤ 1) (i m : ι)
    (ω : ι → Bool) : 0 ≤ tau P Z i m ω := by
  unfold tau
  apply Finset.prod_nonneg
  intro j _
  split_ifs
  · exact (hP j).1
  · linarith [(hP j).2]

lemma sum_pair (X : (ι → Bool) → ℝ) (k : ι) :
    ∑ ω, X ω = ∑ ω, (if ω k = true then X ω + X (Function.update ω k false) else 0) := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_add_distrib]
  conv_lhs => rw [← Finset.sum_filter_add_sum_filter_not univ (fun ω : ι → Bool => ω k = true)]
  congr 1
  symm
  apply Finset.sum_nbij' (fun ω => Function.update ω k false) (fun ω => Function.update ω k true)
  · intro a _; simp
  · intro a _; simp
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    rw [Function.update_idem]
    exact Function.update_eq_self_iff.2 ha.symm
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    rw [Function.update_idem]
    exact Function.update_eq_self_iff.2 (by simpa using ha)
  · intro a _; rfl

lemma upd_false_le (ω : ι → Bool) (k : ι) :
    ∀ j, Function.update ω k false j = true → ω j = true := by
  intro j h
  by_cases hj : j = k
  · rw [hj, Function.update_self] at h; exact absurd h (by simp)
  · rwa [Function.update_of_ne hj] at h

lemma key_ineq (dbar : ι → ι → ℝ) (hdbar : ∀ i j, 0 ≤ dbar i j)
    (hdbarTot : ∀ j, 0 < dbarTot dbar j) (v : ι → ℝ) (Z : ι → ℝ)
    (hZ : ∀ j, v j + dbarTot dbar j ≤ Z j) (i m : ι) (hmi : m ≠ i) (ω : ι → Bool)
    (hi : ω i = true) (hm : ω m = true) :
    0 ≤ Rv dbar v Z i ω - Rv dbar v Z i (Function.update ω m false)
      - Gv dbar v Z i (Function.update ω i false)
      + Gv dbar v Z i (Function.update (Function.update ω i false) m false) := by
  have hfs_i : Function.update ω i false i = false := Function.update_self _ _ _
  have hff_i : Function.update (Function.update ω i false) m false i = false := by
    rw [Function.update_of_ne hmi.symm, Function.update_self]
  have hsf_i : Function.update ω m false i = true := by
    rw [Function.update_of_ne hmi.symm]; exact hi
  have hGfs := Gv_formula dbar hdbar hdbarTot v _ Z hZ i hfs_i
  have hGff := Gv_formula dbar hdbar hdbarTot v _ Z hZ i hff_i
  have m1 := Rv_mono dbar hdbar hdbarTot v _ _ Z hZ
    (upd_false_le (Function.update ω i false) m) i
  have m2 := Rv_mono dbar hdbar hdbarTot v _ _ Z hZ (upd_false_le ω m) i
  have m3 := Rv_mono dbar hdbar hdbarTot v _ _ Z hZ (upd_false_le ω i) i
  have e1 := fun h => Rv_fail_ge dbar hdbar hdbarTot v ω Z hZ i hi h
  have hcomm : Function.update (Function.update ω m false) i false =
      Function.update (Function.update ω i false) m false :=
    (Function.update_comm hmi.symm _ _ _).symm
  have e2 : v i + dbarTot dbar i ≤ Rv dbar v Z i (Function.update ω m false) →
      Rv dbar v Z i (Function.update ω m false) ≤
        Rv dbar v Z i (Function.update (Function.update ω i false) m false) := by
    intro h
    have := Rv_fail_ge dbar hdbar hdbarTot v _ Z hZ i hsf_i h
    rwa [hcomm] at this
  rw [hGfs, hGff]
  have g1 := le_max_left
    (Rv dbar v Z i (Function.update (Function.update ω i false) m false) -
      (v i + dbarTot dbar i)) 0
  have g2 := le_max_right
    (Rv dbar v Z i (Function.update (Function.update ω i false) m false) -
      (v i + dbarTot dbar i)) 0
  rcases max_cases (Rv dbar v Z i (Function.update ω i false) - (v i + dbarTot dbar i)) 0
    with ⟨h, h'⟩ | ⟨h, h'⟩
  · rw [h]
    have := e1 (by linarith)
    by_cases hb : v i + dbarTot dbar i ≤ Rv dbar v Z i (Function.update ω m false)
    · have := e2 hb; linarith
    · linarith
  · rw [h]; linarith

lemma psi_mono (dbar : ι → ι → ℝ) (hdbar : ∀ i j, 0 ≤ dbar i j)
    (hdbarTot : ∀ j, 0 < dbarTot dbar j) (v : ι → ℝ) (P : ℝ → ℝ) (Z : ι → ℝ)
    (hZ : ∀ j, v j + dbarTot dbar j ≤ Z j) (hP : ∀ j, 0 ≤ P (Z j) ∧ P (Z j) ≤ 1)
    (i m : ι) (hmi : m ≠ i) (y1 y2 : ℝ) (hP12 : P y2 ≤ P y1) :
    ∑ ω, uv dbar v P Z i y2 ω * ((if ω m = true then 1 else -1) * tau P Z i m ω) ≤
      ∑ ω, uv dbar v P Z i y1 ω * ((if ω m = true then 1 else -1) * tau P Z i m ω) := by
  rw [← sub_nonpos, ← Finset.sum_sub_distrib]
  rw [sum_pair _ m, sum_pair _ i]
  apply Finset.sum_nonpos
  intro ω _
  by_cases hi : ω i = true
  · rw [if_pos hi]
    have hfm : Function.update ω i false m = ω m := Function.update_of_ne hmi _ _
    rw [hfm]
    by_cases hm : ω m = true
    · rw [if_pos hm]
      have hK := key_ineq dbar hdbar hdbarTot v Z hZ i m hmi ω hi hm
      have ht := tau_nonneg P Z hP i m ω
      have hE := mul_nonneg (mul_nonneg ht hK) (sub_nonneg.2 hP12)
      simp only [uv, tau_upd P Z i m m (Or.inr rfl), tau_upd P Z i m i (Or.inl rfl),
        Function.update_self, Function.update_of_ne hmi, Function.update_of_ne hmi.symm,
        hi, hm, if_true, if_false, Bool.false_eq_true] at hE ⊢
      nlinarith [hE]
    · rw [if_neg hm, if_neg hm, add_zero]
  · rw [if_neg hi]

end aux

theorem proposition_1 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (dbar : ι → ι → ℝ) (hdbar : ∀ i j, 0 ≤ dbar i j) (hdbarTot : ∀ j, 0 < dbarTot dbar j)
    (v : ι → ℝ) (hv : ∀ i, 0 < v i)
    (Zlo Zhi : ℝ) (hZ : Zlo ≤ Zhi) (hnd : ∀ i, v i + dbarTot dbar i ≤ Zlo)
    (P : ℝ → ℝ) (hP01 : ∀ z ∈ Set.Icc Zlo Zhi, 0 < P z ∧ P z < 1)
    (hPanti : AntitoneOn P (Set.Icc Zlo Zhi))
    (hPconc : ConcaveOn ℝ (Set.Icc Zlo Zhi) (fun z => P z * z))
    (i m : ι) (hmi : m ≠ i) (Z : ι → ℝ) (hZbox : ∀ j, Z j ∈ Set.Icc Zlo Zhi)
    (zm' : ℝ) (hzm' : zm' ∈ Set.Icc Zlo Zhi) (hle : Z m ≤ zm')
    (zh zh' : ℝ) (hzh : zh ∈ bestResponse dbar v P Zlo Zhi Z i)
    (hzh' : zh' ∈ bestResponse dbar v P Zlo Zhi (Function.update Z m zm') i) :
    max zh zh' ∈ bestResponse dbar v P Zlo Zhi (Function.update Z m zm') i ∧
      min zh zh' ∈ bestResponse dbar v P Zlo Zhi Z i := by
  have hZv : ∀ j, v j + dbarTot dbar j ≤ Z j := fun j => by linarith [hnd j, (hZbox j).1]
  have hPZ : ∀ j, 0 ≤ P (Z j) ∧ P (Z j) ≤ 1 := fun j =>
    ⟨(hP01 _ (hZbox j)).1.le, (hP01 _ (hZbox j)).2.le⟩
  have hf : ∀ W : ι → ℝ, (∀ j, j ≠ m → W j = Z j) → (∀ j, Zlo ≤ W j) → ∀ y, Zlo ≤ y →
      expProfit dbar v P (Function.update W i y) i =
        ∑ ω, uv dbar v P Z i y ω * ((if ω m = true then P (W m) else 1 - P (W m)) *
          tau P Z i m ω) := by
    intro W hW hWlo y hy
    unfold expProfit
    apply Finset.sum_congr rfl
    intro ω _
    rw [profit_eq dbar hdbar hdbarTot v Zlo hnd W Z hWlo (fun j => (hZbox j).1) y hy ω i,
      sp_eq P Z W i m hmi hW y ω]
    unfold uv
    ring
  have hWZ : ∀ j, j ≠ m → Z j = Z j := fun _ _ => rfl
  have hWZ' : ∀ j, j ≠ m → Function.update Z m zm' j = Z j :=
    fun j hj => Function.update_of_ne hj _ _
  have hZlo : ∀ j, Zlo ≤ Z j := fun j => (hZbox j).1
  have hZ'lo : ∀ j, Zlo ≤ Function.update Z m zm' j := by
    intro j
    by_cases hj : j = m
    · rw [hj, Function.update_self]; exact hzm'.1
    · rw [hWZ' j hj]; exact hZlo j
  have hZ'm : Function.update Z m zm' m = zm' := Function.update_self _ _ _
  have hdiff : ∀ p p' y : ℝ,
      (∑ ω, uv dbar v P Z i y ω * ((if ω m = true then p' else 1 - p') * tau P Z i m ω)) -
      (∑ ω, uv dbar v P Z i y ω * ((if ω m = true then p else 1 - p) * tau P Z i m ω)) =
      (p' - p) * ∑ ω, uv dbar v P Z i y ω *
        ((if ω m = true then 1 else -1) * tau P Z i m ω) := by
    intro p p' y
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> ring
  have hpp : P zm' ≤ P (Z m) := hPanti (hZbox m) hzm' hle
  have ID : ∀ y1 y2, y1 ∈ Set.Icc Zlo Zhi → y2 ∈ Set.Icc Zlo Zhi → y1 ≤ y2 →
      expProfit dbar v P (Function.update Z i y2) i -
        expProfit dbar v P (Function.update Z i y1) i ≤
      expProfit dbar v P (Function.update (Function.update Z m zm') i y2) i -
        expProfit dbar v P (Function.update (Function.update Z m zm') i y1) i := by
    intro y1 y2 hy1 hy2 h12
    rw [hf Z hWZ hZlo y1 hy1.1, hf Z hWZ hZlo y2 hy2.1, hf _ hWZ' hZ'lo y1 hy1.1,
      hf _ hWZ' hZ'lo y2 hy2.1, hZ'm]
    have d1 := hdiff (P (Z m)) (P zm') y1
    have d2 := hdiff (P (Z m)) (P zm') y2
    have hps := psi_mono dbar hdbar hdbarTot v P Z hZv hPZ i m hmi y1 y2
      (hPanti hy1 hy2 h12)
    nlinarith [mul_nonneg (sub_nonneg.2 hpp) (sub_nonneg.2 hps)]
  obtain ⟨hzhI, hzhmax⟩ := hzh
  obtain ⟨hzh'I, hzh'max⟩ := hzh'
  rcases le_total zh zh' with h | h
  · rw [max_eq_right h, min_eq_left h]
    exact ⟨⟨hzh'I, hzh'max⟩, ⟨hzhI, hzhmax⟩⟩
  · rw [max_eq_left h, min_eq_right h]
    have hid := ID zh' zh hzh'I hzhI h
    have a1 := hzhmax zh' hzh'I
    have a2 := hzh'max zh hzhI
    refine ⟨⟨hzhI, fun y hy => ?_⟩, ⟨hzh'I, fun y hy => ?_⟩⟩
    · have := hzh'max y hy; linarith
    · have := hzhmax y hy; linarith

end RiskExposure.Complementarity


-- Platform entry point: restates the target verbatim.
namespace RiskExposure.Complementarity

theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (dbar : ι → ι → ℝ) (hdbar : ∀ i j, 0 ≤ dbar i j) (hdbarTot : ∀ j, 0 < dbarTot dbar j)
    (v : ι → ℝ) (hv : ∀ i, 0 < v i)
    (Zlo Zhi : ℝ) (hZ : Zlo ≤ Zhi) (hnd : ∀ i, v i + dbarTot dbar i ≤ Zlo)
    (P : ℝ → ℝ) (hP01 : ∀ z ∈ Set.Icc Zlo Zhi, 0 < P z ∧ P z < 1)
    (hPanti : AntitoneOn P (Set.Icc Zlo Zhi))
    (hPconc : ConcaveOn ℝ (Set.Icc Zlo Zhi) (fun z => P z * z))
    (i m : ι) (hmi : m ≠ i) (Z : ι → ℝ) (hZbox : ∀ j, Z j ∈ Set.Icc Zlo Zhi)
    (zm' : ℝ) (hzm' : zm' ∈ Set.Icc Zlo Zhi) (hle : Z m ≤ zm')
    (zh zh' : ℝ) (hzh : zh ∈ bestResponse dbar v P Zlo Zhi Z i)
    (hzh' : zh' ∈ bestResponse dbar v P Zlo Zhi (Function.update Z m zm') i) :
    max zh zh' ∈ bestResponse dbar v P Zlo Zhi (Function.update Z m zm') i ∧
      min zh zh' ∈ bestResponse dbar v P Zlo Zhi Z i := by
  apply @RiskExposure.Complementarity.proposition_1 <;> assumption

end RiskExposure.Complementarity
