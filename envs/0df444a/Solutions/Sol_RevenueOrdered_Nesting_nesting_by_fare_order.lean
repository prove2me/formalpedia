-- Prove2me | solution 1 for RevenueOrdered.Nesting.nesting_by_fare_order
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T05:53:19.859448+00:00
-- url     : https://prove2.me/submissions/b1cd1a83-48a0-4289-a59a-926921f83411

import Mathlib
import Definitions.Def_RevenueOrdered_Nesting_DynamicProgram

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RevenueOrdered.Nesting

noncomputable section

variable {C : Type*} [Fintype C] [Nonempty C]

def p320Q (P : C → Finset C → ℝ) (r : C → ℝ) (ℓ : ℕ) : ℝ :=
  ∑ x ∈ RevenueOrdered.Ratio.roSet r ℓ, P x (RevenueOrdered.Ratio.roSet r ℓ)

def p320R (P : C → Finset C → ℝ) (r : C → ℝ) (ℓ : ℕ) : ℝ :=
  ∑ x ∈ RevenueOrdered.Ratio.roSet r ℓ, P x (RevenueOrdered.Ratio.roSet r ℓ) * r x

def p320h (P : C → Finset C → ℝ) (r : C → ℝ) (c : ℝ) : ℕ → ℝ :=
  fun ℓ => p320R P r ℓ - p320Q P r ℓ * c

def p320g (P : C → Finset C → ℝ) (r : C → ℝ) (c : ℝ) : ℝ :=
  (levels r).sup' (levels_nonempty r) (p320h P r c)

def p320om (P : C → Finset C → ℝ) (r : C → ℝ) (c : ℝ) : ℕ :=
  (argmaxLevels r (p320h P r c)).min' (argmaxLevels_nonempty r _)

def p320d (P : C → Finset C → ℝ) (r : C → ℝ) (t q : ℕ) : ℝ :=
  jVal P r t (q + 1) - jVal P r t q

def p320M (r : C → ℝ) : ℝ := (Finset.univ : Finset C).sup' Finset.univ_nonempty r

lemma p320_sup'_add (s : Finset ℕ) (hs : s.Nonempty) (a : ℝ) (f : ℕ → ℝ) :
    s.sup' hs (fun ℓ => a + f ℓ) = a + s.sup' hs f := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun ℓ hℓ => by have := Finset.le_sup' f hℓ; linarith)
  · obtain ⟨ℓ, hℓ, h⟩ := Finset.exists_mem_eq_sup' hs f
    rw [h]
    exact Finset.le_sup' (fun ℓ => a + f ℓ) hℓ

lemma p320_jIdx_succ (P : C → Finset C → ℝ) (r : C → ℝ) (t q ℓ : ℕ) :
    jIdx P r (t + 1) (q + 1) ℓ =
      jVal P r t (q + 1) + p320h P r (jVal P r t (q + 1) - jVal P r t q) ℓ := by
  rw [jIdx]
  simp only [jVal, p320h, p320R, p320Q, RevenueOrdered.Ratio.noPurchase]
  simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

lemma p320_jIdx_succ_fun (P : C → Finset C → ℝ) (r : C → ℝ) (t q : ℕ) :
    jIdx P r (t + 1) (q + 1) =
      fun ℓ => jVal P r t (q + 1) + p320h P r (p320d P r t q) ℓ :=
  funext fun ℓ => p320_jIdx_succ P r t q ℓ

lemma p320_jVal_succ (P : C → Finset C → ℝ) (r : C → ℝ) (t q : ℕ) :
    jVal P r (t + 1) (q + 1) = jVal P r t (q + 1) + p320g P r (p320d P r t q) := by
  rw [jVal, p320_jIdx_succ_fun, p320_sup'_add]
  rfl

lemma p320_jVal_zero_left (P : C → Finset C → ℝ) (r : C → ℝ) (q : ℕ) : jVal P r 0 q = 0 := by
  have : jIdx P r 0 q = fun _ => 0 := funext fun ℓ => by simp [jIdx]
  rw [jVal, this, Finset.sup'_const]

lemma p320_jVal_zero_right (P : C → Finset C → ℝ) (r : C → ℝ) (t : ℕ) : jVal P r t 0 = 0 := by
  have : jIdx P r t 0 = fun _ => 0 := funext fun ℓ => by cases t <;> simp [jIdx]
  rw [jVal, this, Finset.sup'_const]

lemma p320_argmax_add (r : C → ℝ) (a : ℝ) (f : ℕ → ℝ) :
    argmaxLevels r (fun ℓ => a + f ℓ) = argmaxLevels r f := by
  unfold argmaxLevels
  rw [p320_sup'_add]
  apply Finset.filter_congr
  intro ℓ _
  exact add_right_inj a

lemma p320_optLevel_succ (P : C → Finset C → ℝ) (r : C → ℝ) (t q : ℕ) :
    optLevel P r (t + 1) (q + 1) = p320om P r (p320d P r t q) := by
  have key : ∀ F G : ℕ → ℝ, argmaxLevels r F = argmaxLevels r G →
      (argmaxLevels r F).min' (argmaxLevels_nonempty r F) =
        (argmaxLevels r G).min' (argmaxLevels_nonempty r G) := by
    intro F G h
    congr 1
  unfold optLevel p320om
  exact key _ _ (by rw [p320_jIdx_succ_fun, p320_argmax_add])

lemma p320_level_mono (r : C → ℝ) {i j : ℕ} (hi : 1 ≤ i)
    (hj : j ≤ RevenueOrdered.Ratio.numVals r) (hij : i ≤ j) :
    RevenueOrdered.Ratio.level r i ≤ RevenueOrdered.Ratio.level r j := by
  unfold RevenueOrdered.Ratio.level
  rw [dif_pos ⟨hi, by omega⟩, dif_pos ⟨by omega, hj⟩]
  exact (RevenueOrdered.Ratio.sortedVals r).monotone (Fin.mk_le_mk.mpr (by omega))

lemma p320_roSet_sub (r : C → ℝ) {i j : ℕ} (hi : i ∈ levels r) (hj : j ∈ levels r)
    (hij : i ≤ j) : RevenueOrdered.Ratio.roSet r j ⊆ RevenueOrdered.Ratio.roSet r i := by
  unfold levels at hi hj
  rw [Finset.mem_Icc] at hi hj
  intro x hx
  simp only [RevenueOrdered.Ratio.roSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact le_trans (p320_level_mono r hi.1 hj.2 hij) hx

lemma p320_Q_anti {P : C → Finset C → ℝ} (r : C → ℝ) (hP : IsRegular P) {i j : ℕ}
    (hi : i ∈ levels r) (hj : j ∈ levels r) (hij : i ≤ j) : p320Q P r j ≤ p320Q P r i := by
  have h := hP.noPurchase_mono _ _ (p320_roSet_sub r hi hj hij)
  unfold RevenueOrdered.Ratio.noPurchase at h
  unfold p320Q
  linarith

lemma p320_Q_nonneg {P : C → Finset C → ℝ} (r : C → ℝ) (hP : IsRegular P) (ℓ : ℕ) :
    0 ≤ p320Q P r ℓ :=
  Finset.sum_nonneg fun x _ => hP.nonneg x _

lemma p320_Q_le_one {P : C → Finset C → ℝ} (r : C → ℝ) (hP : IsRegular P) (ℓ : ℕ) :
    p320Q P r ℓ ≤ 1 :=
  hP.sum_le_one _

lemma p320_om_mono {P : C → Finset C → ℝ} (r : C → ℝ) (hP : IsRegular P) {c c' : ℝ}
    (hcc : c ≤ c') : p320om P r c ≤ p320om P r c' := by
  by_contra hlt
  rw [not_le] at hlt
  have m1 := Finset.min'_mem (argmaxLevels r (p320h P r c')) (argmaxLevels_nonempty r _)
  have m0 := Finset.min'_mem (argmaxLevels r (p320h P r c)) (argmaxLevels_nonempty r _)
  change p320om P r c' ∈ argmaxLevels r (p320h P r c') at m1
  change p320om P r c ∈ argmaxLevels r (p320h P r c) at m0
  set l1 := p320om P r c' with hl1
  set l0 := p320om P r c with hl0
  unfold argmaxLevels at m1 m0
  rw [Finset.mem_filter] at m1 m0
  have hlt1 : p320h P r c l1 < (levels r).sup' (levels_nonempty r) (p320h P r c) := by
    rcases lt_or_eq_of_le (Finset.le_sup' (p320h P r c) m1.1) with h | h
    · exact h
    · exfalso
      have hm : l1 ∈ argmaxLevels r (p320h P r c) := by
        unfold argmaxLevels
        exact Finset.mem_filter.mpr ⟨m1.1, h⟩
      have := Finset.min'_le _ _ hm
      change l0 ≤ l1 at this
      omega
  have hQ := p320_Q_anti r hP m1.1 m0.1 hlt.le
  have hle0 : p320h P r c' l0 ≤ (levels r).sup' (levels_nonempty r) (p320h P r c') :=
    Finset.le_sup' _ m0.1
  rw [← m1.2] at hle0
  rw [← m0.2] at hlt1
  unfold p320h at hle0 hlt1
  nlinarith [mul_nonneg (sub_nonneg.mpr hQ) (sub_nonneg.mpr hcc)]

lemma p320_g_anti {P : C → Finset C → ℝ} (r : C → ℝ) (hP : IsRegular P) {c c' : ℝ}
    (hcc : c ≤ c') : p320g P r c' ≤ p320g P r c := by
  unfold p320g
  refine Finset.sup'_le _ _ (fun ℓ hℓ => le_trans ?_ (Finset.le_sup' _ hℓ))
  unfold p320h
  nlinarith [p320_Q_nonneg r hP ℓ]

lemma p320_g_lip {P : C → Finset C → ℝ} (r : C → ℝ) (hP : IsRegular P) {c c' : ℝ}
    (hcc : c ≤ c') : p320g P r c - p320g P r c' ≤ c' - c := by
  unfold p320g
  obtain ⟨ℓ, hℓ, h⟩ := Finset.exists_mem_eq_sup' (levels_nonempty r) (p320h P r c)
  rw [h]
  have := Finset.le_sup' (p320h P r c') hℓ
  unfold p320h at this ⊢
  nlinarith [p320_Q_le_one r hP ℓ, p320_Q_nonneg r hP ℓ]

lemma p320_R_le {P : C → Finset C → ℝ} (r : C → ℝ) (hP : IsRegular P) (ℓ : ℕ) :
    p320R P r ℓ ≤ p320Q P r ℓ * p320M r := by
  unfold p320R p320Q
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun x _ =>
    mul_le_mul_of_nonneg_left (Finset.le_sup' r (Finset.mem_univ x)) (hP.nonneg x _)

lemma p320_g_le {P : C → Finset C → ℝ} (r : C → ℝ) (hP : IsRegular P) {c : ℝ}
    (hc : c ≤ p320M r) : p320g P r c ≤ p320M r - c := by
  unfold p320g
  refine Finset.sup'_le _ _ (fun ℓ _ => ?_)
  unfold p320h
  nlinarith [p320_R_le r hP ℓ, p320_Q_le_one r hP ℓ, p320_Q_nonneg r hP ℓ]

lemma p320_exists_top (r : C → ℝ) :
    ∃ ℓ ∈ levels r, RevenueOrdered.Ratio.level r ℓ = p320M r := by
  obtain ⟨x0, -, hx0⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := C)) r
  have hrange := Finset.range_orderEmbOfFin (RevenueOrdered.Ratio.revVals r)
    (k := RevenueOrdered.Ratio.numVals r) rfl
  have hmem : r x0 ∈ ((RevenueOrdered.Ratio.revVals r : Finset ℝ) : Set ℝ) := by
    simp [RevenueOrdered.Ratio.revVals]
  rw [← hrange] at hmem
  obtain ⟨j, hj'⟩ := hmem
  have hj : RevenueOrdered.Ratio.sortedVals r j = r x0 := hj'
  have hjlt := j.2
  refine ⟨j.1 + 1, ?_, ?_⟩
  · unfold levels
    rw [Finset.mem_Icc]
    omega
  · unfold p320M
    rw [hx0]
    unfold RevenueOrdered.Ratio.level
    rw [dif_pos ⟨by omega, by omega⟩, ← hj]
    congr 1

lemma p320_g_nonneg {P : C → Finset C → ℝ} (r : C → ℝ) (hP : IsRegular P) {c : ℝ}
    (hc : c ≤ p320M r) : 0 ≤ p320g P r c := by
  obtain ⟨ℓ0, hℓ0, hlev⟩ := p320_exists_top (C := C) r
  have hR : p320Q P r ℓ0 * p320M r ≤ p320R P r ℓ0 := by
    unfold p320R p320Q
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_left ?_ (hP.nonneg x _)
    simp only [RevenueOrdered.Ratio.roSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [← hlev]
    exact hx
  have := Finset.le_sup' (p320h P r c) hℓ0
  unfold p320g
  refine le_trans ?_ this
  unfold p320h
  nlinarith [p320_Q_nonneg r hP ℓ0]

lemma p320_d_zero_left (P : C → Finset C → ℝ) (r : C → ℝ) (q : ℕ) : p320d P r 0 q = 0 := by
  simp [p320d, p320_jVal_zero_left]

lemma p320_d_succ_zero (P : C → Finset C → ℝ) (r : C → ℝ) (t : ℕ) :
    p320d P r (t + 1) 0 = p320d P r t 0 + p320g P r (p320d P r t 0) := by
  have h := p320_jVal_succ P r t 0
  unfold p320d at h ⊢
  rw [p320_jVal_zero_right, p320_jVal_zero_right] at *
  rw [h]
  ring

lemma p320_d_succ_succ (P : C → Finset C → ℝ) (r : C → ℝ) (t q : ℕ) :
    p320d P r (t + 1) (q + 1) =
      p320d P r t (q + 1) + p320g P r (p320d P r t (q + 1)) - p320g P r (p320d P r t q) := by
  have h1 := p320_jVal_succ P r t (q + 1)
  have h2 := p320_jVal_succ P r t q
  unfold p320d at h1 h2 ⊢
  rw [h1, h2]
  ring

lemma p320_M_nonneg (r : C → ℝ) (hr : ∀ x, 0 < r x) : 0 ≤ p320M r := by
  have := Finset.le_sup' r (Finset.mem_univ (Classical.arbitrary C))
  unfold p320M
  linarith [hr (Classical.arbitrary C)]

lemma p320_inv {P : C → Finset C → ℝ} (r : C → ℝ) (hP : IsRegular P) (hr : ∀ x, 0 < r x)
    (t : ℕ) :
    (∀ q, p320d P r t (q + 1) ≤ p320d P r t q) ∧ (∀ q, p320d P r t q ≤ p320M r) := by
  induction t with
  | zero =>
    refine ⟨fun q => ?_, fun q => ?_⟩
    · simp [p320_d_zero_left]
    · rw [p320_d_zero_left]; exact p320_M_nonneg r hr
  | succ t ih =>
    obtain ⟨hA, hB⟩ := ih
    refine ⟨fun q => ?_, fun q => ?_⟩
    · cases q with
      | zero =>
        rw [p320_d_succ_succ, p320_d_succ_zero]
        have l := p320_g_lip r hP (hA 0)
        have n := p320_g_nonneg r hP (hB 0)
        linarith
      | succ q =>
        rw [p320_d_succ_succ, p320_d_succ_succ]
        have l := p320_g_lip r hP (hA (q + 1))
        have a := p320_g_anti r hP (hA q)
        linarith
    · cases q with
      | zero =>
        rw [p320_d_succ_zero]
        have := p320_g_le r hP (hB 0)
        linarith
      | succ q =>
        rw [p320_d_succ_succ]
        have l := p320_g_lip r hP (hA q)
        linarith [hB q]

lemma p320_d_mono_t {P : C → Finset C → ℝ} (r : C → ℝ) (hP : IsRegular P) (hr : ∀ x, 0 < r x)
    (t q : ℕ) : p320d P r t q ≤ p320d P r (t + 1) q := by
  obtain ⟨hA, hB⟩ := p320_inv r hP hr t
  cases q with
  | zero =>
    rw [p320_d_succ_zero]
    have := p320_g_nonneg r hP (hB 0)
    linarith
  | succ q =>
    rw [p320_d_succ_succ]
    have := p320_g_anti r hP (hA q)
    linarith

end

end RevenueOrdered.Nesting

open RevenueOrdered.Nesting in
theorem solution {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
    {P : C → Finset C → ℝ} {r : C → ℝ} (hP : RevenueOrdered.Nesting.IsRegular P)
    (hr : ∀ x, 0 < r x) (t q : ℕ) (ht : 1 ≤ t) (hq : 1 ≤ q) :
    (2 ≤ q → optLevel P r t q ≤ optLevel P r t (q - 1)) ∧
      (2 ≤ t → optLevel P r (t - 1) q ≤ optLevel P r t q) := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  refine ⟨fun hq2 => ?_, fun ht2 => ?_⟩
  · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 + 1 := ⟨q - 2, by omega⟩
    rw [show q' + 1 + 1 - 1 = q' + 1 by omega, p320_optLevel_succ, p320_optLevel_succ]
    exact p320_om_mono r hP ((p320_inv r hP hr t').1 q')
  · obtain ⟨t'', rfl⟩ : ∃ t'', t' = t'' + 1 := ⟨t' - 1, by omega⟩
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [show t'' + 1 + 1 - 1 = t'' + 1 by omega, p320_optLevel_succ, p320_optLevel_succ]
    exact p320_om_mono r hP (p320_d_mono_t r hP hr t'' q')
