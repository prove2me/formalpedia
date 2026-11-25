-- Prove2me | solution 1 for PI.VolSemiDirect.W.Cj.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:02:57.35088+00:00
-- url     : https://prove2.me/submissions/ef5c0c54-c8e7-431c-9242-eb2569b2b48e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_GlGeneratedTransvectionsDiag
import Theorems.Thm_PI_VolSemiDirect_W_Cj_inG_mul
import Theorems.Thm_PI_VolSemiDirect_W_Cj_inG_diag
import Theorems.Thm_PI_VolSemiDirect_W_Cj_inG_rowT
import Theorems.Thm_PI_VolSemiDirect_W_Cj_inG_colT
import Theorems.Thm_PI_VolSemiDirect_W_Cj_rowT_mul_apply
import Theorems.Thm_PI_VolSemiDirect_W_Cj_colT_mul_apply
import Theorems.Thm_PI_VolSemiDirect_W_Cj_mul_rowT_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Cj
open Matrix
variable {A : Type} [CommRing A] {k : ℕ}
namespace PI.VolSemiDirect.W.Cj
theorem _root_.solution (hA : HasStableRangeOne A) (m : ℕ) (hm : m < k) (X : GL (Fin k) A)
    (hX : Red m (X : Matrix (Fin k) (Fin k) A)) :
    ∃ g ∈ Subgroup.closure (genSet A k), ∃ h ∈ Subgroup.closure (genSet A k),
      Red (m + 1) ((g * X * h : GL (Fin k) A) : Matrix (Fin k) (Fin k) A) := by
  have nev : ∀ i j : Fin k, i.val ≠ j.val → i ≠ j := fun i j h e => h (congrArg Fin.val e)
  set p : Fin k := ⟨m, hm⟩ with hpdef
  have hpv : p.val = m := rfl
  set s : Finset (Fin k) := Finset.univ.filter (fun i : Fin k => m < i.val) with hsdef
  have mem_s : ∀ i : Fin k, i ∈ s ↔ m < i.val := by
    intro i
    simp [hsdef]
  have hps : p ∉ s := by
    rw [mem_s, hpv]
    exact lt_irrefl m
  have tri : ∀ i : Fin k, i.val < m ∨ i = p ∨ i ∈ s := by
    intro i
    rcases lt_trichotomy i.val m with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Fin.ext (h.trans hpv.symm)))
    · exact Or.inr (Or.inr ((mem_s i).2 h))
  set Xm : Matrix (Fin k) (Fin k) A := (X : Matrix (Fin k) (Fin k) A) with hXm
  have z1 : ∀ i j : Fin k, i.val < m → i ≠ j → Xm i j = 0 := fun i j hi hij => by
    rw [hX i j (Or.inl hi), Matrix.one_apply_ne hij]
  have z2 : ∀ i j : Fin k, j.val < m → i ≠ j → Xm i j = 0 := fun i j hj hij => by
    rw [hX i j (Or.inr hj), Matrix.one_apply_ne hij]

  set Y : Matrix (Fin k) (Fin k) A := ((X⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A) with hY
  have hYX : Y * Xm = 1 := by
    rw [hY, hXm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hsum : Xm p p * Y p p + (∑ i ∈ s, Xm i p * Y p i) * 1 = 1 := by
    have h1 := congrFun (congrFun hYX p) p
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
    rw [mul_one, ← h1, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin k => m < i.val),
      add_comm]
    congr 1
    · exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    · rw [Finset.sum_eq_single p]
      · exact mul_comm _ _
      · intro i hi hip
        have hi' : ¬ m < i.val := (Finset.mem_filter.1 hi).2
        have hne : i.val ≠ m := fun h => hip (Fin.ext (h.trans hpv.symm))
        rw [z1 i p (by omega) hip, mul_zero]
      · intro hp
        exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ p, by rw [hpv]; exact lt_irrefl m⟩) hp
  obtain ⟨t, ht⟩ := hA _ _ _ _ hsum

  set c1 : Fin k → A := fun i => t * Y p i with hc1
  set R1 : Matrix (Fin k) (Fin k) A := 1 + ∑ i ∈ s, single p i (c1 i) with hR1
  set X1 : Matrix (Fin k) (Fin k) A := R1 * Xm with hX1d
  have hX1 : ∀ a b, X1 a b = Xm a b + if a = p then ∑ i ∈ s, c1 i * Xm i b else 0 :=
    fun a b => rowT_mul_apply p c1 s Xm a b
  have hX1pp : X1 p p = Xm p p + t * ∑ i ∈ s, Xm i p * Y p i := by
    rw [hX1, if_pos rfl, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by rw [hc1]; ring)
  have hUnit : IsUnit (X1 p p) := by
    rw [hX1pp]
    exact ht
  set w : A := ((hUnit.unit⁻¹ : Aˣ) : A) with hw
  have huw : X1 p p * w = 1 := hUnit.mul_val_inv
  have hwu : w * X1 p p = 1 := hUnit.val_inv_mul
  have X1_ne : ∀ a b, a ≠ p → X1 a b = Xm a b := by
    intro a b ha
    rw [hX1, if_neg ha, add_zero]
  have X1_p_low : ∀ b : Fin k, b.val < m → X1 p b = 0 := by
    intro b hb
    rw [hX1, if_pos rfl, z2 p b hb (nev p b (by omega)), zero_add]
    apply Finset.sum_eq_zero
    intro i hi
    have := (mem_s i).1 hi
    rw [z2 i b hb (nev i b (by omega)), mul_zero]

  set c2 : Fin k → A := fun i => -(X1 i p * w) with hc2
  set C : Matrix (Fin k) (Fin k) A := 1 + ∑ i ∈ s, single i p (c2 i) with hC
  set X2 : Matrix (Fin k) (Fin k) A := C * X1 with hX2d
  have hX2 : ∀ a b, X2 a b = X1 a b + if a ∈ s then c2 a * X1 p b else 0 :=
    fun a b => colT_mul_apply p c2 s X1 a b
  have X2_notin : ∀ a b, a ∉ s → X2 a b = X1 a b := by
    intro a b ha
    rw [hX2, if_neg ha, add_zero]
  have X2_s_p : ∀ a, a ∈ s → X2 a p = 0 := by
    intro a ha
    rw [hX2, if_pos ha, hc2]
    linear_combination (-(X1 a p)) * hwu
  have X2_s_low : ∀ a b, a ∈ s → b.val < m → X2 a b = 0 := by
    intro a b ha hb
    have := (mem_s a).1 ha
    rw [hX2, if_pos ha, X1_p_low b hb, mul_zero, add_zero, X1_ne a b (fun h => hps (h ▸ ha))]
    exact z2 a b hb (nev a b (by omega))

  set c3 : Fin k → A := fun j => -(w * X2 p j) with hc3
  set Rr : Matrix (Fin k) (Fin k) A := 1 + ∑ j ∈ s, single p j (c3 j) with hRr
  set X3 : Matrix (Fin k) (Fin k) A := X2 * Rr with hX3d
  have hX3 : ∀ a b, X3 a b = X2 a b + if b ∈ s then X2 a p * c3 b else 0 :=
    fun a b => mul_rowT_apply p c3 s X2 a b

  set d : Fin k → A := fun i => if i = p then w else 1 with hdd
  set X4 : Matrix (Fin k) (Fin k) A := diagonal d * X3 with hX4d
  have hX4 : ∀ a b, X4 a b = d a * X3 a b := fun a b => diagonal_mul d X3 a b
  have hd : ∀ i, IsUnit (d i) := by
    intro i
    rw [hdd]
    dsimp only
    split_ifs
    · exact (hUnit.unit⁻¹).isUnit
    · exact isUnit_one
  have dp : d p = w := by
    rw [hdd]
    exact if_pos rfl
  have dne : ∀ a, a ≠ p → d a = 1 := by
    intro a ha
    rw [hdd]
    exact if_neg ha
  have gL : InG (diagonal d * C * R1) :=
    inG_mul (inG_mul (inG_diag d hd) (inG_colT p c2 s hps)) (inG_rowT p c1 s hps)
  have gR : InG Rr := inG_rowT p c3 s hps
  obtain ⟨g, hg, hgv⟩ := gL
  obtain ⟨h, hh, hhv⟩ := gR
  refine ⟨g, hg, h, hh, ?_⟩
  have e : ((g * X * h : GL (Fin k) A) : Matrix (Fin k) (Fin k) A) = X4 := by
    rw [Units.val_mul, Units.val_mul, hgv, hhv, hX4d, hX3d, hX2d, hX1d, hXm]
    simp only [Matrix.mul_assoc]
  rw [e]
  intro a b hab
  rw [hX4]
  rcases tri a with ha | ha | ha
  · have hap : a ≠ p := nev a p (by omega)
    have has : a ∉ s := fun h => by have := (mem_s a).1 h; omega
    rw [dne a hap, one_mul, hX3, X2_notin a p has, X1_ne a p hap, z1 a p ha hap, zero_mul,
      ite_self, add_zero, X2_notin a b has, X1_ne a b hap]
    exact hX a b (Or.inl ha)
  · rw [ha, dp]
    rcases tri b with hb | hb | hb
    · rw [hX3, if_neg (fun h => by have := (mem_s b).1 h; omega), add_zero, X2_notin p b hps,
        X1_p_low b hb, mul_zero, Matrix.one_apply_ne (nev p b (by omega))]
    · rw [hb, hX3, if_neg hps, add_zero, X2_notin p p hps, Matrix.one_apply_eq]
      exact hwu
    · have := (mem_s b).1 hb
      rw [hX3, if_pos hb, hc3, X2_notin p b hps, X2_notin p p hps,
        Matrix.one_apply_ne (nev p b (by omega))]
      linear_combination (-(w * X1 p b)) * huw - (w ^ 2 * X1 p p) * X2_notin p b hps
  · have ham := (mem_s a).1 ha
    have hap : a ≠ p := nev a p (by omega)
    have hb' : b.val < m + 1 := by
      rcases hab with h | h
      · omega
      · exact h
    rw [dne a hap, one_mul, hX3, if_neg (fun h => by have := (mem_s b).1 h; omega), add_zero]
    rcases tri b with hb | hb | hb
    · rw [X2_s_low a b ha hb, Matrix.one_apply_ne (nev a b (by omega))]
    · rw [hb, X2_s_p a ha, Matrix.one_apply_ne hap]
    · have := (mem_s b).1 hb
      omega
end PI.VolSemiDirect.W.Cj
