-- Prove2me | solution 1 for OptInapprox.Bal2Sat.opt_le_sdpValue
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:24:06.83498+00:00
-- url     : https://prove2.me/submissions/2b5ea98b-4c42-4157-993e-19afaf588cf9

import Mathlib
import Definitions.Def_HighDimProb_RandomVectors_IsStandardGaussianVector
import Definitions.Def_OptInapprox_Bal2Sat_Setting

-- carved verbatim out of submission cffe6099-6812-4f5e-8cbc-7e13209a0989, lines 580-595

section
set_option autoImplicit false
open OptInapprox.Bal2Sat OptInapprox.MaxCut Finset

lemma pm_sq (b : Bool) : pm b * pm b = 1 := by cases b <;> simp [pm]

lemma pm_mul_cases (a b : Bool) : pm a * pm b = 1 ∨ pm a * pm b = -1 := by
  cases a <;> cases b <;> simp [pm]

def flipAt {n : ℕ} (j : Fin n) (x : Fin n → Bool) : Fin n → Bool := Function.update x j (!x j)

lemma flipAt_invol {n : ℕ} (j : Fin n) : Function.Involutive (flipAt j) := by
  intro x
  funext k
  by_cases h : k = j
  · subst h; simp [flipAt]
  · simp [flipAt, h]

lemma flipAt_same {n : ℕ} (j k : Fin n) (x : Fin n → Bool) (h : k ≠ j) : flipAt j x k = x k := by
  simp [flipAt, h]

lemma sum_flip {n : ℕ} (j : Fin n) (g : (Fin n → Bool) → ℝ)
    (h : ∀ x, g (flipAt j x) = - g x) : ∑ x, g x = 0 := by
  have e := Equiv.sum_comp (Function.Involutive.toPerm (flipAt j) (flipAt_invol j)) g
  simp only [Function.Involutive.coe_toPerm, h, Finset.sum_neg_distrib] at e
  linarith

lemma pm_flip {n : ℕ} (j : Fin n) (x : Fin n → Bool) : pm (flipAt j x j) = - pm (x j) := by
  cases h : x j <;> simp [flipAt, pm, h]

lemma sum_pm {n : ℕ} (j : Fin n) : ∑ x : Fin n → Bool, pm (x j) = 0 :=
  sum_flip j _ (fun x => pm_flip j x)

lemma sum_pm_pm {n : ℕ} (a i : Fin n) :
    ∑ x : Fin n → Bool, pm (x i) * pm (x a) = if a = i then (2:ℝ) ^ n else 0 := by
  by_cases h : a = i
  · subst h; simp [pm_sq]
  · rw [if_neg h]
    refine sum_flip i _ (fun x => ?_)
    rw [pm_flip, flipAt_same i a x h]; ring

lemma sum_triple {n : ℕ} (a b i : Fin n) :
    ∑ x : Fin n → Bool, pm (x i) * (pm (x a) * pm (x b)) = 0 := by
  by_cases hab : a = b
  · subst hab
    have : ∀ x : Fin n → Bool, pm (x i) * (pm (x a) * pm (x a)) = pm (x i) := by
      intro x; rw [pm_sq]; ring
    simp only [this]; exact sum_pm i
  · by_cases hia : i = a
    · subst hia
      have : ∀ x : Fin n → Bool, pm (x i) * (pm (x i) * pm (x b)) = pm (x b) := by
        intro x; rw [← mul_assoc, pm_sq]; ring
      simp only [this]; exact sum_pm b
    · by_cases hib : i = b
      · subst hib
        have : ∀ x : Fin n → Bool, pm (x i) * (pm (x a) * pm (x i)) = pm (x a) := by
          intro x; rw [mul_comm (pm (x a)), ← mul_assoc, pm_sq]; ring
        simp only [this]; exact sum_pm a
      · refine sum_flip i _ (fun x => ?_)
        rw [pm_flip, flipAt_same i a x (Ne.symm hia), flipAt_same i b x (Ne.symm hib)]; ring

lemma ind_eq {n : ℕ} (C : Literal n × Literal n) (x : Fin n → Bool) :
    (if clauseSat C x then (1:ℝ) else 0) =
      (3 - litVal C.1 x - litVal C.2 x - litVal C.1 x * litVal C.2 x) / 4 := by
  obtain ⟨⟨i, r⟩, ⟨j, s⟩⟩ := C
  simp only [clauseSat, litTrue, litVal]
  cases r <;> cases s <;> cases hx : x i <;> cases hy : x j <;> simp [pm, hx, hy] <;> norm_num

lemma satWeight_expand {n : ℕ} (I : Instance n) (x : Fin n → Bool) :
    satWeight I x = ∑ c, I.w c * ((3 - litVal (I.clause c).1 x - litVal (I.clause c).2 x
      - litVal (I.clause c).1 x * litVal (I.clause c).2 x) / 4) := by
  unfold satWeight
  exact Finset.sum_congr rfl (fun c _ => by rw [ind_eq])

noncomputable def Acoef {n : ℕ} (I : Instance n) (i : Fin n) : ℝ :=
  ∑ c, I.w c * ((if (I.clause c).1.1 = i then pm (I.clause c).1.2 else 0) +
    (if (I.clause c).2.1 = i then pm (I.clause c).2.2 else 0))

lemma clause_sum {n : ℕ} (C : Literal n × Literal n) (i : Fin n) :
    ∑ x : Fin n → Bool, pm (x i) * ((3 - litVal C.1 x - litVal C.2 x
      - litVal C.1 x * litVal C.2 x) / 4) =
      -((2:ℝ) ^ n / 4) * ((if C.1.1 = i then pm C.1.2 else 0) + (if C.2.1 = i then pm C.2.2 else 0)) := by
  have h : ∀ x : Fin n → Bool, pm (x i) * ((3 - litVal C.1 x - litVal C.2 x
      - litVal C.1 x * litVal C.2 x) / 4) =
      (3/4) * pm (x i) - (pm C.1.2 / 4) * (pm (x i) * pm (x C.1.1))
        - (pm C.2.2 / 4) * (pm (x i) * pm (x C.2.1))
        - (pm C.1.2 * pm C.2.2 / 4) * (pm (x i) * (pm (x C.1.1) * pm (x C.2.1))) := by
    intro x; unfold litVal; ring
  simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_pm, sum_pm_pm, sum_triple]
  split_ifs <;> simp <;> ring

lemma sum_pm_sat {n : ℕ} (I : Instance n) (i : Fin n) :
    ∑ x : Fin n → Bool, pm (x i) * satWeight I x = -((2:ℝ) ^ n / 4) * Acoef I i := by
  simp only [satWeight_expand, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold Acoef
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have h : ∀ x : Fin n → Bool, pm (x i) * (I.w c * ((3 - litVal (I.clause c).1 x
      - litVal (I.clause c).2 x - litVal (I.clause c).1 x * litVal (I.clause c).2 x) / 4)) =
      I.w c * (pm (x i) * ((3 - litVal (I.clause c).1 x - litVal (I.clause c).2 x
      - litVal (I.clause c).1 x * litVal (I.clause c).2 x) / 4)) := by intro x; ring
  simp only [h, ← Finset.mul_sum, clause_sum]
  ring

lemma Acoef_zero {n : ℕ} (I : Instance n) (hbal : IsBalanced I) (i : Fin n) : Acoef I i = 0 := by
  have h1 := hbal i
  have hsplit : ∑ x : Fin n → Bool, pm (x i) * satWeight I x =
      ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => x i = false), pm (x i) * satWeight I x +
      ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => x i = true), pm (x i) * satWeight I x := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x : Fin n → Bool => x i = false)]
    congr 1
    refine Finset.sum_congr (by ext x; simp) (fun _ _ => rfl)
  have hF : ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => x i = false), pm (x i) * satWeight I x
      = ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => x i = false), satWeight I x :=
    Finset.sum_congr rfl (fun x hx => by
      simp only [Finset.mem_filter] at hx; simp [pm, hx.2])
  have hT : ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => x i = true), pm (x i) * satWeight I x
      = -∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => x i = true), satWeight I x := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun x hx => by
      simp only [Finset.mem_filter] at hx; simp [pm, hx.2])
  have h0 : ∑ x : Fin n → Bool, pm (x i) * satWeight I x = 0 := by
    rw [hsplit, hF, hT, h1]; ring
  rw [sum_pm_sat] at h0
  have hpos : ((2:ℝ) ^ n / 4) ≠ 0 := by positivity
  have : (-((2:ℝ) ^ n / 4)) * Acoef I i = 0 := h0
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (neg_eq_zero.1 h) hpos
  · exact h

lemma lin_zero {n : ℕ} (I : Instance n) (hbal : IsBalanced I) (x : Fin n → Bool) :
    ∑ c, I.w c * (litVal (I.clause c).1 x + litVal (I.clause c).2 x) = 0 := by
  have h : ∑ i, pm (x i) * Acoef I i = 0 :=
    Finset.sum_eq_zero (fun i _ => by rw [Acoef_zero I hbal i, mul_zero])
  unfold Acoef at h
  simp only [Finset.mul_sum] at h
  rw [Finset.sum_comm] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have : ∑ i, pm (x i) * (I.w c * ((if (I.clause c).1.1 = i then pm (I.clause c).1.2 else 0) +
      (if (I.clause c).2.1 = i then pm (I.clause c).2.2 else 0))) =
      I.w c * (pm (x (I.clause c).1.1) * pm (I.clause c).1.2 +
        pm (x (I.clause c).2.1) * pm (I.clause c).2.2) := by
    simp only [mul_add, mul_ite, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    ring
  rw [this]
  unfold litVal
  ring

lemma dot_bounds {d : ℕ} (u w : Fin d → ℝ) (hu : ∑ k, u k ^ 2 = 1) (hw : ∑ k, w k ^ 2 = 1) :
    -1 ≤ dot u w ∧ dot u w ≤ 1 := by
  unfold dot
  constructor
  · have h := Finset.sum_nonneg (s := Finset.univ) (fun k _ => sq_nonneg (u k + w k))
    have e : ∑ k, (u k + w k) ^ 2 = ∑ k, u k ^ 2 + ∑ k, w k ^ 2 + 2 * ∑ k, u k * w k := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [e, hu, hw] at h; linarith
  · have h := Finset.sum_nonneg (s := Finset.univ) (fun k _ => sq_nonneg (u k - w k))
    have e : ∑ k, (u k - w k) ^ 2 = ∑ k, u k ^ 2 + ∑ k, w k ^ 2 - 2 * ∑ k, u k * w k := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [e, hu, hw] at h; linarith

lemma rho_bounds {n d : ℕ} (I : Instance n) (v : Fin n → Fin d → ℝ) (hv : IsUnitFamily v)
    (c : Fin I.m) :
    -1 ≤ pm (I.clause c).1.2 * pm (I.clause c).2.2 * dot (v (I.clause c).1.1) (v (I.clause c).2.1) ∧
    pm (I.clause c).1.2 * pm (I.clause c).2.2 * dot (v (I.clause c).1.1) (v (I.clause c).2.1) ≤ 1 := by
  obtain ⟨h1, h2⟩ := dot_bounds _ _ (hv (I.clause c).1.1) (hv (I.clause c).2.1)
  rcases pm_mul_cases (I.clause c).1.2 (I.clause c).2.2 with h | h <;> rw [h] <;>
    constructor <;> linarith

lemma sdpObj_le {n d : ℕ} (I : Instance n) (v : Fin n → Fin d → ℝ) (hv : IsUnitFamily v) :
    sdpObj I v ≤ ∑ c, I.w c := by
  unfold sdpObj
  apply Finset.sum_le_sum
  intro c _
  obtain ⟨h1, h2⟩ := rho_bounds I v hv c
  nlinarith [mul_nonneg (I.w_nonneg c) (sub_nonneg.2 h1)]

def vv {n : ℕ} (x : Fin n → Bool) : Fin n → Fin 1 → ℝ := fun i _ => pm (x i)

lemma pm_sq' (b : Bool) : pm b ^ 2 = 1 := by cases b <;> simp [pm]

lemma vv_unit {n : ℕ} (x : Fin n → Bool) : IsUnitFamily (vv x) := by
  intro i
  simp [vv, pm_sq']

lemma sdpObj_vv {n : ℕ} (I : Instance n) (hbal : IsBalanced I) (x : Fin n → Bool) :
    sdpObj I (vv x) = satWeight I x := by
  rw [satWeight_expand]
  have L := lin_zero I hbal x
  have key : ∀ c : Fin I.m, I.w c * ((3 - litVal (I.clause c).1 x - litVal (I.clause c).2 x
      - litVal (I.clause c).1 x * litVal (I.clause c).2 x) / 4) =
      I.w c * (3 / 4 - 1 / 4 * (pm (I.clause c).1.2 * pm (I.clause c).2.2 *
        dot (vv x (I.clause c).1.1) (vv x (I.clause c).2.1))) -
      (1 / 4) * (I.w c * (litVal (I.clause c).1 x + litVal (I.clause c).2 x)) := by
    intro c
    simp only [dot, vv, litVal, Finset.univ_unique, Finset.sum_singleton]
    ring
  rw [Finset.sum_congr rfl (fun c _ => key c), Finset.sum_sub_distrib, ← Finset.mul_sum, L]
  unfold sdpObj
  ring

theorem solution {n : ℕ} (I : Instance n) (hbal : IsBalanced I) : OPT I ≤ sdpValue I := by
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin n → Bool))
    (satWeight I)
  have h1 : OPT I = satWeight I x := hx
  rw [h1, ← sdpObj_vv I hbal x]
  apply le_csSup
  · exact ⟨∑ c, I.w c, by rintro s ⟨d, v, hv, rfl⟩; exact sdpObj_le I v hv⟩
  · exact ⟨1, vv x, vv_unit x, rfl⟩

end
