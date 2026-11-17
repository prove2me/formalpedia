-- Prove2me | solution 1 for PolySwap.KMS.lemma_3_17
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T16:37:26.041469+00:00
-- url     : https://prove2.me/submissions/fbd22f3a-96ad-423f-83b1-d41c756bf506

import Mathlib
import Definitions.Def_PolySwap_KMS_Complex
import Definitions.Def_PolySwap_KMS_Cohomology
import Definitions.Def_PolySwap_KMS_Cone
import Definitions.Def_PolySwap_KMS_Dehn
import Definitions.Def_PolySwap_KMS_KMSComplex

section Part_A_amalgam

open Classical Matrix

namespace PolySwap.KMS.L317A

open PolySwap.KMS
section A3

variable {G : Type*} [Group G] {F : Type*} [Field F]

def cm (a b : G) : G := a * b * a⁻¹ * b⁻¹

lemma comm_cm {g a b : G} (ha : Commute g a) (hb : Commute g b) : Commute g (cm a b) := by
  unfold cm; exact ((ha.mul_right hb).mul_right ha.inv_right).mul_right hb.inv_right

lemma cm_mul_right_of_comm {a b c : G} (h : Commute a c) : cm a (b * c) = cm a b := by
  unfold cm
  rw [show a * (b * c) * a⁻¹ * (b * c)⁻¹ = a * b * (c * a⁻¹ * c⁻¹) * b⁻¹ by group,
    ← h.inv_left.eq]; group

lemma cm_mul_left_of_comm {a b c : G} (h : Commute b c) : cm (a * b) c = cm a c := by
  unfold cm
  rw [show a * b * c * (a * b)⁻¹ * c⁻¹ = a * (b * c * b⁻¹) * a⁻¹ * c⁻¹ by group, h.eq]; group

lemma conj_of_cm {a b w : G} (h : cm a b = w) : b * a * b⁻¹ = w⁻¹ * a := by
  rw [← h]; unfold cm; group

lemma conj_eq_cm (a b : G) : a * b * a⁻¹ = cm a b * b := by unfold cm; group

lemma conj_trick {a b g h : G} (hab : a = b * g) (hc : Commute g h) :
    a * h * a⁻¹ = b * h * b⁻¹ := by
  subst hab
  rw [show b * g * h * (b * g)⁻¹ = b * (g * h) * g⁻¹ * b⁻¹ by group, hc.eq]; group

lemma cm_conj (g a b : G) : g * cm a b * g⁻¹ = cm (g * a * g⁻¹) (g * b * g⁻¹) := by
  unfold cm; group

lemma cm_mul_left (a b c : G) : cm (a * b) c = a * cm b c * a⁻¹ * cm a c := by unfold cm; group

lemma cm_mul_right (a b c : G) : cm a (b * c) = cm a b * (b * cm a c * b⁻¹) := by
  unfold cm; group

lemma conj_mul_split (a b c : G) : a * (b * c) * a⁻¹ = cm a b * b * (cm a c * c) := by
  unfold cm; group

lemma comm_conj {a b : G} (h : Commute a b) (g : G) : Commute (g * a * g⁻¹) (g * b * g⁻¹) := by
  unfold Commute SemiconjBy
  rw [show g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ by group, h.eq]; group

lemma conj_of_commute {g a : G} (h : Commute g a) : g * a * g⁻¹ = a := by rw [h.eq]; group

lemma comm_of_conj {g a : G} (h : g * a * g⁻¹ = a) : Commute g a := by
  unfold Commute SemiconjBy
  calc g * a = (g * a * g⁻¹) * g := by group
    _ = a * g := by rw [h]

lemma cm_eq_one_iff {a b : G} : cm a b = 1 ↔ Commute a b := by
  unfold cm Commute SemiconjBy
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]

def IsAdd (f : F → G) : Prop := ∀ a b, f (a + b) = f a * f b

lemma IsAdd.zero {f : F → G} (hf : IsAdd f) : f 0 = 1 := by
  have := hf 0 0; rw [add_zero] at this
  have h2 := congrArg (fun t => (f 0)⁻¹ * t) this
  simp only [inv_mul_cancel, inv_mul_cancel_left] at h2
  exact h2.symm

lemma IsAdd.neg {f : F → G} (hf : IsAdd f) (a : F) : f (-a) = (f a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← hf, neg_add_cancel, hf.zero])

lemma IsAdd.comm {f : F → G} (hf : IsAdd f) (a b : F) : Commute (f a) (f b) := by
  unfold Commute SemiconjBy; rw [← hf, ← hf, add_comm]

lemma gen_comm (f g : F → G) (hf : IsAdd f) (hg : IsAdd g) (hfg : ∀ a b, Commute (f a) (g b))
    (ht : ∀ γ : F, ∃ t, t ≠ 0 ∧ t ≠ γ) (y : G)
    (h : ∀ γ α, γ ≠ 0 → α ≠ 0 → Commute (f γ * g α) y) :
    (∀ γ, Commute (f γ) y) ∧ ∀ α, Commute (g α) y := by
  have hf' : ∀ γ, Commute (f γ) y := by
    intro γ
    obtain ⟨t, ht0, htγ⟩ := ht γ
    have e : f γ = (f t * g 1) * (f (γ - t) * g (-1)) := by
      calc f γ = f (t + (γ - t)) * g (1 + -1) := by
              rw [add_sub_cancel, add_neg_cancel, hg.zero, mul_one]
        _ = _ := by
          rw [hf, hg]; simp only [mul_assoc]; congr 1
          rw [← mul_assoc, ← mul_assoc, (hfg (γ - t) 1).eq]
    rw [e]
    exact (h t 1 ht0 one_ne_zero).mul_left
      (h _ _ (sub_ne_zero.2 (Ne.symm htγ)) (neg_ne_zero.2 one_ne_zero))
  refine ⟨hf', fun α => ?_⟩
  by_cases hα : α = 0
  · rw [hα, hg.zero]; exact Commute.one_left _
  · have e : g α = (f 1 * g α) * f (-1) := by
      rw [mul_assoc, ← (hfg (-1) α).eq, ← mul_assoc, ← hf, add_neg_cancel, hf.zero, one_mul]
    rw [e]; exact (h 1 α one_ne_zero hα).mul_left (hf' (-1))

/-- The A₃ lemma. -/
theorem a3 (x1 x2 x3 x12 x23 : F → G)
    (a1 : IsAdd x1) (a3 : IsAdd x3) (a12 : IsAdd x12) (a23 : IsAdd x23)
    (c12 : ∀ α β, cm (x1 α) (x2 β) = x12 (α * β))
    (k1 : ∀ γ α, Commute (x12 γ) (x1 α)) (k2 : ∀ γ β, Commute (x12 γ) (x2 β))
    (c23 : ∀ β ν, cm (x2 β) (x3 ν) = x23 (β * ν))
    (m2 : ∀ δ β, Commute (x23 δ) (x2 β)) (m3 : ∀ δ ν, Commute (x23 δ) (x3 ν))
    (c13 : ∀ α ν, Commute (x1 α) (x3 ν))
    (hF : ∃ α α' : F, α ≠ 0 ∧ α' ≠ 0 ∧ α + α' ≠ 0) :
    (∀ α δ, cm (x1 α) (x23 δ) = cm (x1 (α * δ)) (x23 1)) ∧
    (∀ γ ν, cm (x12 γ) (x3 ν) = cm (x1 (γ * ν)) (x23 1)) ∧
    IsAdd (fun l => cm (x1 l) (x23 1)) ∧
    (∀ l a, Commute (cm (x1 l) (x23 1)) (x1 a)) ∧
    (∀ l a, Commute (cm (x1 l) (x23 1)) (x2 a)) ∧
    (∀ l a, Commute (cm (x1 l) (x23 1)) (x3 a)) ∧
    (∀ l a, Commute (cm (x1 l) (x23 1)) (x12 a)) ∧
    (∀ l a, Commute (cm (x1 l) (x23 1)) (x23 a)) ∧
    (∀ γ δ, cm (x12 γ) (x23 δ) = 1) := by
  have ht : ∀ γ : F, ∃ t, t ≠ 0 ∧ t ≠ γ := by
    obtain ⟨α, α', hα, hα', hαα'⟩ := hF
    intro γ
    by_cases hγ : γ = 0
    · exact ⟨α, hα, hγ ▸ hα⟩
    · refine ⟨-(γ * α' / α), neg_ne_zero.2 (div_ne_zero (mul_ne_zero hγ hα') hα), fun h => ?_⟩
      have h2 : -(γ * α' / α) * α = γ * α := by rw [h]
      rw [neg_mul, div_mul_cancel₀ _ hα] at h2
      have : γ * (α + α') = 0 := by linear_combination -h2
      exact (mul_ne_zero hγ hαα') this
  -- Step K
  have e1 : ∀ α β, x2 β * x1 α * (x2 β)⁻¹ = x12 (-(α * β)) * x1 α := by
    intro α β; rw [conj_of_cm (c12 α β), a12.neg]
  have e2 : ∀ β ν, x2 β * x3 ν * (x2 β)⁻¹ = x23 (β * ν) * x3 ν := by
    intro β ν; rw [conj_eq_cm, c23]
  have K : ∀ α β ν, Commute (x12 (-(α * β)) * x1 α) (x23 (β * ν) * x3 ν) := by
    intro α β ν; rw [← e1, ← e2]; exact comm_conj (c13 α ν) _
  -- Step Q
  have Qx3 : ∀ α δ ν, Commute (x3 ν) (cm (x1 α) (x23 δ)) :=
    fun α δ ν => comm_cm (c13 α ν).symm (m3 δ ν).symm
  have Q : ∀ α δ, (∀ γ, Commute (x12 γ) (cm (x1 α) (x23 δ))) ∧
      ∀ a, Commute (x1 a) (cm (x1 α) (x23 δ)) := by
    intro α δ
    refine gen_comm x12 x1 a12 a1 k1 ht _ (fun γ' α' hγ hα => ?_)
    have hβ : -γ' / α' ≠ 0 := div_ne_zero (neg_ne_zero.2 hγ) hα
    have h := K α' (-γ' / α') (δ / (-γ' / α'))
    rw [show -(α' * (-γ' / α')) = γ' by field_simp,
      show -γ' / α' * (δ / (-γ' / α')) = δ by field_simp] at h
    rw [← cm_mul_right_of_comm (c13 α (δ / (-γ' / α')))]
    exact comm_cm ((k1 γ' α).mul_left (a1.comm α' α)) h
  -- Step R
  have Rx1 : ∀ γ ν α, Commute (x1 α) (cm (x12 γ) (x3 ν)) :=
    fun γ ν α => comm_cm (k1 γ α).symm (c13 α ν)
  have R : ∀ γ ν, (∀ δ, Commute (x23 δ) (cm (x12 γ) (x3 ν))) ∧
      ∀ a, Commute (x3 a) (cm (x12 γ) (x3 ν)) := by
    intro γ ν
    refine gen_comm x23 x3 a23 a3 m3 ht _ (fun δ' ν' hδ hν => ?_)
    have hβ : δ' / ν' ≠ 0 := div_ne_zero hδ hν
    have h := K (-γ / (δ' / ν')) (δ' / ν') ν'
    rw [show -(-γ / (δ' / ν') * (δ' / ν')) = γ by field_simp,
      show δ' / ν' * ν' = δ' by field_simp] at h
    rw [← cm_mul_left_of_comm (c13 (-γ / (δ' / ν')) ν)]
    exact comm_cm h.symm ((m3 δ' ν).mul_left (a3.comm ν' ν))
  -- Step E
  have E : ∀ α β ν, cm (x1 α) (x23 (β * ν)) =
      cm (x12 (α * β)) (x23 (β * ν)) * cm (x12 (α * β)) (x3 ν) := by
    intro α β ν
    have hg : x1 α = x12 (α * β) * (x12 (-(α * β)) * x1 α) := by
      rw [← mul_assoc, ← a12, add_neg_cancel, a12.zero, one_mul]
    have key := conj_trick hg (K α β ν)
    rw [conj_mul_split, conj_mul_split, cm_eq_one_iff.2 (c13 α ν), one_mul] at key
    have h1 := mul_right_cancel (key.trans (mul_assoc _ _ _).symm)
    rw [mul_assoc, ((R (α * β) ν).1 (β * ν)).eq, ← mul_assoc] at h1
    exact mul_right_cancel h1
  -- Step C
  have p0 : ∀ δ, cm (x12 0) (x23 δ) = 1 := by
    intro δ; rw [a12.zero]; unfold cm; group
  have Cpx : ∀ γ δ, (∀ a, Commute (x1 a) (cm (x12 γ) (x23 δ))) ∧
      (∀ a, Commute (x3 a) (cm (x12 γ) (x23 δ))) := by
    intro γ δ
    by_cases hγ : γ = 0
    · rw [hγ, p0]; exact ⟨fun _ => Commute.one_right _, fun _ => Commute.one_right _⟩
    · have h := E 1 γ (δ / γ)
      rw [one_mul, show γ * (δ / γ) = δ by field_simp] at h
      rw [eq_mul_inv_of_mul_eq h.symm]
      exact ⟨fun a => ((Q 1 δ).2 a).mul_right (Rx1 γ _ a).inv_right,
        fun a => (Qx3 1 δ a).mul_right ((R γ _).2 a).inv_right⟩
  have Cp2 : ∀ γ δ a, Commute (x2 a) (cm (x12 γ) (x23 δ)) :=
    fun γ δ a => comm_cm (k2 γ a).symm (m2 δ a).symm
  have Cp12 : ∀ γ δ a, Commute (x12 a) (cm (x12 γ) (x23 δ)) := by
    intro γ δ a
    rw [show x12 a = cm (x1 a) (x2 1) by rw [c12, mul_one]]
    exact (comm_cm ((Cpx γ δ).1 a).symm (Cp2 γ δ 1).symm).symm
  have Cpr : ∀ γ δ γ' ν', Commute (cm (x12 γ') (x3 ν')) (cm (x12 γ) (x23 δ)) :=
    fun γ δ γ' ν' => (comm_cm (Cp12 γ δ γ').symm ((Cpx γ δ).2 ν').symm).symm
  -- Step A
  have Aq : ∀ α α' δ, cm (x1 (α + α')) (x23 δ) = cm (x1 α') (x23 δ) * cm (x1 α) (x23 δ) := by
    intro α α' δ; rw [a1, cm_mul_left, conj_of_commute ((Q α' δ).2 α)]
  have Ar : ∀ γ ν ν', cm (x12 γ) (x3 (ν + ν')) = cm (x12 γ) (x3 ν) * cm (x12 γ) (x3 ν') := by
    intro γ ν ν'; rw [a3, cm_mul_right, conj_of_commute ((R γ ν').2 ν)]
  -- Step P
  have P1 : ∀ γ δ, cm (x12 γ) (x23 δ) = 1 := by
    intro γ δ
    by_cases hγ : γ = 0
    · rw [hγ]; exact p0 δ
    obtain ⟨α, α', hα, hα', hαα'⟩ := hF
    have hE : ∀ a, a ≠ 0 → cm (x1 a) (x23 δ) =
        cm (x12 γ) (x23 δ) * cm (x12 γ) (x3 (a * δ / γ)) := by
      intro a ha
      have h := E a (γ / a) (a * δ / γ)
      rwa [show a * (γ / a) = γ by field_simp, show γ / a * (a * δ / γ) = δ by field_simp] at h
    have h1 := hE (α + α') hαα'
    rw [Aq, hE α hα, hE α' hα', show (α + α') * δ / γ = α' * δ / γ + α * δ / γ by ring, Ar] at h1
    have hc := Cpr γ δ γ (α' * δ / γ)
    set p := cm (x12 γ) (x23 δ)
    set A := cm (x12 γ) (x3 (α' * δ / γ))
    set B := cm (x12 γ) (x3 (α * δ / γ))
    rw [show p * A * (p * B) = p * (A * p) * B by group, hc.eq,
      show p * (p * A) * B = p * (p * (A * B)) by group] at h1
    have h2 := mul_left_cancel h1
    exact mul_right_cancel (h2.trans (one_mul (A * B)).symm)
  -- Step Z
  have EZ : ∀ α β ν, cm (x1 α) (x23 (β * ν)) = cm (x12 (α * β)) (x3 ν) := by
    intro α β ν; rw [E, P1, one_mul]
  have Z1 : ∀ α δ, cm (x1 α) (x23 δ) = cm (x1 (α * δ)) (x23 1) := by
    intro α δ
    have h1 := EZ α δ 1
    have h2 := EZ (α * δ) 1 1
    simp only [mul_one] at h1 h2
    rw [h1, h2]
  have Z2 : ∀ γ ν, cm (x12 γ) (x3 ν) = cm (x1 (γ * ν)) (x23 1) := by
    intro γ ν; have h := EZ 1 γ ν; rw [one_mul] at h; rw [← h, Z1, one_mul]
  refine ⟨Z1, Z2, fun a b => by simp only; rw [add_comm, Aq], fun l a => ((Q l 1).2 a).symm,
    fun l a => ?_, fun l a => (Qx3 l 1 a).symm, fun l a => ((Q l 1).1 a).symm,
    fun l a => ?_, P1⟩
  · refine (comm_of_conj ?_).symm
    rw [cm_conj, e1, conj_of_commute (m2 1 a).symm, cm_mul_left,
      conj_of_commute ((Q l 1).1 _), P1, mul_one]
  · rw [show cm (x1 l) (x23 1) = cm (x12 l) (x3 1) by rw [Z2, mul_one]]
    exact ((R l 1).1 a).symm

end A3

section Mat

variable {d : ℕ} {F : Type*} [Field F]

abbrev SLd (d : ℕ) (F : Type*) [Field F] := SpecialLinearGroup (Fin (d + 1)) F

/-- Off-diagonal support on pairs `(i, j)`, `i < j`, with every colour of `(i, j]` in `S`. -/
def Pat (S : Set ℕ) (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F) : Prop :=
  ∀ i j : Fin (d + 1), i ≠ j → M i j ≠ 0 → i < j ∧ ∀ c : ℕ, (i : ℕ) < c → c ≤ j → c ∈ S

def Diag1 (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F) : Prop := ∀ i, M i i = 1

lemma Pat.lower {S : Set ℕ} {M : Matrix (Fin (d + 1)) (Fin (d + 1)) F} (h : Pat S M)
    {i j : Fin (d + 1)} (hij : j < i) : M i j = 0 := by
  by_contra hne
  exact absurd (h i j (ne_of_gt hij) hne).1 (not_lt.2 hij.le)

lemma pat_mul {S : Set ℕ} {M N : Matrix (Fin (d + 1)) (Fin (d + 1)) F}
    (hM : Pat S M) (hN : Pat S N) (dM : Diag1 M) (dN : Diag1 N) :
    Pat S (M * N) ∧ Diag1 (M * N) := by
  refine ⟨fun i j hij hne => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply] at hne
    obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have h1 : M i k ≠ 0 := left_ne_zero_of_mul hk
    have h2 : N k j ≠ 0 := right_ne_zero_of_mul hk
    by_cases hik : i = k
    · subst hik; exact hN i j hij h2
    by_cases hkj : k = j
    · subst hkj; exact hM i k hik h1
    obtain ⟨a1, a2⟩ := hM i k hik h1
    obtain ⟨b1, b2⟩ := hN k j hkj h2
    refine ⟨a1.trans b1, fun c hc1 hc2 => ?_⟩
    by_cases hc : c ≤ (k : ℕ)
    · exact a2 c hc1 hc
    · exact b2 c (by omega) hc2
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [dM i, dN i]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · simp [hM.lower h]
      · simp [hN.lower h]
    · simp

lemma pat_transvection {S : Set ℕ} (i j : Fin (d + 1)) (hij : i < j)
    (hS : ∀ c : ℕ, (i : ℕ) < c → c ≤ j → c ∈ S) (c : F) :
    Pat S (transvection i j c) ∧ Diag1 (transvection i j c) := by
  refine ⟨fun a b hab hne => ?_, fun a => ?_⟩
  · simp only [transvection, Matrix.add_apply, Matrix.one_apply, hab, if_false, zero_add,
      Matrix.single_apply] at hne
    split_ifs at hne with h
    · obtain ⟨rfl, rfl⟩ := h; exact ⟨hij, hS⟩
    · exact absurd rfl hne
  · simp [transvection, Matrix.single_apply]
    intro h1 h2; subst h1; subst h2; exact absurd hij (lt_irrefl _)

lemma ss0 {i j k l : Fin (d + 1)} (h : j ≠ k) (a b : F) :
    (Matrix.single i j a : Matrix (Fin (d + 1)) (Fin (d + 1)) F) * Matrix.single k l b = 0 := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun z _ => ?_
  split_ifs with h1 h2 <;> first | (exfalso; exact h (h1.2.trans h2.1.symm)) | simp

lemma tv_mul (i j : Fin (d + 1)) (hij : i ≠ j) (a b : F) :
    (transvection i j a : Matrix (Fin (d + 1)) (Fin (d + 1)) F) * transvection i j b =
      transvection i j (a + b) := by
  simp only [transvection, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    ss0 (Ne.symm hij), add_zero, Matrix.single_add]
  abel

lemma pat_of_mem_UL {S : Finset ℕ} {g : SLd d F} (hg : g ∈ UL d F S) :
    Pat (S : Set ℕ) (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) ∧
      Diag1 (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) := by
  induction hg using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨lam, i, j, hjS, -, hij, hx⟩ := hx
    rw [hx]
    exact pat_transvection i j (Fin.lt_def.2 (by omega))
      (fun c h1 h2 => by have : c = j := by omega
                         subst this; exact hjS) lam
  | inv_mem x hx =>
    obtain ⟨lam, i, j, hjS, -, hij, hx⟩ := hx
    have hne : i ≠ j := fun h => by subst h; omega
    have : ((x⁻¹ : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) = transvection i j (-lam) := by
      have h1 : (x : Matrix (Fin (d + 1)) (Fin (d + 1)) F) * transvection i j (-lam) = 1 := by
        rw [hx, tv_mul i j hne]; simp [transvection]
      have : x⁻¹ = (⟨transvection i j (-lam), det_transvection_of_ne _ _ hne _⟩ : SLd d F) := by
        exact inv_eq_of_mul_eq_one_right (Subtype.ext h1)
      rw [this]
    rw [this]
    exact pat_transvection i j (Fin.lt_def.2 (by omega))
      (fun c h1 h2 => by have : c = j := by omega
                         subst this; exact hjS) _
  | one => exact ⟨fun i j hij hne => absurd (by simp [hij]) hne, fun i => by simp⟩
  | mul x y _ _ hx hy =>
    have e : ((x * y : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) =
        (x : Matrix (Fin (d + 1)) (Fin (d + 1)) F) * y := rfl
    rw [e]
    exact pat_mul hx.1 hy.1 hx.2 hy.2

lemma comm_identity {A : Type*} [Ring A] (E F : A) (hEE : E * E = 0) (hFF : F * F = 0)
    (hFE : F * E = 0) : (1 + E) * (1 + F) * (1 + -E) * (1 + -F) = 1 + E * F := by
  have h1 : E * F * E = 0 := by rw [mul_assoc, hFE, mul_zero]
  have h2 : E * F * F = 0 := by rw [mul_assoc, hFF, mul_zero]
  simp only [add_mul, mul_add, one_mul, mul_one, mul_neg, neg_mul, hEE, hFF, hFE, h1, h2,
    add_zero]
  abel

lemma transvection_mem_UL {S : Finset ℕ} :
    ∀ (k : ℕ) (i j : Fin (d + 1)) (c : F), (j : ℕ) = i + k + 1 →
      (∀ c' : ℕ, (i : ℕ) < c' → c' ≤ j → c' ∈ S) →
      ∀ g : SLd d F, (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) = transvection i j c →
        g ∈ UL d F S := by
  intro k
  induction k with
  | zero =>
    intro i j c hj hS g hg
    exact Subgroup.subset_closure ⟨c, i, j, hS j (by omega) le_rfl, by omega, by omega, hg⟩
  | succ k ih =>
    intro i j c hj hS g hg
    let m : Fin (d + 1) := ⟨i + k + 1, by omega⟩
    have him : i ≠ m := fun h => by
      have := congrArg Fin.val h; simp only [m] at this; omega
    have hmj : m ≠ j := fun h => by
      have := congrArg Fin.val h; simp only [m] at this; omega
    have hij : i ≠ j := fun h => by subst h; omega
    let e1 : SLd d F := ⟨transvection i m c, det_transvection_of_ne _ _ him _⟩
    let e2 : SLd d F := ⟨transvection m j 1, det_transvection_of_ne _ _ hmj _⟩
    let e3 : SLd d F := ⟨transvection i m (-c), det_transvection_of_ne _ _ him _⟩
    let e4 : SLd d F := ⟨transvection m j (-1), det_transvection_of_ne _ _ hmj _⟩
    have h1 : e1 ∈ UL d F S := ih i m c (by simp [m]) (fun c' h1 h2 => hS c' h1 (by
      simp [m] at h2; omega)) e1 rfl
    have h3 : e3 ∈ UL d F S := ih i m (-c) (by simp [m]) (fun c' h1 h2 => hS c' h1 (by
      simp [m] at h2; omega)) e3 rfl
    have h2 : e2 ∈ UL d F S := Subgroup.subset_closure
      ⟨1, m, j, hS j (by omega) le_rfl, by omega, by simp only [m]; omega, rfl⟩
    have h4 : e4 ∈ UL d F S := Subgroup.subset_closure
      ⟨-1, m, j, hS j (by omega) le_rfl, by omega, by simp only [m]; omega, rfl⟩
    have hprod : g = e1 * e2 * e3 * e4 := by
      apply Subtype.ext
      show (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) = transvection i m c * transvection m j 1 *
        transvection i m (-c) * transvection m j (-1)
      rw [hg]
      simp only [transvection]
      have hn1 : Matrix.single i m (-c) = -Matrix.single i m c := by
        ext a b; simp only [Matrix.single_apply, Matrix.neg_apply]; split_ifs <;> simp
      have hn2 : Matrix.single m j (-1 : F) = -Matrix.single m j 1 := by
        ext a b; simp only [Matrix.single_apply, Matrix.neg_apply]; split_ifs <;> simp
      rw [hn1, hn2, comm_identity _ _ (ss0 (Ne.symm him) _ _) (ss0 (Ne.symm hmj) _ _)
        (ss0 (Ne.symm hij) _ _), single_mul_single_same, mul_one]
    rw [hprod]
    exact mul_mem (mul_mem (mul_mem h1 h2) h3) h4

lemma det_of_pat {S : Set ℕ} {M : Matrix (Fin (d + 1)) (Fin (d + 1)) F} (h : Pat S M)
    (hd : Diag1 M) : M.det = 1 := by
  have hU : M.IsUpperTriangular := fun i j hij => h.lower hij
  rw [Matrix.det_of_isUpperTriangular hU]
  exact Finset.prod_eq_one fun i _ => hd i

theorem mem_UL_of_pat {S : Finset ℕ} :
    ∀ g : SLd d F, Pat (S : Set ℕ) (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) →
      Diag1 (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) → g ∈ UL d F S := by
  intro g
  generalize hN : (Finset.univ.filter (fun p : Fin (d + 1) × Fin (d + 1) =>
    p.1 ≠ p.2 ∧ (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) p.1 p.2 ≠ 0)).card = N
  induction N using Nat.strong_induction_on generalizing g with
  | _ N ih =>
    intro hg hdg
    set Mg := (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) with hMg
    set Sx := Finset.univ.filter
      (fun p : Fin (d + 1) × Fin (d + 1) => p.1 ≠ p.2 ∧ Mg p.1 p.2 ≠ 0) with hSx
    by_cases hne : Sx.Nonempty
    · obtain ⟨⟨a, b⟩, hp, hmin⟩ := Sx.exists_min_image (fun p => p.2) hne
      simp only [hSx, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨hab, hrun⟩ := hg a b hp.1 hp.2
      set c := Mg a b with hc
      have hcol : ∀ i, i ≠ a → Mg i a = 0 := by
        intro i hi
        by_contra h
        have := hmin (i, a) (by simp [hSx, hi, h])
        exact absurd hab (not_lt.2 this)
      have hab' : a ≠ b := ne_of_lt hab
      let t : SLd d F := ⟨transvection a b (-c), det_transvection_of_ne _ _ hab' _⟩
      let ti : SLd d F := ⟨transvection a b c, det_transvection_of_ne _ _ hab' _⟩
      have hti : ti ∈ UL d F S := transvection_mem_UL ((b : ℕ) - a - 1) a b c (by omega)
        (fun c' h1 h2 => hrun c' h1 h2) ti rfl
      have hgt_mat : ∀ i j, ((g * t : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) i j =
          if i = a ∧ j = b then 0 else Mg i j := by
        intro i j
        show (Mg * transvection a b (-c)) i j = _
        rw [transvection, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply]
        simp only [Matrix.single_apply, mul_ite, mul_zero]
        rw [Finset.sum_eq_single a]
        · by_cases hj : j = b
          · subst hj
            by_cases hi : i = a
            · subst hi; simp [hdg i, hc]
            · simp [hcol i hi, hi]
          · simp [Ne.symm hj, hj]
        · intro k _ hk; simp [Ne.symm hk]
        · simp
      have htti : t * ti = 1 := by
        apply Subtype.ext
        show transvection a b (-c) * transvection a b c = 1
        rw [tv_mul a b hab']; simp [transvection]
      have hg_eq : g = (g * t) * ti := by rw [mul_assoc, htti, mul_one]
      rw [hg_eq]
      refine mul_mem ?_ hti
      have hS' : Finset.univ.filter (fun p : Fin (d + 1) × Fin (d + 1) => p.1 ≠ p.2 ∧
          ((g * t : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) p.1 p.2 ≠ 0) =
          Sx.erase (a, b) := by
        ext ⟨i, j⟩
        simp only [hgt_mat i j, hSx, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_erase, ne_eq, Prod.mk.injEq]
        by_cases h : i = a ∧ j = b
        · simp [h]
        · simp [h]
      refine ih _ ?_ (g * t) rfl ?_ ?_
      · rw [hS', ← hN]
        exact Finset.card_erase_lt_of_mem (by simpa [hSx, hp.1] using hp.2)
      · intro i j hij hne'
        rw [hgt_mat] at hne'
        split_ifs at hne' with h
        · exact absurd rfl hne'
        · exact hg i j hij hne'
      · intro i
        rw [hgt_mat]
        split_ifs with h
        · exact absurd (h.1.symm.trans h.2) hab'
        · exact hdg i
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      have : g = 1 := by
        apply Subtype.ext
        ext i j
        show Mg i j = (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) F) i j
        rw [Matrix.one_apply]
        by_cases hij : i = j
        · subst hij; simp [hdg i]
        · simp only [hij, if_false]
          by_contra h
          have : (i, j) ∈ Sx := by simp [hSx, hij, h]
          rw [hne] at this
          simp at this
      rw [this]; exact one_mem _

/-! ### Elementary matrices with natural-number indices -/

lemma sl_ext {A B : SLd d F}
    (h : (A : Matrix (Fin (d + 1)) (Fin (d + 1)) F) = B) : A = B := Subtype.ext h

lemma coe_mul' (A B : SLd d F) : ((A * B : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) =
    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) F) * B := rfl

lemma coe_one' : ((1 : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) = 1 := rfl

def tvS {d : ℕ} {F : Type*} [Field F] (i j : Fin (d + 1)) (h : i ≠ j) (l : F) : SLd d F :=
  ⟨transvection i j l, det_transvection_of_ne _ _ h _⟩

def E (d : ℕ) {F : Type*} [Field F] (i j : ℕ) (l : F) : SLd d F :=
  if h : i < d + 1 ∧ j < d + 1 ∧ i ≠ j then
    tvS ⟨i, h.1⟩ ⟨j, h.2.1⟩ (fun e => h.2.2 (congrArg Fin.val e)) l
  else 1

lemma E_coe {i j : ℕ} (hi : i < d + 1) (hj : j < d + 1) (hij : i ≠ j) (l : F) :
    ((E d i j l : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) =
      transvection ⟨i, hi⟩ ⟨j, hj⟩ l := by
  unfold E; rw [dif_pos ⟨hi, hj, hij⟩]; rfl

lemma E_invalid {i j : ℕ} (h : ¬ (i < d + 1 ∧ j < d + 1 ∧ i ≠ j)) (l : F) : E d i j l = 1 := by
  unfold E; rw [dif_neg h]

lemma E_add (i j : ℕ) (a b : F) : E d i j (a + b) = E d i j a * E d i j b := by
  by_cases h : i < d + 1 ∧ j < d + 1 ∧ i ≠ j
  · apply sl_ext
    rw [coe_mul', E_coe h.1 h.2.1 h.2.2, E_coe h.1 h.2.1 h.2.2,
      E_coe h.1 h.2.1 h.2.2, tv_mul _ _ (fun e => h.2.2 (congrArg Fin.val e))]
  · rw [E_invalid h, E_invalid h, E_invalid h, mul_one]

lemma E_zero (i j : ℕ) : E d i j (0 : F) = 1 := by
  by_cases h : i < d + 1 ∧ j < d + 1 ∧ i ≠ j
  · apply sl_ext
    rw [E_coe h.1 h.2.1 h.2.2, transvection_zero, coe_one']
  · exact E_invalid h 0

lemma E_neg (i j : ℕ) (a : F) : E d i j (-a) = (E d i j a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← E_add, neg_add_cancel, E_zero])

lemma E_isAdd (i j : ℕ) : IsAdd (fun l : F => E d i j l) := fun a b => E_add i j a b

lemma E_comm {i j k l : ℕ} (hjk : j ≠ k) (hil : i ≠ l) (a b : F) :
    Commute (E d i j a) (E d k l b) := by
  by_cases h1 : i < d + 1 ∧ j < d + 1 ∧ i ≠ j
  swap; · rw [E_invalid h1]; exact Commute.one_left _
  by_cases h2 : k < d + 1 ∧ l < d + 1 ∧ k ≠ l
  swap; · rw [E_invalid h2]; exact Commute.one_right _
  unfold Commute SemiconjBy
  apply sl_ext
  simp only [coe_mul']
  rw [E_coe h1.1 h1.2.1 h1.2.2, E_coe h2.1 h2.2.1 h2.2.2]
  have e1 : (Matrix.single (⟨i, h1.1⟩ : Fin (d + 1)) (⟨j, h1.2.1⟩ : Fin (d + 1)) a) *
      Matrix.single (⟨k, h2.1⟩ : Fin (d + 1)) (⟨l, h2.2.1⟩ : Fin (d + 1)) b = 0 :=
    ss0 (fun e => hjk (congrArg Fin.val e)) _ _
  have e2 : (Matrix.single (⟨k, h2.1⟩ : Fin (d + 1)) (⟨l, h2.2.1⟩ : Fin (d + 1)) b) *
      Matrix.single (⟨i, h1.1⟩ : Fin (d + 1)) (⟨j, h1.2.1⟩ : Fin (d + 1)) a = 0 :=
    ss0 (fun e => hil (congrArg Fin.val e).symm) _ _
  simp only [transvection, add_mul, mul_add, one_mul, mul_one, e1, e2, add_zero]
  abel

lemma E_cm {i j k : ℕ} (hi : i < d + 1) (hj : j < d + 1) (hk : k < d + 1) (hij : i ≠ j)
    (hjk : j ≠ k) (hik : i ≠ k) (a b : F) :
    cm (E d i j a) (E d j k b) = E d i k (a * b) := by
  unfold cm
  rw [← E_neg, ← E_neg]
  apply sl_ext
  simp only [coe_mul']
  rw [E_coe hi hj hij, E_coe hj hk hjk, E_coe hi hj hij, E_coe hj hk hjk, E_coe hi hk hik]
  simp only [transvection]
  rw [← single_neg, ← single_neg, comm_identity _ _ (ss0 (fun e => hij (congrArg Fin.val e).symm) _ _)
    (ss0 (fun e => hjk (congrArg Fin.val e).symm) _ _)
    (ss0 (fun e => hik (congrArg Fin.val e).symm) _ _), single_mul_single_same]

lemma UL_mono {S T : Finset ℕ} (h : T ⊆ S) : UL d F T ≤ UL d F S := by
  unfold UL; apply Subgroup.closure_mono
  rintro g ⟨lam, i, j, hj, h1, h2, h3⟩; exact ⟨lam, i, j, h hj, h1, h2, h3⟩

lemma E_mem_UL {T : Finset ℕ} {i j : ℕ} (hij : i < j) (hT : ∀ c, i < c → c ≤ j → c ∈ T)
    (l : F) : E d i j l ∈ UL d F T := by
  by_cases hj : j < d + 1
  · exact transvection_mem_UL (j - i - 1) ⟨i, by omega⟩ ⟨j, hj⟩ l (by simp; omega) hT _
      (E_coe _ _ (by omega) l)
  · rw [E_invalid (by omega)]; exact one_mem _

/-- The root element `x_c(l) = e_{c-1,c}(l)` (trivial for degenerate colours). -/
def xc (d : ℕ) {F : Type*} [Field F] (c : ℕ) (l : F) : SLd d F := E d (c - 1) c l

lemma xc_mem {T : Finset ℕ} {c : ℕ} (hc : c ∈ T) (l : F) : xc d c l ∈ UL d F T := by
  unfold xc
  rcases Nat.eq_zero_or_pos c with h | h
  · subst h; rw [E_invalid (by omega)]; exact one_mem _
  · exact E_mem_UL (by omega) (fun c' h1 h2 => by
      have : c' = c := by omega
      subst this; exact hc) l

lemma xc_degen {c : ℕ} (h : c = 0 ∨ d < c) (l : F) : xc d c l = 1 := E_invalid (by omega) l

lemma xc_comm {c c' : ℕ} (h1 : c + 1 < c') (a b : F) : Commute (xc d c a) (xc d c' b) := by
  unfold xc; exact E_comm (by omega) (by omega) a b

lemma UL_eq_closure (T : Finset ℕ) :
    UL d F T = Subgroup.closure {g | ∃ c ∈ T, ∃ l : F, g = xc d c l} := by
  apply le_antisymm
  · unfold UL; rw [Subgroup.closure_le]
    rintro g ⟨lam, i, j, hjT, hj1, hij, hg⟩
    apply Subgroup.subset_closure
    refine ⟨j, hjT, lam, Subtype.ext ?_⟩
    rw [hg]; unfold xc; rw [E_coe (by omega) j.isLt (by omega)]
    congr 1; ext; simp; omega
  · rw [Subgroup.closure_le]; rintro g ⟨c, hc, l, rfl⟩; exact xc_mem hc l

theorem UL_induction {T : Finset ℕ} {p : SLd d F → Prop} (one : p 1)
    (gen : ∀ c ∈ T, ∀ l, p (xc d c l))
    (mul : ∀ u ∈ UL d F T, ∀ v ∈ UL d F T, p u → p v → p (u * v))
    (inv : ∀ u ∈ UL d F T, p u → p u⁻¹) : ∀ u ∈ UL d F T, p u := by
  intro u hu
  rw [UL_eq_closure] at hu mul inv
  induction hu using Subgroup.closure_induction with
  | mem x hx => obtain ⟨c, hc, l, rfl⟩ := hx; exact gen c hc l
  | one => exact one
  | mul x y hx hy ihx ihy => exact mul x hx y hy ihx ihy
  | inv x hx ih => exact inv x hx ih

lemma UL_disjoint {T1 T2 : Finset ℕ} (hd : Disjoint T1 T2) {u : SLd d F}
    (h1 : u ∈ UL d F T1) (h2 : u ∈ UL d F T2) : u = 1 := by
  obtain ⟨p1, dg⟩ := pat_of_mem_UL h1
  obtain ⟨p2, -⟩ := pat_of_mem_UL h2
  apply sl_ext; ext i j
  rw [coe_one']
  by_cases hij : i = j
  · subst hij; rw [dg i, one_apply_eq]
  · rw [one_apply_ne hij]; by_contra hne
    obtain ⟨hlt, hS1⟩ := p1 i j hij hne
    obtain ⟨-, hS2⟩ := p2 i j hij hne
    exact Finset.disjoint_left.1 hd (hS1 j hlt le_rfl) (hS2 j hlt le_rfl)

/-- Off-diagonal entries vanish outside column `c`. -/
def ColP (c : ℕ) (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F) : Prop :=
  ∀ i j : Fin (d + 1), i ≠ j → (j : ℕ) ≠ c → M i j = 0

lemma col_split {T : Finset ℕ} {c : ℕ} (hc : c ∉ T) {u w : SLd d F} (hu : u ∈ UL d F T)
    (hw : ColP c (w : Matrix (Fin (d + 1)) (Fin (d + 1)) F))
    (hwd : Diag1 (w : Matrix (Fin (d + 1)) (Fin (d + 1)) F)) (h : u * w = 1) : u = 1 := by
  obtain ⟨pu, du⟩ := pat_of_mem_UL hu
  apply sl_ext; ext i j
  rw [coe_one']
  by_cases hj : (j : ℕ) = c
  · by_cases hij : i = j
    · subst hij; rw [du i, one_apply_eq]
    · rw [one_apply_ne hij]; by_contra hne
      obtain ⟨hlt, hT⟩ := pu i j hij hne
      exact hc (hj ▸ hT j hlt le_rfl)
  · have := congrArg (fun M : SLd d F => (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F) i j) h
    simp only [coe_mul', coe_one'] at this
    rw [Matrix.mul_apply, Finset.sum_eq_single j] at this
    · rwa [hwd j, mul_one] at this
    · intro k _ hk; rw [hw k j hk hj, mul_zero]
    · simp

end Mat

/-! ### Compatible families and extensions -/

section Ext
set_option linter.unusedSectionVars false

variable {d : ℕ} {F : Type*} [Field F]

def lf {G : Type*} [Group G] (y : ℕ → F → G) : FreeGroup (ℕ × F) →* G :=
  FreeGroup.lift (fun p => y p.1 p.2)

@[simp] lemma lf_of {G : Type*} [Group G] (y : ℕ → F → G) (c : ℕ) (l : F) :
    lf y (FreeGroup.of (c, l)) = y c l := by simp [lf]

/-- Words in the letters of colours `c` and `c'`. -/
def Wd (F : Type*) (c c' : ℕ) : Subgroup (FreeGroup (ℕ × F)) :=
  Subgroup.closure {w | ∃ l : F, w = FreeGroup.of (c, l) ∨ w = FreeGroup.of (c', l)}

lemma of_mem_Wd_left (c c' : ℕ) (l : F) : FreeGroup.of (c, l) ∈ Wd F c c' :=
  Subgroup.subset_closure ⟨l, Or.inl rfl⟩

lemma of_mem_Wd_right (c c' : ℕ) (l : F) : FreeGroup.of (c', l) ∈ Wd F c c' :=
  Subgroup.subset_closure ⟨l, Or.inr rfl⟩

/-- `y` satisfies every rank-`≤ 2` relation of the root elements of colours in `S`. -/
def Compat (d : ℕ) (S : Finset ℕ) {G : Type*} [Group G] (y : ℕ → F → G) : Prop :=
  ∀ c ∈ S, ∀ c' ∈ S, ∀ w ∈ Wd F c c', lf (xc d) w = 1 → lf y w = 1

variable {G : Type*} [Group G] {S : Finset ℕ} {y : ℕ → F → G}

lemma Compat.mono (h : Compat d S y) {T : Finset ℕ} (hT : T ⊆ S) : Compat d T y :=
  fun c hc c' hc' => h c (hT hc) c' (hT hc')

lemma Compat.eq (h : Compat d S y) {c c' : ℕ} (hc : c ∈ S) (hc' : c' ∈ S)
    {w1 w2 : FreeGroup (ℕ × F)} (h1 : w1 ∈ Wd F c c') (h2 : w2 ∈ Wd F c c')
    (he : lf (xc d) w1 = lf (xc d) w2) : lf y w1 = lf y w2 := by
  have := h c hc c' hc' (w1 * w2⁻¹) (mul_mem h1 (inv_mem h2))
    (by rw [map_mul, map_inv, he, mul_inv_cancel])
  rwa [map_mul, map_inv, mul_inv_eq_one] at this

lemma Compat.add (h : Compat d S y) {c : ℕ} (hc : c ∈ S) (a b : F) :
    y c (a + b) = y c a * y c b := by
  have := h.eq hc hc (of_mem_Wd_left c c (a + b))
    (mul_mem (of_mem_Wd_left c c a) (of_mem_Wd_left c c b))
    (by rw [map_mul, lf_of, lf_of, lf_of]; exact E_add _ _ a b)
  rwa [map_mul, lf_of, lf_of, lf_of] at this

lemma Compat.isAdd (h : Compat d S y) {c : ℕ} (hc : c ∈ S) : IsAdd (fun l => y c l) :=
  fun a b => h.add hc a b

lemma Compat.comm (h : Compat d S y) {c c' : ℕ} (hc : c ∈ S) (hc' : c' ∈ S) {a b : F}
    (hx : Commute (xc d c a) (xc d c' b)) : Commute (y c a) (y c' b) := by
  have := h.eq hc hc' (mul_mem (of_mem_Wd_left c c' a) (of_mem_Wd_right c c' b))
    (mul_mem (of_mem_Wd_right c c' b) (of_mem_Wd_left c c' a))
    (by rw [map_mul, map_mul, lf_of, lf_of]; exact hx.eq)
  rw [map_mul, map_mul, lf_of, lf_of] at this
  exact this

lemma Compat.degen (h : Compat d S y) {c : ℕ} (hc : c ∈ S) {l : F} (hx : xc d c l = 1) :
    y c l = 1 := by
  have := h c hc c hc _ (of_mem_Wd_left c c l) (by rw [lf_of]; exact hx)
  rwa [lf_of] at this

/-- `f` extends `y` to a homomorphism on `U_S`. -/
structure IsExt (d : ℕ) (S : Finset ℕ) {G : Type*} [Group G] (y : ℕ → F → G)
    (f : SLd d F → G) : Prop where
  mul : ∀ u ∈ UL d F S, ∀ v ∈ UL d F S, f (u * v) = f u * f v
  gen : ∀ c ∈ S, ∀ l, f (xc d c l) = y c l

lemma eq_one_of_eq_mul_self {a : G} (h : a = a * a) : a = 1 :=
  (mul_left_cancel (h.symm.trans (mul_one a).symm))

variable {f : SLd d F → G}

lemma IsExt.one (h : IsExt d S y f) : f 1 = 1 :=
  eq_one_of_eq_mul_self (by rw [← h.mul 1 (one_mem _) 1 (one_mem _), mul_one])

lemma IsExt.inv (h : IsExt d S y f) {u : SLd d F} (hu : u ∈ UL d F S) : f u⁻¹ = (f u)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← h.mul _ (inv_mem hu) _ hu, inv_mul_cancel, h.one])

lemma IsExt.mono (h : IsExt d S y f) {T : Finset ℕ} (hT : T ⊆ S) : IsExt d T y f :=
  ⟨fun u hu v hv => h.mul u (UL_mono hT hu) v (UL_mono hT hv), fun c hc => h.gen c (hT hc)⟩

lemma IsExt.ext (h1 : IsExt d S y f) {f' : SLd d F → G} (h2 : IsExt d S y f') :
    ∀ u ∈ UL d F S, f u = f' u :=
  UL_induction (by rw [h1.one, h2.one]) (fun c hc l => by rw [h1.gen c hc, h2.gen c hc])
    (fun u hu v hv eu ev => by rw [h1.mul u hu v hv, h2.mul u hu v hv, eu, ev])
    (fun u hu e => by rw [h1.inv hu, h2.inv hu, e])

lemma IsExt.retract (h : IsExt d S y f) (π : G →* SLd d F)
    (hπ : ∀ c ∈ S, ∀ l, π (y c l) = xc d c l) : ∀ u ∈ UL d F S, π (f u) = u :=
  IsExt.ext (f := fun u => π (f u)) (f' := id) (y := xc d)
    ⟨fun u hu v hv => by simp only [h.mul u hu v hv, map_mul],
      fun c hc l => by simp only [h.gen c hc, hπ c hc]⟩
    ⟨fun u _ v _ => rfl, fun _ _ _ => rfl⟩

lemma IsExt.commute (h : IsExt d S y f) {T : Finset ℕ} (hT : T ⊆ S) (g : G)
    (hg : ∀ e ∈ T, ∀ l, Commute (y e l) g) : ∀ u ∈ UL d F T, Commute (f u) g :=
  UL_induction (by rw [h.one]; exact Commute.one_left g)
    (fun c hc l => by rw [h.gen c (hT hc)]; exact hg c hc l)
    (fun u hu v hv eu ev => by rw [h.mul u (UL_mono hT hu) v (UL_mono hT hv)]; exact eu.mul_left ev)
    (fun u hu e => by rw [h.inv (UL_mono hT hu)]; exact e.inv_left)

lemma IsExt.map_cm (h : IsExt d S y f) {u v : SLd d F} (hu : u ∈ UL d F S)
    (hv : v ∈ UL d F S) : f (cm u v) = cm (f u) (f v) := by
  unfold cm
  rw [h.mul _ (mul_mem (mul_mem hu hv) (inv_mem hu)) _ (inv_mem hv),
    h.mul _ (mul_mem hu hv) _ (inv_mem hu), h.mul _ hu _ hv, h.inv hu, h.inv hv]

lemma IsExt.map_comm (h : IsExt d S y f) {u v : SLd d F} (hu : u ∈ UL d F S)
    (hv : v ∈ UL d F S) (hc : Commute u v) : Commute (f u) (f v) := by
  unfold Commute SemiconjBy; rw [← h.mul _ hu _ hv, ← h.mul _ hv _ hu, hc.eq]

end Ext


/-! ### Column matrices -/

section Col

variable {d : ℕ} {F : Type*} [Field F]

lemma col_mul_xc {c : ℕ} (hc1 : 1 ≤ c) (hcd : c ≤ d) {v : SLd d F}
    (hv : ColP c (v : Matrix (Fin (d + 1)) (Fin (d + 1)) F)) (μ : F) :
    ColP c ((v * xc d c μ : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) := by
  intro i j hij hj
  rw [coe_mul', show xc d c μ = E d (c - 1) c μ from rfl, E_coe (by omega) (by omega) (by omega),
    mul_transvection_apply_of_ne _ _ _ _ (fun e => hj (congrArg Fin.val e))]
  exact hv i j hij hj

lemma col_conj_mat {c : ℕ} (p q : Fin (d + 1)) (hpq : p < q) (hpc : (p : ℕ) ≠ c)
    (hqc : (q : ℕ) ≠ c) (V : Matrix (Fin (d + 1)) (Fin (d + 1)) F) (hv : ColP c V)
    (dv : Diag1 V) (lv : V q p = 0) (μ : F) :
    ColP c (transvection p q (-μ) * V * transvection p q μ) := by
  intro i j hij hj
  have hpq' : p ≠ q := ne_of_lt hpq
  by_cases hjq : j = q
  · subst hjq
    rw [mul_transvection_apply_same]
    by_cases hip : i = p
    · subst hip
      rw [transvection_mul_apply_same, transvection_mul_apply_same, hv i j hpq' hqc, dv j, dv i,
        lv]; ring
    · rw [transvection_mul_apply_of_ne _ _ _ _ hip, transvection_mul_apply_of_ne _ _ _ _ hip,
        hv i j hij hqc, hv i p hip hpc]; ring
  · rw [mul_transvection_apply_of_ne _ _ _ _ hjq]
    by_cases hip : i = p
    · subst hip
      rw [transvection_mul_apply_same, hv i j hij hj, hv q j (Ne.symm hjq) hj]; ring
    · rw [transvection_mul_apply_of_ne _ _ _ _ hip]; exact hv i j hij hj

lemma col_conj {T : Finset ℕ} {c e : ℕ} (he1 : 1 ≤ e) (hec : e < c) (hcd : c ≤ d)
    {v : SLd d F} (hvT : v ∈ UL d F T) (hv : ColP c (v : Matrix (Fin (d + 1)) (Fin (d + 1)) F))
    (μ : F) :
    ColP c ((xc d e (-μ) * v * xc d e μ : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) := by
  obtain ⟨pv, dv⟩ := pat_of_mem_UL hvT
  rw [coe_mul', coe_mul', show xc d e (-μ) = E d (e - 1) e (-μ) from rfl,
    show xc d e μ = E d (e - 1) e μ from rfl, E_coe (by omega) (by omega) (by omega),
    E_coe (by omega) (by omega) (by omega)]
  exact col_conj_mat _ _ (Fin.lt_def.2 (by simp; omega)) (by simp; omega) (by simp; omega) _ hv
    dv (pv.lower (Fin.lt_def.2 (by simp; omega))) μ

lemma col_peel_mat {a c : ℕ} (p q : Fin (d + 1)) (hp : (p : ℕ) = a + 1) (hq : (q : ℕ) = c)
    (hpq : p < q) (V : Matrix (Fin (d + 1)) (Fin (d + 1)) F)
    (pv : Pat (↑(Finset.Icc (a + 2) c) : Set ℕ) V) (dv : Diag1 V) (hv : ColP c V) :
    Pat (↑(Finset.Icc (a + 3) c) : Set ℕ) (transvection p q (-V p q) * V) ∧
      Diag1 (transvection p q (-V p q) * V) := by
  constructor
  · intro i j hij hne
    by_cases hip : i = p
    · subst hip
      exfalso; apply hne
      rw [transvection_mul_apply_same]
      by_cases hjq : j = q
      · subst hjq; rw [dv j]; ring
      · have hjc : (j : ℕ) ≠ c := fun e => hjq (Fin.ext (e.trans hq.symm))
        rw [hv i j hij hjc, hv q j (Ne.symm hjq) hjc]; ring
    · rw [transvection_mul_apply_of_ne _ _ _ _ hip] at hne
      obtain ⟨hlt, hS⟩ := pv i j hij hne
      refine ⟨hlt, fun c' h1 h2 => ?_⟩
      have hlt' : (i : ℕ) < j := hlt
      have h3 := hS ((i : ℕ) + 1) (by omega) (by omega)
      have h4 := hS c' h1 h2
      have hi : (i : ℕ) ≠ a + 1 := fun e => hip (Fin.ext (e.trans hp.symm))
      simp only [Finset.coe_Icc, Set.mem_Icc] at h3 h4 ⊢
      omega
  · intro i
    by_cases hip : i = p
    · subst hip; rw [transvection_mul_apply_same, dv i, pv.lower hpq]; ring
    · rw [transvection_mul_apply_of_ne _ _ _ _ hip, dv i]

lemma col_peel {a c : ℕ} (hac : a + 1 < c) (hcd : c ≤ d) {v : SLd d F}
    (hvT : v ∈ UL d F (Finset.Icc (a + 2) c))
    (hv : ColP c (v : Matrix (Fin (d + 1)) (Fin (d + 1)) F)) :
    E d (a + 1) c (-((v : Matrix (Fin (d + 1)) (Fin (d + 1)) F) ⟨a + 1, by omega⟩ ⟨c, by omega⟩)) * v
      ∈ UL d F (Finset.Icc (a + 3) c) := by
  obtain ⟨pv, dv⟩ := pat_of_mem_UL hvT
  have key := col_peel_mat (⟨a + 1, by omega⟩ : Fin (d + 1)) ⟨c, by omega⟩ rfl rfl
    (Fin.lt_def.2 (by simp; omega)) _ pv dv hv
  apply mem_UL_of_pat
  · rw [coe_mul', E_coe (by omega) (by omega) (by omega)]; exact key.1
  · rw [coe_mul', E_coe (by omega) (by omega) (by omega)]; exact key.2

lemma inj_last {a c : ℕ} (hac : a + 3 ≤ c) (hcd : c ≤ d) {u v : SLd d F} {l : F}
    (hu : u ∈ UL d F (Finset.Icc (a + 1) (c - 1))) (hvT : v ∈ UL d F (Finset.Icc (a + 2) c))
    (hv : ColP c (v : Matrix (Fin (d + 1)) (Fin (d + 1)) F)) (h : u * E d a c l * v = 1) :
    u = 1 ∧ l = 0 ∧ v = 1 := by
  obtain ⟨pv, dv⟩ := pat_of_mem_UL hvT
  have hwT : E d a c l * v ∈ UL d F (Finset.Icc (a + 1) c) :=
    mul_mem (E_mem_UL (by omega) (fun c' h1 h2 => Finset.mem_Icc.2 ⟨by omega, h2⟩) l)
      (UL_mono (Finset.Icc_subset_Icc (by omega) le_rfl) hvT)
  have hw : ColP c ((E d a c l * v : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) := by
    rw [coe_mul', E_coe (by omega) (by omega) (by omega)]
    intro i j hij hj
    have hjq : j ≠ (⟨c, by omega⟩ : Fin (d + 1)) := fun e => hj (congrArg Fin.val e)
    by_cases hia : i = ⟨a, by omega⟩
    · subst hia
      rw [transvection_mul_apply_same, hv _ j hij hj, hv _ j (Ne.symm hjq) hj]; ring
    · rw [transvection_mul_apply_of_ne _ _ _ _ hia]; exact hv i j hij hj
  have hu1 : u = 1 := col_split (T := Finset.Icc (a + 1) (c - 1)) (by simp; omega) hu hw
    (pat_of_mem_UL hwT).2 (by rw [← mul_assoc]; exact h)
  subst hu1
  rw [one_mul] at h
  have hne : (⟨a, by omega⟩ : Fin (d + 1)) ≠ ⟨c, by omega⟩ := by simp; omega
  have hvac : (v : Matrix (Fin (d + 1)) (Fin (d + 1)) F) ⟨a, by omega⟩ ⟨c, by omega⟩ = 0 := by
    by_contra hne'
    obtain ⟨-, hS⟩ := pv _ _ hne hne'
    have := hS (a + 1) (by simp) (by simp; omega)
    simp at this
  have hl : l = 0 := by
    have := congrArg (fun M : SLd d F =>
      (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F) ⟨a, by omega⟩ ⟨c, by omega⟩) h
    simp only [coe_mul', coe_one'] at this
    rw [E_coe (by omega) (by omega) (by omega), transvection_mul_apply_same, dv, hvac,
      one_apply_ne hne] at this
    simpa using this
  subst hl
  rw [E_zero, one_mul] at h
  exact ⟨rfl, rfl, h⟩

end Col

/-! ### The induction step -/

section Core

variable {d : ℕ} {F : Type*} [Field F] {P : Type*} [Group P]

lemma closure_right {S : Finset ℕ} {xh : ℕ → F → P} (hcomp : Compat d S xh)
    (hgen : ∀ g : P, g ∈ Subgroup.closure {g | ∃ c ∈ S, ∃ l, g = xh c l})
    (W : P → Prop) (h1 : W 1) (hstep : ∀ g, W g → ∀ c ∈ S, ∀ l, W (g * xh c l)) :
    ∀ g, W g := by
  intro g
  have hg := hgen g
  induction hg using Subgroup.closure_induction_right with
  | one => exact h1
  | mul_right x _ y hy ih =>
    obtain ⟨c, hc, l, rfl⟩ := hy; exact hstep x ih c hc l
  | mul_inv_cancel x _ y hy ih =>
    obtain ⟨c, hc, l, rfl⟩ := hy
    have : xh c (-l) = (xh c l)⁻¹ := (hcomp.isAdd hc).neg l
    rw [← this]; exact hstep x ih c hc (-l)

lemma map_cm' {Q : Type*} [Group Q] (π : P →* Q) (x y : P) : π (cm x y) = cm (π x) (π y) := by
  unfold cm; simp only [map_mul, map_inv]

lemma nf_mid {Au z Bv x : P} (h : Commute x z) : Au * z * Bv * x = Au * x * z * (x⁻¹ * Bv * x) := by
  rw [show Au * x * z * (x⁻¹ * Bv * x) = Au * (x * z * x⁻¹) * Bv * x by group, conj_of_commute h]

theorem core0 {S : Finset ℕ} {xh : ℕ → F → P} (π : P →* SLd d F)
    (hπ : ∀ c ∈ S, ∀ l, π (xh c l) = xc d c l)
    (hgen : ∀ g : P, g ∈ Subgroup.closure {g | ∃ c ∈ S, ∃ l, g = xh c l})
    (hcomp : Compat d S xh) (hS : S.card ≤ 2) : ∀ g, π g = 1 → g = 1 := by
  intro g hg
  rcases S.eq_empty_or_nonempty with h0 | ⟨c, hc⟩
  · have := hgen g
    subst h0
    simpa using this
  obtain ⟨c', hc', hS2⟩ : ∃ c' ∈ S, ∀ e ∈ S, e = c ∨ e = c' := by
    by_cases h1 : (S.erase c).Nonempty
    · obtain ⟨c', hc'⟩ := h1
      refine ⟨c', Finset.mem_of_mem_erase hc', fun e he => ?_⟩
      by_cases hec : e = c
      · exact Or.inl hec
      right
      have hcard : (S.erase c).card ≤ 1 := by rw [Finset.card_erase_of_mem hc]; omega
      exact Finset.card_le_one.1 hcard e (Finset.mem_erase.2 ⟨hec, he⟩) c' hc'
    · refine ⟨c, hc, fun e he => Or.inl ?_⟩
      by_contra hec; exact h1 ⟨e, Finset.mem_erase.2 ⟨hec, he⟩⟩
  have key : ∀ g ∈ Subgroup.closure {g | ∃ c ∈ S, ∃ l, g = xh c l},
      ∃ w ∈ Wd F c c', lf xh w = g ∧ lf (xc d) w = π g := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨e, he, l, rfl⟩ := hx
      refine ⟨FreeGroup.of (e, l), ?_, lf_of _ _ _, by rw [lf_of, hπ e he]⟩
      rcases hS2 e he with rfl | rfl
      · exact of_mem_Wd_left _ _ _
      · exact of_mem_Wd_right _ _ _
    | one => exact ⟨1, one_mem _, map_one _, by rw [map_one, map_one]⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨w1, h1, e1, f1⟩ := ihx
      obtain ⟨w2, h2, e2, f2⟩ := ihy
      exact ⟨w1 * w2, mul_mem h1 h2, by rw [map_mul, e1, e2], by rw [map_mul, map_mul, f1, f2]⟩
    | inv x _ ih =>
      obtain ⟨w, h, e, f⟩ := ih
      exact ⟨w⁻¹, inv_mem h, by rw [map_inv, e], by rw [map_inv, map_inv, f]⟩
  obtain ⟨w, hw, e, f⟩ := key g (hgen g)
  rw [← e]; exact hcomp c hc c' hc' w hw (f.trans hg)

theorem core1 {S : Finset ℕ} {xh : ℕ → F → P} (π : P →* SLd d F)
    (hπ : ∀ c ∈ S, ∀ l, π (xh c l) = xc d c l)
    (hgen : ∀ g : P, g ∈ Subgroup.closure {g | ∃ c ∈ S, ∃ l, g = xh c l})
    (hcomp : Compat d S xh) (IH : ∀ T ⊂ S, ∃ f : SLd d F → P, IsExt d T xh f)
    {k : ℕ} (hk : k ∉ S) {m M : ℕ} (hm : m ∈ S) (hM : M ∈ S) (hmk : m < k) (hkM : k < M) :
    ∀ g, π g = 1 → g = 1 := by
  obtain ⟨f1, hf1⟩ := IH (S.filter (· < k)) (Finset.filter_ssubset.2 ⟨M, hM, by omega⟩)
  obtain ⟨f2, hf2⟩ := IH (S.filter (k < ·)) (Finset.filter_ssubset.2 ⟨m, hm, by omega⟩)
  have hcomm : ∀ e ∈ S.filter (· < k), ∀ u ∈ UL d F (S.filter (k < ·)), ∀ l,
      Commute (f2 u) (xh e l) := by
    intro e he u hu l
    rw [Finset.mem_filter] at he
    refine hf2.commute subset_rfl _ (fun e' he' l' => ?_) u hu
    rw [Finset.mem_filter] at he'
    exact (hcomp.comm he.1 he'.1 (xc_comm (by omega) l l')).symm
  have hW : ∀ g, ∃ u1 ∈ UL d F (S.filter (· < k)), ∃ u2 ∈ UL d F (S.filter (k < ·)),
      g = f1 u1 * f2 u2 := by
    refine closure_right hcomp hgen _ ⟨1, one_mem _, 1, one_mem _, by rw [hf1.one, hf2.one,
      mul_one]⟩ ?_
    rintro g ⟨u1, hu1, u2, hu2, rfl⟩ e he l
    rcases lt_trichotomy e k with h | h | h
    · have he1 : e ∈ S.filter (· < k) := Finset.mem_filter.2 ⟨he, h⟩
      refine ⟨u1 * xc d e l, mul_mem hu1 (xc_mem he1 l), u2, hu2, ?_⟩
      rw [hf1.mul _ hu1 _ (xc_mem he1 l), hf1.gen e he1, mul_assoc, (hcomm e he1 u2 hu2 l).eq,
        ← mul_assoc]
    · exact absurd (h ▸ he) hk
    · have he2 : e ∈ S.filter (k < ·) := Finset.mem_filter.2 ⟨he, h⟩
      refine ⟨u1, hu1, u2 * xc d e l, mul_mem hu2 (xc_mem he2 l), ?_⟩
      rw [hf2.mul _ hu2 _ (xc_mem he2 l), hf2.gen e he2, mul_assoc]
  intro g hg
  obtain ⟨u1, hu1, u2, hu2, rfl⟩ := hW g
  rw [map_mul, hf1.retract π (fun c hc => hπ c (Finset.mem_filter.1 hc).1) u1 hu1,
    hf2.retract π (fun c hc => hπ c (Finset.mem_filter.1 hc).1) u2 hu2] at hg
  have hu1' : u1 = u2⁻¹ := eq_inv_of_mul_eq_one_left hg
  have h1 : u1 = 1 := UL_disjoint (Finset.disjoint_filter.2 (fun x _ h1 h2 => by omega)) hu1
    (hu1' ▸ inv_mem hu2)
  rw [h1, one_mul] at hg
  rw [h1, hg, hf1.one, hf2.one, mul_one]

theorem core2 {S : Finset ℕ} {xh : ℕ → F → P} (π : P →* SLd d F)
    (hπ : ∀ c ∈ S, ∀ l, π (xh c l) = xc d c l)
    (hgen : ∀ g : P, g ∈ Subgroup.closure {g | ∃ c ∈ S, ∃ l, g = xh c l})
    (hcomp : Compat d S xh) (IH : ∀ T ⊂ S, ∃ f : SLd d F → P, IsExt d T xh f)
    (hF : ∃ α α' : F, α ≠ 0 ∧ α' ≠ 0 ∧ α + α' ≠ 0)
    {a c : ℕ} (hS : S = Finset.Icc (a + 1) c) (hac : a + 3 ≤ c) (hcd : c ≤ d) :
    ∀ g, π g = 1 → g = 1 := by
  subst hS
  obtain ⟨A, hA⟩ := IH (Finset.Icc (a + 1) (c - 1)) (by
    rw [Finset.ssubset_iff_of_subset (Finset.Icc_subset_Icc le_rfl (by omega))]
    exact ⟨c, by simp; omega, by simp; omega⟩)
  obtain ⟨B, hB⟩ := IH (Finset.Icc (a + 2) c) (by
    rw [Finset.ssubset_iff_of_subset (Finset.Icc_subset_Icc (by omega) le_rfl)]
    exact ⟨a + 1, by simp; omega, by simp⟩)
  have mS : ∀ e, a + 1 ≤ e → e ≤ c → e ∈ Finset.Icc (a + 1) c :=
    fun e h1 h2 => Finset.mem_Icc.2 ⟨h1, h2⟩
  have mA : ∀ i j, i < j → a ≤ i → j ≤ c - 1 → ∀ l : F,
      E d i j l ∈ UL d F (Finset.Icc (a + 1) (c - 1)) :=
    fun i j hij h1 h2 l => E_mem_UL hij (fun e h3 h4 => Finset.mem_Icc.2 ⟨by omega, by omega⟩) l
  have mB : ∀ i j, i < j → a + 1 ≤ i → j ≤ c → ∀ l : F,
      E d i j l ∈ UL d F (Finset.Icc (a + 2) c) :=
    fun i j hij h1 h2 l => E_mem_UL hij (fun e h3 h4 => Finset.mem_Icc.2 ⟨by omega, by omega⟩) l
  have hAB : ∀ u ∈ UL d F (Finset.Icc (a + 2) (c - 1)), A u = B u :=
    (hA.mono (Finset.Icc_subset_Icc (by omega) le_rfl)).ext
      (hB.mono (Finset.Icc_subset_Icc le_rfl (by omega)))
  have hxA : ∀ e, a + 1 ≤ e → e ≤ c - 1 → ∀ l, xh e l = A (E d (e - 1) e l) := fun e h1 h2 l =>
    (hA.gen e (Finset.mem_Icc.2 ⟨h1, h2⟩) l).symm
  have hxB : ∀ e, a + 2 ≤ e → e ≤ c → ∀ l, xh e l = B (E d (e - 1) e l) := fun e h1 h2 l =>
    (hB.gen e (Finset.mem_Icc.2 ⟨h1, h2⟩) l).symm
  have hx1 : ∀ l, xh (a + 1) l = A (E d a (a + 1) l) := fun l => by
    rw [hxA (a + 1) le_rfl (by omega), Nat.add_sub_cancel]
  have hx3 : ∀ l, xh c l = B (E d (c - 1) c l) := hxB c (by omega) le_rfl
  have hx2 : ∀ l, A (E d (a + 1) (c - 1) l) = B (E d (a + 1) (c - 1) l) := fun l =>
    hAB _ (E_mem_UL (by omega) (fun e h3 h4 => Finset.mem_Icc.2 ⟨by omega, by omega⟩) l)
  have hneg : ∀ e ∈ Finset.Icc (a + 1) c, ∀ μ, xh e (-μ) = (xh e μ)⁻¹ :=
    fun e he μ => (hcomp.isAdd he).neg μ
  obtain ⟨Z1, Z2, Zadd, Zx1, Zx2, Zx3, -, -, -⟩ := a3 (xh (a + 1))
    (fun l => A (E d (a + 1) (c - 1) l)) (xh c) (fun l => A (E d a (c - 1) l))
    (fun l => B (E d (a + 1) c l))
    (hcomp.isAdd (mS _ le_rfl (by omega))) (hcomp.isAdd (mS _ (by omega) le_rfl))
    (fun α β => by
      beta_reduce
      rw [E_add, hA.mul _ (mA a (c - 1) (by omega) le_rfl le_rfl _) _
        (mA a (c - 1) (by omega) le_rfl le_rfl _)])
    (fun α β => by
      beta_reduce
      rw [E_add, hB.mul _ (mB (a + 1) c (by omega) le_rfl le_rfl _) _
        (mB (a + 1) c (by omega) le_rfl le_rfl _)])
    (fun α β => by
      rw [hx1, ← hA.map_cm (mA a (a + 1) (by omega) le_rfl (by omega) _)
        (mA (a + 1) (c - 1) (by omega) (by omega) le_rfl _),
        E_cm (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)])
    (fun γ α => by
      rw [hx1]
      exact hA.map_comm (mA a (c - 1) (by omega) le_rfl le_rfl _)
        (mA a (a + 1) (by omega) le_rfl (by omega) _) (E_comm (by omega) (by omega) _ _))
    (fun γ β => hA.map_comm (mA a (c - 1) (by omega) le_rfl le_rfl _)
        (mA (a + 1) (c - 1) (by omega) (by omega) le_rfl _) (E_comm (by omega) (by omega) _ _))
    (fun β ν => by
      rw [hx2, hx3, ← hB.map_cm (mB (a + 1) (c - 1) (by omega) le_rfl (by omega) _)
        (mB (c - 1) c (by omega) (by omega) le_rfl _),
        E_cm (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)])
    (fun δ β => by
      rw [hx2]
      exact hB.map_comm (mB (a + 1) c (by omega) le_rfl le_rfl _)
        (mB (a + 1) (c - 1) (by omega) le_rfl (by omega) _) (E_comm (by omega) (by omega) _ _))
    (fun δ ν => by
      rw [hx3]
      exact hB.map_comm (mB (a + 1) c (by omega) le_rfl le_rfl _)
        (mB (c - 1) c (by omega) (by omega) le_rfl _) (E_comm (by omega) (by omega) _ _))
    (fun α ν => hcomp.comm (mS _ le_rfl (by omega)) (mS _ (by omega) le_rfl)
      (xc_comm (by omega) _ _))
    hF
  obtain ⟨z, hz⟩ : ∃ z : F → P, ∀ l, z l = cm (xh (a + 1) l) (B (E d (a + 1) c 1)) :=
    ⟨_, fun _ => rfl⟩
  have Z1' : ∀ α δ, cm (xh (a + 1) α) (B (E d (a + 1) c δ)) = z (α * δ) := fun α δ => by
    rw [Z1, hz]
  have Z2' : ∀ γ ν, cm (A (E d a (c - 1) γ)) (xh c ν) = z (γ * ν) := fun γ ν => by
    rw [Z2, hz]
  have zadd : ∀ l l', z (l + l') = z l * z l' := fun l l' => by
    simp only [hz]; exact Zadd l l'
  have z0 : z 0 = 1 := by rw [hz]; exact Zadd.zero
  have zx1 : ∀ l μ, Commute (z l) (xh (a + 1) μ) := fun l μ => by rw [hz]; exact Zx1 l μ
  have zx3 : ∀ l μ, Commute (z l) (xh c μ) := fun l μ => by rw [hz]; exact Zx3 l μ
  have zc : ∀ l, ∀ e ∈ Finset.Icc (a + 1) c, ∀ μ, Commute (z l) (xh e μ) := by
    intro l e he μ
    rw [Finset.mem_Icc] at he
    by_cases e1 : e = a + 1
    · subst e1; exact zx1 l μ
    by_cases e2 : e = c
    · subst e2; exact zx3 l μ
    by_cases e3 : e + 2 ≤ c
    · rw [show z l = cm (A (E d a (c - 1) l)) (xh c 1) by rw [Z2', mul_one]]
      refine (comm_cm ?_ ?_).symm
      · rw [hxA e (by omega) (by omega)]
        exact hA.map_comm (mA (e - 1) e (by omega) (by omega) (by omega) μ)
          (mA a (c - 1) (by omega) le_rfl le_rfl l) (E_comm (by omega) (by omega) _ _)
      · exact hcomp.comm (mS e (by omega) (by omega)) (mS c (by omega) le_rfl)
          (xc_comm (by omega) _ _)
    · obtain rfl : e = c - 1 := by omega
      by_cases e4 : c = a + 3
      · rw [hxA (c - 1) (by omega) le_rfl, show c - 1 - 1 = a + 1 by omega, hz]
        exact Zx2 l μ
      · rw [hz]
        refine (comm_cm ?_ ?_).symm
        · exact (hcomp.comm (mS _ le_rfl (by omega)) (mS (c - 1) (by omega) (by omega))
            (xc_comm (by omega) _ _)).symm
        · rw [hxB (c - 1) (by omega) (by omega)]
          exact hB.map_comm (mB (c - 1 - 1) (c - 1) (by omega) (by omega) (by omega) μ)
            (mB (a + 1) c (by omega) le_rfl le_rfl 1) (E_comm (by omega) (by omega) _ _)
  have hW : ∀ g : P, ∃ u ∈ UL d F (Finset.Icc (a + 1) (c - 1)), ∃ l : F,
      ∃ v ∈ UL d F (Finset.Icc (a + 2) c),
        ColP c (v : Matrix (Fin (d + 1)) (Fin (d + 1)) F) ∧ g = A u * z l * B v := by
    refine closure_right hcomp hgen _ ⟨1, one_mem _, 0, 1, one_mem _, ?_, ?_⟩ ?_
    · intro i j hij _; rw [coe_one', one_apply_ne hij]
    · rw [hA.one, z0, hB.one, mul_one, mul_one]
    rintro g ⟨u, hu, l, v, hv, hcol, rfl⟩ e he μ
    have he' := Finset.mem_Icc.1 he
    by_cases e1 : e = c
    · subst e1
      have hxm : xc d e μ ∈ UL d F (Finset.Icc (a + 2) e) := xc_mem (by simp; omega) μ
      refine ⟨u, hu, l, v * xc d e μ, mul_mem hv hxm, col_mul_xc (by omega) hcd hcol μ, ?_⟩
      rw [hB.mul _ hv _ hxm, hB.gen e (by simp; omega), mul_assoc]
    by_cases e2 : e = a + 1
    · subst e2
      have hv' := col_peel (a := a) (c := c) (by omega) hcd hv hcol
      set m := (v : Matrix (Fin (d + 1)) (Fin (d + 1)) F) ⟨a + 1, by omega⟩ ⟨c, by omega⟩
      have hv'B : E d (a + 1) c (-m) * v ∈ UL d F (Finset.Icc (a + 2) c) :=
        UL_mono (Finset.Icc_subset_Icc (by omega) le_rfl) hv'
      have hBv : B v = B (E d (a + 1) c m) * B (E d (a + 1) c (-m) * v) := by
        rw [← hB.mul _ (mB (a + 1) c (by omega) le_rfl le_rfl m) _ hv'B, ← mul_assoc, ← E_add,
          add_neg_cancel, E_zero, one_mul]
      have hcomm' : Commute (B (E d (a + 1) c (-m) * v)) (xh (a + 1) μ) :=
        hB.commute (Finset.Icc_subset_Icc (by omega) le_rfl) _ (fun e' he' l' => by
          rw [Finset.mem_Icc] at he'
          exact (hcomp.comm (mS _ le_rfl (by omega)) (mS e' (by omega) he'.2)
            (xc_comm (by omega) _ _)).symm) _ hv'
      have hconj : B (E d (a + 1) c m) * xh (a + 1) μ =
          xh (a + 1) μ * (z (-μ * m) * B (E d (a + 1) c m)) := by
        have h1 := conj_eq_cm (xh (a + 1) (-μ)) (B (E d (a + 1) c m))
        rw [Z1', hneg _ (mS _ le_rfl (by omega)), inv_inv] at h1
        rw [← h1]; group
      have hxm : xc d (a + 1) μ ∈ UL d F (Finset.Icc (a + 1) (c - 1)) := xc_mem (by simp; omega) μ
      refine ⟨u * xc d (a + 1) μ, mul_mem hu hxm, l + -μ * m, v, hv, hcol, ?_⟩
      rw [hA.mul _ hu _ hxm, hA.gen (a + 1) (by simp; omega), zadd, hBv]
      simp only [mul_assoc]
      rw [hcomm'.eq, ← mul_assoc (B (E d (a + 1) c m)) (xh (a + 1) μ), hconj]
      simp only [mul_assoc]
      rw [(zx1 l μ).left_comm]
    have heA : e ∈ Finset.Icc (a + 1) (c - 1) := Finset.mem_Icc.2 ⟨by omega, by omega⟩
    have heB : e ∈ Finset.Icc (a + 2) c := Finset.mem_Icc.2 ⟨by omega, by omega⟩
    refine ⟨u * xc d e μ, mul_mem hu (xc_mem heA μ), l, xc d e (-μ) * v * xc d e μ,
      mul_mem (mul_mem (xc_mem heB _) hv) (xc_mem heB _),
      col_conj (by omega) (by omega) hcd hv hcol μ, ?_⟩
    rw [hA.mul _ hu _ (xc_mem heA μ), hA.gen e heA,
      hB.mul _ (mul_mem (xc_mem heB _) hv) _ (xc_mem heB _), hB.mul _ (xc_mem heB _) _ hv,
      hB.gen e heB, hB.gen e heB, hneg e he μ]
    exact nf_mid (zc l e he μ).symm
  intro g hg
  obtain ⟨u, hu, l, v, hv, hcol, rfl⟩ := hW g
  have hπz : π (z l) = E d a c l := by
    rw [hz, map_cm', hπ (a + 1) (mS _ le_rfl (by omega)),
      hB.retract π (fun e he => hπ e (Finset.Icc_subset_Icc (by omega) le_rfl he)) _
        (mB (a + 1) c (by omega) le_rfl le_rfl 1),
      show xc d (a + 1) l = E d a (a + 1) l by simp [xc],
      E_cm (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), mul_one]
  rw [map_mul, map_mul, hA.retract π (fun e he => hπ e (Finset.Icc_subset_Icc le_rfl
    (by omega) he)) u hu, hπz, hB.retract π (fun e he => hπ e (Finset.Icc_subset_Icc (by omega)
    le_rfl he)) v hv] at hg
  obtain ⟨rfl, rfl, rfl⟩ := inj_last hac hcd hu hv hcol hg
  rw [hA.one, z0, hB.one, mul_one, mul_one]

theorem core (hF : ∃ α α' : F, α ≠ 0 ∧ α' ≠ 0 ∧ α + α' ≠ 0) {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 d) {xh : ℕ → F → P} (π : P →* SLd d F)
    (hπ : ∀ c ∈ S, ∀ l, π (xh c l) = xc d c l)
    (hgen : ∀ g : P, g ∈ Subgroup.closure {g | ∃ c ∈ S, ∃ l, g = xh c l})
    (hcomp : Compat d S xh) (IH : ∀ T ⊂ S, ∃ f : SLd d F → P, IsExt d T xh f) :
    ∀ g, π g = 1 → g = 1 := by
  by_cases h2 : S.card ≤ 2
  · exact core0 π hπ hgen hcomp h2
  have hne : S.Nonempty := by rw [← Finset.card_pos]; omega
  have hm1 : 1 ≤ S.min' hne := (Finset.mem_Icc.1 (hS (S.min'_mem hne))).1
  have hMd : S.max' hne ≤ d := (Finset.mem_Icc.1 (hS (S.max'_mem hne))).2
  by_cases hI : ∀ k, S.min' hne < k → k < S.max' hne → k ∈ S
  · have hSeq : S = Finset.Icc (S.min' hne - 1 + 1) (S.max' hne) := by
      ext k; simp only [Finset.mem_Icc]
      constructor
      · intro hk; exact ⟨by have := S.min'_le k hk; omega, S.le_max' k hk⟩
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_or_ge (S.min' hne) k with h3 | h3
        · rcases Nat.lt_or_ge k (S.max' hne) with h4 | h4
          · exact hI k h3 h4
          · have : k = S.max' hne := by omega
            rw [this]; exact S.max'_mem hne
        · have : k = S.min' hne := by omega
          rw [this]; exact S.min'_mem hne
    have hcard := h2
    rw [hSeq, Nat.card_Icc] at hcard
    exact core2 π hπ hgen hcomp IH hF hSeq (by omega) hMd
  · push Not at hI
    obtain ⟨k, hmk, hkM, hk⟩ := hI
    exact core1 π hπ hgen hcomp IH hk (S.min'_mem hne) (S.max'_mem hne) hmk hkM

end Core

/-! ### The rank-2 presentation theorem -/

section Main

universe u

/-- Every family satisfying the rank-`≤ 2` relations of `U_S` extends to a homomorphism on
`U_S` (equivalently, `U_S` is the amalgam of its rank-`≤ 2` subgroups `U_{c,c'}`). -/
theorem ext_main {F : Type u} [Field F] (hF : ∃ α α' : F, α ≠ 0 ∧ α' ≠ 0 ∧ α + α' ≠ 0)
    (d : ℕ) : ∀ (S : Finset ℕ) (G : Type u) [Group G] (y : ℕ → F → G), Compat d S y →
      ∃ f : SLd d F → G, IsExt d S y f := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
  intro G _ y hy
  by_cases hS : S ⊆ Finset.Icc 1 d
  swap
  · have hS0 : S.filter (fun c => 1 ≤ c ∧ c ≤ d) ⊂ S := by
      obtain ⟨c, hc, hc'⟩ := Finset.not_subset.1 hS
      exact Finset.filter_ssubset.2 ⟨c, hc, by simpa using hc'⟩
    obtain ⟨f, hf⟩ := ih _ hS0 G y (hy.mono (Finset.filter_subset _ _))
    have hUL : ∀ u ∈ UL d F S, u ∈ UL d F (S.filter (fun c => 1 ≤ c ∧ c ≤ d)) :=
      UL_induction (one_mem _) (fun c hc l => by
        by_cases h : 1 ≤ c ∧ c ≤ d
        · exact xc_mem (Finset.mem_filter.2 ⟨hc, h⟩) l
        · rw [xc_degen (by omega) l]; exact one_mem _)
        (fun u _ v _ hu hv => mul_mem hu hv) (fun u _ hu => inv_mem hu)
    refine ⟨f, fun u hu v hv => hf.mul u (hUL u hu) v (hUL v hv), fun c hc l => ?_⟩
    by_cases h : 1 ≤ c ∧ c ≤ d
    · exact hf.gen c (Finset.mem_filter.2 ⟨hc, h⟩) l
    · rw [xc_degen (by omega) l, hf.one, hy.degen hc (xc_degen (by omega) l)]
  -- the graph of `y` inside `G × SL`
  let Y : ℕ → F → G × SLd d F := fun c l => (y c l, xc d c l)
  let K : Subgroup (G × SLd d F) := Subgroup.closure {g | ∃ c ∈ S, ∃ l, g = Y c l}
  let xh : ℕ → F → K := fun c l =>
    if h : c ∈ S then ⟨Y c l, Subgroup.subset_closure ⟨c, h, l, rfl⟩⟩ else 1
  let π : K →* SLd d F := (MonoidHom.snd G (SLd d F)).comp K.subtype
  have hxh : ∀ c ∈ S, ∀ l, (xh c l : G × SLd d F) = (y c l, xc d c l) := fun c hc l => by
    simp [xh, hc, Y]
  have hπ : ∀ c ∈ S, ∀ l, π (xh c l) = xc d c l := fun c hc l => by
    simp [π, hxh c hc l]
  have hlift : ∀ c ∈ S, ∀ c' ∈ S, ∀ w ∈ Wd F c c',
      ((lf xh w : K) : G × SLd d F) = (lf y w, lf (xc d) w) := by
    intro c hc c' hc' w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨l, rfl | rfl⟩ := hx
      · rw [lf_of, lf_of, lf_of, hxh c hc l]
      · rw [lf_of, lf_of, lf_of, hxh c' hc' l]
    | one => rw [map_one, map_one, map_one]; rfl
    | mul x1 x2 _ _ h1 h2 =>
      rw [map_mul, map_mul, map_mul, Subgroup.coe_mul, h1, h2, Prod.mk_mul_mk]
    | inv x _ h1 => rw [map_inv, map_inv, map_inv, Subgroup.coe_inv, h1, Prod.inv_mk]
  have hcompK : Compat d S xh := fun c hc c' hc' w hw h1 => by
    apply Subtype.ext
    rw [hlift c hc c' hc' w hw, hy c hc c' hc' w hw h1, h1]
    rfl
  have hgen : ∀ g : K, g ∈ Subgroup.closure {g | ∃ c ∈ S, ∃ l, g = xh c l} := by
    intro g
    have h1 : g ∈ Subgroup.closure (((↑) : K → G × SLd d F) ⁻¹'
        {g | ∃ c ∈ S, ∃ l, g = Y c l}) := by
      rw [Subgroup.closure_closure_coe_preimage]; trivial
    refine Subgroup.closure_mono ?_ h1
    rintro k ⟨c, hc, l, hk⟩
    exact ⟨c, hc, l, Subtype.ext (by rw [hk, hxh c hc l])⟩
  have hinj := core hF hS π hπ hgen hcompK (fun T hT => ih T hT K xh (hcompK.mono hT.subset))
  have hsurj : ∀ u ∈ UL d F S, ∃ k : K, π k = u :=
    UL_induction ⟨1, map_one π⟩ (fun c hc l => ⟨xh c l, hπ c hc l⟩)
      (fun u _ v _ ⟨k1, h1⟩ ⟨k2, h2⟩ => ⟨k1 * k2, by rw [map_mul, h1, h2]⟩)
      (fun u _ ⟨k, h⟩ => ⟨k⁻¹, by rw [map_inv, h]⟩)
  have huniq : ∀ k k' : K, π k = π k' → k = k' := fun k k' h => by
    have := hinj (k * k'⁻¹) (by rw [map_mul, map_inv, h, mul_inv_cancel])
    exact mul_inv_eq_one.1 this
  refine ⟨fun u => if h : ∃ k : K, π k = u then ((h.choose : K) : G × SLd d F).1 else 1, ?_, ?_⟩
  · intro u hu v hv
    have e1 := hsurj u hu
    have e2 := hsurj v hv
    have e3 := hsurj (u * v) (mul_mem hu hv)
    simp only [dif_pos e1, dif_pos e2, dif_pos e3]
    have : e3.choose = e1.choose * e2.choose :=
      huniq _ _ (by rw [e3.choose_spec, map_mul, e1.choose_spec, e2.choose_spec])
    rw [this]; rfl
  · intro c hc l
    have e := hsurj _ (xc_mem hc l)
    simp only [dif_pos e]
    have : e.choose = xh c l := huniq _ _ (by rw [e.choose_spec, hπ c hc l])
    rw [this, hxh c hc l]

end Main

section Amalgam

lemma exists_good {F : Type*} [Field F] [Fintype F] (hq : 3 ≤ Fintype.card F) :
    ∃ α α' : F, α ≠ 0 ∧ α' ≠ 0 ∧ α + α' ≠ 0 := by
  obtain ⟨t, ht0, ht1⟩ : ∃ t : F, t ≠ 0 ∧ t ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := fun t _ => by
      by_cases ht : t = 0
      · simp [ht]
      · simp [h t ht]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ] at this
    have h2 : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
    omega
  by_cases h : 1 + t = 0
  · refine ⟨1, 1, one_ne_zero, one_ne_zero, fun h2 => ht1 ?_⟩
    linear_combination h - h2
  · exact ⟨1, t, one_ne_zero, ht0, h⟩

theorem amalgam (d : ℕ) (F : Type*) [Field F] [Fintype F] (hq : 3 ≤ Fintype.card F)
    (S : Finset ℕ) {ι : Type*} [Fintype ι] (T : ι → Finset ℕ)
    (hT : ∀ c ∈ S, ∀ c' ∈ S, ∃ i, c ∉ T i ∧ c' ∉ T i) :
    ∀ w : FreeGroup (CosetGen (fun i => (UL d F (S \ T i)).subgroupOf (UL d F S))),
      FreeGroup.lift Subtype.val w = 1 →
      w ∈ Subgroup.normalClosure (cosetRel (fun i => (UL d F (S \ T i)).subgroupOf (UL d F S))) := by
  set H : ι → Subgroup (UL d F S) := fun i => (UL d F (S \ T i)).subgroupOf (UL d F S) with hH
  intro w hw
  set N := Subgroup.normalClosure (cosetRel H)
  let mk : FreeGroup (CosetGen H) →* FreeGroup (CosetGen H) ⧸ N := QuotientGroup.mk' N
  have mk_rel : ∀ i, ∀ l : List (CosetGen H), 1 ≤ l.length → l.length ≤ 3 →
      (∀ x ∈ l, x.1 ∈ H i) → (l.map Subtype.val).prod = 1 → mk (l.map FreeGroup.of).prod = 1 := by
    intro i l h1 h2 h3 h4
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_normalClosure
      (Set.mem_iUnion.2 ⟨i, l, h1, h2, h3, h4, rfl⟩))
  let θ : UL d F S → FreeGroup (CosetGen H) ⧸ N := fun g =>
    if h : ∃ i, g ∈ H i then mk (cosetWord H g h) else 1
  have θ_one : θ 1 = 1 := by
    simp only [θ]; split_ifs with h
    · simp [cosetWord]
    · rfl
  have θ_of : ∀ (g : UL d F S) (hg : g ≠ 1) (h : ∃ i, g ∈ H i),
      θ g = mk (FreeGroup.of ⟨g, hg, h⟩) := by
    intro g hg h
    simp only [θ, dif_pos h, cosetWord, dif_neg hg]
  have θ_mul : ∀ i, ∀ g ∈ H i, ∀ h ∈ H i, θ (g * h) = θ g * θ h := by
    intro i g hg h hh
    by_cases g1 : g = 1
    · rw [g1, one_mul, θ_one, one_mul]
    by_cases h1 : h = 1
    · rw [h1, mul_one, θ_one, mul_one]
    have hgi : ∃ i, g ∈ H i := ⟨i, hg⟩
    have hhi : ∃ i, h ∈ H i := ⟨i, hh⟩
    rw [θ_of g g1 hgi, θ_of h h1 hhi]
    by_cases gh1 : g * h = 1
    · rw [gh1, θ_one, ← map_mul]
      have := mk_rel i [⟨g, g1, hgi⟩, ⟨h, h1, hhi⟩] (by simp) (by simp)
        (by simp [hg, hh]) (by simpa using gh1)
      simpa using this.symm
    · have hghi : ∃ i, g * h ∈ H i := ⟨i, mul_mem hg hh⟩
      have hinv1 : (g * h)⁻¹ ≠ 1 := inv_ne_one.2 gh1
      have hinvi : ∃ i, (g * h)⁻¹ ∈ H i := ⟨i, inv_mem (mul_mem hg hh)⟩
      rw [θ_of _ gh1 hghi]
      have r3 := mk_rel i [⟨g, g1, hgi⟩, ⟨h, h1, hhi⟩, ⟨(g * h)⁻¹, hinv1, hinvi⟩] (by simp)
        (by simp) (by simp [hg, hh, mul_mem (inv_mem hh) (inv_mem hg)]) (by simp)
      have r2 := mk_rel i [⟨g * h, gh1, hghi⟩, ⟨(g * h)⁻¹, hinv1, hinvi⟩] (by simp)
        (by simp) (by simp [mul_mem hg hh, mul_mem (inv_mem hh) (inv_mem hg)]) (by simp)
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        map_mul] at r3 r2
      rw [← mul_assoc] at r3
      exact ((eq_inv_of_mul_eq_one_left r3).trans (eq_inv_of_mul_eq_one_left r2).symm).symm
  have θ_inv : ∀ i, ∀ g ∈ H i, θ g⁻¹ = (θ g)⁻¹ := fun i g hg =>
    eq_inv_of_mul_eq_one_left (by rw [← θ_mul i _ (inv_mem hg) _ hg, inv_mul_cancel, θ_one])
  let y : ℕ → F → FreeGroup (CosetGen H) ⧸ N := fun c l =>
    if h : c ∈ S then θ ⟨xc d c l, xc_mem h l⟩ else 1
  have hy : Compat d S y := by
    intro c hc c' hc' w hw h1
    obtain ⟨i, hci, hc'i⟩ := hT c hc c' hc'
    have key : ∀ w ∈ Wd F c c', ∃ g : UL d F S, g ∈ H i ∧
        (g : SLd d F) = lf (xc d) w ∧ lf y w = θ g := by
      intro w hw
      induction hw using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨l, rfl | rfl⟩ := hx
        · refine ⟨⟨xc d c l, xc_mem hc l⟩, ?_, by rw [lf_of], by rw [lf_of]; simp [y, hc]⟩
          rw [hH, Subgroup.mem_subgroupOf]
          exact xc_mem (Finset.mem_sdiff.2 ⟨hc, hci⟩) l
        · refine ⟨⟨xc d c' l, xc_mem hc' l⟩, ?_, by rw [lf_of], by rw [lf_of]; simp [y, hc']⟩
          rw [hH, Subgroup.mem_subgroupOf]
          exact xc_mem (Finset.mem_sdiff.2 ⟨hc', hc'i⟩) l
      | one => exact ⟨1, one_mem _, by rw [map_one]; rfl, by rw [map_one, θ_one]⟩
      | mul x1 x2 _ _ h1 h2 =>
        obtain ⟨g1, m1, e1, f1⟩ := h1
        obtain ⟨g2, m2, e2, f2⟩ := h2
        exact ⟨g1 * g2, mul_mem m1 m2, by rw [map_mul, ← e1, ← e2]; rfl,
          by rw [map_mul, f1, f2, θ_mul i _ m1 _ m2]⟩
      | inv x _ h1 =>
        obtain ⟨g, m, e, f⟩ := h1
        exact ⟨g⁻¹, inv_mem m, by rw [map_inv, ← e]; rfl, by rw [map_inv, f, θ_inv i _ m]⟩
    obtain ⟨g, -, e, f⟩ := key w hw
    have g1 : g = 1 := Subtype.ext (e.trans h1)
    rw [f, g1, θ_one]
  obtain ⟨f, hf⟩ := ext_main (exists_good hq) d S _ y hy
  have hfθ : ∀ i, ∀ u ∈ UL d F (S \ T i), ∀ hu : u ∈ UL d F S, f u = θ ⟨u, hu⟩ := by
    intro i
    refine UL_induction ?_ ?_ ?_ ?_
    · intro hu; rw [hf.one]; exact θ_one.symm
    · intro c hc l hu
      rw [hf.gen c (Finset.mem_sdiff.1 hc).1]
      simp [y, (Finset.mem_sdiff.1 hc).1]
    · intro u hu v hv eu ev huv
      have hu' := UL_mono Finset.sdiff_subset hu
      have hv' := UL_mono Finset.sdiff_subset hv
      rw [hf.mul u hu' v hv', eu hu', ev hv',
        ← θ_mul i ⟨u, hu'⟩ (Subgroup.mem_subgroupOf.2 hu) ⟨v, hv'⟩ (Subgroup.mem_subgroupOf.2 hv)]
      rfl
    · intro u hu eu hui
      have hu' := UL_mono Finset.sdiff_subset hu
      rw [hf.inv hu', eu hu', ← θ_inv i ⟨u, hu'⟩ (Subgroup.mem_subgroupOf.2 hu)]
      rfl
  have key : ∀ w : FreeGroup (CosetGen H),
      mk w = f ((FreeGroup.lift Subtype.val w : UL d F S) : SLd d F) := by
    intro w
    induction w using FreeGroup.induction_on with
    | C1 => rw [map_one, map_one, OneMemClass.coe_one, hf.one]
    | of x =>
      obtain ⟨g, hg1, i, hgi⟩ := x
      rw [FreeGroup.lift_apply_of, ← θ_of g hg1 ⟨i, hgi⟩]
      exact (hfθ i g (Subgroup.mem_subgroupOf.1 hgi) g.2).symm
    | inv_of x h =>
      rw [map_inv, map_inv, h, Subgroup.coe_inv, hf.inv (FreeGroup.lift (Subtype.val : CosetGen H → UL d F S) (FreeGroup.of x)).2]
    | mul x1 x2 h1 h2 =>
      rw [map_mul, map_mul, h1, h2, Subgroup.coe_mul,
        hf.mul _ (FreeGroup.lift (Subtype.val : CosetGen H → UL d F S) x1).2 _
          (FreeGroup.lift (Subtype.val : CosetGen H → UL d F S) x2).2]
  have := key w
  rw [hw, OneMemClass.coe_one, hf.one] at this
  exact (QuotientGroup.eq_one_iff _).1 this

end Amalgam

end PolySwap.KMS.L317A
end Part_A_amalgam

section Part_B_complex

open Classical

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace PolySwap.KMS.L317B

open PolySwap.KMS WComplex

/-- A base chamber type `st` and base element `e`: the apex of the contraction is `⟨st, e H_st⟩`. -/
class Base {G : Type*} [Group G] {ι : Type*} (H : ι → Subgroup G) where
  st : ι
  e : G

section General

variable {V : Type*} (X : WComplex V) (v₀ : V)

/-- Rewriting by `BT` (free) and `TR` (cost 1) moves, with an upper bound on the cost. -/
inductive Rw : ℕ → List V → List V → Prop
  | refl (n : ℕ) (A : List V) : Rw n A A
  | bt {n : ℕ} {A B C : List V} : X.BT v₀ A B → Rw n B C → Rw n A C
  | tr {n : ℕ} {A B C : List V} : X.TR v₀ A B → Rw n B C → Rw (n + 1) A C

variable {X v₀}

lemma Rw.mono {a : ℕ} {A B : List V} (h : Rw X v₀ a A B) : ∀ {b}, a ≤ b → Rw X v₀ b A B := by
  induction h with
  | refl n A => intro b _; exact Rw.refl b A
  | bt h _ ih => intro b hb; exact Rw.bt h (ih hb)
  | tr h _ ih =>
    intro b hb
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    exact Rw.tr h (ih (by omega))

lemma Rw.trans {a b : ℕ} {A B C : List V} (h : Rw X v₀ a A B) (h' : Rw X v₀ b B C) :
    Rw X v₀ (a + b) A C := by
  induction h with
  | refl n A => exact h'.mono (by omega)
  | bt h _ ih => exact Rw.bt h (ih h')
  | @tr n _ _ _ h _ ih =>
    have := Rw.tr h (ih h')
    rwa [show n + 1 + b = n + b + 1 by omega]

lemma Rw.symm {a : ℕ} {A B : List V} (h : Rw X v₀ a A B) : Rw X v₀ a B A := by
  induction h with
  | refl n A => exact Rw.refl n A
  | bt h _ ih => simpa using ih.trans (Rw.bt (Or.symm h) (Rw.refl 0 _))
  | tr h _ ih => simpa using ih.trans (Rw.tr (Or.symm h) (Rw.refl 0 _))

lemma len_of_BT {A B : List V} (h : X.BTstep v₀ A B) : A.length = B.length + 2 := by
  obtain ⟨u, v, Q₀, Q₁, -, ⟨⟨hQ, -⟩, -⟩, -, -, rfl, rfl⟩ := h
  have : Q₁.length ≠ 0 := by simpa using hQ
  simp [pcat]; omega

lemma len_of_TR {A B : List V} (h : X.TRstep v₀ A B) : A.length = B.length + 1 := by
  obtain ⟨u, v, w, Q₀, Q₁, -, -, -, -, -, ⟨⟨hQ, -⟩, -⟩, rfl, rfl⟩ := h
  have : Q₁.length ≠ 0 := by simpa using hQ
  simp [pcat]; omega

lemma not_TR_of_BT {A B : List V} (h : X.BT v₀ A B) : ¬ X.TR v₀ A B := by
  rintro (h' | h') <;> rcases h with h | h <;>
    · have := len_of_BT h; have := len_of_TR h'; omega

lemma trCount_cons_cons (A B : List V) (l : List (List V)) :
    X.trCount v₀ (A :: B :: l) = (if X.TR v₀ A B then 1 else 0) + X.trCount v₀ (B :: l) := by
  simp only [trCount, List.tail_cons, List.zip_cons_cons, List.countP_cons, decide_eq_true_eq]
  split_ifs <;> omega

lemma Rw.chain {n : ℕ} {A B : List V} (h : Rw X v₀ n A B) :
    ∃ l : List (List V), l.head? = some A ∧ l.getLast? = some B ∧
      l.IsChain (fun A B => X.TR v₀ A B ∨ X.BT v₀ A B) ∧ X.trCount v₀ l ≤ n := by
  induction h with
  | refl n A => exact ⟨[A], rfl, rfl, List.isChain_singleton _, by simp [trCount]⟩
  | @bt n A B C h _ ih =>
    obtain ⟨l, h1, h2, h3, h4⟩ := ih
    obtain ⟨l', rfl⟩ : ∃ l', l = B :: l' := by
      cases l with
      | nil => simp at h1
      | cons x l' => simp at h1; exact ⟨l', by rw [h1]⟩
    refine ⟨A :: B :: l', rfl, by simpa using h2, List.IsChain.cons_cons (Or.inr h) h3, ?_⟩
    rw [trCount_cons_cons, if_neg (not_TR_of_BT h)]; omega
  | @tr n A B C h _ ih =>
    obtain ⟨l, h1, h2, h3, h4⟩ := ih
    obtain ⟨l', rfl⟩ : ∃ l', l = B :: l' := by
      cases l with
      | nil => simp at h1
      | cons x l' => simp at h1; exact ⟨l', by rw [h1]⟩
    refine ⟨A :: B :: l', rfl, by simpa using h2, List.IsChain.cons_cons (Or.inl h) h3, ?_⟩
    rw [trCount_cons_cons]; split_ifs <;> omega

/-! ### Paths -/

variable (X)

def Adj (x y : V) : Prop := x ≠ y ∧ X.IsFace {x, y}

lemma vert_of_face {s : Finset V} (h : X.IsFace s) {x : V} (hx : x ∈ s) : x ∈ X.vertices := by
  obtain ⟨τ, hτ, hs⟩ := h
  simp only [vertices, Finset.mem_biUnion, id]
  exact ⟨τ, hτ, hs hx⟩

lemma face_sub {s t : Finset V} (h : X.IsFace t) (hst : s ⊆ t) : X.IsFace s := by
  obtain ⟨τ, hτ, hs⟩ := h
  exact ⟨τ, hτ, hst.trans hs⟩

variable {X}

lemma path_append_left {l₁ l₂ : List V} (h : X.IsPath (l₁ ++ l₂)) (hl : l₁ ≠ []) :
    X.IsPath l₁ :=
  ⟨hl, fun u hu => h.2.1 u (List.mem_append_left _ hu), h.2.2.left_of_append⟩

lemma path_append_right {l₁ l₂ : List V} (h : X.IsPath (l₁ ++ l₂)) (hl : l₂ ≠ []) :
    X.IsPath l₂ :=
  ⟨hl, fun u hu => h.2.1 u (List.mem_append_right _ hu), h.2.2.right_of_append⟩

lemma path_reverse {l : List V} (h : X.IsPath l) : X.IsPath l.reverse := by
  refine ⟨by simpa using h.1, fun u hu => h.2.1 u (List.mem_reverse.1 hu), ?_⟩
  rw [List.isChain_reverse]
  exact h.2.2.imp fun a b hab => ⟨hab.1.symm, by rw [Finset.pair_comm]; exact hab.2⟩

lemma bt_local {P S : List V} {u v : V} (h : X.IsPathFrom v₀ v₀ (P ++ u :: v :: u :: S)) :
    X.BT v₀ (P ++ u :: v :: u :: S) (P ++ u :: S) := by
  obtain ⟨hp, hh, hl⟩ := h
  have hp1 : X.IsPath (P ++ [u]) :=
    path_append_left (l₂ := v :: u :: S) (by simpa using hp) (by simp)
  have hp2 : X.IsPath (u :: S) :=
    path_append_right (l₁ := P ++ [u, v]) (by simpa using hp) (by simp)
  have hch : (u :: v :: u :: S).IsChain (fun u v => u ≠ v ∧ X.IsFace {u, v}) :=
    (path_append_right (l₁ := P) hp (by simp)).2.2
  rw [List.isChain_cons_cons] at hch
  refine Or.inl ⟨u, v, P ++ [u], (u :: S).reverse, ⟨hp1, ?_, by simp⟩,
    ⟨path_reverse hp2, ?_, by simp⟩, hch.1.1, hch.1.2, ?_, ?_⟩
  · cases P with
    | nil => simpa using hh
    | cons a P => simpa using hh
  · rw [List.head?_reverse]
    have : (u :: S).getLast? = (P ++ u :: v :: u :: S).getLast? := by
      rw [List.getLast?_append]; cases S <;> simp [List.getLast?_cons]
    rw [this, hl]
  · simp [pcat]
  · simp [pcat]

lemma tr_local {P S : List V} {u v w : V} (h : X.IsPathFrom v₀ v₀ (P ++ u :: v :: w :: S))
    (huw : u ≠ w) (hf : X.IsFace {u, v, w}) :
    X.TR v₀ (P ++ u :: v :: w :: S) (P ++ u :: w :: S) := by
  obtain ⟨hp, hh, hl⟩ := h
  have hp1 : X.IsPath (P ++ [u]) :=
    path_append_left (l₂ := v :: w :: S) (by simpa using hp) (by simp)
  have hp2 : X.IsPath (w :: S) :=
    path_append_right (l₁ := P ++ [u, v]) (by simpa using hp) (by simp)
  have hch : (u :: v :: w :: S).IsChain (fun u v => u ≠ v ∧ X.IsFace {u, v}) :=
    (path_append_right (l₁ := P) hp (by simp)).2.2
  rw [List.isChain_cons_cons, List.isChain_cons_cons] at hch
  refine Or.inl ⟨u, v, w, P ++ [u], (w :: S).reverse, hch.1.1, hch.2.1.1, huw, hf,
    ⟨hp1, ?_, by simp⟩, ⟨path_reverse hp2, ?_, by simp⟩, ?_, ?_⟩
  · cases P with
    | nil => simpa using hh
    | cons a P => simpa using hh
  · rw [List.head?_reverse]
    have : (w :: S).getLast? = (P ++ u :: v :: w :: S).getLast? := by
      rw [List.getLast?_append]; cases S <;> simp [List.getLast?_cons]
    rw [this, hl]
  · simp [pcat]
  · simp [pcat]

/-! ### Walks and their normal forms -/

variable (X v₀)

/-- A walk: consecutive vertices are equal or adjacent. -/
def IsWalk (W : List V) : Prop :=
  W ≠ [] ∧ (∀ x ∈ W, X.IsFace {x}) ∧ W.IsChain (fun x y => X.IsFace {x, y})

def WLoop (W : List V) : Prop := IsWalk X W ∧ W.head? = some v₀ ∧ W.getLast? = some v₀

/-- Remove consecutive repetitions. -/
def dd : V → List V → List V
  | a, [] => [a]
  | a, b :: l => if a = b then dd a l else a :: dd b l

def nrm : List V → List V
  | [] => []
  | a :: l => dd a l

def Hom (c : ℕ) (W W' : List V) : Prop :=
  (WLoop X v₀ W ↔ WLoop X v₀ W') ∧ (WLoop X v₀ W → Rw X v₀ c (nrm W) (nrm W'))

def LHom (c : ℕ) (S S' : List V) : Prop := ∀ pre suf, Hom X v₀ c (pre ++ S ++ suf) (pre ++ S' ++ suf)

variable {X v₀}

lemma dd_head (a : V) (l : List V) : ∃ t, dd a l = a :: t := by
  induction l generalizing a with
  | nil => exact ⟨[], rfl⟩
  | cons b l ih =>
    by_cases h : a = b
    · subst h; simpa [dd] using ih a
    · simp [dd, h]

lemma dd_split (l : List V) (a b : V) : ∃ Pre, ∀ m, dd a (l ++ b :: m) = Pre ++ dd b m := by
  induction l generalizing a with
  | nil =>
    by_cases h : a = b
    · subst h; exact ⟨[], fun m => by simp [dd]⟩
    · exact ⟨[a], fun m => by simp [dd, h]⟩
  | cons x l ih =>
    by_cases h : a = x
    · obtain ⟨Pre, hP⟩ := ih a
      exact ⟨Pre, fun m => by subst h; simp [dd, hP]⟩
    · obtain ⟨Pre, hP⟩ := ih x
      exact ⟨a :: Pre, fun m => by simp [dd, h, hP]⟩

lemma nrm_split (pre : List V) (b : V) : ∃ Pre, ∀ m, nrm (pre ++ b :: m) = Pre ++ dd b m := by
  cases pre with
  | nil => exact ⟨[], fun m => rfl⟩
  | cons a pre =>
    obtain ⟨Pre, h⟩ := dd_split pre a b
    exact ⟨Pre, fun m => h m⟩

lemma mem_dd {a : V} {l : List V} {x : V} (h : x ∈ dd a l) : x ∈ a :: l := by
  induction l generalizing a with
  | nil => simpa [dd] using h
  | cons b l ih =>
    by_cases hab : a = b
    · subst hab; simp only [dd, if_true] at h
      have := ih h; simp at this ⊢; tauto
    · simp only [dd, hab, if_false, List.mem_cons] at h
      rcases h with h | h
      · simp [h]
      · have := ih h; simp at this ⊢; tauto

lemma dd_getLast (a : V) (l : List V) : (dd a l).getLast? = (a :: l).getLast? := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih =>
    by_cases hab : a = b
    · subst hab; simp only [dd, if_true]; rw [ih]; cases l <;> simp [List.getLast?_cons]
    · simp only [dd, hab, if_false]
      obtain ⟨t, ht⟩ := dd_head b l
      rw [ht, List.getLast?_cons_cons, List.getLast?_cons_cons, ← ih b, ht]

lemma dd_chain (a : V) (l : List V) (h : (a :: l).IsChain (fun x y => X.IsFace {x, y})) :
    (dd a l).IsChain (fun u v => u ≠ v ∧ X.IsFace {u, v}) := by
  induction l generalizing a with
  | nil => exact List.isChain_singleton _
  | cons b l ih =>
    rw [List.isChain_cons_cons] at h
    by_cases hab : a = b
    · subst hab; simpa [dd] using ih a h.2
    · simp only [dd, hab, if_false]
      obtain ⟨t, ht⟩ := dd_head b l
      have := ih b h.2
      rw [ht] at this ⊢
      exact List.IsChain.cons_cons ⟨hab, h.1⟩ this

lemma nrm_loop {W : List V} (h : WLoop X v₀ W) : X.IsPathFrom v₀ v₀ (nrm W) := by
  obtain ⟨⟨hne, hv, hc⟩, hh, hl⟩ := h
  rcases W with _ | ⟨a, l⟩
  · exact absurd rfl hne
  simp only [List.head?_cons, Option.some.injEq] at hh
  subst hh
  obtain ⟨t, ht⟩ := dd_head a l
  refine ⟨⟨?_, fun x hx => ?_, dd_chain a l hc⟩, ?_, ?_⟩
  · simp [nrm, ht]
  · exact vert_of_face X (hv x (mem_dd hx)) (Finset.mem_singleton_self x)
  · simp [nrm, ht]
  · simp only [nrm]; rw [dd_getLast, hl]

lemma dd_of_path {a : V} {l : List V} (h : (a :: l).IsChain (fun u v => u ≠ v ∧ X.IsFace {u, v})) :
    dd a l = a :: l := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih =>
    rw [List.isChain_cons_cons] at h
    simp [dd, h.1.1, ih h.2]

lemma walk_of_path {l : List V} (h : X.IsPath l) : IsWalk X l := by
  refine ⟨h.1, fun x hx => ?_, h.2.2.imp fun a b hab => hab.2⟩
  have := h.2.1 x hx
  simp only [vertices, Finset.mem_biUnion, id] at this
  obtain ⟨τ, hτ, hx⟩ := this
  exact ⟨τ, hτ, by simpa using hx⟩

/-! ### The calculus `Hom` / `LHom` -/

lemma Hom.refl (c : ℕ) (W : List V) : Hom X v₀ c W W := ⟨Iff.rfl, fun _ => Rw.refl c _⟩

lemma Hom.trans {a b : ℕ} {W₁ W₂ W₃ : List V} (h₁ : Hom X v₀ a W₁ W₂) (h₂ : Hom X v₀ b W₂ W₃) :
    Hom X v₀ (a + b) W₁ W₃ :=
  ⟨h₁.1.trans h₂.1, fun h => (h₁.2 h).trans (h₂.2 (h₁.1.1 h))⟩

lemma Hom.symm {a : ℕ} {W₁ W₂ : List V} (h : Hom X v₀ a W₁ W₂) : Hom X v₀ a W₂ W₁ :=
  ⟨h.1.symm, fun hw => (h.2 (h.1.2 hw)).symm⟩

lemma Hom.mono {a b : ℕ} {W₁ W₂ : List V} (h : Hom X v₀ a W₁ W₂) (hab : a ≤ b) :
    Hom X v₀ b W₁ W₂ := ⟨h.1, fun hw => (h.2 hw).mono hab⟩

lemma Hom.of_eq {c : ℕ} {W W' : List V} (h : W = W') : Hom X v₀ c W W' := h ▸ Hom.refl c W

lemma LHom.refl (c : ℕ) (S : List V) : LHom X v₀ c S S := fun _ _ => Hom.refl c _

lemma LHom.of_eq {c : ℕ} {S S' : List V} (h : S = S') : LHom X v₀ c S S' :=
  h ▸ LHom.refl c S

lemma LHom.trans {a b : ℕ} {S₁ S₂ S₃ : List V} (h₁ : LHom X v₀ a S₁ S₂)
    (h₂ : LHom X v₀ b S₂ S₃) : LHom X v₀ (a + b) S₁ S₃ :=
  fun pre suf => (h₁ pre suf).trans (h₂ pre suf)

lemma LHom.symm {a : ℕ} {S₁ S₂ : List V} (h : LHom X v₀ a S₁ S₂) : LHom X v₀ a S₂ S₁ :=
  fun pre suf => (h pre suf).symm

lemma LHom.mono {a b : ℕ} {S₁ S₂ : List V} (h : LHom X v₀ a S₁ S₂) (hab : a ≤ b) :
    LHom X v₀ b S₁ S₂ := fun pre suf => (h pre suf).mono hab

lemma LHom.ctx {c : ℕ} {S S' : List V} (h : LHom X v₀ c S S') (P Q : List V) :
    LHom X v₀ c (P ++ S ++ Q) (P ++ S' ++ Q) := fun pre suf => by
  simpa [List.append_assoc] using h (pre ++ P) (Q ++ suf)

lemma LHom.app {a b : ℕ} {S S' T T' : List V} (h₁ : LHom X v₀ a S S') (h₂ : LHom X v₀ b T T') :
    LHom X v₀ (a + b) (S ++ T) (S' ++ T') :=
  (by simpa using h₁.ctx [] T : LHom X v₀ a (S ++ T) (S' ++ T)).trans
    (by simpa using h₂.ctx S' [])

lemma LHom.hom {c : ℕ} {S S' : List V} (h : LHom X v₀ c S S') : Hom X v₀ c S S' := by
  simpa using h [] []

/-- Replacing a walk segment by another with the same endpoints preserves `WLoop`. -/
lemma wloop_congr {S S' : List V} (hS : IsWalk X S) (hS' : IsWalk X S')
    (hh : S.head? = S'.head?) (hl : S.getLast? = S'.getLast?) (pre suf : List V) :
    WLoop X v₀ (pre ++ S ++ suf) ↔ WLoop X v₀ (pre ++ S' ++ suf) := by
  obtain ⟨hne, hv, hc⟩ := hS
  obtain ⟨hne', hv', hc'⟩ := hS'
  have key : ∀ T : List V, T ≠ [] → T.IsChain (fun x y => X.IsFace {x, y}) →
      ((pre ++ T ++ suf).IsChain (fun x y => X.IsFace {x, y}) ↔
        pre.IsChain (fun x y => X.IsFace {x, y}) ∧ suf.IsChain (fun x y => X.IsFace {x, y}) ∧
        (∀ x ∈ pre.getLast?, ∀ y ∈ T.head?, X.IsFace {x, y}) ∧
        (∀ x ∈ T.getLast?, ∀ y ∈ suf.head?, X.IsFace {x, y})) := by
    intro T hT hTc
    rw [List.append_assoc, List.isChain_append, List.isChain_append]
    have : (T ++ suf).head? = T.head? := by
      cases T with
      | nil => exact absurd rfl hT
      | cons a T => rfl
    rw [this]; tauto
  unfold WLoop IsWalk
  rw [key S hne hc, key S' hne' hc', hh, hl]
  have h1 : (pre ++ S ++ suf).head? = (pre ++ S' ++ suf).head? := by
    simp only [List.append_assoc, List.head?_append]
    cases S with
    | nil => exact absurd rfl hne
    | cons a S => cases S' with
      | nil => exact absurd rfl hne'
      | cons b S' => simp at hh; simp [hh]
  have h2 : (pre ++ S ++ suf).getLast? = (pre ++ S' ++ suf).getLast? := by
    simp only [List.getLast?_append]
    rw [hl]
  rw [h1, h2]
  constructor
  · rintro ⟨⟨-, hm, h⟩, hd, he⟩
    refine ⟨⟨by simp [hne'], fun x hx => ?_, h⟩, hd, he⟩
    simp only [List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact hm x (by simp [hx])
    · exact hv' x hx
    · exact hm x (by simp [hx])
  · rintro ⟨⟨-, hm, h⟩, hd, he⟩
    refine ⟨⟨by simp [hne], fun x hx => ?_, h⟩, hd, he⟩
    simp only [List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact hm x (by simp [hx])
    · exact hv x hx
    · exact hm x (by simp [hx])

lemma walk3 {a b d : V} (h : X.IsFace {a, b, d}) : IsWalk X [a, b, d] := by
  refine ⟨by simp, fun x hx => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    exact face_sub X h (by rcases hx with rfl | rfl | rfl <;> simp)
  · refine List.IsChain.cons_cons (face_sub X h ?_) (List.IsChain.cons_cons (face_sub X h ?_)
      (List.isChain_singleton _))
    · intro x; simp; tauto
    · intro x; simp; tauto

lemma walk2 {a b : V} (h : X.IsFace {a, b}) : IsWalk X [a, b] := by
  refine ⟨by simp, fun x hx => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    exact face_sub X h (by rcases hx with rfl | rfl <;> simp)
  · exact List.IsChain.cons_cons h (List.isChain_singleton _)

lemma walk1 {a : V} (h : X.IsFace {a}) : IsWalk X [a] :=
  ⟨by simp, fun x hx => by simp at hx; subst hx; exact h, List.isChain_singleton _⟩

/-- Deleting the middle vertex of a triangle. -/
lemma lhom_del {a b d : V} (hf : X.IsFace {a, b, d}) : LHom X v₀ 1 [a, b, d] [a, d] := by
  intro pre suf
  refine ⟨wloop_congr (walk3 hf) (walk2 (face_sub X hf (by intro x; simp; tauto))) rfl rfl pre suf,
    fun hw => ?_⟩
  have hp := nrm_loop hw
  obtain ⟨Pre, hPre⟩ := nrm_split pre a
  have e1 : pre ++ [a, b, d] ++ suf = pre ++ a :: (b :: d :: suf) := by simp
  have e2 : pre ++ [a, d] ++ suf = pre ++ a :: (d :: suf) := by simp
  rw [e1, hPre] at hp ⊢
  rw [e2, hPre]
  by_cases hab : a = b
  · subst hab; simp only [dd, if_true]; exact Rw.refl _ _
  by_cases hbd : b = d
  · subst hbd; simp only [dd, hab, if_false, if_true]; exact Rw.refl _ _
  obtain ⟨t, ht⟩ := dd_head d suf
  by_cases had : a = d
  · subst had
    simp only [dd, hab, if_false, hbd, if_true] at hp ⊢
    rw [ht] at hp ⊢
    exact Rw.bt (bt_local hp) (Rw.refl _ _)
  · simp only [dd, hab, if_false, hbd, had] at hp ⊢
    rw [ht] at hp ⊢
    exact Rw.tr (tr_local hp had hf) (Rw.refl _ _)

/-- Removing a backtrack `a b a`. -/
lemma lhom_bt {a b : V} (hf : X.IsFace {a, b}) : LHom X v₀ 0 [a, b, a] [a] := by
  intro pre suf
  have hf' : X.IsFace {a, b, a} := by
    refine face_sub X hf ?_; intro x; simp; tauto
  refine ⟨wloop_congr (walk3 hf') (walk1 (face_sub X hf (by simp))) rfl rfl pre suf,
    fun hw => ?_⟩
  have hp := nrm_loop hw
  obtain ⟨Pre, hPre⟩ := nrm_split pre a
  have e1 : pre ++ [a, b, a] ++ suf = pre ++ a :: (b :: a :: suf) := by simp
  have e2 : pre ++ [a] ++ suf = pre ++ a :: suf := by simp
  rw [e1, hPre] at hp ⊢
  rw [e2, hPre]
  by_cases hab : a = b
  · subst hab; simp only [dd, if_true]; exact Rw.refl _ _
  obtain ⟨t, ht⟩ := dd_head a suf
  simp only [dd, hab, if_false, Ne.symm hab] at hp ⊢
  rw [ht] at hp ⊢
  exact Rw.bt (bt_local hp) (Rw.refl _ _)

lemma lhom_stutter {a : V} : LHom X v₀ 0 [a, a] [a] := by
  intro pre suf
  have e1 : pre ++ [a, a] ++ suf = pre ++ [a] ++ (a :: suf) := by simp
  have e2 : pre ++ [a] ++ suf = pre ++ [] ++ (a :: suf) := by simp
  constructor
  · rw [e1, e2]
    constructor
    · rintro ⟨⟨-, hm, hc⟩, hh, hl⟩
      refine ⟨⟨by simp, fun x hx => hm x (by simp at hx ⊢; tauto), ?_⟩, ?_, ?_⟩
      · simp only [List.append_assoc, List.singleton_append, List.nil_append] at hc ⊢
        rw [List.isChain_append] at hc ⊢
        refine ⟨hc.1, (List.isChain_cons.1 hc.2.1).2, ?_⟩
        intro x hx y hy
        exact hc.2.2 x hx y (by simp at hy; simp [hy])
      · cases pre <;> simpa using hh
      · simpa [List.getLast?_append] using hl
    · rintro ⟨⟨-, hm, hc⟩, hh, hl⟩
      refine ⟨⟨by simp, fun x hx => hm x (by simp at hx ⊢; tauto), ?_⟩, ?_, ?_⟩
      · simp only [List.append_assoc, List.singleton_append, List.nil_append] at hc ⊢
        rw [List.isChain_append] at hc ⊢
        refine ⟨hc.1, List.IsChain.cons_cons ?_ hc.2.1, ?_⟩
        · simpa using hm a (by simp)
        · intro x hx y hy
          exact hc.2.2 x hx y (by simp at hy; simp [hy])
      · cases pre <;> simpa using hh
      · simpa [List.getLast?_append] using hl
  · intro _
    obtain ⟨Pre, hPre⟩ := nrm_split pre a
    have e3 : pre ++ [a, a] ++ suf = pre ++ a :: (a :: suf) := by simp
    have e4 : pre ++ [a] ++ suf = pre ++ a :: suf := by simp
    rw [e3, e4, hPre, hPre]
    simp only [dd, if_true]; exact Rw.refl _ _

lemma lhom_ins {a b d : V} (hf : X.IsFace {a, b, d}) : LHom X v₀ 1 [a, d] [a, b, d] :=
  (lhom_del hf).symm

/-- Collapsing a palindrome `Z⁻¹ ∘ Z`. -/
lemma lhom_pal (Z : List V) : ∀ (a e : V), (a :: Z).IsChain (fun x y => X.IsFace {x, y}) →
    (a :: Z).getLast? = some e → LHom X v₀ 0 ((a :: Z).reverse ++ Z) [e] := by
  induction Z with
  | nil =>
    intro a e _ he
    simp at he; subst he; exact LHom.refl _ _
  | cons b Z ih =>
    intro a e hc he
    rw [List.isChain_cons_cons] at hc
    have h1 : LHom X v₀ 0 ((a :: b :: Z).reverse ++ b :: Z) ((b :: Z).reverse ++ Z) := by
      have := (lhom_bt (X := X) (v₀ := v₀) (a := b) (b := a)
        (by rw [Finset.pair_comm]; exact hc.1)).ctx Z.reverse Z
      simpa using this
    have := h1.trans (ih b e hc.2 (by simpa [List.getLast?_cons] using he))
    simpa using this

lemma wl_le {α : Type*} (L : List (α × Bool)) : wordLength (FreeGroup.mk L) ≤ L.length := by
  unfold wordLength; exact FreeGroup.norm_mk_le

def Edge (X : WComplex V) (u v : V) : Prop := u ≠ v ∧ X.IsFace {u, v}

lemma path_pcat {a b c : V} {P Q : List V} (hP : X.IsPathFrom a b P) (hQ : X.IsPathFrom b c Q) :
    X.IsPathFrom a c (pcat P Q) := by
  obtain ⟨⟨hPn, hPv, hPc⟩, hPh, hPl⟩ := hP
  obtain ⟨⟨hQn, hQv, hQc⟩, hQh, hQl⟩ := hQ
  rcases Q with _ | ⟨b', Q⟩
  · exact absurd rfl hQn
  simp only [List.head?_cons, Option.some.injEq] at hQh
  subst hQh
  simp only [pcat, List.tail_cons]
  refine ⟨⟨by simp [hPn], fun u hu => ?_, ?_⟩, ?_, ?_⟩
  · rcases List.mem_append.1 hu with hu | hu
    · exact hPv u hu
    · exact hQv u (List.mem_cons_of_mem _ hu)
  · rw [List.isChain_append]
    refine ⟨hPc, hQc.tail, fun x hx y hy => ?_⟩
    rw [hPl] at hx; cases hx
    exact (List.isChain_cons.1 hQc).1 y hy
  · cases P with
    | nil => exact absurd rfl hPn
    | cons p P => simpa using hPh
  · rw [List.getLast?_append]
    cases Q with
    | nil => simpa [hPl] using hQl
    | cons q Q => simpa [List.getLast?_cons_cons] using hQl

lemma path_rev {a b : V} {P : List V} (hP : X.IsPathFrom a b P) : X.IsPathFrom b a P.reverse :=
  ⟨path_reverse hP.1, by rw [List.head?_reverse]; exact hP.2.2,
    by rw [List.getLast?_reverse]; exact hP.2.1⟩

lemma eqv_chain {R : List V → List V → Prop} (hR : ∀ A B, R A B → R B A) {A B : List V}
    (h : Relation.EqvGen R A B) :
    ∃ l : List (List V), l.head? = some A ∧ l.getLast? = some B ∧ l.IsChain R := by
  have key : Relation.ReflTransGen R A B ∧ Relation.ReflTransGen R B A := by
    induction h with
    | rel x y h => exact ⟨.single h, .single (hR _ _ h)⟩
    | refl x => exact ⟨.refl, .refl⟩
    | symm x y _ ih => exact ⟨ih.2, ih.1⟩
    | trans x y z _ _ ih₁ ih₂ => exact ⟨ih₁.1.trans ih₂.1, ih₂.2.trans ih₁.2⟩
  obtain ⟨l, hl, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen key.1
  exact ⟨A :: l, rfl, by rw [List.getLast?_eq_getLast_of_ne_nil (by simp), hlast], hl⟩

end General
section Coset

variable {G : Type*} [Group G] [Finite G] {ι : Type*} [Fintype ι] [Nonempty ι]
  (H : ι → Subgroup G) [Base H]

/-- `g` lies in the coset `u`. -/
def Mem (g : G) (u : Σ i, G ⧸ H i) : Prop := u.2 = (g : G ⧸ H u.1)

/-- The vertex `g H_st` of type `st`. -/
def Xv (g : G) : Σ i, G ⧸ H i := ⟨Base.st (H := H), (g : G ⧸ H (Base.st (H := H)))⟩

/-- A type `i` with `g ∈ H i`, when one exists. -/
def kf (g : G) : ι := Classical.epsilon (fun i => g ∈ H i)

def cv (p s : G) : Σ i, G ⧸ H i := ⟨kf H s, (p : G ⧸ H (kf H s))⟩

def encS : G → List G → List ((Σ i, G ⧸ H i) × G)
  | _, [] => []
  | p, s :: l => (cv H p s, p * s) :: encS (p * s) l

def gt (S : List ((Σ i, G ⧸ H i) × G)) : List (Σ i, G ⧸ H i) :=
  S.flatMap (fun q => [q.1, Xv H q.2])

def ee : G → List G → List (Σ i, G ⧸ H i)
  | _, [] => []
  | p, s :: l => cv H p s :: Xv H (p * s) :: ee (p * s) l

/-- The walk of a word read from the chamber `p`. -/
def Ee (p : G) (l : List G) : List (Σ i, G ⧸ H i) := Xv H p :: ee H p l

def galOK : G → List ((Σ i, G ⧸ H i) × G) → Prop
  | _, [] => True
  | h, q :: S => Mem H h q.1 ∧ Mem H q.2 q.1 ∧ galOK q.2 S

abbrev LH (c : ℕ) (S S' : List (Σ i, G ⧸ H i)) : Prop :=
  LHom (cosetComplex G H) (Xv H (Base.e (H := H))) c S S'

variable {H}

lemma chamber_exists (g : G) : ∃ τ ∈ (cosetComplex G H).tops,
    ∀ i, (⟨i, (g : G ⧸ H i)⟩ : Σ i, G ⧸ H i) ∈ τ := by
  unfold cosetComplex
  simp only
  rw [dif_pos ‹Finite G›]
  exact ⟨_, Finset.mem_image.2 ⟨g, @Finset.mem_univ _ (Fintype.ofFinite G) g, rfl⟩,
    fun i => Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩

lemma mems_of_face {s : Finset (Σ i, G ⧸ H i)} (h : (cosetComplex G H).IsFace s) :
    ∃ g, ∀ x ∈ s, Mem H g x := by
  obtain ⟨τ, hτ, hs⟩ := h
  unfold cosetComplex at hτ
  simp only at hτ
  rw [dif_pos ‹Finite G›] at hτ
  obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hτ
  refine ⟨g, fun x hx => ?_⟩
  obtain ⟨i, -, hi⟩ := Finset.mem_image.1 (hs hx)
  rw [← hi]; rfl

local instance (priority := 2000) instDecSig : DecidableEq (Σ i, G ⧸ H i) :=
  fun a b => Classical.propDecidable (a = b)

lemma face_of_mems {g : G} {s : Finset (Σ i, G ⧸ H i)} (hs : ∀ x ∈ s, Mem H g x) :
    (cosetComplex G H).IsFace s := by
  obtain ⟨τ, hτ, hmem⟩ := chamber_exists (H := H) g
  refine ⟨τ, hτ, fun x hx => ?_⟩
  have h := hs x hx
  obtain ⟨i, q⟩ := x
  simp only [Mem] at h
  subst h
  exact hmem i

lemma face3 {g : G} {a b d : Σ i, G ⧸ H i} (ha : Mem H g a) (hb : Mem H g b) (hd : Mem H g d) :
    (cosetComplex G H).IsFace {a, b, d} :=
  face_of_mems (g := g) (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption)

lemma face2 {g : G} {a b : Σ i, G ⧸ H i} (ha : Mem H g a) (hb : Mem H g b) :
    (cosetComplex G H).IsFace {a, b} :=
  face_of_mems (g := g) (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption)

lemma face1 (a : Σ i, G ⧸ H i) : (cosetComplex G H).IsFace {a} := by
  obtain ⟨i, q⟩ := a
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  exact face_of_mems (g := g) (by intro x hx; simp at hx; subst hx; rfl)

lemma mems_of_face2 {a b : Σ i, G ⧸ H i} (h : (cosetComplex G H).IsFace {a, b}) :
    ∃ g, Mem H g a ∧ Mem H g b := by
  obtain ⟨g, hg⟩ := mems_of_face h
  exact ⟨g, hg a (Finset.mem_insert_self a {b}),
    hg b (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))⟩

lemma mem_mul {g s : G} {u : Σ i, G ⧸ H i} (h : Mem H g u) (hs : s ∈ H u.1) :
    Mem H (g * s) u := by
  unfold Mem at h ⊢
  rw [h, QuotientGroup.eq]
  simpa using hs

lemma mem_diff {g g' : G} {u : Σ i, G ⧸ H i} (h : Mem H g u) (h' : Mem H g' u) :
    g⁻¹ * g' ∈ H u.1 := by
  unfold Mem at h h'
  rw [← QuotientGroup.eq, ← h, ← h']

lemma mem_Xv (g : G) : Mem H g (Xv H g) := rfl

lemma mem_cv (p s : G) : Mem H p (cv H p s) := rfl

lemma kf_spec {s : G} (hs : ∃ i, s ∈ H i) : s ∈ H (kf H s) := Classical.epsilon_spec hs

lemma mem_cv' {p s : G} (hs : ∃ i, s ∈ H i) : Mem H (p * s) (cv H p s) :=
  mem_mul (mem_cv p s) (kf_spec hs)

lemma kf_inv (s : G) : kf H s⁻¹ = kf H s := by
  unfold kf; simp only [inv_mem_iff]

lemma cv_inv {p s : G} (hs : ∃ i, s ∈ H i) : cv H (p * s) s⁻¹ = cv H p s := by
  unfold cv
  rw [kf_inv]
  have := mem_cv' (p := p) hs
  unfold Mem cv at this
  simp only at this
  rw [← this]

lemma Xv_eq {g g' : G} (h : Mem H g (Xv H g')) : Xv H g = Xv H g' := by
  unfold Mem Xv at h; unfold Xv; simp only at h; rw [h]

/-! ### Encodings -/

lemma gt_cons (q : (Σ i, G ⧸ H i) × G) (S : List ((Σ i, G ⧸ H i) × G)) :
    gt H (q :: S) = q.1 :: Xv H q.2 :: gt H S := by simp [gt]

lemma ee_eq_gt (p : G) (l : List G) : ee H p l = gt H (encS H p l) := by
  induction l generalizing p with
  | nil => rfl
  | cons s l ih => simp [ee, encS, gt, ih]

lemma ee_append (p : G) (l m : List G) : ee H p (l ++ m) = ee H p l ++ ee H (p * l.prod) m := by
  induction l generalizing p with
  | nil => simp [ee]
  | cons s l ih => simp [ee, ih, mul_assoc]

lemma Ee_append (p : G) (l m : List G) : Ee H p (l ++ m) = Ee H p l ++ ee H (p * l.prod) m := by
  simp [Ee, ee_append]

lemma Ee_cons (p s : G) (l : List G) : Ee H p (s :: l) = Xv H p :: cv H p s :: Ee H (p * s) l :=
  rfl

lemma Ee_last (p : G) (l : List G) : ∃ pre, Ee H p l = pre ++ [Xv H (p * l.prod)] := by
  induction l generalizing p with
  | nil => exact ⟨[], by simp [Ee, ee]⟩
  | cons s l ih =>
    obtain ⟨pre, h⟩ := ih (p * s)
    exact ⟨Xv H p :: cv H p s :: pre, by rw [Ee_cons, h]; simp [mul_assoc]⟩

lemma prod_invs (u : List G) : ((u.map (·⁻¹)).reverse).prod = u.prod⁻¹ := by
  rw [List.prod_inv_reverse]

lemma Ee_rev (u : List G) (hu : ∀ s ∈ u, ∃ i, s ∈ H i) (p : G) :
    Ee H (p * u.prod) ((u.map (·⁻¹)).reverse) = (Ee H p u).reverse := by
  induction u generalizing p with
  | nil => simp [Ee, ee]
  | cons s u ih =>
    have hs : ∃ i, s ∈ H i := hu s (by simp)
    have ih' := ih (fun t ht => hu t (by simp [ht])) (p * s)
    simp only [List.map_cons, List.reverse_cons, List.prod_cons]
    rw [Ee_append, prod_invs, ← mul_assoc, ih']
    simp only [Ee_cons, List.reverse_cons, List.append_assoc]
    simp [ee, cv_inv hs, mul_assoc]

lemma galOK_encS (p : G) (l : List G) (hl : ∀ s ∈ l, ∃ i, s ∈ H i) :
    galOK H p (encS H p l) := by
  induction l generalizing p with
  | nil => trivial
  | cons s l ih =>
    exact ⟨mem_cv p s, mem_cv' (hl s (by simp)), ih (p * s) (fun t ht => hl t (by simp [ht]))⟩

lemma galOK_walk (h : G) (S : List ((Σ i, G ⧸ H i) × G)) (hS : galOK H h S) :
    IsWalk (cosetComplex G H) (Xv H h :: gt H S) := by
  induction S generalizing h with
  | nil => exact walk1 (face1 _)
  | cons q S ih =>
    obtain ⟨v, h'⟩ := q
    obtain ⟨hv, hv', hS⟩ := hS
    have := ih h' hS
    rw [gt_cons]
    refine ⟨by simp, fun x _ => face1 x, ?_⟩
    exact List.IsChain.cons_cons (face2 (mem_Xv h) hv)
      (List.IsChain.cons_cons (face2 hv' (mem_Xv h')) this.2.2)

lemma gal_swap (h : G) (S S' : List ((Σ i, G ⧸ H i) × G)) (hS : galOK H h S)
    (hS' : galOK H h S') (hsn : S.map Prod.snd = S'.map Prod.snd) :
    LH H (2 * S.length) (Xv H h :: gt H S) (Xv H h :: gt H S') := by
  induction S generalizing h S' with
  | nil =>
    cases S' with
    | nil => exact LHom.refl _ _
    | cons _ _ => simp at hsn
  | cons q S ih =>
    cases S' with
    | nil => simp at hsn
    | cons q' S' =>
      obtain ⟨v, h₁⟩ := q
      obtain ⟨v', h₁'⟩ := q'
      simp only [List.map_cons, List.cons.injEq] at hsn
      obtain ⟨rfl, hsn⟩ := hsn
      obtain ⟨hv, hv1, hS⟩ := hS
      obtain ⟨hv', hv1', hS'⟩ := hS'
      have step : LH H 2 [Xv H h, v, Xv H h₁] [Xv H h, v', Xv H h₁] := by
        have a1 := (lhom_ins (X := cosetComplex G H) (v₀ := Xv H (Base.e (H := H)))
          (face3 (mem_Xv h) hv' hv)).ctx [] [Xv H h₁]
        have a2 := (lhom_del (X := cosetComplex G H) (v₀ := Xv H (Base.e (H := H)))
          (face3 hv1' hv1 (mem_Xv h₁))).ctx [Xv H h] []
        simpa using a1.trans a2
      have a1 : LH H 2 (Xv H h :: v :: Xv H h₁ :: gt H S) (Xv H h :: v' :: Xv H h₁ :: gt H S) := by
        simpa using step.ctx [] (gt H S)
      have a2 : LH H (2 * S.length) (Xv H h :: v' :: Xv H h₁ :: gt H S)
          (Xv H h :: v' :: Xv H h₁ :: gt H S') := by
        simpa using (ih h₁ S' hS hS' hsn).ctx [Xv H h, v'] []
      rw [gt_cons, gt_cons]
      exact (a1.trans a2).mono (by simp; omega)

/-- Collapsing the star of `c`. -/
lemma lhom_star (c : Σ i, G ⧸ H i) (P : List G) (hP : ∀ s ∈ P, s ∈ H c.1) (h : G)
    (hc : Mem H h c) :
    LH H 0 (c :: Xv H h :: gt H ((encS H h P).map (fun x => (c, x.2))))
      [c, Xv H (h * P.prod)] := by
  induction P generalizing h with
  | nil => simp [encS, gt]; exact LHom.refl _ _
  | cons s P ih =>
    have hs : s ∈ H c.1 := hP s (by simp)
    have a1 := (lhom_bt (X := cosetComplex G H) (v₀ := Xv H (Base.e (H := H))) (face2 hc (mem_Xv h))).ctx []
      (Xv H (h * s) :: gt H ((encS H (h * s) P).map (fun x => (c, x.2))))
    have a2 := ih (fun t ht => hP t (by simp [ht])) (h * s) (mem_mul hc hs)
    have := a1.trans a2
    simp only [encS, List.map_cons, gt_cons, List.prod_cons, ← mul_assoc]
    simpa using this

lemma galOK_star (c : Σ i, G ⧸ H i) (P : List G) (hP : ∀ s ∈ P, s ∈ H c.1) (h : G)
    (hc : Mem H h c) : galOK H h ((encS H h P).map (fun x => (c, x.2))) := by
  induction P generalizing h with
  | nil => trivial
  | cons s P ih =>
    have hs : s ∈ H c.1 := hP s (by simp)
    exact ⟨hc, mem_mul hc hs, ih (fun t ht => hP t (by simp [ht])) (h * s) (mem_mul hc hs)⟩

lemma length_encS (p : G) (l : List G) : (encS H p l).length = l.length := by
  induction l generalizing p with
  | nil => rfl
  | cons s l ih => simp [encS, ih]

/-- A relator of `H_i` collapses with at most `2 |P|` triangle moves. -/
lemma lhom_rel (i : ι) (P : List G) (hP : ∀ s ∈ P, s ∈ H i) (hprod : P.prod = 1) (q : G) :
    LH H (2 * P.length) (Ee H q P) [Xv H q] := by
  cases P with
  | nil => exact (LHom.refl 0 _).mono (by simp)
  | cons s P =>
    set c : Σ i, G ⧸ H i := ⟨i, (q : G ⧸ H i)⟩
    have hc : Mem H q c := rfl
    have hP' : ∀ t ∈ s :: P, t ∈ H c.1 := hP
    have a1 := gal_swap q (encS H q (s :: P)) ((encS H q (s :: P)).map (fun x => (c, x.2)))
      (galOK_encS q _ (fun t ht => ⟨i, hP t ht⟩)) (galOK_star c _ hP' q hc)
      (by simp [Function.comp_def])
    rw [length_encS] at a1
    have hs : s ∈ H c.1 := hP' s (by simp)
    have a2 := (lhom_star c P (fun t ht => hP' t (by simp [ht])) (q * s) (mem_mul hc hs)).ctx
      [Xv H q] []
    have a3 := (lhom_bt (X := cosetComplex G H) (v₀ := Xv H (Base.e (H := H))) (face2 (mem_Xv q) hc)).ctx [] []
    have e : q * s * P.prod = q := by
      rw [mul_assoc, ← List.prod_cons, hprod, mul_one]
    rw [e] at a2
    simp only [List.nil_append, List.append_nil, List.singleton_append] at a2 a3
    simp only [encS, List.map_cons, gt_cons] at a1
    have := a1.trans (a2.trans a3)
    simpa [Ee, ee_eq_gt, encS, gt_cons] using this

/-- A factor with trivial product can be removed from the middle of a word. -/
lemma lhom_factor {c : ℕ} (F : List G) (hF : ∀ q, LH H c (Ee H q F) [Xv H q])
    (hFp : F.prod = 1) (p : G) (A B : List G) :
    LH H c (Ee H p (A ++ F ++ B)) (Ee H p (A ++ B)) := by
  obtain ⟨pre, hpre⟩ := Ee_last (H := H) p A
  have e1 : Ee H p (A ++ F ++ B) = pre ++ Ee H (p * A.prod) F ++ ee H (p * A.prod) B := by
    rw [List.append_assoc, Ee_append, ee_append, hFp, mul_one, hpre]; simp [Ee]
  have e2 : Ee H p (A ++ B) = pre ++ [Xv H (p * A.prod)] ++ ee H (p * A.prod) B := by
    rw [Ee_append, hpre]
  rw [e1, e2]
  exact (hF _).ctx _ _

lemma lhom_conj {c : ℕ} (u P : List G) (hu : ∀ s ∈ u, ∃ i, s ∈ H i)
    (hP : ∀ q, LH H c (Ee H q P) [Xv H q]) (hPp : P.prod = 1) (q : G) :
    LH H c (Ee H q ((u.map (·⁻¹)).reverse ++ P ++ u)) [Xv H q] := by
  set q' := q * u.prod⁻¹
  have hq : q' * u.prod = q := by simp [q']
  have e1 : Ee H q ((u.map (·⁻¹)).reverse ++ P ++ u) =
      (ee H q' u).reverse ++ Ee H q' P ++ ee H q' u := by
    rw [List.append_assoc, Ee_append, ee_append, hPp, mul_one, prod_invs]
    have : Ee H q (List.map (·⁻¹) u).reverse = (Ee H q' u).reverse := by
      rw [← Ee_rev u hu q', hq]
    rw [this]; simp [Ee, q']
  rw [e1]
  have a1 := (hP q').ctx (ee H q' u).reverse (ee H q' u)
  have hw := galOK_walk q' _ (galOK_encS (H := H) q' u hu)
  rw [← ee_eq_gt] at hw
  obtain ⟨pre, hpre⟩ := Ee_last (H := H) q' u
  have a2 := lhom_pal (X := cosetComplex G H) (v₀ := Xv H (Base.e (H := H))) (ee H q' u) (Xv H q') (Xv H q)
    hw.2.2 (by rw [← Ee, hpre, hq]; simp)
  rw [List.reverse_cons] at a2
  exact a1.trans a2

/-! ### Free-group words -/

/-- The value of a letter. -/
def lv (x : CosetGen H × Bool) : G := cond x.2 x.1.1 x.1.1⁻¹

lemma lv_mem (x : CosetGen H × Bool) : ∃ i, lv x ∈ H i := by
  obtain ⟨⟨g, -, i, hi⟩, b⟩ := x
  cases b
  · exact ⟨i, inv_mem hi⟩
  · exact ⟨i, hi⟩

lemma lv_not (x : CosetGen H) (b : Bool) : lv (x, !b) = (lv (x, b))⁻¹ := by
  cases b <;> simp [lv]

lemma vals_mem (L : List (CosetGen H × Bool)) : ∀ s ∈ L.map lv, ∃ i, s ∈ H i := by
  intro s hs
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hs
  exact lv_mem x

lemma lhom_red_step {L₁ L₂ : List (CosetGen H × Bool)} (h : FreeGroup.Red.Step L₁ L₂) (p : G) :
    LH H 0 (Ee H p (L₁.map lv)) (Ee H p (L₂.map lv)) := by
  cases h with
  | @not L₁ L₂ x b =>
    have hv : ∃ i, (lv (x, b))⁻¹ ∈ H i := by
      obtain ⟨i, hi⟩ := lv_mem (x, b); exact ⟨i, inv_mem hi⟩
    have hF : ∀ q, LH H 0 (Ee H q [lv (x, b), (lv (x, b))⁻¹]) [Xv H q] := by
      intro q
      have := lhom_conj (H := H) [(lv (x, b))⁻¹] [] (by simpa using hv)
        (fun q => LHom.refl 0 _) (by simp) q
      simpa using this
    have := lhom_factor _ hF (by simp) p (L₁.map lv) (L₂.map lv)
    simpa [lv_not] using this

lemma lhom_red {L₁ L₂ : List (CosetGen H × Bool)} (h : FreeGroup.Red L₁ L₂) (p : G) :
    LH H 0 (Ee H p (L₁.map lv)) (Ee H p (L₂.map lv)) := by
  unfold FreeGroup.Red at h
  induction h with
  | refl => exact LHom.refl _ _
  | tail _ hs ih => exact ih.trans (lhom_red_step hs p)

/-- The letter of a group element (none for `1`). -/
def toLet (g : G) : Option (CosetGen H × Bool) :=
  if h : g ≠ 1 ∧ ∃ i, g ∈ H i then some (⟨g, h⟩, true) else none

lemma lhom_filter (l : List G) (hl : ∀ s ∈ l, ∃ i, s ∈ H i) (p : G) :
    LH H 0 (Ee H p l) (Ee H p ((l.filterMap (toLet (H := H))).map lv)) := by
  induction l generalizing p with
  | nil => exact LHom.refl _ _
  | cons s l ih =>
    have ih' := ih (fun t ht => hl t (by simp [ht]))
    by_cases hs : s = 1
    · subst hs
      have hF : ∀ q, LH H 0 (Ee H q [1]) [Xv H q] := fun q => by
        have := (lhom_bt (X := cosetComplex G H) (v₀ := Xv H (Base.e (H := H)))
          (face2 (mem_Xv q) (mem_cv q 1))).ctx [] []
        simpa [Ee, ee] using this
      have := lhom_factor [1] hF (by simp) p [] l
      rw [List.filterMap_cons_none (by simp [toLet])]
      simpa using this.trans (ih' p)
    · rw [List.filterMap_cons_some (b := (⟨s, hs, hl s (by simp)⟩, true))
        (by simp [toLet, hs, hl s (by simp)])]
      simpa [Ee_cons, lv] using (ih' (p * s)).ctx [Xv H p, cv H p s] []

lemma prod_filter (l : List G) (hl : ∀ s ∈ l, ∃ i, s ∈ H i) :
    ((l.filterMap (toLet (H := H))).map lv).prod = l.prod := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    have ih' := ih (fun t ht => hl t (by simp [ht]))
    by_cases hs : s = 1
    · subst hs
      rw [List.filterMap_cons_none (by simp [toLet])]
      simpa using ih'
    · rw [List.filterMap_cons_some (b := (⟨s, hs, hl s (by simp)⟩, true))
        (by simp [toLet, hs, hl s (by simp)])]
      simp [lv, ih']

lemma mk_map_true (l : List (CosetGen H)) :
    FreeGroup.mk (l.map (·, true)) = (l.map FreeGroup.of).prod := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, ← ih, FreeGroup.of, FreeGroup.mul_mk]
    rfl

lemma vals_invRev (L : List (CosetGen H × Bool)) :
    (FreeGroup.invRev L).map lv = ((L.map lv).map (·⁻¹)).reverse := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [FreeGroup.invRev_cons, List.map_append, ih]
    obtain ⟨x, b⟩ := a
    simp [FreeGroup.invRev, lv_not]

lemma rel_letters {ρ : FreeGroup (CosetGen H)} (h : ρ ∈ cosetRel H ∨ ρ⁻¹ ∈ cosetRel H) :
    ∃ Pl : List (CosetGen H × Bool), FreeGroup.mk Pl = ρ ∧ ∃ i,
      (∀ s ∈ Pl.map lv, s ∈ H i) ∧ (Pl.map lv).prod = 1 ∧ Pl.length ≤ 3 := by
  rcases h with h | h
  · obtain ⟨i, h⟩ := Set.mem_iUnion.1 h
    obtain ⟨l, -, h3, hmem, hprod, rfl⟩ := h
    refine ⟨l.map (·, true), mk_map_true l, i, ?_, ?_, by simpa using h3⟩
    · intro s hs
      rw [List.map_map] at hs
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs
      exact hmem x hx
    · simpa [lv, Function.comp_def] using hprod
  · obtain ⟨i, h⟩ := Set.mem_iUnion.1 h
    obtain ⟨l, -, h3, hmem, hprod, hρ⟩ := h
    refine ⟨FreeGroup.invRev (l.map (·, true)), ?_, i, ?_, ?_, by simpa [FreeGroup.invRev] using h3⟩
    · rw [← FreeGroup.inv_mk, mk_map_true, ← hρ, inv_inv]
    · intro s hs
      rw [vals_invRev] at hs
      simp only [List.mem_reverse, List.map_map, List.mem_map] at hs
      obtain ⟨x, hx, rfl⟩ := hs
      exact inv_mem (hmem x hx)
    · rw [vals_invRev, ← List.prod_inv_reverse]
      simpa [lv, Function.comp_def] using hprod

lemma lhom_total (l : List (FreeGroup (CosetGen H) × FreeGroup (CosetGen H)))
    (hl : ∀ p ∈ l, p.2 ∈ cosetRel H ∨ p.2⁻¹ ∈ cosetRel H) :
    ∃ Lt : List (CosetGen H × Bool), FreeGroup.mk Lt = (l.map (fun p => p.1⁻¹ * p.2 * p.1)).prod ∧
      ∀ q, LH H (6 * l.length) (Ee H q (Lt.map lv)) [Xv H q] := by
  induction l with
  | nil => exact ⟨[], by simp [FreeGroup.one_eq_mk], fun q => LHom.refl _ _⟩
  | cons p l ih =>
    obtain ⟨Lt, hmk, hLt⟩ := ih (fun p hp => hl p (by simp [hp]))
    obtain ⟨u, ρ⟩ := p
    obtain ⟨Pl, hPl, i, hmem, hprod, hlen⟩ := rel_letters (hl (u, ρ) (by simp))
    set U := u.toWord
    refine ⟨FreeGroup.invRev U ++ Pl ++ U ++ Lt, ?_, ?_⟩
    · rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk,
        hPl, FreeGroup.mk_toWord, hmk]
      simp
    · intro q
      have hF : ∀ q, LH H 6 (Ee H q ((FreeGroup.invRev U ++ Pl ++ U).map lv)) [Xv H q] := by
        intro q
        have := lhom_conj (U.map lv) (Pl.map lv) (vals_mem U)
          (fun q => ((lhom_rel i _ hmem hprod q).mono
            (show 2 * (Pl.map lv).length ≤ 6 by simp; omega) : LH H 6 _ _)) hprod q
        simpa [vals_invRev] using this
      have hFp : ((FreeGroup.invRev U ++ Pl ++ U).map lv).prod = 1 := by
        rw [List.map_append, List.map_append, vals_invRev, List.prod_append, List.prod_append,
          prod_invs, hprod]; simp
      have := (lhom_factor _ hF hFp q [] (Lt.map lv)).trans (hLt q)
      simp only [List.nil_append, List.map_append] at this ⊢
      refine this.mono ?_
      simp; omega

/-! ### From a loop to a word -/

lemma gallery (T : List (Σ i, G ⧸ H i)) : ∀ (v : Σ i, G ⧸ H i) (g₀ e : G), Mem H g₀ v →
    (v :: T).IsChain (fun x y => (cosetComplex G H).IsFace {x, y}) →
    (∀ y ∈ (v :: T).getLast?, Mem H e y) →
    ∃ S, galOK H g₀ S ∧ S.length = T.length + 1 ∧ (S.map Prod.snd).getLast? = some e ∧
      LH H T.length (gt H S) (v :: T ++ [Xv H e]) := by
  induction T with
  | nil =>
    intro v g₀ e hv _ he
    exact ⟨[(v, e)], ⟨hv, he v (by simp), trivial⟩, rfl, rfl, by simp [gt]; exact LHom.refl _ _⟩
  | cons w T ih =>
    intro v g₀ e hv hc he
    rw [List.isChain_cons_cons] at hc
    obtain ⟨g₁, hg₁v, hg₁w⟩ := mems_of_face2 hc.1
    obtain ⟨S, hS, hlen, hlast, hL⟩ := ih w g₁ e hg₁w hc.2
      (fun y hy => he y (by rw [List.getLast?_cons_cons]; exact hy))
    refine ⟨(v, g₁) :: S, ⟨hv, hg₁v, hS⟩, by simp [hlen], ?_, ?_⟩
    · cases S with
      | nil => simp at hlen
      | cons q S => simpa [List.getLast?_cons_cons] using hlast
    · have a1 := hL.ctx [v, Xv H g₁] []
      have a2 := (lhom_del (X := cosetComplex G H) (v₀ := Xv H (Base.e (H := H)))
        (face3 hg₁v (mem_Xv g₁) hg₁w)).ctx [] (T ++ [Xv H e])
      simp only [List.nil_append, List.append_nil, List.cons_append] at a1 a2
      rw [gt_cons]
      exact (a1.trans a2).mono (by simp)

def diffs : G → List G → List G
  | _, [] => []
  | h, h' :: C => (h⁻¹ * h') :: diffs h' C

lemma encS_diffs (h : G) (C : List G) : (encS H h (diffs h C)).map Prod.snd = C := by
  induction C generalizing h with
  | nil => rfl
  | cons h' C ih => simp [diffs, encS, ih]

lemma diffs_mem (h : G) (S : List ((Σ i, G ⧸ H i) × G)) (hS : galOK H h S) :
    ∀ s ∈ diffs h (S.map Prod.snd), ∃ i, s ∈ H i := by
  induction S generalizing h with
  | nil => simp [diffs]
  | cons q S ih =>
    obtain ⟨v, h'⟩ := q
    obtain ⟨hv, hv', hS⟩ := hS
    intro s hs
    simp only [List.map_cons, diffs, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact ⟨v.1, mem_diff hv hv'⟩
    · exact ih h' hS s hs

lemma diffs_prod (h : G) (C : List G) : h * (diffs h C).prod = C.getLast?.getD h := by
  induction C generalizing h with
  | nil => simp [diffs]
  | cons h' C ih => simp [diffs, ← mul_assoc, ih, List.getLast?_cons]

lemma diffs_length (h : G) (C : List G) : (diffs h C).length = C.length := by
  induction C generalizing h with
  | nil => rfl
  | cons h' C ih => simp [diffs, ih]

/-! ### Contracting a loop -/

theorem main_fin (L : List (Σ i, G ⧸ H i))
    (hL : (cosetComplex G H).IsPathFrom (Xv H (Base.e (H := H))) (Xv H (Base.e (H := H))) L) (A : ℕ)
    (hA : ∀ w : FreeGroup (CosetGen H), FreeGroup.lift Subtype.val w = 1 →
      wordLength w ≤ L.length - 1 → area (cosetRel H) w ≤ A) :
    Rw (cosetComplex G H) (Xv H (Base.e (H := H))) (3 * (L.length - 1) + 6 * A) L [Xv H (Base.e (H := H))] := by
  have hW : WLoop (cosetComplex G H) (Xv H (Base.e (H := H))) L := ⟨walk_of_path hL.1, hL.2.1, hL.2.2⟩
  obtain ⟨⟨hne, -, hch⟩, hh, hl⟩ := hL
  have hnrm : nrm L = L := by
    cases L with
    | nil => exact absurd rfl hne
    | cons a l => exact dd_of_path hch
  suffices h : LH H (3 * (L.length - 1) + 6 * A) L [Xv H (Base.e (H := H))] by
    have := h.hom.2 hW
    rwa [hnrm] at this
  cases L with
  | nil => exact absurd rfl hne
  | cons a rest =>
  simp only [List.head?_cons, Option.some.injEq] at hh
  subst hh
  cases rest with
  | nil => exact LHom.refl _ _
  | cons v T =>
  have fc := hch.imp (fun _ _ h => h.2)
  rw [List.isChain_cons_cons] at fc
  rw [List.getLast?_cons_cons] at hl
  obtain ⟨g₀, hg1, hgv⟩ := mems_of_face2 fc.1
  obtain ⟨S, hS, hlen, hlast, hgal⟩ := gallery T v g₀ g₀ hgv fc.2 (fun y hy => by
    rw [hl] at hy; cases hy; exact hg1)
  have hXg : Xv H g₀ = Xv H (Base.e (H := H)) := Xv_eq hg1
  set sv := diffs g₀ (S.map Prod.snd)
  have hsv : ∀ s ∈ sv, ∃ i, s ∈ H i := diffs_mem g₀ S hS
  have hsvp : sv.prod = 1 := by
    have := diffs_prod g₀ (S.map Prod.snd)
    rw [hlast] at this
    simpa using this
  have hsvl : sv.length = T.length + 1 := by simp [sv, diffs_length, hlen]
  have aswap := gal_swap g₀ S (encS H g₀ sv) hS (galOK_encS g₀ sv hsv) (by rw [encS_diffs])
  rw [← ee_eq_gt] at aswap
  change LH H _ (Xv H g₀ :: gt H S) (Ee H g₀ sv) at aswap
  set Lw := sv.filterMap (toLet (H := H))
  have afilt := lhom_filter sv hsv g₀
  have hlift : FreeGroup.lift Subtype.val (FreeGroup.mk Lw) = 1 := by
    exact (prod_filter sv hsv).trans hsvp
  have hwl : wordLength (FreeGroup.mk Lw) ≤ (Xv H (Base.e (H := H)) :: v :: T).length - 1 := by
    refine (wl_le Lw).trans ?_
    have : Lw.length ≤ sv.length := List.length_filterMap_le _ _
    simp only [List.length_cons]; omega
  have harea := hA _ hlift hwl
  obtain ⟨l, hlc, hll⟩ : ∃ l : List (FreeGroup (CosetGen H) × FreeGroup (CosetGen H)),
      ((∀ p ∈ l, p.2 ∈ cosetRel H ∨ p.2⁻¹ ∈ cosetRel H) ∧
        FreeGroup.mk Lw = (l.map (fun p => p.1⁻¹ * p.2 * p.1)).prod) ∧ l.length ≤ A := by
    have : area (cosetRel H) (FreeGroup.mk Lw) < ((A + 1 : ℕ) : ℕ∞) :=
      lt_of_le_of_lt harea (by exact_mod_cast Nat.lt_succ_self A)
    unfold area at this
    rw [iInf_lt_iff] at this
    obtain ⟨l, hl⟩ := this
    rw [iInf_lt_iff] at hl
    obtain ⟨hc, hlt⟩ := hl
    exact ⟨l, hc, by exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast hlt)⟩
  obtain ⟨Lt, hmk, hLt⟩ := lhom_total l hlc.1
  have hred : FreeGroup.reduce Lw = FreeGroup.reduce Lt := by
    rw [← FreeGroup.toWord_mk, ← FreeGroup.toWord_mk, hmk, ← hlc.2]
  have ar1 := lhom_red (FreeGroup.reduce.red : FreeGroup.Red Lw (FreeGroup.reduce Lw)) g₀
  have ar2 := (lhom_red (FreeGroup.reduce.red : FreeGroup.Red Lt (FreeGroup.reduce Lt)) g₀).symm
  rw [hred] at ar1
  have aend := hLt g₀
  obtain ⟨M, hM⟩ := List.getLast?_eq_some_iff.1 hl
  have ast := (lhom_stutter (X := cosetComplex G H) (v₀ := Xv H (Base.e (H := H))) (a := Xv H (Base.e (H := H)))).ctx
    (Xv H (Base.e (H := H)) :: M) []
  have agal := hgal.ctx [Xv H g₀] []
  rw [hXg] at agal aswap aend
  rw [hM] at agal
  simp only [List.append_nil, List.cons_append, List.append_assoc]
    at ast agal
  have key : LH H (T.length + 2 * S.length + 6 * l.length) (Xv H (Base.e (H := H)) :: v :: T) [Xv H (Base.e (H := H))] := by
    rw [hM]
    have := ast.symm.trans (agal.symm.trans (aswap.trans (afilt.trans (ar1.trans
      (ar2.trans aend)))))
    exact this.mono (by omega)
  exact key.mono (by simp only [List.length_cons]; omega)

end Coset

section Area

variable {S : Type*}

/-- `l` is a product of conjugates of relators: the data witnessing `Area_R(w) ≤ |l|`. -/
def Valid (R : Set (FreeGroup S)) (w : FreeGroup S) (l : List (FreeGroup S × FreeGroup S)) :
    Prop :=
  (∀ p ∈ l, p.2 ∈ R ∨ p.2⁻¹ ∈ R) ∧ w = (l.map (fun p => p.1⁻¹ * p.2 * p.1)).prod

lemma area_le {R : Set (FreeGroup S)} {w : FreeGroup S} {l} (h : Valid R w l) :
    area R w ≤ l.length :=
  iInf_le_of_le l (iInf_le_of_le h le_rfl)

lemma area_attained {R : Set (FreeGroup S)} {w : FreeGroup S} (h : area R w ≠ ⊤) :
    ∃ l, Valid R w l ∧ (l.length : ℕ∞) = area R w := by
  have hne : ∃ l, Valid R w l := by
    by_contra hc
    push Not at hc
    apply h
    simp only [area]
    exact le_antisymm le_top (le_iInf fun l => le_iInf fun hl => absurd hl (hc l))
  have : Nonempty {l // Valid R w l} := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  obtain ⟨⟨l, hl⟩, hmin⟩ := csInf_mem (Set.range_nonempty
    (fun l : {l // Valid R w l} => (l.1.length : ℕ∞)))
  refine ⟨l, hl, ?_⟩
  simp only at hmin
  rw [hmin]
  apply le_antisymm
  · exact le_iInf fun l' => le_iInf fun hl' => csInf_le (OrderBot.bddBelow _) ⟨⟨l', hl'⟩, rfl⟩
  · exact le_csInf (Set.range_nonempty _) (by rintro _ ⟨⟨l', hl'⟩, rfl⟩; exact area_le hl')

lemma area_one (R : Set (FreeGroup S)) : area R 1 = 0 :=
  le_antisymm (by simpa using area_le (R := R) (w := 1) (l := []) ⟨by simp, by simp⟩) bot_le

lemma area_mul_le (R : Set (FreeGroup S)) (a b : FreeGroup S) :
    area R (a * b) ≤ area R a + area R b := by
  by_cases ha : area R a = ⊤
  · simp [ha]
  by_cases hb : area R b = ⊤
  · simp [hb]
  obtain ⟨la, ⟨ha1, ha2⟩, hla⟩ := area_attained ha
  obtain ⟨lb, ⟨hb1, hb2⟩, hlb⟩ := area_attained hb
  rw [← hla, ← hlb]
  have := area_le (R := R) (w := a * b) (l := la ++ lb)
    ⟨fun p hp => by
      rcases List.mem_append.1 hp with h | h
      · exact ha1 p h
      · exact hb1 p h,
     by rw [List.map_append, List.prod_append, ← ha2, ← hb2]⟩
  simpa using this

lemma area_conj_le (R : Set (FreeGroup S)) (a u : FreeGroup S) :
    area R (u⁻¹ * a * u) ≤ area R a := by
  by_cases ha : area R a = ⊤
  · simp [ha]
  obtain ⟨l, ⟨h1, h2⟩, hl⟩ := area_attained ha
  rw [← hl]
  have key : ∀ l : List (FreeGroup S × FreeGroup S),
      u⁻¹ * (l.map (fun p => p.1⁻¹ * p.2 * p.1)).prod * u =
        ((l.map (fun p => (p.1 * u, p.2))).map (fun p => p.1⁻¹ * p.2 * p.1)).prod := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih =>
      simp only [List.map_cons, List.prod_cons] at ih ⊢
      rw [← ih]; group
  have := area_le (R := R) (w := u⁻¹ * a * u) (l := l.map (fun p => (p.1 * u, p.2)))
    ⟨fun p hp => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact h1 q hq,
     by rw [h2, key]⟩
  simpa using this

lemma area_inv_le (R : Set (FreeGroup S)) (a : FreeGroup S) : area R a⁻¹ ≤ area R a := by
  by_cases ha : area R a = ⊤
  · simp [ha]
  obtain ⟨l, ⟨h1, h2⟩, hl⟩ := area_attained ha
  rw [← hl]
  have key : ∀ l : List (FreeGroup S × FreeGroup S),
      ((l.map (fun p => p.1⁻¹ * p.2 * p.1)).prod)⁻¹ =
        (((l.map (fun p => (p.1, p.2⁻¹))).reverse).map (fun p => p.1⁻¹ * p.2 * p.1)).prod := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih =>
      simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.map_append,
        List.prod_append, List.map_nil, List.prod_nil, mul_inv_rev] at ih ⊢
      rw [ih]; group
  have := area_le (R := R) (w := a⁻¹) (l := (l.map (fun p => (p.1, p.2⁻¹))).reverse)
    ⟨fun p hp => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hp)
      rcases h1 q hq with h | h
      · exact Or.inr (by simpa using h)
      · exact Or.inl h,
     by rw [h2, key]⟩
  simpa using this

lemma area_of_mem {R : Set (FreeGroup S)} {ρ : FreeGroup S} (h : ρ ∈ R) : area R ρ ≤ 1 := by
  simpa using area_le (R := R) (w := ρ) (l := [(1, ρ)]) ⟨by simp [h], by simp⟩

/-- The words with a finite area form a normal subgroup containing `R`. -/
def finiteArea (R : Set (FreeGroup S)) : Subgroup (FreeGroup S) where
  carrier := {w | area R w ≠ ⊤}
  one_mem' := by simp [area_one]
  mul_mem' := by
    intro a b ha hb
    exact ne_top_of_le_ne_top (by rw [Ne, ENat.add_eq_top]; exact not_or.2 ⟨ha, hb⟩)
      (area_mul_le R a b)
  inv_mem' := by
    intro a ha
    exact ne_top_of_le_ne_top ha (area_inv_le R a)

instance (R : Set (FreeGroup S)) : (finiteArea R).Normal where
  conj_mem a ha u := by
    have := area_conj_le R a u⁻¹
    rw [inv_inv] at this
    exact ne_top_of_le_ne_top ha this

lemma area_ne_top {R : Set (FreeGroup S)} {w : FreeGroup S} (h : w ∈ Subgroup.normalClosure R) :
    area R w ≠ ⊤ := by
  have : Subgroup.normalClosure R ≤ finiteArea R :=
    Subgroup.normalClosure_le_normal fun ρ hρ =>
      ne_top_of_le_ne_top (by simp) (area_of_mem hρ)
  exact this h


end Area

section Final

local instance (priority := 2000) instDecSig' {G : Type*} [Group G] {ι : Type*}
    {H : ι → Subgroup G} : DecidableEq (Σ i, G ⧸ H i) :=
  fun a b => Classical.propDecidable (a = b)

lemma rw_eqv {V : Type*} {X : WComplex V} {v₀ : V} {n : ℕ} {A B : List V}
    (h : Rw X v₀ n A B) : Relation.EqvGen (fun A B => X.TR v₀ A B ∨ X.BT v₀ A B) A B := by
  induction h with
  | refl n A => exact .refl _
  | bt h _ ih => exact .trans _ _ _ (.rel _ _ (Or.inr h)) ih
  | tr h _ ih => exact .trans _ _ _ (.rel _ _ (Or.inl h)) ih

lemma finite_words {S : Type*} [Finite S] (n : ℕ) :
    {w : FreeGroup S | wordLength w ≤ n}.Finite := by
  have : {w : FreeGroup S | wordLength w ≤ n} ⊆
      FreeGroup.mk '' {L : List (S × Bool) | L.length ≤ n} := by
    intro w hw
    exact ⟨w.toWord, by simpa [wordLength, FreeGroup.norm] using hw, FreeGroup.mk_toWord⟩
  exact ((List.finite_length_le _ n).image _).subset this

lemma eqv_rtg {α : Type*} {R : α → α → Prop} (hR : ∀ a b, R a b → R b a) {a b : α}
    (h : Relation.EqvGen R a b) : Relation.ReflTransGen R a b := by
  have key : Relation.ReflTransGen R a b ∧ Relation.ReflTransGen R b a := by
    induction h with
    | rel x y h => exact ⟨.single h, .single (hR _ _ h)⟩
    | refl x => exact ⟨.refl, .refl⟩
    | symm x y _ ih => exact ⟨ih.2, ih.1⟩
    | trans x y z _ _ ih₁ ih₂ => exact ⟨ih₁.1.trans ih₂.1, ih₂.2.trans ih₁.2⟩
  exact key.1

/-- (1) If the `H_i` generate `G`, the coset complex is connected. -/
theorem connected_of_closure {G : Type*} [Group G] [Finite G] {ι : Type*} [Fintype ι]
    [Nonempty ι] (H : ι → Subgroup G) (hgen : Subgroup.closure (⋃ i, (H i : Set G)) = ⊤) :
    (cosetComplex G H).IsConnected := by
  let _ : Base H := ⟨Classical.arbitrary ι, 1⟩
  set X := cosetComplex G H
  have hvert : ∀ u, u ∈ X.vertices := fun u =>
    vert_of_face X (face1 u) (Finset.mem_singleton_self u)
  have hsame : ∀ (g : G) (i j : ι), Relation.EqvGen (fun x y => X.IsFace {x, y})
      ⟨i, (g : G ⧸ H i)⟩ ⟨j, (g : G ⧸ H j)⟩ :=
    fun g i j => .rel _ _ (face2 (H := H) (g := g) (a := ⟨i, (g : G ⧸ H i)⟩)
      (b := ⟨j, (g : G ⧸ H j)⟩) rfl rfl)
  have hstep : ∀ i (x : G), x ∈ Subgroup.closure (⋃ k, (H k : Set G)) → ∀ g : G,
      Relation.EqvGen (fun x y => X.IsFace {x, y})
        ⟨i, (g : G ⧸ H i)⟩ ⟨i, ((g * x : G) : G ⧸ H i)⟩ := by
    intro i x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      intro g
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hx
      have e : (⟨k, ((g : G) : G ⧸ H k)⟩ : Σ i, G ⧸ H i) = ⟨k, ((g * x : G) : G ⧸ H k)⟩ := by
        simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
        rw [QuotientGroup.eq]; simpa using hk
      have := hsame (g * x) k i
      rw [← e] at this
      exact (hsame g i k).trans _ _ _ this
    | one => intro g; simpa using Relation.EqvGen.refl _
    | mul x y _ _ ihx ihy =>
      intro g
      have := ihy (g * x)
      rw [mul_assoc] at this
      exact (ihx g).trans _ _ _ this
    | inv x _ ih =>
      intro g
      have := ih (g * x⁻¹)
      simp only [inv_mul_cancel_right] at this
      exact this.symm
  refine ⟨⟨⟨Classical.arbitrary ι, (1 : G)⟩, hvert _⟩, ?_⟩
  rintro ⟨i, q⟩ - ⟨j, q'⟩ -
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q'
  have h1 := hstep i (a⁻¹ * b) (by rw [hgen]; trivial) a
  rw [mul_inv_cancel_left] at h1
  have h2 := eqv_rtg (fun x y h => by rwa [Finset.pair_comm]) (h1.trans _ _ _ (hsame b i j))
  obtain ⟨l, hl, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen h2
  obtain ⟨t, ht⟩ := dd_head (⟨i, (a : G ⧸ H i)⟩ : Σ i, G ⧸ H i) l
  refine ⟨dd _ l, ⟨by simp [ht], fun u _ => hvert u, dd_chain _ l hl⟩, by simp [ht], ?_⟩
  rw [dd_getLast, List.getLast?_eq_getLast_of_ne_nil (by simp), hlast]

/-- (2) A presentation by the multiplication tables makes the coset complex 1-connected. -/
theorem oneConnected_of_pres {G : Type*} [Group G] [Finite G] {ι : Type*} [Fintype ι]
    [Nonempty ι] (H : ι → Subgroup G) (hconn : (cosetComplex G H).IsConnected)
    (hpres : ∀ w : FreeGroup (CosetGen H), FreeGroup.lift Subtype.val w = 1 →
      w ∈ Subgroup.normalClosure (cosetRel H)) :
    (cosetComplex G H).IsOneConnected := by
  refine ⟨hconn, ?_⟩
  rintro ⟨i, q⟩ - P hP
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  let _ : Base H := ⟨i, g⟩
  obtain ⟨A, hA⟩ := ((finite_words (S := CosetGen H) (P.length - 1)).image
    (fun w => (area (cosetRel H) w).toNat)).bddAbove
  have hA' : ∀ w : FreeGroup (CosetGen H), FreeGroup.lift Subtype.val w = 1 →
      wordLength w ≤ P.length - 1 → area (cosetRel H) w ≤ A := by
    intro w h1 h2
    rw [← ENat.natCast_toNat (area_ne_top (hpres w h1))]
    exact_mod_cast hA ⟨w, h2, rfl⟩
  exact rw_eqv (main_fin P hP A hA')

end Final

section Coh

variable {V : Type*} {Λ : Type*} [Group Λ] (φ : V → V → Λ)

/-- The product of `φ` along a path, latest edge leftmost. -/
def pp : List V → Λ
  | [] => 1
  | [_] => 1
  | a :: b :: l => pp (b :: l) * φ a b

lemma pp_split (x : V) (B : List V) :
    ∀ A : List V, pp φ (A ++ x :: B) = pp φ (x :: B) * pp φ (A ++ [x])
  | [] => by simp [pp]
  | [a] => by simp [pp]
  | a :: c :: A => by
    have := pp_split x B (c :: A)
    simp only [List.cons_append] at this ⊢
    simp only [pp, this, mul_assoc]

variable {φ}

lemma pp_rev {X : WComplex V} (hC : X.IsC1 φ) :
    ∀ l : List V, l.IsChain (fun u v => u ≠ v ∧ X.IsFace {u, v}) →
      pp φ l.reverse = (pp φ l)⁻¹
  | [], _ => by simp [pp]
  | [a], _ => by simp [pp]
  | a :: b :: l, h => by
    rw [List.isChain_cons_cons] at h
    have ih := pp_rev hC (b :: l) h.2
    have hba : φ b a = (φ a b)⁻¹ :=
      hC b a ⟨h.1.1.symm, by rw [Finset.pair_comm]; exact h.1.2⟩
    have e : (a :: b :: l).reverse = l.reverse ++ b :: [a] := by simp
    have e' : l.reverse ++ [b] = (b :: l).reverse := by simp
    rw [e, pp_split, e', ih]
    simp [pp, hba]

lemma pp_step {X : WComplex V} (hZ : X.IsZ1 φ) {v₀ : V} {P P' : List V}
    (h : X.TRstep v₀ P P' ∨ X.BTstep v₀ P P') : pp φ P = pp φ P' := by
  rcases h with ⟨u, v, w, Q₀, Q₁, huv, hvw, huw, hf, hQ₀, hQ₁, rfl, rfl⟩ |
    ⟨u, v, Q₀, Q₁, hQ₀, hQ₁, huv, hf, rfl, rfl⟩
  · obtain ⟨Q, rfl⟩ := List.getLast?_eq_some_iff.1 hQ₀.2.2
    obtain ⟨R, hR⟩ := List.getLast?_eq_some_iff.1 hQ₁.2.2
    have e1 : pcat (pcat (Q ++ [u]) [u, v, w]) Q₁.reverse = Q ++ u :: (v :: w :: R.reverse) := by
      simp [pcat, hR]
    have e2 : pcat (pcat (Q ++ [u]) [u, w]) Q₁.reverse = Q ++ u :: (w :: R.reverse) := by
      simp [pcat, hR]
    rw [e1, e2, pp_split φ u (v :: w :: R.reverse) Q, pp_split φ u (w :: R.reverse) Q]
    congr 1
    have hc := hZ.2 u v w ⟨huv, hvw, huw, hf⟩
    have hwu : φ w u = (φ u w)⁻¹ :=
      hZ.1 w u ⟨huw.symm, face_sub X hf (by intro x; simp; tauto)⟩
    simp only [d1, hwu] at hc
    have hb := eq_inv_of_mul_eq_one_right hc
    simp only [pp, mul_assoc]
    rw [hb]; group
  · obtain ⟨Q, rfl⟩ := List.getLast?_eq_some_iff.1 hQ₀.2.2
    obtain ⟨R, hR⟩ := List.getLast?_eq_some_iff.1 hQ₁.2.2
    have e1 : pcat (pcat (Q ++ [u]) [u, v, u]) Q₁.reverse = Q ++ u :: (v :: u :: R.reverse) := by
      simp [pcat, hR]
    have e2 : pcat (pcat (Q ++ [u]) [u]) Q₁.reverse = Q ++ u :: R.reverse := by
      simp [pcat, hR]
    rw [e1, e2, pp_split φ u (v :: u :: R.reverse) Q, pp_split φ u R.reverse Q]
    congr 1
    have huv' : φ u v = (φ v u)⁻¹ := hZ.1 u v ⟨huv, hf⟩
    simp [pp, huv', mul_assoc]

/-- (3) A 1-connected complex has trivial `H¹` with any coefficient group. -/
theorem h1Trivial_of_oneConnected {V : Type*} (X : WComplex V) (hX : X.IsOneConnected)
    (Λ : Type*) [Group Λ] : X.H1Trivial Λ := by
  intro φ hZ
  obtain ⟨⟨v₀, hv₀⟩, hconn⟩ := hX.1
  have key : ∀ A B, Relation.EqvGen (fun A B => X.TR v₀ A B ∨ X.BT v₀ A B) A B →
      pp φ A = pp φ B := by
    intro A B h
    induction h with
    | rel A B h =>
      rcases h with (h | h) | (h | h)
      · exact pp_step hZ (Or.inl h)
      · exact (pp_step hZ (Or.inl h)).symm
      · exact pp_step hZ (Or.inr h)
      · exact (pp_step hZ (Or.inr h)).symm
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  let Pf : V → List V := fun u => if h : ∃ P, X.IsPathFrom v₀ u P then h.choose else []
  have hPf : ∀ u ∈ X.vertices, X.IsPathFrom v₀ u (Pf u) := by
    intro u hu
    have h : ∃ P, X.IsPathFrom v₀ u P := hconn v₀ hv₀ u hu
    simp only [Pf, dif_pos h]
    exact h.choose_spec
  refine ⟨fun u => pp φ (Pf u), fun u v huv => ?_⟩
  have hPu := hPf u (vert_of_face X huv.2 (by simp))
  have hPv := hPf v (vert_of_face X huv.2 (by simp))
  have hL : X.IsPathFrom v₀ v₀ (pcat (pcat (Pf u) [u, v]) (Pf v).reverse) := by
    refine path_pcat (path_pcat hPu ?_) (path_rev hPv)
    exact ⟨⟨by simp, by simp [vert_of_face X huv.2],
      List.IsChain.cons_cons huv (List.isChain_singleton _)⟩, rfl, rfl⟩
  have h1 := key _ _ (hX.2 v₀ hv₀ _ hL)
  have hrev := pp_rev hZ.1 _ hPv.1.2.2
  obtain ⟨Q, hQ⟩ := List.getLast?_eq_some_iff.1 hPu.2.2
  obtain ⟨R, hR⟩ := List.getLast?_eq_some_iff.1 hPv.2.2
  have e : pcat (pcat (Pf u) [u, v]) (Pf v).reverse = (Q ++ [u]) ++ v :: R.reverse := by
    simp [pcat, hQ, hR]
  have e' : (Pf v).reverse = v :: R.reverse := by simp [hR]
  rw [e, pp_split, ← e', hrev, List.append_assoc, List.singleton_append, pp_split, ← hQ] at h1
  simp only [pp, one_mul] at h1
  rw [inv_mul_eq_one] at h1
  simp only [d0, h1, mul_inv_cancel_right]

end Coh


end PolySwap.KMS.L317B
end
end Part_B_complex

section Part_C_link

open Classical Matrix Polynomial

namespace PolySwap.KMS.L317C

open PolySwap.KMS

variable {d : ℕ} {F : Type*} [Field F]

abbrev SLd (d : ℕ) (F : Type*) [Field F] := SpecialLinearGroup (Fin (d + 1)) F

/-- The off-diagonal support of `M` lies on pairs `(i, j)` with `i < j` and every colour of
`(i, j]` in `S`. -/
def Pat (S : Set ℕ) (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F) : Prop :=
  ∀ i j : Fin (d + 1), i ≠ j → M i j ≠ 0 → i < j ∧ ∀ c : ℕ, (i : ℕ) < c → c ≤ j → c ∈ S

/-- Unit diagonal. -/
def Diag1 (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F) : Prop := ∀ i, M i i = 1

lemma Pat.mono {S S' : Set ℕ} {M : Matrix (Fin (d + 1)) (Fin (d + 1)) F} (h : Pat S M)
    (hS : S ⊆ S') : Pat S' M := fun i j hij hne =>
  ⟨(h i j hij hne).1, fun c h1 h2 => hS ((h i j hij hne).2 c h1 h2)⟩

lemma Pat.lower {S : Set ℕ} {M : Matrix (Fin (d + 1)) (Fin (d + 1)) F} (h : Pat S M)
    {i j : Fin (d + 1)} (hij : j < i) : M i j = 0 := by
  by_contra hne
  exact absurd (h i j (ne_of_gt hij) hne).1 (not_lt.2 hij.le)

lemma pat_mul {S : Set ℕ} {M N : Matrix (Fin (d + 1)) (Fin (d + 1)) F}
    (hM : Pat S M) (hN : Pat S N) (dM : Diag1 M) (dN : Diag1 N) :
    Pat S (M * N) ∧ Diag1 (M * N) := by
  refine ⟨fun i j hij hne => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply] at hne
    obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have h1 : M i k ≠ 0 := left_ne_zero_of_mul hk
    have h2 : N k j ≠ 0 := right_ne_zero_of_mul hk
    by_cases hik : i = k
    · subst hik; exact hN i j hij h2
    by_cases hkj : k = j
    · subst hkj; exact hM i k hik h1
    obtain ⟨a1, a2⟩ := hM i k hik h1
    obtain ⟨b1, b2⟩ := hN k j hkj h2
    refine ⟨a1.trans b1, fun c hc1 hc2 => ?_⟩
    by_cases hc : c ≤ (k : ℕ)
    · exact a2 c hc1 hc
    · exact b2 c (by omega) hc2
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [dM i, dN i]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · simp [hM.lower h]
      · simp [hN.lower h]
    · simp

lemma pat_transvection {S : Set ℕ} (i j : Fin (d + 1)) (hij : i < j)
    (hS : ∀ c : ℕ, (i : ℕ) < c → c ≤ j → c ∈ S) (c : F) :
    Pat S (transvection i j c) ∧ Diag1 (transvection i j c) := by
  refine ⟨fun a b hab hne => ?_, fun a => ?_⟩
  · simp only [transvection, Matrix.add_apply, Matrix.one_apply, hab, if_false, zero_add,
      Matrix.single_apply] at hne
    split_ifs at hne with h
    · obtain ⟨rfl, rfl⟩ := h; exact ⟨hij, hS⟩
    · exact absurd rfl hne
  · simp [transvection, Matrix.single_apply]
    intro h1 h2; subst h1; subst h2; exact absurd hij (lt_irrefl _)

lemma ss0 {i j k l : Fin (d + 1)} (h : j ≠ k) (a b : F) :
    (Matrix.single i j a : Matrix (Fin (d + 1)) (Fin (d + 1)) F) * Matrix.single k l b = 0 :=
  by
    ext x y
    simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun z _ => ?_
    split_ifs with h1 h2 <;> first | (exfalso; exact h (h1.2.trans h2.1.symm)) | simp

lemma tv_mul (i j : Fin (d + 1)) (hij : i ≠ j) (a b : F) :
    (transvection i j a : Matrix (Fin (d + 1)) (Fin (d + 1)) F) * transvection i j b =
      transvection i j (a + b) := by
  simp only [transvection, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    ss0 (Ne.symm hij), add_zero, Matrix.single_add]
  abel

/-- Elements of `UL S` are unitriangular with support in `S`-runs. -/
lemma pat_of_mem_UL {S : Finset ℕ} {g : SLd d F} (hg : g ∈ UL d F S) :
    Pat (S : Set ℕ) (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) ∧
      Diag1 (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) := by
  induction hg using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨lam, i, j, hjS, -, hij, hx⟩ := hx
    rw [hx]
    exact pat_transvection i j (Fin.lt_def.2 (by omega))
      (fun c h1 h2 => by have : c = j := by omega
                         subst this; exact hjS) lam
  | inv_mem x hx =>
    obtain ⟨lam, i, j, hjS, -, hij, hx⟩ := hx
    have hne : i ≠ j := fun h => by subst h; omega
    have : ((x⁻¹ : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) = transvection i j (-lam) := by
      have h1 : (x : Matrix (Fin (d + 1)) (Fin (d + 1)) F) * transvection i j (-lam) = 1 := by
        rw [hx, tv_mul i j hne]; simp [transvection]
      have : x⁻¹ = (⟨transvection i j (-lam), det_transvection_of_ne _ _ hne _⟩ : SLd d F) := by
        exact inv_eq_of_mul_eq_one_right (Subtype.ext h1)
      rw [this]
    rw [this]
    exact pat_transvection i j (Fin.lt_def.2 (by omega))
      (fun c h1 h2 => by have : c = j := by omega
                         subst this; exact hjS) _
  | one => exact ⟨fun i j hij hne => absurd (by simp [hij]) hne, fun i => by simp⟩
  | mul x y _ _ hx hy =>
    have e : ((x * y : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) =
        (x : Matrix (Fin (d + 1)) (Fin (d + 1)) F) * y := rfl
    rw [e]
    exact pat_mul hx.1 hy.1 hx.2 hy.2

lemma comm_identity {A : Type*} [Ring A] (E F : A) (hEE : E * E = 0) (hFF : F * F = 0)
    (hFE : F * E = 0) : (1 + E) * (1 + F) * (1 + -E) * (1 + -F) = 1 + E * F := by
  have h1 : E * F * E = 0 := by rw [mul_assoc, hFE, mul_zero]
  have h2 : E * F * F = 0 := by rw [mul_assoc, hFF, mul_zero]
  simp only [add_mul, mul_add, one_mul, mul_one, mul_neg, neg_mul, hEE, hFF, hFE, h1, h2,
    add_zero]
  abel

/-- `t_{ij}(c) ∈ UL S` when `i < j` and every colour of `(i, j]` is in `S`. -/
lemma transvection_mem_UL {S : Finset ℕ} :
    ∀ (k : ℕ) (i j : Fin (d + 1)) (c : F), (j : ℕ) = i + k + 1 →
      (∀ c' : ℕ, (i : ℕ) < c' → c' ≤ j → c' ∈ S) →
      ∀ g : SLd d F, (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) = transvection i j c →
        g ∈ UL d F S := by
  intro k
  induction k with
  | zero =>
    intro i j c hj hS g hg
    exact Subgroup.subset_closure ⟨c, i, j, hS j (by omega) le_rfl, by omega, by omega, hg⟩
  | succ k ih =>
    intro i j c hj hS g hg
    let m : Fin (d + 1) := ⟨i + k + 1, by omega⟩
    have him : i ≠ m := fun h => by
      have := congrArg Fin.val h; simp only [m] at this; omega
    have hmj : m ≠ j := fun h => by
      have := congrArg Fin.val h; simp only [m] at this; omega
    have hij : i ≠ j := fun h => by subst h; omega
    let e1 : SLd d F := ⟨transvection i m c, det_transvection_of_ne _ _ him _⟩
    let e2 : SLd d F := ⟨transvection m j 1, det_transvection_of_ne _ _ hmj _⟩
    let e3 : SLd d F := ⟨transvection i m (-c), det_transvection_of_ne _ _ him _⟩
    let e4 : SLd d F := ⟨transvection m j (-1), det_transvection_of_ne _ _ hmj _⟩
    have h1 : e1 ∈ UL d F S := ih i m c (by simp [m]) (fun c' h1 h2 => hS c' h1 (by
      simp [m] at h2; omega)) e1 rfl
    have h3 : e3 ∈ UL d F S := ih i m (-c) (by simp [m]) (fun c' h1 h2 => hS c' h1 (by
      simp [m] at h2; omega)) e3 rfl
    have h2 : e2 ∈ UL d F S := Subgroup.subset_closure
      ⟨1, m, j, hS j (by omega) le_rfl, by omega, by simp only [m]; omega, rfl⟩
    have h4 : e4 ∈ UL d F S := Subgroup.subset_closure
      ⟨-1, m, j, hS j (by omega) le_rfl, by omega, by simp only [m]; omega, rfl⟩
    have hprod : g = e1 * e2 * e3 * e4 := by
      apply Subtype.ext
      show (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) = transvection i m c * transvection m j 1 *
        transvection i m (-c) * transvection m j (-1)
      rw [hg]
      simp only [transvection]
      have hn1 : Matrix.single i m (-c) = -Matrix.single i m c := by
        ext a b; simp only [Matrix.single_apply, Matrix.neg_apply]; split_ifs <;> simp
      have hn2 : Matrix.single m j (-1 : F) = -Matrix.single m j 1 := by
        ext a b; simp only [Matrix.single_apply, Matrix.neg_apply]; split_ifs <;> simp
      rw [hn1, hn2, comm_identity _ _ (ss0 (Ne.symm him) _ _) (ss0 (Ne.symm hmj) _ _)
        (ss0 (Ne.symm hij) _ _), single_mul_single_same, mul_one]
    rw [hprod]
    exact mul_mem (mul_mem (mul_mem h1 h2) h3) h4

lemma det_of_pat {S : Set ℕ} {M : Matrix (Fin (d + 1)) (Fin (d + 1)) F} (h : Pat S M)
    (hd : Diag1 M) : M.det = 1 := by
  have hU : M.IsUpperTriangular := fun i j hij => h.lower hij
  rw [Matrix.det_of_isUpperTriangular hU]
  exact Finset.prod_eq_one fun i _ => hd i

/-- The `SL` element of a unitriangular matrix. -/
noncomputable def mkSL (S : Set ℕ) (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F) (h : Pat S M)
    (hd : Diag1 M) : SLd d F := ⟨M, det_of_pat h hd⟩

@[simp] lemma coe_mkSL (S : Set ℕ) (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F) (h : Pat S M)
    (hd : Diag1 M) : ((mkSL S M h hd : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) = M := rfl

/-- A unitriangular `SL` element with support in `S`-runs lies in `UL S`. -/
theorem mem_UL_of_pat {S : Finset ℕ} :
    ∀ g : SLd d F, Pat (S : Set ℕ) (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) →
      Diag1 (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) → g ∈ UL d F S := by
  intro g
  generalize hN : (Finset.univ.filter (fun p : Fin (d + 1) × Fin (d + 1) =>
    p.1 ≠ p.2 ∧ (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) p.1 p.2 ≠ 0)).card = N
  induction N using Nat.strong_induction_on generalizing g with
  | _ N ih =>
    intro hg hdg
    set Mg := (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) with hMg
    set Sx := Finset.univ.filter
      (fun p : Fin (d + 1) × Fin (d + 1) => p.1 ≠ p.2 ∧ Mg p.1 p.2 ≠ 0) with hSx
    by_cases hne : Sx.Nonempty
    · obtain ⟨⟨a, b⟩, hp, hmin⟩ := Sx.exists_min_image (fun p => p.2) hne
      simp only [hSx, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨hab, hrun⟩ := hg a b hp.1 hp.2
      set c := Mg a b with hc
      have hcol : ∀ i, i ≠ a → Mg i a = 0 := by
        intro i hi
        by_contra h
        have := hmin (i, a) (by simp [hSx, hi, h])
        exact absurd hab (not_lt.2 this)
      have hab' : a ≠ b := ne_of_lt hab
      let t : SLd d F := ⟨transvection a b (-c), det_transvection_of_ne _ _ hab' _⟩
      let ti : SLd d F := ⟨transvection a b c, det_transvection_of_ne _ _ hab' _⟩
      have hti : ti ∈ UL d F S := transvection_mem_UL ((b : ℕ) - a - 1) a b c (by omega)
        (fun c' h1 h2 => hrun c' h1 h2) ti rfl
      have hgt_mat : ∀ i j, ((g * t : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) i j =
          if i = a ∧ j = b then 0 else Mg i j := by
        intro i j
        show (Mg * transvection a b (-c)) i j = _
        rw [transvection, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply]
        simp only [Matrix.single_apply, mul_ite, mul_zero]
        rw [Finset.sum_eq_single a]
        · by_cases hj : j = b
          · subst hj
            by_cases hi : i = a
            · subst hi; simp [hdg i, hc]
            · simp [hcol i hi, hi]
          · simp [Ne.symm hj, hj]
        · intro k _ hk; simp [Ne.symm hk]
        · simp
      have htti : t * ti = 1 := by
        apply Subtype.ext
        show transvection a b (-c) * transvection a b c = 1
        rw [tv_mul a b hab']; simp [transvection]
      have hg_eq : g = (g * t) * ti := by rw [mul_assoc, htti, mul_one]
      rw [hg_eq]
      refine mul_mem ?_ hti
      have hS' : Finset.univ.filter (fun p : Fin (d + 1) × Fin (d + 1) => p.1 ≠ p.2 ∧
          ((g * t : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) p.1 p.2 ≠ 0) =
          Sx.erase (a, b) := by
        ext ⟨i, j⟩
        simp only [hgt_mat i j, hSx, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_erase, ne_eq, Prod.mk.injEq]
        by_cases h : i = a ∧ j = b
        · simp [h]
        · simp [h]
      refine ih _ ?_ (g * t) rfl ?_ ?_
      · rw [hS', ← hN]
        exact Finset.card_erase_lt_of_mem (by simpa [hSx, hp.1] using hp.2)
      · intro i j hij hne'
        rw [hgt_mat] at hne'
        split_ifs at hne' with h
        · exact absurd rfl hne'
        · exact hg i j hij hne'
      · intro i
        rw [hgt_mat]
        split_ifs with h
        · exact absurd (h.1.symm.trans h.2) hab'
        · exact hdg i
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      have : g = 1 := by
        apply Subtype.ext
        ext i j
        show Mg i j = (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) F) i j
        rw [Matrix.one_apply]
        by_cases hij : i = j
        · subst hij; simp [hdg i]
        · simp only [hij, if_false]
          by_contra h
          have : (i, j) ∈ Sx := by simp [hSx, hij, h]
          rw [hne] at this
          simp at this
      rw [this]; exact one_mem _


/-! ## Cyclic arithmetic -/

lemma val_sub' (i b : Fin (d + 1)) :
    ((i - b : Fin (d + 1)) : ℕ) = if (b : ℕ) ≤ i then (i : ℕ) - b else i + (d + 1) - b := by
  rw [Fin.val_sub]
  have hi := i.isLt; have hb := b.isLt
  split_ifs with h
  · rw [show d + 1 - b + i = (i - b) + (d + 1) by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

lemma relabel_eq {b c : ℕ} (hb : b < d + 1) (hc : c < d + 1) :
    relabel d b c = if b ≤ c then c - b else c + (d + 1) - b := by
  unfold relabel
  split_ifs with h
  · rw [show c + (d + 1) - b = (c - b) + (d + 1) by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

lemma relabel_self {b : ℕ} (hb : b < d + 1) : relabel d b b = 0 := by
  rw [relabel_eq hb hb]; simp

/-- Colour `c` lies on the cyclic path of coordinates from `i` to `j` (colours `i+1, …, j`). -/
def inCyc (i j c : ℕ) : Prop := (i < j ∧ i < c ∧ c ≤ j) ∨ (j < i ∧ (i < c ∨ c ≤ j))

lemma K1 {i j b : Fin (d + 1)} (hij : i ≠ j) (h : ¬ inCyc i j b) :
    ((i - b : Fin (d + 1)) : ℕ) < ((j - b : Fin (d + 1)) : ℕ) := by
  have := Fin.val_ne_of_ne hij
  rw [val_sub', val_sub']
  have := i.isLt; have := j.isLt; have := b.isLt
  unfold inCyc at h
  split_ifs <;> omega

lemma K2 {i j b : Fin (d + 1)} (h : ((i - b : Fin (d + 1)) : ℕ) < ((j - b : Fin (d + 1)) : ℕ))
    {c : ℕ} (hc : c < d + 1) :
    inCyc i j c ↔ ((i - b : Fin (d + 1)) : ℕ) < relabel d b c ∧
      relabel d b c ≤ ((j - b : Fin (d + 1)) : ℕ) := by
  rw [val_sub', val_sub'] at *
  rw [relabel_eq b.isLt hc]
  have := i.isLt; have := j.isLt; have := b.isLt
  unfold inCyc
  split_ifs at * <;> omega

lemma K2' {i j b : Fin (d + 1)} (h : ((i - b : Fin (d + 1)) : ℕ) < ((j - b : Fin (d + 1)) : ℕ)) :
    (j : ℕ) < i ↔ (b : ℕ) ≤ i ∧ ¬ (b : ℕ) ≤ j := by
  rw [val_sub', val_sub'] at h
  have := i.isLt; have := j.isLt; have := b.isLt
  split_ifs at h <;> omega

/-! ## The embedding `Φ_b` of the upper-triangular model -/

section Phi

variable {f : F[X]} [Fact (Irreducible f)]

variable (f) in
/-- `s_i = t^{[b ≤ i]}`. -/
noncomputable def sc (b i : Fin (d + 1)) : AdjoinRoot f :=
  if (b : ℕ) ≤ i then AdjoinRoot.root f else 1

lemma sc_ne (ht : AdjoinRoot.root f ≠ 0) (b i : Fin (d + 1)) : sc f b i ≠ 0 := by
  unfold sc; split_ifs; exacts [ht, one_ne_zero]

variable (f) in
/-- `Φ_b(M)_{ij} = s_i M_{i-b, j-b} s_j⁻¹`: the model coordinate `a` sits at `a + b`. -/
noncomputable def Φm (b : Fin (d + 1)) (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) (AdjoinRoot f) :=
  fun i j => sc f b i * algebraMap F (AdjoinRoot f) (M (i - b) (j - b)) * (sc f b j)⁻¹

lemma Φm_mul (ht : AdjoinRoot.root f ≠ 0) (b : Fin (d + 1))
    (M N : Matrix (Fin (d + 1)) (Fin (d + 1)) F) : Φm f b (M * N) = Φm f b M * Φm f b N := by
  ext i j
  simp only [Φm, Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  refine (Fintype.sum_equiv (Equiv.subRight b) _ _ (fun k => ?_)).symm
  simp only [Equiv.subRight_apply]
  have := inv_mul_cancel₀ (sc_ne ht b k)
  linear_combination (sc f b i * algebraMap F (AdjoinRoot f) (M (i - b) (k - b)) *
    algebraMap F (AdjoinRoot f) (N (k - b) (j - b)) * (sc f b j)⁻¹) * this

lemma Φm_one (ht : AdjoinRoot.root f ≠ 0) (b : Fin (d + 1)) :
    Φm f b (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) F) = 1 := by
  ext i j
  simp only [Φm, Matrix.one_apply, sub_left_inj]
  split_ifs with h
  · subst h; simp [mul_inv_cancel₀ (sc_ne ht b i)]
  · simp

lemma Φm_det (ht : AdjoinRoot.root f ≠ 0) (b : Fin (d + 1))
    (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F) :
    (Φm f b M).det = algebraMap F (AdjoinRoot f) M.det := by
  have e : Φm f b M = diagonal (sc f b) * ((M.map (algebraMap F (AdjoinRoot f))).submatrix
      (Equiv.subRight b) (Equiv.subRight b)) * diagonal (fun j => (sc f b j)⁻¹) := by
    ext i j; simp [Φm, diagonal_mul, mul_diagonal]
  rw [e, det_mul, det_mul, det_diagonal, det_diagonal, det_submatrix_equiv_self,
    RingHom.map_det, Finset.prod_inv_distrib]
  have : ∏ i, sc f b i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => sc_ne ht b i
  rw [RingHom.mapMatrix_apply]
  field_simp

/-- `Φ_b : SL_{d+1}(F) → SL_{d+1}(F[t]/(f))` (a homomorphism, injective). -/
noncomputable def Φ (ht : AdjoinRoot.root f ≠ 0) (b : Fin (d + 1)) :
    SLd d F →* SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) where
  toFun M := ⟨Φm f b M, by rw [Φm_det ht, M.2, map_one]⟩
  map_one' := Subtype.ext (Φm_one ht b)
  map_mul' M N := Subtype.ext (Φm_mul ht b M N)

lemma coe_Φ (ht : AdjoinRoot.root f ≠ 0) (b : Fin (d + 1)) (M : SLd d F) :
    ((Φ ht b M : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)) :
      Matrix (Fin (d + 1)) (Fin (d + 1)) (AdjoinRoot f)) = Φm f b M := rfl

lemma alg_inj : Function.Injective (algebraMap F (AdjoinRoot f)) := (algebraMap F _).injective

lemma Φ_inj (ht : AdjoinRoot.root f ≠ 0) (b : Fin (d + 1)) : Function.Injective (Φ ht b) := by
  intro M N h
  have h' := congrArg (fun P : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) =>
    (P : Matrix (Fin (d + 1)) (Fin (d + 1)) (AdjoinRoot f))) h
  simp only [coe_Φ] at h'
  apply Subtype.ext; ext a a'
  have := congrFun (congrFun h' (a + b)) (a' + b)
  simp only [Φm, add_sub_cancel_right] at this
  have h1 := sc_ne ht b (a + b); have h2 := inv_ne_zero (sc_ne ht b (a' + b))
  rw [mul_assoc, mul_assoc] at this
  exact alg_inj (mul_right_cancel₀ h2 (mul_left_cancel₀ h1 this))

lemma K3 (ht : AdjoinRoot.root f ≠ 0) {i j b : Fin (d + 1)}
    (h : ((i - b : Fin (d + 1)) : ℕ) < ((j - b : Fin (d + 1)) : ℕ)) (x : AdjoinRoot f) :
    sc f b i * x * (sc f b j)⁻¹ = x * (if (j : ℕ) < i then AdjoinRoot.root f else 1) := by
  rw [val_sub', val_sub'] at h
  have := i.isLt; have := j.isLt
  unfold sc
  by_cases h1 : (b : ℕ) ≤ i <;> by_cases h2 : (b : ℕ) ≤ j <;> by_cases h3 : (j : ℕ) < i <;>
    simp only [h1, h2, h3, if_true, if_false] at h ⊢
  all_goals first | (exfalso; omega) | (simp; done) | (field_simp; done) | (simp; ring)

variable (f) in
/-- Entry pattern in original coordinates for `⋂_{c ∈ C} H^f_c`. -/
def OPat (C : Finset ℕ) (N : Matrix (Fin (d + 1)) (Fin (d + 1)) (AdjoinRoot f)) :
    Prop :=
  (∀ i, N i i = 1) ∧ ∀ i j : Fin (d + 1), i ≠ j →
    (∃ l : F, N i j = algebraMap F (AdjoinRoot f) l *
      (if (j : ℕ) < i then AdjoinRoot.root f else 1)) ∧
    (N i j ≠ 0 → ∀ c ∈ C, ¬ inCyc i j c)

lemma OPat.mono {C C' : Finset ℕ} {N : Matrix (Fin (d + 1)) (Fin (d + 1)) (AdjoinRoot f)}
    (h : OPat f C N) (hC : C' ⊆ C) : OPat f C' N :=
  ⟨h.1, fun i j hij => ⟨(h.2 i j hij).1, fun hn c hc => (h.2 i j hij).2 hn c (hC hc)⟩⟩

lemma opat_of_pat (ht : AdjoinRoot.root f ≠ 0) (b : Fin (d + 1)) {S : Set ℕ}
    {M : Matrix (Fin (d + 1)) (Fin (d + 1)) F} (hP : Pat S M) (hD : Diag1 M) {C : Finset ℕ}
    (hCr : ∀ c ∈ C, c < d + 1) (hCS : ∀ c ∈ C, relabel d b c ∉ S) : OPat f C (Φm f b M) := by
  refine ⟨fun i => by simp [Φm, hD (i - b), mul_inv_cancel₀ (sc_ne ht b i)], fun i j hij => ?_⟩
  have hab : i - b ≠ j - b := fun h => hij (sub_left_inj.1 h)
  by_cases hm : M (i - b) (j - b) = 0
  · exact ⟨⟨0, by simp [Φm, hm]⟩, fun h => absurd (by simp [Φm, hm]) h⟩
  obtain ⟨hlt, hS⟩ := hP _ _ hab hm
  have hlt' : ((i - b : Fin (d + 1)) : ℕ) < ((j - b : Fin (d + 1)) : ℕ) := hlt
  refine ⟨⟨_, K3 ht hlt' _⟩, fun _ c hc hcyc => ?_⟩
  have := (K2 hlt' (hCr c hc)).1 hcyc
  exact hCS c hc (hS _ this.1 this.2)

lemma pat_of_opat (ht : AdjoinRoot.root f ≠ 0) (b : Fin (d + 1))
    {M : Matrix (Fin (d + 1)) (Fin (d + 1)) F} {C : Finset ℕ} (hN : OPat f C (Φm f b M))
    (hb : (b : ℕ) ∈ C) (hCr : ∀ c ∈ C, c < d + 1) :
    Pat ((Finset.range (d + 1) \ C.image (relabel d b) : Finset ℕ) : Set ℕ) M ∧ Diag1 M := by
  constructor
  · intro a a' haa hm
    have hij : a + b ≠ a' + b := fun h => haa (add_right_cancel h)
    have hne : Φm f b M (a + b) (a' + b) ≠ 0 := by
      simp only [Φm, add_sub_cancel_right]
      exact mul_ne_zero (mul_ne_zero (sc_ne ht b _) ((_root_.map_ne_zero _).2 hm))
        (inv_ne_zero (sc_ne ht b _))
    have hc := (hN.2 _ _ hij).2 hne
    have hlt := K1 hij (hc _ hb)
    simp only [add_sub_cancel_right] at hlt
    refine ⟨hlt, fun m h1 h2 => ?_⟩
    simp only [Finset.coe_sdiff, Finset.coe_range, Finset.coe_image, Set.mem_sdiff, Set.mem_Iio,
      Set.mem_image, Finset.mem_coe, not_exists, not_and]
    refine ⟨by have := a'.isLt; omega, fun c hcC hcm => hc c hcC ?_⟩
    have hlt' := K1 hij (hc _ hb)
    rw [K2 hlt' (hCr c hcC), hcm]
    simpa only [add_sub_cancel_right] using And.intro h1 h2
  · intro a
    have := hN.1 (a + b)
    simp only [Φm, add_sub_cancel_right] at this
    have h1 := sc_ne ht b (a + b)
    rw [mul_assoc, mul_comm _ (sc f b (a + b))⁻¹, ← mul_assoc, mul_inv_cancel₀ h1, one_mul] at this
    exact alg_inj (by rw [this, map_one])

lemma exists_of_opat (ht : AdjoinRoot.root f ≠ 0) (b : Fin (d + 1))
    {N : Matrix (Fin (d + 1)) (Fin (d + 1)) (AdjoinRoot f)} {C : Finset ℕ} (hN : OPat f C N)
    (hb : (b : ℕ) ∈ C) : ∃ M, Φm f b M = N := by
  have hch : ∀ i j : Fin (d + 1), ∃ l : F, i ≠ j → N i j = algebraMap F (AdjoinRoot f) l *
      (if (j : ℕ) < i then AdjoinRoot.root f else 1) := by
    intro i j
    by_cases h : i = j
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨l, hl⟩ := (hN.2 i j h).1; exact ⟨l, fun _ => hl⟩
  choose L hL using hch
  refine ⟨fun a a' => if a = a' then 1 else L (a + b) (a' + b), ?_⟩
  ext i j
  simp only [Φm, sub_add_cancel, sub_left_inj]
  split_ifs with h
  · subst h; rw [hN.1 i, map_one, mul_one, mul_inv_cancel₀ (sc_ne ht b i)]
  · have hs := hL i j h
    by_cases h0 : N i j = 0
    · have hs' : algebraMap F (AdjoinRoot f) (L i j) *
          (if (j : ℕ) < i then AdjoinRoot.root f else 1) = 0 := by rw [← hs]; exact h0
      have : algebraMap F (AdjoinRoot f) (L i j) = 0 := by
        rcases mul_eq_zero.1 hs' with h' | h'
        · exact h'
        · exact absurd h' (by split_ifs <;> simp [ht])
      rw [this, h0]; simp
    · rw [K3 ht (K1 h ((hN.2 i j h).2 h0 _ hb))]; exact hs.symm

lemma sl_of_opat (ht : AdjoinRoot.root f ≠ 0) (b : Fin (d + 1))
    (N : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)) {C : Finset ℕ}
    (hN : OPat f C (N : Matrix (Fin (d + 1)) (Fin (d + 1)) (AdjoinRoot f)))
    (hb : (b : ℕ) ∈ C) (hCr : ∀ c ∈ C, c < d + 1) :
    ∃ y : SLd d F, y ∈ UL d F (Finset.range (d + 1) \ C.image (relabel d b)) ∧ Φ ht b y = N := by
  obtain ⟨M, hM⟩ := exists_of_opat ht b hN hb
  rw [← hM] at hN
  obtain ⟨hP, hD⟩ := pat_of_opat ht b hN hb hCr
  refine ⟨mkSL _ M hP hD, mem_UL_of_pat _ hP hD, Subtype.ext ?_⟩
  rw [coe_Φ, coe_mkSL, hM]

end Phi

/-! ## `H^f_c` and its intersections as entry patterns -/

section Hf

variable {f : F[X]} [Fact (Irreducible f)]

lemma tv_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (i j : Fin (d + 1)) (c : R) :
    (transvection i j c).map φ = transvection i j (φ c) := by
  ext a b'
  simp only [transvection, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  split_ifs <;> simp

lemma Φm_tv (ht : AdjoinRoot.root f ≠ 0) (b : Fin (d + 1)) {a a' : Fin (d + 1)}
    (ha : (a : ℕ) + 1 = a') (l : F) :
    Φm f b (transvection a a' l) = transvection (a + b) (a' + b)
      (algebraMap F (AdjoinRoot f) l *
        (if ((a' + b : Fin (d + 1)) : ℕ) < (a + b : Fin (d + 1)) then AdjoinRoot.root f else 1)) := by
  have haa : a ≠ a' := fun h => by subst h; omega
  have hlt : ((a + b - b : Fin (d + 1)) : ℕ) < ((a' + b - b : Fin (d + 1)) : ℕ) := by
    simp only [add_sub_cancel_right]; omega
  have e := K3 ht hlt (algebraMap F (AdjoinRoot f) l)
  have key : ∀ x y : Fin (d + 1), (x = y - b) ↔ (y = x + b) := fun x y =>
    ⟨fun h => by rw [h, sub_add_cancel], fun h => by rw [h, add_sub_cancel_right]⟩
  ext i j
  simp only [Φm, transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
    sub_left_inj]
  simp only [key]
  by_cases hi : i = a + b <;> by_cases hj : j = a' + b
  · subst hi hj
    have : a + b ≠ a' + b := fun h => haa (add_right_cancel h)
    simp only [this, if_false, and_self, if_true, zero_add]; exact e
  all_goals
    have hn : ¬ (a + b = i ∧ a' + b = j) := fun h => by rcases h with ⟨rfl, rfl⟩; tauto
    have hn2 : ¬ (i = a + b ∧ j = a' + b) := fun h => by rcases h with ⟨rfl, rfl⟩; tauto
    simp only [hn, hn2, if_false, add_zero]
    by_cases hij : i = j
    · subst hij; simp only [if_true, map_one, mul_one, add_zero]
      exact mul_inv_cancel₀ (sc_ne ht b i)
    · simp only [hij, if_false, map_zero, mul_zero, zero_mul, add_zero]

omit [Fact (Irreducible f)] in
/-- A transvection as an element of `SL`. -/
def tvSL {R : Type*} [CommRing R] (i j : Fin (d + 1)) (c : R) (h : i ≠ j) :
    SpecialLinearGroup (Fin (d + 1)) R := ⟨transvection i j c, det_transvection_of_ne _ _ h _⟩

omit [Fact (Irreducible f)] in
lemma mk_tv (i j : Fin (d + 1)) (p : F[X]) (g : SpecialLinearGroup (Fin (d + 1)) F[X])
    (hg : (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F[X]) = transvection i j p) :
    ((SpecialLinearGroup.map (AdjoinRoot.mk f) g : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)) :
        Matrix (Fin (d + 1)) (Fin (d + 1)) (AdjoinRoot f)) =
      transvection i j (AdjoinRoot.mk f p) := by
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, hg]
  exact tv_map _ i j p

lemma Hf_eq (ht : AdjoinRoot.root f ≠ 0) (b : Fin (d + 1)) :
    Hf d F f b = (UL d F (Finset.range (d + 1) \ {0})).map (Φ ht b) := by
  have hb := b.isLt
  unfold Hf Hcol U UL
  rw [MonoidHom.map_closure, MonoidHom.map_closure]
  apply le_antisymm <;> rw [Subgroup.closure_le]
  · rintro _ ⟨g, hg, rfl⟩
    simp only [Set.mem_iUnion] at hg
    obtain ⟨c, hc, l, i, j, hgen⟩ := hg
    rw [Finset.mem_erase, Finset.mem_range] at hc
    apply Subgroup.subset_closure
    have hi := i.isLt; have hj := j.isLt
    rcases hgen with ⟨h1, h2, hic, hjc, hg⟩ | ⟨h0, hic, hjc, hg⟩
    · have hab : (((i - b : Fin (d + 1)) : ℕ)) + 1 = ((j - b : Fin (d + 1)) : ℕ) := by
        rw [val_sub', val_sub']; split_ifs <;> omega
      have hne : i - b ≠ j - b := fun h => by rw [h] at hab; omega
      refine ⟨⟨transvection (i - b) (j - b) l, det_transvection_of_ne _ _ hne _⟩,
        ⟨l, i - b, j - b, ?_, ?_, hab, rfl⟩, ?_⟩
      · simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton]
        constructor
        · exact (j - b).isLt
        · rw [val_sub']; split_ifs <;> omega
      · omega
      · have hij : i ≠ j := fun h => by rw [h] at hic; omega
        apply Subtype.ext
        rw [mk_tv i j _ g hg]
        change Φm f b (transvection (i - b) (j - b) l) = _
        rw [Φm_tv ht b hab, sub_add_cancel, sub_add_cancel, AdjoinRoot.mk_C,
          AdjoinRoot.algebraMap_eq, if_neg (by omega), mul_one]
    · have hab : (((i - b : Fin (d + 1)) : ℕ)) + 1 = ((j - b : Fin (d + 1)) : ℕ) := by
        rw [val_sub', val_sub']; split_ifs <;> omega
      have hne : i - b ≠ j - b := fun h => by rw [h] at hab; omega
      refine ⟨⟨transvection (i - b) (j - b) l, det_transvection_of_ne _ _ hne _⟩,
        ⟨l, i - b, j - b, ?_, ?_, hab, rfl⟩, ?_⟩
      · simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton]
        constructor
        · exact (j - b).isLt
        · rw [val_sub']; split_ifs <;> omega
      · omega
      · have hij : i ≠ j := fun h => by rw [h] at hic; omega
        apply Subtype.ext
        rw [mk_tv i j _ g hg]
        change Φm f b (transvection (i - b) (j - b) l) = _
        rw [Φm_tv ht b hab, sub_add_cancel, sub_add_cancel, map_mul, AdjoinRoot.mk_C,
          AdjoinRoot.mk_X, AdjoinRoot.algebraMap_eq, if_pos (by omega)]
  · rintro _ ⟨y, ⟨l, a, a', ha'S, h1, ha, hy⟩, rfl⟩
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at ha'S
    apply Subgroup.subset_closure
    have hav := a.isLt; have ha'v := a'.isLt
    have hi := Fin.val_add_eq_ite a b; have hj := Fin.val_add_eq_ite a' b
    have hij : a + b ≠ a' + b := fun h => by
      have := congrArg Fin.val h; rw [hi, hj] at this; split_ifs at this <;> omega
    have hΦ : (((Φ ht b) y : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)) :
        Matrix (Fin (d + 1)) (Fin (d + 1)) (AdjoinRoot f)) = transvection (a + b) (a' + b)
          (algebraMap F (AdjoinRoot f) l * (if ((a' + b : Fin (d + 1)) : ℕ) <
            (a + b : Fin (d + 1)) then AdjoinRoot.root f else 1)) := by
      rw [coe_Φ, hy, Φm_tv ht b ha]
    have hablt := (a + b).isLt; have ha'blt := (a' + b).isLt
    by_cases hw : ((a' + b : Fin (d + 1)) : ℕ) = 0
    · have hw' : (a' : ℕ) + b = d + 1 := by rw [hj] at hw; split_ifs at hw <;> omega
      refine ⟨tvSL (a + b) (a' + b) (C l * X) hij, ?_, ?_⟩
      · refine Set.mem_iUnion₂.2 ⟨0, ?_, l, a + b, a' + b, Or.inr ⟨rfl, ?_, hw, rfl⟩⟩
        · rw [Finset.mem_erase, Finset.mem_range]; constructor
          · intro h; rw [hj] at hw; split_ifs at hw <;> omega
          · omega
        · rw [hi]; rw [hj] at hw; split_ifs at hw ⊢ <;> omega
      · apply Subtype.ext
        rw [mk_tv _ _ _ _ rfl, hΦ, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X, AdjoinRoot.algebraMap_eq,
          if_pos (by rw [hw, hi]; split_ifs <;> omega)]
    · refine ⟨tvSL (a + b) (a' + b) (C l) hij, ?_, ?_⟩
      · refine Set.mem_iUnion₂.2 ⟨((a' + b : Fin (d + 1)) : ℕ), ?_, l, a + b, a' + b,
          Or.inl ⟨by omega, by omega, ?_, rfl, rfl⟩⟩
        · rw [Finset.mem_erase, Finset.mem_range]; refine ⟨?_, (a' + b).isLt⟩
          rw [hj]; split_ifs <;> omega
        · rw [hi]; rw [hj] at hw ⊢; split_ifs at hw ⊢ <;> omega
      · apply Subtype.ext
        rw [mk_tv _ _ _ _ rfl, hΦ, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq,
          if_neg (by rw [hi, hj]; rw [hj] at hw; split_ifs at hw ⊢ <;> omega), mul_one]

lemma Hf_char (ht : AdjoinRoot.root f ≠ 0) {c : ℕ} (hc : c < d + 1)
    (N : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)) :
    N ∈ Hf d F f c ↔ OPat f {c} (N : Matrix (Fin (d + 1)) (Fin (d + 1)) (AdjoinRoot f)) := by
  have e := Hf_eq ht (⟨c, hc⟩ : Fin (d + 1))
  simp only [Fin.val_mk] at e
  rw [e]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hP, hD⟩ := pat_of_mem_UL hy
    exact opat_of_pat ht _ hP hD (by simpa using hc) (by simp [relabel_self hc])
  · intro h
    obtain ⟨y, hy, rfl⟩ := sl_of_opat ht ⟨c, hc⟩ N h (by simp) (by simpa using hc)
    refine ⟨y, ?_, rfl⟩
    simpa [relabel_self hc] using hy

/-- `⋂_{c ∈ C} H^f_c = Φ_b(U_{[d] \ relabel_b(C)})` for `b ∈ C`. -/
lemma MG (ht : AdjoinRoot.root f ≠ 0) (b : Fin (d + 1)) {C : Finset ℕ} (hb : (b : ℕ) ∈ C)
    (hCr : ∀ c ∈ C, c < d + 1) (N : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)) :
    (∀ c ∈ C, N ∈ Hf d F f c) ↔
      ∃ y ∈ UL d F (Finset.range (d + 1) \ C.image (relabel d b)), Φ ht b y = N := by
  constructor
  · intro h
    have h0 := (Hf_char ht (hCr _ hb) N).1 (h _ hb)
    have hO : OPat f C (N : Matrix (Fin (d + 1)) (Fin (d + 1)) (AdjoinRoot f)) :=
      ⟨h0.1, fun i j hij => ⟨(h0.2 i j hij).1, fun hn c hc =>
        (((Hf_char ht (hCr c hc) N).1 (h c hc)).2 i j hij).2 hn c (Finset.mem_singleton_self c)⟩⟩
    exact sl_of_opat ht b N hO hb hCr
  · rintro ⟨y, hy, rfl⟩ c hc
    obtain ⟨hP, hD⟩ := pat_of_mem_UL hy
    have hO := opat_of_pat (f := f) ht b hP hD hCr (fun c hc h => by
      simp only [Finset.coe_sdiff, Finset.coe_range, Finset.coe_image, Set.mem_sdiff,
        Set.mem_image, Finset.mem_coe, not_exists, not_and] at h
      exact h.2 c hc rfl)
    exact (Hf_char ht (hCr c hc) _).2 (hO.mono (by simpa using hc))

end Hf

/-! ## Transfer of trivial `H¹` along a vertex bijection respecting faces -/

section Transfer

variable {V₁ V₂ : Type*} (X₁ : WComplex V₁) (X₂ : WComplex V₂) (Ψ : V₂ → V₁)

lemma face_image (h1 : ∀ τ ∈ X₂.tops, ∃ τ₁ ∈ X₁.tops, τ.image Ψ ⊆ τ₁) {s : Finset V₂}
    (hs : X₂.IsFace s) : X₁.IsFace (s.image Ψ) := by
  obtain ⟨τ, hτ, hsτ⟩ := hs
  obtain ⟨τ₁, h1', h2'⟩ := h1 τ hτ
  exact ⟨τ₁, h1', (Finset.image_subset_image hsτ).trans h2'⟩

/-- If `Ψ : V₂ → V₁` is injective, maps maximal faces of `X₂` into maximal faces of `X₁`, and
every maximal face of `X₁` is covered by the image of a maximal face of `X₂`, then trivial `H¹`
transfers from `X₂` to `X₁`. -/
theorem h1_transfer {Λ : Type*} [Group Λ] (hinj : Function.Injective Ψ)
    (h1 : ∀ τ ∈ X₂.tops, ∃ τ₁ ∈ X₁.tops, τ.image Ψ ⊆ τ₁)
    (h2 : ∀ τ₁ ∈ X₁.tops, ∃ τ ∈ X₂.tops, τ₁ ⊆ τ.image Ψ)
    (h : X₂.H1Trivial Λ) : X₁.H1Trivial Λ := by
  intro ϕ hϕ
  have hE : ∀ a b, X₂.IsEdge a b → X₁.IsEdge (Ψ a) (Ψ b) := by
    rintro a b ⟨hab, hf⟩
    refine ⟨fun e => hab (hinj e), ?_⟩
    simpa [Finset.image_insert, Finset.image_singleton] using face_image X₁ X₂ Ψ h1 hf
  have hT : ∀ a b c, X₂.IsTri a b c → X₁.IsTri (Ψ a) (Ψ b) (Ψ c) := by
    rintro a b c ⟨h1', h2', h3', hf⟩
    refine ⟨fun e => h1' (hinj e), fun e => h2' (hinj e), fun e => h3' (hinj e), ?_⟩
    simpa [Finset.image_insert, Finset.image_singleton] using face_image X₁ X₂ Ψ h1 hf
  obtain ⟨g', hg'⟩ := h (fun a b => ϕ (Ψ a) (Ψ b))
    ⟨fun a b hab => hϕ.1 _ _ (hE a b hab), fun a b c habc => hϕ.2 _ _ _ (hT a b c habc)⟩
  refine ⟨fun u => if hu : ∃ a, Ψ a = u then g' (Classical.choose hu) else 1, fun u v huv => ?_⟩
  obtain ⟨τ₁, hτ₁, hsub⟩ := huv.2
  obtain ⟨τ, hτ, hsub'⟩ := h2 τ₁ hτ₁
  have hu : u ∈ τ.image Ψ := hsub' (hsub (by simp))
  have hv : v ∈ τ.image Ψ := hsub' (hsub (by simp))
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hu
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hv
  have hab : X₂.IsEdge a b := ⟨fun e => huv.1 (congrArg Ψ e), τ, hτ, by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption⟩
  have e1 : ∃ a', Ψ a' = Ψ a := ⟨a, rfl⟩
  have e2 : ∃ b', Ψ b' = Ψ b := ⟨b, rfl⟩
  have := hg' a b hab
  simp only [WComplex.d0] at this ⊢
  rw [dif_pos e1, dif_pos e2, hinj (Classical.choose_spec e1), hinj (Classical.choose_spec e2)]
  exact this

end Transfer

/-! ## Colored faces of the KMS complex -/

section Complex

omit [Field F] in
lemma mem_image' {α β : Type*} {inst : DecidableEq β} {g : α → β} {s : Finset α} {b : β} :
    b ∈ @Finset.image α β inst g s ↔ ∃ a ∈ s, g a = b := Finset.mem_image

variable {f : F[X]}

variable (F) in
/-- `τ_K` for the chamber `τ = gH`: its vertices with colour in `K`. -/
noncomputable def part (f : F[X]) (g : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f))
    (K : Finset ℕ) :
    Finset (Σ i : Fin (d + 1), SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ Hf d F f i) :=
  (Finset.univ.filter (fun i : Fin (d + 1) => (i : ℕ) ∈ K)).image
    (fun i => ⟨i, (g : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ Hf d F f i)⟩)

lemma mem_part {g : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)} {K : Finset ℕ}
    {x : Σ i : Fin (d + 1), SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ Hf d F f i} :
    x ∈ part F f g K ↔
      (x.1 : ℕ) ∈ K ∧ x.2 = (g : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ _) := by
  obtain ⟨i, q⟩ := x
  simp only [part, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, h⟩; cases h; exact ⟨hj, rfl⟩
  · rintro ⟨hi, rfl⟩; exact ⟨i, hi, rfl⟩

lemma part_col {g : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)} {K : Finset ℕ}
    (hK : K ⊆ Finset.range (d + 1)) : (part F f g K).image (kmsCol d F f) = K := by
  ext c
  simp only [Finset.mem_image, mem_part, kmsCol]
  constructor
  · rintro ⟨x, ⟨hx, -⟩, rfl⟩; exact hx
  · intro hc
    exact ⟨⟨⟨c, Finset.mem_range.1 (hK hc)⟩, g⟩, ⟨hc, rfl⟩, rfl⟩

lemma part_eq_iff {g g' : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)} {K : Finset ℕ}
    (hK : K ⊆ Finset.range (d + 1)) :
    part F f g K = part F f g' K ↔ ∀ k ∈ K, g⁻¹ * g' ∈ Hf d F f k := by
  constructor
  · intro h k hk
    have hk' : k < d + 1 := Finset.mem_range.1 (hK hk)
    have hm : (⟨⟨k, hk'⟩, (g : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ _)⟩ :
        Σ i : Fin (d + 1), SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ Hf d F f i) ∈
        part F f g' K := h ▸ mem_part.2 ⟨hk, rfl⟩
    exact QuotientGroup.eq.1 (mem_part.1 hm).2
  · intro h
    ext ⟨i, q⟩
    simp only [mem_part]
    constructor
    · rintro ⟨hi, rfl⟩; exact ⟨hi, QuotientGroup.eq.2 (h _ hi)⟩
    · rintro ⟨hi, rfl⟩
      refine ⟨hi, QuotientGroup.eq.2 ?_⟩
      have := inv_mem (h _ hi)
      simpa using this

lemma part_ne {g g' : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)} {K K' : Finset ℕ}
    (hK : K ⊆ Finset.range (d + 1)) (hK' : K' ⊆ Finset.range (d + 1))
    (h : part F f g K = part F f g' K') : K = K' := by
  rw [← part_col (g := g) hK, ← part_col (g := g') hK', h]

lemma filt_mem (g : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)) (K : Finset ℕ)
    {inst : DecidableEq (Σ i : Fin (d + 1), SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸
      Hf d F f i)} {p : DecidablePred (fun v : Σ i : Fin (d + 1),
        SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ Hf d F f i => kmsCol d F f v ∈ K)}
    (x : Σ i : Fin (d + 1), SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ Hf d F f i) :
    x ∈ @Finset.filter _ (fun v => kmsCol d F f v ∈ K) p (@Finset.image _ _ inst
      (fun i : Fin (d + 1) => (⟨i, (g : _ ⧸ Hf d F f i)⟩ :
        Σ i : Fin (d + 1), SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ Hf d F f i))
      Finset.univ) ↔ x ∈ part F f g K := by
  rw [Finset.mem_filter, Finset.mem_image, mem_part]
  simp only [Finset.mem_univ, true_and, kmsCol]
  obtain ⟨i, q⟩ := x
  constructor
  · rintro ⟨⟨j, hj⟩, hi⟩; cases hj; exact ⟨hi, rfl⟩
  · rintro ⟨hi, hq⟩; exact ⟨⟨i, by simp only at hq; rw [hq]⟩, hi⟩

lemma tops_FI (hG : Finite (SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)))
    {I : Finset (Finset ℕ)} (hI : ∀ K ∈ I, K ⊆ Finset.range (d + 1)) (Tp) :
    Tp ∈ (kmsFI d F f I).tops ↔ ∃ g, ∀ P, P ∈ Tp ↔ ∃ K ∈ I, part F f g K = P := by
  simp only [kmsFI, kmsX, WComplex.coloredFaces, cosetComplex, dif_pos hG, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨τ, ⟨⟨g, rfl⟩, -⟩, rfl⟩
    refine ⟨g, fun P => ?_⟩
    rw [mem_image']
    refine exists_congr fun K => and_congr_right fun _ => ?_
    rw [Finset.ext (filt_mem g K)]
  · rintro ⟨g, hg⟩
    refine ⟨_, ⟨⟨g, rfl⟩, fun K hK => ?_⟩, ?_⟩
    · rw [Finset.ext (filt_mem g K)]; exact part_col (hI K hK)
    · ext P
      rw [mem_image', hg]
      refine exists_congr fun K => and_congr_right fun _ => ?_
      rw [Finset.ext (filt_mem g K)]

lemma tops_link {V : Type*} (X : WComplex V) (v : V) (Tp : Finset V) :
    Tp ∈ (X.link {v}).tops ↔ ∃ T' ∈ X.tops, v ∈ T' ∧ ∀ u, u ∈ Tp ↔ u ∈ T' ∧ u ≠ v := by
  simp only [WComplex.link, mem_image', Finset.mem_filter, Finset.singleton_subset_iff]
  constructor
  · rintro ⟨T', ⟨h1, h2⟩, rfl⟩
    exact ⟨T', h1, h2, fun u => by simp only [Finset.mem_sdiff, Finset.mem_singleton]⟩
  · rintro ⟨T', h1, h2, h3⟩
    exact ⟨T', ⟨h1, h2⟩, by ext u; simp only [Finset.mem_sdiff, Finset.mem_singleton, h3]⟩

lemma tops_linkY {I : Finset (Finset ℕ)} {J : Finset ℕ} [hfin : Finite (UL d F (compl d J))]
    (τ) : τ ∈ (linkY d F I J).tops ↔ ∃ x : UL d F (compl d J),
      ∀ p, p ∈ τ ↔ p.2 = (x : UL d F (compl d J) ⧸ linkH d F I J p.1) := by
  simp only [linkY, cosetComplex, dif_pos hfin, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x, fun p => ?_⟩
    rw [mem_image']
    obtain ⟨K, q⟩ := p
    constructor
    · rintro ⟨K', -, h⟩; cases h; rfl
    · intro h; exact ⟨K, Finset.mem_univ _, by simp only at h; rw [h]⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    ext p
    rw [mem_image', hx]
    obtain ⟨K, q⟩ := p
    constructor
    · rintro ⟨K', -, h⟩; cases h; rfl
    · intro h; exact ⟨K, Finset.mem_univ _, by simp only at h; rw [h]⟩

end Complex

/-! ## The vertex link of `F^I X` at a vertex of colour `J` -/

section Main

omit [Field F] in
lemma base_mem {J : Finset ℕ} (hne : J.Nonempty) : base J ∈ J := by
  simp only [base, dif_pos hne]; exact J.min'_mem hne

variable {f : F[X]} [Fact (Irreducible f)]

/-- `⟨K, x(H_J ∩ H_K)⟩ ↦ (g₀ Φ(x))_K`. -/
noncomputable def Psi (ht : AdjoinRoot.root f ≠ 0) (b : Fin (d + 1)) (I : Finset (Finset ℕ))
    (J : Finset ℕ) (g₀ : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f))
    (p : Σ K : {K // K ∈ I.erase J}, (UL d F (compl d J)) ⧸ linkH d F I J K) :
    Finset (Σ i : Fin (d + 1), SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ Hf d F f i) :=
  part F f (g₀ * Φ ht b ((Quotient.out p.2 : UL d F (compl d J)) : SLd d F)) p.1.1

end Main

theorem link_h1 (d r T : ℕ) (hd : 2 ≤ d) (F : Type*) [Field F] [Fintype F]
    (I : Finset (Finset ℕ)) (hI : I ∈ disjointColorSets d r T) (J : Finset ℕ) (hJ : J ∈ I)
    (f : F[X]) (hf : Irreducible f) (hdeg : 2 ≤ f.natDegree)
    (v) (hv : v ∈ (kmsFI d F f I).vertices) (hvJ : v.image (kmsCol d F f) = J)
    (Λ : Type*) [Group Λ] (h : (linkY d F I J).H1Trivial Λ) :
    ((kmsFI d F f I).link {v}).H1Trivial Λ := by
  have : Fact (Irreducible f) := ⟨hf⟩
  have ht : AdjoinRoot.root f ≠ 0 := by
    intro h0
    have hdvd : f ∣ X := AdjoinRoot.mk_eq_zero.1 (by rw [AdjoinRoot.mk_X]; exact h0)
    have := Polynomial.natDegree_le_of_dvd hdvd X_ne_zero
    rw [natDegree_X] at this; omega
  have hIr : ∀ K ∈ I, K ⊆ Finset.range (d + 1) ∧ K.Nonempty := by
    intro K hK
    simp only [disjointColorSets, Finset.mem_filter, Finset.mem_powersetCard] at hI
    have := Finset.mem_powersetCard.1 (hI.1.1 hK)
    exact ⟨this.1, Finset.card_pos.1 (by omega)⟩
  have hIr' : ∀ K ∈ I, K ⊆ Finset.range (d + 1) := fun K hK => (hIr K hK).1
  have hJr := (hIr J hJ).1
  have hJne := (hIr J hJ).2
  have hbJlt : base J < d + 1 := Finset.mem_range.1 (hJr (base_mem hJne))
  let b : Fin (d + 1) := ⟨base J, hbJlt⟩
  have hbmem : (b : ℕ) ∈ J := base_mem hJne
  have hG : Finite (SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)) := by
    by_contra hne
    simp [kmsFI, kmsX, WComplex.coloredFaces, cosetComplex, hne, WComplex.vertices] at hv
  have : Finite (UL d F (compl d J)) := inferInstance
  have MGJ : ∀ N, (∀ j ∈ J, N ∈ Hf d F f j) ↔ ∃ y ∈ UL d F (compl d J), Φ ht b y = N :=
    fun N => MG ht b hbmem (fun c hc => Finset.mem_range.1 (hJr hc)) N
  have MGJK : ∀ K ⊆ Finset.range (d + 1), ∀ N, (∀ c ∈ J ∪ K, N ∈ Hf d F f c) ↔
      ∃ y ∈ UL d F (compl d J \ rl d J K), Φ ht b y = N := by
    intro K hK N
    have e : Finset.range (d + 1) \ (J ∪ K).image (relabel d b) = compl d J \ rl d J K := by
      rw [Finset.image_union]; ext c
      simp only [compl, rl, Finset.mem_sdiff, Finset.mem_union, b]; tauto
    rw [← e]
    exact MG ht b (Finset.mem_union_left _ hbmem) (fun c hc => Finset.mem_range.1
      ((Finset.mem_union.1 hc).elim (fun h => hJr h) (fun h => hK h))) N
  obtain ⟨g₀, hv0⟩ : ∃ g₀, v = part F f g₀ J := by
    simp only [WComplex.vertices, Finset.mem_biUnion, id] at hv
    obtain ⟨Tp, hT, hvT⟩ := hv
    obtain ⟨g, hg⟩ := (tops_FI hG hIr' Tp).1 hT
    obtain ⟨K, hK, rfl⟩ := (hg v).1 hvT
    rw [part_col (hIr' K hK)] at hvJ
    exact ⟨g, by rw [hvJ]⟩
  have hKr : ∀ K : {K // K ∈ I.erase J}, K.1 ⊆ Finset.range (d + 1) :=
    fun K => hIr' K.1 (Finset.mem_of_mem_erase K.2)
  have hΨ : ∀ (K : {K // K ∈ I.erase J}) (x : UL d F (compl d J)),
      Psi ht b I J g₀ ⟨K, (x : _ ⧸ linkH d F I J K)⟩ = part F f (g₀ * Φ ht b x) K.1 := by
    intro K x
    obtain ⟨hh, hh'⟩ := QuotientGroup.mk_out_eq_mul (linkH d F I J K) x
    unfold Psi
    simp only
    rw [hh']
    refine (part_eq_iff (hKr K)).2 fun k hk => ?_
    have hmem : ((hh : UL d F (compl d J)) : SLd d F) ∈ UL d F (compl d J \ rl d J K.1) :=
      Subgroup.mem_subgroupOf.1 hh.2
    have := (MGJK K.1 (hKr K) _).2 ⟨_, hmem, rfl⟩ k (Finset.mem_union_right _ hk)
    have e : (g₀ * Φ ht b ((x * hh : UL d F (compl d J)) : SLd d F))⁻¹ * (g₀ * Φ ht b x) =
        (Φ ht b ((hh : UL d F (compl d J)) : SLd d F))⁻¹ := by
      simp only [Subgroup.coe_mul, map_mul]; group
    rw [e]; exact inv_mem this
  refine h1_transfer _ _ (Psi ht b I J g₀) ?_ ?_ ?_ h
  · rintro ⟨K, q⟩ ⟨K', q'⟩ hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective q'
    rw [hΨ, hΨ] at hq
    obtain rfl : K = K' := Subtype.ext (part_ne (hKr K) (hKr K') hq)
    have hk := (part_eq_iff (hKr K)).1 hq
    have e : (g₀ * Φ ht b x)⁻¹ * (g₀ * Φ ht b x') =
        Φ ht b ((x⁻¹ * x' : UL d F (compl d J)) : SLd d F) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]; group
    rw [e] at hk
    have hJp := (MGJ _).2 ⟨_, (x⁻¹ * x').2, rfl⟩
    obtain ⟨y, hy, hyeq⟩ := (MGJK K.1 (hKr K) _).1
      (fun c hc => (Finset.mem_union.1 hc).elim (hJp c) (hk c))
    have hyx := Φ_inj ht b hyeq
    refine Sigma.ext rfl (heq_of_eq ?_)
    apply QuotientGroup.eq.2
    rw [linkH, Subgroup.mem_subgroupOf, ← hyx]; exact hy
  · intro τ hτ
    obtain ⟨x, hx⟩ := (tops_linkY τ).1 hτ
    have hgJ : part F f g₀ J = part F f (g₀ * Φ ht b x) J :=
      (part_eq_iff hJr).2 (fun j hj => by rw [inv_mul_cancel_left]; exact (MGJ _).2 ⟨x, x.2, rfl⟩ j hj)
    refine ⟨(I.image (part F f (g₀ * Φ ht b x))) \ {v}, (tops_link _ _ _).2
      ⟨I.image (part F f (g₀ * Φ ht b x)), (tops_FI hG hIr' _).2 ⟨_, fun P => Finset.mem_image⟩,
        Finset.mem_image.2 ⟨J, hJ, by rw [← hgJ, hv0]⟩, fun u => by
          simp only [Finset.mem_sdiff, Finset.mem_singleton]⟩, ?_⟩
    intro u hu
    obtain ⟨⟨K, q⟩, hp, rfl⟩ := mem_image'.1 hu
    have hq := (hx _).1 hp
    simp only at hq
    subst hq
    rw [hΨ, Finset.mem_sdiff, Finset.mem_singleton]
    refine ⟨Finset.mem_image.2 ⟨K.1, Finset.mem_of_mem_erase K.2, rfl⟩, fun he => ?_⟩
    rw [hv0] at he
    exact Finset.ne_of_mem_erase K.2 (part_ne (hKr K) hJr he)
  · intro τ₁ hτ₁
    obtain ⟨T', hT', hvT', hτ₁m⟩ := (tops_link _ _ _).1 hτ₁
    obtain ⟨g, hg⟩ := (tops_FI hG hIr' T').1 hT'
    obtain ⟨K₀, hK₀, hK₀v⟩ := (hg v).1 hvT'
    have hK₀J : K₀ = J := part_ne (hIr' K₀ hK₀) hJr (hK₀v.trans hv0)
    rw [hK₀J] at hK₀v
    obtain ⟨y, hy, hyeq⟩ := (MGJ _).1 ((part_eq_iff hJr).1 (hv0.symm.trans hK₀v.symm))
    let x : UL d F (compl d J) := ⟨y, hy⟩
    refine ⟨Finset.univ.image (fun K : {K // K ∈ I.erase J} =>
      (⟨K, (x : _ ⧸ linkH d F I J K)⟩ :
        Σ K : {K // K ∈ I.erase J}, (UL d F (compl d J)) ⧸ linkH d F I J K)),
      (tops_linkY _).2 ⟨x, fun p => ?_⟩, ?_⟩
    · obtain ⟨K, q⟩ := p
      rw [Finset.mem_image]
      constructor
      · rintro ⟨K', -, h⟩; cases h; rfl
      · intro h; exact ⟨K, Finset.mem_univ _, by simp only at h; rw [h]⟩
    · intro u hu
      obtain ⟨huT, huv⟩ := (hτ₁m u).1 hu
      obtain ⟨K, hK, rfl⟩ := (hg u).1 huT
      have hKJ : K ≠ J := fun e => huv (by rw [e]; exact hK₀v)
      refine mem_image'.2 ⟨⟨⟨K, Finset.mem_erase.2 ⟨hKJ, hK⟩⟩, (x : _ ⧸ _)⟩,
        Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
      rw [hΨ]
      show part F f (g₀ * Φ ht b y) K = part F f g K
      rw [hyeq, mul_inv_cancel_left]

end PolySwap.KMS.L317C
end Part_C_link

section Part_D_glue

open Classical Polynomial Matrix

namespace PolySwap.KMS.L317D

open PolySwap.KMS

lemma relabel_inj {d j₀ c c' : ℕ} (hj : j₀ ≤ d) (hc : c < d + 1) (hc' : c' < d + 1)
    (h : relabel d j₀ c = relabel d j₀ c') : c = c' := by
  unfold relabel at h
  have e1 : c + (d + 1) - j₀ = c + (d + 1 - j₀) := by omega
  have e2 : c' + (d + 1) - j₀ = c' + (d + 1 - j₀) := by omega
  rw [e1, e2] at h
  have : c ≡ c' [MOD d + 1] := Nat.ModEq.add_right_cancel' _ h
  rwa [Nat.ModEq, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hc'] at this

lemma mem_sub {d r T : ℕ} {I : Finset (Finset ℕ)} (hI : I ∈ disjointColorSets d r T)
    {K : Finset ℕ} (hK : K ∈ I) : K ⊆ Finset.range (d + 1) := by
  unfold disjointColorSets at hI
  rw [Finset.mem_filter, Finset.mem_powersetCard] at hI
  exact (Finset.mem_powersetCard.1 (hI.1.1 hK)).1

lemma base_le {d r T : ℕ} {I : Finset (Finset ℕ)} (hI : I ∈ disjointColorSets d r T)
    {J : Finset ℕ} (hJ : J ∈ I) : base J ≤ d := by
  unfold base
  split_ifs with h
  · have := mem_sub hI hJ (J.min'_mem h); simp at this; omega
  · omega

/-- distinct members of `I` have disjoint relabelled colour sets -/
theorem rl_disjoint (d r T : ℕ) (I : Finset (Finset ℕ)) (hI : I ∈ disjointColorSets d r T)
    (J : Finset ℕ) (hJ : J ∈ I) (K K' : Finset ℕ) (hK : K ∈ I) (hK' : K' ∈ I) (hne : K ≠ K') :
    Disjoint (rl d J K) (rl d J K') := by
  have hpd : (I : Set (Finset ℕ)).PairwiseDisjoint id := by
    unfold disjointColorSets at hI; exact (Finset.mem_filter.1 hI).2
  have hKK : Disjoint K K' := hpd hK hK' hne
  rw [Finset.disjoint_left]
  intro c hc hc'
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hc
  obtain ⟨y, hy, hxy⟩ := Finset.mem_image.1 hc'
  have := relabel_inj (base_le hI hJ) (Finset.mem_range.1 (mem_sub hI hK' hy))
    (Finset.mem_range.1 (mem_sub hI hK hx)) hxy
  subst this
  exact Finset.disjoint_left.1 hKK hx hy

lemma filter_card_le {d r T : ℕ} {I : Finset (Finset ℕ)} (hI : I ∈ disjointColorSets d r T)
    {J : Finset ℕ} (hJ : J ∈ I) (c : ℕ) :
    ((I.erase J).filter (fun K => c ∈ rl d J K)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro K hK K' hK'
  rw [Finset.mem_filter] at hK hK'
  by_contra hne
  exact Finset.disjoint_left.1 (rl_disjoint d r T I hI J hJ K K' (Finset.mem_of_mem_erase hK.1)
    (Finset.mem_of_mem_erase hK'.1) hne) hK.2 hK'.2

lemma card_erase_ge {I : Finset (Finset ℕ)} {J : Finset ℕ} (hJ : J ∈ I) :
    (I.erase J).card + 1 = I.card := Finset.card_erase_add_one hJ

/-- every pair of colours misses some `K ∈ I \ {J}`, when `|I| ≥ 4` -/
theorem pair_avoid (d r T : ℕ) (I : Finset (Finset ℕ)) (hI : I ∈ disjointColorSets d r T)
    (J : Finset ℕ) (hJ : J ∈ I) (h4 : 4 ≤ I.card) :
    ∀ c ∈ compl d J, ∀ c' ∈ compl d J, ∃ K : {K // K ∈ I.erase J},
      c ∉ rl d J K.1 ∧ c' ∉ rl d J K.1 := by
  intro c _ c' _
  have hS := card_erase_ge hJ
  have h1 := filter_card_le hI hJ c
  have h2 := filter_card_le hI hJ c'
  have hor : ((I.erase J).filter (fun K => c ∈ rl d J K ∨ c' ∈ rl d J K)).card ≤ 2 := by
    rw [Finset.filter_or]
    exact (Finset.card_union_le _ _).trans (by omega)
  have hsum := Finset.card_filter_add_card_filter_not
    (s := I.erase J) (fun K => c ∈ rl d J K ∨ c' ∈ rl d J K)
  obtain ⟨K, hK⟩ : ((I.erase J).filter (fun K => ¬ (c ∈ rl d J K ∨ c' ∈ rl d J K))).Nonempty := by
    rw [← Finset.card_pos]; omega
  rw [Finset.mem_filter, not_or] at hK
  exact ⟨⟨K, hK.1⟩, hK.2⟩

lemma one_avoid {d r T : ℕ} {I : Finset (Finset ℕ)} (hI : I ∈ disjointColorSets d r T)
    {J : Finset ℕ} (hJ : J ∈ I) (h3 : 3 ≤ I.card) (c : ℕ) :
    ∃ K : {K // K ∈ I.erase J}, c ∉ rl d J K.1 := by
  have hS := card_erase_ge hJ
  have h1 := filter_card_le hI hJ c
  have hsum := Finset.card_filter_add_card_filter_not
    (s := I.erase J) (fun K => c ∈ rl d J K)
  obtain ⟨K, hK⟩ : ((I.erase J).filter (fun K => c ∉ rl d J K)).Nonempty := by
    rw [← Finset.card_pos]; omega
  rw [Finset.mem_filter] at hK
  exact ⟨⟨K, hK.1⟩, hK.2⟩

/-- generation, when `|I| ≥ 3` -/
theorem linkH_gen (d r T : ℕ) (F : Type*) [Field F] (I : Finset (Finset ℕ))
    (hI : I ∈ disjointColorSets d r T) (J : Finset ℕ) (hJ : J ∈ I) (h3 : 3 ≤ I.card) :
    Subgroup.closure (⋃ K, (linkH d F I J K : Set (UL d F (compl d J)))) = ⊤ := by
  set H := Subgroup.closure (⋃ K, (linkH d F I J K : Set (UL d F (compl d J))))
  have key : UL d F (compl d J) ≤ H.map (UL d F (compl d J)).subtype := by
    unfold UL
    rw [Subgroup.closure_le]
    rintro x ⟨lam, i, j, hjB, hj1, hij, hx⟩
    have hxU : x ∈ UL d F (compl d J) := Subgroup.subset_closure ⟨lam, i, j, hjB, hj1, hij, hx⟩
    obtain ⟨K, hK⟩ := one_avoid hI hJ h3 (j : ℕ)
    refine ⟨⟨x, hxU⟩, Subgroup.subset_closure (Set.mem_iUnion.2 ⟨K, ?_⟩), rfl⟩
    change (⟨x, hxU⟩ : UL d F (compl d J)) ∈
      (UL d F (compl d J \ rl d J K.1)).subgroupOf (UL d F (compl d J))
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.subset_closure ⟨lam, i, j, Finset.mem_sdiff.2 ⟨hjB, hK⟩, hj1, hij, hx⟩
  rw [eq_top_iff]
  rintro g -
  obtain ⟨h, hh, he⟩ := key g.2
  have : h = g := Subtype.ext he
  exact this ▸ hh

end PolySwap.KMS.L317D
end Part_D_glue

namespace PolySwap.KMS.L317

open PolySwap.KMS

lemma ne_of_three (I : Finset (Finset ℕ)) (J : Finset ℕ) (hJ : J ∈ I) (h3 : 3 ≤ I.card) :
    Nonempty {K // K ∈ I.erase J} := by
  have : (I.erase J).Nonempty := Finset.card_pos.1 (by rw [Finset.card_erase_of_mem hJ]; omega)
  obtain ⟨K, hK⟩ := this
  exact ⟨⟨K, hK⟩⟩

lemma conn (d r T : ℕ) (F : Type*) [Field F] [Fintype F] (I : Finset (Finset ℕ))
    (hI : I ∈ disjointColorSets d r T) (J : Finset ℕ) (hJ : J ∈ I) (h3 : 3 ≤ I.card) :
    (linkY d F I J).IsConnected :=
  haveI := ne_of_three I J hJ h3
  L317B.connected_of_closure (linkH d F I J) (L317D.linkH_gen d r T F I hI J hJ h3)

lemma oneConn (d r T : ℕ) (F : Type*) [Field F] [Fintype F] (hq : 5 ≤ Fintype.card F)
    (I : Finset (Finset ℕ)) (hI : I ∈ disjointColorSets d r T) (J : Finset ℕ) (hJ : J ∈ I)
    (h4 : 4 ≤ I.card) : (linkY d F I J).IsOneConnected :=
  haveI := ne_of_three I J hJ (by omega)
  L317B.oneConnected_of_pres (linkH d F I J) (conn d r T F I hI J hJ (by omega))
    (L317A.amalgam d F (by omega) (compl d J) (fun K : {K // K ∈ I.erase J} => rl d J K.1)
      (L317D.pair_avoid d r T I hI J hJ h4))

lemma linkH1 (d r T : ℕ) (hd : 2 ≤ d) (F : Type*) [Field F] [Fintype F]
    (hq : 5 ≤ Fintype.card F) (I : Finset (Finset ℕ)) (hI : I ∈ disjointColorSets d r T)
    (J : Finset ℕ) (hJ : J ∈ I) (h4 : 4 ≤ I.card) (f : Polynomial F) (hf : Irreducible f)
    (hdeg : 2 ≤ f.natDegree)
    (v : Finset (Σ i : Fin (d + 1), Matrix.SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ Hf d F f i))
    (hv : v ∈ (kmsFI d F f I).vertices) (hvJ : v.image (kmsCol d F f) = J)
    (Λ : Type*) [Group Λ] : ((kmsFI d F f I).link {v}).H1Trivial Λ :=
  L317C.link_h1 d r T hd F I hI J hJ f hf hdeg v hv hvJ Λ
    (L317B.h1Trivial_of_oneConnected _ (oneConn d r T F hq I hI J hJ h4) Λ)

end PolySwap.KMS.L317

open PolySwap.KMS in
theorem solution (d r T : ℕ) (hd : 2 ≤ d) (hr : 1 ≤ r) (F : Type*) [Field F] [Fintype F]
    (hq : 5 ≤ Fintype.card F) (I : Finset (Finset ℕ)) (hI : I ∈ disjointColorSets d r T)
    (J : Finset ℕ) (hJ : J ∈ I) :
    (3 ≤ I.card → (linkY d F I J).IsConnected) ∧
    (4 ≤ I.card → (linkY d F I J).IsOneConnected) ∧
    (4 ≤ I.card → ∀ f : Polynomial F, Irreducible f → 2 ≤ f.natDegree →
      ∀ v ∈ (kmsFI d F f I).vertices, v.image (kmsCol d F f) = J →
        ∀ (Λ : Type*) [Group Λ], ((kmsFI d F f I).link {v}).H1Trivial Λ) :=
  ⟨PolySwap.KMS.L317.conn d r T F I hI J hJ,
   PolySwap.KMS.L317.oneConn d r T F hq I hI J hJ,
   fun h4 f hf hdeg v hv hvJ Λ _ =>
     PolySwap.KMS.L317.linkH1 d r T hd F hq I hI J hJ h4 f hf hdeg v hv hvJ Λ⟩
