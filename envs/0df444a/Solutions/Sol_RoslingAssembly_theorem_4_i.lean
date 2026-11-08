-- Prove2me | solution 1 for RoslingAssembly.theorem_4_i
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T18:59:19.488711+00:00
-- url     : https://prove2.me/submissions/c4bd93fe-bbc6-4c65-9718-4b662e896877

import Mathlib
import Definitions.Def_RoslingAssembly_IsPolicy
import Definitions.Def_RoslingAssembly_Feasible
import Definitions.Def_RoslingAssembly_HistOK
import Definitions.Def_RoslingAssembly_CostBelow
import Definitions.Def_RoslingAssembly_Network_B
import Definitions.Def_RoslingAssembly_Network_Ms

set_option autoImplicit false
set_option linter.all false

open MeasureTheory

namespace RoslingAssembly
namespace R5f

variable {N : ℕ} (net : Network N)

/-- the successor relation -/
def Rs (a b : Fin N) : Prop := net.s a = some b

lemma transGen_lt {a b : Fin N} (h : Relation.TransGen (Rs net) a b) : b < a := by
  induction h with
  | single hab => exact net.s_lt _ _ hab
  | tail _ hbc ih => exact lt_trans (net.s_lt _ _ hbc) ih

lemma mem_A {k x : Fin N} : x ∈ net.A k ↔ Relation.TransGen (Rs net) k x := by
  unfold Network.A
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

lemma not_mem_A_self (k : Fin N) : k ∉ net.A k := by
  intro h
  exact lt_irrefl _ (transGen_lt net ((mem_A net).1 h))

lemma A_of_none {k : Fin N} (hk : net.s k = none) : net.A k = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  rcases Relation.TransGen.head'_iff.1 ((mem_A net).1 hx) with ⟨b, hb, -⟩
  have : net.s k = some b := hb
  rw [hk] at this
  exact absurd this (by simp)

lemma A_of_some {k j : Fin N} (hk : net.s k = some j) : net.A k = insert j (net.A j) := by
  ext x
  rw [Finset.mem_insert, mem_A, mem_A, Relation.TransGen.head'_iff]
  constructor
  · rintro ⟨b, hb, hbx⟩
    have hbj : b = j := by
      have : net.s k = some b := hb
      rw [hk] at this
      exact (Option.some.inj this).symm
    subst hbj
    rcases Relation.reflTransGen_iff_eq_or_transGen.1 hbx with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨j, hk, h ▸ Relation.ReflTransGen.refl⟩
    · exact ⟨j, hk, h.to_reflTransGen⟩

lemma M_eq (ℓ : Fin N → ℕ) (k : Fin N) : net.M ℓ k = ℓ k + net.Ms ℓ k := by
  unfold Network.Ms
  cases hk : net.s k with
  | none => simp [Network.M, A_of_none net hk]
  | some j =>
    simp only [Network.M, A_of_some net hk]
    rw [Finset.sum_insert (not_mem_A_self net j)]

lemma not_mem_B_self (i : Fin N) : i ∉ net.B i := by
  unfold Network.B
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact not_mem_A_self net i

/-- predecessors of an item of `U = insert i (B i)` lie in `U` -/
lemma P_sub_U (i j k : Fin N) (hj : j ∈ insert i (net.B i)) (hk : k ∈ net.P j) :
    k ∈ insert i (net.B i) := by
  have hs : net.s k = some j := by
    unfold Network.P at hk; simpa using hk
  apply Finset.mem_insert_of_mem
  unfold Network.B
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [A_of_some net hs]
  rcases Finset.mem_insert.1 hj with h | h
  · exact Finset.mem_insert.2 (Or.inl h.symm)
  · unfold Network.B at h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact Finset.mem_insert_of_mem h

/-- the condition's sum is a sum over `U` -/
lemma cond_sum (H : Fin N → ℝ) (ℓ : Fin N → ℕ) (α : ℝ) (i : Fin N) :
    net.h H i * α ^ (-(net.Ms ℓ i : ℤ)) + ∑ k ∈ net.B i, net.h H k * α ^ (-(net.Ms ℓ k : ℤ)) =
      ∑ k ∈ insert i (net.B i), net.h H k * α ^ (-(net.Ms ℓ k : ℤ)) := by
  rw [Finset.sum_insert (not_mem_B_self net i)]


/-! ## S2: closed-form policy (replenish own demand after delay `dd j`, plus a step shift) -/

noncomputable def Lb (ℓ : Fin N → ℕ) : ℕ := Finset.univ.sup ℓ

noncomputable def dd (ℓ : Fin N → ℕ) (j : Fin N) : ℕ := (N - j.val) * (Lb ℓ + 1)

lemma le_Lb (ℓ : Fin N → ℕ) (k : Fin N) : ℓ k ≤ Lb ℓ := Finset.le_sup (Finset.mem_univ k)

lemma s_of_mem_P {j k : Fin N} (hk : k ∈ net.P j) : net.s k = some j := by
  unfold Network.P at hk; simpa using hk

lemma dd_ge (ℓ : Fin N → ℕ) {j k : Fin N} (hk : k ∈ net.P j) : dd ℓ k + ℓ k + 1 ≤ dd ℓ j := by
  have hjk : j < k := net.s_lt _ _ (s_of_mem_P net hk)
  have hjk' : j.val < k.val := hjk
  have h1 : N - k.val + 1 ≤ N - j.val := by have := k.isLt; omega
  have h2 := Nat.mul_le_mul_right (Lb ℓ + 1) h1
  have h3 := le_Lb ℓ k
  unfold dd; rw [add_mul, one_mul] at h2; omega

def shf (U : Finset (Fin N)) (T : Fin N → ℕ) (δ : ℝ) (n : ℕ) (j : Fin N) : ℝ :=
  if j ∈ U ∧ T j ≤ n then δ else 0

noncomputable def pol (Yh : ℤ → Fin N → ℝ) (ξh : ℤ → ℝ) (ℓ : Fin N → ℕ) (U : Finset (Fin N))
    (T : Fin N → ℕ) (δ : ℝ) : ℕ → (ℕ → ℝ) → Fin N → ℝ := fun n ω j =>
  Yh 0 j - ξh 0 - ∑ r ∈ Finset.range n, ω r + ∑ r ∈ Finset.range (n - dd ℓ j), max (ω r) 0 +
    shf U T δ n j

lemma shf_nonneg {U : Finset (Fin N)} {T : Fin N → ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) (j : Fin N) :
    0 ≤ shf U T δ n j := by
  unfold shf; split_ifs <;> linarith

lemma shf_mono {U : Finset (Fin N)} {T : Fin N → ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (j : Fin N) {m n : ℕ}
    (h : m ≤ n) : shf U T δ m j ≤ shf U T δ n j := by
  unfold shf
  split_ifs with h1 h2 <;> first | exact le_rfl | exact hδ | exact absurd ⟨h1.1, h1.2.trans h⟩ h2

lemma shf_P (ℓ : Fin N → ℕ) {U : Finset (Fin N)} {T : Fin N → ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hU : ∀ j k, k ∈ net.P j → j ∈ U → k ∈ U ∧ T k + ℓ k ≤ T j) {j k : Fin N}
    (hk : k ∈ net.P j) (n : ℕ) :
    (ℓ k ≤ n → shf U T δ n j ≤ shf U T δ (n - ℓ k) k) ∧ (n < ℓ k → shf U T δ n j = 0) := by
  constructor
  · intro hn
    unfold shf
    split_ifs with h1 h2 <;> first | exact le_rfl | exact hδ | skip
    exfalso
    have a1 := (hU j k hk h1.1).2
    have a2 := h1.2
    exact h2 ⟨(hU j k hk h1.1).1, by omega⟩
  · intro hn
    unfold shf
    rw [if_neg]
    rintro ⟨h1, h2⟩
    have := (hU j k hk h1).2
    omega

/-! ## path lemmas -/

lemma Ypath_succ (Yh : ℤ → Fin N → ℝ) (P : ℕ → (ℕ → ℝ) → Fin N → ℝ) (ω : ℕ → ℝ) (n : ℕ)
    (i : Fin N) : Ypath Yh P ω ((n : ℤ) + 1) i = P n ω i := by
  unfold Ypath
  rw [if_neg (by omega), show ((n : ℤ) + 1 - 1).toNat = n by omega]

lemma Ypath_nonpos (Yh : ℤ → Fin N → ℝ) (P : ℕ → (ℕ → ℝ) → Fin N → ℝ) (ω : ℕ → ℝ) {t : ℤ}
    (ht : t ≤ 0) (i : Fin N) : Ypath Yh P ω t i = Yh t i := by
  unfold Ypath; rw [if_pos ht]

lemma dem_succ (ξh : ℤ → ℝ) (ω : ℕ → ℝ) (r : ℕ) : demPath ξh ω ((r : ℤ) + 1) = ω r := by
  unfold demPath
  rw [if_neg (by omega), show ((r : ℤ) + 1 - 1).toNat = r by omega]

lemma dem_nonpos (ξh : ℤ → ℝ) (ω : ℕ → ℝ) {s : ℤ} (hs : s ≤ 0) : demPath ξh ω s = ξh s := by
  unfold demPath; rw [if_pos hs]

lemma sumIco_split (f : ℤ → ℝ) {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    ∑ s ∈ Finset.Ico a c, f s = ∑ s ∈ Finset.Ico a b, f s + ∑ s ∈ Finset.Ico b c, f s := by
  rw [← Finset.Ico_union_Ico_eq_Ico hab hbc,
    Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive a b c)]

lemma sumIco_one (f : ℤ → ℝ) (b : ℤ) : ∑ s ∈ Finset.Ico b (b + 1), f s = f b := by
  rw [show Finset.Ico b (b + 1) = {b} by ext x; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega]
  simp

lemma sum_dem_nat (ξh : ℤ → ℝ) (ω : ℕ → ℝ) (m n : ℕ) :
    ∑ s ∈ Finset.Ico ((m : ℤ) + 1) ((n : ℤ) + 1), demPath ξh ω s = ∑ r ∈ Finset.Ico m n, ω r := by
  have e : Finset.Ico ((m : ℤ) + 1) ((n : ℤ) + 1) =
      (Finset.Ico m n).image (fun r : ℕ => (r : ℤ) + 1) := by
    ext s
    simp only [Finset.mem_Ico, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(s - 1).toNat, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨r, ⟨h1, h2⟩, rfl⟩
      omega
  rw [e, Finset.sum_image (by intro a _ b _ h; simp only at h; omega)]
  exact Finset.sum_congr rfl fun r _ => dem_succ ξh ω r

lemma sum_dem_zero (ξh : ℤ → ℝ) (ω : ℕ → ℝ) (n : ℕ) :
    ∑ s ∈ Finset.Ico (0 : ℤ) ((n : ℤ) + 1), demPath ξh ω s =
      ξh 0 + ∑ r ∈ Finset.range n, ω r := by
  rw [sumIco_split _ (b := 1) (by norm_num) (by omega)]
  have h1 := sum_dem_nat ξh ω 0 n
  simp only [Nat.cast_zero, zero_add] at h1
  rw [h1, ← Finset.range_eq_Ico, show (1 : ℤ) = 0 + 1 by norm_num, sumIco_one,
    dem_nonpos _ _ le_rfl]

/-! ## history lemmas -/

lemma hist_chain {ℓ : Fin N → ℕ} {Yh : ℤ → Fin N → ℝ} {ξh : ℤ → ℝ} (hH : HistOK net ℓ Yh ξh)
    (k : Fin N) : ∀ m : ℕ, m ≤ ℓ k →
      Yh (-(ℓ k : ℤ)) k - ∑ s ∈ Finset.Ico (-(ℓ k : ℤ)) (-(ℓ k : ℤ) + m), ξh s ≤
        Yh (-(ℓ k : ℤ) + m) k := by
  have hL := Finset.le_sup (f := ℓ) (Finset.mem_univ k)
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have ih' := ih (by omega)
    have hs := (hH (-(ℓ k : ℤ) + ((m + 1 : ℕ) : ℤ)) (by push_cast; omega) (by push_cast; omega) k).1
    rw [show (-(ℓ k : ℤ) + ((m + 1 : ℕ) : ℤ)) = (-(ℓ k : ℤ) + m) + 1 by push_cast; ring] at hs ⊢
    simp only [add_sub_cancel_right] at hs
    rw [sumIco_split ξh (b := -(ℓ k : ℤ) + m) (by omega) (by omega), sumIco_one]
    linarith

lemma hist_main {ℓ : Fin N → ℕ} {Yh : ℤ → Fin N → ℝ} {ξh : ℤ → ℝ} (hH : HistOK net ℓ Yh ξh)
    {i k : Fin N} (hk : k ∈ net.P i) (u : ℤ) (hu1 : -(ℓ k : ℤ) ≤ u) (hu2 : u ≤ 0) :
    Yh 0 i ≤ Yh u k - ∑ s ∈ Finset.Ico u 0, ξh s := by
  have h0 := (hH 0 (by simp) le_rfl i).2 k hk
  rw [zero_sub] at h0
  have hc := hist_chain net hH k (u + ℓ k).toNat (by omega)
  rw [show -(ℓ k : ℤ) + ((u + ℓ k).toNat : ℤ) = u by omega] at hc
  rw [sumIco_split ξh (b := u) hu1 hu2] at h0
  linarith

/-! ## S3: feasibility on every path -/

theorem feasible_pol {ℓ : Fin N → ℕ} {Yh : ℤ → Fin N → ℝ} {ξh : ℤ → ℝ}
    (hH : HistOK net ℓ Yh ξh) {U : Finset (Fin N)} {T : Fin N → ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hU : ∀ j k, k ∈ net.P j → j ∈ U → k ∈ U ∧ T k + ℓ k ≤ T j) :
    Feasible net ℓ Yh ξh (pol Yh ξh ℓ U T δ) := by
  intro ω t ht i
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, t = (n : ℤ) + 1 := ⟨(t - 1).toNat, by omega⟩
  refine ⟨?_, fun k hk => ?_⟩
  · unfold Xpath
    rw [Ypath_succ, add_sub_cancel_right]
    cases n with
    | zero =>
      simp only [Nat.cast_zero]
      rw [Ypath_nonpos _ _ _ le_rfl, dem_nonpos _ _ le_rfl]
      simp only [pol, Finset.range_zero, Finset.sum_empty, Nat.zero_sub]
      linarith [shf_nonneg (U := U) (T := T) hδ 0 i]
    | succ m =>
      rw [Nat.cast_succ, Ypath_succ, dem_succ]
      simp only [pol, Finset.sum_range_succ]
      have h1 : ∑ r ∈ Finset.range (m - dd ℓ i), max (ω r) 0 ≤
          ∑ r ∈ Finset.range (m + 1 - dd ℓ i), max (ω r) 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          (fun _ _ _ => le_max_right _ _)
      have h2 := shf_mono (U := U) (T := T) hδ i (Nat.le_succ m)
      linarith
  · unfold XlPath
    have hd := dd_ge net ℓ hk
    by_cases hn : ℓ k ≤ n
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + ℓ k := ⟨n - ℓ k, by omega⟩
      rw [show ((m + ℓ k : ℕ) : ℤ) + 1 - ℓ k = (m : ℤ) + 1 by push_cast; ring, Ypath_succ,
        Ypath_succ, show ((m + ℓ k : ℕ) : ℤ) + 1 = ((m + ℓ k : ℕ) : ℤ) + 1 from rfl,
        sum_dem_nat]
      simp only [pol]
      have e := Finset.sum_range_add_sum_Ico (fun r => ω r) (Nat.le_add_right m (ℓ k))
      have h1 : ∑ r ∈ Finset.range (m + ℓ k - dd ℓ i), max (ω r) 0 ≤
          ∑ r ∈ Finset.range (m - dd ℓ k), max (ω r) 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          (fun _ _ _ => le_max_right _ _)
      have h2 := (shf_P net ℓ hδ hU hk (m + ℓ k)).1 (Nat.le_add_left _ _)
      rw [Nat.add_sub_cancel] at h2
      have h3 := hist_main net hH hk 0 (by omega) le_rfl
      simp only [Finset.Ico_self, Finset.sum_empty, sub_zero] at h3
      linarith
    · push Not at hn
      rw [Ypath_succ, Ypath_nonpos _ _ _ (by omega)]
      rw [sumIco_split _ (b := 0) (by omega) (by omega), sum_dem_zero]
      rw [Finset.sum_congr rfl (fun s hs => dem_nonpos ξh ω (by simp only [Finset.mem_Ico] at hs; omega))]
      simp only [pol]
      rw [show n - dd ℓ i = 0 by omega, (shf_P net ℓ hδ hU hk n).2 hn]
      have h3 := hist_main net hH hk ((n : ℤ) + 1 - ℓ k) (by omega) (by omega)
      simp only [Finset.range_zero, Finset.sum_empty]
      linarith

lemma isPolicy_pol (Yh : ℤ → Fin N → ℝ) (ξh : ℤ → ℝ) (ℓ : Fin N → ℕ) (U : Finset (Fin N))
    (T : Fin N → ℕ) (δ : ℝ) : IsPolicy (pol Yh ξh ℓ U T δ) := by
  refine ⟨fun n ω ω' h => ?_, fun n j => ?_⟩
  · funext j
    have e1 : ∑ r ∈ Finset.range n, ω r = ∑ r ∈ Finset.range n, ω' r :=
      Finset.sum_congr rfl fun r hr => h r (Finset.mem_range.1 hr)
    have e2 : ∑ r ∈ Finset.range (n - dd ℓ j), max (ω r) 0 =
        ∑ r ∈ Finset.range (n - dd ℓ j), max (ω' r) 0 :=
      Finset.sum_congr rfl fun r hr => by
        rw [h r (by have := Finset.mem_range.1 hr; omega)]
    simp only [pol, e1, e2]
  · simp only [pol]
    exact (((measurable_const.sub (Finset.measurable_sum _ fun r _ => measurable_pi_apply r)).add
      (Finset.measurable_sum _ fun r _ => (measurable_pi_apply r).max measurable_const)).add
      measurable_const)

/-! ## S4: backlog function and path-measure facts -/

section G
variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

lemma integrable_coord (hμi : Integrable (fun x => x) μ) (m : ℕ) (j : Fin (m + 1)) :
    Integrable (fun x : Fin (m + 1) → ℝ => x j) (Measure.pi fun _ => μ) := by
  have h := MeasureTheory.measurePreserving_eval (fun _ : Fin (m + 1) => μ) j
  exact (h.integrable_comp hμi.aestronglyMeasurable).2 hμi

lemma integrable_G_integrand (hμi : Integrable (fun x => x) μ) (m : ℕ) (y : ℝ) :
    Integrable (fun x : Fin (m + 1) → ℝ => max 0 (∑ j, x j - y)) (Measure.pi fun _ => μ) := by
  have hs : Integrable (fun x : Fin (m + 1) → ℝ => ∑ j, x j - y) (Measure.pi fun _ => μ) :=
    (integrable_finset_sum _ fun j _ => integrable_coord hμi m j).sub (integrable_const y)
  exact (integrable_const (0 : ℝ)).sup hs

lemma G_nonneg (m : ℕ) (y : ℝ) : 0 ≤ backlogG μ m y :=
  integral_nonneg fun _ => le_max_left _ _

lemma max_sub_lip (S y y' : ℝ) : |max 0 (S - y) - max 0 (S - y')| ≤ |y - y'| := by
  have a1 := le_abs_self (y - y')
  have a2 := neg_abs_le (y - y')
  have h1 : max 0 (S - y) ≤ max 0 (S - y') + |y - y'| :=
    max_le (add_nonneg (le_max_left _ _) (abs_nonneg _)) (by linarith [le_max_right 0 (S - y')])
  have h2 : max 0 (S - y') ≤ max 0 (S - y) + |y - y'| :=
    max_le (add_nonneg (le_max_left _ _) (abs_nonneg _)) (by linarith [le_max_right 0 (S - y)])
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

lemma G_lip (hμi : Integrable (fun x => x) μ) (m : ℕ) (y y' : ℝ) :
    |backlogG μ m y - backlogG μ m y'| ≤ |y - y'| := by
  unfold backlogG
  rw [← integral_sub (integrable_G_integrand hμi m y) (integrable_G_integrand hμi m y')]
  calc _ ≤ ∫ x, |max 0 (∑ j, x j - y) - max 0 (∑ j, x j - y')| ∂(Measure.pi fun _ : Fin (m + 1) => μ) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _x, |y - y'| ∂(Measure.pi fun _ : Fin (m + 1) => μ) :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (integrable_const _)
          (ae_of_all _ fun x => max_sub_lip _ y y')
    _ = |y - y'| := by simp

lemma G_anti (hμi : Integrable (fun x => x) μ) (m : ℕ) : Antitone (backlogG μ m) := by
  intro y y' h
  unfold backlogG
  exact integral_mono (integrable_G_integrand hμi m y') (integrable_G_integrand hμi m y)
    fun x => max_le_max le_rfl (by linarith)

lemma G_le (hμi : Integrable (fun x => x) μ) (m : ℕ) (y : ℝ) :
    backlogG μ m y ≤ backlogG μ m 0 + |y| := by
  have := G_lip hμi m y 0
  rw [sub_zero] at this
  linarith [le_abs_self (backlogG μ m y - backlogG μ m 0)]

lemma G_cont (hμi : Integrable (fun x => x) μ) (m : ℕ) : Continuous (backlogG μ m) :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun y y' => by
    simpa [Real.dist_eq] using G_lip hμi m y y').continuous

lemma coord_mp (r : ℕ) :
    MeasurePreserving (fun ω : ℕ → ℝ => ω r) (pathMeasure μ) μ :=
  measurePreserving_eval_infinitePi (fun _ : ℕ => μ) r

lemma integrable_path_coord (hμi : Integrable (fun x => x) μ) (r : ℕ) :
    Integrable (fun ω : ℕ → ℝ => ω r) (pathMeasure μ) :=
  ((coord_mp r).integrable_comp hμi.aestronglyMeasurable).2 hμi

lemma ae_path_nonneg (hμ0 : μ (Set.Iio 0) = 0) :
    ∀ᵐ ω ∂(pathMeasure μ), ∀ r, 0 ≤ ω r := by
  rw [ae_all_iff]
  intro r
  have h : ∀ᵐ x ∂μ, 0 ≤ x := by
    rw [ae_iff]
    convert hμ0 using 2
    ext x
    simp [not_le]
  exact (coord_mp r).quasiMeasurePreserving.ae h

lemma shift_mp (m : ℕ) :
    MeasurePreserving (fun ω : ℕ → ℝ => fun r => ω (r + m)) (pathMeasure μ) (pathMeasure μ) := by
  have hmeas : Measurable (fun ω : ℕ → ℝ => fun r => ω (r + m)) :=
    measurable_pi_lambda _ fun r => measurable_pi_apply _
  refine ⟨hmeas, ?_⟩
  unfold pathMeasure
  apply Measure.eq_infinitePi
  intro s t ht
  rw [Measure.map_apply hmeas (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  have e : (fun ω : ℕ → ℝ => fun r => ω (r + m)) ⁻¹' (Set.pi (↑s) t) =
      Set.pi (↑(s.map ⟨fun r : ℕ => r + m, add_left_injective m⟩)) (fun r => t (r - m)) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Finset.coe_map, Set.forall_mem_image, Finset.mem_coe,
      Function.Embedding.coeFn_mk]
    exact forall₂_congr fun a _ => by rw [Nat.add_sub_cancel]
  rw [e, Measure.infinitePi_pi]
  · rw [Finset.prod_map]
    exact Finset.prod_congr rfl fun x _ => by simp only [Function.Embedding.coeFn_mk]; rw [Nat.add_sub_cancel]
  · intro i _; exact ht _

end G

/-! ## S5: the set U, the delays T, the horizon D -/

open Filter Topology

noncomputable def cc (ℓ : Fin N → ℕ) : ℕ := ∑ j, net.M ℓ j

noncomputable def TT (ℓ : Fin N → ℕ) (j : Fin N) : ℕ := cc net ℓ - net.M ℓ j

noncomputable def DD (ℓ : Fin N → ℕ) : ℕ := ∑ j, (dd ℓ j + TT net ℓ j)

lemma M_le_cc (ℓ : Fin N → ℕ) (j : Fin N) : net.M ℓ j ≤ cc net ℓ :=
  Finset.single_le_sum (f := fun j => net.M ℓ j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

lemma Ms_of_P (ℓ : Fin N → ℕ) {j k : Fin N} (hk : k ∈ net.P j) : net.Ms ℓ k = net.M ℓ j := by
  unfold Network.Ms; rw [s_of_mem_P net hk]

lemma hU_main (ℓ : Fin N → ℕ) (i : Fin N) :
    ∀ j k, k ∈ net.P j → j ∈ insert i (net.B i) →
      k ∈ insert i (net.B i) ∧ TT net ℓ k + ℓ k ≤ TT net ℓ j := by
  intro j k hk hj
  refine ⟨P_sub_U net i j k hj hk, ?_⟩
  have h1 := M_eq net ℓ k
  have h2 := Ms_of_P net ℓ hk
  have h3 := M_le_cc net ℓ k
  have h4 := M_le_cc net ℓ j
  unfold TT; omega

lemma hD_main (ℓ : Fin N → ℕ) : ∀ j, dd ℓ j ≤ DD net ℓ ∧ TT net ℓ j ≤ DD net ℓ := by
  intro j
  have := Finset.single_le_sum (f := fun j => dd ℓ j + TT net ℓ j) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ j)
  beta_reduce at this
  unfold DD; constructor <;> omega

lemma coef_eq (ℓ : Fin N → ℕ) (H : Fin N → ℝ) (U : Finset (Fin N)) {α : ℝ} (hα0 : 0 < α) :
    ∑ i ∈ U, α ^ ℓ i * net.h H i * (α ^ TT net ℓ i / (1 - α)) =
      α ^ cc net ℓ / (1 - α) * ∑ k ∈ U, net.h H k * α ^ (-(net.Ms ℓ k : ℤ)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := M_eq net ℓ i
  have h2 := M_le_cc net ℓ i
  have e : cc net ℓ = (ℓ i + TT net ℓ i) + net.Ms ℓ i := by unfold TT; omega
  have hinv : α ^ net.Ms ℓ i * (α ^ net.Ms ℓ i)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hα0.ne')
  rw [e, zpow_neg, zpow_natCast, pow_add, pow_add]
  linear_combination (-(α ^ ℓ i * α ^ TT net ℓ i * net.h H i * (1 - α)⁻¹)) * hinv

/-! ## S6: real-analysis helpers -/

lemma summable_ev_const {x : ℕ → ℝ} {D : ℕ} (hx : ∀ n, D ≤ n → x n = x D) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) : Summable (fun n => β ^ n * x n) := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_left (∑ m ∈ Finset.range (D + 1), |x m|))
    fun n => ?_
  have hb : |x n| ≤ ∑ m ∈ Finset.range (D + 1), |x m| := by
    rcases le_or_gt D n with h | h
    · rw [hx n h]
      exact Finset.single_le_sum (f := fun m => |x m|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (Nat.lt_succ_self D))
    · exact Finset.single_le_sum (f := fun m => |x m|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega))
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 n)]
  exact (mul_le_mul_of_nonneg_left hb (pow_nonneg hβ0 n)).trans_eq (mul_comm _ _)

lemma tsum_ev_const {x : ℕ → ℝ} {D : ℕ} (hx : ∀ n, D ≤ n → x n = x D) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∑' n, β ^ n * x n = ∑ n ∈ Finset.range D, β ^ n * x n + β ^ D * x D / (1 - β) := by
  have hs := summable_ev_const hx hβ0 hβ1
  have h1 : ∑ n ∈ Finset.range D, β ^ n * x n + ∑' n, β ^ (n + D) * x (n + D) =
      ∑' n, β ^ n * x n := hs.sum_add_tsum_nat_add D
  have e : ∑' n, β ^ (n + D) * x (n + D) = β ^ D * x D / (1 - β) := by
    have e' : (fun n => β ^ (n + D) * x (n + D)) = fun n => β ^ D * x D * β ^ n := by
      funext n; rw [hx (n + D) (Nat.le_add_left _ _), pow_add]; ring
    rw [e', tsum_mul_left, tsum_geometric_of_lt_one hβ0 hβ1, div_eq_mul_inv]
  rw [← h1, e]

lemma tsum_ind {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (T : ℕ) :
    ∑' n, β ^ n * (if T ≤ n then (1 : ℝ) else 0) = β ^ T / (1 - β) := by
  have h := tsum_ev_const (x := fun n => if T ≤ n then (1 : ℝ) else 0) (D := T)
    (fun n hn => by simp [hn]) hβ0 hβ1
  beta_reduce at h
  rw [h, Finset.sum_eq_zero fun n hn => by
    rw [if_neg (by have := Finset.mem_range.1 hn; omega)]; ring]
  simp

lemma tsum_w {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (U : Finset (Fin N)) (T : Fin N → ℕ)
    (a : Fin N → ℝ) :
    ∑' n, β ^ n * ∑ i ∈ U, a i * (if T i ≤ n then (1 : ℝ) else 0) =
      ∑ i ∈ U, a i * (β ^ T i / (1 - β)) := by
  have hs : ∀ i ∈ U, Summable (fun n => β ^ n * (a i * (if T i ≤ n then (1 : ℝ) else 0))) :=
    fun i _ => summable_ev_const (x := fun n => a i * (if T i ≤ n then (1 : ℝ) else 0))
      (D := T i) (fun n hn => by simp [hn]) hβ0 hβ1
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum hs]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← tsum_ind hβ0 hβ1 (T i), ← tsum_mul_left]
  congr 1; funext n; ring

lemma exists_delta {f : ℝ → ℝ} {a q K : ℝ} (hq : q < 0) (hf : ∀ δ, 0 ≤ δ → f δ ≤ a + δ * q) :
    ∃ δ, 0 ≤ δ ∧ f δ < K := by
  refine ⟨max 0 ((a - K + 1) / (-q)), le_max_left _ _, ?_⟩
  have h2 : (a - K + 1) / (-q) ≤ max 0 ((a - K + 1) / (-q)) := le_max_right _ _
  rw [div_le_iff₀ (by linarith)] at h2
  have h3 := hf _ (le_max_left 0 ((a - K + 1) / (-q)))
  nlinarith

noncomputable def abelF (D : ℕ) (E : ℕ → ℝ → ℝ) (S : ℝ → ℝ) (β : ℝ) : ℝ :=
  (1 - β) / β * ∑ n ∈ Finset.range D, β ^ n * E n β + β ^ D * E D β / β - S β / β

lemma abel_real (D : ℕ) (E : ℕ → ℝ → ℝ) (hE : ∀ n, Continuous (E n))
    (hED : ∀ n β, D ≤ n → E n β = E D β) (S : ℝ → ℝ) (hS : Continuous S) (K : ℝ → ℝ)
    (hK : ∀ β, β < 1 → K β = -S β / (1 - β)) :
    Tendsto (fun β => (1 - β) / β * ((∑' n, β ^ n * E n β) + K β)) (𝓝[<] 1)
      (𝓝 (E D 1 - S 1)) := by
  have hF : ContinuousAt (abelF D E S) 1 := by
    unfold abelF
    have hid : ContinuousAt (fun β : ℝ => β) 1 := continuousAt_id
    exact ((((continuousAt_const.sub hid).div hid one_ne_zero).mul
      (continuous_finset_sum _ fun n _ => (continuous_pow n).mul (hE n)).continuousAt).add
      ((((continuous_pow D).mul (hE D)).continuousAt).div hid one_ne_zero)).sub
      ((hS.continuousAt).div hid one_ne_zero)
  have hF1 : abelF D E S 1 = E D 1 - S 1 := by simp [abelF]
  rw [← hF1]
  refine (hF.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with β hβ
  obtain ⟨hβ0, hβ1⟩ := hβ
  have h1 : (1 : ℝ) - β ≠ 0 := by intro h; linarith
  have h0 : β ≠ 0 := hβ0.ne'
  have ht := tsum_ev_const (x := fun n => E n β) (D := D) (fun n hn => hED n β hn) hβ0.le hβ1
  beta_reduce at ht
  rw [ht, hK β hβ1]
  unfold abelF
  field_simp
  ring

/-! ## S7: costs of the closed-form policies -/

section Cost
variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

local instance instPathProb : IsProbabilityMeasure (pathMeasure μ) := by
  unfold pathMeasure; infer_instance

noncomputable def Phi [NeZero N] (ℓ : Fin N → ℕ) (H : Fin N → ℝ) (p : ℝ) (μ : Measure ℝ) (β : ℝ)
    (y : Fin N → ℝ) : ℝ :=
  ∑ i, β ^ ℓ i * net.h H i * y i + β ^ ℓ 0 * (p + H 0) * backlogG μ (ℓ 0) (y 0)

lemma periodCost_eq [NeZero N] (ℓ : Fin N → ℕ) (H : Fin N → ℝ) (p : ℝ) (Yh : ℤ → Fin N → ℝ)
    (P : ℕ → (ℕ → ℝ) → Fin N → ℝ) (β : ℝ) (ω : ℕ → ℝ) (n : ℕ) :
    periodCost net ℓ H p μ Yh P β ω ((n : ℤ) + 1) = Phi net ℓ H p μ β (P n ω) := by
  simp only [periodCost, Phi, Ypath_succ]

lemma Phi_cont [NeZero N] (hμi : Integrable (fun x => x) μ) (ℓ : Fin N → ℕ) (H : Fin N → ℝ)
    (p β : ℝ) : Continuous (Phi net ℓ H p μ β) := by
  unfold Phi
  exact (continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_apply i)).add
    (continuous_const.mul ((G_cont hμi _).comp (continuous_apply 0)))

lemma pol_delta (Yh : ℤ → Fin N → ℝ) (ξh : ℤ → ℝ) (ℓ : Fin N → ℕ) (U : Finset (Fin N))
    (T : Fin N → ℕ) (δ : ℝ) (n : ℕ) (ω : ℕ → ℝ) (i : Fin N) :
    pol Yh ξh ℓ U T δ n ω i = pol Yh ξh ℓ U T 0 n ω i + shf U T δ n i := by
  simp only [pol, shf]; split_ifs <;> ring

lemma shf_sum (a : Fin N → ℝ) (U : Finset (Fin N)) (T : Fin N → ℕ) (δ : ℝ) (n : ℕ) :
    ∑ i, a i * shf U T δ n i = δ * ∑ i ∈ U, a i * (if T i ≤ n then (1 : ℝ) else 0) := by
  have e : ∀ i, a i * shf U T δ n i =
      if i ∈ U then δ * (a i * (if T i ≤ n then (1 : ℝ) else 0)) else 0 := by
    intro i; unfold shf
    by_cases hi : i ∈ U <;> by_cases ht : T i ≤ n <;>
      simp only [hi, ht, and_self, and_false, false_and, true_and, and_true, ↓reduceIte,
        mul_one, mul_zero] <;> ring
  rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]

lemma pol_tail (Yh : ℤ → Fin N → ℝ) (ξh : ℤ → ℝ) (ℓ : Fin N → ℕ) (U : Finset (Fin N))
    (T : Fin N → ℕ) (δ : ℝ) (n : ℕ) (ω : ℕ → ℝ) (hω : ∀ r, 0 ≤ ω r) (j : Fin N)
    (hn : dd ℓ j ≤ n) :
    pol Yh ξh ℓ U T δ n ω j = Yh 0 j - ξh 0 -
      ∑ x ∈ Finset.range (dd ℓ j), ω (n - dd ℓ j + x) + shf U T δ n j := by
  unfold pol
  have e1 : ∑ r ∈ Finset.range (n - dd ℓ j), max (ω r) 0 = ∑ r ∈ Finset.range (n - dd ℓ j), ω r :=
    Finset.sum_congr rfl fun r _ => max_eq_left (hω r)
  have e2 := Finset.sum_range_add (fun r => ω r) (n - dd ℓ j) (dd ℓ j)
  rw [Nat.sub_add_cancel hn] at e2
  rw [e1, e2]; ring

lemma shf_stable {U : Finset (Fin N)} {T : Fin N → ℕ} {δ : ℝ} {j : Fin N} {D n : ℕ}
    (hT : T j ≤ D) (hn : D ≤ n) : shf U T δ n j = shf U T δ D j := by
  unfold shf
  have h1 : T j ≤ n := hT.trans hn
  simp only [h1, hT, and_true]

lemma pol_shift (Yh : ℤ → Fin N → ℝ) (ξh : ℤ → ℝ) (ℓ : Fin N → ℕ) (U : Finset (Fin N))
    (T : Fin N → ℕ) (δ : ℝ) {D : ℕ} (hD : ∀ j, dd ℓ j ≤ D ∧ T j ≤ D) (m : ℕ) (ω : ℕ → ℝ)
    (hω : ∀ r, 0 ≤ ω r) :
    pol Yh ξh ℓ U T δ (D + m) ω = pol Yh ξh ℓ U T δ D (fun r => ω (r + m)) := by
  funext j
  have hj := (hD j).1
  rw [pol_tail Yh ξh ℓ U T δ (D + m) ω hω j (by omega),
    pol_tail Yh ξh ℓ U T δ D _ (fun r => hω _) j hj,
    shf_stable (hD j).2 (Nat.le_add_right D m)]
  simp only [add_left_inj, sub_right_inj]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1; omega

lemma integral_shift_eq (hμ0 : μ (Set.Iio 0) = 0) (Yh : ℤ → Fin N → ℝ) (ξh : ℤ → ℝ)
    (ℓ : Fin N → ℕ) (U : Finset (Fin N)) (T : Fin N → ℕ) (δ : ℝ) {D : ℕ}
    (hD : ∀ j, dd ℓ j ≤ D ∧ T j ≤ D) (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) {n : ℕ}
    (hn : D ≤ n) :
    ∫ ω, F (pol Yh ξh ℓ U T δ n ω) ∂(pathMeasure μ) =
      ∫ ω, F (pol Yh ξh ℓ U T δ D ω) ∂(pathMeasure μ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hpm : Measurable (fun ω : ℕ → ℝ => pol Yh ξh ℓ U T δ D ω) :=
    measurable_pi_lambda _ fun j => (isPolicy_pol Yh ξh ℓ U T δ).2 D j
  have h := shift_mp (μ := μ) m
  calc ∫ ω, F (pol Yh ξh ℓ U T δ (D + m) ω) ∂(pathMeasure μ)
      = ∫ ω, F (pol Yh ξh ℓ U T δ D (fun r => ω (r + m))) ∂(pathMeasure μ) := by
        refine integral_congr_ae ?_
        filter_upwards [ae_path_nonneg hμ0] with ω hω
        rw [pol_shift Yh ξh ℓ U T δ hD m ω hω]
    _ = ∫ ω, F (pol Yh ξh ℓ U T δ D ω) ∂(pathMeasure μ) := by
        conv_rhs => rw [← h.map_eq]
        exact (integral_map (f := fun ω => F (pol Yh ξh ℓ U T δ D ω)) h.measurable.aemeasurable
          (hF.comp hpm).aestronglyMeasurable).symm

lemma integrable_pol (hμi : Integrable (fun x => x) μ) (Yh : ℤ → Fin N → ℝ) (ξh : ℤ → ℝ)
    (ℓ : Fin N → ℕ) (U : Finset (Fin N)) (T : Fin N → ℕ) (δ : ℝ) (n : ℕ) (j : Fin N) :
    Integrable (fun ω => pol Yh ξh ℓ U T δ n ω j) (pathMeasure μ) := by
  unfold pol
  exact (((integrable_const _).sub
    (integrable_finset_sum _ fun r _ => integrable_path_coord hμi r)).add
    (integrable_finset_sum _ fun r _ => (integrable_path_coord hμi r).sup (integrable_const 0))).add
    (integrable_const _)

lemma integrable_G_pol (hμi : Integrable (fun x => x) μ) (Yh : ℤ → Fin N → ℝ) (ξh : ℤ → ℝ)
    (ℓ : Fin N → ℕ) (U : Finset (Fin N)) (T : Fin N → ℕ) (δ : ℝ) (n m : ℕ) (j : Fin N) :
    Integrable (fun ω => backlogG μ m (pol Yh ξh ℓ U T δ n ω j)) (pathMeasure μ) := by
  refine Integrable.mono' ((integrable_const (backlogG μ m 0)).add
    (integrable_pol hμi Yh ξh ℓ U T δ n j).abs)
    ((G_cont hμi m).measurable.comp ((isPolicy_pol Yh ξh ℓ U T δ).2 n j)).aestronglyMeasurable ?_
  refine ae_of_all _ fun ω => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (G_nonneg (μ := μ) m _)]
  exact G_le hμi m _

lemma integrable_Phi_pol [NeZero N] (hμi : Integrable (fun x => x) μ) (H : Fin N → ℝ) (p β : ℝ)
    (Yh : ℤ → Fin N → ℝ) (ξh : ℤ → ℝ) (ℓ : Fin N → ℕ) (U : Finset (Fin N)) (T : Fin N → ℕ)
    (δ : ℝ) (n : ℕ) :
    Integrable (fun ω => Phi net ℓ H p μ β (pol Yh ξh ℓ U T δ n ω)) (pathMeasure μ) := by
  unfold Phi
  exact (integrable_finset_sum _ fun i _ => (integrable_pol hμi Yh ξh ℓ U T δ n i).const_mul _).add
    ((integrable_G_pol hμi Yh ξh ℓ U T δ n (ℓ 0) 0).const_mul _)

lemma integral_Phi_pol [NeZero N] (hμi : Integrable (fun x => x) μ) (H : Fin N → ℝ) (p β : ℝ)
    (Yh : ℤ → Fin N → ℝ) (ξh : ℤ → ℝ) (ℓ : Fin N → ℕ) (U : Finset (Fin N)) (T : Fin N → ℕ)
    (δ : ℝ) (n : ℕ) :
    ∫ ω, Phi net ℓ H p μ β (pol Yh ξh ℓ U T δ n ω) ∂(pathMeasure μ) =
      ∑ i, β ^ ℓ i * net.h H i * ∫ ω, pol Yh ξh ℓ U T δ n ω i ∂(pathMeasure μ) +
      β ^ ℓ 0 * (p + H 0) * ∫ ω, backlogG μ (ℓ 0) (pol Yh ξh ℓ U T δ n ω 0) ∂(pathMeasure μ) := by
  unfold Phi
  rw [integral_add (integrable_finset_sum _ fun i _ =>
      (integrable_pol hμi Yh ξh ℓ U T δ n i).const_mul _)
      ((integrable_G_pol hμi Yh ξh ℓ U T δ n (ℓ 0) 0).const_mul _),
    integral_finset_sum _ fun i _ => (integrable_pol hμi Yh ξh ℓ U T δ n i).const_mul _]
  simp only [integral_const_mul]

lemma Phi_cmp [NeZero N] (hμi : Integrable (fun x => x) μ) (H : Fin N → ℝ) (p β : ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) (Yh : ℤ → Fin N → ℝ) (ξh : ℤ → ℝ) (ℓ : Fin N → ℕ) (U : Finset (Fin N))
    (T : Fin N → ℕ) (n : ℕ) (ω : ℕ → ℝ) :
    Phi net ℓ H p μ β (pol Yh ξh ℓ U T δ n ω) ≤ Phi net ℓ H p μ β (pol Yh ξh ℓ U T 0 n ω) +
      |β ^ ℓ 0 * (p + H 0)| * backlogG μ (ℓ 0) (pol Yh ξh ℓ U T 0 n ω 0) +
      δ * ∑ i ∈ U, β ^ ℓ i * net.h H i * (if T i ≤ n then (1 : ℝ) else 0) := by
  have hs := shf_sum (fun i => β ^ ℓ i * net.h H i) U T δ n
  beta_reduce at hs
  have hlin : ∑ i, β ^ ℓ i * net.h H i * pol Yh ξh ℓ U T δ n ω i =
      ∑ i, β ^ ℓ i * net.h H i * pol Yh ξh ℓ U T 0 n ω i +
        δ * ∑ i ∈ U, β ^ ℓ i * net.h H i * (if T i ≤ n then (1 : ℝ) else 0) := by
    rw [← hs, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [pol_delta Yh ξh ℓ U T δ n ω i]; ring
  have hG0 := G_nonneg (μ := μ) (ℓ 0) (pol Yh ξh ℓ U T δ n ω 0)
  have hG1 : backlogG μ (ℓ 0) (pol Yh ξh ℓ U T δ n ω 0) ≤
      backlogG μ (ℓ 0) (pol Yh ξh ℓ U T 0 n ω 0) :=
    G_anti hμi _ (by
      rw [pol_delta Yh ξh ℓ U T δ n ω 0]
      linarith [shf_nonneg (U := U) (T := T) hδ n 0])
  have hG2 := G_nonneg (μ := μ) (ℓ 0) (pol Yh ξh ℓ U T 0 n ω 0)
  have hc : β ^ ℓ 0 * (p + H 0) * backlogG μ (ℓ 0) (pol Yh ξh ℓ U T δ n ω 0) ≤
      β ^ ℓ 0 * (p + H 0) * backlogG μ (ℓ 0) (pol Yh ξh ℓ U T 0 n ω 0) +
      |β ^ ℓ 0 * (p + H 0)| * backlogG μ (ℓ 0) (pol Yh ξh ℓ U T 0 n ω 0) := by
    rcases le_or_gt 0 (β ^ ℓ 0 * (p + H 0)) with h | h
    · have := mul_le_mul_of_nonneg_left hG1 h
      nlinarith [abs_nonneg (β ^ ℓ 0 * (p + H 0))]
    · rw [abs_of_neg h]
      nlinarith
  unfold Phi
  linarith

lemma int_cmp [NeZero N] (hμi : Integrable (fun x => x) μ) (H : Fin N → ℝ) (p β : ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) (Yh : ℤ → Fin N → ℝ) (ξh : ℤ → ℝ) (ℓ : Fin N → ℕ) (U : Finset (Fin N))
    (T : Fin N → ℕ) (n : ℕ) :
    ∫ ω, Phi net ℓ H p μ β (pol Yh ξh ℓ U T δ n ω) ∂(pathMeasure μ) ≤
      ∫ ω, Phi net ℓ H p μ β (pol Yh ξh ℓ U T 0 n ω) ∂(pathMeasure μ) +
      |β ^ ℓ 0 * (p + H 0)| * ∫ ω, backlogG μ (ℓ 0) (pol Yh ξh ℓ U T 0 n ω 0) ∂(pathMeasure μ) +
      δ * ∑ i ∈ U, β ^ ℓ i * net.h H i * (if T i ≤ n then (1 : ℝ) else 0) := by
  have hA := integrable_Phi_pol net hμi H p β Yh ξh ℓ U T 0 n
  have hB := (integrable_G_pol hμi Yh ξh ℓ U T 0 n (ℓ 0) 0).const_mul |β ^ ℓ 0 * (p + H 0)|
  have hAB : Integrable (fun ω => Phi net ℓ H p μ β (pol Yh ξh ℓ U T 0 n ω) +
      |β ^ ℓ 0 * (p + H 0)| * backlogG μ (ℓ 0) (pol Yh ξh ℓ U T 0 n ω 0)) (pathMeasure μ) :=
    hA.add hB
  calc _ ≤ ∫ ω, (Phi net ℓ H p μ β (pol Yh ξh ℓ U T 0 n ω) +
        |β ^ ℓ 0 * (p + H 0)| * backlogG μ (ℓ 0) (pol Yh ξh ℓ U T 0 n ω 0) +
        δ * ∑ i ∈ U, β ^ ℓ i * net.h H i * (if T i ≤ n then (1 : ℝ) else 0)) ∂(pathMeasure μ) :=
        integral_mono (integrable_Phi_pol net hμi H p β Yh ξh ℓ U T δ n)
          (hAB.add (integrable_const _))
          (fun ω => Phi_cmp net hμi H p β hδ Yh ξh ℓ U T n ω)
    _ = _ := by
        rw [integral_add hAB (integrable_const _), integral_add hA hB, integral_const_mul,
          integral_const]
        simp

lemma adm [NeZero N] (hμ0 : μ (Set.Iio 0) = 0) (hμi : Integrable (fun x => x) μ)
    (H : Fin N → ℝ) (p : ℝ) (Yh : ℤ → Fin N → ℝ) (ξh : ℤ → ℝ) (ℓ : Fin N → ℕ)
    (U : Finset (Fin N)) (T : Fin N → ℕ) (δ : ℝ) {D : ℕ} (hD : ∀ j, dd ℓ j ≤ D ∧ T j ≤ D)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Admissible net ℓ H p μ Yh (pol Yh ξh ℓ U T δ) β := by
  refine ⟨fun n => ?_, ?_⟩
  · simp only [periodCost_eq]
    exact integrable_Phi_pol net hμi H p β Yh ξh ℓ U T δ n
  · simp only [periodCost_eq]
    exact summable_ev_const
      (x := fun n => ∫ ω, |Phi net ℓ H p μ β (pol Yh ξh ℓ U T δ n ω)| ∂(pathMeasure μ))
      (fun n hn => integral_shift_eq hμ0 Yh ξh ℓ U T δ hD
        (fun y => |Phi net ℓ H p μ β y|) (Phi_cont net hμi ℓ H p β).abs.measurable hn) hβ0 hβ1

lemma disc_cmp [NeZero N] (hμ0 : μ (Set.Iio 0) = 0) (hμi : Integrable (fun x => x) μ)
    (H : Fin N → ℝ) (p : ℝ) (Yh : ℤ → Fin N → ℝ) (ξh : ℤ → ℝ) (ℓ : Fin N → ℕ)
    (U : Finset (Fin N)) (T : Fin N → ℕ) {D : ℕ} (hD : ∀ j, dd ℓ j ≤ D ∧ T j ≤ D)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (δ : ℝ) (hδ : 0 ≤ δ) :
    discCost net ℓ H p μ Yh (pol Yh ξh ℓ U T δ) β ≤
      (discCost net ℓ H p μ Yh (pol Yh ξh ℓ U T 0) β +
        |β ^ ℓ 0 * (p + H 0)| *
          ∑' n, β ^ n * ∫ ω, backlogG μ (ℓ 0) (pol Yh ξh ℓ U T 0 n ω 0) ∂(pathMeasure μ)) +
      δ * ∑ i ∈ U, β ^ ℓ i * net.h H i * (β ^ T i / (1 - β)) := by
  simp only [discCost, periodCost_eq]
  have ev : ∀ (δ' : ℝ) (F : (Fin N → ℝ) → ℝ), Measurable F → ∀ n, D ≤ n →
      ∫ ω, F (pol Yh ξh ℓ U T δ' n ω) ∂(pathMeasure μ) =
        ∫ ω, F (pol Yh ξh ℓ U T δ' D ω) ∂(pathMeasure μ) :=
    fun δ' F hF n hn => integral_shift_eq hμ0 Yh ξh ℓ U T δ' hD F hF hn
  have hPm := (Phi_cont net hμi ℓ H p β).measurable
  have hGm : Measurable (fun y : Fin N → ℝ => backlogG μ (ℓ 0) (y 0)) :=
    (G_cont hμi _).measurable.comp (measurable_pi_apply 0)
  have S1 := summable_ev_const
    (x := fun n => ∫ ω, Phi net ℓ H p μ β (pol Yh ξh ℓ U T δ n ω) ∂(pathMeasure μ))
    (ev δ _ hPm) hβ0 hβ1
  have S2 := summable_ev_const
    (x := fun n => ∫ ω, Phi net ℓ H p μ β (pol Yh ξh ℓ U T 0 n ω) ∂(pathMeasure μ))
    (ev 0 _ hPm) hβ0 hβ1
  have S3 := summable_ev_const
    (x := fun n => ∫ ω, backlogG μ (ℓ 0) (pol Yh ξh ℓ U T 0 n ω 0) ∂(pathMeasure μ))
    (ev 0 _ hGm) hβ0 hβ1
  have S4 := summable_ev_const
    (x := fun n => ∑ i ∈ U, β ^ ℓ i * net.h H i * (if T i ≤ n then (1 : ℝ) else 0)) (D := D)
    (fun n hn => Finset.sum_congr rfl fun i _ => by
      rw [if_pos ((hD i).2.trans hn), if_pos (hD i).2]) hβ0 hβ1
  have hw := tsum_w hβ0 hβ1 U T (fun i => β ^ ℓ i * net.h H i)
  beta_reduce at hw S1 S2 S3 S4
  rw [← hw]
  have hle := Summable.tsum_le_tsum (fun n => by
      nlinarith [mul_le_mul_of_nonneg_left (int_cmp net hμi H p β hδ Yh ξh ℓ U T n)
        (pow_nonneg hβ0 n)]) S1
    ((S2.add (S3.mul_left |β ^ ℓ 0 * (p + H 0)|)).add (S4.mul_left δ))
  rw [Summable.tsum_add (S2.add (S3.mul_left _)) (S4.mul_left _),
    Summable.tsum_add S2 (S3.mul_left _), tsum_mul_left, tsum_mul_left] at hle
  linarith

lemma abel_pol [NeZero N] (hμ0 : μ (Set.Iio 0) = 0) (hμi : Integrable (fun x => x) μ)
    (H : Fin N → ℝ) (p : ℝ) (Yh : ℤ → Fin N → ℝ) (ξh : ℤ → ℝ) (ℓ : Fin N → ℕ)
    (U : Finset (Fin N)) (T : Fin N → ℕ) (δ : ℝ) {D : ℕ} (hD : ∀ j, dd ℓ j ≤ D ∧ T j ≤ D) :
    Tendsto (fun β => (1 - β) / β * discCost net ℓ H p μ Yh (pol Yh ξh ℓ U T δ) β) (𝓝[<] 1)
      (𝓝 (∫ ω, Phi net ℓ H p μ 1 (pol Yh ξh ℓ U T δ D ω) ∂(pathMeasure μ) -
        ∑ i, net.h H i * (∫ x, x ∂μ) * ((ℓ i : ℝ) + 1) * (1 : ℝ) ^ ℓ i)) := by
  have he : ∀ n, D ≤ n → ∀ i, ∫ ω, pol Yh ξh ℓ U T δ n ω i ∂(pathMeasure μ) =
      ∫ ω, pol Yh ξh ℓ U T δ D ω i ∂(pathMeasure μ) := fun n hn i =>
    integral_shift_eq hμ0 Yh ξh ℓ U T δ hD (fun y => y i) (measurable_pi_apply i) hn
  have hg : ∀ n, D ≤ n → ∫ ω, backlogG μ (ℓ 0) (pol Yh ξh ℓ U T δ n ω 0) ∂(pathMeasure μ) =
      ∫ ω, backlogG μ (ℓ 0) (pol Yh ξh ℓ U T δ D ω 0) ∂(pathMeasure μ) := fun n hn =>
    integral_shift_eq hμ0 Yh ξh ℓ U T δ hD (fun y => backlogG μ (ℓ 0) (y 0))
      ((G_cont hμi _).measurable.comp (measurable_pi_apply 0)) hn
  have key := abel_real D
    (fun n β => ∑ i, β ^ ℓ i * net.h H i * ∫ ω, pol Yh ξh ℓ U T δ n ω i ∂(pathMeasure μ) +
      β ^ ℓ 0 * (p + H 0) * ∫ ω, backlogG μ (ℓ 0) (pol Yh ξh ℓ U T δ n ω 0) ∂(pathMeasure μ))
    (fun n => (continuous_finset_sum _ fun i _ =>
        ((continuous_pow _).mul continuous_const).mul continuous_const).add
      (((continuous_pow _).mul continuous_const).mul continuous_const))
    (fun n β hn => by
      simp only [he n hn, hg n hn])
    (fun β => ∑ i, net.h H i * (∫ x, x ∂μ) * ((ℓ i : ℝ) + 1) * β ^ ℓ i)
    (continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_pow _))
    (K4 net ℓ H μ) (fun β _ => by beta_reduce; rw [K4, neg_div, Finset.sum_div])
  beta_reduce at key
  rw [← integral_Phi_pol net hμi H p 1 Yh ξh ℓ U T δ D] at key
  refine key.congr' (Eventually.of_forall fun β => ?_)
  simp only [discCost, periodCost_eq, integral_Phi_pol net hμi H p β Yh ξh ℓ U T δ]

lemma avg_cmp [NeZero N] (hμi : Integrable (fun x => x) μ) (H : Fin N → ℝ) (p : ℝ)
    (Yh : ℤ → Fin N → ℝ) (ξh : ℤ → ℝ) (ℓ : Fin N → ℕ) (U : Finset (Fin N)) (T : Fin N → ℕ)
    {D : ℕ} (hD : ∀ j, dd ℓ j ≤ D ∧ T j ≤ D) (S : ℝ) :
    ∀ δ : ℝ, 0 ≤ δ → ∫ ω, Phi net ℓ H p μ 1 (pol Yh ξh ℓ U T δ D ω) ∂(pathMeasure μ) - S ≤
      (∫ ω, Phi net ℓ H p μ 1 (pol Yh ξh ℓ U T 0 D ω) ∂(pathMeasure μ) +
        |(1 : ℝ) ^ ℓ 0 * (p + H 0)| *
          ∫ ω, backlogG μ (ℓ 0) (pol Yh ξh ℓ U T 0 D ω 0) ∂(pathMeasure μ) - S) +
      δ * ∑ k ∈ U, net.h H k * (1 : ℝ) ^ (-(net.Ms ℓ k : ℤ)) := by
  intro δ hδ
  have h := int_cmp net hμi H p 1 hδ Yh ξh ℓ U T D
  have hw : ∑ i ∈ U, (1 : ℝ) ^ ℓ i * net.h H i * (if T i ≤ D then (1 : ℝ) else 0) =
      ∑ k ∈ U, net.h H k * (1 : ℝ) ^ (-(net.Ms ℓ k : ℤ)) :=
    Finset.sum_congr rfl fun i _ => by rw [if_pos (hD i).2]; simp
  rw [hw] at h
  linarith

theorem main [NeZero N] (ℓ : Fin N → ℕ) (H : Fin N → ℝ) (p α : ℝ) (hα : 0 < α ∧ α ≤ 1)
    (hμ0 : μ (Set.Iio 0) = 0) (hμi : Integrable (fun x => x) μ)
    (Yh : ℤ → Fin N → ℝ) (ξh : ℤ → ℝ) (hHist : HistOK net ℓ Yh ξh) (U : Finset (Fin N))
    (hU : ∀ j k, k ∈ net.P j → j ∈ U → k ∈ U ∧ TT net ℓ k + ℓ k ≤ TT net ℓ j)
    {D : ℕ} (hD : ∀ j, dd ℓ j ≤ D ∧ TT net ℓ j ≤ D)
    (hcond : ∑ k ∈ U, net.h H k * α ^ (-(net.Ms ℓ k : ℤ)) < 0) (K : ℝ) :
    ∃ P : ℕ → (ℕ → ℝ) → Fin N → ℝ, IsPolicy P ∧ Feasible net ℓ Yh ξh P ∧
      CostBelow net ℓ H p μ Yh α P K := by
  by_cases hα1 : α < 1
  · have hα0 : 0 < α := hα.1
    have hQ : ∑ i ∈ U, α ^ ℓ i * net.h H i * (α ^ TT net ℓ i / (1 - α)) < 0 := by
      rw [coef_eq net ℓ H U hα0]
      exact mul_neg_of_pos_of_neg (div_pos (pow_pos hα0 _) (by linarith)) hcond
    obtain ⟨δ, hδ0, hδK⟩ := exists_delta (K := K) hQ
      (disc_cmp net hμ0 hμi H p Yh ξh ℓ U (TT net ℓ) hD hα0.le hα1)
    refine ⟨pol Yh ξh ℓ U (TT net ℓ) δ, isPolicy_pol _ _ _ _ _ _,
      feasible_pol net hHist hδ0 hU, ?_⟩
    rw [CostBelow, if_pos hα1]
    exact ⟨adm net hμ0 hμi H p Yh ξh ℓ U (TT net ℓ) δ hD hα0.le hα1, hδK⟩
  · have hα' : α = 1 := le_antisymm hα.2 (not_lt.1 hα1)
    subst hα'
    obtain ⟨δ, hδ0, hδK⟩ := exists_delta (K := K) hcond
      (avg_cmp net hμi H p Yh ξh ℓ U (TT net ℓ) hD
        (∑ i, net.h H i * (∫ x, x ∂μ) * ((ℓ i : ℝ) + 1) * (1 : ℝ) ^ ℓ i))
    refine ⟨pol Yh ξh ℓ U (TT net ℓ) δ, isPolicy_pol _ _ _ _ _ _,
      feasible_pol net hHist hδ0 hU, ?_⟩
    rw [CostBelow, if_neg (lt_irrefl _)]
    exact ⟨_, fun β hβ => adm net hμ0 hμi H p Yh ξh ℓ U (TT net ℓ) δ hD hβ.1.le hβ.2,
      abel_pol net hμ0 hμi H p Yh ξh ℓ U (TT net ℓ) δ hD, hδK⟩

end Cost

end R5f
end RoslingAssembly

open MeasureTheory RoslingAssembly in
theorem solution {N : ℕ} [NeZero N] (net : Network N) (ℓ : Fin N → ℕ) (H : Fin N → ℝ)
    (p : ℝ) (α : ℝ) (hα : 0 < α ∧ α ≤ 1) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hμac : μ ≪ volume) (hμi : Integrable (fun x => x) μ)
    (hlam : 0 < ∫ x, x ∂μ) (Yh : ℤ → Fin N → ℝ) (ξh : ℤ → ℝ) (hξh : ∀ t ≤ 0, 0 ≤ ξh t)
    (hHist : HistOK net ℓ Yh ξh)
    (hcond : ∃ i : Fin N, net.h H i * α ^ (-(net.Ms ℓ i : ℤ)) +
      ∑ k ∈ net.B i, net.h H k * α ^ (-(net.Ms ℓ k : ℤ)) < 0) :
    ∀ K : ℝ, ∃ pol : ℕ → (ℕ → ℝ) → Fin N → ℝ, IsPolicy pol ∧ Feasible net ℓ Yh ξh pol ∧
      CostBelow net ℓ H p μ Yh α pol K := by
  intro K
  obtain ⟨i0, hi0⟩ := hcond
  rw [R5f.cond_sum] at hi0
  exact R5f.main net ℓ H p α hα hμ0 hμi Yh ξh hHist _ (R5f.hU_main net ℓ i0)
    (R5f.hD_main net ℓ) hi0 K
