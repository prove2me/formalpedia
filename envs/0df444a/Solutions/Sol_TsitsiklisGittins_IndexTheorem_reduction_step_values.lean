-- Prove2me | solution 1 for TsitsiklisGittins.IndexTheorem.reduction_step_values
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T01:34:09.593224+00:00
-- url     : https://prove2.me/submissions/5a455fc8-4697-4852-926b-f1bee7f1bc77

import Mathlib
import Definitions.Def_TsitsiklisGittins_IndexTheorem_Reduction



namespace TsitsiklisGittins.IndexTheorem

open MeasureTheory

namespace Stage

variable {n : ℕ} {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

/-- one-play operator for bandit `j` -/
noncomputable def Tj (S : Stage n X) (j : Fin n) (V : JointState n X → ℝ) (z : JointState n X) : ℝ :=
  S.ρ ⟨j, z j⟩ + ∑ y : X j, S.D ⟨j, z j⟩ ⟨j, y⟩ * V (Function.update z j y)

/-- row sum of the transition data within the bandit of `q` -/
noncomputable def rs (S : Stage n X) (q : Σ i, X i) : ℝ := ∑ y : X q.1, S.D q ⟨q.1, y⟩

/-- regularity: nonnegative data and uniformly contracting row sums -/
def Reg (S : Stage n X) (κ : ℝ) : Prop :=
  (∀ q p, 0 ≤ S.D q p) ∧ 0 ≤ κ ∧ κ < 1 ∧ ∀ q, S.rs q ≤ κ

lemma Tj_sub_abs {S : Stage n X} {κ : ℝ} (hr : Reg S κ) (j : Fin n) (V W : JointState n X → ℝ)
    (M : ℝ) (hM : ∀ z, |V z - W z| ≤ M) (z : JointState n X) :
    |S.Tj j V z - S.Tj j W z| ≤ κ * M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (Classical.choice ⟨z⟩))
  unfold Tj
  have h1 : S.ρ ⟨j, z j⟩ + ∑ y : X j, S.D ⟨j, z j⟩ ⟨j, y⟩ * V (Function.update z j y) -
      (S.ρ ⟨j, z j⟩ + ∑ y : X j, S.D ⟨j, z j⟩ ⟨j, y⟩ * W (Function.update z j y)) =
      ∑ y : X j, S.D ⟨j, z j⟩ ⟨j, y⟩ * (V (Function.update z j y) - W (Function.update z j y)) := by
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun y _ => by ring)
  rw [h1]
  calc |∑ y : X j, S.D ⟨j, z j⟩ ⟨j, y⟩ * (V (Function.update z j y) - W (Function.update z j y))|
      ≤ ∑ y : X j, |S.D ⟨j, z j⟩ ⟨j, y⟩ * (V (Function.update z j y) - W (Function.update z j y))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y : X j, S.D ⟨j, z j⟩ ⟨j, y⟩ * M := by
        apply Finset.sum_le_sum
        intro y _
        rw [abs_mul, abs_of_nonneg (hr.1 _ _)]
        exact mul_le_mul_of_nonneg_left (hM _) (hr.1 _ _)
    _ = S.rs ⟨j, z j⟩ * M := by rw [← Finset.sum_mul]; rfl
    _ ≤ κ * M := mul_le_mul_of_nonneg_right (hr.2.2.2 _) hM0


noncomputable def Tpi (S : Stage n X) (π : Policy n X) (V : JointState n X → ℝ) :
    JointState n X → ℝ := fun z => S.Tj (π z) V z

lemma playValue_eq (S : Stage n X) (π : Policy n X) (k : ℕ) :
    playValue S.ρ S.D π k = (S.Tpi π)^[k] 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    funext z
    show S.Tj (π z) (playValue S.ρ S.D π k) z = S.Tj (π z) ((S.Tpi π)^[k] 0) z
    rw [ih]

lemma contracting_Tpi {S : Stage n X} {κ : ℝ} (hr : Reg S κ) (π : Policy n X) :
    ContractingWith κ.toNNReal (S.Tpi π) := by
  refine ⟨?_, LipschitzWith.of_dist_le_mul fun V W => ?_⟩
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr.2.1]; simpa using hr.2.2.1
  · rw [Real.coe_toNNReal _ hr.2.1]
    refine (dist_pi_le_iff (mul_nonneg hr.2.1 dist_nonneg)).2 fun z => ?_
    rw [Real.dist_eq]
    exact Tj_sub_abs hr (π z) V W (dist V W) (fun z => by rw [← Real.dist_eq]; exact dist_le_pi_dist V W z) z

lemma value_fixed {S : Stage n X} {κ : ℝ} (hr : Reg S κ) (π : Policy n X) :
    ∀ z, S.value π z = S.Tj (π z) (S.value π) z := by
  have hc := contracting_Tpi hr π
  have tend := hc.tendsto_iterate_fixedPoint (0 : JointState n X → ℝ)
  have hv : S.value π = ContractingWith.fixedPoint _ hc := by
    funext z
    unfold Stage.value momentValue
    simp only [playValue_eq]
    exact ((tendsto_pi_nhds.1 tend) z).limUnder_eq
  intro z
  have := congrFun (ContractingWith.fixedPoint_isFixedPt (hf := hc)) z
  rw [hv]
  exact this.symm

variable [NeZero n]

noncomputable def Tb (S : Stage n X) (V : JointState n X → ℝ) : JointState n X → ℝ :=
  fun z => Finset.univ.sup' Finset.univ_nonempty (fun j => S.Tj j V z)

lemma Tb_sub_le {S : Stage n X} {κ : ℝ} (hr : Reg S κ) (V W : JointState n X → ℝ)
    (M : ℝ) (hM : ∀ z, |V z - W z| ≤ M) (z : JointState n X) :
    S.Tb V z ≤ S.Tb W z + κ * M := by
  unfold Tb
  apply Finset.sup'_le
  intro j _
  have h1 := Tj_sub_abs hr j V W M hM z
  have h2 : S.Tj j W z ≤ Finset.univ.sup' Finset.univ_nonempty (fun j => S.Tj j W z) :=
    Finset.le_sup' (fun j => S.Tj j W z) (Finset.mem_univ j)
  linarith [(abs_le.1 h1).2]

lemma contracting_Tb {S : Stage n X} {κ : ℝ} (hr : Reg S κ) :
    ContractingWith κ.toNNReal S.Tb := by
  refine ⟨?_, LipschitzWith.of_dist_le_mul fun V W => ?_⟩
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr.2.1]; simpa using hr.2.2.1
  · rw [Real.coe_toNNReal _ hr.2.1]
    refine (dist_pi_le_iff (mul_nonneg hr.2.1 dist_nonneg)).2 fun z => ?_
    rw [Real.dist_eq, abs_le]
    have hVW : ∀ z, |V z - W z| ≤ dist V W := fun z => by rw [← Real.dist_eq]; exact dist_le_pi_dist V W z
    have hWV : ∀ z, |W z - V z| ≤ dist V W := fun z => by
      rw [abs_sub_comm]; exact hVW z
    have a1 := Tb_sub_le hr V W _ hVW z
    have a2 := Tb_sub_le hr W V _ hWV z
    constructor <;> linarith

lemma exists_vstar {S : Stage n X} {κ : ℝ} (hr : Reg S κ) : ∃ V : JointState n X → ℝ, ∀ z, V z = S.Tb V z :=
  ⟨_, fun z => (congrFun (ContractingWith.fixedPoint_isFixedPt (hf := contracting_Tb hr)) z).symm⟩

lemma Tj_sub (S : Stage n X) (j : Fin n) (V W : JointState n X → ℝ) (z : JointState n X) :
    S.Tj j V z - S.Tj j W z =
      ∑ y : X j, S.D ⟨j, z j⟩ ⟨j, y⟩ * (V (Function.update z j y) - W (Function.update z j y)) := by
  unfold Tj
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun y _ => by ring)

lemma Tj_mono {S : Stage n X} {κ : ℝ} (hr : Reg S κ) (j : Fin n) (V W : JointState n X → ℝ)
    (h : ∀ z, V z ≤ W z) (z : JointState n X) : S.Tj j V z ≤ S.Tj j W z := by
  have := Tj_sub S j V W z
  have h2 : ∑ y : X j, S.D ⟨j, z j⟩ ⟨j, y⟩ * (V (Function.update z j y) - W (Function.update z j y)) ≤ 0 :=
    Finset.sum_nonpos (fun y _ => mul_nonpos_of_nonneg_of_nonpos (hr.1 _ _) (sub_nonpos.2 (h _)))
  linarith

lemma comp_nonneg {S : Stage n X} {κ : ℝ} (hr : Reg S κ) (N : Set (JointState n X))
    (hN : ∀ z ∈ N, ∀ j y, S.D ⟨j, z j⟩ ⟨j, y⟩ ≠ 0 → Function.update z j y ∈ N)
    (E : JointState n X → ℝ) (π : Policy n X)
    (hE : ∀ z ∈ N, ∑ y : X (π z), S.D ⟨π z, z (π z)⟩ ⟨π z, y⟩ * E (Function.update z (π z) y) ≤ E z) :
    ∀ z ∈ N, 0 ≤ E z := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨z1, hz1, hneg⟩ := hcon
  obtain ⟨z0, hz0, hmin⟩ := Set.exists_min_image N E (Set.toFinite N) ⟨z1, hz1⟩
  have hm : E z0 < 0 := lt_of_le_of_lt (hmin z1 hz1) hneg
  have h1 := hE z0 hz0
  have h2 : ∑ y : X (π z0), S.D ⟨π z0, z0 (π z0)⟩ ⟨π z0, y⟩ * E z0 ≤
      ∑ y : X (π z0), S.D ⟨π z0, z0 (π z0)⟩ ⟨π z0, y⟩ * E (Function.update z0 (π z0) y) := by
    apply Finset.sum_le_sum
    intro y _
    by_cases hd : S.D ⟨π z0, z0 (π z0)⟩ ⟨π z0, y⟩ = 0
    · simp [hd]
    · exact mul_le_mul_of_nonneg_left (hmin _ (hN z0 hz0 _ y hd)) (hr.1 _ _)
  have h3 : ∑ y : X (π z0), S.D ⟨π z0, z0 (π z0)⟩ ⟨π z0, y⟩ * E z0 = S.rs ⟨π z0, z0 (π z0)⟩ * E z0 := by
    rw [← Finset.sum_mul]; rfl
  have h4 := hr.2.2.2 ⟨π z0, z0 (π z0)⟩
  have h5 := mul_le_mul_of_nonpos_right h4 hm.le
  nlinarith [mul_pos_of_neg_of_neg (sub_neg.2 hr.2.2.1) hm]

lemma comp_nonpos {S : Stage n X} {κ : ℝ} (hr : Reg S κ) (N : Set (JointState n X))
    (hN : ∀ z ∈ N, ∀ j y, S.D ⟨j, z j⟩ ⟨j, y⟩ ≠ 0 → Function.update z j y ∈ N)
    (E : JointState n X → ℝ) (π : Policy n X)
    (hE : ∀ z ∈ N, E z ≤ ∑ y : X (π z), S.D ⟨π z, z (π z)⟩ ⟨π z, y⟩ * E (Function.update z (π z) y)) :
    ∀ z ∈ N, E z ≤ 0 := by
  have := comp_nonneg hr N hN (fun z => - E z) π (fun z hz => by
    have h := hE z hz
    have : ∑ y : X (π z), S.D ⟨π z, z (π z)⟩ ⟨π z, y⟩ * (-E (Function.update z (π z) y)) =
        -∑ y : X (π z), S.D ⟨π z, z (π z)⟩ ⟨π z, y⟩ * E (Function.update z (π z) y) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun y _ => by ring)
    rw [this]; linarith)
  intro z hz
  linarith [this z hz]

noncomputable def vstar (S : Stage n X) : JointState n X → ℝ :=
  Classical.epsilon (fun V : JointState n X → ℝ => ∀ z, V z = S.Tb V z)

lemma vstar_spec {S : Stage n X} {κ : ℝ} (hr : Reg S κ) : ∀ z, S.vstar z = S.Tb S.vstar z :=
  Classical.epsilon_spec (exists_vstar hr)

lemma Tj_le_vstar {S : Stage n X} {κ : ℝ} (hr : Reg S κ) (j : Fin n) (z : JointState n X) :
    S.Tj j S.vstar z ≤ S.vstar z := by
  have h : S.Tj j S.vstar z ≤ S.Tb S.vstar z := Finset.le_sup' (fun j => S.Tj j S.vstar z) (Finset.mem_univ j)
  rwa [← vstar_spec hr z] at h

lemma exists_greedy {S : Stage n X} {κ : ℝ} (hr : Reg S κ) (z : JointState n X) :
    ∃ j, S.Tj j S.vstar z = S.vstar z := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin n)) (fun j => S.Tj j S.vstar z)
  exact ⟨j, by rw [← hj]; exact (vstar_spec hr z).symm⟩

lemma value_le_vstar {S : Stage n X} {κ : ℝ} (hr : Reg S κ) (π : Policy n X) :
    ∀ z, S.value π z ≤ S.vstar z := by
  have := comp_nonneg hr Set.univ (fun _ _ _ _ _ => Set.mem_univ _) (fun z => S.vstar z - S.value π z) π
    (fun z _ => by
      have h := Tj_sub S (π z) S.vstar (S.value π) z
      rw [← value_fixed hr π z] at h
      have := Tj_le_vstar hr (π z) z
      rw [← h] at *
      linarith [h])
  intro z; linarith [this z (Set.mem_univ _)]

lemma value_eq_of_greedy {S : Stage n X} {κ : ℝ} (hr : Reg S κ) (N : Set (JointState n X))
    (hN : ∀ z ∈ N, ∀ j y, S.D ⟨j, z j⟩ ⟨j, y⟩ ≠ 0 → Function.update z j y ∈ N)
    (π : Policy n X) (hg : ∀ z ∈ N, S.Tj (π z) S.vstar z = S.vstar z) :
    ∀ z ∈ N, S.value π z = S.vstar z := by
  have key : ∀ z ∈ N, ∑ y : X (π z), S.D ⟨π z, z (π z)⟩ ⟨π z, y⟩ *
      (S.vstar (Function.update z (π z) y) - S.value π (Function.update z (π z) y)) = S.vstar z - S.value π z := by
    intro z hz
    have h := Tj_sub S (π z) S.vstar (S.value π) z
    rw [← value_fixed hr π z, hg z hz] at h
    exact h.symm
  have a := comp_nonneg hr N hN (fun z => S.vstar z - S.value π z) π (fun z hz => (key z hz).le)
  have b := comp_nonpos hr N hN (fun z => S.vstar z - S.value π z) π (fun z hz => (key z hz).ge)
  intro z hz
  linarith [a z hz, b z hz]

lemma exists_opt {S : Stage n X} {κ : ℝ} (hr : Reg S κ) :
    ∃ π : Policy n X, ∀ z, S.value π z = S.vstar z := by
  choose π hπ using exists_greedy hr
  exact ⟨π, fun z => value_eq_of_greedy hr Set.univ (fun _ _ _ _ _ => Set.mem_univ _) π (fun z _ => hπ z) z (Set.mem_univ _)⟩

/-- the states with all components still alive -/
def Dom (S : Stage n X) : Set (JointState n X) := {z | ∀ i, (⟨i, z i⟩ : Σ i, X i) ∈ S.alive}

lemma Valid.rs_eq {β : ℝ} {S : Stage n X} (hv : S.Valid β) (q : Σ i, X i) :
    β * S.w q = 1 - S.rs q := by
  have h := hv.2.2.2.2 q
  have : ∑ p : Σ i, X i, S.D q p = S.rs q := by
    rw [Fintype.sum_sigma]
    unfold rs
    rw [Finset.sum_eq_single q.1]
    · intro i _ hi; exact Finset.sum_eq_zero (fun y _ => hv.2.2.1 q ⟨i, y⟩ (fun h => hi h.symm))
    · simp
  rw [h, this]

lemma Valid.reg {β : ℝ} [∀ i, Nonempty (X i)] {S : Stage n X} (hβ : 0 < β) (hv : S.Valid β) :
    ∃ κ, Reg S κ := by
  haveI : Nonempty (Σ i, X i) := ⟨⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩, Classical.arbitrary _⟩⟩
  obtain ⟨q0, -, hq0⟩ := Finset.exists_max_image Finset.univ (fun q => S.rs q) Finset.univ_nonempty
  have hnn : ∀ q, 0 ≤ S.rs q := fun q => Finset.sum_nonneg (fun y _ => hv.2.1 _ _)
  refine ⟨S.rs q0, hv.2.1, hnn q0, ?_, fun q => hq0 q (Finset.mem_univ _)⟩
  have := hv.rs_eq q0
  have := mul_pos hβ (hv.1 q0)
  linarith

lemma Dom_closed {β : ℝ} {S : Stage n X} (hv : S.Valid β) :
    ∀ z ∈ S.Dom, ∀ j y, S.D ⟨j, z j⟩ ⟨j, y⟩ ≠ 0 → Function.update z j y ∈ S.Dom := by
  intro z hz j y hd i
  by_cases hij : i = j
  · subst hij
    rw [Function.update_self]
    by_contra hnot
    exact hd (hv.2.2.2.1 _ _ hnot)
  · rw [Function.update_of_ne hij]; exact hz i

lemma topA {β κ : ℝ} (hβ : 0 < β) {S : Stage n X} (hv : S.Valid β) (hr : Reg S κ)
    (s : Σ i, X i) (hs : s ∈ S.alive) (hmax : ∀ q ∈ S.alive, S.rate q ≤ S.rate s) :
    ∀ z ∈ S.Dom, z s.1 = s.2 → S.Tj s.1 S.vstar z = S.vstar z := by
  let U : JointState n X → ℝ := fun z => if z s.1 = s.2 then S.Tj s.1 S.vstar z else S.vstar z
  have hUle : ∀ z, U z ≤ S.vstar z := by
    intro z; simp only [U]; split_ifs
    · exact Tj_le_vstar hr _ _
    · exact le_rfl
  have hsuper : ∀ z ∈ S.Dom, ∀ j, S.Tj j U z ≤ U z := by
    intro z hz j
    by_cases hzs : z s.1 = s.2
    · have hUz : U z = S.Tj s.1 S.vstar z := by simp only [U]; rw [if_pos hzs]
      rw [hUz]
      by_cases hj : j = s.1
      · subst hj
        exact Tj_mono hr _ U S.vstar hUle z
      · have hj' : s.1 ≠ j := fun h => hj h.symm
        -- notation
        have hsa : (⟨s.1, z s.1⟩ : Σ i, X i) ∈ S.alive := hz s.1
        have hja : (⟨j, z j⟩ : Σ i, X i) ∈ S.alive := hz j
        have hUy : ∀ y, U (Function.update z j y) = S.Tj s.1 S.vstar (Function.update z j y) := by
          intro y
          simp only [U]
          rw [if_pos (by rw [Function.update_of_ne hj']; exact hzs)]
        have E1 : S.Tj j U z = S.ρ ⟨j, z j⟩ + S.ρ ⟨s.1, z s.1⟩ * ∑ y : X j, S.D ⟨j, z j⟩ ⟨j, y⟩ +
            ∑ x : X s.1, ∑ y : X j, S.D ⟨s.1, z s.1⟩ ⟨s.1, x⟩ * S.D ⟨j, z j⟩ ⟨j, y⟩ *
              S.vstar (Function.update (Function.update z s.1 x) j y) := by
          unfold Tj
          have : ∀ y : X j, S.D ⟨j, z j⟩ ⟨j, y⟩ * U (Function.update z j y) =
              S.D ⟨j, z j⟩ ⟨j, y⟩ * S.ρ ⟨s.1, z s.1⟩ + ∑ x : X s.1, S.D ⟨s.1, z s.1⟩ ⟨s.1, x⟩ * S.D ⟨j, z j⟩ ⟨j, y⟩ *
              S.vstar (Function.update (Function.update z s.1 x) j y) := by
            intro y
            rw [hUy y]
            unfold Tj
            rw [Function.update_of_ne hj']
            simp_rw [Function.update_comm hj']
            rw [mul_add, Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl
            intros
            ring
          rw [Finset.sum_congr rfl (fun y _ => this y), Finset.sum_add_distrib, ← Finset.sum_mul,
            Finset.sum_comm]
          ring
        have E2 : ∑ x : X s.1, S.D ⟨s.1, z s.1⟩ ⟨s.1, x⟩ * S.Tj j S.vstar (Function.update z s.1 x) =
            S.ρ ⟨j, z j⟩ * ∑ x : X s.1, S.D ⟨s.1, z s.1⟩ ⟨s.1, x⟩ +
            ∑ x : X s.1, ∑ y : X j, S.D ⟨s.1, z s.1⟩ ⟨s.1, x⟩ * S.D ⟨j, z j⟩ ⟨j, y⟩ *
              S.vstar (Function.update (Function.update z s.1 x) j y) := by
          have : ∀ x : X s.1, S.D ⟨s.1, z s.1⟩ ⟨s.1, x⟩ * S.Tj j S.vstar (Function.update z s.1 x) =
              S.ρ ⟨j, z j⟩ * S.D ⟨s.1, z s.1⟩ ⟨s.1, x⟩ + ∑ y : X j, S.D ⟨s.1, z s.1⟩ ⟨s.1, x⟩ * S.D ⟨j, z j⟩ ⟨j, y⟩ *
              S.vstar (Function.update (Function.update z s.1 x) j y) := by
            intro x
            unfold Tj
            rw [Function.update_of_ne hj]
            rw [mul_add, Finset.mul_sum]
            congr 1
            · ring
            · apply Finset.sum_congr rfl
              intros
              ring
          rw [Finset.sum_congr rfl (fun x _ => this x), Finset.sum_add_distrib, ← Finset.mul_sum]
        have hQ : S.Tj s.1 S.vstar z = S.ρ ⟨s.1, z s.1⟩ + ∑ x : X s.1, S.D ⟨s.1, z s.1⟩ ⟨s.1, x⟩ * S.vstar (Function.update z s.1 x) := rfl
        have hQ2 : ∑ x : X s.1, S.D ⟨s.1, z s.1⟩ ⟨s.1, x⟩ * S.Tj j S.vstar (Function.update z s.1 x) ≤
            ∑ x : X s.1, S.D ⟨s.1, z s.1⟩ ⟨s.1, x⟩ * S.vstar (Function.update z s.1 x) :=
          Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (Tj_le_vstar hr j _) (hr.1 _ _))
        have hss : (⟨s.1, z s.1⟩ : Σ i, X i) = s := by rw [hzs]
        have hrate : S.rate ⟨j, z j⟩ ≤ S.rate ⟨s.1, z s.1⟩ := by rw [hss]; exact hmax _ hja
        have hwj := hv.1 ⟨j, z j⟩
        have hws := hv.1 ⟨s.1, z s.1⟩
        unfold Stage.rate at hrate
        rw [div_le_div_iff₀ hwj hws] at hrate
        have e1 := hv.rs_eq ⟨j, z j⟩
        have e2 := hv.rs_eq ⟨s.1, z s.1⟩
        have e1' : S.rs ⟨j, z j⟩ = ∑ y : X j, S.D ⟨j, z j⟩ ⟨j, y⟩ := rfl
        have e2' : S.rs ⟨s.1, z s.1⟩ = ∑ x : X s.1, S.D ⟨s.1, z s.1⟩ ⟨s.1, x⟩ := rfl
        rw [E1]
        have hfin : 0 ≤ β * (S.ρ ⟨s.1, z s.1⟩ * S.w ⟨j, z j⟩ - S.ρ ⟨j, z j⟩ * S.w ⟨s.1, z s.1⟩) :=
          mul_nonneg hβ.le (by linarith)
        have hSe : ∑ y : X j, S.D ⟨j, z j⟩ ⟨j, y⟩ = 1 - β * S.w ⟨j, z j⟩ := by
          have := e1; rw [e1'] at this; linarith
        have hSd : ∑ x : X s.1, S.D ⟨s.1, z s.1⟩ ⟨s.1, x⟩ = 1 - β * S.w ⟨s.1, z s.1⟩ := by
          have := e2; rw [e2'] at this; linarith
        have h3 : S.ρ ⟨s.1, z s.1⟩ * ∑ y : X j, S.D ⟨j, z j⟩ ⟨j, y⟩ =
            S.ρ ⟨s.1, z s.1⟩ - S.ρ ⟨s.1, z s.1⟩ * (β * S.w ⟨j, z j⟩) := by rw [hSe]; ring
        have h4 : S.ρ ⟨j, z j⟩ * ∑ x : X s.1, S.D ⟨s.1, z s.1⟩ ⟨s.1, x⟩ =
            S.ρ ⟨j, z j⟩ - S.ρ ⟨j, z j⟩ * (β * S.w ⟨s.1, z s.1⟩) := by rw [hSd]; ring
        rw [hQ]
        rw [hQ] at *
        linarith
    · have hUz : U z = S.vstar z := by simp only [U]; rw [if_neg hzs]
      rw [hUz]
      exact (Tj_mono hr j U S.vstar hUle z).trans (Tj_le_vstar hr j z)
  choose π hπ using exists_greedy hr
  have key := comp_nonneg hr S.Dom (Dom_closed hv) (fun z => U z - S.vstar z) π (fun z hz => by
    have h := Tj_sub S (π z) U S.vstar z
    rw [hπ z] at h
    have := hsuper z hz (π z)
    rw [← h]; linarith)
  intro z hz hzs
  have h1 := key z hz
  have hUz : U z = S.Tj s.1 S.vstar z := by simp only [U]; rw [if_pos hzs]
  have h2 := Tj_le_vstar hr s.1 z
  linarith

end Stage

lemma e42_int_exp (β : ℝ) (hβ : 0 < β) (b : ℝ) :
    ∫ t in (0:ℝ)..b, Real.exp (-(β * t)) = (1 - Real.exp (-(β * b))) / β := by
  have h : ∀ x ∈ Set.uIcc 0 b, HasDerivAt (fun t => -(Real.exp (-(β * t))) / β) (Real.exp (-(β * x))) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => -β * t) (-β) x := by
      simpa using (hasDerivAt_id' x).const_mul (-β)
    have h2 := (h1.exp).neg.div_const β
    simp only [neg_mul] at h2
    refine h2.congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h (by
    apply Continuous.intervalIntegrable; fun_prop)]
  simp
  field_simp
  ring

namespace SemiMarkovBandit

variable {n : ℕ} {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]

lemma ind_meas (B : SemiMarkovBandit n X) (q p : Σ i, X i) :
    Measurable (fun ω : ℝ × ℝ × X q.1 => if (⟨q.1, ω.2.2⟩ : Σ i, X i) = p then (1:ℝ) else 0) := by
  apply Measurable.ite _ measurable_const measurable_const
  have : MeasurableSet {y : X q.1 | (⟨q.1, y⟩ : Σ i, X i) = p} := (Set.toFinite _).measurableSet
  exact measurable_snd.snd this

lemma kernel_int (B : SemiMarkovBandit n X) (q p : Σ i, X i) :
    Integrable (fun ω : ℝ × ℝ × X q.1 => Real.exp (-(B.β * ω.1)) *
      (if (⟨q.1, ω.2.2⟩ : Σ i, X i) = p then (1:ℝ) else 0)) (B.law q.1 q.2) := by
  haveI := B.isProb q.1 q.2
  refine Integrable.of_bound ?_ 1 ?_
  · exact ((Real.measurable_exp.comp (measurable_const.mul measurable_fst).neg).mul (B.ind_meas q p)).aestronglyMeasurable
  · filter_upwards [B.T_nonneg q.1 q.2] with ω hω
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    have h1 : Real.exp (-(B.β * ω.1)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [B.β_pos]
    have h2 : ‖(if (⟨q.1, ω.2.2⟩ : Σ i, X i) = p then (1:ℝ) else 0)‖ ≤ 1 := by
      split_ifs <;> simp
    calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

lemma initStage_valid (B : SemiMarkovBandit n X) : B.initStage.Valid B.β := by
  have hβ := B.β_pos
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- positivity of discounted durations
    intro q
    haveI := B.isProb q.1 q.2
    show 0 < B.discDuration q
    unfold discDuration
    have hF : (fun ω : ℝ × ℝ × X q.1 => ∫ t in (0 : ℝ)..ω.1, Real.exp (-(B.β * t))) =
        fun ω => (1 - Real.exp (-(B.β * ω.1))) / B.β := by
      funext ω; exact e42_int_exp B.β hβ _
    rw [hF]
    have hnn : 0 ≤ᵐ[B.law q.1 q.2] fun ω : ℝ × ℝ × X q.1 => (1 - Real.exp (-(B.β * ω.1))) / B.β := by
      filter_upwards [B.T_nonneg q.1 q.2] with ω hω
      have : Real.exp (-(B.β * ω.1)) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
      show 0 ≤ _
      apply div_nonneg (by linarith) hβ.le
    have hint : Integrable (fun ω : ℝ × ℝ × X q.1 => (1 - Real.exp (-(B.β * ω.1))) / B.β) (B.law q.1 q.2) := by
      refine Integrable.of_bound ?_ (1 / B.β) ?_
      · exact ((measurable_const.sub (Real.measurable_exp.comp (measurable_const.mul measurable_fst).neg)).div_const _).aestronglyMeasurable
      · filter_upwards [B.T_nonneg q.1 q.2] with ω hω
        have h1 : Real.exp (-(B.β * ω.1)) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
        have h2 := Real.exp_pos (-(B.β * ω.1))
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith) hβ.le)]
        exact div_le_div_of_nonneg_right (by linarith) hβ.le
    rw [integral_pos_iff_support_of_nonneg_ae hnn hint]
    refine lt_of_lt_of_le (B.T_pos q.1 q.2) (measure_mono ?_)
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    simp only [Function.mem_support]
    have : Real.exp (-(B.β * ω.1)) < 1 := by
      have := Real.exp_lt_exp.2 (show -(B.β * ω.1) < 0 by nlinarith)
      simpa using this
    exact ne_of_gt (div_pos (by linarith) hβ)
  · intro q p
    show 0 ≤ B.discKernel q p
    unfold discKernel
    apply integral_nonneg
    intro ω
    show 0 ≤ Real.exp _ * _
    split_ifs <;> simp [Real.exp_pos, (Real.exp_pos _).le]
  · intro q p hqp
    show B.discKernel q p = 0
    unfold discKernel
    have : ∀ ω : ℝ × ℝ × X q.1, (if (⟨q.1, ω.2.2⟩ : Σ i, X i) = p then (1:ℝ) else 0) = 0 := by
      intro ω
      rw [if_neg]
      intro h
      have h2 := congrArg Sigma.fst h
      exact hqp h2
    simp [this]
  · intro q p hp
    exact absurd (Finset.mem_univ p) hp
  · intro q
    haveI := B.isProb q.1 q.2
    show B.β * B.discDuration q = 1 - ∑ p, B.discKernel q p
    have hF : (fun ω : ℝ × ℝ × X q.1 => ∫ t in (0 : ℝ)..ω.1, Real.exp (-(B.β * t))) =
        fun ω => (1 - Real.exp (-(B.β * ω.1))) / B.β := by
      funext ω; exact e42_int_exp B.β hβ _
    have hsum : ∑ p : Σ i, X i, B.discKernel q p = ∫ ω, Real.exp (-(B.β * ω.1)) ∂(B.law q.1 q.2) := by
      unfold discKernel
      rw [← integral_finsetSum _ (fun p _ => B.kernel_int q p)]
      congr 1
      funext ω
      rw [← Finset.mul_sum]
      have : ∑ p : Σ i, X i, (if (⟨q.1, ω.2.2⟩ : Σ i, X i) = p then (1:ℝ) else 0) = 1 := by
        simp
      rw [this, mul_one]
    have hint1 : Integrable (fun ω : ℝ × ℝ × X q.1 => Real.exp (-(B.β * ω.1))) (B.law q.1 q.2) := by
      refine Integrable.of_bound ?_ 1 ?_
      · exact (Real.measurable_exp.comp (measurable_const.mul measurable_fst).neg).aestronglyMeasurable
      · filter_upwards [B.T_nonneg q.1 q.2] with ω hω
        rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]; nlinarith
    rw [hsum]
    unfold discDuration
    rw [hF, integral_div, integral_sub (integrable_const _) hint1]
    simp
    field_simp

end SemiMarkovBandit

namespace Stage
variable {n : ℕ} {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
variable [NeZero n]

end Stage

section Cores

variable {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [∀ i, Nonempty (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]

theorem lemma21_core (B : SemiMarkovBandit n X)
    (s : Σ i, X i) (hmax : ∀ q : Σ i, X i, B.rate q ≤ B.rate s) :
    ∃ π : Policy n X, B.IsOptimal π ∧ ∀ z : JointState n X, z s.1 = s.2 → π z = s.1 := by
  have hv := B.initStage_valid
  obtain ⟨κ, hr⟩ := hv.reg B.β_pos
  choose π0 hπ0 using Stage.exists_greedy hr
  refine ⟨fun z => if z s.1 = s.2 then s.1 else π0 z, ?_, fun z hz => by simp [hz]⟩
  have hg : ∀ z ∈ (Set.univ : Set (JointState n X)),
      B.initStage.Tj (if z s.1 = s.2 then s.1 else π0 z) B.initStage.vstar z = B.initStage.vstar z := by
    intro z _
    by_cases hz : z s.1 = s.2
    · simp only [hz, if_true]
      exact Stage.topA B.β_pos hv hr s (Finset.mem_univ _) (fun q _ => hmax q) z
        (fun i => Finset.mem_univ _) hz
    · simp only [hz, if_false]
      exact hπ0 z
  have hval := Stage.value_eq_of_greedy hr Set.univ (fun _ _ _ _ _ => Set.mem_univ _) _ hg
  intro π' z
  have h1 := Stage.value_le_vstar hr π' z
  have h2 := hval z (Set.mem_univ _)
  show B.initStage.value π' z ≤ B.initStage.value _ z
  rw [h2]; exact h1

end Cores

namespace Stage

variable {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

lemma Dss_lt {β : ℝ} (hβ : 0 < β) {S : Stage n X} (hv : S.Valid β) (s : Σ i, X i) : S.D s s < 1 := by
  have h1 : S.D s s ≤ S.rs s := by
    unfold rs
    exact Finset.single_le_sum (f := fun y : X s.1 => S.D s ⟨s.1, y⟩) (fun y _ => hv.2.1 _ _) (Finset.mem_univ s.2)
  have := hv.rs_eq s
  have := mul_pos hβ (hv.1 s)
  linarith

lemma sum_ite_ne {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℝ) (s : α) :
    ∑ p, (if p = s then 0 else f p) = ∑ p, f p - f s := by
  have h1 : ∑ p, (if p = s then 0 else f p) = ∑ p ∈ Finset.univ.erase s, f p := by
    rw [← Finset.sum_erase (Finset.univ) (f := fun p => if p = s then 0 else f p) (a := s) (by simp)]
    exact Finset.sum_congr rfl (fun p hp => by rw [if_neg (Finset.ne_of_mem_erase hp)])
  rw [h1]
  have := Finset.add_sum_erase Finset.univ f (Finset.mem_univ s)
  linarith

lemma Valid.reduce {β : ℝ} (hβ : 0 < β) {S : Stage n X} (hv : S.Valid β) (s : Σ i, X i) :
    (S.reduce s).Valid β := by
  have hd : 0 < 1 - S.D s s := sub_pos.2 (Dss_lt hβ hv s)
  have hc : ∀ q, 0 ≤ S.D q s / (1 - S.D s s) := fun q => div_nonneg (hv.2.1 _ _) hd.le
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q
    show 0 < S.w q + S.D q s / (1 - S.D s s) * S.w s
    have := hv.1 q; have := hv.1 s; have := mul_nonneg (hc q) (hv.1 s).le
    linarith
  · intro q p
    show 0 ≤ if p = s then 0 else S.D q p + S.D q s / (1 - S.D s s) * S.D s p
    split_ifs
    · exact le_rfl
    · exact add_nonneg (hv.2.1 _ _) (mul_nonneg (hc q) (hv.2.1 _ _))
  · intro q p hqp
    show (if p = s then 0 else S.D q p + S.D q s / (1 - S.D s s) * S.D s p) = 0
    split_ifs
    · rfl
    · rw [hv.2.2.1 q p hqp]
      by_cases h : q.1 = s.1
      · rw [hv.2.2.1 s p (by rw [← h]; exact hqp)]; simp
      · rw [hv.2.2.1 q s h]; simp
  · intro q p hp
    show (if p = s then 0 else S.D q p + S.D q s / (1 - S.D s s) * S.D s p) = 0
    split_ifs with h
    · rfl
    · have hp' : p ∉ S.alive := fun hh => hp (Finset.mem_erase.2 ⟨h, hh⟩)
      rw [hv.2.2.2.1 q p hp', hv.2.2.2.1 s p hp']; simp
  · intro q
    show β * (S.w q + S.D q s / (1 - S.D s s) * S.w s) =
      1 - ∑ p, (if p = s then 0 else S.D q p + S.D q s / (1 - S.D s s) * S.D s p)
    rw [sum_ite_ne, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hq := hv.2.2.2.2 q
    have hs := hv.2.2.2.2 s
    have hcd : S.D q s / (1 - S.D s s) * (1 - S.D s s) = S.D q s := div_mul_cancel₀ _ hd.ne'
    linear_combination hq + (S.D q s / (1 - S.D s s)) * hs + hcd

end Stage

namespace Stage

variable {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

lemma reduce_Tj_ne {β : ℝ} {S : Stage n X} (hv : S.Valid β) (s : Σ i, X i) (j : Fin n) (hj : j ≠ s.1)
    (V : JointState n X → ℝ) (z : JointState n X) :
    (S.reduce s).Tj j V z = S.Tj j V z := by
  have hq : S.D ⟨j, z j⟩ s = 0 := hv.2.2.1 _ _ hj
  unfold Tj
  have h1 : (S.reduce s).ρ ⟨j, z j⟩ = S.ρ ⟨j, z j⟩ := by
    show S.ρ _ + S.D _ s / _ * S.ρ s = _
    rw [hq]; simp
  rw [h1]
  congr 1
  refine Finset.sum_congr rfl (fun y _ => ?_)
  have hne : (⟨j, y⟩ : Σ i, X i) ≠ s := fun h => hj (congrArg Sigma.fst h)
  show (if (⟨j, y⟩ : Σ i, X i) = s then 0 else S.D ⟨j, z j⟩ ⟨j, y⟩ + S.D ⟨j, z j⟩ s / (1 - S.D s s) * S.D s ⟨j, y⟩) *
    V (Function.update z j y) = _
  rw [if_neg hne, hq]; simp

lemma reduce_Tj_eq {β : ℝ} (hβ : 0 < β) {S : Stage n X} (hv : S.Valid β) (s : Σ i, X i)
    (V : JointState n X → ℝ) (z : JointState n X)
    (hs : V (Function.update z s.1 s.2) = S.Tj s.1 V (Function.update z s.1 s.2)) :
    (S.reduce s).Tj s.1 V z = S.Tj s.1 V z := by
  have hd : 0 < 1 - S.D s s := sub_pos.2 (Dss_lt hβ hv s)
  set c := S.D ⟨s.1, z s.1⟩ s / (1 - S.D s s) with hc
  have hcd : c * (1 - S.D s s) = S.D ⟨s.1, z s.1⟩ s := div_mul_cancel₀ _ hd.ne'
  set F : X s.1 → ℝ := fun y => V (Function.update z s.1 y) with hF
  have hs' : F s.2 * (1 - S.D s s) = S.ρ s + ∑ y ∈ Finset.univ.erase s.2, S.D s ⟨s.1, y⟩ * F y := by
    have h1 : F s.2 = S.ρ s + ∑ y : X s.1, S.D s ⟨s.1, y⟩ * F y := by
      have := hs
      unfold Tj at this
      simp only [Function.update_self, Function.update_idem] at this
      exact this
    have h2 := Finset.add_sum_erase Finset.univ (fun y => S.D s ⟨s.1, y⟩ * F y) (Finset.mem_univ s.2)
    have h3 : S.D s ⟨s.1, s.2⟩ = S.D s s := rfl
    rw [h3] at h2
    linarith
  have hL : (S.reduce s).Tj s.1 V z = S.ρ ⟨s.1, z s.1⟩ + c * S.ρ s +
      (∑ y ∈ Finset.univ.erase s.2, S.D ⟨s.1, z s.1⟩ ⟨s.1, y⟩ * F y +
        c * ∑ y ∈ Finset.univ.erase s.2, S.D s ⟨s.1, y⟩ * F y) := by
    unfold Tj
    show S.ρ ⟨s.1, z s.1⟩ + c * S.ρ s + ∑ y : X s.1, (if (⟨s.1, y⟩ : Σ i, X i) = s then 0 else
      S.D ⟨s.1, z s.1⟩ ⟨s.1, y⟩ + c * S.D s ⟨s.1, y⟩) * V (Function.update z s.1 y) = _
    congr 1
    rw [← Finset.sum_erase Finset.univ (f := fun y : X s.1 => (if (⟨s.1, y⟩ : Σ i, X i) = s then 0 else
      S.D ⟨s.1, z s.1⟩ ⟨s.1, y⟩ + c * S.D s ⟨s.1, y⟩) * V (Function.update z s.1 y)) (a := s.2) (by simp)]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    have hne : (⟨s.1, y⟩ : Σ i, X i) ≠ s := by
      intro h
      have := (Sigma.ext_iff.1 h).2
      exact Finset.ne_of_mem_erase hy (eq_of_heq this)
    rw [if_neg hne]
    simp only [hF]
    ring
  have hR : S.Tj s.1 V z = S.ρ ⟨s.1, z s.1⟩ + S.D ⟨s.1, z s.1⟩ s * F s.2 +
      ∑ y ∈ Finset.univ.erase s.2, S.D ⟨s.1, z s.1⟩ ⟨s.1, y⟩ * F y := by
    unfold Tj
    have h2 := Finset.add_sum_erase Finset.univ (fun y => S.D ⟨s.1, z s.1⟩ ⟨s.1, y⟩ * F y) (Finset.mem_univ s.2)
    have h3 : S.D ⟨s.1, z s.1⟩ ⟨s.1, s.2⟩ = S.D ⟨s.1, z s.1⟩ s := rfl
    rw [h3] at h2
    rw [add_assoc, ← h2]
  rw [hL, hR]
  linear_combination (-c) * hs' + (F s.2) * hcd

end Stage

namespace Stage

variable {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

lemma eq_of_fixed_on {S : Stage n X} {κ : ℝ} (hr : Reg S κ) (N : Set (JointState n X))
    (hN : ∀ z ∈ N, ∀ j y, S.D ⟨j, z j⟩ ⟨j, y⟩ ≠ 0 → Function.update z j y ∈ N)
    (π : Policy n X) (f g : JointState n X → ℝ)
    (hf : ∀ z ∈ N, f z = S.Tj (π z) f z) (hg : ∀ z ∈ N, g z = S.Tj (π z) g z) :
    ∀ z ∈ N, f z = g z := by
  have key : ∀ z ∈ N, ∑ y : X (π z), S.D ⟨π z, z (π z)⟩ ⟨π z, y⟩ *
      ((fun z => f z - g z) (Function.update z (π z) y)) = f z - g z := by
    intro z hz
    have h := Tj_sub S (π z) f g z
    rw [← hf z hz, ← hg z hz] at h
    exact h.symm
  have a := comp_nonneg hr N hN (fun z => f z - g z) π (fun z hz => (key z hz).le)
  have b := comp_nonpos hr N hN (fun z => f z - g z) π (fun z hz => (key z hz).ge)
  intro z hz
  linarith [a z hz, b z hz]

end Stage

section Cores2

variable {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [∀ i, Nonempty (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]

lemma reduce_closed {S : Stage n X} (s : Σ i, X i) :
    ∀ z ∈ {z : JointState n X | z s.1 ≠ s.2}, ∀ j y, (S.reduce s).D ⟨j, z j⟩ ⟨j, y⟩ ≠ 0 →
      Function.update z j y ∈ {z : JointState n X | z s.1 ≠ s.2} := by
  intro z hz j y hd
  simp only [Set.mem_setOf_eq] at hz ⊢
  by_cases hj : j = s.1
  · subst hj
    rw [Function.update_self]
    intro hy
    apply hd
    show (if (⟨s.1, y⟩ : Σ i, X i) = s then 0 else _) = 0
    rw [if_pos]
    exact Sigma.ext rfl (heq_of_eq hy)
  · rw [Function.update_of_ne (Ne.symm hj)]; exact hz

theorem reduction_core (B : SemiMarkovBandit n X)
    (s : Σ i, X i) :
    (B.initStage.reduce s).Valid B.β ∧
      (B.initStage.reduce s).alive.card + 1 = Fintype.card (Σ i, X i) ∧
      (∀ π : Policy n X, (∀ z : JointState n X, z s.1 = s.2 → π z = s.1) →
        ∀ z : JointState n X, z s.1 ≠ s.2 → B.value π z = (B.initStage.reduce s).value π z) ∧
      (∀ π' : Policy n X, ∃ π : Policy n X, (∀ z : JointState n X, z s.1 = s.2 → π z = s.1) ∧
        ∀ z : JointState n X, z s.1 ≠ s.2 →
          (B.initStage.reduce s).value π z = (B.initStage.reduce s).value π' z) := by
  have hv := B.initStage_valid
  have hv' := Stage.Valid.reduce B.β_pos hv s
  obtain ⟨κ, hr⟩ := hv.reg B.β_pos
  obtain ⟨κ', hr'⟩ := hv'.reg B.β_pos
  refine ⟨hv', ?_, ?_, ?_⟩
  · show (Finset.univ.erase s).card + 1 = _
    rw [Finset.card_erase_add_one (Finset.mem_univ s), Finset.card_univ]
  · intro π hπ z hz
    have hW := Stage.value_fixed hr π
    have hfix : ∀ z ∈ {z : JointState n X | z s.1 ≠ s.2},
        B.initStage.value π z = (B.initStage.reduce s).Tj (π z) (B.initStage.value π) z := by
      intro z _
      by_cases hpz : π z = s.1
      · have hs := hW (Function.update z s.1 s.2)
        rw [hπ _ (by simp)] at hs
        rw [hpz, Stage.reduce_Tj_eq B.β_pos hv s _ z hs, ← hpz]
        exact hW z
      · rw [Stage.reduce_Tj_ne hv s _ hpz]
        exact hW z
    exact Stage.eq_of_fixed_on hr' _ (reduce_closed s) π _ _ hfix
      (fun z _ => Stage.value_fixed hr' π z) z hz
  · intro π'
    refine ⟨fun z => if z s.1 = s.2 then s.1 else π' z, fun z hz => by simp [hz], ?_⟩
    intro z hz
    refine Stage.eq_of_fixed_on hr' _ (reduce_closed s) π' _ _ ?_
      (fun z _ => Stage.value_fixed hr' π' z) z hz
    intro z' hz'
    have h := Stage.value_fixed hr' (fun z => if z s.1 = s.2 then s.1 else π' z) z'
    have hz'' : z' s.1 ≠ s.2 := hz'
    simp only [hz'', if_false] at h
    exact h

end Cores2

end TsitsiklisGittins.IndexTheorem

open TsitsiklisGittins.IndexTheorem


theorem solution {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    [∀ i, Nonempty (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (B : SemiMarkovBandit n X)
    (s : Σ i, X i) (hmax : ∀ q : Σ i, X i, B.rate q ≤ B.rate s) (hns : ∃ x : X s.1, x ≠ s.2) :
    (B.initStage.reduce s).Valid B.β ∧
      (B.initStage.reduce s).alive.card + 1 = Fintype.card (Σ i, X i) ∧
      (∀ π : Policy n X, (∀ z : JointState n X, z s.1 = s.2 → π z = s.1) →
        ∀ z : JointState n X, z s.1 ≠ s.2 → B.value π z = (B.initStage.reduce s).value π z) ∧
      (∀ π' : Policy n X, ∃ π : Policy n X, (∀ z : JointState n X, z s.1 = s.2 → π z = s.1) ∧
        ∀ z : JointState n X, z s.1 ≠ s.2 →
          (B.initStage.reduce s).value π z = (B.initStage.reduce s).value π' z) := by
  exact reduction_core B s
