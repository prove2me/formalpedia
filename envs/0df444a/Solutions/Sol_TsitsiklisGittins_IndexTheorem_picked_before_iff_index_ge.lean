-- Prove2me | solution 1 for TsitsiklisGittins.IndexTheorem.picked_before_iff_index_ge
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T01:52:00.722869+00:00
-- url     : https://prove2.me/submissions/6daebcc5-ce23-4d2a-bedc-9fb5c96cbe41

import Mathlib
import Definitions.Def_TsitsiklisGittins_IndexTheorem_IndexRun



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

namespace Stage

variable {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

lemma Tj_congr_on {S : Stage n X} (N : Set (JointState n X))
    (hN : ∀ z ∈ N, ∀ j y, S.D ⟨j, z j⟩ ⟨j, y⟩ ≠ 0 → Function.update z j y ∈ N)
    (f g : JointState n X → ℝ) (hfg : ∀ z ∈ N, f z = g z) :
    ∀ z ∈ N, ∀ j, S.Tj j f z = S.Tj j g z := by
  intro z hz j
  unfold Tj
  congr 1
  refine Finset.sum_congr rfl (fun y _ => ?_)
  by_cases hd : S.D ⟨j, z j⟩ ⟨j, y⟩ = 0
  · rw [hd]; simp
  · rw [hfg _ (hN z hz j y hd)]

lemma Dom_update_mem {S : Stage n X} (z : JointState n X) (hz : z ∈ S.Dom) (s : Σ i, X i)
    (hs : s ∈ S.alive) : Function.update z s.1 s.2 ∈ S.Dom := by
  intro i
  by_cases hi : i = s.1
  · subst hi; rw [Function.update_self]; exact hs
  · rw [Function.update_of_ne hi]; exact hz i

/-- translation between the optimal value of a stage and of its reduction -/
lemma translate {β κ κ' : ℝ} (hβ : 0 < β) {S : Stage n X} (hv : S.Valid β) (hr : Reg S κ)
    (s : Σ i, X i) (hr' : Reg (S.reduce s) κ')
    (hs : s ∈ S.alive) (hmax : ∀ q ∈ S.alive, S.rate q ≤ S.rate s) :
    ∀ z ∈ (S.reduce s).Dom, (S.reduce s).vstar z = S.vstar z ∧
      ∀ j, (S.reduce s).Tj j (S.reduce s).vstar z = S.Tj j S.vstar z := by
  have hv' := Valid.reduce hβ hv s
  have hclosed := Dom_closed hv'
  -- membership of the reduced domain
  have hDom : ∀ z ∈ (S.reduce s).Dom, z ∈ S.Dom ∧ z s.1 ≠ s.2 := by
    intro z hz
    refine ⟨fun i => ?_, fun h => ?_⟩
    · exact (Finset.mem_erase.1 (hz i)).2
    · have := (Finset.mem_erase.1 (hz s.1)).1
      exact this (Sigma.ext rfl (heq_of_eq h))
  -- (ii') Bellman data agree on the reduced domain
  have hT : ∀ z ∈ (S.reduce s).Dom, ∀ j, (S.reduce s).Tj j S.vstar z = S.Tj j S.vstar z := by
    intro z hz j
    obtain ⟨hzD, _⟩ := hDom z hz
    by_cases hj : j = s.1
    · subst hj
      refine reduce_Tj_eq hβ hv s _ z ?_
      have := topA hβ hv hr s hs hmax _ (Dom_update_mem z hzD s hs) (by simp)
      exact this.symm
    · exact reduce_Tj_ne hv s j hj _ z
  -- S.vstar satisfies the Bellman equation of the reduced stage on its domain
  have hf : ∀ z ∈ (S.reduce s).Dom, ∃ j, S.vstar z = (S.reduce s).Tj j S.vstar z := by
    intro z hz
    obtain ⟨j, hj⟩ := exists_greedy hr z
    exact ⟨j, by rw [hT z hz j, hj]⟩
  have hf2 : ∀ z ∈ (S.reduce s).Dom, ∀ j, (S.reduce s).Tj j S.vstar z ≤ S.vstar z := by
    intro z hz j; rw [hT z hz j]; exact Tj_le_vstar hr j z
  choose! πf hπf using hf
  choose πg hπg using exists_greedy hr'
  have hge : ∀ z ∈ (S.reduce s).Dom, S.vstar z = (S.reduce s).vstar z := by
    intro z hz
    have a := comp_nonpos hr' (S.reduce s).Dom hclosed (fun z => S.vstar z - (S.reduce s).vstar z) πf
      (fun z hz => by
        have h1 := Tj_sub (S.reduce s) (πf z) S.vstar (S.reduce s).vstar z
        have h2 := Tj_le_vstar hr' (πf z) z
        have h3 := hπf z hz
        linarith)
    have b := comp_nonneg hr' (S.reduce s).Dom hclosed (fun z => S.vstar z - (S.reduce s).vstar z) πg
      (fun z hz => by
        have h1 := Tj_sub (S.reduce s) (πg z) S.vstar (S.reduce s).vstar z
        have h2 := hπg z
        have h3 := hf2 z hz (πg z)
        linarith)
    linarith [a z hz, b z hz]
  intro z hz
  refine ⟨(hge z hz).symm, fun j => ?_⟩
  rw [Tj_congr_on (S := S.reduce s) (S.reduce s).Dom hclosed _ _ (fun z hz => (hge z hz).symm) z hz j]
  exact hT z hz j

end Stage

namespace SemiMarkovBandit

section Runs

variable {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [∀ i, Nonempty (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]

lemma foldl_valid {β : ℝ} (hβ : 0 < β) (L : List (Σ i, X i)) :
    ∀ S : Stage n X, S.Valid β → (L.foldl Stage.reduce S).Valid β := by
  induction L with
  | nil => intro S h; exact h
  | cons a L ih => intro S h; exact ih _ (Stage.Valid.reduce hβ h a)

lemma foldl_alive (L : List (Σ i, X i)) (q : Σ i, X i) :
    ∀ S : Stage n X, q ∈ (L.foldl Stage.reduce S).alive ↔ q ∈ S.alive ∧ q ∉ L := by
  induction L with
  | nil => intro S; simp
  | cons a L ih =>
    intro S
    rw [List.foldl_cons, ih]
    show (q ∈ S.alive.erase a ∧ _) ↔ _
    rw [Finset.mem_erase]
    simp only [List.mem_cons, not_or]
    tauto

lemma stageAfter_valid (B : SemiMarkovBandit n X) (L : List (Σ i, X i)) :
    (B.stageAfter L).Valid B.β :=
  foldl_valid B.β_pos L _ B.initStage_valid

lemma stageAfter_alive (B : SemiMarkovBandit n X) (L : List (Σ i, X i)) (q : Σ i, X i) :
    q ∈ (B.stageAfter L).alive ↔ q ∉ L := by
  unfold stageAfter
  rw [foldl_alive]
  show (q ∈ (Finset.univ : Finset (Σ i, X i)) ∧ _) ↔ _
  simp

lemma stageAfter_snoc (B : SemiMarkovBandit n X) (L : List (Σ i, X i)) (s : Σ i, X i) :
    B.stageAfter (L ++ [s]) = (B.stageAfter L).reduce s := by
  unfold stageAfter
  rw [List.foldl_append]; rfl

lemma take_succ_eq (l : List (Σ i, X i)) (k : ℕ) (hk : k < l.length) :
    l.take (k + 1) = l.take k ++ [l[k]] := by
  rw [List.take_succ, List.getElem?_eq_getElem hk]; rfl

end Runs

end SemiMarkovBandit

section Cores3

variable {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [∀ i, Nonempty (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]

lemma Dom_reduce_of_ne {S : Stage n X} (s : Σ i, X i) (z : JointState n X) (hz : z ∈ S.Dom)
    (hzs : z s.1 ≠ s.2) : z ∈ (S.reduce s).Dom := by
  intro i
  show _ ∈ S.alive.erase s
  rw [Finset.mem_erase]
  refine ⟨fun h => ?_, hz i⟩
  obtain ⟨h1, h2⟩ := Sigma.ext_iff.1 h
  subst h1
  exact hzs (eq_of_heq h2)

lemma optimal_of_greedy (B : SemiMarkovBandit n X) (π : Policy n X)
    (hg : ∀ z, B.initStage.Tj (π z) B.initStage.vstar z = B.initStage.vstar z) : B.IsOptimal π := by
  have hv := B.initStage_valid
  obtain ⟨κ, hr⟩ := hv.reg B.β_pos
  have hval := Stage.value_eq_of_greedy hr Set.univ (fun _ _ _ _ _ => Set.mem_univ _) π (fun z _ => hg z)
  intro π' z
  have h1 := Stage.value_le_vstar hr π' z
  have h2 := hval z (Set.mem_univ _)
  show B.initStage.value π' z ≤ B.initStage.value π z
  rw [h2]; exact h1

theorem pick_order_core (B : SemiMarkovBandit n X)
    (seq : List (Σ i, X i)) (γ : (Σ i, X i) → ℝ) (hrun : B.IsIndexRun seq γ)
    (rank : (Σ i, X i) → ℕ)
    (hord : ∀ (a b : ℕ) (ha : a < seq.length) (hb : b < seq.length), a < b → rank seq[b] < rank seq[a])
    (π : Policy n X) (hπ : FollowsRank rank π) : B.IsOptimal π := by
  have key : ∀ m k, k + m = seq.length → ∀ z ∈ (B.stageAfter (seq.take k)).Dom,
      (B.stageAfter (seq.take k)).Tj (π z) (B.stageAfter (seq.take k)).vstar z =
        (B.stageAfter (seq.take k)).vstar z := by
    intro m
    induction m with
    | zero =>
      intro k hk z hz
      exfalso
      have hk' : k = seq.length := by omega
      have h0 := hz (0 : Fin n)
      rw [B.stageAfter_alive, hk', List.take_length] at h0
      exact h0 (hrun.2.1 _)
    | succ m ih =>
      intro k hk z hz
      have hlt : k < seq.length := by omega
      obtain ⟨halive, hmax, _⟩ := hrun.2.2 k hlt
      have hv := B.stageAfter_valid (seq.take k)
      obtain ⟨κ, hr⟩ := hv.reg B.β_pos
      have hred : B.stageAfter (seq.take (k + 1)) = (B.stageAfter (seq.take k)).reduce seq[k] := by
        rw [SemiMarkovBandit.take_succ_eq seq k hlt, B.stageAfter_snoc]
      have hv' := Stage.Valid.reduce B.β_pos hv seq[k]
      obtain ⟨κ', hr'⟩ := hv'.reg B.β_pos
      by_cases hzs : z (seq[k]).1 = (seq[k]).2
      · have hpi : π z = (seq[k]).1 := by
          have hqalive := hz (π z)
          rw [B.stageAfter_alive] at hqalive
          obtain ⟨p, hp, hpq⟩ := List.mem_iff_getElem.1 (hrun.2.1 ⟨π z, z (π z)⟩)
          have hpk : k ≤ p := by
            by_contra h
            push_neg at h
            apply hqalive
            rw [← hpq]
            exact List.mem_iff_getElem.2 ⟨p, by simp; omega, by simp⟩
          have hr1 := hπ z (seq[k]).1
          have hss : (⟨(seq[k]).1, z (seq[k]).1⟩ : Σ i, X i) = seq[k] := Sigma.ext rfl (heq_of_eq hzs)
          rw [hss] at hr1
          rcases lt_or_eq_of_le hpk with hlt2 | heq
          · have := hord k p hlt hp hlt2
            rw [hpq] at this
            omega
          · subst heq
            exact (congrArg Sigma.fst hpq).symm
        rw [hpi]
        exact Stage.topA B.β_pos hv hr seq[k] halive hmax z hz hzs
      · have hzD := Dom_reduce_of_ne seq[k] z hz hzs
        have := ih (k + 1) (by omega) z (by rw [hred]; exact hzD)
        rw [hred] at this
        obtain ⟨h1, h2⟩ := Stage.translate B.β_pos hv hr seq[k] hr' halive hmax z hzD
        rw [h2 (π z), h1] at this
        exact this
  apply optimal_of_greedy
  intro z
  have := key seq.length 0 (by omega) z (fun i => by
    rw [B.stageAfter_alive]; simp)
  rw [List.take_zero] at this
  exact this

end Cores3

section Cores4

variable {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [∀ i, Nonempty (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]

lemma exists_run_prefix (B : SemiMarkovBandit n X) : ∀ m, m ≤ Fintype.card (Σ i, X i) →
    ∃ L : List (Σ i, X i), L.length = m ∧ L.Nodup ∧ ∀ k (hk : k < L.length),
      L[k] ∈ (B.stageAfter (L.take k)).alive ∧
      ∀ q ∈ (B.stageAfter (L.take k)).alive,
        (B.stageAfter (L.take k)).rate q ≤ (B.stageAfter (L.take k)).rate L[k] := by
  intro m
  induction m with
  | zero => intro _; exact ⟨[], rfl, List.nodup_nil, fun k hk => absurd hk (by simp)⟩
  | succ m ih =>
    intro hm
    obtain ⟨L, hlen, hnd, hL⟩ := ih (by omega)
    have hne : (B.stageAfter L).alive.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      have hall : ∀ q : Σ i, X i, q ∈ L := by
        intro q
        by_contra hq
        have := (B.stageAfter_alive L q).2 hq
        rw [h] at this
        simp at this
      have : (Finset.univ : Finset (Σ i, X i)) ⊆ L.toFinset := fun q _ => List.mem_toFinset.2 (hall q)
      have h2 := Finset.card_le_card this
      rw [Finset.card_univ] at h2
      have := List.toFinset_card_le L
      omega
    obtain ⟨s, hs, hsmax⟩ := Finset.exists_max_image (B.stageAfter L).alive (B.stageAfter L).rate hne
    have hsL : s ∉ L := (B.stageAfter_alive L s).1 hs
    refine ⟨L ++ [s], by simp [hlen], ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hnd, List.nodup_singleton s, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      intro hab; subst hab; exact hsL ha
    · intro k hk
      have hk' : k < L.length + 1 := by simpa using hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hlt | heq
      · have htake : (L ++ [s]).take k = L.take k := List.take_append_of_le_length hlt.le
        have hget : (L ++ [s])[k] = L[k] := List.getElem_append_left hlt
        rw [htake, hget]
        exact hL k hlt
      · subst heq
        have htake : (L ++ [s]).take L.length = L := by simp
        have hget : (L ++ [s])[L.length] = s := by simp
        rw [htake, hget]
        exact ⟨hs, fun q hq => hsmax q hq⟩

lemma exists_run (B : SemiMarkovBandit n X) : ∃ seq γ, B.IsIndexRun seq γ := by
  obtain ⟨L, hlen, hnd, hL⟩ := exists_run_prefix B (Fintype.card (Σ i, X i)) le_rfl
  have hall : ∀ q : Σ i, X i, q ∈ L := by
    have : L.toFinset = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [List.toFinset_card_of_nodup hnd, hlen]
    intro q
    rw [← List.mem_toFinset, this]; exact Finset.mem_univ q
  refine ⟨L, fun q => (B.stageAfter (L.take (L.idxOf q))).rate q, hnd, hall, fun k hk => ?_⟩
  obtain ⟨h1, h2⟩ := hL k hk
  refine ⟨h1, h2, ?_⟩
  show (B.stageAfter (L.take (L.idxOf L[k]))).rate L[k] = _
  rw [hnd.idxOf_getElem k hk]

end Cores4

section Cores5

variable {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [∀ i, Nonempty (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]

theorem theorem21_core (B : SemiMarkovBandit n X) :
    ∃ π : Policy n X, IsPriorityRule π ∧ B.IsOptimal π := by
  obtain ⟨seq, γ, hrun⟩ := exists_run B
  have hnd := hrun.1
  have hall := hrun.2.1
  let rank : (Σ i, X i) → ℕ := fun q => seq.length - seq.idxOf q
  have hinj : Function.Injective rank := by
    intro p q hpq
    have hp : seq.idxOf p < seq.length := List.idxOf_lt_length_iff.2 (hall p)
    have hq : seq.idxOf q < seq.length := List.idxOf_lt_length_iff.2 (hall q)
    have : seq.idxOf p = seq.idxOf q := by
      have hpq' : seq.length - seq.idxOf p = seq.length - seq.idxOf q := hpq
      omega
    exact (List.idxOf_inj (hall p)).1 this
  have hex : ∀ z : JointState n X, ∃ j : Fin n, ∀ i : Fin n, rank ⟨i, z i⟩ ≤ rank ⟨j, z j⟩ := by
    intro z
    obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (fun j : Fin n => rank ⟨j, z j⟩) Finset.univ_nonempty
    exact ⟨j, fun i => hj i (Finset.mem_univ i)⟩
  choose π hπ using hex
  have hord : ∀ (a b : ℕ) (ha : a < seq.length) (hb : b < seq.length), a < b → rank seq[b] < rank seq[a] := by
    intro a b ha hb hab
    show seq.length - seq.idxOf seq[b] < seq.length - seq.idxOf seq[a]
    rw [hnd.idxOf_getElem a ha, hnd.idxOf_getElem b hb]
    omega
  exact ⟨π, ⟨rank, hinj, hπ⟩, pick_order_core B seq γ hrun rank hord π hπ⟩

end Cores5

namespace Stage

variable {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

lemma rate_reduce_bounds {β : ℝ} (hβ : 0 < β) {S : Stage n X} (hv : S.Valid β) (s q : Σ i, X i)
    (hq : S.rate q ≤ S.rate s) :
    S.rate q ≤ (S.reduce s).rate q ∧ (S.reduce s).rate q ≤ S.rate s ∧
      (S.rate q < S.rate s → (S.reduce s).rate q < S.rate s) := by
  have hd : 0 < 1 - S.D s s := sub_pos.2 (Dss_lt hβ hv s)
  have hc : 0 ≤ S.D q s / (1 - S.D s s) := div_nonneg (hv.2.1 _ _) hd.le
  set c := S.D q s / (1 - S.D s s) with hcdef
  have hw := hv.1 q
  have hws := hv.1 s
  have hw' : 0 < S.w q + c * S.w s := by
    have := mul_nonneg hc hws.le
    linarith
  have hρs : S.ρ s = S.rate s * S.w s := by
    unfold Stage.rate; field_simp
  have hρq : S.ρ q = S.rate q * S.w q := by
    unfold Stage.rate; field_simp
  have hrate : (S.reduce s).rate q = (S.ρ q + c * S.ρ s) / (S.w q + c * S.w s) := rfl
  rw [hrate]
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ hw', hρs, hρq]
    nlinarith [mul_nonneg (mul_nonneg hc hws.le) (sub_nonneg.2 hq)]
  · rw [div_le_iff₀ hw', hρs, hρq]
    nlinarith [mul_nonneg hw.le (sub_nonneg.2 hq)]
  · intro hlt
    rw [div_lt_iff₀ hw', hρs, hρq]
    nlinarith [mul_pos hw (sub_pos.2 hlt)]

end Stage

section Cores6

variable {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [∀ i, Nonempty (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]

/-- facts about index runs used for the tie analysis -/
structure RunFacts (B : SemiMarkovBandit n X) (seq : List (Σ i, X i)) (γ : (Σ i, X i) → ℝ) : Prop where
  red : ∀ k (hk : k < seq.length), B.stageAfter (seq.take (k + 1)) = (B.stageAfter (seq.take k)).reduce seq[k]
  hM : ∀ k (hk : k < seq.length), γ seq[k] = (B.stageAfter (seq.take k)).rate seq[k]
  pos : ∀ k q, q ∈ (B.stageAfter (seq.take k)).alive → ∃ p, ∃ hp : p < seq.length, k ≤ p ∧ seq[p] = q
  alive_of_le : ∀ k p (hp : p < seq.length), k ≤ p → seq[p] ∈ (B.stageAfter (seq.take k)).alive
  anti : ∀ a b (ha : a < seq.length) (hb : b < seq.length), a ≤ b → γ seq[b] ≤ γ seq[a]
  tie : ∀ k p (hk : k < seq.length) (hp : p < seq.length), k ≤ p → γ seq[p] = γ seq[k] →
    (B.stageAfter (seq.take k)).rate seq[p] = γ seq[k]

lemma runFacts (B : SemiMarkovBandit n X) (seq : List (Σ i, X i)) (γ : (Σ i, X i) → ℝ)
    (hrun : B.IsIndexRun seq γ) : RunFacts B seq γ := by
  have hnd := hrun.1
  have hred : ∀ k (hk : k < seq.length), B.stageAfter (seq.take (k + 1)) = (B.stageAfter (seq.take k)).reduce seq[k] := by
    intro k hk; rw [SemiMarkovBandit.take_succ_eq seq k hk, B.stageAfter_snoc]
  have hM : ∀ k (hk : k < seq.length), γ seq[k] = (B.stageAfter (seq.take k)).rate seq[k] :=
    fun k hk => (hrun.2.2 k hk).2.2
  have hpos : ∀ k q, q ∈ (B.stageAfter (seq.take k)).alive → ∃ p, ∃ hp : p < seq.length, k ≤ p ∧ seq[p] = q := by
    intro k q hq
    rw [B.stageAfter_alive] at hq
    obtain ⟨p, hp, hpq⟩ := List.mem_iff_getElem.1 (hrun.2.1 q)
    refine ⟨p, hp, ?_, hpq⟩
    by_contra h
    push_neg at h
    apply hq
    rw [← hpq]
    exact List.mem_iff_getElem.2 ⟨p, by simp; omega, by simp⟩
  have halive : ∀ k p (hp : p < seq.length), k ≤ p → seq[p] ∈ (B.stageAfter (seq.take k)).alive := by
    intro k p hp hkp
    rw [B.stageAfter_alive]
    intro h
    obtain ⟨i, hi, hiq⟩ := List.mem_iff_getElem.1 h
    rw [List.getElem_take] at hiq
    have hi' : i < k := (by simpa using hi : i < k ∧ i < seq.length).1
    have : i = p := (hnd.getElem_inj_iff).1 hiq
    omega
  have hstep : ∀ k (hk : k + 1 < seq.length), γ seq[k + 1] ≤ γ seq[k] := by
    intro k hk
    have hk0 : k < seq.length := by omega
    obtain ⟨hal1, _, _⟩ := hrun.2.2 (k + 1) hk
    rw [hred k hk0] at hal1
    have hq : seq[k + 1] ∈ (B.stageAfter (seq.take k)).alive := (Finset.mem_erase.1 hal1).2
    have hmx := (hrun.2.2 k hk0).2.1 _ hq
    have hv := B.stageAfter_valid (seq.take k)
    have := (Stage.rate_reduce_bounds B.β_pos hv seq[k] seq[k + 1] hmx).2.1
    rw [hM (k + 1) hk, hred k hk0, hM k hk0]
    exact this
  have hanti : ∀ a b (ha : a < seq.length) (hb : b < seq.length), a ≤ b → γ seq[b] ≤ γ seq[a] := by
    intro a b ha hb hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hab ih =>
      have hb0 : b < seq.length := by omega
      exact (hstep b hb).trans (ih hb0)
  have htie : ∀ d k p, p = k + d → ∀ (hk : k < seq.length) (hp : p < seq.length),
      γ seq[p] = γ seq[k] → (B.stageAfter (seq.take k)).rate seq[p] = γ seq[k] := by
    intro d
    induction d with
    | zero =>
      intro k p hpk hk hp _
      have hpk' : p = k := by omega
      have hse : seq[p] = seq[k] := by simp [hpk']
      rw [hse]
      exact (hM k hk).symm
    | succ d ih =>
      intro k p hpk hk hp hγ
      have hk1 : k + 1 < seq.length := by omega
      have hq := halive k p hp (by omega)
      have hmx := (hrun.2.2 k hk).2.1 _ hq
      have hMk := hM k hk
      by_contra hne
      have hlt : (B.stageAfter (seq.take k)).rate seq[p] < (B.stageAfter (seq.take k)).rate seq[k] := by
        rw [hMk] at hne
        exact lt_of_le_of_ne hmx hne
      have hv := B.stageAfter_valid (seq.take k)
      have hb := (Stage.rate_reduce_bounds B.β_pos hv seq[k] seq[p] hmx).2.2 hlt
      rw [← hred k hk] at hb
      have h1 := hanti (k + 1) p hk1 hp (by omega)
      have h2 := hstep k hk1
      have h3 : γ seq[k + 1] = γ seq[k] := le_antisymm h2 (by rw [← hγ]; exact h1)
      have := ih (k + 1) p (by omega) hk1 hp (by rw [hγ, h3])
      rw [h3] at this
      rw [this, ← hMk] at hb
      exact lt_irrefl _ hb
  exact ⟨hred, hM, hpos, halive, hanti, fun k p hk hp hkp hγ => htie (p - k) k p (by omega) hk hp hγ⟩

end Cores6

section Cores7

variable {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [∀ i, Nonempty (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]

theorem goal_core (B : SemiMarkovBandit n X)
    (seq : List (Σ i, X i)) (γ : (Σ i, X i) → ℝ) (hrun : B.IsIndexRun seq γ)
    (rank : (Σ i, X i) → ℕ)
    (hcompat : ∀ x y : Σ i, X i, γ y < γ x → rank y < rank x)
    (π : Policy n X) (hπ : FollowsRank rank π) : B.IsOptimal π := by
  have F := runFacts B seq γ hrun
  have key : ∀ m k, k + m = seq.length → ∀ z ∈ (B.stageAfter (seq.take k)).Dom,
      (B.stageAfter (seq.take k)).Tj (π z) (B.stageAfter (seq.take k)).vstar z =
        (B.stageAfter (seq.take k)).vstar z := by
    intro m
    induction m with
    | zero =>
      intro k hk z hz
      exfalso
      have hk' : k = seq.length := by omega
      have h0 := hz (0 : Fin n)
      rw [B.stageAfter_alive, hk', List.take_length] at h0
      exact h0 (hrun.2.1 _)
    | succ m ih =>
      intro k hk z hz
      have hlt : k < seq.length := by omega
      obtain ⟨halive, hmax, _⟩ := hrun.2.2 k hlt
      have hv := B.stageAfter_valid (seq.take k)
      obtain ⟨κ, hr⟩ := hv.reg B.β_pos
      have hred := F.red k hlt
      have hv' := Stage.Valid.reduce B.β_pos hv seq[k]
      obtain ⟨κ', hr'⟩ := hv'.reg B.β_pos
      have hqa := hz (π z)
      obtain ⟨p, hp, hkp, hpq⟩ := F.pos k _ hqa
      have hγle := F.anti k p hlt hp hkp
      rcases eq_or_lt_of_le hγle with heq | hlt2
      · -- tie with the picked state: the policy's choice has maximal rate
        have hrate := F.tie k p hlt hp hkp heq
        rw [hpq] at hrate
        refine Stage.topA B.β_pos hv hr ⟨π z, z (π z)⟩ hqa ?_ z hz rfl
        intro q' hq'
        have := hmax q' hq'
        rw [F.hM k hlt] at hrate
        rw [hrate]
        exact this
      · have hzs : z (seq[k]).1 ≠ (seq[k]).2 := by
          intro hzs
          have hr1 := hπ z (seq[k]).1
          have hss : (⟨(seq[k]).1, z (seq[k]).1⟩ : Σ i, X i) = seq[k] := Sigma.ext rfl (heq_of_eq hzs)
          rw [hss] at hr1
          have hc := hcompat seq[k] ⟨π z, z (π z)⟩ (by rw [← hpq]; exact hlt2)
          omega
        have hzD := Dom_reduce_of_ne seq[k] z hz hzs
        have := ih (k + 1) (by omega) z (by rw [hred]; exact hzD)
        rw [hred] at this
        obtain ⟨h1, h2⟩ := Stage.translate B.β_pos hv hr seq[k] hr' halive hmax z hzD
        rw [h2 (π z), h1] at this
        exact this
  apply optimal_of_greedy
  intro z
  have := key seq.length 0 (by omega) z (fun i => by
    rw [B.stageAfter_alive]; simp)
  rw [List.take_zero] at this
  exact this

end Cores7

lemma comm_alg (α β' u v qa qb rq ra rb : ℝ) (hα : 0 < 1 - α) (hβ : 0 < 1 - β')
    (hΔ : 0 < (1 - α) * (1 - β') - u * v) :
    (rq + qa / (1 - α) * ra) + ((qb + qa / (1 - α) * u) / (1 - (β' + v / (1 - α) * u))) * (rb + v / (1 - α) * ra) =
    (rq + qb / (1 - β') * rb) + ((qa + qb / (1 - β') * v) / (1 - (α + u / (1 - β') * v))) * (ra + u / (1 - β') * rb) := by
  have h1 : 1 - (β' + v / (1 - α) * u) = ((1 - α) * (1 - β') - u * v) / (1 - α) := by
    field_simp; ring
  have h2 : 1 - (α + u / (1 - β') * v) = ((1 - α) * (1 - β') - u * v) / (1 - β') := by
    field_simp; ring
  rw [h1, h2]
  have hα' := hα.ne'
  have hβ' := hβ.ne'
  have hΔ' := hΔ.ne'
  field_simp
  ring

namespace Stage

variable {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

lemma ext' {S T : Stage n X} (h1 : S.alive = T.alive) (h2 : S.ρ = T.ρ) (h3 : S.w = T.w)
    (h4 : S.D = T.D) : S = T := by
  cases S; cases T; simp_all

lemma reduce_comm {β : ℝ} (hβ : 0 < β) {S : Stage n X} (hv : S.Valid β) (a b : Σ i, X i)
    (hab : a ≠ b) : (S.reduce a).reduce b = (S.reduce b).reduce a := by
  have hba : b ≠ a := Ne.symm hab
  have hα : 0 < 1 - S.D a a := sub_pos.2 (Dss_lt hβ hv a)
  have hβ' : 0 < 1 - S.D b b := sub_pos.2 (Dss_lt hβ hv b)
  have hΔ : 0 < (1 - S.D a a) * (1 - S.D b b) - S.D a b * S.D b a := by
    have h := Dss_lt hβ (Valid.reduce hβ hv a) b
    have h' : (S.reduce a).D b b = S.D b b + S.D b a / (1 - S.D a a) * S.D a b := by
      show (if b = a then 0 else S.D b b + S.D b a / (1 - S.D a a) * S.D a b) = _
      rw [if_neg hba]
    rw [h'] at h
    have e : (1 - S.D a a) * (1 - S.D b b) - S.D a b * S.D b a =
        (1 - S.D a a) * (1 - (S.D b b + S.D b a / (1 - S.D a a) * S.D a b)) := by
      field_simp; ring
    rw [e]
    exact mul_pos hα (sub_pos.2 h)
  have hΔ' : 0 < (1 - S.D b b) * (1 - S.D a a) - S.D b a * S.D a b := by nlinarith
  apply ext'
  · exact Finset.erase_right_comm
  · funext q
    show (S.ρ q + S.D q a / (1 - S.D a a) * S.ρ a) +
        (if b = a then 0 else S.D q b + S.D q a / (1 - S.D a a) * S.D a b) /
          (1 - (if b = a then 0 else S.D b b + S.D b a / (1 - S.D a a) * S.D a b)) *
        (S.ρ b + S.D b a / (1 - S.D a a) * S.ρ a) =
      (S.ρ q + S.D q b / (1 - S.D b b) * S.ρ b) +
        (if a = b then 0 else S.D q a + S.D q b / (1 - S.D b b) * S.D b a) /
          (1 - (if a = b then 0 else S.D a a + S.D a b / (1 - S.D b b) * S.D b a)) *
        (S.ρ a + S.D a b / (1 - S.D b b) * S.ρ b)
    rw [if_neg hba, if_neg hba, if_neg hab, if_neg hab]
    exact comm_alg _ _ _ _ _ _ _ _ _ hα hβ' hΔ
  · funext q
    show (S.w q + S.D q a / (1 - S.D a a) * S.w a) +
        (if b = a then 0 else S.D q b + S.D q a / (1 - S.D a a) * S.D a b) /
          (1 - (if b = a then 0 else S.D b b + S.D b a / (1 - S.D a a) * S.D a b)) *
        (S.w b + S.D b a / (1 - S.D a a) * S.w a) =
      (S.w q + S.D q b / (1 - S.D b b) * S.w b) +
        (if a = b then 0 else S.D q a + S.D q b / (1 - S.D b b) * S.D b a) /
          (1 - (if a = b then 0 else S.D a a + S.D a b / (1 - S.D b b) * S.D b a)) *
        (S.w a + S.D a b / (1 - S.D b b) * S.w b)
    rw [if_neg hba, if_neg hba, if_neg hab, if_neg hab]
    exact comm_alg _ _ _ _ _ _ _ _ _ hα hβ' hΔ
  · funext q p
    simp only [Stage.reduce]
    by_cases hpb : p = b
    · subst hpb
      simp [hba, hab]
    · by_cases hpa : p = a
      · subst hpa
        simp [hba, hab]
      · simp only [if_neg hpa, if_neg hpb, if_neg hba, if_neg hab]
        exact comm_alg _ _ _ _ _ _ _ _ _ hα hβ' hΔ

end Stage

section Swap

variable {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [∀ i, Nonempty (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]

lemma stageAfter_swap (B : SemiMarkovBandit n X) (L T : List (Σ i, X i)) (a b : Σ i, X i) (hab : a ≠ b) :
    B.stageAfter (L ++ b :: a :: T) = B.stageAfter (L ++ a :: b :: T) := by
  have e1 : L ++ b :: a :: T = (L ++ [b, a]) ++ T := by simp
  have e2 : L ++ a :: b :: T = (L ++ [a, b]) ++ T := by simp
  have h1 : ∀ (M : List (Σ i, X i)), B.stageAfter (M ++ T) = T.foldl Stage.reduce (B.stageAfter M) := by
    intro M; unfold SemiMarkovBandit.stageAfter; rw [List.foldl_append]
  rw [e1, e2, h1, h1]
  congr 1
  have e3 : ∀ c d : Σ i, X i, B.stageAfter (L ++ [c, d]) = ((B.stageAfter L).reduce c).reduce d := by
    intro c d
    have : L ++ [c, d] = (L ++ [c]) ++ [d] := by simp
    rw [this, B.stageAfter_snoc, B.stageAfter_snoc]
  rw [e3, e3]
  exact (Stage.reduce_comm B.β_pos (B.stageAfter_valid L) a b hab).symm

lemma seq_decomp (l : List (Σ i, X i)) (k : ℕ) (hk : k + 1 < l.length) :
    l = l.take k ++ l[k] :: l[k + 1] :: l.drop (k + 2) := by
  have h1 := SemiMarkovBandit.take_succ_eq l k (by omega)
  have h2 := SemiMarkovBandit.take_succ_eq l (k + 1) hk
  have h3 := List.take_append_drop (k + 2) l
  rw [h2, h1] at h3
  simpa using h3.symm

end Swap

section Swap2

variable {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [∀ i, Nonempty (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]

lemma swap_run (B : SemiMarkovBandit n X) (seq : List (Σ i, X i)) (γ : (Σ i, X i) → ℝ)
    (hrun : B.IsIndexRun seq γ) (k : ℕ) (hk : k + 1 < seq.length)
    (htie : γ seq[k + 1] = γ seq[k]) :
    ∃ seq' : List (Σ i, X i), B.IsIndexRun seq' γ ∧ seq'.length = seq.length ∧
      (∀ i (hi : i < k) (h1 : i < seq.length) (h2 : i < seq'.length), seq'[i] = seq[i]) ∧
      (∃ h : k < seq'.length, seq'[k] = seq[k + 1]) ∧ (∃ h : k + 1 < seq'.length, seq'[k + 1] = seq[k]) := by
  have F := runFacts B seq γ hrun
  have hnd := hrun.1
  have hk0 : k < seq.length := by omega
  have hab : seq[k] ≠ seq[k + 1] := by
    intro h
    have := (hnd.getElem_inj_iff).1 h
    omega
  have hdec := seq_decomp seq k hk
  set P := seq.take k with hPdef
  set R := seq.drop (k + 2) with hRdef
  set a := seq[k] with hadef
  set b := seq[k + 1] with hbdef
  have hP : P.length = k := by simp [hPdef]; omega
  have hR : R.length = seq.length - (k + 2) := by simp [hRdef]
  set seq' : List (Σ i, X i) := P ++ b :: a :: R with hseq'
  have hperm : seq'.Perm seq := by
    have h1 : seq'.Perm (P ++ a :: b :: R) := List.Perm.append_left _ (List.Perm.swap a b R)
    rw [← hdec] at h1
    exact h1
  have hlen : seq'.length = seq.length := hperm.length_eq
  have hnd' : seq'.Nodup := hperm.nodup_iff.2 hnd
  have hall' : ∀ q, q ∈ seq' := fun q => hperm.mem_iff.2 (hrun.2.1 q)
  have htake_lt : ∀ j, j ≤ k → seq'.take j = seq.take j := by
    intro j hj
    rw [hseq', List.take_append_of_le_length (by omega), hPdef, List.take_take]
    congr 1; omega
  have htake_k1 : seq'.take (k + 1) = P ++ [b] := by
    rw [hseq', List.take_append]
    have : P.take (k + 1) = P := List.take_of_length_le (by omega)
    rw [this]
    have : (k + 1 - P.length) = 1 := by omega
    rw [this]; simp
  have hS : B.stageAfter (seq'.take k) = B.stageAfter P := by rw [htake_lt k le_rfl]
  have hget_lt : ∀ j (hj : j < k) (h2 : j < seq'.length) (h1 : j < seq.length), seq'[j] = seq[j] := by
    intro j hj h2 h1
    have : seq'[j] = P[j]'(by omega) := List.getElem_append_left (by omega)
    exact this.trans (List.getElem_take ..)
  have hget_k : seq'[k]'(by omega) = b :=
    (List.getElem_append_right (as := P) (bs := b :: a :: R) (i := k) (by omega)).trans
      (by simp [hP])
  have hget_k1 : seq'[k + 1]'(by omega) = a :=
    (List.getElem_append_right (as := P) (bs := b :: a :: R) (i := k + 1) (by omega)).trans
      (by simp [hP])
  have hget_ge : ∀ j (hj : k + 2 ≤ j) (h2 : j < seq'.length) (h1 : j < seq.length), seq'[j] = seq[j] := by
    intro j hj h2 h1
    obtain ⟨t, rfl⟩ : ∃ t, j = k + 2 + t := ⟨j - (k + 2), by omega⟩
    have e1 : seq'[k + 2 + t] = (b :: a :: R)[k + 2 + t - P.length]'(by simp only [List.length_cons]; omega) :=
      List.getElem_append_right (by omega)
    have e2 : seq[k + 2 + t] = (a :: b :: R)[k + 2 + t - P.length]'(by simp only [List.length_cons]; omega) :=
      (List.getElem_of_eq hdec h1).trans (List.getElem_append_right (by omega))
    rw [e1, e2]
    have : k + 2 + t - P.length = t + 2 := by omega
    simp only [this]
    simp
  have htake_ge : ∀ j, k + 2 ≤ j → j ≤ seq.length →
      B.stageAfter (seq'.take j) = B.stageAfter (seq.take j) := by
    intro j hj hjl
    have e1 : seq'.take j = P ++ b :: a :: R.take (j - k - 2) := by
      rw [hseq', List.take_append]
      have : P.take j = P := List.take_of_length_le (by omega)
      rw [this]
      have : j - P.length = (j - k - 2) + 2 := by omega
      rw [this]; simp
    have e2 : seq.take j = P ++ a :: b :: R.take (j - k - 2) := by
      conv_lhs => rw [hdec]
      rw [List.take_append]
      have : P.take j = P := List.take_of_length_le (by omega)
      rw [this]
      have : j - P.length = (j - k - 2) + 2 := by omega
      rw [this]; simp
    rw [e1, e2]
    exact stageAfter_swap B P (R.take (j - k - 2)) a b hab
  refine ⟨seq', ⟨hnd', hall', ?_⟩, hlen, ?_, ⟨by omega, hget_k⟩, ⟨by omega, hget_k1⟩⟩
  · intro j hj
    have hj0 : j < seq.length := by rw [← hlen]; exact hj
    rcases lt_trichotomy j k with hjk | hjk | hjk
    · rw [hget_lt j hjk hj hj0, htake_lt j hjk.le]
      exact hrun.2.2 j hj0
    · have hjk' : k = j := hjk.symm
      subst hjk'
      rw [hget_k, hS]
      obtain ⟨hal, hmx, hMk⟩ := hrun.2.2 k hk0
      have htie' := F.tie k (k + 1) hk0 hk (Nat.le_succ k) htie
      refine ⟨F.alive_of_le k (k + 1) hk (Nat.le_succ k), fun q hq => ?_, htie.trans htie'.symm⟩
      calc _ ≤ (B.stageAfter P).rate a := hmx q hq
        _ = γ a := hMk.symm
        _ = _ := htie'.symm
    · rcases Nat.lt_or_ge j (k + 2) with hj2 | hj2
      · have hjk' : k + 1 = j := by omega
        subst hjk'
        rw [hget_k1, htake_k1, B.stageAfter_snoc]
        obtain ⟨hal, hmx, hMk⟩ := hrun.2.2 k hk0
        have htie' := F.tie k (k + 1) hk0 hk (Nat.le_succ k) htie
        have hv := B.stageAfter_valid P
        have hrab : (B.stageAfter P).rate a = (B.stageAfter P).rate b := by
          rw [htie', hMk]
        have hb1 := (Stage.rate_reduce_bounds B.β_pos hv b a hrab.le)
        refine ⟨Finset.mem_erase.2 ⟨hab, hal⟩, fun q hq => ?_, ?_⟩
        · have hqS : q ∈ (B.stageAfter P).alive := (Finset.mem_erase.1 hq).2
          have hqb : (B.stageAfter P).rate q ≤ (B.stageAfter P).rate b := by
            rw [← hrab]; exact hmx q hqS
          have := (Stage.rate_reduce_bounds B.β_pos hv b q hqb).2.1
          exact this.trans (hrab.symm.trans_le hb1.1)
        · apply le_antisymm
          · rw [hMk]; exact hb1.1
          · rw [hMk]; exact (hrab ▸ hb1.2.1)
      · rw [hget_ge j hj2 hj hj0, htake_ge j hj2 hj0.le]
        exact hrun.2.2 j hj0
  · intro i hi h1 h2
    exact hget_lt i hi h2 h1

end Swap2

section Picked

variable {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [∀ i, Nonempty (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]

lemma bubble_step (B : SemiMarkovBandit n X) (seq : List (Σ i, X i)) (γ : (Σ i, X i) → ℝ)
    (hrun : B.IsIndexRun seq γ) (x y : Σ i, X i) (hγ : γ x = γ y)
    (hlt : seq.idxOf y < seq.idxOf x) :
    ∃ seq1 : List (Σ i, X i), B.IsIndexRun seq1 γ ∧ seq1.idxOf x + 1 = seq.idxOf x ∧
      (seq.idxOf y + 1 < seq.idxOf x → seq1.idxOf y = seq.idxOf y) ∧
      (seq.idxOf y + 1 = seq.idxOf x → seq1.idxOf y = seq.idxOf x) := by
  have F := runFacts B seq γ hrun
  have hnd := hrun.1
  have hxl : seq.idxOf x < seq.length := List.idxOf_lt_length_iff.2 (hrun.2.1 x)
  have hyl : seq.idxOf y < seq.length := List.idxOf_lt_length_iff.2 (hrun.2.1 y)
  obtain ⟨k, hk⟩ : ∃ k, seq.idxOf x = k + 1 := ⟨seq.idxOf x - 1, by omega⟩
  have hk1 : k + 1 < seq.length := by omega
  have hk0 : k < seq.length := by omega
  have hxe : seq[k + 1] = x := by
    have := List.getElem_idxOf (x := x) (xs := seq) hxl
    simpa [hk] using this
  have hye : seq[seq.idxOf y] = y := List.getElem_idxOf hyl
  have htie : γ seq[k + 1] = γ seq[k] := by
    have h1 := F.anti (seq.idxOf y) k hyl hk0 (by omega)
    have h2 := F.anti k (k + 1) hk0 hk1 (by omega)
    rw [hye] at h1
    rw [hxe] at h2 ⊢
    linarith
  obtain ⟨seq1, hrun1, hlen1, hlt1, ⟨hk1', hgk⟩, ⟨hk2', hgk1⟩⟩ := swap_run B seq γ hrun k hk1 htie
  have hnd1 := hrun1.1
  have hix : seq1.idxOf x = k := by
    have := hnd1.idxOf_getElem k hk1'
    rw [hgk, hxe] at this
    exact this
  refine ⟨seq1, hrun1, by omega, fun h => ?_, fun h => ?_⟩
  · have hi : seq.idxOf y < k := by omega
    have := hnd1.idxOf_getElem (seq.idxOf y) (by omega)
    rw [hlt1 _ hi hyl (by omega), hye] at this
    exact this
  · have hyk : seq.idxOf y = k := by omega
    have := hnd1.idxOf_getElem (k + 1) hk2'
    have hyy : seq[k] = y := by simpa [hyk] using hye
    rw [hgk1, hyy] at this
    omega

lemma bubble (B : SemiMarkovBandit n X) (γ : (Σ i, X i) → ℝ) :
    ∀ d (seq : List (Σ i, X i)), B.IsIndexRun seq γ → ∀ x y : Σ i, X i, γ x = γ y →
      seq.idxOf y + d + 1 = seq.idxOf x → ∃ seq', B.IsIndexRun seq' γ ∧ seq'.idxOf x < seq'.idxOf y := by
  intro d
  induction d with
  | zero =>
    intro seq hrun x y hγ hd
    obtain ⟨seq1, hrun1, h1, _, h3⟩ := bubble_step B seq γ hrun x y hγ (by omega)
    exact ⟨seq1, hrun1, by have := h3 (by omega); omega⟩
  | succ d ih =>
    intro seq hrun x y hγ hd
    obtain ⟨seq1, hrun1, h1, h2, _⟩ := bubble_step B seq γ hrun x y hγ (by omega)
    exact ih seq1 hrun1 x y hγ (by have := h2 (by omega); omega)

theorem picked_core (B : SemiMarkovBandit n X)
    (seq : List (Σ i, X i)) (γ : (Σ i, X i) → ℝ) (hrun : B.IsIndexRun seq γ)
    (x y : Σ i, X i) (hxy : x ≠ y) :
    γ y ≤ γ x ↔ ∃ seq' : List (Σ i, X i), B.IsIndexRun seq' γ ∧ seq'.idxOf x < seq'.idxOf y := by
  constructor
  · intro hle
    by_cases h : seq.idxOf x < seq.idxOf y
    · exact ⟨seq, hrun, h⟩
    · have hne : seq.idxOf y ≠ seq.idxOf x := fun h' => hxy ((List.idxOf_inj (hrun.2.1 x)).1 h'.symm)
      have hlt : seq.idxOf y < seq.idxOf x := by omega
      have F := runFacts B seq γ hrun
      have hxl : seq.idxOf x < seq.length := List.idxOf_lt_length_iff.2 (hrun.2.1 x)
      have hyl : seq.idxOf y < seq.length := List.idxOf_lt_length_iff.2 (hrun.2.1 y)
      have h1 := F.anti (seq.idxOf y) (seq.idxOf x) hyl hxl hlt.le
      rw [List.getElem_idxOf, List.getElem_idxOf] at h1
      exact bubble B γ (seq.idxOf x - seq.idxOf y - 1) seq hrun x y (le_antisymm h1 hle) (by omega)
  · rintro ⟨seq', hrun', hlt⟩
    have F := runFacts B seq' γ hrun'
    have hxl : seq'.idxOf x < seq'.length := List.idxOf_lt_length_iff.2 (hrun'.2.1 x)
    have hyl : seq'.idxOf y < seq'.length := List.idxOf_lt_length_iff.2 (hrun'.2.1 y)
    have h1 := F.anti (seq'.idxOf x) (seq'.idxOf y) hxl hyl hlt.le
    rwa [List.getElem_idxOf, List.getElem_idxOf] at h1

end Picked

end TsitsiklisGittins.IndexTheorem

open TsitsiklisGittins.IndexTheorem


theorem solution {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    [∀ i, Nonempty (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (B : SemiMarkovBandit n X)
    (seq : List (Σ i, X i)) (γ : (Σ i, X i) → ℝ) (hrun : B.IsIndexRun seq γ)
    (x y : Σ i, X i) (hxy : x ≠ y) :
    γ y ≤ γ x ↔ ∃ seq' : List (Σ i, X i), B.IsIndexRun seq' γ ∧ seq'.idxOf x < seq'.idxOf y := by
  exact picked_core B seq γ hrun x y hxy
