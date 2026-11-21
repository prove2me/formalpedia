-- Prove2me | solution 1 for TranspositionIID.Main.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:05:18.652114+00:00
-- url     : https://prove2.me/submissions/09e265e6-3cfc-4241-b0ac-85b4661d40d7

import Mathlib
import Definitions.Def_TranspositionIID_Main_Stationary
import Definitions.Def_TranspositionIID_Main_Entropy
import Definitions.Def_TranspositionIID_Main_Auxiliary
import Definitions.Def_TranspositionIID_Main_Buffer
import Theorems.Thm_TranspositionIID_Main_proposition_3_4
import Theorems.Thm_TranspositionIID_Main_lemma_2_1
import Theorems.Thm_TranspositionIID_Main_lemma_2_2

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.Rev
open TranspositionIID.Main

variable {n : ℕ}

def pr (a : Equiv.Perm (Fin n)) (i : Fin n) : Fin n :=
  ⟨(a i).val - 1, by have := (a i).isLt; omega⟩

lemma T_pos {a : Equiv.Perm (Fin n)} {i : Fin n} (h : 0 < (a i).val) :
    transposeRequest a i = a.trans (Equiv.swap (a i) (pr a i)) := by
  unfold transposeRequest; rw [dif_pos h]; rfl

lemma T_zero {a : Equiv.Perm (Fin n)} {i : Fin n} (h : ¬ 0 < (a i).val) :
    transposeRequest a i = a := by
  unfold transposeRequest; rw [dif_neg h]

lemma kernel_nonneg (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i) (a b : Equiv.Perm (Fin n)) :
    0 ≤ transpositionKernel q a b :=
  Finset.sum_nonneg fun i _ => by split_ifs <;> simp [hq i]

lemma kernel_row (q : Fin n → ℝ) (a : Equiv.Perm (Fin n)) :
    ∑ b, transpositionKernel q a b = ∑ i, q i := by
  unfold transpositionKernel
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

lemma kernel_markov (q : Fin n → ℝ) (hq : ActuarialValuation.isFiniteStateDistribution q) :
    ActuarialValuation.isFiniteMarkovKernel (transpositionKernel q) :=
  ⟨kernel_nonneg q hq.1, fun a => by rw [kernel_row]; exact hq.2⟩

lemma pow_markov {S : Type*} [Fintype S] [DecidableEq S] (P : Matrix S S ℝ)
    (hP : ActuarialValuation.isFiniteMarkovKernel P) (t : ℕ) :
    (∀ a b, 0 ≤ (P ^ t) a b) ∧ ∀ a, ∑ b, (P ^ t) a b = 1 := by
  induction t with
  | zero =>
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · simp [Matrix.one_apply]; split_ifs <;> simp
    · simp [Matrix.one_apply]
  | succ t ih =>
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun c _ => mul_nonneg (ih.1 a c) (hP.1 c b)
    · rw [pow_succ]
      simp only [Matrix.mul_apply]
      rw [Finset.sum_comm]
      calc ∑ c, ∑ b, (P ^ t) a c * P c b = ∑ c, (P ^ t) a c := by
            apply Finset.sum_congr rfl; intro c _
            rw [← Finset.mul_sum, hP.2 c, mul_one]
        _ = 1 := ih.2 a

lemma weight_swap (q : Fin n → ℝ) (a : Equiv.Perm (Fin n)) (i : Fin n) (h : 0 < (a i).val) :
    stationaryWeight q (a.trans (Equiv.swap (a i) (pr a i))) * q (a.symm (pr a i)) =
      stationaryWeight q a * q i := by
  set j := a.symm (pr a i) with hj
  have haj : a j = pr a i := by simp [hj]
  have hji : j ≠ i := by
    intro e; rw [e] at haj
    have := congrArg Fin.val haj
    simp [pr] at this; omega
  set z := a.trans (Equiv.swap (a i) (pr a i)) with hz
  have hzi : z i = pr a i := by simp [hz]
  have hzj : z j = a i := by simp [hz, haj]
  have hzk : ∀ k, k ≠ i → k ≠ j → z k = a k := by
    intro k hki hkj
    simp only [hz, Equiv.trans_apply]
    apply Equiv.swap_apply_of_ne_of_ne
    · intro e; exact hki (a.injective e)
    · intro e; apply hkj; rw [← haj] at e; exact a.injective e
  have hprv : (pr a i).val = (a i).val - 1 := rfl
  have hlt := (a i).isLt
  unfold stationaryWeight
  have hmem_i : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  have hmem_j : j ∈ (Finset.univ : Finset (Fin n)).erase i := by simp [hji]
  rw [← Finset.mul_prod_erase _ _ hmem_i, ← Finset.mul_prod_erase _ _ hmem_i,
    ← Finset.mul_prod_erase _ _ hmem_j, ← Finset.mul_prod_erase _ _ hmem_j]
  have hrest : ∏ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase j, q k ^ (n - 1 - (z k).val) =
      ∏ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase j, q k ^ (n - 1 - (a k).val) := by
    apply Finset.prod_congr rfl
    intro k hk
    simp only [Finset.mem_erase] at hk
    rw [hzk k hk.2.1 hk.1]
  rw [hrest, hzi, hzj, haj]
  have e1 : n - 1 - (pr a i).val = (n - 1 - (a i).val) + 1 := by rw [hprv]; omega
  have e2 : n - 1 - (a i).val + 1 = n - 1 - (pr a i).val := e1.symm
  rw [e1, pow_succ]
  ring

lemma detailed_balance_ne (q : Fin n → ℝ) (a z : Equiv.Perm (Fin n)) (hne : z ≠ a) :
    stationaryWeight q a * transpositionKernel q a z =
      stationaryWeight q z * transpositionKernel q z a := by
  unfold transpositionKernel
  rw [Finset.mul_sum, Finset.mul_sum]
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  have key : ∀ i, transposeRequest a i = z → 0 < (a i).val := by
    intro i hi; by_contra h; rw [T_zero h] at hi; exact hne hi.symm
  have key2 : ∀ k, transposeRequest z k = a → 0 < (z k).val := by
    intro k hk; by_contra h; rw [T_zero h] at hk; exact hne hk
  have fwd : ∀ i, transposeRequest a i = z →
      transposeRequest z (a.symm (pr a i)) = a ∧ z (a.symm (pr a i)) = a i := by
    intro i hi
    have hp := key i hi
    rw [T_pos hp] at hi
    subst hi
    have hzk : (a.trans (Equiv.swap (a i) (pr a i))) (a.symm (pr a i)) = a i := by simp
    refine ⟨?_, hzk⟩
    rw [T_pos (by rw [hzk]; exact hp), hzk]
    have : pr (a.trans (Equiv.swap (a i) (pr a i))) (a.symm (pr a i)) = pr a i := by
      simp only [pr]; congr 1; simp
    rw [this]
    ext m; simp
  have bwd : ∀ k, transposeRequest z k = a →
      transposeRequest a (a.symm (z k)) = z ∧ a (a.symm (pr z k)) = pr z k ∧ a k = pr z k := by
    intro k hk
    have hp := key2 k hk
    rw [T_pos hp] at hk
    have hak : a k = pr z k := by
      rw [← hk]; simp
    have hz : z = a.trans (Equiv.swap (z k) (pr z k)) := by
      rw [← hk]; ext m; simp
    refine ⟨?_, by simp, hak⟩
    have h1 : a (a.symm (z k)) = z k := by simp
    have hp' : 0 < (a (a.symm (z k))).val := by rw [h1]; exact hp
    rw [T_pos hp']
    have : pr a (a.symm (z k)) = pr z k := by
      simp only [pr]; congr 1; rw [h1]
    rw [this, h1]
    exact hz.symm
  refine Finset.sum_bij' (fun i _ => a.symm (pr a i)) (fun k _ => a.symm (z k)) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact (fwd i hi).1
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact (bwd k hk).1
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [(fwd i hi).2]
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    have := (bwd k hk).2.2
    have h2 : pr a (a.symm (z k)) = pr z k := by
      simp only [pr]; congr 1; simp
    show a.symm (pr a (a.symm (z k))) = k
    rw [h2, ← this]; simp
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hp := key i hi
    have := weight_swap q a i hp
    rw [← T_pos hp, hi] at this
    exact this.symm

lemma weight_pos (q : Fin n → ℝ) (hpos : ∀ i, 0 < q i) (a : Equiv.Perm (Fin n)) :
    0 < stationaryWeight q a :=
  Finset.prod_pos fun i _ => pow_pos (hpos i) _

lemma partition_pos (q : Fin n → ℝ) (hpos : ∀ i, 0 < q i) : 0 < partitionFunction q :=
  Finset.sum_pos (fun a _ => weight_pos q hpos a) Finset.univ_nonempty

lemma law_pos (q : Fin n → ℝ) (hpos : ∀ i, 0 < q i) (a : Equiv.Perm (Fin n)) :
    0 < stationaryLaw q a :=
  div_pos (weight_pos q hpos a) (partition_pos q hpos)

lemma reversible_stationary (q : Fin n → ℝ)
    (hq : ActuarialValuation.isFiniteStateDistribution q) (hpos : ∀ i, 0 < q i) :
    ReversibleProbability (transpositionKernel q) (stationaryLaw q) := by
  have hZ := partition_pos q hpos
  have hdb : ∀ a z : Equiv.Perm (Fin n), stationaryLaw q a * transpositionKernel q a z =
      stationaryLaw q z * transpositionKernel q z a := by
    intro a z
    by_cases h : z = a
    · subst h; rfl
    · unfold stationaryLaw
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, detailed_balance_ne q a z h]
  refine ⟨⟨fun a => (law_pos q hpos a).le, ?_⟩, law_pos q hpos, ?_, hdb⟩
  · unfold stationaryLaw
    rw [← Finset.sum_div]
    exact div_self hZ.ne'
  · intro z
    calc ∑ a, stationaryLaw q a * transpositionKernel q a z
        = ∑ a, stationaryLaw q z * transpositionKernel q z a :=
          Finset.sum_congr rfl fun a _ => hdb a z
      _ = stationaryLaw q z := by
          rw [← Finset.mul_sum, kernel_row, hq.2, mul_one]

end TranspositionIID.Main.Dev.Rev
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.L42
open TranspositionIID.Main
open TranspositionIID.Main.Dev

variable {S : Type*} [Fintype S] [DecidableEq S]

lemma dirichlet_eq (P : Matrix S S ℝ) (hP : ActuarialValuation.isFiniteMarkovKernel P)
    (μ : S → ℝ) (hμ : ReversibleProbability P μ) (u v : S → ℝ) :
    GibbsCongestion.dirichletForm P μ u v =
      ∑ x, μ x * (u x - ∑ y, P x y * u y) * v x := by
  unfold GibbsCongestion.dirichletForm
  have hexp : ∀ x y, μ x * P x y * (u x - u y) * (v x - v y) =
      μ x * P x y * (u x * v x) + μ x * P x y * (u y * v y)
        - μ x * P x y * (u x * v y) - μ x * P x y * (u y * v x) := fun x y => by ring
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hexp x y]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have t1 : ∑ x, ∑ y, μ x * P x y * (u x * v x) = ∑ x, μ x * (u x * v x) := by
    apply Finset.sum_congr rfl; intro x _
    rw [← Finset.sum_mul, ← Finset.mul_sum, hP.2 x]; ring
  have t2 : ∑ x, ∑ y, μ x * P x y * (u y * v y) = ∑ y, μ y * (u y * v y) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro y _
    rw [← Finset.sum_mul, hμ.2.2.1 y]
  have t3 : ∑ x, ∑ y, μ x * P x y * (u x * v y) = ∑ x, ∑ y, μ x * P x y * (u y * v x) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro y _
    apply Finset.sum_congr rfl; intro x _
    rw [hμ.2.2.2 y x]
  have t4 : ∑ x, ∑ y, μ x * P x y * (u y * v x) = ∑ x, μ x * (∑ y, P x y * u y) * v x := by
    apply Finset.sum_congr rfl; intro x _
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro y _; ring
  rw [t1, t2, t3, t4]
  have : ∑ x, μ x * (u x - ∑ y, P x y * u y) * v x =
      ∑ x, μ x * (u x * v x) - ∑ x, μ x * (∑ y, P x y * u y) * v x := by
    rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro x _; ring
  rw [this]; ring

end TranspositionIID.Main.Dev.L42
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.L41
open TranspositionIID.Main TranspositionIID.Main.Dev TranspositionIID.Main.Dev.L42

variable {S : Type*} [Fintype S] [DecidableEq S]

lemma cs_weighted {X : Type*} [Fintype X] (w a b : X → ℝ) (hw : ∀ z, 0 ≤ w z) :
    (∑ z, w z * a z * b z) ^ 2 ≤ (∑ z, w z * a z ^ 2) * (∑ z, w z * b z ^ 2) := by
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun z => Real.sqrt (w z) * a z)
    (fun z => Real.sqrt (w z) * b z)
  have e1 : ∀ z, Real.sqrt (w z) * a z * (Real.sqrt (w z) * b z) = w z * a z * b z := fun z => by
    have h := Real.mul_self_sqrt (hw z)
    calc Real.sqrt (w z) * a z * (Real.sqrt (w z) * b z)
        = (Real.sqrt (w z) * Real.sqrt (w z)) * a z * b z := by ring
      _ = w z * a z * b z := by rw [h]
  have e2 : ∀ z, (Real.sqrt (w z) * a z) ^ 2 = w z * a z ^ 2 := fun z => by
    rw [mul_pow, Real.sq_sqrt (hw z)]
  have e3 : ∀ z, (Real.sqrt (w z) * b z) ^ 2 = w z * b z ^ 2 := fun z => by
    rw [mul_pow, Real.sq_sqrt (hw z)]
  simpa only [e1, e2, e3] using this

section
variable (B : Matrix S S ℝ) (μ : S → ℝ)

/-- Self-adjointness of `B` in `L²(μ)`. -/
lemma selfadj (hμ : ReversibleProbability B μ) (u v : S → ℝ) :
    ∑ z, μ z * (B.mulVec u) z * v z = ∑ z, μ z * u z * (B.mulVec v) z := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro z _
  apply Finset.sum_congr rfl; intro w _
  have := hμ.2.2.2 z w
  calc μ w * (B w z * u z) * v w = (μ w * B w z) * u z * v w := by ring
    _ = (μ z * B z w) * u z * v w := by rw [this]
    _ = μ z * u z * (B z w * v w) := by ring

lemma contraction (hB : ActuarialValuation.isFiniteMarkovKernel B) (hμ : ReversibleProbability B μ)
    (u : S → ℝ) :
    ∑ z, μ z * (B.mulVec u) z ^ 2 ≤ ∑ z, μ z * u z ^ 2 := by
  have h1 : ∀ z, (B.mulVec u) z ^ 2 ≤ ∑ w, B z w * u w ^ 2 := by
    intro z
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun w => Real.sqrt (B z w))
      (fun w => Real.sqrt (B z w) * u w)
    have e1 : ∀ w, Real.sqrt (B z w) * (Real.sqrt (B z w) * u w) = B z w * u w := fun w => by
      have h := Real.mul_self_sqrt (hB.1 z w)
      calc Real.sqrt (B z w) * (Real.sqrt (B z w) * u w)
          = (Real.sqrt (B z w) * Real.sqrt (B z w)) * u w := by ring
        _ = B z w * u w := by rw [h]
    have e2 : ∀ w, Real.sqrt (B z w) ^ 2 = B z w := fun w => Real.sq_sqrt (hB.1 z w)
    have e3 : ∀ w, (Real.sqrt (B z w) * u w) ^ 2 = B z w * u w ^ 2 := fun w => by
      rw [mul_pow, Real.sq_sqrt (hB.1 z w)]
    simp only [e1, e2, e3, hB.2 z, one_mul] at this
    simpa [Matrix.mulVec, dotProduct] using this
  calc ∑ z, μ z * (B.mulVec u) z ^ 2 ≤ ∑ z, μ z * ∑ w, B z w * u w ^ 2 :=
        Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (h1 z) (hμ.2.1 z).le
    _ = ∑ w, (∑ z, μ z * B z w) * u w ^ 2 := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro w _
        apply Finset.sum_congr rfl; intro z _; ring
    _ = ∑ w, μ w * u w ^ 2 := by
        apply Finset.sum_congr rfl; intro w _
        rw [hμ.2.2.1 w]

lemma ip_abs_le (hB : ActuarialValuation.isFiniteMarkovKernel B) (hμ : ReversibleProbability B μ)
    (u : S → ℝ) :
    |∑ z, μ z * u z * (B.mulVec u) z| ≤ ∑ z, μ z * u z ^ 2 := by
  have h := cs_weighted μ u (B.mulVec u) (fun z => (hμ.2.1 z).le)
  have h2 := contraction B μ hB hμ u
  set A := ∑ z, μ z * u z ^ 2 with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun z _ => mul_nonneg (hμ.2.1 z).le (sq_nonneg _)
  have h3 : (∑ z, μ z * u z * (B.mulVec u) z) ^ 2 ≤ A * A :=
    h.trans (mul_le_mul le_rfl h2 (Finset.sum_nonneg fun z _ => mul_nonneg (hμ.2.1 z).le (sq_nonneg _)) hA0)
  have h4 : (∑ z, μ z * u z * (B.mulVec u) z) ^ 2 ≤ A ^ 2 := by nlinarith
  exact abs_le.2 (abs_le_of_sq_le_sq' h4 hA0)

end

end TranspositionIID.Main.Dev.L41
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.L41
open TranspositionIID.Main TranspositionIID.Main.Dev TranspositionIID.Main.Dev.L42

variable {S : Type*} [Fintype S] [DecidableEq S]

section
variable (B : Matrix S S ℝ) (μ : S → ℝ)

noncomputable def ip (u v : S → ℝ) : ℝ := ∑ z, μ z * u z * v z

lemma ip_comm (u v : S → ℝ) : ip μ u v = ip μ v u := by
  unfold ip; apply Finset.sum_congr rfl; intro z _; ring

lemma E_eq (hB : ActuarialValuation.isFiniteMarkovKernel B) (hμ : ReversibleProbability B μ)
    (u v : S → ℝ) :
    GibbsCongestion.dirichletForm B μ u v = ip μ (fun z => u z - B.mulVec u z) v := by
  rw [dirichlet_eq B hB μ hμ u v]
  unfold ip
  apply Finset.sum_congr rfl; intro z _
  simp [Matrix.mulVec, dotProduct]

lemma E_nonneg (hB : ActuarialValuation.isFiniteMarkovKernel B) (hμ : ReversibleProbability B μ)
    (u : S → ℝ) : 0 ≤ GibbsCongestion.dirichletForm B μ u u := by
  unfold GibbsCongestion.dirichletForm
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg; intro x _
  apply Finset.sum_nonneg; intro y _
  have := hμ.2.1 x; have := hB.1 x y
  nlinarith [mul_nonneg (hμ.2.1 x).le (hB.1 x y), sq_nonneg (u x - u y)]

lemma E_cs (hB : ActuarialValuation.isFiniteMarkovKernel B) (hμ : ReversibleProbability B μ)
    (u v : S → ℝ) :
    GibbsCongestion.dirichletForm B μ u v ^ 2 ≤
      GibbsCongestion.dirichletForm B μ u u * GibbsCongestion.dirichletForm B μ v v := by
  have h := cs_weighted (X := S × S) (fun xy => μ xy.1 * B xy.1 xy.2)
    (fun xy => u xy.1 - u xy.2) (fun xy => v xy.1 - v xy.2)
    (fun xy => mul_nonneg (hμ.2.1 _).le (hB.1 _ _))
  simp only [Fintype.sum_prod_type] at h
  unfold GibbsCongestion.dirichletForm
  have e : ∀ (f g : S → ℝ), ∑ x, ∑ y, μ x * B x y * (f x - f y) * (g x - g y) =
      ∑ x, ∑ y, μ x * B x y * (f x - f y) * (g x - g y) := fun _ _ => rfl
  have e2 : ∀ (f : S → ℝ), ∑ x, ∑ y, μ x * B x y * (f x - f y) ^ 2 =
      ∑ x, ∑ y, μ x * B x y * (f x - f y) * (f x - f y) := fun f => by
    apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro y _; ring
  rw [e2 u, e2 v] at h
  nlinarith [h]

end

end TranspositionIID.Main.Dev.L41
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.L41
open TranspositionIID.Main TranspositionIID.Main.Dev TranspositionIID.Main.Dev.L42

variable {S : Type*} [Fintype S] [DecidableEq S]

section
variable (B : Matrix S S ℝ) (μ : S → ℝ)

lemma ip_sub_left (a b c : S → ℝ) :
    ip μ (fun z => a z - b z) c = ip μ a c - ip μ b c := by
  unfold ip; rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro z _; ring

lemma ip_sub_right (a b c : S → ℝ) :
    ip μ c (fun z => a z - b z) = ip μ c a - ip μ c b := by
  unfold ip; rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro z _; ring

lemma selfadj_ip (hμ : ReversibleProbability B μ) (u v : S → ℝ) :
    ip μ (B.mulVec u) v = ip μ u (B.mulVec v) := selfadj B μ hμ u v

lemma E_contr (hB : ActuarialValuation.isFiniteMarkovKernel B) (hμ : ReversibleProbability B μ)
    (h : S → ℝ) :
    GibbsCongestion.dirichletForm B μ (B.mulVec h) (B.mulVec h) ≤
      GibbsCongestion.dirichletForm B μ h h := by
  rw [E_eq B μ hB hμ, E_eq B μ hB hμ]
  set Bh := B.mulVec h with hBh
  set BBh := B.mulVec Bh with hBBh
  set u : S → ℝ := fun z => h z - Bh z with hu
  have hBu : B.mulVec u = fun z => Bh z - BBh z := by
    funext z
    have : u = h - Bh := by funext w; simp [hu]
    rw [this, Matrix.mulVec_sub]; rfl
  have hpsd := ip_abs_le B μ hB hμ u
  have hsq : ∑ z, μ z * u z ^ 2 = ip μ u u := by
    unfold ip; exact Finset.sum_congr rfl fun z _ => by ring
  have hA : ip μ u u + ip μ u (B.mulVec u) ≥ 0 := by
    have := (abs_le.1 hpsd).1
    rw [hsq] at this
    have e : ∑ z, μ z * u z * B.mulVec u z = ip μ u (B.mulVec u) := rfl
    rw [e] at this
    linarith
  have e1 : ip μ u u = ip μ h h - 2 * ip μ h Bh + ip μ Bh Bh := by
    simp only [hu, ip_sub_left, ip_sub_right]; rw [ip_comm μ Bh h]; ring
  have e2 : ip μ u (B.mulVec u) = ip μ h Bh - ip μ h BBh - ip μ Bh Bh + ip μ Bh BBh := by
    rw [hBu]; simp only [hu, ip_sub_left, ip_sub_right]; ring
  have e3 : ip μ h BBh = ip μ Bh Bh := (selfadj_ip B μ hμ h Bh).symm
  have e4 : ip μ (fun z => h z - Bh z) h = ip μ h h - ip μ h Bh := by
    rw [ip_sub_left, ip_comm μ Bh h]
  have e5 : ip μ (fun z => Bh z - BBh z) Bh = ip μ Bh Bh - ip μ Bh BBh := by
    rw [ip_sub_left, ip_comm μ BBh Bh]
  rw [e4, e5]
  rw [e1, e2, e3] at hA
  linarith

lemma pow_db (hμ : ReversibleProbability B μ) (k : ℕ) :
    ∀ a z, μ a * (B ^ k) a z = μ z * (B ^ k) z a := by
  induction k with
  | zero =>
    intro a z
    by_cases h : a = z
    · subst h; simp
    · simp [Matrix.one_apply, h, Ne.symm h]
  | succ k ih =>
    intro a z
    conv_lhs => rw [pow_succ]
    conv_rhs => rw [pow_succ']
    simp only [Matrix.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro c _
    calc μ a * ((B ^ k) a c * B c z) = (μ a * (B ^ k) a c) * B c z := by ring
      _ = (μ c * (B ^ k) c a) * B c z := by rw [ih a c]
      _ = (B ^ k) c a * (μ c * B c z) := by ring
      _ = (B ^ k) c a * (μ z * B z c) := by rw [hμ.2.2.2 c z]
      _ = μ z * (B z c * (B ^ k) c a) := by ring

lemma pow_rev (hB : ActuarialValuation.isFiniteMarkovKernel B) (hμ : ReversibleProbability B μ)
    (k : ℕ) : ReversibleProbability (B ^ k) μ := by
  have hmk := Rev.pow_markov B hB k
  refine ⟨hμ.1, hμ.2.1, ?_, pow_db B μ hμ k⟩
  intro z
  calc ∑ a, μ a * (B ^ k) a z = ∑ a, μ z * (B ^ k) z a :=
        Finset.sum_congr rfl fun a _ => pow_db B μ hμ k a z
    _ = μ z := by rw [← Finset.mul_sum, hmk.2 z, mul_one]

end

end TranspositionIID.Main.Dev.L41
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.L41
open TranspositionIID.Main TranspositionIID.Main.Dev TranspositionIID.Main.Dev.L42

variable {S : Type*} [Fintype S] [DecidableEq S]

section
variable (B : Matrix S S ℝ) (μ : S → ℝ)

lemma E_pow_le (hB : ActuarialValuation.isFiniteMarkovKernel B) (hμ : ReversibleProbability B μ)
    (g : S → ℝ) (k : ℕ) :
    GibbsCongestion.dirichletForm B μ ((B ^ k).mulVec g) ((B ^ k).mulVec g) ≤
      GibbsCongestion.dirichletForm B μ g g := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : (B ^ (k + 1)).mulVec g = B.mulVec ((B ^ k).mulVec g) := by
      rw [pow_succ', Matrix.mulVec_mulVec]
    rw [this]
    exact (E_contr B μ hB hμ _).trans ih

lemma E_le_diag (hB : ActuarialValuation.isFiniteMarkovKernel B) (hμ : ReversibleProbability B μ)
    (g : S → ℝ) (k : ℕ) :
    GibbsCongestion.dirichletForm B μ g ((B ^ k).mulVec g) ≤
      GibbsCongestion.dirichletForm B μ g g := by
  have h1 := E_cs B μ hB hμ g ((B ^ k).mulVec g)
  have h2 := E_pow_le B μ hB hμ g k
  have h0 := E_nonneg B μ hB hμ g
  have h3 : GibbsCongestion.dirichletForm B μ g ((B ^ k).mulVec g) ^ 2 ≤
      GibbsCongestion.dirichletForm B μ g g ^ 2 := by
    calc _ ≤ _ := h1
      _ ≤ GibbsCongestion.dirichletForm B μ g g * GibbsCongestion.dirichletForm B μ g g :=
          mul_le_mul_of_nonneg_left h2 h0
      _ = _ := by ring
  exact (abs_le_of_sq_le_sq' h3 h0).2

lemma tele_sum (hB : ActuarialValuation.isFiniteMarkovKernel B) (hμ : ReversibleProbability B μ)
    (g : S → ℝ) (N : ℕ) :
    ip μ (fun z => g z - (B ^ N).mulVec g z) g =
      ∑ k ∈ Finset.range N, ip μ (fun z => g z - B.mulVec g z) ((B ^ k).mulVec g) := by
  induction N with
  | zero => simp [ip]
  | succ N ih =>
    rw [Finset.sum_range_succ, ← ih]
    have e : (B ^ (N + 1)).mulVec g = (B ^ N).mulVec (B.mulVec g) := by
      rw [pow_succ, Matrix.mulVec_mulVec]
    have hsa := selfadj (B ^ N) μ (pow_rev B μ hB hμ N) (fun z => g z - B.mulVec g z) g
    have e2 : (B ^ N).mulVec (fun z => g z - B.mulVec g z) =
        fun z => (B ^ N).mulVec g z - (B ^ N).mulVec (B.mulVec g) z := by
      funext z
      have : (fun z => g z - B.mulVec g z) = g - B.mulVec g := rfl
      rw [this, Matrix.mulVec_sub]; rfl
    have h3 : ip μ (fun z => g z - (B ^ (N + 1)).mulVec g z) g =
        ip μ (fun z => g z - (B ^ N).mulVec g z) g +
          ip μ (fun z => (B ^ N).mulVec (fun z => g z - B.mulVec g z) z) g := by
      rw [e2, e]
      simp only [ip_sub_left]; ring
    rw [h3]
    congr 1

lemma tele (hB : ActuarialValuation.isFiniteMarkovKernel B) (hμ : ReversibleProbability B μ)
    (g : S → ℝ) (N : ℕ) :
    GibbsCongestion.dirichletForm (B ^ N) μ g g ≤ N * GibbsCongestion.dirichletForm B μ g g := by
  have hBN : ActuarialValuation.isFiniteMarkovKernel (B ^ N) := Rev.pow_markov B hB N
  rw [E_eq (B ^ N) μ hBN (pow_rev B μ hB hμ N), tele_sum B μ hB hμ g N]
  calc ∑ k ∈ Finset.range N, ip μ (fun z => g z - B.mulVec g z) ((B ^ k).mulVec g)
      ≤ ∑ k ∈ Finset.range N, GibbsCongestion.dirichletForm B μ g g := by
        apply Finset.sum_le_sum; intro k _
        rw [← E_eq B μ hB hμ]
        exact E_le_diag B μ hB hμ g k
    _ = N * GibbsCongestion.dirichletForm B μ g g := by simp

end

end TranspositionIID.Main.Dev.L41
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.L41
open TranspositionIID.Main TranspositionIID.Main.Dev TranspositionIID.Main.Dev.L42

variable {S : Type*} [Fintype S] [DecidableEq S]

lemma core (K : Matrix S S ℝ) (μ : S → ℝ) (hK : ActuarialValuation.isFiniteMarkovKernel K)
    (hμ : ReversibleProbability K μ) (g J : S → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hg : ∑ z, μ z * g z ^ 2 = 1) (hJ0 : ∀ z, 0 ≤ J z) (hJM : ∀ z, J z ≤ M) :
    ip μ (fun z => J z - K.mulVec J z) (fun z => g z ^ 2) ≤
      Real.sqrt 2 * M * Real.sqrt (GibbsCongestion.dirichletForm K μ g g) := by
  set E := GibbsCongestion.dirichletForm K μ g g with hE
  have hE0 : 0 ≤ E := E_nonneg K μ hK hμ g
  set L := ip μ (fun z => J z - K.mulVec J z) (fun z => g z ^ 2) with hL
  have hLeq : L = GibbsCongestion.dirichletForm K μ J (fun z => g z ^ 2) :=
    (E_eq K μ hK hμ J _).symm
  have hw : ∀ xy : S × S, 0 ≤ μ xy.1 * K xy.1 xy.2 := fun xy => mul_nonneg (hμ.2.1 _).le (hK.1 _ _)
  have hcs := cs_weighted (X := S × S) (fun xy => μ xy.1 * K xy.1 xy.2)
    (fun xy => g xy.1 - g xy.2) (fun xy => (g xy.1 + g xy.2) * (J xy.1 - J xy.2)) hw
  simp only [Fintype.sum_prod_type] at hcs
  -- T = 2 L
  have hT : ∑ x, ∑ y, μ x * K x y * (g x - g y) * ((g x + g y) * (J x - J y)) = 2 * L := by
    rw [hLeq]; unfold GibbsCongestion.dirichletForm
    rw [← mul_assoc, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul]
    apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro y _; ring
  have hA : ∑ x, ∑ y, μ x * K x y * (g x - g y) ^ 2 = 2 * E := by
    rw [hE]; unfold GibbsCongestion.dirichletForm
    rw [← mul_assoc, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul]
    apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro y _; ring
  have hmass : ∑ x, ∑ y, μ x * K x y * (g x ^ 2 + g y ^ 2) = 2 := by
    have e1 : ∑ x, ∑ y, μ x * K x y * g x ^ 2 = 1 := by
      calc ∑ x, ∑ y, μ x * K x y * g x ^ 2 = ∑ x, μ x * g x ^ 2 := by
            apply Finset.sum_congr rfl; intro x _
            rw [← Finset.sum_mul, ← Finset.mul_sum, hK.2 x]; ring
        _ = 1 := hg
    have e2 : ∑ x, ∑ y, μ x * K x y * g y ^ 2 = 1 := by
      rw [Finset.sum_comm]
      calc ∑ y, ∑ x, μ x * K x y * g y ^ 2 = ∑ y, μ y * g y ^ 2 := by
            apply Finset.sum_congr rfl; intro y _
            rw [← Finset.sum_mul, hμ.2.2.1 y]
        _ = 1 := hg
    simp only [mul_add, Finset.sum_add_distrib]; rw [e1, e2]; norm_num
  have hB : ∑ x, ∑ y, μ x * K x y * ((g x + g y) * (J x - J y)) ^ 2 ≤ 4 * M ^ 2 := by
    calc ∑ x, ∑ y, μ x * K x y * ((g x + g y) * (J x - J y)) ^ 2
        ≤ ∑ x, ∑ y, μ x * K x y * (2 * (g x ^ 2 + g y ^ 2) * M ^ 2) := by
          apply Finset.sum_le_sum; intro x _; apply Finset.sum_le_sum; intro y _
          apply mul_le_mul_of_nonneg_left _ (hw (x, y))
          have h1 : (J x - J y) ^ 2 ≤ M ^ 2 := by
            nlinarith [hJ0 x, hJ0 y, hJM x, hJM y]
          have h2 : (g x + g y) ^ 2 ≤ 2 * (g x ^ 2 + g y ^ 2) := by nlinarith [sq_nonneg (g x - g y)]
          rw [mul_pow]
          exact mul_le_mul h2 h1 (sq_nonneg _) (by positivity)
      _ = 2 * M ^ 2 * ∑ x, ∑ y, μ x * K x y * (g x ^ 2 + g y ^ 2) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; ring
      _ = 4 * M ^ 2 := by rw [hmass]; ring
  rw [hT, hA] at hcs
  have hsq : L ^ 2 ≤ 2 * M ^ 2 * E := by
    have : (2 * L) ^ 2 ≤ (2 * E) * (4 * M ^ 2) :=
      hcs.trans (mul_le_mul_of_nonneg_left hB (by linarith))
    nlinarith
  have h3 : L ≤ Real.sqrt (2 * M ^ 2 * E) := by
    apply le_trans (le_abs_self L)
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsq
  calc L ≤ Real.sqrt (2 * M ^ 2 * E) := h3
    _ = Real.sqrt 2 * M * Real.sqrt E := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hM]

end TranspositionIID.Main.Dev.L41
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.L41
open TranspositionIID.Main TranspositionIID.Main.Dev TranspositionIID.Main.Dev.L42

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The pointwise-in-`x` estimate, for an abstract kernel `B`. -/
lemma pointwise (P B : Matrix S S ℝ) (μ : S → ℝ)
    (hB : ActuarialValuation.isFiniteMarkovKernel B) (hμB : ReversibleProbability B μ)
    (ν : S → ℝ) (hν : ActuarialValuation.isFiniteStateDistribution ν)
    (J : S → ℝ) (n : ℕ) (hn : 1 ≤ n) (hJ0 : ∀ z, 0 ≤ J z) (hJM : ∀ z, J z ≤ (n : ℝ) ^ 2 / 4)
    (c : ℝ) (hc : 0 < c) (hcmp : ∀ v : S → ℝ,
      GibbsCongestion.dirichletForm B μ v v ≤ 2 * (n : ℝ) ^ 2 * c *
        GibbsCongestion.dirichletForm P μ v v)
    (bound : ℝ) (hbound : ∀ σ, expectedAfter B σ (n ^ 4) J ≤ bound)
    (g : S → ℝ) (hg0 : ∀ z, 0 ≤ g z) (hgν : ∀ z, μ z * g z ^ 2 = ν z)
    (hEP : 0 ≤ GibbsCongestion.dirichletForm P μ g g) :
    ∑ σ, ν σ * J σ ≤ bound + (n : ℝ) ^ 5 / 2 * Real.sqrt c *
      Real.sqrt (GibbsCongestion.dirichletForm P μ g g) := by
  have hBN : ActuarialValuation.isFiniteMarkovKernel (B ^ n ^ 4) := Rev.pow_markov B hB _
  have hrevN := pow_rev B μ hB hμB (n ^ 4)
  have hν1 : ∑ z, μ z * g z ^ 2 = 1 := by
    simp_rw [hgν]; exact hν.2
  -- split ν J = ν (K J) + ν (J - K J)
  have hsplit : ∑ σ, ν σ * J σ = ∑ σ, ν σ * (B ^ n ^ 4).mulVec J σ +
      ip μ (fun z => J z - (B ^ n ^ 4).mulVec J z) (fun z => g z ^ 2) := by
    unfold ip
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro z _
    rw [show μ z * (J z - (B ^ n ^ 4).mulVec J z) * g z ^ 2 =
      (μ z * g z ^ 2) * (J z - (B ^ n ^ 4).mulVec J z) by ring, hgν]
    ring
  have h1 : ∑ σ, ν σ * (B ^ n ^ 4).mulVec J σ ≤ bound := by
    calc ∑ σ, ν σ * (B ^ n ^ 4).mulVec J σ ≤ ∑ σ, ν σ * bound :=
          Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (hbound σ) (hν.1 σ)
      _ = bound := by rw [← Finset.sum_mul, hν.2, one_mul]
  have hM : (0 : ℝ) ≤ (n : ℝ) ^ 2 / 4 := by positivity
  have h2 := core (B ^ n ^ 4) μ hBN hrevN g J ((n : ℝ) ^ 2 / 4) hM hν1 hJ0 hJM
  have h3 : GibbsCongestion.dirichletForm (B ^ n ^ 4) μ g g ≤
      ((n ^ 4 : ℕ) : ℝ) * (2 * (n : ℝ) ^ 2 * c * GibbsCongestion.dirichletForm P μ g g) :=
    (tele B μ hB hμB g (n ^ 4)).trans
      (mul_le_mul_of_nonneg_left (hcmp g) (by positivity))
  have h4 : Real.sqrt (GibbsCongestion.dirichletForm (B ^ n ^ 4) μ g g) ≤
      Real.sqrt (((n ^ 4 : ℕ) : ℝ) * (2 * (n : ℝ) ^ 2 * c * GibbsCongestion.dirichletForm P μ g g)) :=
    Real.sqrt_le_sqrt h3
  have h5 : Real.sqrt (((n ^ 4 : ℕ) : ℝ) * (2 * (n : ℝ) ^ 2 * c * GibbsCongestion.dirichletForm P μ g g)) =
      Real.sqrt 2 * (n : ℝ) ^ 3 * Real.sqrt c * Real.sqrt (GibbsCongestion.dirichletForm P μ g g) := by
    have e : ((n ^ 4 : ℕ) : ℝ) * (2 * (n : ℝ) ^ 2 * c * GibbsCongestion.dirichletForm P μ g g) =
        2 * ((n : ℝ) ^ 3) ^ 2 * c * GibbsCongestion.dirichletForm P μ g g := by push_cast; ring
    rw [e, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have h6 : Real.sqrt 2 * ((n : ℝ) ^ 2 / 4) * (Real.sqrt 2 * (n : ℝ) ^ 3 * Real.sqrt c *
      Real.sqrt (GibbsCongestion.dirichletForm P μ g g)) =
      (n : ℝ) ^ 5 / 2 * Real.sqrt c * Real.sqrt (GibbsCongestion.dirichletForm P μ g g) := by
    have : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    calc _ = (Real.sqrt 2 * Real.sqrt 2) * ((n : ℝ) ^ 2 / 4 * (n : ℝ) ^ 3) * Real.sqrt c *
          Real.sqrt (GibbsCongestion.dirichletForm P μ g g) := by ring
      _ = _ := by rw [this]; ring
  have h7 : ip μ (fun z => J z - (B ^ n ^ 4).mulVec J z) (fun z => g z ^ 2) ≤
      (n : ℝ) ^ 5 / 2 * Real.sqrt c * Real.sqrt (GibbsCongestion.dirichletForm P μ g g) := by
    refine h2.trans ?_
    rw [← h6]
    apply mul_le_mul_of_nonneg_left (h4.trans h5.le) (by positivity)
  linarith

end TranspositionIID.Main.Dev.L41
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.C1
open TranspositionIID.Main TranspositionIID.Main.Dev

variable {n : ℕ}

def nonint (p : Fin n → ℝ) (x θ : ℝ) (k : Fin n) : Prop :=
  Real.log (p k) ≤ x ∨ x + θ < Real.log (p k)

lemma mem_pairs (p : Fin n → ℝ) (x θ : ℝ) (σ : ListState n) (k l : Fin n) :
    (k, l) ∈ auxiliaryPairs p x θ σ ↔
      nonint p x θ k ∧ nonint p x θ l ∧ σ k < σ l ∧
        ∀ m, σ k < σ m → σ m < σ l → ¬ nonint p x θ m := by
  unfold auxiliaryPairs nonint
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, fun m hm1 hm2 hm => ?_⟩
    have := h4 m hm1 hm2
    rcases hm with h | h <;> linarith [this.1, this.2]
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, fun m hm1 hm2 => ?_⟩
    have := h4 m hm1 hm2
    simp only [not_or, not_le, not_lt] at this
    exact this

lemma swap_nonint (p : Fin n → ℝ) (x θ : ℝ) (i j : Fin n) (hi : nonint p x θ i)
    (hj : nonint p x θ j) (m : Fin n) :
    nonint p x θ (Equiv.swap i j m) ↔ nonint p x θ m := by
  by_cases h1 : m = i
  · subst h1; simp [hj, hi]
  · by_cases h2 : m = j
    · subst h2; simp [hi, hj]
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

lemma pairs_comp (p : Fin n → ℝ) (x θ : ℝ) (σ : ListState n) (τ : Equiv.Perm (Fin n))
    (hτ : ∀ m, nonint p x θ (τ m) ↔ nonint p x θ m) (k l : Fin n) :
    (k, l) ∈ auxiliaryPairs p x θ (τ.trans σ) ↔ (τ k, τ l) ∈ auxiliaryPairs p x θ σ := by
  rw [mem_pairs, mem_pairs]
  simp only [Equiv.trans_apply, hτ]
  apply and_congr Iff.rfl; apply and_congr Iff.rfl; apply and_congr Iff.rfl
  constructor
  · intro h m' h1 h2
    have := h (τ.symm m') (by simpa using h1) (by simpa using h2)
    intro hm; apply this
    exact (hτ (τ.symm m')).1 (by simpa using hm)
  · intro h m h1 h2
    have := h (τ m) h1 h2
    exact fun hm => this ((hτ m).2 hm)

lemma trans_swap_eq (σ : ListState n) (i j : Fin n) :
    σ.trans (Equiv.swap (σ i) (σ j)) = (Equiv.swap i j).trans σ := by
  ext m
  simp only [Equiv.trans_apply]
  by_cases h1 : m = i
  · subst h1; simp
  · by_cases h2 : m = j
    · subst h2; simp
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2,
        Equiv.swap_apply_of_ne_of_ne (fun h => h1 (σ.injective h)) (fun h => h2 (σ.injective h))]

lemma weight_swap_gen (q : Fin n → ℝ) (σ : ListState n) (i j : Fin n) (hij : σ i < σ j) :
    stationaryWeight q ((Equiv.swap i j).trans σ) * q i ^ ((σ j).val - (σ i).val) =
      stationaryWeight q σ * q j ^ ((σ j).val - (σ i).val) := by
  have hne : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
  set η := (Equiv.swap i j).trans σ with hη
  have hηi : η i = σ j := by simp [hη]
  have hηj : η j = σ i := by simp [hη]
  have hηk : ∀ k, k ≠ i → k ≠ j → η k = σ k := fun k h1 h2 => by
    simp [hη, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have hlt : (σ i).val < (σ j).val := hij
  have hi' := (σ i).isLt
  have hj' := (σ j).isLt
  unfold stationaryWeight
  have hmem_i : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  have hmem_j : j ∈ (Finset.univ : Finset (Fin n)).erase i := by simp [hne.symm]
  rw [← Finset.mul_prod_erase _ _ hmem_i, ← Finset.mul_prod_erase _ _ hmem_i,
    ← Finset.mul_prod_erase _ _ hmem_j, ← Finset.mul_prod_erase _ _ hmem_j]
  have hrest : ∏ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase j, q k ^ (n - 1 - (η k).val) =
      ∏ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase j, q k ^ (n - 1 - (σ k).val) := by
    apply Finset.prod_congr rfl
    intro k hk
    simp only [Finset.mem_erase] at hk
    rw [hηk k hk.2.1 hk.1]
  rw [hrest, hηi, hηj]
  set d := (σ j).val - (σ i).val with hd
  have e1 : n - 1 - (σ i).val = (n - 1 - (σ j).val) + d := by omega
  rw [e1]
  rw [pow_add, pow_add]
  ring

end TranspositionIID.Main.Dev.C1
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.C1
open TranspositionIID.Main TranspositionIID.Main.Dev

variable {n : ℕ}

lemma a_bounds (p : Fin n → ℝ) (hpos : ∀ i, 0 < p i) (i j : Fin n) (d : ℕ) :
    0 ≤ p j ^ d / (p j ^ d + p i ^ d) ∧ p j ^ d / (p j ^ d + p i ^ d) ≤ 1 := by
  have h1 := pow_pos (hpos i) d
  have h2 := pow_pos (hpos j) d
  constructor
  · positivity
  · rw [div_le_one (by positivity)]; linarith

lemma kappa_nonneg (p : Fin n → ℝ) (hpos : ∀ i, 0 < p i) (x : ℝ) (σ η : ListState n)
    (ij : Fin n × Fin n) : 0 ≤ auxiliaryPairKernel p x σ η ij := by
  unfold auxiliaryPairKernel
  have hb := a_bounds p hpos ij.1 ij.2 ((σ ij.2).val - (σ ij.1).val)
  by_cases h : (Real.log (p ij.1) ≤ x ↔ Real.log (p ij.2) ≤ x)
  · simp only [h, if_true]; split_ifs <;> norm_num
  · simp only [h, if_false]
    apply add_nonneg
    · split_ifs <;> linarith [hb.1]
    · split_ifs <;> linarith [hb.2]

lemma kappa_sum (p : Fin n → ℝ) (hpos : ∀ i, 0 < p i) (x : ℝ) (σ : ListState n)
    (ij : Fin n × Fin n) : ∑ η, auxiliaryPairKernel p x σ η ij = 1 := by
  unfold auxiliaryPairKernel
  by_cases h : (Real.log (p ij.1) ≤ x ↔ Real.log (p ij.2) ≤ x)
  · simp [h]
  · simp only [h, if_false, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring

lemma aux_markov (p : Fin n → ℝ) (hpos : ∀ i, 0 < p i) (x θ : ℝ) :
    ActuarialValuation.isFiniteMarkovKernel (auxiliaryKernel p x θ) := by
  constructor
  · intro σ η
    unfold auxiliaryKernel
    simp only
    split_ifs
    · norm_num
    · norm_num
    · exact div_nonneg (Finset.sum_nonneg fun ij _ => kappa_nonneg p hpos x σ η ij) (Nat.cast_nonneg _)
  · intro σ
    unfold auxiliaryKernel
    simp only
    by_cases hc : (auxiliaryPairs p x θ σ).card = 0
    · simp [hc]
    · simp only [hc, if_false]
      rw [← Finset.sum_div, Finset.sum_comm]
      simp_rw [kappa_sum p hpos x σ]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact div_self (by exact_mod_cast hc)

end TranspositionIID.Main.Dev.C1
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.C1
open TranspositionIID.Main TranspositionIID.Main.Dev
open Classical

variable {n : ℕ}

noncomputable def S1 (p : Fin n → ℝ) (x θ : ℝ) (σ η : ListState n) : ℝ :=
  ∑ ij ∈ auxiliaryPairs p x θ σ, auxiliaryPairKernel p x σ η ij

def Opp (p : Fin n → ℝ) (x : ℝ) (ij : Fin n × Fin n) : Prop :=
  ¬ (Real.log (p ij.1) ≤ x ↔ Real.log (p ij.2) ≤ x)

noncomputable def aa (p : Fin n → ℝ) (σ : ListState n) (ij : Fin n × Fin n) : ℝ :=
  p ij.2 ^ ((σ ij.2).val - (σ ij.1).val) /
    (p ij.2 ^ ((σ ij.2).val - (σ ij.1).val) + p ij.1 ^ ((σ ij.2).val - (σ ij.1).val))

lemma B_eq (p : Fin n → ℝ) (x θ : ℝ) (σ η : ListState n) (h : σ ≠ η) :
    auxiliaryKernel p x θ σ η = S1 p x θ σ η / (auxiliaryPairs p x θ σ).card := by
  unfold auxiliaryKernel S1
  simp only
  by_cases hc : (auxiliaryPairs p x θ σ).card = 0
  · simp [hc, h]
  · simp [hc]

lemma kappa_ne (p : Fin n → ℝ) (x : ℝ) (σ η : ListState n) (h : σ ≠ η) (ij : Fin n × Fin n) :
    auxiliaryPairKernel p x σ η ij =
      if Opp p x ij ∧ σ.trans (Equiv.swap (σ ij.1) (σ ij.2)) = η then aa p σ ij else 0 := by
  unfold auxiliaryPairKernel Opp aa
  by_cases hc : (Real.log (p ij.1) ≤ x ↔ Real.log (p ij.2) ≤ x)
  · simp [hc, h]
  · simp [hc, h]

lemma trans_swap_twice (σ : ListState n) (u v : Fin n) :
    (σ.trans (Equiv.swap u v)).trans (Equiv.swap u v) = σ := by
  ext m; simp

lemma step (p : Fin n → ℝ) (x θ : ℝ) (σ η : ListState n) (ij : Fin n × Fin n)
    (h1 : ij ∈ auxiliaryPairs p x θ σ) (h2 : Opp p x ij)
    (h3 : σ.trans (Equiv.swap (σ ij.1) (σ ij.2)) = η) :
    (ij.2, ij.1) ∈ auxiliaryPairs p x θ η ∧ Opp p x (ij.2, ij.1) ∧
      η.trans (Equiv.swap (η ij.2) (η ij.1)) = σ := by
  obtain ⟨i, j⟩ := ij
  simp only at *
  have hm := (mem_pairs p x θ σ i j).1 h1
  have hη : η = (Equiv.swap i j).trans σ := by rw [← h3]; exact trans_swap_eq σ i j
  have hτ := swap_nonint p x θ i j hm.1 hm.2.1
  refine ⟨?_, fun h => h2 h.symm, ?_⟩
  · rw [hη, pairs_comp p x θ σ (Equiv.swap i j) hτ]
    simpa using h1
  · have e1 : η j = σ i := by rw [← h3]; simp
    have e2 : η i = σ j := by rw [← h3]; simp
    rw [e1, e2, ← h3]
    exact trans_swap_twice σ (σ i) (σ j)

lemma claimA (p : Fin n → ℝ) (hpos : ∀ i, 0 < p i) (x θ : ℝ) (σ η : ListState n) (h : σ ≠ η) :
    stationaryWeight p σ * S1 p x θ σ η = stationaryWeight p η * S1 p x θ η σ := by
  unfold S1
  simp only [kappa_ne p x σ η h, kappa_ne p x η σ h.symm]
  rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_bij' (fun ij _ => (ij.2, ij.1)) (fun ij _ => (ij.2, ij.1)) ?_ ?_ ?_ ?_ ?_
  · intro ij hij
    simp only [Finset.mem_filter] at hij ⊢
    have := step p x θ σ η ij hij.1 hij.2.1 hij.2.2
    exact ⟨this.1, this.2.1, this.2.2⟩
  · intro ij hij
    simp only [Finset.mem_filter] at hij ⊢
    have := step p x θ η σ ij hij.1 hij.2.1 hij.2.2
    exact ⟨this.1, this.2.1, this.2.2⟩
  · intro ij _; rfl
  · intro ij _; rfl
  · intro ij hij
    simp only [Finset.mem_filter] at hij
    obtain ⟨i, j⟩ := ij
    simp only at *
    have hm := (mem_pairs p x θ σ i j).1 hij.1
    have hη : η = (Equiv.swap i j).trans σ := by rw [← hij.2.2]; exact trans_swap_eq σ i j
    have hw := weight_swap_gen p σ i j hm.2.2.1
    rw [← hη] at hw
    have e1 : η j = σ i := by rw [← hij.2.2]; simp
    have e2 : η i = σ j := by rw [← hij.2.2]; simp
    unfold aa
    simp only [e1, e2]
    set d := (σ j).val - (σ i).val
    have h1 := pow_pos (hpos i) d
    have h2 := pow_pos (hpos j) d
    rw [mul_div_assoc', mul_div_assoc', add_comm (p i ^ d)]
    congr 1
    linarith

end TranspositionIID.Main.Dev.C1
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.C1
open TranspositionIID.Main TranspositionIID.Main.Dev
open Classical

variable {n : ℕ}

lemma card_swap (p : Fin n → ℝ) (x θ : ℝ) (σ : ListState n) (i j : Fin n)
    (hi : nonint p x θ i) (hj : nonint p x θ j) :
    (auxiliaryPairs p x θ ((Equiv.swap i j).trans σ)).card = (auxiliaryPairs p x θ σ).card := by
  have hτ := swap_nonint p x θ i j hi hj
  refine Finset.card_bij' (fun kl _ => (Equiv.swap i j kl.1, Equiv.swap i j kl.2))
    (fun kl _ => (Equiv.swap i j kl.1, Equiv.swap i j kl.2)) ?_ ?_ ?_ ?_
  · intro kl hkl
    obtain ⟨k, l⟩ := kl
    exact (pairs_comp p x θ σ _ hτ k l).1 hkl
  · intro kl hkl
    obtain ⟨k, l⟩ := kl
    exact (pairs_comp p x θ σ _ hτ _ _).2 (by simpa using hkl)
  · intro kl _; simp
  · intro kl _; simp

lemma claimB (p : Fin n → ℝ) (x θ : ℝ) (σ η : ListState n) (h : σ ≠ η)
    (hS : S1 p x θ σ η ≠ 0) :
    (auxiliaryPairs p x θ σ).card = (auxiliaryPairs p x θ η).card := by
  unfold S1 at hS
  obtain ⟨ij, hij, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
  rw [kappa_ne p x σ η h] at hne
  have hc : Opp p x ij ∧ σ.trans (Equiv.swap (σ ij.1) (σ ij.2)) = η := by
    by_contra hh; exact hne (if_neg hh)
  obtain ⟨i, j⟩ := ij
  simp only at hc hij
  have hm := (mem_pairs p x θ σ i j).1 hij
  have hη : η = (Equiv.swap i j).trans σ := by rw [← hc.2]; exact trans_swap_eq σ i j
  rw [hη, card_swap p x θ σ i j hm.1 hm.2.1]

lemma aux_db (p : Fin n → ℝ) (hpos : ∀ i, 0 < p i) (x θ : ℝ) (σ η : ListState n) :
    stationaryLaw p σ * auxiliaryKernel p x θ σ η =
      stationaryLaw p η * auxiliaryKernel p x θ η σ := by
  by_cases h : σ = η
  · subst h; rfl
  · rw [B_eq p x θ σ η h, B_eq p x θ η σ (Ne.symm h)]
    unfold stationaryLaw
    have hA := claimA p hpos x θ σ η h
    have hZ := Rev.partition_pos p hpos
    by_cases hS : S1 p x θ σ η = 0
    · have : S1 p x θ η σ = 0 := by
        have hw := Rev.weight_pos p hpos η
        rw [hS, mul_zero] at hA
        rcases mul_eq_zero.1 hA.symm with h0 | h0
        · exact absurd h0 hw.ne'
        · exact h0
      rw [hS, this]; simp
    · rw [claimB p x θ σ η h hS]
      rw [div_mul_div_comm, div_mul_div_comm, hA]

lemma aux_rev (p : Fin n → ℝ) (hp : ActuarialValuation.isFiniteStateDistribution p)
    (hpos : ∀ i, 0 < p i) (x θ : ℝ) :
    ReversibleProbability (auxiliaryKernel p x θ) (stationaryLaw p) := by
  have hr := Rev.reversible_stationary p hp hpos
  have hM := aux_markov p hpos x θ
  refine ⟨hr.1, hr.2.1, ?_, aux_db p hpos x θ⟩
  intro z
  calc ∑ a, stationaryLaw p a * auxiliaryKernel p x θ a z
      = ∑ a, stationaryLaw p z * auxiliaryKernel p x θ z a :=
        Finset.sum_congr rfl fun a _ => aux_db p hpos x θ a z
    _ = stationaryLaw p z := by rw [← Finset.mul_sum, hM.2 z, mul_one]

end TranspositionIID.Main.Dev.C1
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.L41
open TranspositionIID.Main TranspositionIID.Main.Dev Set

variable {n : ℕ}

lemma J_bounds (p : Fin n → ℝ) (x θ : ℝ) (hθ : 0 < θ) (σ : ListState n) :
    0 ≤ separatedInversions p x θ σ ∧ separatedInversions p x θ σ ≤ (n : ℝ) ^ 2 / 4 := by
  classical
  refine ⟨Nat.cast_nonneg _, ?_⟩
  unfold separatedInversions
  set H := Finset.univ.filter (fun i : Fin n => x + θ < Real.log (p i)) with hH
  set L := Finset.univ.filter (fun j : Fin n => Real.log (p j) ≤ x) with hL
  have hsub : (Finset.univ.filter (fun ij : Fin n × Fin n =>
      Real.log (p ij.2) ≤ x ∧ x + θ < Real.log (p ij.1) ∧ σ ij.2 < σ ij.1)) ⊆ H ×ˢ L := by
    intro ij hij
    have h := (Finset.mem_filter.1 hij).2
    exact Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, h.2.1⟩,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, h.1⟩⟩
  have hdisj : Disjoint H L := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [hH, hL, Finset.mem_filter] at hi hi'
    linarith [hi.2, hi'.2]
  have hcard : H.card + L.card ≤ n := by
    rw [← Finset.card_union_of_disjoint hdisj]
    calc (H ∪ L).card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
      _ = n := by simp
  have h1 : (Finset.univ.filter (fun ij : Fin n × Fin n =>
      Real.log (p ij.2) ≤ x ∧ x + θ < Real.log (p ij.1) ∧ σ ij.2 < σ ij.1)).card ≤ H.card * L.card := by
    calc _ ≤ (H ×ˢ L).card := Finset.card_le_card hsub
      _ = H.card * L.card := Finset.card_product _ _
  have h2 : (H.card : ℝ) + L.card ≤ n := by exact_mod_cast hcard
  have h3 : ((Finset.univ.filter (fun ij : Fin n × Fin n =>
      Real.log (p ij.2) ≤ x ∧ x + θ < Real.log (p ij.1) ∧ σ ij.2 < σ ij.1)).card : ℝ) ≤
      (H.card : ℝ) * L.card := by exact_mod_cast h1
  have h4 : (H.card : ℝ) * L.card ≤ ((H.card : ℝ) + L.card) ^ 2 / 4 := by
    nlinarith [sq_nonneg ((H.card : ℝ) - L.card)]
  have h5 : ((H.card : ℝ) + L.card) ^ 2 ≤ (n : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  linarith

end TranspositionIID.Main.Dev.L41
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.L41
open TranspositionIID.Main TranspositionIID.Main.Dev Set

noncomputable def mm (t : ℝ) : ℝ := (t + 1) * Real.log t - 2 * (t - 1)

lemma hasDerivAt_mm {t : ℝ} (ht : 0 < t) :
    HasDerivAt mm (Real.log t + (t + 1) * t⁻¹ - 2) t := by
  have h1 := Real.hasDerivAt_log ht.ne'
  have h2 := ((hasDerivAt_id t).add_const 1).mul h1
  have h3 := (((hasDerivAt_id t).sub_const 1).const_mul 2)
  have h4 := h2.sub h3
  have h5 : HasDerivAt mm _ t := h4
  convert h5 using 1
  simp

lemma mm_mono : MonotoneOn mm (Ioi 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · intro x hx; exact (hasDerivAt_mm hx).continuousAt.continuousWithinAt
  · intro x hx; rw [interior_Ioi] at hx
    exact (hasDerivAt_mm hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx' : (0 : ℝ) < x := hx
    rw [(hasDerivAt_mm hx').deriv]
    have h := Real.one_sub_inv_le_log_of_pos hx'
    have : (x + 1) * x⁻¹ = 1 + x⁻¹ := by field_simp
    rw [this]; linarith

lemma mm_one : mm 1 = 0 := by simp [mm]

lemma mm_sign {t : ℝ} (ht : 0 < t) : 0 ≤ (t - 1) * mm t := by
  rcases le_total 1 t with h | h
  · have := mm_mono (Set.mem_Ioi.2 (zero_lt_one' ℝ)) (Set.mem_Ioi.2 ht) h
    rw [mm_one] at this
    exact mul_nonneg (by linarith) this
  · have := mm_mono (Set.mem_Ioi.2 ht) (Set.mem_Ioi.2 (zero_lt_one' ℝ)) h
    rw [mm_one] at this
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) this

lemma edge_real {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    4 * (u - v) ^ 2 ≤ (u ^ 2 - v ^ 2) * (Real.log (u ^ 2) - Real.log (v ^ 2)) := by
  have h := mm_sign (div_pos hu hv)
  unfold mm at h
  have hlog : Real.log (u / v) = Real.log u - Real.log v := Real.log_div hu.ne' hv.ne'
  rw [hlog] at h
  have e1 : Real.log (u ^ 2) = 2 * Real.log u := by rw [Real.log_pow]; norm_num
  have e2 : Real.log (v ^ 2) = 2 * Real.log v := by rw [Real.log_pow]; norm_num
  rw [e1, e2]
  have key : (u ^ 2 - v ^ 2) * (2 * Real.log u - 2 * Real.log v) - 4 * (u - v) ^ 2 =
      2 * v ^ 2 * ((u / v - 1) * ((u / v + 1) * (Real.log u - Real.log v) - 2 * (u / v - 1))) := by
    field_simp; ring
  have : 0 ≤ 2 * v ^ 2 * ((u / v - 1) * ((u / v + 1) * (Real.log u - Real.log v) - 2 * (u / v - 1))) :=
    mul_nonneg (by positivity) h
  linarith

lemma edge_ennreal (c gx gy : ℝ) (hc : 0 ≤ c) (hgx : 0 ≤ gx) (hgy : 0 ≤ gy) :
    ENNReal.ofReal (4 * c * (gx - gy) ^ 2) ≤ entropyEdge c (gx ^ 2) (gy ^ 2) := by
  unfold entropyEdge
  by_cases h1 : c = 0
  · simp [h1]
  by_cases h2 : gx = 0 ∧ gy = 0
  · simp [h2.1, h2.2]
  have h3 : ¬ (gx ^ 2 = 0 ∧ gy ^ 2 = 0) := fun h => h2 ⟨pow_eq_zero_iff (two_ne_zero) |>.1 h.1,
    pow_eq_zero_iff (two_ne_zero) |>.1 h.2⟩
  simp only [h1, h3, false_or, if_false]
  by_cases h4 : gx ^ 2 = 0 ∨ gy ^ 2 = 0
  · simp only [h4, if_true]; exact le_top
  · simp only [h4, if_false]
    push Not at h4
    have hx : 0 < gx := lt_of_le_of_ne hgx (fun h => h4.1 (by rw [← h]; ring))
    have hy : 0 < gy := lt_of_le_of_ne hgy (fun h => h4.2 (by rw [← h]; ring))
    apply ENNReal.ofReal_le_ofReal
    have := edge_real hx hy
    have hcp : 0 < c := lt_of_le_of_ne hc (Ne.symm h1)
    nlinarith [mul_le_mul_of_nonneg_left this hc]

lemma dir_ge {S : Type*} [Fintype S] (P : Matrix S S ℝ) (μ g : S → ℝ)
    (hc : ∀ a b, 0 ≤ μ a * P a b) (hg : ∀ a, 0 ≤ g a) :
    ENNReal.ofReal (4 * GibbsCongestion.dirichletForm P μ g g) ≤
      entropyDissipation P μ (fun z => g z ^ 2) := by
  unfold entropyDissipation GibbsCongestion.dirichletForm
  have hterm : ∀ a b, 0 ≤ 4 * (μ a * P a b) * (g a - g b) ^ 2 := fun a b => by
    have := hc a b; positivity
  have hsum : ∑ a, ∑ b, ENNReal.ofReal (4 * (μ a * P a b) * (g a - g b) ^ 2) =
      ENNReal.ofReal (∑ a, ∑ b, 4 * (μ a * P a b) * (g a - g b) ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => Finset.sum_nonneg fun b _ => hterm a b)]
    exact Finset.sum_congr rfl fun a _ => (ENNReal.ofReal_sum_of_nonneg (fun b _ => hterm a b)).symm
  have e0 : 4 * ∑ x, ∑ y, μ x * P x y * (g x - g y) * (g x - g y) =
      ∑ a, ∑ b, 4 * (μ a * P a b) * (g a - g b) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b _; ring
  have e : 4 * (1 / 2 * ∑ x, ∑ y, μ x * P x y * (g x - g y) * (g x - g y)) =
      1 / 2 * ∑ a, ∑ b, 4 * (μ a * P a b) * (g a - g b) ^ 2 := by
    rw [← e0]; ring
  rw [e, ENNReal.ofReal_mul (by norm_num), ← hsum, ennreal_half']
  apply mul_le_mul' le_rfl
  exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => edge_ennreal _ _ _ (hc a b) (hg a) (hg b)
where
  ennreal_half' : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp

end TranspositionIID.Main.Dev.L41
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.L21
open TranspositionIID.Main Set

variable {n : ℕ}

noncomputable def Phi (p : Fin n → ℝ) (x r : ℝ) : ℝ := ∑ i, max (r - |x - Real.log (p i)|) 0

def Sset (p : Fin n → ℝ) (x : ℝ) : Set ℝ := {r | 0 ≤ r ∧ 1 ≤ Phi p x r}

lemma root_eq (p : Fin n → ℝ) (x : ℝ) : bufferRoot p x = sInf (Sset p x) := rfl

lemma Phi_cont (p : Fin n → ℝ) (x : ℝ) : Continuous (Phi p x) := by
  unfold Phi; fun_prop

lemma Phi_zero (p : Fin n → ℝ) (x : ℝ) : Phi p x 0 = 0 := by
  unfold Phi
  apply Finset.sum_eq_zero; intro i _
  apply max_eq_right; linarith [abs_nonneg (x - Real.log (p i))]

lemma Phi_le (p : Fin n → ℝ) (x : ℝ) {r : ℝ} (hr : 0 ≤ r) : Phi p x r ≤ n * r := by
  unfold Phi
  calc ∑ i, max (r - |x - Real.log (p i)|) 0 ≤ ∑ _i : Fin n, r :=
        Finset.sum_le_sum fun i _ => max_le (by linarith [abs_nonneg (x - Real.log (p i))]) hr
    _ = n * r := by simp

lemma Phi_ge (p : Fin n → ℝ) (x : ℝ) (i0 : Fin n) (r : ℝ) :
    r - |x - Real.log (p i0)| ≤ Phi p x r := by
  unfold Phi
  exact (le_max_left _ _).trans (Finset.single_le_sum (f := fun i => max (r - |x - Real.log (p i)|) 0)
    (fun i _ => le_max_right _ _) (Finset.mem_univ i0))

lemma Sset_nonempty (hn : 1 ≤ n) (p : Fin n → ℝ) (x : ℝ) : (Sset p x).Nonempty := by
  refine ⟨1 + |x - Real.log (p ⟨0, hn⟩)|, by positivity, ?_⟩
  have := Phi_ge p x ⟨0, hn⟩ (1 + |x - Real.log (p ⟨0, hn⟩)|)
  linarith

lemma Sset_closed (p : Fin n → ℝ) (x : ℝ) : IsClosed (Sset p x) :=
  isClosed_Ici.inter (isClosed_le continuous_const (Phi_cont p x))

lemma Sset_bdd (p : Fin n → ℝ) (x : ℝ) : BddBelow (Sset p x) := ⟨0, fun r hr => hr.1⟩

lemma root_le (p : Fin n → ℝ) (x : ℝ) {r : ℝ} (hr : 0 ≤ r) (h : 1 ≤ Phi p x r) :
    bufferRoot p x ≤ r := csInf_le (Sset_bdd p x) ⟨hr, h⟩

lemma root_spec (hn : 1 ≤ n) (p : Fin n → ℝ) (x : ℝ) :
    0 < bufferRoot p x ∧ Phi p x (bufferRoot p x) = 1 := by
  have hmem := (Sset_closed p x).csInf_mem (Sset_nonempty hn p x) (Sset_bdd p x)
  rw [← root_eq] at hmem
  obtain ⟨hR0, h1⟩ := hmem
  set R := bufferRoot p x with hR
  have hivt := intermediate_value_Icc hR0 (Phi_cont p x).continuousOn
  have h1mem : (1 : ℝ) ∈ Icc (Phi p x 0) (Phi p x R) := by
    rw [Phi_zero]; exact ⟨zero_le_one, h1⟩
  obtain ⟨r, hr, hr1⟩ := hivt h1mem
  have hRr : R ≤ r := root_le p x hr.1 (by rw [hr1])
  have hrR : r = R := le_antisymm hr.2 hRr
  have hPhi : Phi p x R = 1 := by rw [← hrR]; exact hr1
  refine ⟨lt_of_le_of_ne hR0 (fun h0 => ?_), hPhi⟩
  rw [← h0, Phi_zero] at hPhi; norm_num at hPhi

lemma buffer_le (p : Fin n → ℝ) (x : ℝ) : buffer p x ≤ 1 / 2 := by
  unfold buffer; have := min_le_left 1 (bufferRoot p x); linarith

lemma buffer_ge (hn : 1 ≤ n) (p : Fin n → ℝ) (x : ℝ) : 1 / (2 * (n : ℝ)) ≤ buffer p x := by
  obtain ⟨hR0, hPhi⟩ := root_spec hn p x
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 1 ≤ (n : ℝ) * bufferRoot p x := by
    have := Phi_le p x hR0.le; linarith
  have h2 : 1 / (n : ℝ) ≤ bufferRoot p x := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have h3 : 1 / (n : ℝ) ≤ min 1 (bufferRoot p x) := by
    apply le_min _ h2
    rw [div_le_one (by linarith)]; exact hn'
  unfold buffer
  calc 1 / (2 * (n : ℝ)) = 1 / 2 * (1 / (n : ℝ)) := by field_simp
    _ ≤ 1 / 2 * min 1 (bufferRoot p x) := mul_le_mul_of_nonneg_left h3 (by norm_num)

lemma buffer_pos (hn : 1 ≤ n) (p : Fin n → ℝ) (x : ℝ) : 0 < buffer p x := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact lt_of_lt_of_le (by positivity) (buffer_ge hn p x)

end TranspositionIID.Main.Dev.L21
end

section
set_option autoImplicit false

namespace TranspositionIID.Main
open TranspositionIID.Main.Dev TranspositionIID.Main.Dev.L41 MeasureTheory Set

theorem chk_lemma_4_1 {n : ℕ} (hn : 1024 ≤ n) (p : Fin n → ℝ)
    (hp : ActuarialValuation.isFiniteStateDistribution p)
    (hsort : Decreasing p) (hpos : ∀ i, 0 < p i)
    (ν : ListState n → ℝ) (hν : ActuarialValuation.isFiniteStateDistribution ν) :
    ENNReal.ofReal (∑ σ, ν σ * excess p σ) ≤
      ENNReal.ofReal C0 + ENNReal.ofReal ((3 / 2 : ℝ) * (n : ℝ) ^ 5) *
        ENNReal.rpow (entropyDissipation (transpositionKernel p) (stationaryLaw p)
          (fun σ => ν σ / stationaryLaw p σ)) (1 / 2) := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hM := Rev.kernel_markov p hp
  have hrev := Rev.reversible_stationary p hp hpos
  have hμpos := Rev.law_pos p hpos
  obtain ⟨g, hg⟩ : ∃ g : ListState n → ℝ, g = fun σ => Real.sqrt (ν σ / stationaryLaw p σ) :=
    ⟨_, rfl⟩
  have hg0 : ∀ σ, 0 ≤ g σ := fun σ => by rw [hg]; exact Real.sqrt_nonneg _
  have hgsq : ∀ σ, g σ ^ 2 = ν σ / stationaryLaw p σ := fun σ => by
    rw [hg]; exact Real.sq_sqrt (div_nonneg (hν.1 σ) (hμpos σ).le)
  have hgν : ∀ σ, stationaryLaw p σ * g σ ^ 2 = ν σ := fun σ => by
    rw [hgsq]; have := (hμpos σ).ne'; field_simp
  have hfun : (fun σ => ν σ / stationaryLaw p σ) = fun σ => g σ ^ 2 :=
    funext fun σ => (hgsq σ).symm
  rw [hfun]
  obtain ⟨ε, hε⟩ : ∃ ε, ε = GibbsCongestion.dirichletForm (transpositionKernel p) (stationaryLaw p) g g :=
    ⟨_, rfl⟩
  have hε0 : 0 ≤ ε := by rw [hε]; exact L41.E_nonneg _ _ hM hrev g
  have hc : ∀ a b, 0 ≤ stationaryLaw p a * transpositionKernel p a b := fun a b =>
    mul_nonneg (hμpos a).le (Rev.kernel_nonneg p hp.1 a b)
  -- the ENNReal comparison
  have hD := dir_ge (transpositionKernel p) (stationaryLaw p) g hc hg0
  rw [← hε] at hD
  have hD2 := ENNReal.rpow_le_rpow hD (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) (by norm_num), ← Real.sqrt_eq_rpow] at hD2
  -- the real estimate
  have hreal : ∑ σ, ν σ * excess p σ ≤ C0 + 3 * (n : ℝ) ^ 5 * Real.sqrt ε := by
    have h21 := lemma_2_1 hn1 p hp hsort hpos
    have h22 := fun σ => lemma_2_2 hn1 p hp hsort hpos σ
    set s := Real.sqrt (Real.exp 1) with hs
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ≤ 2 := by
      have he : Real.exp 1 ≤ 4 := (Real.exp_one_lt_d9).le.trans (by norm_num)
      calc s ≤ Real.sqrt (2 ^ 2) := Real.sqrt_le_sqrt (by linarith)
        _ = 2 := Real.sqrt_sq (by norm_num)
    have hpt : ∀ x : ℝ, Real.exp x * ∑ σ, ν σ * adaptiveInversions p x σ ≤
        Real.exp x / 4 + Real.pi ^ 2 / 6 * (Real.exp x / buffer p x ^ 2) +
          (n : ℝ) ^ 5 / 2 * Real.sqrt ε * Real.exp (1 / 2 * x) := by
      intro x
      have hθ0 := Dev.L21.buffer_pos hn1 p x
      have hθ1 := Dev.L21.buffer_le p x
      have h34 := proposition_3_4 hn p hp hsort hpos x (buffer p x) hθ0 hθ1
      have hJ := fun σ => L41.J_bounds p x (buffer p x) hθ0 σ
      have hpw := L41.pointwise (transpositionKernel p) (auxiliaryKernel p x (buffer p x))
        (stationaryLaw p) (C1.aux_markov p hpos x (buffer p x)) (C1.aux_rev p hp hpos x (buffer p x))
        ν hν (fun σ => separatedInversions p x (buffer p x) σ) n hn1 (fun σ => (hJ σ).1)
        (fun σ => (hJ σ).2) (Real.exp (-x)) (Real.exp_pos _) (fun v => h34.2 v)
        (1 / 4 + Real.pi ^ 2 / (6 * buffer p x ^ 2)) h34.1 g hg0 hgν (by rw [← hε]; exact hε0)
      rw [← hε] at hpw
      have hsx : Real.sqrt (Real.exp (-x)) = Real.exp (-(1 / 2 * x)) := by
        rw [show Real.exp (-x) = Real.exp (-(1 / 2 * x)) ^ 2 by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring]
        exact Real.sqrt_sq (Real.exp_pos _).le
      rw [hsx] at hpw
      have hexp : Real.exp x * Real.exp (-(1 / 2 * x)) = Real.exp (1 / 2 * x) := by
        rw [← Real.exp_add]; congr 1; ring
      have hθ2 : 0 < buffer p x ^ 2 := by positivity
      calc Real.exp x * ∑ σ, ν σ * adaptiveInversions p x σ
          ≤ Real.exp x * (1 / 4 + Real.pi ^ 2 / (6 * buffer p x ^ 2) +
              (n : ℝ) ^ 5 / 2 * Real.exp (-(1 / 2 * x)) * Real.sqrt ε) :=
            mul_le_mul_of_nonneg_left hpw (Real.exp_pos _).le
        _ = Real.exp x / 4 + Real.pi ^ 2 / 6 * (Real.exp x / buffer p x ^ 2) +
              (n : ℝ) ^ 5 / 2 * Real.sqrt ε * (Real.exp x * Real.exp (-(1 / 2 * x))) := by
            field_simp
        _ = _ := by rw [hexp]
    have hI1 : IntegrableOn (fun x : ℝ => Real.exp x / 4) (Iic 0) :=
      (integrableOn_exp_Iic 0).div_const 4
    have hI2 : IntegrableOn (fun x : ℝ => Real.pi ^ 2 / 6 * (Real.exp x / buffer p x ^ 2)) (Iic 0) :=
      h21.2.2.1.const_mul _
    have hI3 : IntegrableOn (fun x : ℝ => (n : ℝ) ^ 5 / 2 * Real.sqrt ε * Real.exp (1 / 2 * x)) (Iic 0) :=
      (integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 1 / 2) 0).const_mul _
    have hI12 : IntegrableOn (fun x : ℝ => Real.exp x / 4 +
        Real.pi ^ 2 / 6 * (Real.exp x / buffer p x ^ 2)) (Iic 0) := hI1.add hI2
    have hIrhs : IntegrableOn (fun x : ℝ => Real.exp x / 4 +
        Real.pi ^ 2 / 6 * (Real.exp x / buffer p x ^ 2) +
        (n : ℝ) ^ 5 / 2 * Real.sqrt ε * Real.exp (1 / 2 * x)) (Iic 0) := hI12.add hI3
    have hIσ : ∀ σ, IntegrableOn (fun x : ℝ => Real.exp x * adaptiveInversions p x σ) (Iic 0) :=
      fun σ => (h22 σ).1
    have hIsum : IntegrableOn (fun x : ℝ => ∑ σ, ν σ * (Real.exp x * adaptiveInversions p x σ)) (Iic 0) :=
      integrable_finsetSum _ fun σ _ => (hIσ σ).const_mul (ν σ)
    have hint1 : ∫ x in Iic 0, ∑ σ, ν σ * (Real.exp x * adaptiveInversions p x σ) =
        ∑ σ, ν σ * ∫ x in Iic 0, Real.exp x * adaptiveInversions p x σ := by
      rw [integral_finsetSum _ fun σ _ => (hIσ σ).const_mul (ν σ)]
      exact Finset.sum_congr rfl fun σ _ => integral_const_mul _ _
    have hint2 : ∫ x in Iic 0, ∑ σ, ν σ * (Real.exp x * adaptiveInversions p x σ) ≤
        ∫ x in Iic 0, (Real.exp x / 4 + Real.pi ^ 2 / 6 * (Real.exp x / buffer p x ^ 2) +
          (n : ℝ) ^ 5 / 2 * Real.sqrt ε * Real.exp (1 / 2 * x)) := by
      apply setIntegral_mono hIsum hIrhs
      intro x
      have := hpt x
      simp only
      calc ∑ σ, ν σ * (Real.exp x * adaptiveInversions p x σ)
          = Real.exp x * ∑ σ, ν σ * adaptiveInversions p x σ := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun σ _ => by ring
        _ ≤ _ := this
    have hint3 : ∫ x in Iic 0, (Real.exp x / 4 + Real.pi ^ 2 / 6 * (Real.exp x / buffer p x ^ 2) +
        (n : ℝ) ^ 5 / 2 * Real.sqrt ε * Real.exp (1 / 2 * x)) ≤
        1 / 4 + Real.pi ^ 2 / 6 * (4 + 32 * Real.exp 1) + (n : ℝ) ^ 5 * Real.sqrt ε := by
      rw [integral_add hI12 hI3, integral_add hI1 hI2, integral_div, integral_exp_Iic_zero,
        integral_const_mul, integral_const_mul, integral_exp_mul_Iic (by norm_num : (0 : ℝ) < 1 / 2)]
      have := h21.2.2.2
      have hpi : 0 ≤ Real.pi ^ 2 / 6 := by positivity
      have := mul_le_mul_of_nonneg_left this hpi
      norm_num
      nlinarith [this]
    have hexc : ∑ σ, ν σ * excess p σ ≤ 2 + (1 + s) * ∑ σ, ν σ *
        ∫ x in Iic 0, Real.exp x * adaptiveInversions p x σ := by
      calc ∑ σ, ν σ * excess p σ ≤ ∑ σ, ν σ * (2 + (1 + s) *
            ∫ x in Iic 0, Real.exp x * adaptiveInversions p x σ) :=
            Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (h22 σ).2 (hν.1 σ)
        _ = 2 + (1 + s) * ∑ σ, ν σ * ∫ x in Iic 0, Real.exp x * adaptiveInversions p x σ := by
            have : ∑ σ, ν σ * (2 + (1 + s) * ∫ x in Iic 0, Real.exp x * adaptiveInversions p x σ) =
                2 * ∑ σ, ν σ + (1 + s) * ∑ σ, ν σ * ∫ x in Iic 0, Real.exp x * adaptiveInversions p x σ := by
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun σ _ => by ring
            rw [this, hν.2]; ring
    have hmain : ∑ σ, ν σ * ∫ x in Iic 0, Real.exp x * adaptiveInversions p x σ ≤
        1 / 4 + Real.pi ^ 2 / 6 * (4 + 32 * Real.exp 1) + (n : ℝ) ^ 5 * Real.sqrt ε := by
      rw [← hint1]; exact hint2.trans hint3
    have hC0eq : C0 = 2 + (1 + s) * (1 / 4 + Real.pi ^ 2 / 6 * (4 + 32 * Real.exp 1)) := by
      unfold C0; rw [hs]; ring
    have hnn : 0 ≤ (n : ℝ) ^ 5 * Real.sqrt ε := by positivity
    have hs1 : 0 ≤ 1 + s := by linarith
    calc ∑ σ, ν σ * excess p σ ≤ 2 + (1 + s) * (1 / 4 + Real.pi ^ 2 / 6 * (4 + 32 * Real.exp 1) +
          (n : ℝ) ^ 5 * Real.sqrt ε) :=
          hexc.trans (by nlinarith [mul_le_mul_of_nonneg_left hmain hs1])
      _ = C0 + (1 + s) * ((n : ℝ) ^ 5 * Real.sqrt ε) := by rw [hC0eq]; ring
      _ ≤ C0 + 3 * (n : ℝ) ^ 5 * Real.sqrt ε := by nlinarith [mul_nonneg (by linarith : 0 ≤ 2 - s) hnn]
  have hsq4 : Real.sqrt (4 * ε) = 2 * Real.sqrt ε := by
    rw [Real.sqrt_mul (by norm_num)]
    have : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [this]
  rw [hsq4] at hD2
  have hC0 : 0 ≤ C0 := by unfold C0; positivity
  calc ENNReal.ofReal (∑ σ, ν σ * excess p σ) ≤ ENNReal.ofReal (C0 + 3 * (n : ℝ) ^ 5 * Real.sqrt ε) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal C0 + ENNReal.ofReal ((3 / 2 : ℝ) * (n : ℝ) ^ 5) *
          ENNReal.ofReal (2 * Real.sqrt ε) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add hC0 (by positivity)]
        congr 1; ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul' le_rfl hD2)

end TranspositionIID.Main
end

theorem solution : type_of% @TranspositionIID.Main.chk_lemma_4_1 := @TranspositionIID.Main.chk_lemma_4_1
